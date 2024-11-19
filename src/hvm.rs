use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::alloc::{alloc, dealloc, Layout};
use std::mem;

// Runtime
// =======

// Types
pub type Tag  = u8;  // Tag  ::= 4-bit (rounded up to u8)
pub type Lab  = u32; // Lab  ::= 28-bit (rounded up to u32)
pub type Val  = u32; // Val  ::= 28-bit (rounded up to u32)
pub type Rule = u8;  // Rule ::= 8-bit (fits a u8)

// Port
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Hash)]
pub struct Port(pub Val);

// Pair
pub struct Pair(pub u64);

// Atomics
pub type AVal = AtomicU32;
pub struct APort(pub AVal);
pub struct APair(pub AtomicU64);


// Tags
pub const VAR : Tag = 0x0; // variable
pub const REF : Tag = 0x1; // reference
pub const ERA : Tag = 0x2; // eraser
pub const CAL : Tag = 0x3; // call
pub const LAM : Tag = 0x4; // lambda
pub const APP : Tag = 0x5; // application
pub const DUP : Tag = 0x6; // duplicator
pub const EVL : Tag = 0x7; // eval
pub const WAI : Tag = 0x8; // wait
pub const HLD : Tag = 0x9; // hold
pub const DCD : Tag = 0xA; // decide

// Rules
pub const LINK : Rule = 0x0; // variable link
pub const DREF : Rule = 0x1; // definition dereference
pub const VOID : Rule = 0x2; // erase nullary
pub const ERAS : Rule = 0x3; // erase binary
pub const ANNI : Rule = 0x4; // annihilation
pub const COMM : Rule = 0x5; // commutation
pub const BETA : Rule = 0x6; // lazy beta reduction
pub const ELAM : Rule = 0x7; // evaluate lambda
pub const EDUP : Rule = 0x8; // evaluate superposition
pub const EWAI : Rule = 0x9; // evaluate wait
pub const WAPP : Rule = 0xA; // wait application
pub const WDUP : Rule = 0xB; // wait duplication
pub const CHLD : Rule = 0xC; // call hold
pub const CDCD : Rule = 0xD; // call decide
pub const EDCD : Rule = 0xE; // erase decide
pub const ERR_ : Rule = 0xF; // error

// Constants
pub const FREE : Port = Port(0x0);
pub const ROOT : Port = Port(0xFFFFFFF0);
pub const NONE : Port = Port(0xFFFFFFFF);

// RBag
pub struct RBag {
  pub lo: Vec<Pair>,
  pub hi: Vec<Pair>,
}

// Global Net
pub struct GNet<'a> {
  pub nlen: usize, // length of the node buffer
  pub vlen: usize, // length of the vars buffer
  pub node: &'a mut [APair], // node buffer
  pub vars: &'a mut [APort], // vars buffer
  pub itrs: AtomicU64, // interaction count
}

// Thread Memory
pub struct TMem {
  pub tid: u32, // thread id
  pub tids: u32, // thread count
  pub tick: u32, // tick counter
  pub itrs: u32, // interaction count
  pub nput: usize, // next node allocation index
  pub vput: usize, // next vars allocation index
  pub nloc: Vec<usize>, // allocated node locations
  pub vloc: Vec<usize>, // allocated vars locations
  pub rbag: RBag, // local redex bag
}

// Top-Level Definition
pub struct Def {
  pub name: String, // def name
  pub safe: bool, // has no dups
  pub root: Port, // root port
  pub rbag: Vec<Pair>, // def redex bag
  pub node: Vec<Pair>, // def node buffer
  pub vars: usize, // def vars count
}

// Book of Definitions
pub struct Book {
  pub defs: Vec<Def>,
}

impl Port {
  pub fn new(tag: Tag, val: Val) -> Self {
    Port((val << 4) | tag as Val)
  }

  pub fn get_tag(&self) -> Tag {
    (self.0 & 0b1111) as Tag
  }

  pub fn get_val(&self) -> Val {
    self.0 >> 4
  }

  pub fn is_nod(&self) -> bool {
    self.get_tag() >= LAM
  }

  pub fn is_var(&self) -> bool {
    self.get_tag() == VAR
  }

  pub fn get_rule(a: Port, b: Port) -> Rule {
    const TABLE: [[Rule; 11]; 11] = [
      //VAR  REF  ERA  CAL  LAM  APP  DUP  EVL  WAI  HLD  DCD
      [LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK], // VAR
      [LINK,VOID,VOID,ERR_,DREF,DREF,DREF,DREF,DREF,ERR_,ERR_], // REF
      [LINK,VOID,VOID,VOID,ERAS,ERAS,ERAS,ERAS,ERAS,ERAS,EDCD], // ERA
      [LINK,ERR_,VOID,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,CDCD], // CAL
      [LINK,DREF,ERAS,ERR_,ERR_,ANNI,COMM,ELAM,ERR_,ERR_,ERR_], // LAM
      [LINK,DREF,ERAS,ERR_,ANNI,ERR_,COMM,ERR_,WAPP,ERR_,ERR_], // APP
      [LINK,DREF,ERAS,ERR_,COMM,COMM,ANNI,EDUP,WDUP,ERR_,ERR_], // DUP
      [LINK,DREF,ERAS,ERR_,ELAM,ERR_,EDUP,ERR_,EWAI,ERR_,ERR_], // EVL
      [LINK,DREF,ERAS,ERR_,ERR_,WAPP,WDUP,EWAI,ERR_,ERR_,ERR_], // WAI
      [LINK,ERR_,ERAS,CHLD,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_], // HLD
      [LINK,ERR_,EDCD,CDCD,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_], // DCD
    ];
    return TABLE[a.get_tag() as usize][b.get_tag() as usize];
  }

  pub fn should_swap(a: Port, b: Port) -> bool {
    b.get_tag() < a.get_tag()
  }

  pub fn is_high_priority(rule: Rule) -> bool {
    match rule {
      COMM | DREF | BETA | WAPP | WDUP => true,
      LINK | VOID | ERAS | ANNI | ELAM | EDUP | EWAI | CHLD | CDCD | EDCD | ERR_ => true,
      _ => unreachable!("Invalid rule {}", rule),
    }
  }

  pub fn adjust_port(&self, tm: &TMem) -> Port {
    let tag = self.get_tag();
    let val = self.get_val();
    if self.is_nod() {
      Port::new(tag, tm.nloc[val as usize] as u32)
    } else if self.is_var() {
      Port::new(tag, tm.vloc[val as usize] as u32)
    } else {
      Port::new(tag, val)
    }
  }

}

impl Pair {
  pub fn new(fst: Port, snd: Port) -> Self {
    Pair(((snd.0 as u64) << 32) | fst.0 as u64)
  }

  pub fn get_fst(&self) -> Port {
    Port((self.0 & 0xFFFFFFFF) as u32)
  }

  pub fn get_snd(&self) -> Port {
    Port((self.0 >> 32) as u32)
  }

  pub fn adjust_pair(&self, tm: &TMem) -> Pair {
    let p1 = self.get_fst().adjust_port(tm);
    let p2 = self.get_snd().adjust_port(tm);
    Pair::new(p1, p2)
  }
}

impl RBag {
  pub fn new() -> Self {
    RBag {
      lo: Vec::new(),
      hi: Vec::new(),
    }
  }

  pub fn push_redex(&mut self, redex: Pair) {
    let rule = Port::get_rule(redex.get_fst(), redex.get_snd());
    if Port::is_high_priority(rule) {
      self.hi.push(redex);
    } else {
      self.lo.push(redex);
    }
  }

  pub fn pop_redex(&mut self) -> Option<Pair> {
    if !self.hi.is_empty() {
      self.hi.pop()
    } else {
      self.lo.pop()
    }
  }

  pub fn len(&self) -> usize {
    self.lo.len() + self.hi.len()
  }

  pub fn has_highs(&self) -> bool {
    !self.hi.is_empty()
  }
}

impl<'a> GNet<'a> {
  pub fn new(nlen: usize, vlen: usize) -> Self {
    let nlay = Layout::array::<APair>(nlen).unwrap();
    let vlay = Layout::array::<APort>(vlen).unwrap();
    let nptr = unsafe { alloc(nlay) as *mut APair };
    let vptr = unsafe { alloc(vlay) as *mut APort };
    let node = unsafe { std::slice::from_raw_parts_mut(nptr, nlen) };
    let vars = unsafe { std::slice::from_raw_parts_mut(vptr, vlen) };
    GNet { nlen, vlen, node, vars, itrs: AtomicU64::new(0) }
  }

  pub fn node_create(&self, loc: usize, val: Pair) {
    self.node[loc].0.store(val.0, Ordering::Relaxed);
  }

  pub fn vars_create(&self, var: usize, val: Port) {
    self.vars[var].0.store(val.0, Ordering::Relaxed);
  }

  pub fn node_load(&self, loc: usize) -> Pair {
    Pair(self.node[loc].0.load(Ordering::Relaxed))
  }

  pub fn vars_load(&self, var: usize) -> Port {
    Port(self.vars[var].0.load(Ordering::Relaxed) as u32)
  }

  pub fn node_store(&self, loc: usize, val: Pair) {
    self.node[loc].0.store(val.0, Ordering::Relaxed);
  }

  pub fn vars_store(&self, var: usize, val: Port) {
    self.vars[var].0.store(val.0, Ordering::Relaxed);
  }

  pub fn node_exchange(&self, loc: usize, val: Pair) -> Pair {
    Pair(self.node[loc].0.swap(val.0, Ordering::Relaxed))
  }

  pub fn vars_exchange(&self, var: usize, val: Port) -> Port {
    Port(self.vars[var].0.swap(val.0, Ordering::Relaxed) as u32)
  }

  pub fn node_take(&self, loc: usize) -> Pair {
    self.node_exchange(loc, Pair(0))
  }

  pub fn vars_take(&self, var: usize) -> Port {
    self.vars_exchange(var, Port(0))
  }

  pub fn is_node_free(&self, loc: usize) -> bool {
    self.node_load(loc).0 == 0
  }

  pub fn is_vars_free(&self, var: usize) -> bool {
    self.vars_load(var).0 == 0
  }

  pub fn enter(&self, mut var: Port) -> Port {
    // While `B` is VAR: extend it (as an optimization)
    while var.get_tag() == VAR {
      // Takes the current `B` substitution as `B'`
      let val = self.vars_exchange(var.get_val() as usize, NONE);
      // If there was no `B'`, stop, as there is no extension
      if val == NONE || val == Port(0) {
        break;
      }
      // Otherwise, delete `B` (we own both) and continue as `A ~> B'`
      self.vars_take(var.get_val() as usize);
      var = val;
    }
    return var;
  }

}

impl<'a> Drop for GNet<'a> {
  fn drop(&mut self) {
    let nlay = Layout::array::<APair>(self.nlen).unwrap();
    let vlay = Layout::array::<APair>(self.vlen).unwrap();
    unsafe {
      dealloc(self.node.as_mut_ptr() as *mut u8, nlay);
      dealloc(self.vars.as_mut_ptr() as *mut u8, vlay);
    }
  }

}

impl TMem {
  // TODO: implement a TMem::new() fn
  pub fn new(tid: u32, tids: u32) -> Self {
    TMem {
      tid,
      tids,
      tick: 0,
      itrs: 0,
      nput: 0,
      vput: 0,
      nloc: vec![0; 0xFFF], // FIXME: move to a constant
      vloc: vec![0; 0xFFF],
      rbag: RBag::new(),
    }
  }

  pub fn node_alloc(&mut self, net: &GNet, num: usize) -> usize {
    let mut got = 0;
    for _ in 0..net.nlen {
      self.nput += 1; // index 0 reserved
      if self.nput < net.nlen-1 || net.is_node_free(self.nput % net.nlen) {
        self.nloc[got] = self.nput % net.nlen;
        got += 1;
        //println!("ALLOC NODE {} {}", got, self.nput);
      }
      if got >= num {
        break;
      }
    }
    return got
  }

  pub fn vars_alloc(&mut self, net: &GNet, num: usize) -> usize {
    let mut got = 0;
    for _ in 0..net.vlen {
      self.vput += 1; // index 0 reserved for FREE
      if self.vput < net.vlen-1 || net.is_vars_free(self.vput % net.vlen) {
        self.vloc[got] = self.vput % net.nlen;
        //println!("ALLOC VARS {} {}", got, self.vput);
        got += 1;
      }
      if got >= num {
        break;
      }
    }
    got
  }

  pub fn get_resources(&mut self, net: &GNet, _need_rbag: usize, need_node: usize, need_vars: usize) -> bool {
    let got_node = self.node_alloc(net, need_node);
    let got_vars = self.vars_alloc(net, need_vars);
    got_node >= need_node && got_vars >= need_vars
  }

  // Atomically Links `A ~ B`.
  pub fn link(&mut self, net: &GNet, a: Port, b: Port) {
    //println!("link {} ~ {}", a.show(), b.show());
    let mut a = a;
    let mut b = b;

    // Attempts to directionally point `A ~> B`
    loop {
      // If `A` is NODE: swap `A` and `B`, and continue
      if a.get_tag() != VAR && b.get_tag() == VAR {
        let x = a; a = b; b = x;
      }

      // If `A` is NODE: create the `A ~ B` redex
      if a.get_tag() != VAR {
        self.rbag.push_redex(Pair::new(a, b));
        break;
      }

      // While `B` is VAR: extend it (as an optimization)
      b = net.enter(b);

      // Since `A` is VAR: point `A ~> B`.
      if true {
        // Stores `A -> B`, taking the current `A` subst as `A'`
        let a_ = net.vars_exchange(a.get_val() as usize, b);
        // If there was no `A'`, stop, as we lost B's ownership
        if a_ == NONE {
          break;
        }
        // Otherwise, delete `A` (we own both) and link `A' ~ B`
        net.vars_take(a.get_val() as usize);
        a = a_;
      }
    }
  }

  // Links `A ~ B` (as a pair).
  pub fn link_pair(&mut self, net: &GNet, ab: Pair) {
    self.link(net, ab.get_fst(), ab.get_snd());
    //println!("link_pair {:016X}", ab.0);
  }

  // The Link Interaction.
  pub fn interact_link(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 1, 0, 0) {
      return false;
    }

    // Links.
    self.link_pair(net, Pair::new(a, b));

    true
  }

  // The Call Interaction.
  pub fn interact_call(&mut self, net: &GNet, a: Port, b: Port, book: &Book) -> bool {
    let fid = (a.get_val() as usize) & 0xFFFFFFF;
    let def = &book.defs[fid];

    // Copy Optimization.
    if b.get_tag() == DUP {
      if def.safe {
        return self.interact_eras(net, a, b);
      } else {
        // TODO:
        // Currently, we'll not allow copying of REFs with DUPs. While this is perfectly valid on
        // IC semantics (i.e., if the user know what they're doing), this can lead to unsound
        // reductions when compiling λ-terms to HVM. So, for now, we'll just disable this feature,
        // and consider it undefined behavior. We should add a `--unsafe` flag that allows it.
        println!("ERROR: attempt to clone a non-affine global reference.\n");
        std::process::exit(0);
      }
    }

    // Allocates needed nodes and vars.
    if !self.get_resources(net, def.rbag.len() + 1, def.node.len(), def.vars as usize) {
      return false;
    }

    // Stores new vars.
    for i in 0..def.vars {
      net.vars_create(self.vloc[i], NONE);
      //println!("vars_create vars_loc[{:04X}] {:04X}", i, self.vloc[i]);
    }

    // Stores new nodes.
    for i in 0..def.node.len() {
      net.node_create(self.nloc[i], def.node[i].adjust_pair(self));
      //println!("node_create node_loc[{:04X}] {:016X}", i-1, def.node[i].0);
    }

    // Links.
    for pair in &def.rbag {
      self.link_pair(net, pair.adjust_pair(self));
    }
    self.link_pair(net, Pair::new(def.root.adjust_port(self), b));

    true
  }

  // The Void Interaction.
  pub fn interact_void(&mut self, _net: &GNet, _a: Port, _b: Port) -> bool {
    true
  }

  // The Eras Interaction.
  // #X(a b) ~ *
  // --------------- ERAS
  // a ~ *
  // b ~ *
  pub fn interact_eras(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 2, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_exchange(b.get_val() as usize, Pair(0));
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Links.
    self.link_pair(net, Pair::new(a, b1));
    self.link_pair(net, Pair::new(a, b2));

    true
  }

  // The Anni Interaction.
  // #X(a b) ~ #X(c d)
  // --------------- ANNI
  // a ~ c
  // b ~ d
  pub fn interact_anni(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 2, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Links.
    self.link_pair(net, Pair::new(a1, b1));
    self.link_pair(net, Pair::new(a2, b2));

    return true;
  }

  // The Comm Interaction.
  // #X(a b) ~ #Y(c d)
  // --------------- COMM
  // a ~ #Y(l m)
  // b ~ #Y(n o)
  // c ~ #X(l n)
  // d ~ #X(m o)
  pub fn interact_comm(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 4, 4, 4) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Stores new vars.
    net.vars_create(self.vloc[0], NONE);
    net.vars_create(self.vloc[1], NONE);
    net.vars_create(self.vloc[2], NONE);
    net.vars_create(self.vloc[3], NONE);

    // Stores new nodes.
    net.node_create(self.nloc[0], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(VAR, self.vloc[1] as u32)));
    net.node_create(self.nloc[1], Pair::new(Port::new(VAR, self.vloc[2] as u32), Port::new(VAR, self.vloc[3] as u32)));
    net.node_create(self.nloc[2], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(VAR, self.vloc[2] as u32)));
    net.node_create(self.nloc[3], Pair::new(Port::new(VAR, self.vloc[1] as u32), Port::new(VAR, self.vloc[3] as u32)));

    // Links.
    self.link_pair(net, Pair::new(Port::new(b.get_tag(), self.nloc[0] as u32), a1));
    self.link_pair(net, Pair::new(Port::new(b.get_tag(), self.nloc[1] as u32), a2));
    self.link_pair(net, Pair::new(Port::new(a.get_tag(), self.nloc[2] as u32), b1));
    self.link_pair(net, Pair::new(Port::new(a.get_tag(), self.nloc[3] as u32), b2));

    true
  }

  // The Lazy Beta Reduction Interaction.
  // #λ(a b) ~ #@(c d)
  // --------------- BETA
  // a ~ #W(i #H(i c))
  // b ~ d
  pub fn interact_beta(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 2, 2, 1) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Stores new vars.
    net.vars_create(self.vloc[0], NONE);

    // Stores new nodes.
    net.node_create(self.nloc[0], Pair::new(Port::new(VAR, self.vloc[0] as u32), b1));
    net.node_create(self.nloc[1], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(HLD, self.nloc[0] as u32)));

    // Links.
    self.link_pair(net, Pair::new(a2, b2));
    self.link_pair(net, Pair::new(Port::new(WAI, self.nloc[1] as u32), a1));

    true
  }

  // Lambda evaluation interaction.
  // #λ(a b) ~ #E(c *)
  // --------------- EVAL-LAM
  // c ~ #λ(a i)
  // #E(i *) ~ b
  pub fn interact_elam(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 2, 2, 1) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Stores new vars.
    net.vars_create(self.vloc[0], NONE);

    // Stores new nodes.
    net.node_create(self.nloc[0], Pair::new(a1, Port::new(VAR, self.vloc[0] as u32)));
    net.node_create(self.nloc[1], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(ERA, 0)));

    // Links.
    self.link_pair(net, Pair::new(b1, Port::new(LAM, self.nloc[0] as u32)));
    self.link_pair(net, Pair::new(Port::new(EVL, self.nloc[1] as u32), a2));

    true
  }

  // Dup evaluation interaction.
  // #d(a b) ~ #E(c *)
  // --------------- EVAL-DUP
  // #d(a b) ~ c
  pub fn interact_edup(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 1, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();

    // Links.
    self.link_pair(net, Pair::new(a, b1));

    true
  }

  // Wait evaluation interaction.
  // #E(a *) ~ #W(c d)
  // --------------- EVAL-WAI
  // #E(a *) ~ c
  // #C      ~ d
  pub fn interact_ewai(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 2, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_fst();

    // Links.
    self.link_pair(net, Pair::new(a, b1));
    self.link_pair(net, Pair::new(Port::new(CAL, 0), b2));

    true
  }

  // Application wait interaction.
  // #@(a b) ~ #W(c d)
  // --------------- WAIT-APP
  // a ~ #W(i #H(#@(b i) #W(c d)))
  pub fn interact_wapp(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 1, 3, 1) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();

    // Stores new vars.
    net.vars_create(self.vloc[0], NONE);

    // Stores new nodes.
    net.node_create(self.nloc[0], Pair::new(a2, Port::new(VAR, self.vloc[0] as u32)));
    net.node_create(self.nloc[1], Pair::new(Port::new(APP, self.nloc[0] as u32), b));
    net.node_create(self.nloc[2], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(HLD, self.nloc[1] as u32)));

    // Links.
    self.link_pair(net, Pair::new(a1, Port::new(WAI, self.nloc[2] as u32)));

    true
  }

  // Duplication wait interaction.
  // #d(a b) ~ #W(c d)
  // --------------- WAIT-DUP
  // a ~ #W(i j)
  // b ~ #W(k l)
  // j ~ l ~ #D(d)
  // c ~ #d(i k)
  pub fn interact_wdup(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 3, 4, 2) {
      return false;
    }

    // Checks availability
    if net.node_load(a.get_val() as usize).0 == 0 || net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let a_ = net.node_take(a.get_val() as usize);
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Stores new vars.
    net.vars_create(self.vloc[0], NONE); // dup1
    net.vars_create(self.vloc[1], NONE); // dup2

    // Stores new nodes.
    net.node_create(self.nloc[0], Pair::new(b2, Port::new(ERA, 0)));
    net.node_create(self.nloc[1], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(DCD, self.nloc[0] as u32)));
    net.node_create(self.nloc[2], Pair::new(Port::new(VAR, self.vloc[1] as u32), Port::new(DCD, self.nloc[0] as u32)));
    net.node_create(self.nloc[3], Pair::new(Port::new(VAR, self.vloc[0] as u32), Port::new(VAR, self.vloc[1] as u32)));

    // Links.
    self.link_pair(net, Pair::new(a1, Port::new(WAI, self.nloc[1] as u32)));
    self.link_pair(net, Pair::new(a2, Port::new(WAI, self.nloc[2] as u32)));
    self.link_pair(net, Pair::new(b1, Port::new(DUP, self.nloc[3] as u32)));

    true
  }

  // Call hold interaction.
  // #C ~ #H(a b)
  // --------------- CALL-HLD
  // #E(a *) ~ b
  pub fn interact_chld(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // Allocates needed nodes and vars.
    if !self.get_resources(net, 1, 1, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_take(b.get_val() as usize);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    // Store new nodes.
    net.node_create(self.nloc[0], Pair::new(b1, Port::new(ERA, 0)));

    // Links.
    self.link_pair(net, Pair::new(Port::new(EVL, self.nloc[0] as u32), b2));

    true
  }

  // Call decide interaction.
  // #D(a 0) ~ #C ~ b
  // --------------- CALL-DCD(0) (fst)
  // #C      ~ a
  // #D(a 1) ~ b
  //
  // #D(a 1) ~ #C ~ b
  // --------------- CALL-DCD(1) (snd, prev CDCD)
  // .
  //
  // #D(a 2) ~ #C ~ b
  // --------------- CALL-DCD(2) (snd, prev EDCD)
  // #C ~ a
  pub fn interact_cdcd(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    // The two principal ports of the decide node race to get its value.
    // They communicate by atomically swapping the second aux port of the DCD which is unused.
    // We swap the second aux port value with 0x1
    // If the taken value was 0x0, that this was the first node to reach the decide node.
    // Execute the interaction and continue.
    // If the taken value was 0x1, this was the second node and the previous one did a CDCD interaction.
    // This means that we just erase the call, free the decide node and return nothing.
    // If the taken value was 0x2, this was the second node and the previous one did a EDCD interaction.
    // We propagate the call to port 1 of the DCD.
    // 
    // This does not implement exactly the same interaction as in the paper,
    // but since the only thing that can reach a DCD are CAL and negative ERA,
    // the positive ERA would not propagate upwards anyways.
    if !self.get_resources(net, 1, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_load(b.get_val() as usize);
    let b_ = Pair::new(b_.get_fst(), Port::new(CAL, 1));
    let b_ = net.node_exchange(b.get_val() as usize, b_);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    match b2.get_val() {
      0 => {
        // First to reach
        self.link_pair(net, Pair::new(b1, Port::new(CAL, 0)));
        true
      }
      1 => {
        // Second to reach, previous was CDCD
        net.node_take(b.get_val() as usize);
        true
      }
      2 => {
        // Second to reach, previous was EDCD
        net.node_take(b.get_val() as usize);
        self.link_pair(net, Pair::new(b1, Port::new(CAL, 1)));
        true
      }
      _ => unreachable!("Invalid CDCD state")
    }
  }

  // Erase decide interaction.
  // #D(a 0) ~ * ~ b
  // --------------- ERAS-DCD(0) (fst)
  // #D(a 2) ~ b
  //
  // #D(a 1) ~ #C ~ b
  // --------------- ERAS-DCD(1) (snd, prev CDCD)
  // .
  //
  // #D(a 2) ~ #C ~ b
  // --------------- ERAS-DCD(3) (snd, prev EDCD)
  // * ~ a
  pub fn interact_edcd(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    if !self.get_resources(net, 1, 0, 0) {
      return false;
    }

    // Checks availability
    if net.node_load(b.get_val() as usize).0 == 0 {
      return false;
    }

    // Loads ports.
    let b_ = net.node_load(b.get_val() as usize);
    let b_ = Pair::new(b_.get_fst(), Port::new(CAL, 2));
    let b_ = net.node_exchange(b.get_val() as usize, b_);
    let b1 = b_.get_fst();
    let b2 = b_.get_snd();

    match b2.get_val() {
      0 => {
        // First to reach
        true
      }
      1 => {
        // Second to reach, previous was CDCD
        net.node_take(b.get_val() as usize);
        true
      }
      2 => {
        // Second to reach, previous was EDCD
        net.node_take(b.get_val() as usize);
        self.link_pair(net, Pair::new(b1, Port::new(ERA, 0)));
        true
      }
      _ => unreachable!("Invalid EDCD state")
    }
  }

  pub fn interact_err(&mut self, net: &GNet, a: Port, b: Port) -> bool {
    unreachable!("Invalid redex pair: {} ~ {}", a.show(), b.show());
  }

  // Pops a local redex and performs a single interaction.
  pub fn interact(&mut self, net: &GNet, book: &Book) -> bool {
    // Pops a redex.
    let redex = match self.rbag.pop_redex() {
      Some(redex) => redex,
      None => return true, // If there is no redex, stop
    };

    // Gets redex ports A and B.
    let mut a = redex.get_fst();
    let mut b = redex.get_snd();

    // Gets the rule type.
    let mut rule = Port::get_rule(a, b);

    // Used for root redex.
    if a.get_tag() == REF && b == ROOT {
      rule = DREF;
    // Swaps ports if necessary.
    } else if Port::should_swap(a,b) {
      let x = a; a = b; b = x;
    }

    //println!("[{:04x}] REDUCE {} ~ {} | {}", self.tid, a.show(), b.show(), rule);

    let success = match rule {
      LINK => self.interact_link(net, a, b),
      DREF => self.interact_call(net, a, b, book),
      VOID => self.interact_void(net, a, b),
      ERAS => self.interact_eras(net, a, b),
      ANNI => self.interact_anni(net, a, b),
      COMM => self.interact_comm(net, a, b),
      BETA => self.interact_beta(net, a, b),
      ELAM => self.interact_elam(net, a, b),
      EDUP => self.interact_edup(net, a, b),
      EWAI => self.interact_ewai(net, a, b),
      WAPP => self.interact_wapp(net, a, b),
      WDUP => self.interact_wdup(net, a, b),
      CHLD => self.interact_chld(net, a, b),
      CDCD => self.interact_cdcd(net, a, b),
      EDCD => self.interact_edcd(net, a, b),
      ERR_ => self.interact_err(net, a, b),
      _    => panic!("Invalid rule"),
    };

    // If error, pushes redex back.
    if !success {
      self.rbag.push_redex(redex);
      false
    // Else, increments the interaction count.
    } else if rule != LINK {
      self.itrs += 1;
      true
    } else {
      true
    }
  }

  pub fn evaluator(&mut self, net: &GNet, book: &Book) {
    // Increments the tick
    self.tick += 1;

    // DEBUG:
    //let mut max_rlen = 0;
    //let mut max_nlen = 0;
    //let mut max_vlen = 0;

    // Performs some interactions
    while self.rbag.len() > 0 {
      self.interact(net, book);

      // DEBUG:
      //println!("{}{}", self.rbag.show(), net.show());
      //println!("");
      //let rlen = self.rbag.lo.len() + self.rbag.hi.len();
      //let mut nlen = 0;
      //for i in 0 .. 256 {
        //if net.node_load(i).0 != 0 {
          //nlen += 1;
        //}
      //}
      //let mut vlen = 0;
      //for i in 0..256 {
        //if net.vars_load(i).0 != 0 {
          //vlen += 1;
        //}
      //}
      //max_rlen = max_rlen.max(rlen);
      //max_nlen = max_nlen.max(nlen);
      //max_vlen = max_vlen.max(vlen);

    }

    // DEBUG:
    //println!("MAX_RLEN: {}", max_rlen);
    //println!("MAX_NLEN: {}", max_nlen);
    //println!("MAX_VLEN: {}", max_vlen);

    net.itrs.fetch_add(self.itrs as u64, Ordering::Relaxed);
    self.itrs = 0;
  }
}

// Serialization
// -------------

impl Book {
  pub fn to_buffer(&self, buf: &mut Vec<u8>) {
    // Writes the number of defs
    buf.extend_from_slice(&(self.defs.len() as u32).to_ne_bytes());

    // For each def
    for (fid, def) in self.defs.iter().enumerate() {
      // Writes the safe flag
      buf.extend_from_slice(&(fid as u32).to_ne_bytes());

      // Writes the name
      // TODO: store as varlen to save space
      let name_bytes = def.name.as_bytes();
      if name_bytes.len() < 256 {
        buf.extend_from_slice(&name_bytes[..name_bytes.len()]);
        buf.resize(buf.len() + (256 - name_bytes.len()), 0);
      } else {
        panic!("Name too long: {}", def.name);
      }

      // Writes the safe flag
      buf.extend_from_slice(&(def.safe as u32).to_ne_bytes());

      // Writes the rbag length
      buf.extend_from_slice(&(def.rbag.len() as u32).to_ne_bytes());

      // Writes the node length
      buf.extend_from_slice(&(def.node.len() as u32).to_ne_bytes());

      // Writes the vars length
      buf.extend_from_slice(&(def.vars as u32).to_ne_bytes());

      // Writes the root
      buf.extend_from_slice(&def.root.0.to_ne_bytes());

      // Writes the rbag buffer
      for pair in &def.rbag {
        buf.extend_from_slice(&pair.0.to_ne_bytes());
      }

      // Writes the node buffer
      for pair in &def.node {
        buf.extend_from_slice(&pair.0.to_ne_bytes());
      }
    }
  }
}

// Debug
// -----

impl Port {
  pub fn show(&self) -> String {
    match self.get_tag() {
      VAR => format!("VAR:{:08X}", self.get_val()),
      REF => format!("REF:{:08X}", self.get_val()),
      ERA => format!("ERA:{:08X}", self.get_val()),
      LAM => format!("LAM:{:08X}", self.get_val()),
      APP => format!("APP:{:08X}", self.get_val()),
      DUP => format!("DUP:{:08X}", self.get_val()),
      _   => panic!("Invalid tag"),
    }
  }
}

impl Pair {
  pub fn show(&self) -> String {
    format!("{} ~ {}", self.get_fst().show(), self.get_snd().show())
  }
}

impl RBag {
  pub fn show(&self) -> String {
    let mut s = String::new();
    s.push_str("RBAG | FST-TREE     | SND-TREE    \n");
    s.push_str("---- | ------------ | ------------\n");
    for (i, pair) in self.hi.iter().enumerate() {
      s.push_str(&format!("{:04X} | {} | {}\n", i, pair.get_fst().show(), pair.get_snd().show()));
    }
    s.push_str("~~~~ | ~~~~~~~~~~~~ | ~~~~~~~~~~~~\n");
    for (i, pair) in self.lo.iter().enumerate() {
      s.push_str(&format!("{:04X} | {} | {}\n", i + self.hi.len(), pair.get_fst().show(), pair.get_snd().show()));
    }
    s.push_str("==== | ============ | ============\n");
    return s;
  }
}

impl<'a> GNet<'a> {
  pub fn show(&self) -> String {
    let mut s = String::new();
    s.push_str("NODE | FST-PORT     | SND-PORT     \n");
    s.push_str("---- | ------------ | ------------\n");
    //for i in 0..256 {
    for i in 0..self.nlen-1 {
      let node = self.node_load(i);
      if node.0 != 0 {
        s.push_str(&format!("{:04X} | {} | {}\n", i, node.get_fst().show(), node.get_snd().show()));
      }
    }
    s.push_str("==== | ============ | ============\n");
    s.push_str("VARS | VALUE        |\n");
    s.push_str("---- | ------------ |\n");
    //for i in 0..256 {
    for i in 0..self.vlen-1 {
      let var = self.vars_load(i);
      if var.0 != 0 {
        s.push_str(&format!("{:04X} | {} |\n", i, var.show()));
      }
    }
    let root = self.vars_load(0x1FFFFFFF);
    s.push_str(&format!("ROOT | {} |\n", root.show()));
    s.push_str("==== | ============ |\n");
    return s;
  }
}

impl Book {
  pub fn show(&self) -> String {
    let mut s = String::new();
    for def in &self.defs {
      s.push_str(&format!("==== | ============ | ============ {} (vars={},safe={})\n", def.name, def.vars, def.safe));
      s.push_str("NODE | FST-PORT     | SND-PORT     \n");
      s.push_str("---- | ------------ | ------------\n");
      for (i, node) in def.node.iter().enumerate() {
        s.push_str(&format!("{:04X} | {} | {}\n", i, node.get_fst().show(), node.get_snd().show()));
      }
      s.push_str("==== | ============ | ============\n");
      s.push_str("RBAG | FST-TREE     | SND-TREE    \n");
      s.push_str("---- | ------------ | ------------\n");
      for (i, node) in def.rbag.iter().enumerate() {
        s.push_str(&format!("{:04X} | {} | {}\n", i, node.get_fst().show(), node.get_snd().show()));
      }
      s.push_str("==== | ============ | ============\n");

    }
    return s;
  }
}
