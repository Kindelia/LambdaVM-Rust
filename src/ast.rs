use TSPL::{new_parser, Parser, ParseError};
use highlight_error::highlight_error;
use crate::hvm;
use std::fmt::{Debug, Display};
use std::collections::{BTreeMap, BTreeSet};

// Types
// -----

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct Numb(pub u32);

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Tree {
  Var { nam: String },
  Ref { nam: String },
  Era,
  Lam { fst: Box<Tree>, snd: Box<Tree> },
  App { fst: Box<Tree>, snd: Box<Tree> },
  Dup { fst: Box<Tree>, snd: Box<Tree> },
}

pub type Redex = (bool, Tree, Tree);

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct Net {
  pub root: Tree,
  pub rbag: Vec<Redex>,
}

pub struct Book {
  pub defs: BTreeMap<String, Net>,
}

// Parser
// ------

pub type ParseResult<T> = std::result::Result<T, ParseError>;

new_parser!(CoreParser);

impl<'i> CoreParser<'i> {
  pub fn parse_tree(&mut self) -> ParseResult<Tree> {
    self.skip_trivia();
    //println!("aaa ||{}", &self.input[self.index..]);
    match self.peek_one() {
      Some('(') => {
        self.advance_one();
        let fst = Box::new(self.parse_tree()?);
        self.skip_trivia();
        let snd = Box::new(self.parse_tree()?);
        self.consume(")")?;
        Ok(Tree::Lam { fst, snd })
      }
      Some('{') => {
        self.advance_one();
        let fst = Box::new(self.parse_tree()?);
        self.skip_trivia();
        let snd = Box::new(self.parse_tree()?);
        self.consume("}")?;
        Ok(Tree::Dup { fst, snd })
      }
      Some('!') => {
        self.advance_one();
        self.consume("(")?;
        let fst = Box::new(self.parse_tree()?);
        self.skip_trivia();
        let snd = Box::new(self.parse_tree()?);
        self.consume(")")?;
        Ok(Tree::App { fst, snd })
      }
      Some('@') => {
        self.advance_one();
        let nam = self.parse_name()?;
        Ok(Tree::Ref { nam })
      }
      Some('*') => {
        self.advance_one();
        Ok(Tree::Era)
      }
      _ => {
        let nam = self.parse_name()?;
        Ok(Tree::Var { nam })
      }
    }
  }

  pub fn parse_net(&mut self) -> ParseResult<Net> {
    let root = self.parse_tree()?;
    let mut rbag = Vec::new();
    self.skip_trivia();
    while self.peek_one() == Some('&') {
      self.consume("&")?;
      let fst = self.parse_tree()?;
      self.consume("~")?;
      let snd = self.parse_tree()?;
      rbag.push((false,fst,snd));
      self.skip_trivia();
    }
    Ok(Net { root, rbag })
  }

  pub fn parse_book(&mut self) -> ParseResult<Book> {
    let mut defs = BTreeMap::new();
    while !self.is_eof() {
      self.consume("@")?;
      let name = self.parse_name()?;
      self.consume("=")?;
      let net = self.parse_net()?;
      defs.insert(name, net);
    }
    Ok(Book { defs })
  }

  fn try_consume(&mut self, str: &str) -> bool {
    let matches = self.peek_many(str.len()) == Some(str);
    if matches {
      self.advance_many(str.len());
    }
    matches
  }
}

// Stringifier
// -----------

impl Tree {
  pub fn show(&self) -> String {
    match self {
      Tree::Var { nam } => nam.to_string(),
      Tree::Ref { nam } => format!("@{}", nam),
      Tree::Era => "*".to_string(),
      Tree::Lam { fst, snd } => format!("({} {})", fst.show(), snd.show()),
      Tree::App { fst, snd } => format!("!({} {})", fst.show(), snd.show()),
      Tree::Dup { fst, snd } => format!("{{{} {}}}", fst.show(), snd.show()),
    }
  }
}

impl Net {
  pub fn show(&self) -> String {
    let mut s = self.root.show();
    for (par, fst, snd) in &self.rbag {
      s.push_str(" &");
      s.push_str(if *par { "!" } else { " " });
      s.push_str(&fst.show());
      s.push_str(" ~ ");
      s.push_str(&snd.show());
    }
    s
  }
}

impl Book {
  pub fn show(&self) -> String {
    let mut s = String::new();
    for (name, net) in &self.defs {
      s.push_str("@");
      s.push_str(name);
      s.push_str(" = ");
      s.push_str(&net.show());
      s.push('\n');
    }
    s
  }
}

// Readback
// --------

impl Tree {
  pub fn readback(net: &hvm::GNet, port: hvm::Port, fids: &BTreeMap<hvm::Val, String>) -> Option<Tree> {
    //println!("reading {}", port.show());
    match port.get_tag() {
      hvm::VAR => {
        let got = net.enter(port);
        if got != port {
          return Tree::readback(net, got, fids);
        } else {
          return Some(Tree::Var { nam: format!("v{:x}", port.get_val()) });
        }
      }
      hvm::REF => {
        return Some(Tree::Ref { nam: fids.get(&port.get_val())?.clone() });
      }
      hvm::ERA => {
        return Some(Tree::Era);
      }
      hvm::LAM => {
        let pair = net.node_load(port.get_val() as usize);
        let fst = Tree::readback(net, pair.get_fst(), fids)?;
        let snd = Tree::readback(net, pair.get_snd(), fids)?;
        return Some(Tree::Lam { fst: Box::new(fst), snd: Box::new(snd) });
      }
      hvm::APP => {
        let pair = net.node_load(port.get_val() as usize);
        let fst = Tree::readback(net, pair.get_fst(), fids)?;
        let snd = Tree::readback(net, pair.get_snd(), fids)?;
        return Some(Tree::App { fst: Box::new(fst), snd: Box::new(snd) });
      }
      hvm::DUP => {
        let pair = net.node_load(port.get_val() as usize);
        let fst = Tree::readback(net, pair.get_fst(), fids)?;
        let snd = Tree::readback(net, pair.get_snd(), fids)?;
        return Some(Tree::Dup { fst: Box::new(fst), snd: Box::new(snd) });
      }
      _ => {
        unreachable!()
      }
    }
  }
}

impl Net {
  pub fn readback(net: &hvm::GNet, book: &hvm::Book) -> Option<Net> {
    let mut fids = BTreeMap::new();
    for (fid, def) in book.defs.iter().enumerate() {
      fids.insert(fid as hvm::Val, def.name.clone());
    }
    let root = net.enter(hvm::ROOT);
    let root = Tree::readback(net, root, &fids)?;
    let rbag = Vec::new();
    return Some(Net { root, rbag });
  }
}

// Def Builder
// -----------

impl Tree {
  pub fn build(&self, def: &mut hvm::Def, fids: &BTreeMap<String, hvm::Val>, vars: &mut BTreeMap<String, hvm::Val>) -> hvm::Port {
    match self {
      Tree::Var { nam } => {
        if !vars.contains_key(nam) {
          vars.insert(nam.clone(), vars.len() as hvm::Val);
          def.vars += 1;
        }
        return hvm::Port::new(hvm::VAR, *vars.get(nam).unwrap());
      }
      Tree::Ref { nam } => {
        if let Some(fid) = fids.get(nam) {
          return hvm::Port::new(hvm::REF, *fid);
        } else {
          panic!("Unbound definition: {}", nam);
        }
      }
      Tree::Era => {
        return hvm::Port::new(hvm::ERA, 0);
      }
      Tree::Lam { fst, snd } => {
        let index = def.node.len();
        def.node.push(hvm::Pair(0));
        let p1 = fst.build(def, fids, vars);
        let p2 = snd.build(def, fids, vars);
        def.node[index] = hvm::Pair::new(p1, p2);
        return hvm::Port::new(hvm::LAM, index as hvm::Val);
      }
      Tree::App { fst, snd } => {
        let index = def.node.len();
        def.node.push(hvm::Pair(0));
        let p1 = fst.build(def, fids, vars);
        let p2 = snd.build(def, fids, vars);
        def.node[index] = hvm::Pair::new(p1, p2);
        return hvm::Port::new(hvm::APP, index as hvm::Val);
      }
      Tree::Dup { fst, snd } => {
        def.safe = false;
        let index = def.node.len();
        def.node.push(hvm::Pair(0));
        let p1 = fst.build(def, fids, vars);
        let p2 = snd.build(def, fids, vars);
        def.node[index] = hvm::Pair::new(p1, p2);
        return hvm::Port::new(hvm::DUP, index as hvm::Val);
      },
    }
  }

  pub fn direct_dependencies<'name>(&'name self) -> BTreeSet<&'name str> {
    let mut stack: Vec<&Tree> = vec![self];
    let mut acc: BTreeSet<&'name str> = BTreeSet::new();
    
    while let Some(curr) = stack.pop() {
      match curr {
        Tree::Ref { nam } => { acc.insert(nam); },
        Tree::Lam { fst, snd } => { stack.push(fst); stack.push(snd); },
        Tree::App { fst, snd } => { stack.push(fst); stack.push(snd); },
        Tree::Dup { fst, snd } => { stack.push(fst); stack.push(snd); },
        Tree::Var { nam } => {},
        Tree::Era => {},
      };
    }
    acc
  }
}

impl Net {
  pub fn build(&self, def: &mut hvm::Def, fids: &BTreeMap<String, hvm::Val>, vars: &mut BTreeMap<String, hvm::Val>) {
    let index = def.node.len();
    def.root = self.root.build(def, fids, vars);
    for (par, fst, snd) in &self.rbag {
      let index = def.rbag.len();
      def.rbag.push(hvm::Pair(0));
      let p1 = fst.build(def, fids, vars);
      let p2 = snd.build(def, fids, vars);
      let rx = hvm::Pair::new(p1, p2);
      def.rbag[index] = rx;
    }
  }
}

impl Book {
  pub fn parse(code: &str) -> ParseResult<Self> {
    CoreParser::new(code).parse_book()
  }

  pub fn build(&self) -> hvm::Book {
    let mut name_to_fid = BTreeMap::new();
    let mut fid_to_name = BTreeMap::new();
    fid_to_name.insert(0, "main".to_string());
    name_to_fid.insert("main".to_string(), 0);
    for (_i, (name, _)) in self.defs.iter().enumerate() {
      if name != "main" {
        fid_to_name.insert(name_to_fid.len() as hvm::Val, name.clone());
        name_to_fid.insert(name.clone(), name_to_fid.len() as hvm::Val);
      }
    }
    let mut book = hvm::Book { defs: Vec::new() };
    for (fid, name) in &fid_to_name {
      let ast_def = self.defs.get(name).expect("missing `@main` definition");
      let mut def = hvm::Def {
        name: name.clone(),
        safe: true,
        root: hvm::Port(0),
        rbag: vec![],
        node: vec![],
        vars: 0,
      };
      ast_def.build(&mut def, &name_to_fid, &mut BTreeMap::new());
      book.defs.push(def);
    }
    self.propagate_safety(&mut book, &name_to_fid);
    return book;
  }

  /// Propagate unsafe definitions to those that reference them.
  ///
  /// When calling this function, it is expected that definitions that are directly
  /// unsafe are already marked as such in the `compiled_book`.
  /// 
  /// This does not completely solve the cloning safety in HVM. It only stops invalid
  /// **global** definitions from being cloned, but local unsafe code can still be
  /// cloned and can generate seemingly unexpected results, such as placing eraser
  /// nodes in weird places. See HVM issue [#362](https://github.com/HigherOrderCO/HVM/issues/362)
  /// for an example.
  fn propagate_safety(&self, compiled_book: &mut hvm::Book, lookup: &BTreeMap<String, u32>) {
    let dependents = self.direct_dependents();
    let mut stack: Vec<&str> = Vec::new();

    for (name, _) in self.defs.iter() {
      let def = &mut compiled_book.defs[lookup[name] as usize];
      if !def.safe {
        for next in dependents[name.as_str()].iter() {
          stack.push(next);
        }
      }
    }

    while let Some(curr) = stack.pop() {
      let def = &mut compiled_book.defs[lookup[curr] as usize];
      if !def.safe {
        // Already visited, skip this
        continue;
      }

      def.safe = false;

      for &next in dependents[curr].iter() {
        stack.push(next);
      }
    }
  }

  /// Calculates the dependents of each definition, that is, if definition `A`
  /// requires `B`, `B: A` is in the return map. This is used to propagate unsafe
  /// definitions to others that depend on them.
  /// 
  /// This solution has linear complexity on the number of definitions in the
  /// book and the number of direct references in each definition, but it also
  /// traverses each definition's trees entirely once.
  ///
  /// Complexity: O(d*t + r)
  /// - `d` is the number of definitions in the book
  /// - `r` is the number of direct references in each definition
  /// - `t` is the number of nodes in each tree
  fn direct_dependents<'name>(&'name self) -> BTreeMap<&'name str, BTreeSet<&'name str>> {
    let mut result = BTreeMap::new();
    for (name, _) in self.defs.iter() {
      result.insert(name.as_str(), BTreeSet::new());
    }

    let mut process = |tree: &'name Tree, name: &'name str| {
      for dependency in tree.direct_dependencies() {
        result
          .get_mut(dependency)
          .expect("global definition depends on undeclared reference")
          .insert(name);
      }
    };

    for (name, net) in self.defs.iter() {
      process(&net.root, name);
      for (_, r1, r2) in net.rbag.iter() {
        process(r1, name);
        process(r2, name);
      }
    }
    result
  }
}
