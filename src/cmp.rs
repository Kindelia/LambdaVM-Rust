use crate::ast;
use crate::hvm;

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Target { CUDA, C }

// Compiles a whole Book.
pub fn compile_book(trg: Target, book: &hvm::Book) -> String {
  let mut code = String::new();

  // Compiles functions
  for fid in 0..book.defs.len() {
    compile_def(trg, &mut code, book, 0, fid as hvm::Val);
    code.push_str(&format!("\n"));
  }

  // Compiles interact_call
  if trg == Target::CUDA {
    code.push_str(&format!("__device__ "));
  }
  code.push_str(&format!("bool interact_call(Net *net, TM *tm, Port a, Port b) {{\n"));
  code.push_str(&format!("  u32 fid = get_val(a) & 0xFFFFFFF;\n"));
  code.push_str(&format!("  switch (fid) {{\n"));
  for (fid, def) in book.defs.iter().enumerate() {
    code.push_str(&format!("    case {}: return interact_call_{}(net, tm, a, b);\n", fid, &def.name.replace("/","_").replace(".","_").replace("-","_")));
  }
  code.push_str(&format!("    default: return false;\n"));
  code.push_str(&format!("  }}\n"));
  code.push_str(&format!("}}"));

  return code;
}

// Compiles a single Def.
pub fn compile_def(trg: Target, code: &mut String, book: &hvm::Book, tab: usize, fid: hvm::Val) {
  let def = &book.defs[fid as usize];
  let fun = &def.name.replace("/","_").replace(".","_").replace("-","_");

  // Initializes context
  let neo = &mut 0;
  
  // Generates function
  if trg == Target::CUDA {
    code.push_str(&format!("__device__ "));
  }
  code.push_str(&format!("{}bool interact_call_{}(Net *net, TM *tm, Port a, Port b) {{\n", indent(tab), fun));
  // Fast DUP-REF
  if def.safe {
    code.push_str(&format!("{}if (get_tag(b) == DUP) {{\n", indent(tab+1)));
    code.push_str(&format!("{}return interact_eras(net, tm, a, b);\n", indent(tab+2)));
    code.push_str(&format!("{}}}\n", indent(tab+1)));
  }
  code.push_str(&format!("{}u32 vl = 0;\n", indent(tab+1)));
  code.push_str(&format!("{}u32 nl = 0;\n", indent(tab+1)));

  // Allocs resources (using fast allocator)
  for i in 0 .. def.vars {
    code.push_str(&format!("{}Val v{:x} = vars_alloc_1(net, tm, &vl);\n", indent(tab+1), i));
  }
  for i in 0 .. def.node.len() {
    code.push_str(&format!("{}Val n{:x} = node_alloc_1(net, tm, &nl);\n", indent(tab+1), i));
  }
  code.push_str(&format!("{}if (0", indent(tab+1)));
  for i in 0 .. def.vars {
    code.push_str(&format!(" || !v{:x}", i));
  }
  for i in 0 .. def.node.len() {
    code.push_str(&format!(" || !n{:x}", i));
  }
  code.push_str(&format!(") {{\n"));
  code.push_str(&format!("{}return false;\n", indent(tab+2)));
  code.push_str(&format!("{}}}\n", indent(tab+1)));
  for i in 0 .. def.vars {
    code.push_str(&format!("{}vars_create(net, v{:x}, NONE);\n", indent(tab+1), i));
  }

  // Allocs resources (using slow allocator)
  //code.push_str(&format!("{}// Allocates needed resources.\n", indent(tab+1)));
  //code.push_str(&format!("{}if (!get_resources(net, tm, {}, {}, {})) {{\n", indent(tab+1), def.rbag.len()+1, def.node.len(), def.vars));
  //code.push_str(&format!("{}return false;\n", indent(tab+2)));
  //code.push_str(&format!("{}}}\n", indent(tab+1)));
  //for i in 0 .. def.node.len() {
    //code.push_str(&format!("{}Val n{:x} = tm->nloc[0x{:x}];\n", indent(tab+1), i, i));
  //}
  //for i in 0 .. def.vars {
    //code.push_str(&format!("{}Val v{:x} = tm->vloc[0x{:x}];\n", indent(tab+1), i, i));
  //}
  //for i in 0 .. def.vars {
    //code.push_str(&format!("{}vars_create(net, v{:x}, NONE);\n", indent(tab+1), i));
  //}

  // Compiles root
  compile_link_fast(trg, code, book, neo, tab+1, def, def.root, "b");

  // Compiles rbag
  for redex in &def.rbag {
    let fun = compile_node(trg, code, book, neo, tab+1, def, redex.get_fst());
    let arg = compile_node(trg, code, book, neo, tab+1, def, redex.get_snd());
    code.push_str(&format!("{}link(net, tm, {}, {});\n", indent(tab+1), &fun, &arg));
  }

  // Return
  code.push_str(&format!("{}return true;\n", indent(tab+1)));
  code.push_str(&format!("{}}}\n", indent(tab)));
}

// Compiles a link, performing some pre-defined static reductions.
pub fn compile_link_fast(trg: Target, code: &mut String, book: &hvm::Book, neo: &mut usize, tab: usize, def: &hvm::Def, a: hvm::Port, b: &str) {
  // FIXME: REVIEW
  // {a1 a2} <~ #v
  // ------------- Fast COPY
  // a1 <~ #v
  // a2 <~ #v
  if trg != Target::CUDA && a.get_tag() == hvm::DUP {
    let a_ = &def.node[a.get_val() as usize];
    let p1 = a_.get_fst();
    let p2 = a_.get_snd();
    let op = fresh(neo);
    let x1 = fresh(neo);
    let x2 = fresh(neo);
    code.push_str(&format!("{}bool {} = 0;\n", indent(tab), &op));
    code.push_str(&format!("{}Port {} = NONE;\n", indent(tab), &x1));
    code.push_str(&format!("{}Port {} = NONE;\n", indent(tab), &x2));
    code.push_str(&format!("{}// fast copy\n", indent(tab)));
    code.push_str(&format!("{}if (get_tag({}) == NUM) {{\n", indent(tab), b));
    code.push_str(&format!("{}tm->itrs += 1;\n", indent(tab+1)));
    code.push_str(&format!("{}{} = 1;\n", indent(tab+1), &op));
    code.push_str(&format!("{}{} = {};\n", indent(tab+1), &x1, b));
    code.push_str(&format!("{}{} = {};\n", indent(tab+1), &x2, b));
    code.push_str(&format!("{}}}\n", indent(tab)));
    compile_link_fast(trg, code, book, neo, tab, def, p2, &x2);
    compile_link_fast(trg, code, book, neo, tab, def, p1, &x1);
    code.push_str(&format!("{}if (!{}) {{\n", indent(tab), &op));
    code.push_str(&format!("{}node_create(net, n{:x}, new_pair({},{}));\n", indent(tab+1), a.get_val(), x1, x2));
    link_or_store(trg, code, book, neo, tab+1, def, &format!("new_port(DUP,n{:x})", a.get_val()), b);
    code.push_str(&format!("{}}}\n", indent(tab)));
    return;
  }

  // (a1 a2) <~ (x1 x2)
  // ------------------ Fast ANNI
  // a1 <~ x1
  // a2 <~ x2
  if trg != Target::CUDA && (a.get_tag() == hvm::LAM || a.get_tag() == hvm::APP) {
    let a_ = &def.node[a.get_val() as usize];
    let a1 = a_.get_fst();
    let a2 = a_.get_snd();
    let op = fresh(neo);
    let bv = fresh(neo);
    let x1 = fresh(neo);
    let x2 = fresh(neo);
    code.push_str(&format!("{}bool {} = 0;\n", indent(tab), &op));
    code.push_str(&format!("{}Pair {} = 0;\n", indent(tab), &bv));
    code.push_str(&format!("{}Port {} = NONE;\n", indent(tab), &x1));
    code.push_str(&format!("{}Port {} = NONE;\n", indent(tab), &x2));
    code.push_str(&format!("{}// fast anni\n", indent(tab)));
    code.push_str(&format!("{}if (get_tag({}) == CON && node_load(net, get_val({})) != 0) {{\n", indent(tab), b, b));
    //code.push_str(&format!("{}atomic_fetch_add(&FAST, 1);\n", indent(tab+1)));
    code.push_str(&format!("{}tm->itrs += 1;\n", indent(tab+1)));
    code.push_str(&format!("{}{} = 1;\n", indent(tab+1), &op));
    code.push_str(&format!("{}{} = node_take(net, get_val({}));\n", indent(tab+1), &bv, b));
    code.push_str(&format!("{}{} = get_fst({});\n", indent(tab+1), x1, &bv));
    code.push_str(&format!("{}{} = get_snd({});\n", indent(tab+1), x2, &bv));
    code.push_str(&format!("{}}}\n", indent(tab)));
    //code.push_str(&format!("{}else {{ atomic_fetch_add(&SLOW, 1); }}\n", indent(tab)));
    compile_link_fast(trg, code, book, neo, tab, def, a2, &x2);
    compile_link_fast(trg, code, book, neo, tab, def, a1, &x1);
    code.push_str(&format!("{}if (!{}) {{\n", indent(tab), &op));
    code.push_str(&format!("{}node_create(net, n{:x}, new_pair({},{}));\n", indent(tab+1), a.get_val(), x1, x2));
    link_or_store(trg, code, book, neo, tab+1, def, &format!("new_port(CON,n{:x})", a.get_val()), b);
    code.push_str(&format!("{}}}\n", indent(tab)));
    return;
  }

  // FIXME: since get_tag(NONE) == REF, comparing if something's tag is REF always has the issue of
  // returning true when that thing is NONE. this caused a bug in the optimization below. in
  // general, this is a potential source of bugs across the entire implementation, so we always
  // need to check that case. an alternative, of course, would be to make get_tag handle this, but
  // I'm concerned about the performance issues. so, instead, we should make sure that, across the
  // entire codebase, we never use get_tag expecting a REF on something that might be NONE
  
  // ATOM <~ *
  // --------- Fast VOID
  // nothing
  if trg != Target::CUDA && a.get_tag() == hvm::ERA {
    code.push_str(&format!("{}// fast void\n", indent(tab)));
    code.push_str(&format!("{}if (get_tag({}) == ERA || get_tag({}) == NUM) {{\n", indent(tab), b, b));
    code.push_str(&format!("{}tm->itrs += 1;\n", indent(tab+1)));
    code.push_str(&format!("{}}} else {{\n", indent(tab)));
    compile_link_slow(trg, code, book, neo, tab+1, def, a, b);
    code.push_str(&format!("{}}}\n", indent(tab)));
    return;
  }

  compile_link_slow(trg, code, book, neo, tab, def, a, b);
}

// Compiles a link, without pre-defined reductions.
pub fn compile_link_slow(trg: Target, code: &mut String, book: &hvm::Book, neo: &mut usize, tab: usize, def: &hvm::Def, a: hvm::Port, b: &str) {
  let a_node = compile_node(trg, code, book, neo, tab, def, a);
  link_or_store(trg, code, book, neo, tab, def, &a_node, b);
}

// TODO: comment
pub fn link_or_store(trg: Target, code: &mut String, book: &hvm::Book, neo: &mut usize, tab: usize, def: &hvm::Def, a: &str, b: &str) {
  code.push_str(&format!("{}if ({} != NONE) {{\n", indent(tab), b));
  code.push_str(&format!("{}link(net, tm, {}, {});\n", indent(tab+1), a, b));
  code.push_str(&format!("{}}} else {{\n", indent(tab)));
  code.push_str(&format!("{}{} = {};\n", indent(tab+1), b, a));
  code.push_str(&format!("{}}}\n", indent(tab)));
}

// Compiles just a node.
pub fn compile_node(trg: Target, code: &mut String, book: &hvm::Book, neo: &mut usize, tab: usize, def: &hvm::Def, a: hvm::Port) -> String {
  if a.is_nod() {
    let nd = &def.node[a.get_val() as usize];
    let p1 = compile_node(trg, code, book, neo, tab, def, nd.get_fst());
    let p2 = compile_node(trg, code, book, neo, tab, def, nd.get_snd());
    code.push_str(&format!("{}node_create(net, n{:x}, new_pair({},{}));\n", indent(tab), a.get_val(), p1, p2));
    return format!("new_port({},n{:x})", compile_tag(trg, a.get_tag()), a.get_val());
  } else if a.is_var() {
    return format!("new_port(VAR,v{:x})", a.get_val());
  } else {
    return format!("new_port({},0x{:08x})", compile_tag(trg, a.get_tag()), a.get_val());
  }
}

// Compiles an atomic port.
//fn compile_atom(trg: Target, port: hvm::Port) -> String {
  //return format!("new_port({},0x{:08x})/*atom*/", compile_tag(trg, port.get_tag()), port.get_val());
//}

// Compiles a tag.
pub fn compile_tag(trg: Target, tag: hvm::Tag) -> &'static str {
  match tag {
    hvm::VAR => "VAR",
    hvm::REF => "REF",
    hvm::ERA => "ERA",
    hvm::LAM => "LAM",
    hvm::APP => "APP",
    hvm::DUP => "DUP",
    _ => unreachable!(),
  }
}

// Creates indentation.
pub fn indent(tab: usize) -> String {
  return "  ".repeat(tab);
}

// Generates a fresh name.
fn fresh(count: &mut usize) -> String {
  *count += 1;
  format!("k{}", count)
}
