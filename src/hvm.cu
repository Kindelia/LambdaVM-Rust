// HVM-CUDA: an Interaction Combinator evaluator in CUDA.
// 
// # Format
// 
// An HVM net is a graph with 8 node types:
// - *       ::= ERAser node.
// - #N      ::= NUMber node.
// - @def    ::= REFerence node.
// - x       ::= VARiable node.
// - (a b)   ::= CONstructor node.
// - {a b}   ::= DUPlicator node.
// - <+ a b> ::= OPErator node.
// - ?<a b>  ::= SWItch node.
// 
// Nodes form a tree-like structure in memory. For example:
// 
//     ((* x) {x (y y)})
// 
// Represents a tree with 3 CON nodes, 1 ERA node and 4 VAR nodes.
// 
// A net consists of a root tree, plus list of redexes. Example:
// 
//     (a b)
//     & (b a) ~ (x (y *)) 
//     & {y x} ~ @foo
// 
// The net above has a root and 2 redexes (in the shape `& A ~ B`).
// 
// # Interactions 
// 
// Redexes are reduced via *interaction rules*:
// 
// ## 0. LINK
// 
//     a ~ b
//     ------ LINK
//     a ~> b
//
// ## 1. CALL
// 
//     @foo ~ B
//     ---------------
//     deref(@foo) ~ B
// 
// ## 2. VOID
// 
//     * ~ *
//     -----
//     void
// 
// ## 3. ERAS
// 
//     * ~ (B1 B2)
//     -----------
//     * ~ B1
//     * ~ B2
//     
// ## 4. ANNI (https://i.imgur.com/ASdOzbg.png)
//
//     (A1 A2) ~ (B1 B2)
//     -----------------
//     A1 ~ B1
//     A2 ~ B2
//     
// ## 5. COMM (https://i.imgur.com/gyJrtAF.png)
// 
//     (A1 A2) ~ {B1 B2}
//     -----------------
//     {x y} ~ A1
//     {z w} ~ A2
//     (x z) ~ B1
//     (y w) ~ B2
// 
// ## 6. OPER
// 
//     #A ~ <+ B1 B2>
//     --------------
//     if B1 is #B:
//       #A+B ~ B2
//     else:
//       B1 ~ <+ #A B2>
//
// ## 7. SWIT
// 
//     #A ~ ?<B1 B2>
//     -------------
//     if A == 0:
//       B1 ~ (B2 *)
//     else:
//       B1 ~ (* (#A-1 B2))
// 
// # Interaction Table
// 
// | A\B |  VAR |  REF |  ERA |  NUM |  CON |  DUP |  OPR |  SWI |
// |-----|------|------|------|------|------|------|------|------|
// | VAR | LINK | CALL | LINK | LINK | LINK | LINK | LINK | LINK |
// | REF | CALL | VOID | VOID | VOID | CALL | CALL | CALL | CALL |
// | ERA | LINK | VOID | VOID | VOID | ERAS | ERAS | ERAS | ERAS |
// | NUM | LINK | VOID | VOID | VOID | ERAS | ERAS | OPER | CASE |
// | CON | LINK | CALL | ERAS | ERAS | ANNI | COMM | COMM | COMM |
// | DUP | LINK | CALL | ERAS | ERAS | COMM | ANNI | COMM | COMM |
// | OPR | LINK | CALL | ERAS | OPER | COMM | COMM | ANNI | COMM |
// | SWI | LINK | CALL | ERAS | CASE | COMM | COMM | COMM | ANNI |
// 
// # Definitions
// 
// A top-level definition is just a statically known closed net, also called a
// package. It is represented like a net, with a root and linked trees:
// 
//     @foo = (a b)
//     & @tic ~ (x a)
//     & @tac ~ (x b)
// 
// The statement above represents a definition, @foo, with the `(a b)` tree as
// the root, and two linked trees: `@tic ~ (x a)` and `@tac ~ (x b)`. When a
// REF is part of a redex, it expands to its complete value. For example:
// 
//     & @foo ~ ((* a) (* a))
// 
// Expands to:
// 
//     & (a0 b0) ~ ((* a) (* a))
//     & @tic ~ (x0 a0)
//     & @tac ~ (x0 b0)
// 
// As an optimization, `@foo ~ {a b}` and `@foo ~ *` will NOT expand; instead,
// it will copy or erase when it is safe to do so.
// 
// # Example Reduction
// 
// Consider the first example, which had 2 redexes. HVM is strongly confluent,
// thus, we can reduce them in any order, even in parallel, with no effect on
// the total work done. Below is its complete reduction:
// 
//     (a b) & (b a) ~ (x (y *)) & {y x} ~ @foo
//     ----------------------------------------------- ANNI
//     (a b) & b ~ x & a ~ (y *) & {y x} ~ @foo
//     ----------------------------------------------- COMM
//     (a b) & b ~ x & a ~ (y *) & y ~ @foo & x ~ @foo
//     ----------------------------------------------- LINK `y` and `x`
//     (a b) & b ~ @foo & a ~ (@foo *)
//     ----------------------------------------------- LINK `b` and `a`
//     ((@foo *) @foo)
//     ----------------------------------------------- CALL `@foo` (optional)
//     ((a0 b0) (a1 b1))
//     & @tic ~ (x0 a0) & @tac ~ (x0 b0)
//     & @tic ~ (x1 a1) & @tac ~ (x1 b1)
//     ----------------------------------------------- CALL `@tic` and `@tac`
//     ((a0 b0) (a1 b1))
//     & (k0 k0) ~ (x0 a0) & (k1 k1) ~ (x0 b0)
//     & (k2 k2) ~ (x1 a1) & (k3 k3) ~ (x1 b1)
//     ----------------------------------------------- ANNI (many in parallel)
//     ((a0 b0) (a1 b1))
//     & k0 ~ x0 & k0 ~ a0 & k1 ~ x0 & k1 ~ b0
//     & k2 ~ x1 & k2 ~ a1 & k3 ~ x1 & k3 ~ b1
//     ----------------------------------------------- LINK `kN`
//     ((a0 b0) (a1 b1))
//     & x0 ~ a0 & x0 ~ b0 & x1 ~ a1 & x1 ~ b1
//     ----------------------------------------------- LINK `xN`
//     ((a0 b0) (a1 b1)) & a0 ~ b0 & a1 ~ b1
//     ----------------------------------------------- LINK `aN`
//     ((b0 b0) (b1 b1))
// 
// # Memory Layout
// 
// An HVM-CUDA net includes a redex bag, a node buffer and a vars buffer:
//
//     LNet ::= { RBAG: [Pair], NODE: [Pair], VARS: [Port] }
// 
// A Pair consists of two Ports, representing a either a redex or a node:
// 
//     Pair ::= (Port, Port)
// 
// A Port consists of a tag and a value:
// 
//     Port ::= 3-bit tag + 13-bit val
// 
// There are 8 Tags:
// 
//     Tag ::=
//       | VAR ::= a variable
//       | REF ::= a reference
//       | ERA ::= an eraser
//       | NUM ::= numeric literal
//       | CON ::= a constructor
//       | DUP ::= a duplicator
//       | OPR ::= numeric binary op
//       | SWI ::= numeric switch
// 
// ## Memory Layout Example
// 
// Consider, again, the following net:
// 
//     (a b)
//     & (b a) ~ (x (y *)) 
//     & {y x} ~ @foo
// 
// In memory, it could be represented as, for example:
// 
// - RBAG | FST-TREE | SND-TREE
// - ---- | -------- | --------
// - 0800 | CON 0001 | CON 0002 // '& (b a) ~ (x (y *))'
// - 1800 | DUP 0005 | REF 0000 // '& {x y} ~ @foo'
// - ---- | -------- | --------
// - NODE | PORT-1   | PORT-2
// - ---- | -------- | --------
// - 0000 | CON 0001 |          // points to root node
// - 0001 | VAR 0000 | VAR 0001 // '(a b)' node (root)
// - 0002 | VAR 0001 | VAR 0000 // '(b a)' node
// - 0003 | VAR 0002 | CON 0004 // '(x (y *))' node
// - 0004 | VAR 0003 | DUP 0000 // '(y *)' node
// - 0005 | VAR 0003 | VAR 0002 // '{y x}' node
// - ---- | -------- | --------

#define INTERPRETED
//#define DEBUG

#include <stdint.h>
#include <stdio.h>

// Integers
// --------

typedef  uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef  int32_t i32;
typedef    float f32;
typedef   double f64;
typedef unsigned long long int u64;

// Configuration
// -------------

// Clocks per Second
const u64 S = 2520000000;

// Threads per Block
const u32 TPB_L2 = 8;
const u32 TPB    = 1 << TPB_L2;

// Blocks per GPU
const u32 BPG_L2 = 7;
const u32 BPG    = 1 << BPG_L2;

// Threads per GPU
const u32 TPG = TPB * BPG;

// Types
// -----

// Local Types
typedef u8  Tag;  // Tag  ::= 3-bit (rounded up to u8)
typedef u32 Val;  // Val  ::= 29-bit (rounded up to u32)
typedef u32 Port; // Port ::= Tag + Val (fits a u32)
typedef u64 Pair; // Pair ::= Port + Port (fits a u64)

// Rules
typedef u8 Rule; // Rule ::= 3-bit (rounded up to 8)

// Numbs
typedef u32 Numb; // Numb ::= 29-bit (rounded up to u32)

// Tags
const Tag VAR = 0x0; // variable
const Tag REF = 0x1; // reference
const Tag ERA = 0x2; // eraser
const Tag NUM = 0x3; // number
const Tag CON = 0x4; // constructor
const Tag DUP = 0x5; // duplicator
const Tag OPR = 0x6; // operator
const Tag SWI = 0x7; // switch

// Interaction Rule Values
const Rule LINK = 0x0;
const Rule CALL = 0x1;
const Rule VOID = 0x2;
const Rule ERAS = 0x3;
const Rule ANNI = 0x4;
const Rule COMM = 0x5;
const Rule OPER = 0x6;
const Rule SWIT = 0x7;

// Constants
const Port FREE = 0x00000000;
const Port ROOT = 0xFFFFFFF8;
const Port NONE = 0xFFFFFFFF;

// Numbers
const Tag SYM = 0x0;
const Tag U24 = 0x1;
const Tag I24 = 0x2;
const Tag F24 = 0x3;
const Tag ADD = 0x4;
const Tag SUB = 0x5;
const Tag MUL = 0x6;
const Tag DIV = 0x7;
const Tag REM = 0x8;
const Tag EQ  = 0x9;
const Tag NEQ = 0xA;
const Tag LT  = 0xB;
const Tag GT  = 0xC;
const Tag AND = 0xD;
const Tag OR  = 0xE;
const Tag XOR = 0xF;

// Thread Redex Bag Length
const u32 RLEN = 256;

// Thread Redex Bag
// It uses the same space to store two stacks:
// - HI: a high-priotity stack, for shrinking reductions
// - LO: a low-priority stack, for growing reductions
struct RBag {
  u32  hi_end;
  Pair hi_buf[RLEN];
  u32  lo_ini;
  u32  lo_end;
  Pair lo_buf[RLEN];
};

// Local Net
const u32 L_NODE_LEN = 0x2000;
const u32 L_VARS_LEN = 0x2000;
struct LNet {
  Pair node_buf[L_NODE_LEN];
  Port vars_buf[L_VARS_LEN];
};

// Global Net
const u32 G_NODE_LEN = 1 << 29; // max 536m nodes
const u32 G_VARS_LEN = 1 << 29; // max 536m vars
const u32 G_RBAG_LEN = TPB * BPG * RLEN * 2; // max 4m redexes
struct GNet {
  u32  rbag_use_A; // total rbag redex count (buffer A)
  u32  rbag_use_B; // total rbag redex count (buffer B)
  Pair rbag_buf_A[G_RBAG_LEN]; // global redex bag (buffer A)
  Pair rbag_buf_B[G_RBAG_LEN]; // global redex bag (buffer B)
  Pair node_buf[G_NODE_LEN]; // global node buffer
  Port vars_buf[G_VARS_LEN]; // global vars buffer
  u32  node_put[TPB*BPG];
  u32  vars_put[TPB*BPG];
  u32  fail; // failed last tick
  u32  glob; // global alloc mode
  u64  itrs; // interaction count
  u64  leak; // leak count
};

// View Net: includes both GNet and LNet
struct Net {
  i32   l_node_dif; // delta node space
  i32   l_vars_dif; // delta vars space
  Pair *l_node_buf; // local node buffer values
  Port *l_vars_buf; // local vars buffer values
  u32  *g_rbag_use_A; // global rbag count (active buffer)
  u32  *g_rbag_use_B; // global rbag count (inactive buffer)
  Pair *g_rbag_buf_A; // global rbag values (active buffer)
  Pair *g_rbag_buf_B; // global rbag values (inactive buffer)
  Pair *g_node_buf; // global node buffer values
  Port *g_vars_buf; // global vars buffer values
  u32  *g_node_put; // next global node allocation index
  u32  *g_vars_put; // next global vars allocation index
};

// Thread Memory
struct TM {
  u32  page; // page index
  u32  nput; // node alloc index
  u32  vput; // vars alloc index
  u32  itrs; // interactions
  u32  leak; // leaks
  bool glob; // global alloc mode
  u32  nloc[32]; // node allocs
  u32  vloc[32]; // vars allocs
  RBag rbag; // tmem redex bag
};

// Top-Level Definition
struct Def {
  char name[32];
  bool safe;
  u32  rbag_len;
  u32  node_len;
  u32  vars_len;
  Port root;
  Pair rbag_buf[32];
  Pair node_buf[32];
};

// Book of Definitions
struct Book {
  u32 defs_len;
  Def defs_buf[256];
};

// Static Book
__device__ Book BOOK;

// Debugger
// --------

struct Show {
  char x[13];
};

__device__ __host__ void put_u16(char* B, u16 val);
__device__ __host__ Show show_port(Port port);
__device__ Show show_rule(Rule rule);
__device__ void print_rbag(RBag* rbag);
__device__ __host__ void print_net(Net* net, u32, u32);
__device__ void pretty_print_port(Net* net, Port port);
__device__ void pretty_print_rbag(Net* net, RBag* rbag);

// Utils
// -----

__device__ inline u32 TID() {
  return threadIdx.x;
}

__device__ inline u32 BID() {
  return blockIdx.x;
}

__device__ inline u32 GID() {
  return TID() + BID() * blockDim.x;
}

__device__ __host__ inline u32 div(u32 a, u32 b) {
  return (a + b - 1) / b;
}

__device__ u32 push_index(u32 msk, u32 idx) {
  return msk | (1U << (31 - idx));
}

__device__ u32 pop_index(u32* msk) {
  u32 idx = __clz(*msk);
  *msk &= ~(1U << (31 - idx));
  return idx;
}

// Port: Constructor and Getters
// -----------------------------

__device__ __host__ inline Port new_port(Tag tag, Val val) {
  return (val << 3) | tag;
}

__device__ __host__ inline Tag get_tag(Port port) {
  return port & 7;
}

__device__ __host__ inline Val get_val(Port port) {
  return port >> 3;
}

// Pair: Constructor and Getters
// -----------------------------

__device__ __host__ inline Pair new_pair(Port fst, Port snd) {
  return ((u64)snd << 32) | fst;
}

__device__ __host__ inline Port get_fst(Pair pair) {
  return pair & 0xFFFFFFFF;
}

__device__ __host__ inline Port get_snd(Pair pair) {
  return pair >> 32;
}

// Utils
// -----

// Swaps two ports.
__device__ __host__ inline void swap(Port *a, Port *b) {
  Port x = *a; *a = *b; *b = x;
}

// Transposes an index over a matrix.
__device__ u32 transpose(u32 idx, u32 width, u32 height) {
  u32 old_row = idx / width;
  u32 old_col = idx % width;
  u32 new_row = old_col % height;
  u32 new_col = old_col / height + old_row * (width / height);
  return new_row * width + new_col;
}

// Returns true if all 'x' are true, block-wise
__device__ __noinline__ bool block_all(bool x) {
  __shared__ bool res;
  if (TID() == 0) res = true;
  __syncthreads();
  if (!x) res = false;
  __syncthreads();
  return res;
}

// Returns true if any 'x' is true, block-wise
__device__ __noinline__ bool block_any(bool x) {
  __shared__ bool res;
  if (TID() == 0) res = false;
  __syncthreads();
  if (x) res = true;
  __syncthreads();
  return res;
}

// Returns the sum of a value, block-wise
template <typename A>
__device__ __noinline__ A block_sum(A x) {
  __shared__ A res;
  if (TID() == 0) res = 0;
  __syncthreads();
  atomicAdd(&res, x);
  __syncthreads();
  return res;
}

// Returns the sum of a boolean, block-wise
__device__ __noinline__ u32 block_count(bool x) {
  __shared__ u32 res;
  if (TID() == 0) res = 0;
  __syncthreads();
  atomicAdd(&res, x);
  __syncthreads();
  return res;
}

// Prints a 4-bit value for each thread in a block
__device__ void block_print(u32 x) {
  __shared__ u8 value[TPB];

  value[TID()] = x;
  __syncthreads();

  if (TID() == 0) {
    for (u32 i = 0; i < TPB; ++i) {
      printf("%x", min(value[i],0xF));
    }
  }
  __syncthreads();
}


// Ports / Pairs / Rules
// ---------------------

// True if this port has a pointer to a node.
__device__ __host__ inline bool is_nod(Port a) {
  return get_tag(a) >= CON;
}

// True if this port is a variable.
__device__ __host__ inline bool is_var(Port a) {
  return get_tag(a) == VAR;
}

// True if this port is a local node/var (that can leak).
__device__ __host__ inline bool is_local(Port a) {
  return (is_nod(a) || is_var(a)) && get_val(a) < L_NODE_LEN;
}

// True if this port is a global node/var (that can be leaked into).
__device__ __host__ inline bool is_global(Port a) {
  return (is_nod(a) || is_var(a)) && get_val(a) >= L_NODE_LEN;
}

// Given two tags, gets their interaction rule. Uses a u64mask lookup table.
__device__ __host__ inline Rule get_rule(Port A, Port B) {
  const u64 x = 0b0111111010110110110111101110111010110000111100001111000100000010;
  const u64 y = 0b0000110000001100000011100000110011111110111111100010111000000000;
  const u64 z = 0b1111100011111000111100001111000011000000000000000000000000000000;
  const u64 i = ((u64)get_tag(A) << 3) | (u64)get_tag(B);
  return (Rule)((x>>i&1) | (y>>i&1)<<1 | (z>>i&1)<<2);
}

// Same as above, but receiving a pair.
__device__ __host__ inline Rule get_pair_rule(Pair AB) {
  return get_rule(get_fst(AB), get_snd(AB));
}

// Should we swap ports A and B before reducing this rule?
__device__ __host__ inline bool should_swap(Port A, Port B) {
  return get_tag(B) < get_tag(A);
}
// Gets a rule's priority
__device__ __host__ inline bool is_high_priority(Rule rule) {
  return (bool)((0b00011101 >> rule) & 1);
}

// Adjusts a newly allocated port.
__device__ inline Port adjust_port(Net* net, TM* tm, Port port) {
  Tag tag = get_tag(port);
  Val val = get_val(port);
  if (is_nod(port)) return new_port(tag, tm->nloc[val]);
  if (is_var(port)) return new_port(tag, tm->vloc[val]);
  return new_port(tag, val);
}

// Adjusts a newly allocated pair.
__device__ inline Pair adjust_pair(Net* net, TM* tm, Pair pair) {
  Port p1 = adjust_port(net, tm, get_fst(pair));
  Port p2 = adjust_port(net, tm, get_snd(pair));
  return new_pair(p1, p2);
}

// Words
// -----

// Constructor and getters for SYM (operation selector)
__device__ inline Numb new_sym(u32 val) {
  return ((val & 0xF) << 4) | SYM;
}

__device__ inline u32 get_sym(Numb word) {
  return (word >> 4) & 0xF;
}

// Constructor and getters for U24 (unsigned 24-bit integer)
__device__ inline Numb new_u24(u32 val) {
  return ((val & 0xFFFFFF) << 4) | U24;
}

__device__ inline u32 get_u24(Numb word) {
  return (word >> 4) & 0xFFFFFF;
}

// Constructor and getters for I24 (signed 24-bit integer)
__device__ inline Numb new_i24(i32 val) {
  return (((u32)val << 4) & 0xFFFFFF) | I24;
}

__device__ inline i32 get_i24(Numb word) {
  return (((word >> 4) & 0xFFFFFF) << 8) >> 8;
}

// Constructor and getters for F24 (24-bit float)
__device__ inline Numb new_f24(f32 val) {
  u32 bits = *(u32*)&val;
  u32 sign = (bits >> 31) & 0x1;
  i32 expo = ((bits >> 23) & 0xFF) - 127;
  u32 mant = bits & 0x7FFFFF;
  u32 uexp = expo + 63;
  u32 bts1 = (sign << 23) | (uexp << 16) | (mant >> 7);
  return (bts1 << 4) | F24;
}

__device__ inline f32 get_f24(Numb word) {
  u32 bits = (word >> 4) & 0xFFFFFF;
  u32 sign = (bits >> 23) & 0x1;
  u32 expo = (bits >> 16) & 0x7F;
  u32 mant = bits & 0xFFFF;
  i32 iexp = expo - 63;
  u32 bts0 = (sign << 31) | ((iexp + 127) << 23) | (mant << 7);
  u32 bts1 = (mant == 0 && iexp == -63) ? (sign << 31) : bts0;
  return *(f32*)&bts1;
}

// Flip flag
__device__ inline Tag get_typ(Numb word) {
  return word & 0xF;
}

__device__ inline bool get_flp(Numb word) {
  return ((word >> 29) & 1) == 1;
}

__device__ inline Numb set_flp(Numb word) {
  return word | 0x10000000;
}

__device__ inline Numb flp_flp(Numb word) {
  return word ^ 0x10000000;
}

// Partial application
__device__ inline Numb partial(Numb a, Numb b) {
  return b & 0xFFFFFFF0 | get_sym(a);
}

// Operate function
__device__ inline Numb operate(Numb a, Numb b) {
  if (get_flp(a) ^ get_flp(b)) {
    Numb t = a; a = b; b = t;
  }
  Tag at = get_typ(a);
  Tag bt = get_typ(b);
  if (at == SYM && bt == SYM) {
    return new_u24(0);
  }
  if (at == SYM && bt != SYM) {
    return partial(a, b);
  }
  if (at != SYM && bt == SYM) {
    return partial(b, a);
  }
  if (at >= ADD && bt >= ADD) {
    return new_u24(0);
  }
  if (at < ADD && bt < ADD) {
    return new_u24(0);
  }
  Tag op = (at >= ADD) ? at : bt;
  Tag ty = (at >= ADD) ? bt : at;
  switch (ty) {
    case U24: {
      u32 av = get_u24(a);
      u32 bv = get_u24(b);
      switch (op) {
        case ADD: return new_u24(av + bv);
        case SUB: return new_u24(av - bv);
        case MUL: return new_u24(av * bv);
        case DIV: return new_u24(av / bv);
        case REM: return new_u24(av % bv);
        case EQ:  return new_u24(av == bv);
        case NEQ: return new_u24(av != bv);
        case LT:  return new_u24(av < bv);
        case GT:  return new_u24(av > bv);
        case AND: return new_u24(av & bv);
        case OR:  return new_u24(av | bv);
        case XOR: return new_u24(av ^ bv);
        default:  return new_u24(0);
      }
    }
    case I24: {
      i32 av = get_i24(a);
      i32 bv = get_i24(b);
      switch (op) {
        case ADD: return new_i24(av + bv);
        case SUB: return new_i24(av - bv);
        case MUL: return new_i24(av * bv);
        case DIV: return new_i24(av / bv);
        case REM: return new_i24(av % bv);
        case EQ:  return new_i24(av == bv);
        case NEQ: return new_i24(av != bv);
        case LT:  return new_i24(av < bv);
        case GT:  return new_i24(av > bv);
        case AND: return new_i24(av & bv);
        case OR:  return new_i24(av | bv);
        case XOR: return new_i24(av ^ bv);
        default:  return new_i24(0);
      }
    }
    case F24: {
      f32 av = get_f24(a);
      f32 bv = get_f24(b);
      switch (op) {
        case ADD: return new_f24(av + bv);
        case SUB: return new_f24(av - bv);
        case MUL: return new_f24(av * bv);
        case DIV: return new_f24(av / bv);
        case REM: return new_f24(fmodf(av, bv));
        case EQ:  return new_u24(av == bv);
        case NEQ: return new_u24(av != bv);
        case LT:  return new_u24(av < bv);
        case GT:  return new_u24(av > bv);
        case AND: return new_f24(atan2f(av, bv));
        case OR:  return new_f24(logf(bv) / logf(av));
        case XOR: return new_f24(powf(av, bv));
        default:  return new_f24(0);
      }
    }
    default: return new_u24(0);
  }
}

// RBag
// ----

__device__ RBag rbag_new() {
  RBag rbag;
  rbag.hi_end = 0;
  rbag.lo_ini = 0;
  rbag.lo_end = 0;
  return rbag;
}

__device__ void push_redex(TM* tm, Pair redex) {
  Rule rule = get_pair_rule(redex);
  if (is_high_priority(rule)) {
    #ifdef DEBUG
    if (tm->rbag.lo_end - tm->rbag.lo_ini >= RLEN) printf("[%04x] ERR PUSH_REDEX A %d\n", GID());
    #endif
    tm->rbag.hi_buf[tm->rbag.hi_end++ % RLEN] = redex;
  } else {
    #ifdef DEBUG
    if (tm->rbag.lo_end - tm->rbag.lo_ini >= RLEN) printf("[%04x] ERR PUSH_REDEX A\n", GID());
    #endif
    tm->rbag.lo_buf[tm->rbag.lo_end++ % RLEN] = redex;
  }
}

__device__ Pair pop_redex(TM* tm) {
  if (tm->rbag.hi_end > 0) {
    #ifdef DEBUG
    if (tm->rbag.hi_end == 0) printf("[%04x] ERR POP_REDEX A\n", GID());
    #endif
    return tm->rbag.hi_buf[(--tm->rbag.hi_end) % RLEN];
  } else if (tm->rbag.lo_end - tm->rbag.lo_ini > 0) {
    #ifdef DEBUG
    if (tm->rbag.lo_end == tm->rbag.lo_ini) printf("[%04x] ERR POP_REDEX B\n", GID());
    #endif
    return tm->rbag.lo_buf[(--tm->rbag.lo_end) % RLEN];
  } else {
    return 0; // FIXME: is this ok?
  }
}

__device__ u32 rbag_len(RBag* rbag) {
  return rbag->hi_end + rbag->lo_end - rbag->lo_ini;
}

__device__ u32 rbag_has_highs(RBag* rbag) {
  return rbag->hi_end > 0;
}

// TM
// --

__device__ TM tmem_new() {
  TM tm;
  tm.rbag = rbag_new();
  tm.nput = 1;
  tm.vput = 1;
  tm.itrs = 0;
  tm.leak = 0;
  return tm;
}

// Net
// ----

__device__ Net vnet_new(GNet* gnet, void* smem, u32 turn) {
  Net net;
  net.l_node_dif   = 0;
  net.l_vars_dif   = 0;
  net.l_node_buf   = ((LNet*)smem)->node_buf;
  net.l_vars_buf   = ((LNet*)smem)->vars_buf;
  net.g_rbag_use_A = turn % 2 == 0 ? &gnet->rbag_use_A : &gnet->rbag_use_B;
  net.g_rbag_use_B = turn % 2 == 0 ? &gnet->rbag_use_B : &gnet->rbag_use_A;
  net.g_rbag_buf_A = turn % 2 == 0 ? gnet->rbag_buf_A : gnet->rbag_buf_B;
  net.g_rbag_buf_B = turn % 2 == 0 ? gnet->rbag_buf_B : gnet->rbag_buf_A;
  net.g_node_buf   = gnet->node_buf;
  net.g_vars_buf   = gnet->vars_buf;
  net.g_node_put   = &gnet->node_put[GID()];
  net.g_vars_put   = &gnet->vars_put[GID()];
  return net;
}

// Stores a new node on global.
__device__ inline void node_create(Net* net, u32 loc, Pair val) {
  Pair old;
  if (loc < L_NODE_LEN) {
    net->l_node_dif += 1;
    old = atomicExch(&net->l_node_buf[loc], val);
  } else {
    old = atomicExch(&net->g_node_buf[loc], val);
  }
  #ifdef DEBUG
  if (old != 0) printf("[%04x] ERR NODE_CREATE | %04x\n", GID(), loc);
  #endif
}

// Stores a var on global.
__device__ inline void vars_create(Net* net, u32 var, Port val) {
  Port old;
  if (var < L_VARS_LEN) {
    net->l_vars_dif += 1;
    old = atomicExch(&net->l_vars_buf[var], val);
  } else {
    old = atomicExch(&net->g_vars_buf[var], val);
  }
  #ifdef DEBUG
  if (old != 0) printf("[%04x] ERR VARS_CREATE | %04x\n", GID(), var);
  #endif
}

// Reads a node from global.
__device__ __host__ inline Pair node_load(Net* net, u32 loc) {
  Pair got;
  if (loc < L_NODE_LEN) {
    got = net->l_node_buf[loc];
  } else {
    got = net->g_node_buf[loc];
  }
  return got;
}

// Reads a var from global.
__device__ __host__ inline Port vars_load(Net* net, u32 var) {
  Port got;
  if (var < L_VARS_LEN) {
    got = net->l_vars_buf[var];
  } else {
    got = net->g_vars_buf[var];
  }
  return got;
}

// Exchanges a node on global by a value. Returns old.
__device__ inline Pair node_exchange(Net* net, u32 loc, Pair val) {
  Pair got = 0;
  if (loc < L_NODE_LEN) {
    got = atomicExch(&net->l_node_buf[loc], val);
  } else {
    got = atomicExch(&net->g_node_buf[loc], val);
  }
  #ifdef DEBUG
  if (got == 0) printf("[%04x] ERR NODE_EXCHANGE | %04x\n", GID(), loc);
  #endif
  return got;
}

// Exchanges a var on global by a value. Returns old.
__device__ inline Port vars_exchange(Net* net, u32 var, Port val) {
  Port got = 0;
  if (var < L_VARS_LEN) {
    got = atomicExch(&net->l_vars_buf[var], val);
  } else {
    got = atomicExch(&net->g_vars_buf[var], val);
  }
  #ifdef DEBUG
  if (got == 0) printf("[%04x] ERR VARS_EXCHANGE | %04x\n", GID(), var);
  #endif
  return got;
}

// Takes a node.
__device__ inline Pair node_take(Net* net, u32 loc) {
  Pair got = 0;
  if (loc < L_NODE_LEN) {
    net->l_node_dif -= 1;
    got = atomicExch(&net->l_node_buf[loc], 0);
  } else {
    got = atomicExch(&net->g_node_buf[loc], 0);
  }
  #ifdef DEBUG
  if (got == 0) printf("[%04x] ERR NODE_TAKE | %04x\n", GID(), loc);
  #endif
  return got;
}

// Takes a var.
__device__ inline Port vars_take(Net* net, u32 var) {
  Port got = 0;
  if (var < L_VARS_LEN) {
    net->l_vars_dif -= 1;
    got = atomicExch(&net->l_vars_buf[var], 0);
  } else {
    got = atomicExch(&net->g_vars_buf[var], 0);
  }
  #ifdef DEBUG
  if (got == 0) printf("[%04x] ERR VARS_TAKE | %04x\n", GID(), var); asm("trap;"); }
  #endif
  return got;
}

// GNet
// ----

// Initializes a Global Net.
__global__ void gnet_init(GNet* gnet) {
  // Creates root variable.
  gnet->vars_buf[get_val(ROOT)] = NONE;
}

// Allocator
// ---------

template <typename A>
__device__ u32 g_alloc_1(Net* net, TM* tm, u32* g_put, A* g_buf) {
  while (true) {
    //u32 lc = BID()*(G_NODE_LEN/BPG) + (*g_put*TPB+TID()) % (G_NODE_LEN/BPG);
    //u32 lc = (GID() + (*g_put * TPG)) % G_NODE_LEN;
    u32 lc = GID()*(G_NODE_LEN/TPG) + (*g_put%(G_NODE_LEN/TPG)); // 9 GIPS | 2.8 GIPS
    A elem = g_buf[lc];
    *g_put += 1;
    if (lc >= L_NODE_LEN && elem == 0) {
      return lc;
    }
    // FIXME: check OOM (without dropping performance)
  }
}

template <typename A>
__device__ u32 g_alloc(Net* net, TM* tm, u32* ret, u32* g_put, A* g_buf, u32 num) {
  u32 got = 0;
  while (got < num) {
    u32 lc = GID()*(G_NODE_LEN/TPG) + (*g_put%(G_NODE_LEN/TPG)); // 9 GIPS | 2.8 GIPS
    A elem = g_buf[lc];
    *g_put += 1;
    if (lc >= L_NODE_LEN && elem == 0) {
      ret[got++] = lc;
    }
    // FIXME: check OOM (without dropping performance)
  }
  return got;

}

template <typename A>
__device__ u32 l_alloc(Net* net, TM* tm, u32* ret, u32* l_put, A* l_buf, u32 num) {
  u32 got = 0;
  u32 lps = 0;
  while (got < num) {
    u32 lc = ((*l_put)++ * TPB) % L_NODE_LEN + TID();
    A elem = l_buf[lc];
    if (++lps >= L_NODE_LEN/TPB) {
      break;
    }
    if (lc > 0 && elem == 0) {
      ret[got++] = lc;
    }
  }
  return got;
}

template <typename A>
__device__ u32 l_alloc_1(Net* net, TM* tm, u32* ret, u32* l_put, A* l_buf, u32* lps) {
  u32 got = 0;
  while (true) {
    u32 lc = ((*l_put)++ * TPB) % L_NODE_LEN + TID();
    A elem = l_buf[lc];
    if (++(*lps) >= L_NODE_LEN/TPB) {
      break;
    }
    if (lc > 0 && elem == 0) {
      return lc;
    }
  }
  return got;
}

__device__ u32 g_node_alloc_1(Net* net, TM* tm) {
  return g_alloc_1(net, tm, net->g_node_put, net->g_node_buf);
}

__device__ u32 g_vars_alloc_1(Net* net, TM* tm) {
  return g_alloc_1(net, tm, net->g_vars_put, net->g_vars_buf);
}

__device__ u32 g_node_alloc(Net* net, TM* tm, u32 num) {
  return g_alloc(net, tm, tm->nloc, net->g_node_put, net->g_node_buf, num);
}

__device__ u32 g_vars_alloc(Net* net, TM* tm, u32 num) {
  return g_alloc(net, tm, tm->vloc, net->g_vars_put, net->g_vars_buf, num);
}

__device__ u32 l_node_alloc(Net* net, TM* tm, u32 num) {
  return l_alloc(net, tm, tm->nloc, &tm->nput, net->l_node_buf, num);
}

__device__ u32 l_vars_alloc(Net* net, TM* tm, u32 num) {
  return l_alloc(net, tm, tm->vloc, &tm->vput, net->l_vars_buf, num);
}

__device__ u32 l_node_alloc_1(Net* net, TM* tm, u32* lps) {
  return l_alloc_1(net, tm, tm->nloc, &tm->nput, net->l_node_buf, lps);
}

__device__ u32 l_vars_alloc_1(Net* net, TM* tm, u32* lps) {
  return l_alloc_1(net, tm, tm->vloc, &tm->vput, net->l_vars_buf, lps);
}

__device__ u32 node_alloc_1(Net* net, TM* tm, u32* lps) {
  if (tm->glob) {
    return l_node_alloc_1(net, tm, lps);
  } else {
    return g_node_alloc_1(net, tm);
  }
}

__device__ u32 vars_alloc_1(Net* net, TM* tm, u32* lps) {
  if (tm->glob) {
    return l_vars_alloc_1(net, tm, lps);
  } else {
    return g_vars_alloc_1(net, tm);
  }
}

// Linking
// -------

// Finds a variable's value.
__device__ inline Port enter(Net* net, TM* tm, Port var) {
  // While `B` is VAR: extend it (as an optimization)
  while (get_tag(var) == VAR) {
    // Takes the current `var` substitution as `val`
    Port val = vars_exchange(net, get_val(var), NONE);
    // If there was no `val`, stop, as there is no extension
    if (val == NONE) {
      break;
    }
    // Otherwise, delete `B` (we own both) and continue
    vars_take(net, get_val(var));
    var = val;
  }
  return var;
}

// Atomically Links `A ~ B`.
__device__ void link(Net* net, TM* tm, Port A, Port B) {
  Port INI_A = A;
  Port INI_B = B;

  // Attempts to directionally point `A ~> B`
  while (true) {

    // If `A` is NODE: swap `A` and `B`, and continue
    if (get_tag(A) != VAR && get_tag(B) == VAR) {
      Port X = A; A = B; B = X;
    }

    // If `A` is NODE: create the `A ~ B` redex
    if (get_tag(A) != VAR) {
      //printf("[%04x] new redex A %s ~ %s\n", GID(), show_port(A).x, show_port(B).x);
      push_redex(tm, new_pair(A, B)); // TODO: move global ports to local
      break;
    }

    // While `B` is VAR: extend it (as an optimization)
    B = enter(net, tm, B);

    // Since `A` is VAR: point `A ~> B`.
    if (true) {
      // If B would leak...
      if (is_global(A) && is_local(B)) {
        // If B is a var, just swap it
        if (is_var(B)) {
          Port X = A; A = B; B = X;
          continue;
        }
        // If B is a nod, create a leak interaction
        if (is_nod(B)) {
          //if (!TID()) printf("[%04x] NODE LEAK %s ~ %s\n", GID(), show_port(A).x, show_port(B).x);
          push_redex(tm, new_pair(A, B));
          break;
        }
      }

      // Stores `A -> B`, taking the current `A` subst as `A'`
      Port A_ = vars_exchange(net, get_val(A), B);

      // If there was no `A'`, stop, as we lost B's ownership
      if (A_ == NONE) {
        break;
      }

      #ifdef DEBUG
      if (A_ == 0) printf("[%04x] ERR LINK %s ~ %s | %s ~ %s\n", GID() show_port(INI_A).x, show_port(INI_B).x, show_port(A).x, show_port(B).x);
      #endif

      // Otherwise, delete `A` (we own both) and link `A' ~ B`
      vars_take(net, get_val(A));
      A = A_;
    }
  }
}

// Links `A ~ B` (as a pair).
__device__ void link_pair(Net* net, TM* tm, Pair AB) {
  link(net, tm, get_fst(AB), get_snd(AB));
}

// Sharing
// -------

// Sends redex to a friend local thread, when it is starving.
// FIXME: the way this is done will drop redexes if TPB<5
__device__ void share_redexes(TM* tm) {
  __shared__ Pair pool[TPB];
  Pair send, recv;
  u32*  ini = &tm->rbag.lo_ini;
  u32*  end = &tm->rbag.lo_end;
  Pair* bag = tm->rbag.lo_buf;
  for (u32 off = 1; off < 32; off *= 2) {
    send = (*end - *ini) > 1 ? bag[*ini%RLEN] : 0;
    recv = __shfl_xor_sync(__activemask(), send, off);
    if (!send &&  recv) bag[((*end)++)%RLEN] = recv;
    if ( send && !recv) ++(*ini);
  }
  for (u32 off = 32; off < TPB; off *= 2) {
    u32 a = TID();
    u32 b = a ^ off;
    send = (*end - *ini) > 1 ? bag[*ini%RLEN] : 0;
    pool[a] = send;
    __syncthreads();
    recv = pool[b];
    if (!send &&  recv) bag[((*end)++)%RLEN] = recv;
    if ( send && !recv) ++(*ini);
  }
}

// Resources
// ---------

// Gets the necessary resources for an interaction.
__device__ bool get_resources(Net* net, TM* tm, u8 need_rbag, u8 need_node, u8 need_vars) {
  u32 got_rbag = min(RLEN - (tm->rbag.lo_end - tm->rbag.lo_ini), RLEN - tm->rbag.hi_end);
  u32 got_node;
  u32 got_vars;
  if (tm->glob) {
    got_node = g_node_alloc(net, tm, need_node);
    got_vars = g_vars_alloc(net, tm, need_vars);
  } else {
    got_node = l_node_alloc(net, tm, need_node);
    got_vars = l_vars_alloc(net, tm, need_vars);
  }
  return got_rbag >= need_rbag && got_node >= need_node && got_vars >= need_vars;
}

// Interactions
// ------------

// The Link Interaction.
__device__ bool interact_link(Net* net, TM* tm, Port a, Port b) {
  // If A is a global var and B is a local node, leak it:
  // ^A ~ (b1 b2)
  // ------------- LEAK-NODE
  // ^X ~ b1
  // ^Y ~ b2
  // ^A ~ ^(^X ^Y)
  if (is_global(a) && is_nod(b) && is_local(b)) {
    // Allocates needed nodes and vars.
    if (!get_resources(net, tm, 3, 0, 0)) {
      return false;
    }

    tm->leak += 1;

    // Loads ports.
    Pair l_b  = node_take(net, get_val(b));
    Port l_b1 = enter(net, tm, get_fst(l_b));
    Port l_b2 = enter(net, tm, get_snd(l_b));

    // Leaks port 1.
    Port g_b1;
    if (is_local(l_b1)) {
      g_b1 = new_port(VAR, g_vars_alloc_1(net, tm));
      vars_create(net, get_val(g_b1), NONE);
      link_pair(net, tm, new_pair(g_b1, l_b1));
    } else {
      g_b1 = l_b1;
    }

    // Leaks port 2.
    Port g_b2;
    if (is_local(l_b2)) {
      g_b2 = new_port(VAR, g_vars_alloc_1(net, tm));
      vars_create(net, get_val(g_b2), NONE);
      link_pair(net, tm, new_pair(g_b2, l_b2));
    } else {
      g_b2 = l_b2;
    }

    // Leaks node.
    Port g_b = new_port(get_tag(b), g_node_alloc_1(net, tm));
    node_create(net, get_val(g_b), new_pair(g_b1, g_b2));
    link_pair(net, tm, new_pair(a, g_b));

    return true;

  // Otherwise, just perform a normal link.
  } else {
    // Allocates needed nodes and vars.
    if (!get_resources(net, tm, 1, 0, 0)) {
      return false;
    }

    link_pair(net, tm, new_pair(a, b));
  }

  return true;
}

// The Call Interaction.
#ifdef COMPILED
///COMPILED_INTERACT_CALL///
#else
__device__ bool interact_eras(Net* net, TM* tm, Port a, Port b);
__device__ bool interact_call(Net* net, TM* tm, Port a, Port b) {
  // Loads Definition.
  u32 fid  = get_val(a);
  Def* def = &BOOK.defs_buf[fid];

  // Copy Optimization.
  if (def->safe && get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }

  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, def->rbag_len + 1, def->node_len, def->vars_len)) {
    return false;
  }

  // Stores new vars.
  for (u32 i = 0; i < def->vars_len; ++i) {
    vars_create(net, tm->vloc[i], NONE);
  }

  // Stores new nodes.
  for (u32 i = 0; i < def->node_len; ++i) {
    node_create(net, tm->nloc[i], adjust_pair(net, tm, def->node_buf[i]));
  }

  // Links.
  for (u32 i = 0; i < def->rbag_len; ++i) {
    link_pair(net, tm, adjust_pair(net, tm, def->rbag_buf[i]));
  }
  link_pair(net, tm, new_pair(adjust_port(net, tm, def->root), b));

  return true;
}
#endif

// The Void Interaction.
__device__ bool interact_void(Net* net, TM* tm, Port a, Port b) {
  return true;
}

// The Eras Interaction.
__device__ bool interact_eras(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    return false;
  }

  // Loads ports.
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links.
  link_pair(net, tm, new_pair(a, B1));
  link_pair(net, tm, new_pair(a, B2));

  return true;
}

// The Anni Interaction.
__device__ bool interact_anni(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    return false;
  }

  // Loads ports.
  Pair A  = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links.
  link_pair(net, tm, new_pair(A1, B1));
  link_pair(net, tm, new_pair(A2, B2));

  return true;
}

// The Comm Interaction.
__device__ bool interact_comm(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 4, 4, 4)) {
    return false;
  }

  // Loads ports.
  Pair A  = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new vars.
  vars_create(net, tm->vloc[0], NONE);
  vars_create(net, tm->vloc[1], NONE);
  vars_create(net, tm->vloc[2], NONE);
  vars_create(net, tm->vloc[3], NONE);

  // Stores new nodes.
  node_create(net, tm->nloc[0], new_pair(new_port(VAR, tm->vloc[0]), new_port(VAR, tm->vloc[1])));
  node_create(net, tm->nloc[1], new_pair(new_port(VAR, tm->vloc[2]), new_port(VAR, tm->vloc[3])));
  node_create(net, tm->nloc[2], new_pair(new_port(VAR, tm->vloc[0]), new_port(VAR, tm->vloc[2])));
  node_create(net, tm->nloc[3], new_pair(new_port(VAR, tm->vloc[1]), new_port(VAR, tm->vloc[3])));

  // Links.
  link_pair(net, tm, new_pair(new_port(get_tag(b), tm->nloc[0]), A1));
  link_pair(net, tm, new_pair(new_port(get_tag(b), tm->nloc[1]), A2));
  link_pair(net, tm, new_pair(new_port(get_tag(a), tm->nloc[2]), B1));
  link_pair(net, tm, new_pair(new_port(get_tag(a), tm->nloc[3]), B2));

  return true;
}

// The Oper Interaction.
__device__ bool interact_oper(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 1, 0)) {
    return false;
  }

  // Loads ports.
  Val  av = get_val(a);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = enter(net, tm, get_snd(B));
    
  // Performs operation.
  if (get_tag(B1) == NUM) {
    Val  bv = get_val(B1);
    Numb cv = operate(av, bv);
    link_pair(net, tm, new_pair(new_port(NUM, cv), B2));
  } else {
    node_create(net, tm->nloc[0], new_pair(new_port(get_tag(a), flp_flp(av)), B2));
    link_pair(net, tm, new_pair(B1, new_port(OPR, tm->nloc[0])));
  }


  return true;
}

// The Swit Interaction.
__device__ bool interact_swit(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 2, 0)) {
    return false;
  }

  // Loads ports.
  u32  av = get_u24(get_val(a));
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new nodes.
  if (av == 0) {
    node_create(net, tm->nloc[0], new_pair(B2, new_port(ERA,0)));
    link_pair(net, tm, new_pair(new_port(CON, tm->nloc[0]), B1));
  } else {
    node_create(net, tm->nloc[0], new_pair(new_port(ERA,0), new_port(CON, tm->nloc[1])));
    node_create(net, tm->nloc[1], new_pair(new_port(NUM, new_u24(av-1)), B2));
    link_pair(net, tm, new_pair(new_port(CON, tm->nloc[0]), B1));
  }

  return true;
}

// Pops a local redex and performs a single interaction.
__device__ bool interact(Net* net, TM* tm, u32 turn) {
  // Pops a redex.
  Pair redex = pop_redex(tm);

  // Gets redex ports A and B.
  Port a = get_fst(redex);
  Port b = get_snd(redex);

  // Gets the rule type.
  Rule rule = get_rule(a, b);

  // If there is no redex, stop.
  if (redex != 0) {
    //printf("[%04x] REDUCE %s ~ %s | %s\n", GID(), show_port(a).x, show_port(b).x, show_rule(rule).x);

    // Used for root redex.
    if (get_tag(a) == REF && b == ROOT) {
      rule = CALL;
    // Swaps ports if necessary.
    } else if (should_swap(a,b)) {
      swap(&a, &b);
    }

    // Dispatches interaction rule.
    bool success;
    switch (rule) {
      case LINK: success = interact_link(net, tm, a, b); break;
      case CALL: success = interact_call(net, tm, a, b); break;
      case VOID: success = interact_void(net, tm, a, b); break;
      case ERAS: success = interact_eras(net, tm, a, b); break;
      case ANNI: success = interact_anni(net, tm, a, b); break;
      case COMM: success = interact_comm(net, tm, a, b); break;
      case OPER: success = interact_oper(net, tm, a, b); break;
      case SWIT: success = interact_swit(net, tm, a, b); break;
    }

    // If error, pushes redex back.
    if (!success) {
      push_redex(tm, redex);
      return false;
    // Else, increments the interaction count.
    } else if (rule != LINK) {
      tm->itrs += 1;
    }
  }

  return true;
}

// RBag Save/Load
// --------------

// Moves redexes from shared memory to global bag
__device__ void save_redexes(Net* net, TM *tm, u32 turn) {
  // Target bag index
  u32 bag = transpose(GID(), TPB, BPG);

  // Next redex index
  u32 idx = 0;

  //printf("[%04x] saving: lo=%d hi=%d tot=%d\n", GID(), tm->rbag.lo_end - tm->rbag.lo_ini, tm->rbag.hi_end, rbag_len(&tm->rbag));

  // Leaks low-priority redexes
  while (tm->rbag.lo_end > tm->rbag.lo_ini) {
    Pair R = tm->rbag.lo_buf[(--tm->rbag.lo_end) % RLEN];
    Port x = get_fst(R);
    Port y = get_snd(R);
    Port X = new_port(VAR, g_vars_alloc_1(net, tm));
    Port Y = new_port(VAR, g_vars_alloc_1(net, tm));
    vars_create(net, get_val(X), NONE);
    vars_create(net, get_val(Y), NONE);
    link_pair(net, tm, new_pair(X, x));
    link_pair(net, tm, new_pair(Y, y));
    net->g_rbag_buf_B[bag * RLEN + (idx++)] = new_pair(X, Y);
  }
  __syncthreads();

  // Executes all high-priority redexes
  while (rbag_has_highs(&tm->rbag)) {
    if (!interact(net, tm, turn)) {
      printf("ERROR: failed to clear high-priority redexes");
    }
  }
  __syncthreads();

  #ifdef DEBUG
  if (rbag_len(&tm->rbag) > 0) printf("[%04x] ERR SAVE_REDEXES lo=%d hi=%d tot=%d\n", GID(), tm->rbag.lo_end - tm->rbag.lo_ini, tm->rbag.hi_end, rbag_len(&tm->rbag));
  #endif

  // Updates global redex counter
  atomicAdd(net->g_rbag_use_B, idx);
}

// Loads redexes from global bag to shared memory
// FIXME: check if we have enuogh space for all loads
__device__ void load_redexes(Net* net, TM *tm, u32 turn) {
  u32 bag = GID();
  for (u32 i = 0; i < RLEN; ++i) {
    Pair redex = atomicExch(&net->g_rbag_buf_A[bag * RLEN + i], 0);
    if (redex != 0) {
      Port a = enter(net, tm, get_fst(redex));
      Port b = enter(net, tm, get_snd(redex));
      #ifdef DEBUG
      if (is_local(a) || is_local(b)) printf("[%04x] ERR LOAD_REDEXES\n", turn);
      #endif
      push_redex(tm, new_pair(a, b));
    } else {
      break;
    }
  }
}

// TODO: improve variable names
__device__ bool is_block_full(Net* net, TM* tm, u32* chkt, u32* chka) {
  u32 actv = block_count(rbag_len(&tm->rbag) > 0);
  i32 ndif = block_sum(net->l_node_dif);
  i32 vdif = block_sum(net->l_vars_dif);
  u32 flim = L_NODE_LEN / TPB / 2 * actv;
  if (ndif > flim || vdif > flim) {
    return true;
  }
  *chka *= 2;
  *chkt += *chka;
  return false;
};

// Evaluator
// ---------

__global__ void inbetween(GNet* gnet, u32 turn) {
  // Clears rbag use counter
  if (turn % 2 == 0) {
    gnet->rbag_use_A = 0;
  } else {
    gnet->rbag_use_B = 0;
  }
  // Sets global mode if failed last turn
  gnet->glob = gnet->fail;
  // Clears the fail flag
  gnet->fail = 0;
}

__global__ void evaluator(GNet* gnet, u32 turn) {
  extern __shared__ char shared_mem[]; // 96 KB
  __shared__ bool halt; // halting flag

  //if (GID() == 0) printf("EVALUATOR %d\n", turn);
  //__syncthreads();

  // Local State
  u32 tick = 0; // current tick
  u32 fail = 0; // have we failed
  u32 chkt = 0; // next tick to check fullness
  u32 chka = 1; // how much to add to chkt

  // Thread Memory
  TM tm = tmem_new();
  tm.glob = true;

  // Net (Local-Global View)
  Net net = vnet_new(gnet, shared_mem, turn);

  // Clears shared memory
  for (u32 i = 0; i < L_NODE_LEN / TPB; ++i) {
    net.l_node_buf[i * TPB + TID()] = 0;
    net.l_vars_buf[i * TPB + TID()] = 0;
  }
  __syncthreads();

  // Loads Redexes
  load_redexes(&net, &tm, turn);

  // Aborts if empty
  if (block_all(rbag_len(&tm.rbag) == 0)) {
    return;
  }

  // Constants
  const u64  INIT = clock64(); // initial time
  const u64  REPS = 13; // log2 of number of loops
  const bool GROW = *net.g_rbag_use_A < TPB*BPG; // expanding rbag?
  const bool GLOB = GROW || tm.glob; // alloc on global buffer?

  // Interaction Loop
  for (tick = 0; tick < 1 << REPS; ++tick) {
    // Performs some interactions
    fail = !interact(&net, &tm, turn);
    while (!fail && rbag_has_highs(&tm.rbag)) {
      fail = fail || !interact(&net, &tm, turn);
    }

    //if (!TID()) printf("TICK %d\n", i);
    //block_print(rbag_len(&tm.rbag));
    //if (!TID()) printf("\n");
    //__syncthreads();

    // Shares a redex with neighbor thread
    if (TPB > 1 && tick % (1<<(tick/(1<<(REPS-5)))) == 0) {
      share_redexes(&tm);
    }

    // If the local page is more than half full, quit
    if (tick == chkt && is_block_full(&net, &tm, &chkt, &chka)) {
      atomicOr(&gnet->fail, 1);
      break;
    }

    // If grow-mode and all threads are full, halt
    if (GROW && block_all(rbag_len(&tm.rbag) > 0)) {
      break;
    }
  }

  //u32 ITRS = block_sum(tm.itrs);
  //u32 RLEN = block_sum(rbag_len(&tm.rbag));
  ////u32 SAVE = block_sum(saved);
  //u32 FAIL = block_sum((u32)fail);
  //u32 LOOP = block_sum((u32)tick);
  //i32 NDIF = block_sum(net.l_node_dif);
  //i32 VDIF = block_sum(net.l_vars_dif);
  //f64 TIME = (f64)(clock64() - INIT) / (f64)S;
  //f64 MIPS = (f64)ITRS / TIME / (f64)1000000.0;
  //if (TID() == 0) {
    //printf("%04x:[%02x]: ITRS=%d LOOP=%d RLEN=%d NDIF=%d VDIF=%d FAIL=%d TIME=%f MIPS=%.0f\n", turn, BID(), ITRS, LOOP, RLEN, NDIF, VDIF, FAIL, TIME, MIPS);
  //}

  __syncthreads();

  // Moves rbag to global
  save_redexes(&net, &tm, turn);

  // Stores rewrites
  atomicAdd(&gnet->itrs, tm.itrs);
  atomicAdd(&gnet->leak, tm.leak);
}

u32 get_rlen(GNet* gnet, u32 turn) {
  u32 rbag_use;
  if (turn % 2 == 0) {
    cudaMemcpy(&rbag_use, &gnet->rbag_use_B, sizeof(u32), cudaMemcpyDeviceToHost);
  } else {
    cudaMemcpy(&rbag_use, &gnet->rbag_use_A, sizeof(u32), cudaMemcpyDeviceToHost);
  }
  return rbag_use;
}

u64 get_itrs(GNet* gnet, u32 turn) {
  u64 itrs;
  cudaMemcpy(&itrs, &gnet->itrs, sizeof(u64), cudaMemcpyDeviceToHost);
  return itrs;
}

u64 get_leak(GNet* gnet, u32 turn) {
  u64 leak;
  cudaMemcpy(&leak, &gnet->leak, sizeof(u64), cudaMemcpyDeviceToHost);
  return leak;
}

// Book Loader
// -----------

void book_load(u32* buf, Book* book) {
  // Reads defs_len
  book->defs_len = *buf++;

  //printf("len %d\n", book->defs_len);

  // Parses each def
  for (u32 i = 0; i < book->defs_len; ++i) {
    // Reads fid
    u32 fid = *buf++;

    // Gets def
    Def* def = &book->defs_buf[fid];
    
    // Reads name
    memcpy(def->name, buf, 32);
    buf += 8;

    // Reads safe flag
    def->safe = *buf++;

    // Reads lengths
    def->rbag_len = *buf++;
    def->node_len = *buf++;
    def->vars_len = *buf++;

    // Reads root
    def->root = *buf++;

    // Reads rbag_buf
    memcpy(def->rbag_buf, buf, 8*def->rbag_len);
    buf += def->rbag_len * 2;
    
    // Reads node_buf
    memcpy(def->node_buf, buf, 8*def->node_len);
    buf += def->node_len * 2;
  }
}

// Debug Printing
// --------------

__device__ __host__ void put_u32(char* B, u32 val) {
  for (int i = 0; i < 8; i++, val >>= 4) {
    B[8-i-1] = "0123456789ABCDEF"[val & 0xF];
  }
}

__device__ __host__ Show show_port(Port port) {
  // NOTE: this is done like that because sprintf seems not to be working
  Show s;
  switch (get_tag(port)) {
    case VAR: memcpy(s.x, "VAR:", 4); put_u32(s.x+4, get_val(port)); break;
    case REF: memcpy(s.x, "REF:", 4); put_u32(s.x+4, get_val(port)); break;
    case ERA: memcpy(s.x, "ERA:________", 12); break;
    case NUM: memcpy(s.x, "NUM:", 4); put_u32(s.x+4, get_val(port)); break;
    case CON: memcpy(s.x, "CON:", 4); put_u32(s.x+4, get_val(port)); break;
    case DUP: memcpy(s.x, "DUP:", 4); put_u32(s.x+4, get_val(port)); break;
    case OPR: memcpy(s.x, "OPR:", 4); put_u32(s.x+4, get_val(port)); break;
    case SWI: memcpy(s.x, "SWI:", 4); put_u32(s.x+4, get_val(port)); break;
  }
  s.x[12] = '\0';
  return s;
}

__device__ Show show_rule(Rule rule) {
  Show s;
  switch (rule) {
    case LINK: memcpy(s.x, "LINK", 4); break;
    case VOID: memcpy(s.x, "VOID", 4); break;
    case ERAS: memcpy(s.x, "ERAS", 4); break;
    case ANNI: memcpy(s.x, "ANNI", 4); break;
    case COMM: memcpy(s.x, "COMM", 4); break;
    case OPER: memcpy(s.x, "OPER", 4); break;
    case SWIT: memcpy(s.x, "SWIT", 4); break;
    case CALL: memcpy(s.x, "CALL", 4); break;
    default  : memcpy(s.x, "????", 4); break;
  }
  s.x[4] = '\0';
  return s;
}

__device__ void print_rbag(RBag* rbag) {
  printf("RBAG | FST-TREE     | SND-TREE    \n");
  printf("---- | ------------ | ------------\n");
  for (u32 i = rbag->lo_ini; i < rbag->lo_end; ++i) {
    Pair redex = rbag->lo_buf[i%RLEN];
    printf("%04X | %s | %s\n", i, show_port((Port)get_fst(redex)).x, show_port((Port)get_snd(redex)).x);
  }

  for (u32 i = 0; i > rbag->hi_end; ++i) {
    Pair redex = rbag->hi_buf[i];
    printf("%04X | %s | %s\n", i, show_port((Port)get_fst(redex)).x, show_port((Port)get_snd(redex)).x);
  }
  printf("==== | ============ | ============\n");
}

__device__ __host__ void print_net(Net* net, u32 ini, u32 end) {
  printf("NODE | PORT-1       | PORT-2      \n");
  printf("---- | ------------ | ------------\n");
  for (u32 i = ini; i < end; ++i) {
    Pair node = node_load(net, i);
    if (node != 0) {
      printf("%04X | %s | %s\n", i, show_port(get_fst(node)).x, show_port(get_snd(node)).x);
    }
  }
  printf("==== | ============ |\n");
  printf("VARS | VALUE        |\n");
  printf("---- | ------------ |\n");
  for (u32 i = ini; i < end; ++i) {
    Port var = vars_load(net,i);
    if (var != 0) {
      printf("%04X | %s |\n", i, show_port(vars_load(net,i)).x);
    }
  }
  printf("==== | ============ |\n");
}

__device__ void pretty_print_port(Net* net, Port port) {
  Port stack[32];
  stack[0] = port;
  u32 len = 1;
  u32 num = 0;
  while (len > 0) {
    if (++num > 256) {
      printf("(...)\n");
      return;
    }
    if (len > 32) {
      printf("...");
      --len;
      continue;
    }
    Port cur = stack[--len];
    if (cur > 0xFFFFFF00) {
      printf("%c", (char)(cur&0xFF));
      continue;
    }
    switch (get_tag(cur)) {
      case CON: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("(");
        stack[len++] = (0xFFFFFF00) | (u32)(')');
        stack[len++] = p2;
        stack[len++] = (0xFFFFFF00) | (u32)(' ');
        stack[len++] = p1;
        break;
      }
      case ERA: {
        printf("*");
        break;
      }
      case VAR: {
        printf("x%x", get_val(cur));
        Port got = vars_load(net, get_val(cur));
        if (got != NONE) {
          printf("=");
          stack[len++] = got;
        }
        break;
      }
      case NUM: {
        Numb word = get_val(cur);
        switch (get_typ(word)) {
          case SYM: printf("[%x]", get_sym(word)); break;
          case U24: printf("%u", get_u24(word)); break;
          case I24: printf("%d", get_i24(word)); break;
          case F24: printf("%f", get_f24(word)); break;
        }
        break;
      }
      case DUP: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("{");
        stack[len++] = (0xFFFFFF00) | (u32)('}');
        stack[len++] = p2;
        stack[len++] = (0xFFFFFF00) | (u32)(' ');
        stack[len++] = p1;
        break;
      }
      case OPR: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("<+ ");
        stack[len++] = (0xFFFFFF00) | (u32)('>');
        stack[len++] = p2;
        stack[len++] = (0xFFFFFF00) | (u32)(' ');
        stack[len++] = p1;
        break;
      }
      case SWI: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("?<");
        stack[len++] = (0xFFFFFF00) | (u32)('>');
        stack[len++] = p2;
        stack[len++] = (0xFFFFFF00) | (u32)(' ');
        stack[len++] = p1;
        break;
      }
      case REF: {
        printf("@%d", get_val(cur));
        break;
      }
    }
  }
}

__device__ void pretty_print_rbag(Net* net, RBag* rbag) {
  for (u32 i = rbag->lo_ini; i < rbag->lo_end; ++i) {
    Pair redex = rbag->lo_buf[i%RLEN];
    if (redex != 0) {
      pretty_print_port(net, get_fst(redex));
      printf(" ~ ");
      pretty_print_port(net, get_snd(redex));
      printf("\n");
    }
  }
  for (u32 i = 0; i > rbag->hi_end; ++i) {
    Pair redex = rbag->hi_buf[i];
    if (redex != 0) {
      pretty_print_port(net, get_fst(redex));
      printf(" ~ ");
      pretty_print_port(net, get_snd(redex));
      printf("\n");
    }
  }
}

__device__ u32 NODE_COUNT;
__device__ u32 VARS_COUNT;

__global__ void count_memory(GNet* gnet) {
  u32 node_count = 0;
  u32 vars_count = 0;
  for (u32 i = GID(); i < G_NODE_LEN; i += TPG) {
    if (gnet->node_buf[i] != 0) ++node_count;
    if (gnet->vars_buf[i] != 0) ++vars_count;
  }

  __shared__ u32 block_node_count;
  __shared__ u32 block_vars_count;

  if (TID() == 0) block_node_count = 0;
  if (TID() == 0) block_vars_count = 0;
  __syncthreads();

  atomicAdd(&block_node_count, node_count);
  atomicAdd(&block_vars_count, vars_count);
  __syncthreads();

  if (TID() == 0) atomicAdd(&NODE_COUNT, block_node_count);
  if (TID() == 0) atomicAdd(&VARS_COUNT, block_vars_count);
}

__global__ void print_heatmap(GNet* gnet, u32 turn) {
  if (GID() > 0) return;

  for (u32 bid = 0; bid < BPG; bid++) {
    for (u32 tid = 0; tid < TPB; tid++) {
      u32 gid = bid * TPB + tid;
      u32 len = 0;
      for (u32 i = 0; i < RLEN; i++) {
        if ( turn % 2 == 0 && gnet->rbag_buf_A[gid * RLEN + i] != 0
          || turn % 2 == 1 && gnet->rbag_buf_B[gid * RLEN + i] != 0) {
          len++;
        }
      }
      u32 heat = min(len, 0xF);
      printf("%x", heat);
    }
    printf("\n");
  }

  //printf("NODE_COUNT: %d\n", NODE_COUNT);
  //printf("VARS_COUNT: %d\n", VARS_COUNT);
  //NODE_COUNT = 0;
  //VARS_COUNT = 0;
}

__global__ void print_full_net(GNet* gnet, u32 turn) {
}

__global__ void print_result(GNet* gnet, u32 turn) {
  Net net = vnet_new(gnet, NULL, turn);
  if (threadIdx.x == 0 && blockIdx.x == 0) {
    printf("Result: ");
    pretty_print_port(&net, enter(&net, NULL, ROOT));
    printf("\n");
  }
}

// Main
// ----

// stress 2^18 x 131072
static const u8 DEMO_BOOK[] = {6, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 11, 9, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 102, 117, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 2, 0, 0, 0, 102, 117, 110, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 4, 0, 0, 0, 11, 0, 128, 0, 0, 0, 0, 0, 3, 0, 0, 0, 102, 117, 110, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 36, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 108, 111, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 41, 0, 0, 0, 5, 0, 0, 0, 108, 111, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 33, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0};

// stress 2^14 x 131072
//static const u8 DEMO_BOOK[] = {6, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 11, 7, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 102, 117, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 2, 0, 0, 0, 102, 117, 110, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 4, 0, 0, 0, 11, 0, 128, 0, 0, 0, 0, 0, 3, 0, 0, 0, 102, 117, 110, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 36, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 108, 111, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 41, 0, 0, 0, 5, 0, 0, 0, 108, 111, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 33, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0};

// stress 2^10 x 131072
//static const u8 DEMO_BOOK[] = {6, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 11, 5, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 102, 117, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 2, 0, 0, 0, 102, 117, 110, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 4, 0, 0, 0, 11, 0, 128, 0, 0, 0, 0, 0, 3, 0, 0, 0, 102, 117, 110, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 36, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 108, 111, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 41, 0, 0, 0, 5, 0, 0, 0, 108, 111, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 33, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0};

// sort/bitonic_lam 16
//static const u8 DEMO_BOOK[] = {28, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 4, 0, 0, 0, 121, 0, 0, 0, 12, 0, 0, 0, 73, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 11, 8, 0, 0, 36, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 76, 101, 97, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 100, 111, 119, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 100, 111, 119, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 36, 0, 0, 0, 49, 0, 0, 0, 52, 0, 0, 0, 49, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 100, 111, 119, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 6, 0, 0, 0, 102, 108, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 20, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 102, 108, 111, 119, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 9, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 36, 0, 0, 0, 185, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 102, 108, 111, 119, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 89, 0, 0, 0, 10, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 60, 0, 0, 0, 73, 0, 0, 0, 76, 0, 0, 0, 73, 0, 0, 0, 92, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 68, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 24, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 106, 111, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 113, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 106, 111, 105, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 36, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 14, 0, 0, 0, 106, 111, 105, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 105, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 15, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 137, 0, 0, 0, 20, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 115, 111, 114, 116, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 11, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 28, 0, 0, 0, 17, 0, 0, 0, 44, 0, 0, 0, 121, 0, 0, 0, 60, 0, 0, 0, 121, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 11, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 139, 0, 0, 0, 48, 0, 0, 0, 17, 0, 0, 0, 115, 111, 114, 116, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 18, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 0, 0, 0, 8, 0, 0, 0, 19, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 145, 0, 0, 0, 20, 0, 0, 0, 145, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 20, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 177, 0, 0, 0, 21, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 23, 0, 0, 0, 119, 97, 114, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 217, 0, 0, 0, 20, 0, 0, 0, 201, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 119, 97, 114, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 97, 0, 0, 0, 52, 0, 0, 0, 185, 0, 0, 0, 68, 0, 0, 0, 185, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 36, 0, 0, 0, 45, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 64, 0, 0, 0, 48, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 32, 0, 0, 0, 56, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 25, 0, 0, 0, 119, 97, 114, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 68, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 193, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 26, 0, 0, 0, 119, 97, 114, 112, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 76, 0, 0, 0, 9, 0, 0, 0, 100, 0, 0, 0, 9, 0, 0, 0, 108, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 68, 0, 0, 0, 38, 0, 0, 0, 32, 0, 0, 0, 3, 6, 0, 128, 46, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 131, 7, 0, 128, 62, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 84, 0, 0, 0, 48, 0, 0, 0, 92, 0, 0, 0, 56, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 56, 0, 0, 0, 27, 0, 0, 0, 119, 97, 114, 112, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 209, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 68, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0};

// sort/bitonic_lam 18
//static const u8 DEMO_BOOK[] = {28, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 4, 0, 0, 0, 121, 0, 0, 0, 12, 0, 0, 0, 73, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 11, 9, 0, 0, 36, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 76, 101, 97, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 100, 111, 119, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 100, 111, 119, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 36, 0, 0, 0, 49, 0, 0, 0, 52, 0, 0, 0, 49, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 100, 111, 119, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 6, 0, 0, 0, 102, 108, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 20, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 102, 108, 111, 119, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 9, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 36, 0, 0, 0, 185, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 102, 108, 111, 119, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 89, 0, 0, 0, 10, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 60, 0, 0, 0, 73, 0, 0, 0, 76, 0, 0, 0, 73, 0, 0, 0, 92, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 68, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 24, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 106, 111, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 113, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 106, 111, 105, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 36, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 14, 0, 0, 0, 106, 111, 105, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 105, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 15, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 137, 0, 0, 0, 20, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 115, 111, 114, 116, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 11, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 28, 0, 0, 0, 17, 0, 0, 0, 44, 0, 0, 0, 121, 0, 0, 0, 60, 0, 0, 0, 121, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 11, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 139, 0, 0, 0, 48, 0, 0, 0, 17, 0, 0, 0, 115, 111, 114, 116, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 18, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 0, 0, 0, 8, 0, 0, 0, 19, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 145, 0, 0, 0, 20, 0, 0, 0, 145, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 20, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 177, 0, 0, 0, 21, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 23, 0, 0, 0, 119, 97, 114, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 217, 0, 0, 0, 20, 0, 0, 0, 201, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 119, 97, 114, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 97, 0, 0, 0, 52, 0, 0, 0, 185, 0, 0, 0, 68, 0, 0, 0, 185, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 36, 0, 0, 0, 45, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 64, 0, 0, 0, 48, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 32, 0, 0, 0, 56, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 25, 0, 0, 0, 119, 97, 114, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 68, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 193, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 26, 0, 0, 0, 119, 97, 114, 112, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 76, 0, 0, 0, 9, 0, 0, 0, 100, 0, 0, 0, 9, 0, 0, 0, 108, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 68, 0, 0, 0, 38, 0, 0, 0, 32, 0, 0, 0, 3, 6, 0, 128, 46, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 131, 7, 0, 128, 62, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 84, 0, 0, 0, 48, 0, 0, 0, 92, 0, 0, 0, 56, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 56, 0, 0, 0, 27, 0, 0, 0, 119, 97, 114, 112, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 209, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 68, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0};

// sort/bitonic_tup 16
//static const u8 DEMO_BOOK[] = {17, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 8, 0, 0, 5, 0, 0, 0, 73, 0, 0, 0, 20, 0, 0, 0, 57, 0, 0, 0, 36, 0, 0, 0, 41, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 44, 0, 0, 0, 11, 0, 0, 0, 52, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 24, 0, 0, 0, 68, 0, 0, 0, 11, 0, 0, 0, 40, 0, 0, 0, 1, 0, 0, 0, 100, 111, 119, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 17, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 2, 0, 0, 0, 100, 111, 119, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 13, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 60, 0, 0, 0, 25, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 32, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 3, 0, 0, 0, 102, 108, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 33, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 102, 108, 111, 119, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 60, 0, 0, 0, 113, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 28, 0, 0, 0, 22, 0, 0, 0, 8, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 32, 0, 0, 0, 108, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 5, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 68, 0, 0, 0, 41, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 60, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 7, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 65, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 115, 111, 114, 116, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 17, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 60, 0, 0, 0, 57, 0, 0, 0, 92, 0, 0, 0, 57, 0, 0, 0, 116, 0, 0, 0, 13, 0, 0, 0, 36, 0, 0, 0, 22, 0, 0, 0, 29, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 64, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 11, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 56, 0, 0, 0, 16, 0, 0, 0, 124, 0, 0, 0, 139, 0, 0, 0, 132, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 9, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 36, 0, 0, 0, 28, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 10, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 73, 0, 0, 0, 36, 0, 0, 0, 73, 0, 0, 0, 68, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 54, 0, 0, 0, 3, 2, 0, 128, 62, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 11, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 97, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 12, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 13, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 119, 97, 114, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 52, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 15, 0, 0, 0, 119, 97, 114, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 89, 0, 0, 0, 76, 0, 0, 0, 14, 0, 0, 0, 28, 0, 0, 0, 131, 7, 0, 128, 22, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 37, 0, 0, 0, 60, 0, 0, 0, 46, 0, 0, 0, 24, 0, 0, 0, 3, 6, 0, 128, 54, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 69, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 24, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 119, 97, 114, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 21, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 113, 0, 0, 0, 92, 0, 0, 0, 113, 0, 0, 0, 132, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 68, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 64, 0, 0, 0, 72, 0, 0, 0, 80, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 16, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 116, 0, 0, 0, 48, 0, 0, 0, 124, 0, 0, 0, 64, 0, 0, 0, 80, 0, 0, 0, 8, 0, 0, 0, 140, 0, 0, 0, 24, 0, 0, 0, 148, 0, 0, 0, 40, 0, 0, 0, 156, 0, 0, 0, 56, 0, 0, 0, 164, 0, 0, 0, 72, 0, 0, 0, 88, 0, 0, 0};

// sort/bitonic_tup 18
//static const u8 DEMO_BOOK[] = {17, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 9, 0, 0, 5, 0, 0, 0, 73, 0, 0, 0, 20, 0, 0, 0, 57, 0, 0, 0, 36, 0, 0, 0, 41, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 44, 0, 0, 0, 11, 0, 0, 0, 52, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 24, 0, 0, 0, 68, 0, 0, 0, 11, 0, 0, 0, 40, 0, 0, 0, 1, 0, 0, 0, 100, 111, 119, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 17, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 2, 0, 0, 0, 100, 111, 119, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 13, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 60, 0, 0, 0, 25, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 32, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 3, 0, 0, 0, 102, 108, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 33, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 102, 108, 111, 119, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 60, 0, 0, 0, 113, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 28, 0, 0, 0, 22, 0, 0, 0, 8, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 76, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 100, 0, 0, 0, 32, 0, 0, 0, 108, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 5, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 68, 0, 0, 0, 41, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 60, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 7, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 65, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 115, 111, 114, 116, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 17, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 60, 0, 0, 0, 57, 0, 0, 0, 92, 0, 0, 0, 57, 0, 0, 0, 116, 0, 0, 0, 13, 0, 0, 0, 36, 0, 0, 0, 22, 0, 0, 0, 29, 0, 0, 0, 163, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 64, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 11, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 56, 0, 0, 0, 16, 0, 0, 0, 124, 0, 0, 0, 139, 0, 0, 0, 132, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 9, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 36, 0, 0, 0, 28, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 10, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 73, 0, 0, 0, 36, 0, 0, 0, 73, 0, 0, 0, 68, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 54, 0, 0, 0, 3, 2, 0, 128, 62, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 11, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 97, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 12, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 13, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 119, 97, 114, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 52, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 15, 0, 0, 0, 119, 97, 114, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 89, 0, 0, 0, 76, 0, 0, 0, 14, 0, 0, 0, 28, 0, 0, 0, 131, 7, 0, 128, 22, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 37, 0, 0, 0, 60, 0, 0, 0, 46, 0, 0, 0, 24, 0, 0, 0, 3, 6, 0, 128, 54, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 69, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 24, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 119, 97, 114, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 21, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 113, 0, 0, 0, 92, 0, 0, 0, 113, 0, 0, 0, 132, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 68, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 64, 0, 0, 0, 72, 0, 0, 0, 80, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 16, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 116, 0, 0, 0, 48, 0, 0, 0, 124, 0, 0, 0, 64, 0, 0, 0, 80, 0, 0, 0, 8, 0, 0, 0, 140, 0, 0, 0, 24, 0, 0, 0, 148, 0, 0, 0, 40, 0, 0, 0, 156, 0, 0, 0, 56, 0, 0, 0, 164, 0, 0, 0, 72, 0, 0, 0, 88, 0, 0, 0};

// sort/radix 16
//static const u8 DEMO_BOOK[] = {31, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 4, 0, 0, 0, 153, 0, 0, 0, 12, 0, 0, 0, 57, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 11, 8, 0, 0, 28, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 66, 117, 115, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 67, 111, 110, 99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 69, 109, 112, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 70, 114, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 6, 0, 0, 0, 83, 105, 110, 103, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 73, 0, 0, 0, 8, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 57, 0, 0, 0, 68, 0, 0, 0, 57, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 32, 0, 0, 0, 51, 1, 0, 0, 37, 0, 0, 0, 16, 0, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 10, 0, 0, 0, 109, 101, 114, 103, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 20, 0, 0, 0, 113, 0, 0, 0, 28, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 36, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 81, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 13, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 97, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 89, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 14, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 15, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 114, 97, 100, 105, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 76, 0, 0, 0, 20, 0, 0, 0, 52, 0, 0, 0, 28, 0, 0, 0, 145, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 18, 0, 0, 0, 114, 97, 100, 105, 120, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 76, 0, 0, 0, 177, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 131, 6, 0, 128, 38, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 68, 0, 0, 0, 62, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 124, 0, 0, 0, 33, 0, 0, 0, 56, 0, 0, 0, 19, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 201, 0, 0, 0, 12, 0, 0, 0, 225, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 8, 0, 0, 0, 21, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 20, 0, 0, 0, 161, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 185, 0, 0, 0, 193, 0, 0, 0, 23, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 25, 0, 0, 0, 116, 111, 95, 97, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 25, 0, 0, 0, 217, 0, 0, 0, 36, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 201, 0, 0, 0, 84, 0, 0, 0, 201, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 62, 0, 0, 0, 35, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 76, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 27, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 116, 111, 95, 109, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 241, 0, 0, 0, 28, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 81, 0, 0, 0, 20, 0, 0, 0, 225, 0, 0, 0, 36, 0, 0, 0, 225, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 30, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 12, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 139, 0, 0, 0, 36, 0, 0, 0, 9, 0, 0, 0, 8, 0, 0, 0};

// sort/radix 18
//static const u8 DEMO_BOOK[] = {31, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 4, 0, 0, 0, 153, 0, 0, 0, 12, 0, 0, 0, 57, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 11, 9, 0, 0, 28, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 66, 117, 115, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 67, 111, 110, 99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 69, 109, 112, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 70, 114, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 6, 0, 0, 0, 83, 105, 110, 103, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 73, 0, 0, 0, 8, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 57, 0, 0, 0, 68, 0, 0, 0, 57, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 32, 0, 0, 0, 51, 1, 0, 0, 37, 0, 0, 0, 16, 0, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 10, 0, 0, 0, 109, 101, 114, 103, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 20, 0, 0, 0, 113, 0, 0, 0, 28, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 36, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 81, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 13, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 97, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 89, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 14, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 15, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 114, 97, 100, 105, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 76, 0, 0, 0, 20, 0, 0, 0, 52, 0, 0, 0, 28, 0, 0, 0, 145, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 18, 0, 0, 0, 114, 97, 100, 105, 120, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 76, 0, 0, 0, 177, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 131, 6, 0, 128, 38, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 68, 0, 0, 0, 62, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 124, 0, 0, 0, 33, 0, 0, 0, 56, 0, 0, 0, 19, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 201, 0, 0, 0, 12, 0, 0, 0, 225, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 8, 0, 0, 0, 21, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 20, 0, 0, 0, 161, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 185, 0, 0, 0, 193, 0, 0, 0, 23, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 25, 0, 0, 0, 116, 111, 95, 97, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 25, 0, 0, 0, 217, 0, 0, 0, 36, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 201, 0, 0, 0, 84, 0, 0, 0, 201, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 62, 0, 0, 0, 35, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 76, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 27, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 116, 111, 95, 109, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 241, 0, 0, 0, 28, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 81, 0, 0, 0, 20, 0, 0, 0, 225, 0, 0, 0, 36, 0, 0, 0, 225, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 30, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 12, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 139, 0, 0, 0, 36, 0, 0, 0, 9, 0, 0, 0, 8, 0, 0, 0};

// sort/radix 20
//static const u8 DEMO_BOOK[] = {31, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 4, 0, 0, 0, 153, 0, 0, 0, 12, 0, 0, 0, 57, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 11, 10, 0, 0, 28, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 66, 117, 115, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 67, 111, 110, 99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 69, 109, 112, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 70, 114, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 6, 0, 0, 0, 83, 105, 110, 103, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 73, 0, 0, 0, 8, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 57, 0, 0, 0, 68, 0, 0, 0, 57, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 32, 0, 0, 0, 51, 1, 0, 0, 37, 0, 0, 0, 16, 0, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 10, 0, 0, 0, 109, 101, 114, 103, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 20, 0, 0, 0, 113, 0, 0, 0, 28, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 36, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 81, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 13, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 97, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 89, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 14, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 15, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 114, 97, 100, 105, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 76, 0, 0, 0, 20, 0, 0, 0, 52, 0, 0, 0, 28, 0, 0, 0, 145, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 18, 0, 0, 0, 114, 97, 100, 105, 120, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 76, 0, 0, 0, 177, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 131, 6, 0, 128, 38, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 68, 0, 0, 0, 62, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 124, 0, 0, 0, 33, 0, 0, 0, 56, 0, 0, 0, 19, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 201, 0, 0, 0, 12, 0, 0, 0, 225, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 8, 0, 0, 0, 21, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 20, 0, 0, 0, 161, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 185, 0, 0, 0, 193, 0, 0, 0, 23, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 25, 0, 0, 0, 116, 111, 95, 97, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 25, 0, 0, 0, 217, 0, 0, 0, 36, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 201, 0, 0, 0, 84, 0, 0, 0, 201, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 62, 0, 0, 0, 35, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 76, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 27, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 116, 111, 95, 109, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 241, 0, 0, 0, 28, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 81, 0, 0, 0, 20, 0, 0, 0, 225, 0, 0, 0, 36, 0, 0, 0, 225, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 30, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 12, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 139, 0, 0, 0, 36, 0, 0, 0, 9, 0, 0, 0, 8, 0, 0, 0};

// sort/radix 22
//static const u8 DEMO_BOOK[] = {31, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 4, 0, 0, 0, 153, 0, 0, 0, 12, 0, 0, 0, 57, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 139, 11, 0, 0, 28, 0, 0, 0, 11, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 66, 117, 115, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 67, 111, 110, 99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 3, 0, 0, 0, 69, 109, 112, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 70, 114, 101, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 6, 0, 0, 0, 83, 105, 110, 103, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 7, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 73, 0, 0, 0, 8, 0, 0, 0, 103, 101, 110, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 103, 101, 110, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 52, 0, 0, 0, 57, 0, 0, 0, 68, 0, 0, 0, 57, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 32, 0, 0, 0, 51, 1, 0, 0, 37, 0, 0, 0, 16, 0, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 60, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 10, 0, 0, 0, 109, 101, 114, 103, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 20, 0, 0, 0, 113, 0, 0, 0, 28, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 10, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 36, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 81, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 12, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 13, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 97, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 89, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 14, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 2, 0, 0, 0, 11, 0, 0, 0, 15, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 109, 101, 114, 103, 101, 36, 67, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 9, 0, 0, 0, 28, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 114, 97, 100, 105, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 76, 0, 0, 0, 20, 0, 0, 0, 52, 0, 0, 0, 28, 0, 0, 0, 145, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 18, 0, 0, 0, 114, 97, 100, 105, 120, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 76, 0, 0, 0, 177, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 30, 0, 0, 0, 131, 6, 0, 128, 38, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 68, 0, 0, 0, 62, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 124, 0, 0, 0, 33, 0, 0, 0, 56, 0, 0, 0, 19, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 201, 0, 0, 0, 12, 0, 0, 0, 225, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 20, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 11, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 0, 0, 0, 8, 0, 0, 0, 21, 0, 0, 0, 115, 117, 109, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 161, 0, 0, 0, 20, 0, 0, 0, 161, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 2, 0, 128, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 22, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 185, 0, 0, 0, 193, 0, 0, 0, 23, 0, 0, 0, 115, 119, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 115, 119, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 25, 0, 0, 0, 116, 111, 95, 97, 114, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 25, 0, 0, 0, 217, 0, 0, 0, 36, 0, 0, 0, 209, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 68, 0, 0, 0, 201, 0, 0, 0, 84, 0, 0, 0, 201, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 29, 0, 0, 0, 32, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 51, 1, 0, 0, 46, 0, 0, 0, 163, 0, 0, 0, 16, 0, 0, 0, 51, 1, 0, 0, 62, 0, 0, 0, 35, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 76, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 27, 0, 0, 0, 116, 111, 95, 97, 114, 114, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 49, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 116, 111, 95, 109, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 20, 0, 0, 0, 241, 0, 0, 0, 28, 0, 0, 0, 233, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 81, 0, 0, 0, 20, 0, 0, 0, 225, 0, 0, 0, 36, 0, 0, 0, 225, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 30, 0, 0, 0, 116, 111, 95, 109, 97, 112, 36, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 137, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 11, 12, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 139, 0, 0, 0, 36, 0, 0, 0, 9, 0, 0, 0, 8, 0, 0, 0};

void hvm_cu(u32* book_buffer) {
  // Start the timer
  clock_t start = clock();
  
  // Loads the Book
  if (book_buffer) {
    Book* book = (Book*)malloc(sizeof(Book));
    book_load((u32*)book_buffer, book);
    cudaMemcpyToSymbol(BOOK, book, sizeof(Book));
    free(book);
  }

  // GMem
  GNet *d_gnet;
  cudaMalloc((void**)&d_gnet, sizeof(GNet));
  cudaMemset(d_gnet, 0, sizeof(GNet));

  // Set the initial redex
  Pair pair = new_pair(new_port(REF, 0), ROOT);
  cudaMemcpy(&d_gnet->rbag_buf_A[0], &pair, sizeof(Pair), cudaMemcpyHostToDevice);

  // Configures Shared Memory Size
  cudaFuncSetAttribute(evaluator, cudaFuncAttributeMaxDynamicSharedMemorySize, sizeof(LNet));

  // Inits the GNet
  gnet_init<<<BPG, TPB>>>(d_gnet);

  // Invokes the Evaluator Kernel repeatedly
  u32 turn;
  u64 itrs = 0;
  u64 leak = 0;
  u32 rlen = 0;
  for (turn = 0; turn < 0xFFFFFFFF; ++turn) {
    //cudaDeviceSynchronize();
    //printf("-------------------------------------------- TURN: %04x | RLEN: %04x | ITRS: %012llu\n", turn, rlen, itrs);
    
    evaluator<<<BPG, TPB, sizeof(LNet)>>>(d_gnet, turn);
    inbetween<<<1, 1>>>(d_gnet, turn);

    //cudaDeviceSynchronize();
    //count_memory<<<BPG, TPB>>>(d_gnet);

    //cudaDeviceSynchronize();
    //print_heatmap<<<1,1>>>(d_gnet, turn+1);

    itrs = get_itrs(d_gnet, turn);
    leak = get_leak(d_gnet, turn);
    rlen = get_rlen(d_gnet, turn);
    if (rlen == 0) {
      printf("Completed after %d kernel launches!\n", turn);
      break;
    }
  }

  // Invokes the Result Printer Kernel
  cudaDeviceSynchronize();
  print_result<<<1,1>>>(d_gnet, turn);

  // Reports errors
  cudaError_t err = cudaGetLastError();
  if (err != cudaSuccess) {
    fprintf(stderr, "Failed to launch kernels (error code %s)!\n", cudaGetErrorString(err));
    exit(EXIT_FAILURE);
  }

  // Stops the timer
  clock_t end = clock();
  double duration = ((double)(end - start)) / CLOCKS_PER_SEC;

  // Prints entire memdump
  //{
    //// Allocate host memory for the net
    //GNet *h_gnet = (GNet*)malloc(sizeof(GNet));

    //// Copy the net from device to host
    //cudaMemcpy(h_gnet, d_gnet, sizeof(GNet), cudaMemcpyDeviceToHost);

    //// Create a Net view of the host GNet
    //Net net;
    //net.g_node_buf = h_gnet->node_buf;
    //net.g_vars_buf = h_gnet->vars_buf;

    //// Print the net
    //print_net(&net, L_NODE_LEN, G_NODE_LEN);

    //// Free host memory
    //free(h_gnet);
  //}

  // Gets interaction count
  //cudaMemcpy(&itrs, &d_gnet->itrs, sizeof(u64), cudaMemcpyDeviceToHost);

  // Prints interactions, time and MIPS
  printf("- ITRS: %llu\n", itrs);
  printf("- LEAK: %llu\n", leak);
  printf("- TIME: %.2fs\n", duration);
  printf("- MIPS: %.2f\n", (double)itrs / duration / 1000000.0);
}

int main() {
  hvm_cu((u32*)DEMO_BOOK);
  //hvm_cu(NULL);
  return 0;
}
