#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef DEBUG
  #define debug(...) fprintf(stderr, __VA_ARGS__)
#else
  #define debug(...)
#endif

#define INTERPRETED
#define WITHOUT_MAIN

// Types
// --------

typedef  uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef  int32_t i32;
typedef    float f32;
typedef   double f64;

typedef  _Atomic(u8)  a8;
typedef _Atomic(u16) a16;
typedef _Atomic(u32) a32;
typedef _Atomic(u64) a64;

// Configuration
// -------------

// Threads per CPU
#ifndef TPC_L2
#define TPC_L2 0
#endif
#define TPC (1ul << TPC_L2)

// Types
// -----

// Local Types
typedef u8  Tag;  // Tag  ::= 4-bit (rounded up to u8)
typedef u32 Val;  // Val  ::= 28-bit (rounded up to u32)
typedef u32 Port; // Port ::= Tag + Val (fits a u32)
typedef u64 Pair; // Pair ::= Port + Port (fits a u64)

typedef a32 APort; // atomic Port
typedef a64 APair; // atomic Pair

// Rules
typedef u8 Rule; // Rule ::= 3-bit (rounded up to 8)

// Numbs
typedef u32 Numb; // Numb ::= 29-bit (rounded up to u32)

// Tags
//#define VAR 0x0 // variable
//#define REF 0x1 // reference
//#define ERA 0x2 // eraser
//#define NUM 0x3 // number
//#define CON 0x4 // constructor
//#define DUP 0x5 // duplicator
//#define OPR 0x6 // operator
//#define SWI 0x7 // switch

#define VAR 0x0 // variable
#define REF 0x1 // reference 
#define ERA 0x2 // eraser
#define CAL 0x3 // call
#define LAM 0x4 // lambda
#define APP 0x5 // application
#define DUP 0x6 // duplicator
#define EVL 0x7 // eval
#define WAI 0x8 // wait
#define HLD 0x9 // hold
#define DCD 0xA // decide

// Interaction Rule Values
//#define LINK 0x0
//#define DREF 0x1
//#define VOID 0x2
//#define ERAS 0x3
//#define ANNI 0x4
//#define COMM 0x5
//#define OPER 0x6
//#define SWIT 0x7

#define LINK 0x0 // variable link
#define DREF 0x1 // definition dereference 
#define VOID 0x2 // erase nullary
#define ERAS 0x3 // erase binary
#define ANNI 0x4 // annihilation
#define COMM 0x5 // commutation
#define BETA 0x6 // lazy beta reduction
#define ELAM 0x7 // evaluate lambda
#define EDUP 0x8 // evaluate superposition
#define EWAI 0x9 // evaluate wait
#define WAPP 0xA // wait application
#define WDUP 0xB // wait duplication
#define CHLD 0xC // call hold
#define CDCD 0xD // call decide
#define EDCD 0xE // erase decide
#define ERR_ 0xF // error

// Constants
#define TAG_LEN (4)
#define VAL_LEN (28)
#define TAG_MASK (0b1111)

#define FREE 0x00000000
#define NONE 0xFFFFFFFF
#define ROOT ((NONE << TAG_LEN) | LINK)

// Cache Padding
#define CACHE_PAD 64

// Global Net
#define HLEN (1ul << 16) // max 16k high-priority redexes
#define RLEN (1ul << 24) // max 16m low-priority redexes
#define G_NODE_LEN (1ul << VAL_LEN) // max 536m nodes
#define G_VARS_LEN (1ul << VAL_LEN) // max 536m vars
#define G_RBAG_LEN (TPC * RLEN)

typedef struct Net {
  APair node_buf[G_NODE_LEN]; // global node buffer
  APort vars_buf[G_VARS_LEN]; // global vars buffer
  APair rbag_buf[G_RBAG_LEN]; // global rbag buffer
  a64 itrs; // interaction count
  a32 idle; // idle thread counter
} Net;

#define DEF_RBAG_LEN 0xFFF
#define DEF_NODE_LEN 0xFFF

// Top-Level Definition
typedef struct Def {
  char name[256];
  bool safe;
  u32  rbag_len;
  u32  node_len;
  u32  vars_len;
  Port root;
  Pair node_buf[DEF_NODE_LEN];
  Pair rbag_buf[DEF_RBAG_LEN];
} Def;

typedef struct Book Book;

// A Foreign Function
typedef struct {
  char name[256];
  Port (*func)(Net*, Book*, Port);
} FFn;

// Book of Definitions
typedef struct Book {
  u32 defs_len;
  Def defs_buf[0x4000];
  u32 ffns_len;
  FFn ffns_buf[0x4000];
} Book;

// Local Thread Memory
typedef struct TM {
  u32  tid; // thread id
  u32  itrs; // interaction count
  u32  nput; // next node allocation attempt index
  u32  vput; // next vars allocation attempt index
  u32  hput; // next hbag push index
  u32  rput; // next rbag push index
  u32  sidx; // steal index
  u32  nloc[0xFFF]; // global node allocation indices
  u32  vloc[0xFFF]; // global vars allocation indices
  Pair hbag_buf[HLEN]; // high-priority redexes
} TM;

// Port: Constructor and Getters
// -----------------------------

static inline Port new_port(Tag tag, Val val) {
  return (val << TAG_LEN) | tag;
}

static inline Tag get_tag(Port port) {
  return port & TAG_MASK;
}

static inline Val get_val(Port port) {
  return port >> TAG_LEN;
}

// Pair: Constructor and Getters
// -----------------------------

static inline const Pair new_pair(Port fst, Port snd) {
  return ((u64)snd << 32) | fst;
}

static inline Port get_fst(Pair pair) {
  return pair & 0xFFFFFFFF;
}

static inline Port get_snd(Pair pair) {
  return pair >> 32;
}

// Utils
// -----

// Swaps two ports.
static inline void swap(Port *a, Port *b) {
  Port x = *a; *a = *b; *b = x;
}

static inline u32 min(u32 a, u32 b) {
  return (a < b) ? a : b;
}

static inline f32 clamp(f32 x, f32 min, f32 max) {
  const f32 t = x < min ? min : x;
  return (t > max) ? max : t;
}

// A simple spin-wait barrier using atomic operations
a64 a_reached = 0; // number of threads that reached the current barrier
a64 a_barrier = 0; // number of barriers passed during this program
void sync_threads() {
  u64 barrier_old = atomic_load_explicit(&a_barrier, memory_order_relaxed);
  if (atomic_fetch_add_explicit(&a_reached, 1, memory_order_relaxed) == (TPC - 1)) {
    // Last thread to reach the barrier resets the counter and advances the barrier
    atomic_store_explicit(&a_reached, 0, memory_order_relaxed);
    atomic_store_explicit(&a_barrier, barrier_old + 1, memory_order_release);
  } else {
    u32 tries = 0;
    while (atomic_load_explicit(&a_barrier, memory_order_acquire) == barrier_old) {
      sched_yield();
    }
  }
}

// Global sum function
static a32 GLOBAL_SUM = 0;
u32 global_sum(u32 x) {
  atomic_fetch_add_explicit(&GLOBAL_SUM, x, memory_order_relaxed);
  sync_threads();
  u32 sum = atomic_load_explicit(&GLOBAL_SUM, memory_order_relaxed);
  sync_threads();
  atomic_store_explicit(&GLOBAL_SUM, 0, memory_order_relaxed);
  return sum;
}

// TODO: write a time64() function that returns the time as fast as possible as a u64
static inline u64 time64() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (u64)ts.tv_sec * 1000000000ULL + (u64)ts.tv_nsec;
}

// Ports / Pairs / Rules
// ---------------------

// True if this port has a pointer to a node.
static inline bool is_nod(Port a) {
  return get_tag(a) >= LAM;
}

// True if this port is a variable.
static inline bool is_var(Port a) {
  return get_tag(a) == VAR;
}

// Given two tags, gets their interaction rule.
static inline Rule get_rule(Port a, Port b) {
  //const u8 table[8][8] = {
  //  //VAR  REF  ERA  NUM  CON  DUP  OPR  SWI
  //  {LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK}, // VAR
  //  {LINK,VOID,VOID,VOID,DREF,DREF,DREF,DREF}, // REF
  //  {LINK,VOID,VOID,VOID,ERAS,ERAS,ERAS,ERAS}, // ERA
  //  {LINK,VOID,VOID,VOID,ERAS,ERAS,OPER,SWIT}, // NUM
  //  {LINK,DREF,ERAS,ERAS,ANNI,COMM,COMM,COMM}, // CON
  //  {LINK,DREF,ERAS,ERAS,COMM,ANNI,COMM,COMM}, // DUP
  //  {LINK,DREF,ERAS,OPER,COMM,COMM,ANNI,COMM}, // OPR
  //  {LINK,DREF,ERAS,SWIT,COMM,COMM,COMM,ANNI}, // SWI
  //};
  const u8 table[11][11] = {
    //VAR  REF  ERA  CAL  LAM  APP  DUP  EVL  WAI  HLD  DCD
    {LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK}, // VAR
    {LINK,VOID,VOID,ERR_,DREF,DREF,DREF,DREF,DREF,ERR_,ERR_}, // REF
    {LINK,VOID,VOID,VOID,ERAS,ERAS,ERAS,ERAS,ERAS,ERAS,EDCD}, // ERA
    {LINK,ERR_,VOID,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,CHLD,CDCD}, // CAL
    {LINK,DREF,ERAS,ERR_,ERR_,BETA,COMM,ELAM,ERR_,ERR_,ERR_}, // LAM
    {LINK,DREF,ERAS,ERR_,BETA,ERR_,COMM,ERR_,WAPP,ERR_,ERR_}, // APP
    {LINK,DREF,ERAS,ERR_,COMM,COMM,ANNI,EDUP,WDUP,ERR_,ERR_}, // DUP
    {LINK,DREF,ERAS,ERR_,ELAM,ERR_,EDUP,ERR_,EWAI,ERR_,ERR_}, // EVL
    {LINK,DREF,ERAS,ERR_,ERR_,WAPP,WDUP,EWAI,ERR_,ERR_,ERR_}, // WAI
    {LINK,ERR_,ERAS,CHLD,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_}, // HLD
    {LINK,ERR_,EDCD,CDCD,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_,ERR_}, // DCD
  };
  return table[get_tag(a)][get_tag(b)];
}

// Same as above, but receiving a pair.
static inline Rule get_pair_rule(Pair AB) {
  return get_rule(get_fst(AB), get_snd(AB));
}

// Should we swap ports A and B before reducing this rule?
static inline bool should_swap(Port A, Port B) {
  return get_tag(B) < get_tag(A);
}

// Gets a rule's priority
static inline bool is_high_priority(Rule rule) {
  // TODO: this needs to be more readable
  switch (rule) {
    case COMM:
    case DREF:
    case BETA:
    case WAPP:
    case WDUP:
      return false;
    case LINK:
    case VOID:
    case ERAS:
    case ANNI:
    case ELAM:
    case EDUP:
    case EWAI:
    case CHLD:
    case CDCD:
    case EDCD:
    default:
      return true;
  }
}

// Adjusts a newly allocated port.
static inline Port adjust_port(Net* net, TM* tm, Port port) {
  Tag tag = get_tag(port);
  Val val = get_val(port);
  if (is_nod(port)) return new_port(tag, tm->nloc[val]);
  if (is_var(port)) return new_port(tag, tm->vloc[val]);
  return new_port(tag, val);
}

// Adjusts a newly allocated pair.
static inline Pair adjust_pair(Net* net, TM* tm, Pair pair) {
  Port p1 = adjust_port(net, tm, get_fst(pair));
  Port p2 = adjust_port(net, tm, get_snd(pair));
  return new_pair(p1, p2);
}

// RBag
// ----

// FIXME: what about some bound checks?

static inline void push_redex(Net* net, TM* tm, Pair redex) {
  #ifdef DEBUG
  bool free_local = tm->hput < HLEN;
  bool free_global = tm->rput < RLEN;
  if (!free_global || !free_local) {
    debug("push_redex: limited resources, maybe corrupting memory\n");
  }
  #endif

  if (is_high_priority(get_pair_rule(redex))) {
    tm->hbag_buf[tm->hput++] = redex;
  } else {
    atomic_store_explicit(&net->rbag_buf[tm->tid*(G_RBAG_LEN/TPC) + (tm->rput++)], redex, memory_order_relaxed);
  }
}

static inline Pair pop_redex(Net* net, TM* tm) {
  if (tm->hput > 0) {
    return tm->hbag_buf[--tm->hput];
  } else if (tm->rput > 0) {
    return atomic_exchange_explicit(&net->rbag_buf[tm->tid*(G_RBAG_LEN/TPC) + (--tm->rput)], 0, memory_order_relaxed);
  } else {
    return 0;
  }
}

static inline u32 rbag_len(Net* net, TM* tm) {
  return tm->rput + tm->hput;
}

// TM
// --

static TM* tm[TPC];

TM* tm_new(u32 tid) {
  TM* tm   = malloc(sizeof(TM));
  tm->tid  = tid;
  tm->itrs = 0;
  tm->nput = 1;
  tm->vput = 1;
  tm->rput = 0;
  tm->hput = 0;
  tm->sidx = 0;
  return tm;
}

void alloc_static_tms() {
  for (u32 t = 0; t < TPC; ++t) {
    tm[t] = tm_new(t);
  }
}

void free_static_tms() {
  for (u32 t = 0; t < TPC; ++t) {
    free(tm[t]);
  }
}

// Net
// ----

// Stores a new node on global.
static inline void node_create(Net* net, u32 loc, Pair val) {
  atomic_store_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Stores a var on global.
static inline void vars_create(Net* net, u32 var, Port val) {
  atomic_store_explicit(&net->vars_buf[var], val, memory_order_relaxed);
}

// Reads a node from global.
static inline Pair node_load(Net* net, u32 loc) {
  return atomic_load_explicit(&net->node_buf[loc], memory_order_relaxed);
}

// Reads a var from global.
static inline Port vars_load(Net* net, u32 var) {
  return atomic_load_explicit(&net->vars_buf[var], memory_order_relaxed);
}

// Stores a node on global.
static inline void node_store(Net* net, u32 loc, Pair val) {
  atomic_store_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Exchanges a node on global by a value. Returns old.
static inline Pair node_exchange(Net* net, u32 loc, Pair val) {
  return atomic_exchange_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Exchanges a var on global by a value. Returns old.
static inline Port vars_exchange(Net* net, u32 var, Port val) {
  return atomic_exchange_explicit(&net->vars_buf[var], val, memory_order_relaxed);
}

// Takes a node.
static inline Pair node_take(Net* net, u32 loc) {
  return node_exchange(net, loc, 0);
}

// Takes a var.
static inline Port vars_take(Net* net, u32 var) {
  return vars_exchange(net, var, 0);
}


// Net
// ---

// Initializes a net.
static inline Net* net_new() {
  Net* net = calloc(1, sizeof(Net));

  atomic_store(&net->itrs, 0);
  atomic_store(&net->idle, 0);

  return net;
}

// Allocator
// ---------

u32 node_alloc_1(Net* net, TM* tm, u32* lps) {
  while (true) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->nput%(G_NODE_LEN/TPC));
    Pair elem = net->node_buf[lc];
    tm->nput += 1;
    if (lc > 0 && elem == 0) {
      return lc;
    }
    // FIXME: check this decently
    if (++(*lps) >= G_NODE_LEN/TPC) printf("OOM\n");
  }
}

u32 vars_alloc_1(Net* net, TM* tm, u32* lps) {
  while (true) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->vput%(G_NODE_LEN/TPC));
    Port elem = net->vars_buf[lc];
    tm->vput += 1;
    if (lc > 0 && elem == 0) {
      return lc;
    }
    // FIXME: check this decently
    if (++(*lps) >= G_NODE_LEN/TPC) printf("OOM\n");
  }
}

u32 node_alloc(Net* net, TM* tm, u32 num) {
  u32 got = 0;
  u32 lps = 0;
  while (got < num) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->nput%(G_NODE_LEN/TPC));
    Pair elem = net->node_buf[lc];
    tm->nput += 1;
    if (lc > 0 && elem == 0) {
      tm->nloc[got++] = lc;
    }
    // FIXME: check this decently
    if (++lps >= G_NODE_LEN/TPC) printf("OOM\n");
  }
  return got;
}

u32 vars_alloc(Net* net, TM* tm, u32 num) {
  u32 got = 0;
  u32 lps = 0;
  while (got < num) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->vput%(G_NODE_LEN/TPC));
    Port elem = net->vars_buf[lc];
    tm->vput += 1;
    if (lc > 0 && elem == 0) {
      tm->vloc[got++] = lc;
    }
    // FIXME: check this decently
    if (++lps >= G_NODE_LEN/TPC) printf("OOM\n");
  }
  return got;
}

// Gets the necessary resources for an interaction. Returns success.
static inline bool get_resources(Net* net, TM* tm, u32 need_rbag, u32 need_node, u32 need_vars) {
  u32 got_rbag = min(RLEN - tm->rput, HLEN - tm->hput);
  u32 got_node = node_alloc(net, tm, need_node);
  u32 got_vars = vars_alloc(net, tm, need_vars);

  return got_rbag >= need_rbag && got_node >= need_node && got_vars >= need_vars;
}

// Linking
// -------

// Peeks a variable's final target without modifying it.
static inline Port peek(Net* net, Port var) {
  while (get_tag(var) == VAR) {
    Port val = vars_load(net, get_val(var));
    if (val == NONE) break;
    if (val == 0) break;
    var = val;
  }
  return var;
}

// Finds a variable's value.
static inline Port enter(Net* net, Port var) {
  // While `B` is VAR: extend it (as an optimization)
  while (get_tag(var) == VAR) {
    // Takes the current `var` substitution as `val`
    Port val = vars_exchange(net, get_val(var), NONE);
    // If there was no `val`, stop, as there is no extension
    if (val == NONE || val == 0) {
      break;
    }
    // Otherwise, delete `B` (we own both) and continue
    vars_take(net, get_val(var));
    var = val;
  }
  return var;
}

// Atomically Links `A ~ B`.
static inline void link(Net* net, TM* tm, Port A, Port B) {
  // Attempts to directionally point `A ~> B`
  while (true) {
    // If `A` is NODE: swap `A` and `B`, and continue
    if (get_tag(A) != VAR && get_tag(B) == VAR) {
      Port X = A; A = B; B = X;
    }

    // If `A` is NODE: create the `A ~ B` redex
    if (get_tag(A) != VAR) {
      push_redex(net, tm, new_pair(A, B)); // TODO: move global ports to local
      break;
    }

    // Extends B (as an optimization)
    B = enter(net, B);

    // Since `A` is VAR: point `A ~> B`.
    // Stores `A -> B`, taking the current `A` subst as `A'`
    Port A_ = vars_exchange(net, get_val(A), B);
    // If there was no `A'`, stop, as we lost B's ownership
    if (A_ == NONE) {
      break;
    }
    //if (A_ == 0) { ? } // FIXME: must handle on the move-to-global algo
    // Otherwise, delete `A` (we own both) and link `A' ~ B`
    vars_take(net, get_val(A));
    A = A_;
  }
}

// Links `A ~ B` (as a pair).
static inline void link_pair(Net* net, TM* tm, Pair AB) {
  link(net, tm, get_fst(AB), get_snd(AB));
}

// Interactions
// ------------

// The Link Interaction.
static inline bool interact_link(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 0, 0)) {
    debug("interact_link: get_resources failed\n");
    return false;
  }

  // Links.
  link_pair(net, tm, new_pair(a, b));

  return true;
}

// Declared here for use in call interactions.
static inline bool interact_eras(Net* net, TM* tm, Port a, Port b);

// The Call Interaction.
#ifdef COMPILED
///COMPILED_INTERACT_DREF///
#else
static inline bool interact_call(Net* net, TM* tm, Port a, Port b, Book* book) {
  // Loads Definition.
  u32  fid = get_val(a) & 0xFFFFFFF;
  Def* def = &book->defs_buf[fid];

  // Copy Optimization.
  if (def->safe && get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }

  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, def->rbag_len + 1, def->node_len, def->vars_len)) {
    debug("interact_call: get_resources failed\n");
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
static inline bool interact_void(Net* net, TM* tm, Port a, Port b) {
  return true;
}

// The Eras Interaction.
static inline bool interact_eras(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    debug("interact_eras: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  Pair B  = node_exchange(net, get_val(b), 0);
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links.
  link_pair(net, tm, new_pair(a, B1));
  link_pair(net, tm, new_pair(a, B2));

  return true;
}

// The Anni Interaction.
static inline bool interact_anni(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    debug("interact_anni: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
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
static inline bool interact_comm(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 4, 4, 4)) {
    debug("interact_comm: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
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

// The Lazy Beta Reduction Interaction
// #λ(a b) ~ #@(c d)
// --------------- BETA
// a ~ #W(i #H(i c))
// b ~ d
static inline bool interact_beta(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 2, 2, 1)) {
    debug("interact_beta: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair A = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new vars
  vars_create(net, tm->vloc[0], NONE);

  // Stores new nodes
  node_create(net, tm->nloc[0], new_pair(new_port(VAR, tm->vloc[0]), B1));
  node_create(net, tm->nloc[1], new_pair(new_port(VAR, tm->vloc[0]), new_port(HLD, tm->nloc[0])));

  // Links
  link_pair(net, tm, new_pair(A2, B2));
  link_pair(net, tm, new_pair(new_port(WAI, tm->nloc[1]), A1));

  return true;
}

// Lambda evaluation interaction
// #λ(a b) ~ #E(c *)
// --------------- EVAL-LAM
// c ~ #λ(a i)
// #E(i *) ~ b
static inline bool interact_elam(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 2, 2, 1)) {
    debug("interact_elam: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair A = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);

  // Stores new vars
  vars_create(net, tm->vloc[0], NONE);

  // Stores new nodes
  node_create(net, tm->nloc[0], new_pair(A1, new_port(VAR, tm->vloc[0])));
  node_create(net, tm->nloc[1], new_pair(new_port(VAR, tm->vloc[0]), new_port(ERA, 0)));

  // Links
  link_pair(net, tm, new_pair(B1, new_port(LAM, tm->nloc[0])));
  link_pair(net, tm, new_pair(new_port(EVL, tm->nloc[1]), A2));

  return true;
}

// Dup evaluation interaction
// #d(a b) ~ #E(c *)
// --------------- EVAL-DUP
// #d(a b) ~ c
static inline bool interact_edup(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 1, 0, 0)) {
    debug("interact_edup: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);

  // Links
  link_pair(net, tm, new_pair(a, B1));

  return true;
}

// Wait evaluation interaction
// #E(a *) ~ #W(c d)
// --------------- EVAL-WAI
// #E(a *) ~ c
// #C      ~ d
static inline bool interact_ewai(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 2, 0, 0)) {
    debug("interact_ewai: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links
  link_pair(net, tm, new_pair(a, B1));
  link_pair(net, tm, new_pair(new_port(CAL, 0), B2));

  return true;
}

// Application wait interaction
// #@(a b) ~ #W(c d)
// --------------- WAIT-APP
// b ~ #W(i #H(#@(a i) #W(c d)))
static inline bool interact_wapp(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 1, 3, 1)) {
    debug("interact_wapp: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair A = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);

  // Stores new vars
  vars_create(net, tm->vloc[0], NONE);

  // Stores new nodes
  node_create(net, tm->nloc[0], new_pair(A1, new_port(VAR, tm->vloc[0])));
  node_create(net, tm->nloc[1], new_pair(new_port(APP, tm->nloc[0]), b));
  node_create(net, tm->nloc[2], new_pair(new_port(VAR, tm->vloc[0]), new_port(HLD, tm->nloc[1])));

  // Links
  link_pair(net, tm, new_pair(A2, new_port(WAI, tm->nloc[2])));

  return true;
}

// Duplication wait interaction
// #d(a b) ~ #W(c d)
// --------------- WAIT-DUP
// a ~ #W(i j)
// b ~ #W(k l)
// j ~ l ~ #D(d)
// c ~ #d(i k)
static inline bool interact_wdup(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 3, 4, 2)) {
    debug("interact_wdup: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair A = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new vars
  vars_create(net, tm->vloc[0], NONE);
  vars_create(net, tm->vloc[1], NONE);

  // Stores new nodes
  node_create(net, tm->nloc[0], new_pair(B2, new_port(ERA, 0)));
  node_create(net, tm->nloc[1], new_pair(new_port(VAR, tm->vloc[0]), new_port(DCD, tm->nloc[0])));
  node_create(net, tm->nloc[2], new_pair(new_port(VAR, tm->vloc[1]), new_port(DCD, tm->nloc[0])));
  node_create(net, tm->nloc[3], new_pair(new_port(VAR, tm->vloc[0]), new_port(VAR, tm->vloc[1])));

  // Links
  link_pair(net, tm, new_pair(A1, new_port(WAI, tm->nloc[1])));
  link_pair(net, tm, new_pair(A2, new_port(WAI, tm->nloc[2])));
  link_pair(net, tm, new_pair(B1, new_port(DUP, tm->nloc[3])));

  return true;
}

// Call hold interaction
// #C ~ #H(a b)
// --------------- CALL-HLD
// #E(a *) ~ b
static inline bool interact_chld(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars
  if (!get_resources(net, tm, 1, 1, 0)) {
    debug("interact_chld: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair B = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Store new nodes
  node_create(net, tm->nloc[0], new_pair(B1, new_port(ERA, 0)));

  // Links
  link_pair(net, tm, new_pair(new_port(EVL, tm->nloc[0]), B2));

  return true;
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
// -----------
static inline bool interact_cdcd(Net* net, TM* tm, Port a, Port b) {
  if (!get_resources(net, tm, 1, 0, 0)) {
    debug("interact_cdcd: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair B = node_load(net, get_val(b));
  Pair B_ = new_pair(get_fst(B), new_port(CAL, 1));
  B = node_exchange(net, get_val(b), B_);
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  switch (get_val(B2)) {
    case 0: // First to reach
      link_pair(net, tm, new_pair(B1, new_port(CAL, 0)));
      return true;
    case 1: // Second to reach, previous was CDCD
      node_take(net, get_val(b));
      return true;
    case 2: // Second to reach, previous was EDCD
      node_take(net, get_val(b));
      link_pair(net, tm, new_pair(B1, new_port(CAL, 1)));
      return true;
    default:
      debug("interact_cdcd: Invalid CDCD state\n");
      return false;
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
static inline bool interact_edcd(Net* net, TM* tm, Port a, Port b) {
  if (!get_resources(net, tm, 1, 0, 0)) {
    debug("interact_edcd: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports
  Pair B = node_load(net, get_val(b));
  Pair B_ = new_pair(get_fst(B), new_port(CAL, 2));
  B = node_exchange(net, get_val(b), B_);
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  switch (get_val(B2)) {
    case 0: // First to reach
      return true;
    case 1: // Second to reach, previous was CDCD
      node_take(net, get_val(b));
      return true;
    case 2: // Second to reach, previous was EDCD
      node_take(net, get_val(b));
      link_pair(net, tm, new_pair(B1, new_port(ERA, 0)));
      return true;
    default:
      debug("interact_edcd: Invalid EDCD state\n");
      return false;
  }
}

// Error interaction
static inline bool interact_err(Net* net, TM* tm, Port a, Port b) {
  debug("interact_err: Invalid redex pair: %d ~ %d\n", get_tag(a), get_tag(b));
  return false;
}

// Pops a local redex and performs a single interaction.
static inline bool interact(Net* net, TM* tm, Book* book) {
  // Pops a redex.
  Pair redex = pop_redex(net, tm);

  // If there is no redex, stop.
  if (redex != 0) {
    // Gets redex ports A and B.
    Port a = get_fst(redex);
    Port b = get_snd(redex);

    // Gets the rule type.
    Rule rule = get_rule(a, b);

    // Used for root redex.
    if (get_tag(a) == REF && b == ROOT) {
      rule = DREF;
    // Swaps ports if necessary.
    } else if (should_swap(a,b)) {
      swap(&a, &b);
    }

    // Dispatches interaction rule.
    bool success;
    switch (rule) {
      case LINK: success = interact_link(net, tm, a, b); break;
      #ifdef COMPILED
      case DREF: success = interact_call(net, tm, a, b); break;
      #else
      case DREF: success = interact_call(net, tm, a, b, book); break;
      #endif
      case VOID: success = interact_void(net, tm, a, b); break; 
      case ERAS: success = interact_eras(net, tm, a, b); break;
      case ANNI: success = interact_anni(net, tm, a, b); break;
      case COMM: success = interact_comm(net, tm, a, b); break;
      case BETA: success = interact_beta(net, tm, a, b); break;
      case ELAM: success = interact_elam(net, tm, a, b); break;
      case EDUP: success = interact_edup(net, tm, a, b); break;
      case EWAI: success = interact_ewai(net, tm, a, b); break;
      case WAPP: success = interact_wapp(net, tm, a, b); break;
      case WDUP: success = interact_wdup(net, tm, a, b); break;
      case CHLD: success = interact_chld(net, tm, a, b); break;
      case CDCD: success = interact_cdcd(net, tm, a, b); break;
      case EDCD: success = interact_edcd(net, tm, a, b); break;
      case ERR_: success = interact_err(net, tm, a, b); break;
    }

    // If error, pushes redex back.
    if (!success) {
      push_redex(net, tm, redex);
      return false;
    // Else, increments the interaction count.
    } else if (rule != LINK) {
      tm->itrs += 1;
    }
  }

  return true;
}

// Evaluator
// ---------

void evaluator(Net* net, TM* tm, Book* book) {
  // Initializes the global idle counter
  atomic_store_explicit(&net->idle, TPC - 1, memory_order_relaxed);
  sync_threads();

  // Performs some interactions
  u32  tick = 0;
  bool busy = tm->tid == 0;
  while (true) {
    tick += 1;

    // If we have redexes...
    if (rbag_len(net, tm) > 0) {
      // Update global idle counter
      if (!busy) atomic_fetch_sub_explicit(&net->idle, 1, memory_order_relaxed);
      busy = true;

      // Perform an interaction
      #ifdef DEBUG
      if (!interact(net, tm, book)) debug("interaction failed\n");
      #else
      interact(net, tm, book);
      #endif
    // If we have no redexes...
    } else {
      // Update global idle counter
      if (busy) atomic_fetch_add_explicit(&net->idle, 1, memory_order_relaxed);
      busy = false;

      //// Peeks a redex from target
      u32 sid = (tm->tid - 1) % TPC;
      u32 idx = sid*(G_RBAG_LEN/TPC) + (tm->sidx++);

      // Stealing Everything: this will steal all redexes

      Pair got = atomic_exchange_explicit(&net->rbag_buf[idx], 0, memory_order_relaxed);
      if (got != 0) {
        push_redex(net, tm, got);
        continue;
      } else {
        tm->sidx = 0;
      }

      // Chill...
      sched_yield();
      // Halt if all threads are idle
      if (tick % 256 == 0) {
        if (atomic_load_explicit(&net->idle, memory_order_relaxed) == TPC) {
          break;
        }
      }
    }
  }

  sync_threads();

  atomic_fetch_add(&net->itrs, tm->itrs);
  tm->itrs = 0;
}

// Normalizer
// ----------

// Thread data
typedef struct {
  Net*  net;
  TM*   tm;
  Book* book;
} ThreadArg;

void* thread_func(void* arg) {
  ThreadArg* data = (ThreadArg*)arg;
  evaluator(data->net, data->tm, data->book);
  return NULL;
}

// Sets the initial redex.
void boot_redex(Net* net, Pair redex) {
  net->vars_buf[get_val(ROOT)] = NONE;
  net->rbag_buf[0] = redex;
}

// Evaluates all redexes.
// TODO: cache threads to avoid spawning overhead
void normalize(Net* net, Book* book) {
  // Inits thread_arg objects
  ThreadArg thread_arg[TPC];
  for (u32 t = 0; t < TPC; ++t) {
    thread_arg[t].net  = net;
    thread_arg[t].tm   = tm[t];
    thread_arg[t].book = book;
  }

  // Spawns the evaluation threads
  pthread_t threads[TPC];
  for (u32 t = 0; t < TPC; ++t) {
    pthread_create(&threads[t], NULL, thread_func, &thread_arg[t]);
  }

  // Wait for the threads to finish
  for (u32 t = 0; t < TPC; ++t) {
    pthread_join(threads[t], NULL);
  }
}

// Util: expands a REF Port.
Port expand(Net* net, Book* book, Port port) {
  Port old = vars_load(net, get_val(ROOT));
  Port got = peek(net, port);
  while (get_tag(got) == REF) {
    boot_redex(net, new_pair(got, ROOT));
    normalize(net, book);
    got = peek(net, vars_load(net, get_val(ROOT)));
  }
  vars_create(net, get_val(ROOT), old);
  return got;
}

// Book Loader
// -----------

bool book_load(Book* book, u32* buf) {
  // Reads defs_len
  book->defs_len = *buf++;

  // Parses each def
  for (u32 i = 0; i < book->defs_len; ++i) {
    // Reads fid
    u32 fid = *buf++;

    // Gets def
    Def* def = &book->defs_buf[fid];

    // Reads name
    memcpy(def->name, buf, 256);
    buf += 64;

    // Reads safe flag
    def->safe = *buf++;

    // Reads lengths
    def->rbag_len = *buf++;
    def->node_len = *buf++;
    def->vars_len = *buf++;

    if (def->rbag_len > DEF_RBAG_LEN) {
      fprintf(stderr, "def '%s' has too many redexes: %u\n", def->name, def->rbag_len);
      return false;
    }

    if (def->node_len > DEF_NODE_LEN) {
      fprintf(stderr, "def '%s' has too many nodes: %u\n", def->name, def->node_len);
      return false;
    }

    // Reads root
    def->root = *buf++;

    // Reads rbag_buf
    memcpy(def->rbag_buf, buf, 8*def->rbag_len);
    buf += def->rbag_len * 2;

    // Reads node_buf
    memcpy(def->node_buf, buf, 8*def->node_len);
    buf += def->node_len * 2;
  }

  return true;
}

void pretty_print_port(Net* net, Book* book, Port port) {
  Port stack[4096];
  stack[0] = port;
  u32 len = 1;
  u32 num = 0;
  while (len > 0) {
    Port cur = stack[--len];
    switch (get_tag(cur)) {
      case LAM: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case APP: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("!(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case ERA: {
        if (get_val(cur) != 0) {
          printf("%c", (char)get_val(cur));
        } else {
          printf("*");
        }
        break;
      }
      case VAR: {
        Port got = vars_load(net, get_val(cur));
        if (got != NONE) {
          stack[len++] = got;
        } else {
          printf("x%x", get_val(cur));
        }
        break;
      }
      case DUP: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("#d(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case REF: {
        u32  fid = get_val(cur) & 0xFFFFFFF;
        Def* def = &book->defs_buf[fid];
        printf("@%s", def->name);
        break;
      }
      case CAL: {
        printf("#C");
        break;
      }
      case EVL: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("#E(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p1;
        break;
      }
      case WAI: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("#W(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p1;
        break;
      }
      case HLD: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("#H(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p1;
        break;
      }
      case DCD: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("#D(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p1;
        break;
      }
    }
  }
}


//COMPILED_BOOK_BUF//

#ifdef IO
void do_run_io(Net* net, Book* book, Port port);
#endif

// Main
// ----

void hvm_c(u32* book_buffer) {
  // Creates static TMs
  alloc_static_tms();

  // Loads the Book
  Book* book = NULL;
  if (book_buffer) {
    book = (Book*)malloc(sizeof(Book));
    if (!book_load(book, book_buffer)) {
      fprintf(stderr, "failed to load book\n");
      return;
    }
  }

  // GMem
  Net *net = net_new();

  // Starts the timer
  u64 start = time64();

  // Creates an initial redex that calls main
  boot_redex(net, new_pair(new_port(REF, 0), ROOT));

  printf("Starting evaluation...\n");

  normalize(net, book);

  // Prints the result
  printf("Result: ");
  pretty_print_port(net, book, enter(net, ROOT));
  printf("\n");

  // Stops the timer
  double duration = (time64() - start) / 1000000000.0; // seconds

  // Prints interactions and time
  u64 itrs = atomic_load(&net->itrs);
  printf("- ITRS: %" PRIu64 "\n", itrs);
  printf("- TIME: %.2fs\n", duration);
  printf("- MIPS: %.2f\n", (double)itrs / duration / 1000000.0);

  // Frees everything
  free_static_tms();
  free(net);
  free(book);
}

#ifdef WITH_MAIN
int main() {
  hvm_c((u32*)BOOK_BUF);
  return 0;
}
#endif
