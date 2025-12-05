#ifdef ENABLE_DEBUG
#define DEBUG_PRINT(...) printf(__VA_ARGS__)
#define WHEN_DEBUG(x) x
#else
#define DEBUG_PRINT(...) ((void) 0)
#define WHEN_DEBUG(x)
#endif

#include "max_flow_edmonds_karp_seq.c"
#include "max_flow_edmonds_karp_par.c"
#include "max_flow_dinic_seq.c"
#include "max_flow_dinic_par.c"