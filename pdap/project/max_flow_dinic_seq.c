// Edge structure for adjacency lists
typedef struct {
  int to;
  int rev; // index of reverse edge in adj[to]
  int cap; // residual capacity
} Edge;

// Global pointers required by BFS/DFS
static Edge **G_adj = NULL;
static int *G_deg = NULL; // number of edges in each adj[u]
static int *G_level = NULL;
static int *G_iter = NULL;
static int G_N, G_s, G_t;

// BFS: Build level graph, return 1 if t reachable
static int dinic_bfs(void) {
  for (int i = 0; i < G_N; i++)
    G_level[i] = -1;

  int *queue = (int *) malloc(G_N * sizeof(int));
  int head = 0, tail = 0;

  G_level[G_s] = 0;
  queue[tail++] = G_s;

  while (head < tail) {
    int u = queue[head++];
    for (int i = 0; i < G_deg[u]; i++) {
      Edge *e = &G_adj[u][i];
      if (e->cap > 0 && G_level[e->to] < 0) {
        G_level[e->to] = G_level[u] + 1;
        queue[tail++] = e->to;
      }
    }
  }

  free(queue);
  return G_level[G_t] >= 0;
}

// DFS: send blocking flow, returns pushed flow
int dinic_dfs(int u, int f) {
  if (u == G_t)
    return f;

  for (int *it = &G_iter[u]; *it < G_deg[u]; (*it)++) {
    Edge *e = &G_adj[u][*it];
    if (e->cap > 0 && G_level[e->to] == G_level[u] + 1) {
      int ret = dinic_dfs(e->to, f < e->cap ? f : e->cap);
      if (ret > 0) {
        e->cap -= ret;
        G_adj[e->to][e->rev].cap += ret;
        return ret;
      }
    }
  }
  return 0;
}

// Main function
void max_flow_dinic_seq(char *graph_file_name, int *flow_value) {
  // Check we have indeed one proc only
  int size = 0;
  MPI_Comm_size(MPI_COMM_WORLD, &size);

  if (size > 1) {
    printf("sequential algorithm called on %d procs instead of 1 only\n", size);
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  // Get input graph
  int N, M, s, t;
  int *in_adj, *in_w, *in_adj_beg;
  int *out_adj, *out_w, *out_adj_beg;
  int in_adj_size, out_adj_size;

  parse_graph(graph_file_name, &N, &M, &s, &t, &out_adj, &out_w, &out_adj_beg, &in_adj,
              &in_w, &in_adj_beg, &in_adj_size, &out_adj_size);

  G_N = N;
  G_s = s;
  G_t = t;

  // Build residual graph with reverse edges

  // compute degrees for allocation
  int *deg = calloc(N, sizeof(int));
  for (int u = 0; u < N; u++) {
    for (int idx = out_adj_beg[u]; idx < out_adj_beg[u + 1]; idx++) {
      int v = out_adj[idx];
      deg[u]++; // forward
      deg[v]++; // reverse
    }
  }

  G_adj = malloc(N * sizeof(Edge *));
  G_deg = malloc(N * sizeof(int));
  int *next = calloc(N, sizeof(int));

  for (int i = 0; i < N; i++) {
    G_deg[i] = deg[i];
    G_adj[i] = deg[i] ? malloc(deg[i] * sizeof(Edge)) : NULL;
  }

  // add edges (u -> v) and reverse edges (v -> u)
  for (int u = 0; u < N; u++) {
    for (int idx = out_adj_beg[u]; idx < out_adj_beg[u + 1]; idx++) {
      int v = out_adj[idx];
      int cap = out_w[idx];

      int pu = next[u]++;
      int pv = next[v]++;

      // forward
      G_adj[u][pu].to = v;
      G_adj[u][pu].cap = cap;
      G_adj[u][pu].rev = pv;

      // reverse
      G_adj[v][pv].to = u;
      G_adj[v][pv].cap = 0;
      G_adj[v][pv].rev = pu;
    }
  }

  free(deg);
  free(next);

  // allocate level and iteration arrays
  G_level = malloc(N * sizeof(int));
  G_iter = malloc(N * sizeof(int));

  // Dinic main loop
  int flow = 0;
  const int INF = INT_MAX / 4;

  while (dinic_bfs()) {
    for (int i = 0; i < N; i++)
      G_iter[i] = 0;

    int pushed;
    while ((pushed = dinic_dfs(G_s, INF)) > 0)
      flow += pushed;
  }

  *flow_value = flow;

  // free everything
  for (int i = 0; i < N; i++)
    free(G_adj[i]);

  free(G_adj);
  free(G_deg);
  free(G_level);
  free(G_iter);

  free_graph(&out_adj, &out_adj_beg, &in_adj, &in_adj_beg);
}
