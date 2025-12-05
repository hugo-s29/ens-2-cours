void max_flow_edmonds_karp_seq(char *graph_file_name, int *flow_value) {
  DEBUG_PRINT("[DEBUG] Entered max_flow_edmonds_karp_seq\n");
  int size = 0;
  MPI_Comm_size(MPI_COMM_WORLD, &size);

  // Check we have indeed one proc only
  if (size > 1) {
    DEBUG_PRINT("sequential algorithm called on %d procs instead of 1 only\n", size);
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  DEBUG_PRINT("[DEBUG] Parsing graph from file: %s\n", graph_file_name);

  // Get the graph
  int N, M, s, t;
  int *in_adj = NULL, *in_w = NULL, *in_adj_beg = NULL;
  int *out_adj = NULL, *out_w = NULL, *out_adj_beg = NULL;
  int in_adj_size = 0, out_adj_size = 0;
  parse_graph(graph_file_name, &N, &M, &s, &t, &out_adj, &out_w, &out_adj_beg, &in_adj,
              &in_w, &in_adj_beg, &in_adj_size, &out_adj_size);

  DEBUG_PRINT("[DEBUG] Graph parsed: N=%d, M=%d, s=%d, t=%d\n", N, M, s, t);

  // Build an explicit residual capacity matrix res[u*N + v].
  // Using a dense matrix is simpler and robust for a sequential implementation.
  int *res = malloc(sizeof(int) * N * N);
  if (!res) {
    fprintf(stderr, "malloc failed for residual matrix\n");
    MPI_Abort(MPI_COMM_WORLD, 1);
  }
  for (int i = 0; i < N * N; ++i)
    res[i] = 0;

  // fill forward capacities from out_adj/out_w
  for (int u = 0; u < N; ++u) {
    for (int i = out_adj_beg[u]; i < out_adj_beg[u + 1]; ++i) {
      int v = out_adj[i];
      int capacity = out_w[i];
      // if multiple edges between same u->v exist, sum capacities
      res[u * N + v] += capacity;
    }
  }

  // Allocate memory for BFS structures
  int *depth = malloc(N * sizeof(int));
  int *parent = malloc(N * sizeof(int));
  int *parent_cap = malloc(N * sizeof(int));
  if (!depth || !parent || !parent_cap) {
    fprintf(stderr, "malloc failed for BFS arrays\n");
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  int found_augmenting_path = 0;
  int max_flow = 0;

  WHEN_DEBUG(int iter = 0);
  do {
    DEBUG_PRINT("[DEBUG] Iteration %d: Starting BFS\n", iter++);
    // 1. BFS from source
    // Initialize BFS structures
    for (int i = 0; i < N; i++) {
      depth[i] = -1; // -1 indicates unvisited
      parent[i] = -1;
      parent_cap[i] = 0;
    }

    // BFS queue
    int *queue = malloc(N * sizeof(int));
    if (!queue) {
      fprintf(stderr, "malloc failed for queue\n");
      MPI_Abort(MPI_COMM_WORLD, 1);
    }
    int front = 0, back = 0;

    // Start BFS from source
    depth[s] = 0;
    queue[back++] = s;

    found_augmenting_path = 0;

    while (front < back) {
      int u = queue[front++];
      DEBUG_PRINT("[DEBUG] Visiting node %d\n", u);
      // iterate over all possible v and check residual capacity
      // (we use dense matrix; for large sparse graphs you can
      //  adapt to iterate over out_adj only but check res[u*N+v])
      for (int v = 0; v < N; ++v) {
        int capacity = res[u * N + v];
        if (depth[v] == -1 && capacity > 0) {
          depth[v] = depth[u] + 1;
          parent[v] = u;
          parent_cap[v] = capacity;
          queue[back++] = v;
          DEBUG_PRINT("[DEBUG]   Found neighbor %d with capacity %d\n", v, capacity);

          // Stop BFS if we reach the sink
          if (v == t) {
            found_augmenting_path = 1;
            DEBUG_PRINT("[DEBUG]   Found augmenting path to sink %d\n", t);
            break;
          }
        }
      }
      if (found_augmenting_path)
        break;
    }

    free(queue);

    // 2. If augmenting path found, backtrack from t to s to find bottleneck
    // capacity
    int bottleneck = 0;
    if (found_augmenting_path) {
      DEBUG_PRINT("[DEBUG] Backtracking to find bottleneck\n");
      // Backtrack from t to s using parent[] to find bottleneck
      bottleneck = INT_MAX;
      for (int v = t; v != s; v = parent[v]) {
        if (parent[v] == -1) {
          DEBUG_PRINT("[DEBUG]   Error: parent[%d] == -1 during backtrack\n", v);
          bottleneck = 0;
          break;
        }
        int u = parent[v];
        int cap_uv = res[u * N + v];
        if (cap_uv < bottleneck) {
          bottleneck = cap_uv;
        }
      }

      if (bottleneck <= 0) {
        DEBUG_PRINT("[DEBUG]   Bottleneck non-positive (%d), terminating\n", bottleneck);
        break;
      }
      DEBUG_PRINT("[DEBUG]   Bottleneck capacity found: %d\n", bottleneck);

      // 3. Update residual capacities along the path
      for (int v = t; v != s; v = parent[v]) {
        int u = parent[v];
        // reduce forward residual
        res[u * N + v] -= bottleneck;
        // increase reverse residual
        res[v * N + u] += bottleneck;
        DEBUG_PRINT("[DEBUG]   Update edge (%d,%d): forward now %d, reverse now %d\n", u,
                    v, res[u * N + v], res[v * N + u]);
      }

      max_flow += bottleneck;
      DEBUG_PRINT("[DEBUG]   Updated max_flow: %d\n", max_flow);
    } else {
      DEBUG_PRINT("[DEBUG] No augmenting path found, terminating.\n");
    }
  } while (found_augmenting_path);

  *flow_value = max_flow;
  DEBUG_PRINT("[DEBUG] Finished. Max flow = %d\n", max_flow);

  // cleanup
  free(res);
  free(depth);
  free(parent);
  free(parent_cap);
  free_graph(&out_adj, &out_adj_beg, &in_adj, &in_adj_beg);

  return;
}
