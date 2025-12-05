void max_flow_edmonds_karp_par(char *graph_file_name, int *flow_value) {
  DEBUG_PRINT("[DEBUG] Entered max_flow_edmonds_karp_par\n");

  int rank, size;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);

  // Parse the graph
  int N, M, s, t;
  int *in_adj = NULL, *in_w = NULL, *in_adj_beg = NULL;
  int *out_adj = NULL, *out_w = NULL, *out_adj_beg = NULL;
  int in_adj_size = 0, out_adj_size = 0;
  parse_graph(graph_file_name, &N, &M, &s, &t, &out_adj, &out_w, &out_adj_beg, &in_adj,
              &in_w, &in_adj_beg, &in_adj_size, &out_adj_size);

  DEBUG_PRINT("[DEBUG] Rank %d: Graph parsed: N=%d, M=%d, s=%d, t=%d\n", rank, N, M, s,
              t);

  int n_local = nb_local_vertices(N);

  // Build local residual capacity
  int *local_res = malloc(sizeof(int) * out_adj_size);
  if (!local_res) {
    fprintf(stderr, "malloc failed for local residual capacities\n");
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  for (int i = 0; i < out_adj_size; ++i) {
    local_res[i] = out_w[i];
  }

  // Reverse edges
  int *rev_adj = malloc(sizeof(int) * in_adj_size);
  int *rev_res = malloc(sizeof(int) * in_adj_size);
  int *rev_adj_beg = malloc(sizeof(int) * (n_local + 1));
  if (!rev_adj || !rev_res || !rev_adj_beg) {
    fprintf(stderr, "malloc failed for reverse structures\n");
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  for (int i = 0; i < in_adj_size; ++i) {
    rev_adj[i] = in_adj[i];
    rev_res[i] = 0;
  }
  for (int i = 0; i <= n_local; ++i) {
    rev_adj_beg[i] = in_adj_beg[i];
  }

  // Global arrays for BFS
  int *depth = malloc(sizeof(int) * N);
  int *parent = malloc(sizeof(int) * N);
  int *parent_cap = malloc(sizeof(int) * N);

  if (!depth || !parent || !parent_cap) {
    fprintf(stderr, "malloc failed for BFS arrays\n");
    MPI_Abort(MPI_COMM_WORLD, 1);
  }

  int found_augmenting_path = 0;
  WHEN_DEBUG(int iter = 0);

  do {
    DEBUG_PRINT("[DEBUG] Rank %d: Iteration %d\n", rank, iter++);

    // Initialize BFS arrays
    for (int i = 0; i < N; i++) {
      depth[i] = N + 1;
      parent[i] = -1;
      parent_cap[i] = 0;
    }
    depth[s] = 0;

    // Encode parent and capacity together to keep them matched
    long long *parent_encoded = malloc(sizeof(long long) * N);
    long long *local_parent_encoded = malloc(sizeof(long long) * N);

    for (int i = 0; i < N; i++) {
      parent_encoded[i] = LLONG_MAX;
      local_parent_encoded[i] = LLONG_MAX;
    }

    // BFS
    int todo = 1;
    while (todo) {
      todo = 0;

      // Reset local proposals
      for (int i = 0; i < N; i++) {
        local_parent_encoded[i] = LLONG_MAX;
      }

      // Each process processes ONLY its local vertices
      for (int u_local = 0; u_local < n_local; u_local++) {
        int u_global = global_of_local_index(u_local, N);

        if (depth[u_global] != N + 1) {
          int next_depth = depth[u_global] + 1;

          // Check outgoing edges u->v
          for (int e = out_adj_beg[u_local]; e < out_adj_beg[u_local + 1]; e++) {
            int v = out_adj[e];
            int cap = local_res[e];

            if (cap > 0 && next_depth < depth[v]) {
              // Encode: lower 32 bits = parent, upper 32 bits = INT_MAX - cap
              // (for MIN selection with higher cap priority)
              long long encoded = ((long long) (INT_MAX - cap) << 32) | u_global;
              if (encoded < local_parent_encoded[v]) {
                local_parent_encoded[v] = encoded;
                todo = 1;
              }
            }
          }

          // Check reverse edges u->v
          for (int e = rev_adj_beg[u_local]; e < rev_adj_beg[u_local + 1]; e++) {
            int v = rev_adj[e];
            int cap = rev_res[e];

            if (cap > 0 && next_depth < depth[v]) {
              long long encoded = ((long long) (INT_MAX - cap) << 32) | u_global;
              if (encoded < local_parent_encoded[v]) {
                local_parent_encoded[v] = encoded;
                todo = 1;
              }
            }
          }
        }
      }

      // Synchronize
      MPI_Allreduce(MPI_IN_PLACE, &todo, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);

      if (!todo)
        break;

      MPI_Allreduce(local_parent_encoded, parent_encoded, N, MPI_LONG_LONG, MPI_MIN,
                    MPI_COMM_WORLD);

      // Update depth, parent, and parent_cap based on reduced encoded values
      for (int v = 0; v < N; v++) {
        if (parent_encoded[v] != LLONG_MAX && depth[v] == N + 1) {
          int u = (int) (parent_encoded[v] & 0xFFFFFFFF);
          int cap = INT_MAX - (int) (parent_encoded[v] >> 32);
          depth[v] = depth[u] + 1;
          parent[v] = u;
          parent_cap[v] = cap;
        }
      }

      // Early exit if we reached the sink
      if (depth[t] != N + 1) {
        break;
      }
    }

    free(parent_encoded);
    free(local_parent_encoded);

    found_augmenting_path = (depth[t] != N + 1);

    if (found_augmenting_path) {
      DEBUG_PRINT("[DEBUG] Rank %d: Augmenting path found\n", rank);

      // Find bottleneck capacity in the augmenting path
      int bottleneck = INT_MAX;
      int v = t;
      while (v != s) {
        if (parent[v] == -1) { // If parent is invalid, path is broken
          found_augmenting_path = 0;
          break;
        }
        int cap = parent_cap[v]; // Capacity of the edge in the path
        if (cap < bottleneck)    // Update bottleneck to the minimum capacity
          bottleneck = cap;
        v = parent[v]; // Move to the parent vertex
      }

      // If no valid path or bottleneck is invalid, exit the loop
      if (!found_augmenting_path || bottleneck <= 0) {
        DEBUG_PRINT("[DEBUG] Rank %d: Invalid path or bottleneck, breaking\n", rank);
        break;
      }

      DEBUG_PRINT("[DEBUG] Rank %d: Bottleneck = %d\n", rank, bottleneck);

      // Update residual capacities along the augmenting path
      v = t;
      while (v != s) {
        int u = parent[v];                  // Parent vertex
        int u_owner = proc_of_vertex(u, N); // Owner process of u
        int v_owner = proc_of_vertex(v, N); // Owner process of v

        // Update forward edge u->v if the current process owns u
        if (rank == u_owner) {
          int u_local = local_of_global_index(u, N); // Local index of u
          int found_edge = 0;

          // Check outgoing edges of u
          for (int i = out_adj_beg[u_local]; i < out_adj_beg[u_local + 1]; i++) {
            if (out_adj[i] == v) {        // If edge u->v is found
              local_res[i] -= bottleneck; // Reduce residual capacity
              found_edge = 1;
              break;
            }
          }

          // If not found in outgoing edges, check reverse edges
          if (!found_edge) {
            for (int i = rev_adj_beg[u_local]; i < rev_adj_beg[u_local + 1]; i++) {
              if (rev_adj[i] == v) {      // If reverse edge u->v is found
                rev_res[i] -= bottleneck; // Reduce reverse residual capacity
                break;
              }
            }
          }
        }

        // Update reverse edge v->u if the current process owns v
        if (rank == v_owner) {
          int v_local = local_of_global_index(v, N); // Local index of v
          int found_edge = 0;

          // Check reverse edges of v
          for (int i = rev_adj_beg[v_local]; i < rev_adj_beg[v_local + 1]; i++) {
            if (rev_adj[i] == u) {      // If reverse edge v->u is found
              rev_res[i] += bottleneck; // Increase reverse residual capacity
              found_edge = 1;
              break;
            }
          }

          // If not found in reverse edges, check outgoing edges
          if (!found_edge) {
            for (int i = out_adj_beg[v_local]; i < out_adj_beg[v_local + 1]; i++) {
              if (out_adj[i] == u) {        // If edge v->u is found
                local_res[i] += bottleneck; // Increase residual capacity
                break;
              }
            }
          }
        }

        v = u; // Move to the parent vertex
      }
    }
  } while (found_augmenting_path);

  // Compute flow value at source
  if (rank == proc_of_vertex(s, N)) {
    int s_local = local_of_global_index(s, N);
    int total_flow = 0;
    for (int i = out_adj_beg[s_local]; i < out_adj_beg[s_local + 1]; i++) {
      total_flow += (out_w[i] - local_res[i]);
    }
    *flow_value = total_flow;
  }

  int s_owner = proc_of_vertex(s, N);
  MPI_Bcast(flow_value, 1, MPI_INT, s_owner, MPI_COMM_WORLD);

  DEBUG_PRINT("[DEBUG] Rank %d: Max flow = %d\n", rank, *flow_value);

  // Cleanup
  free(local_res);
  free(rev_adj);
  free(rev_res);
  free(rev_adj_beg);
  free(depth);
  free(parent);
  free(parent_cap);
  free_graph(&out_adj, &out_adj_beg, &in_adj, &in_adj_beg);
}
