// Parallel BFS to build level graph
static int parallel_bfs(int N, int s, int t, int n_local, int *out_adj, int *out_adj_beg,
                        int *local_res, int *rev_adj, int *rev_adj_beg, int *rev_res,
                        int *level) {
  for (int i = 0; i < N; i++) {
    level[i] = -1;
  }
  level[s] = 0;

  long long *local_proposals = malloc(sizeof(long long) * N);
  long long *global_proposals = malloc(sizeof(long long) * N);

  for (int i = 0; i < N; i++) {
    local_proposals[i] = LLONG_MAX;
  }

  int todo = 1;
  while (todo) {
    todo = 0;

    for (int i = 0; i < N; i++) {
      local_proposals[i] = LLONG_MAX;
    }

    // Iterate over all local vertices
    for (int u_local = 0; u_local < n_local; u_local++) {
      int u = global_of_local_index(u_local, N);

      // Check if the current vertex has been assigned a level
      if (level[u] != -1) {
        int next_level = level[u] + 1;

        // Explore outgoing edges
        for (int e = out_adj_beg[u_local]; e < out_adj_beg[u_local + 1]; e++) {
          int v = out_adj[e];
          // If the edge has residual capacity and the target vertex has not been visited
          if (local_res[e] > 0 && level[v] == -1) {
            // Propose the next level for vertex v
            local_proposals[v] = ((long long) next_level << 32) | 1;
            todo = 1; // Mark that there is more work to do
          }
        }

        // Explore reverse edges
        for (int e = rev_adj_beg[u_local]; e < rev_adj_beg[u_local + 1]; e++) {
          int v = rev_adj[e];
          // If the reverse edge has residual capacity and the target vertex has not been
          // visited
          if (rev_res[e] > 0 && level[v] == -1) {
            // Propose the next level for vertex v
            local_proposals[v] = ((long long) next_level << 32) | 1;
            todo = 1; // Mark that there is more work to do
          }
        }
      }
    }

    MPI_Allreduce(MPI_IN_PLACE, &todo, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);
    if (!todo)
      break;

    MPI_Allreduce(local_proposals, global_proposals, N, MPI_LONG_LONG, MPI_MIN,
                  MPI_COMM_WORLD);

    // Update levels of vertices based on global proposals
    for (int v = 0; v < N; v++) {
      if (global_proposals[v] != LLONG_MAX && level[v] == -1) {
        // Extract the proposed level from the global proposal and assign it to vertex v
        level[v] = (int) (global_proposals[v] >> 32);
      }
    }

    if (level[t] != -1)
      break;
  }

  free(local_proposals);
  free(global_proposals);

  return (level[t] != -1);
}

// Find ONE augmenting path using level graph (like Edmonds-Karp but respecting
// levels)
static int find_augmenting_path_with_levels(int N, int s, int t, int n_local,
                                            int *out_adj, int *out_adj_beg,
                                            int *local_res, int *rev_adj,
                                            int *rev_adj_beg, int *rev_res, int *level,
                                            int *parent, int *parent_cap) {
  for (int i = 0; i < N; i++) {
    parent[i] = -1;
    parent_cap[i] = 0;
  }

  long long *local_proposals = malloc(sizeof(long long) * N);
  long long *global_proposals = malloc(sizeof(long long) * N);

  for (int i = 0; i < N; i++) {
    local_proposals[i] = LLONG_MAX;
  }

  int *visited = calloc(N, sizeof(int));
  visited[s] = 1;

  int found = 0;
  // Loop until an augmenting path is found or no more paths exist
  while (!found) {
    int todo = 0;

    // Reset local proposals for this iteration
    for (int i = 0; i < N; i++) {
      local_proposals[i] = LLONG_MAX;
    }

    // Explore from visited vertices
    for (int u_local = 0; u_local < n_local; u_local++) {
      int u = global_of_local_index(u_local, N);

      // Only explore vertices that have been visited and are part of the level graph
      if (visited[u] && level[u] != -1) {
        // Explore outgoing edges to the next level
        for (int e = out_adj_beg[u_local]; e < out_adj_beg[u_local + 1]; e++) {
          int v = out_adj[e];
          if (local_res[e] > 0 && !visited[v] && level[v] == level[u] + 1) {
            // Encode the proposal with capacity and parent vertex
            long long encoded = ((long long) (INT_MAX - local_res[e]) << 32) | u;
            if (encoded < local_proposals[v]) {
              local_proposals[v] = encoded;
              todo = 1; // Mark that there is more work to do
            }
          }
        }

        // Explore reverse edges to the next level
        for (int e = rev_adj_beg[u_local]; e < rev_adj_beg[u_local + 1]; e++) {
          int v = rev_adj[e];
          if (rev_res[e] > 0 && !visited[v] && level[v] == level[u] + 1) {
            // Encode the proposal with capacity and parent vertex
            long long encoded = ((long long) (INT_MAX - rev_res[e]) << 32) | u;
            if (encoded < local_proposals[v]) {
              local_proposals[v] = encoded;
              todo = 1; // Mark that there is more work to do
            }
          }
        }
      }
    }

    // Check if there is more work to do across all processes
    MPI_Allreduce(MPI_IN_PLACE, &todo, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);
    if (!todo)
      break;

    // Combine proposals from all processes
    MPI_Allreduce(local_proposals, global_proposals, N, MPI_LONG_LONG, MPI_MIN,
                  MPI_COMM_WORLD);

    // Update visited vertices and parent information based on global proposals
    for (int v = 0; v < N; v++) {
      if (global_proposals[v] != LLONG_MAX && !visited[v]) {
        visited[v] = 1;
        parent[v] = (int) (global_proposals[v] & 0xFFFFFFFF); // Extract parent vertex
        parent_cap[v] = INT_MAX - (int) (global_proposals[v] >> 32); // Extract capacity

        // If the sink is reached, stop the search
        if (v == t) {
          found = 1;
          break;
        }
      }
    }

    if (found)
      break;
  }

  free(local_proposals);
  free(global_proposals);
  free(visited);

  return found;
}

void max_flow_dinic_par(char *graph_file_name, int *flow_value) {
  DEBUG_PRINT("[DEBUG] Entered max_flow_dinic_par\n");

  int rank, size;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);

  int N, M, s, t;
  int *in_adj = NULL, *in_w = NULL, *in_adj_beg = NULL;
  int *out_adj = NULL, *out_w = NULL, *out_adj_beg = NULL;
  int in_adj_size = 0, out_adj_size = 0;
  parse_graph(graph_file_name, &N, &M, &s, &t, &out_adj, &out_w, &out_adj_beg, &in_adj,
              &in_w, &in_adj_beg, &in_adj_size, &out_adj_size);

  DEBUG_PRINT("[DEBUG] Rank %d: Graph parsed: N=%d, M=%d, s=%d, t=%d\n", rank, N, M, s,
              t);

  int n_local = nb_local_vertices(N);

  int *local_res = malloc(sizeof(int) * out_adj_size);
  for (int i = 0; i < out_adj_size; ++i) {
    local_res[i] = out_w[i];
  }

  int *rev_adj = malloc(sizeof(int) * in_adj_size);
  int *rev_res = malloc(sizeof(int) * in_adj_size);
  int *rev_adj_beg = malloc(sizeof(int) * (n_local + 1));
  for (int i = 0; i < in_adj_size; ++i) {
    rev_adj[i] = in_adj[i];
    rev_res[i] = 0;
  }
  for (int i = 0; i <= n_local; ++i) {
    rev_adj_beg[i] = in_adj_beg[i];
  }

  int *level = malloc(sizeof(int) * N);
  int *parent = malloc(sizeof(int) * N);
  int *parent_cap = malloc(sizeof(int) * N);

  int total_flow = 0;
  WHEN_DEBUG(int phase = 0);

  // Main Dinic loop
  while (1) {
    DEBUG_PRINT("[DEBUG] Rank %d: Phase %d\n", rank, phase++);

    // Build level graph
    if (!parallel_bfs(N, s, t, n_local, out_adj, out_adj_beg, local_res, rev_adj,
                      rev_adj_beg, rev_res, level)) {
      DEBUG_PRINT("[DEBUG] Rank %d: No level graph found\n", rank);
      break;
    }

    // Find blocking flow by repeatedly finding augmenting paths that respect
    // levels
    int phase_flow = 0;
    int found_path = 1;

    // While there are augmenting paths in the level graph
    while (found_path) {
      // Find an augmenting path that respects levels
      found_path = find_augmenting_path_with_levels(
          N, s, t, n_local, out_adj, out_adj_beg, local_res, rev_adj, rev_adj_beg,
          rev_res, level, parent, parent_cap);

      if (found_path) {
        // Determine the bottleneck capacity of the augmenting path
        int bottleneck = INT_MAX;
        int v = t;
        while (v != s) {
          if (parent[v] == -1) {
            found_path = 0; // Path is invalid, stop processing
            break;
          }
          int cap = parent_cap[v];
          if (cap < bottleneck)
            bottleneck = cap; // Update bottleneck capacity
          v = parent[v];
        }

        if (!found_path || bottleneck <= 0)
          break; // No valid path or bottleneck is zero, stop processing

        // Update residual capacities along the augmenting path
        v = t;
        while (v != s) {
          int u = parent[v];
          int u_owner = proc_of_vertex(u, N);
          int v_owner = proc_of_vertex(v, N);

          // Update residual capacities for edges owned by the current process
          if (rank == u_owner) {
            int u_local = local_of_global_index(u, N);
            int found_edge = 0;

            // Update forward edges
            for (int i = out_adj_beg[u_local]; i < out_adj_beg[u_local + 1]; i++) {
              if (out_adj[i] == v) {
                local_res[i] -= bottleneck;
                found_edge = 1;
                break;
              }
            }

            // Update reverse edges if forward edge not found
            if (!found_edge) {
              for (int i = rev_adj_beg[u_local]; i < rev_adj_beg[u_local + 1]; i++) {
                if (rev_adj[i] == v) {
                  rev_res[i] -= bottleneck;
                  break;
                }
              }
            }
          }

          // Update residual capacities for edges owned by the target process
          if (rank == v_owner) {
            int v_local = local_of_global_index(v, N);
            int found_edge = 0;

            // Update reverse edges
            for (int i = rev_adj_beg[v_local]; i < rev_adj_beg[v_local + 1]; i++) {
              if (rev_adj[i] == u) {
                rev_res[i] += bottleneck;
                found_edge = 1;
                break;
              }
            }

            // Update forward edges if reverse edge not found
            if (!found_edge) {
              for (int i = out_adj_beg[v_local]; i < out_adj_beg[v_local + 1]; i++) {
                if (out_adj[i] == u) {
                  local_res[i] += bottleneck;
                  break;
                }
              }
            }
          }

          v = u; // Move to the previous vertex in the path
        }

        // Add the bottleneck capacity to the total flow for this phase
        phase_flow += bottleneck;
      }
    }

    total_flow += phase_flow;
    DEBUG_PRINT("[DEBUG] Rank %d: Phase pushed %d flow, total = %d\n", rank, phase_flow,
                total_flow);

    if (phase_flow == 0)
      break;
  }

  *flow_value = total_flow;

  DEBUG_PRINT("[DEBUG] Rank %d: Max flow = %d\n", rank, total_flow);

  free(local_res);
  free(rev_adj);
  free(rev_res);
  free(rev_adj_beg);
  free(level);
  free(parent);
  free(parent_cap);
  free_graph(&out_adj, &out_adj_beg, &in_adj, &in_adj_beg);
}
