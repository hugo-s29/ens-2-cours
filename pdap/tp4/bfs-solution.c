void bfs(int n, int *adjBeg, int *adj, int *depth, int root) {
    int procRank; MPI_Comm_rank(MPI_COMM_WORLD, &procRank);
    int numProcs; MPI_Comm_size(MPI_COMM_WORLD, &numProcs);

    int todo = 1;

    while(todo) {
      todo = 0;

      for(int i = procRank; i < n; i += numProcs) {
        for(int k = adjBeg[i]; k < adjBeg[i+1]; k++) {
          int j = adj[k];

          if(depth[j] != n+1 && (depth[i] == n+1 || depth[j] + 1 < depth[i])) {
            depth[i] = depth[j] + 1;
            todo = 1;
          }
        }
      }

      MPI_Allreduce(MPI_IN_PLACE, &todo, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);
      MPI_Allreduce(MPI_IN_PLACE, depth, n, MPI_INT, MPI_MIN, MPI_COMM_WORLD);
    }
}

