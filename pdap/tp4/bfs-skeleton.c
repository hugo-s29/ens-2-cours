#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <time.h>
#include <mpi.h>
#include <assert.h>

#include "bfs-solution.c"

void readGraph(
    char *fileName,
    int *pnVtx,
    int *pnEdge,
    int **padjBeg,
    int **padj)
{
    FILE *file = fopen(fileName, "r");
    if (file == NULL)
    {
        int rank;
        MPI_Comm_rank(MPI_COMM_WORLD, &rank);
        if (rank == 0)
        {
            printf("ERROR: Unable to open the file %s.\n", fileName);
            MPI_Abort(MPI_COMM_WORLD, 1);
        }
    }

    int nVtx, nEdge;
    int *adjBeg, *adj;
    fscanf(file, " %d %d", pnVtx, pnEdge);
    nVtx = *pnVtx;
    nEdge = *pnEdge;
    int *edgeLeft, *edgeRight;
    edgeLeft = (int *)malloc(nEdge * sizeof(int));
    edgeRight = (int *)malloc(nEdge * sizeof(int));
    *padjBeg = adjBeg = (int *)malloc((nVtx + 1) * sizeof(int));
    memset(adjBeg, 0, (nVtx + 1) * sizeof(int));
    *padj = adj = (int *)malloc(2 * nEdge * sizeof(int));

    int i;
    for (i = 0; i < nEdge; i++)
    {
        fscanf(file, " %d %d", edgeLeft + i, edgeRight + i);
        adjBeg[edgeLeft[i]]++;
        adjBeg[edgeRight[i]]++;
    }
    for (i = 1; i <= nVtx; i++)
    {
        adjBeg[i] += adjBeg[i - 1];
    }
    for (i = 0; i < nEdge; i++)
    {
        adj[--adjBeg[edgeRight[i]]] = edgeLeft[i];
        adj[--adjBeg[edgeLeft[i]]] = edgeRight[i];
    }

    free(edgeLeft);
    free(edgeRight);
    fclose(file);
}

void printUsage()
{
    int rank;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    if (rank == 0)
    {
        printf("Usage: mpirun -np [num-procs] ./bfs [graph-file-name] [bfs-root-node]\n");
    }
}

void bfsSol(int n, int *adjBeg, int *adj, int *depth, int root)
{
    int new = 1;
    while (new > 0)
    {
        new = 0;
        for (int i = 0; i < n; i++)
        {
            for (int j = adjBeg[i]; j < adjBeg[i + 1]; j++)
            {
                if (depth[adj[j]] != -1 && (depth[i] == -1 || depth[adj[j]] + 1 < depth[i]))
                { // Visit the neighbor, update the depth
                    depth[i] = depth[adj[j]] + 1;
                    new = 1;
                }
            }
        }
    }
}

int arrayEq(int N, int *arr1, int *arr2)
{
    for (int i = 0; i < N; i++)
    {
        if (arr1[i] != arr2[i])
        {
            return 0;
        }
    }

    return 1;
}

int main(int argc, char **argv)
{
    MPI_Init(&argc, &argv);

    if (argc != 3)
    {
        printUsage();
        MPI_Abort(MPI_COMM_WORLD, 1);
    }

    int root = atoi(argv[2]);
    int procRank;
    MPI_Comm_rank(MPI_COMM_WORLD, &procRank);
    int nVtx, nEdge;
    int *adjBeg, *adj;
    int *depth, *depthSol;

    readGraph(argv[1], &nVtx, &nEdge, &adjBeg, &adj);

    depth = (int *)malloc(nVtx * sizeof(int));
    for(int i = 0; i < nVtx; i++)
      depth[i] = nVtx + 1;
    depth[root] = 0;

    // Start the timer
    double start_time;
    MPI_Barrier(MPI_COMM_WORLD);
    if (procRank == 0)
        start_time = MPI_Wtime();

    bfs(nVtx, adjBeg, adj, depth, root);

    MPI_Barrier(MPI_COMM_WORLD);
    if (procRank == 0)
        fprintf(stdout, "time: %.3lf seconds\n", MPI_Wtime() - start_time);

    if (procRank == 0)
    {
        depthSol = (int *)malloc(nVtx * sizeof(int));
        memset(depthSol, -1, nVtx * sizeof(int));
        depthSol[root] = 0;

        bfsSol(nVtx, adjBeg, adj, depthSol, root);

        if (arrayEq(nVtx, depth, depthSol))
        {
            printf("SUCCESS: BFS result is correct!\n");
        }
        else
        {
          for (int i = 0; i < nVtx; ++i) {
            if (depth[i] != depthSol[i])
              printf("Node %d: %d expected %d\n", i, depth[i], depthSol[i]);
          }
          printf("ERROR: BFS result is incorrect!\n");

        }
    }

    MPI_Finalize();
    return 0;
}
