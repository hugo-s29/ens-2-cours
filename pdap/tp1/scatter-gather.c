#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mpi.h>


int MPI_ScatterSingleInt(const int *sendbuf, int *recvbuf, int root, MPI_Comm comm) {
    int rank, numProcs;
    MPI_Comm_rank(comm, &rank);
    MPI_Comm_size(comm, &numProcs);

    if (rank == root) {
      for(int other = 0; other < numProcs; other++) {
        if (other == rank) *recvbuf = sendbuf[root];
        else MPI_Send(sendbuf + other, 1, MPI_INT, other, 0, comm);
      }
    } else {
      MPI_Recv(recvbuf, 1, MPI_INT, root, 0, comm, MPI_STATUS_IGNORE);
    }
  
    return MPI_SUCCESS;
}


int MPI_GatherSingleInt(const int *sendbuf, int *recvbuf, int root, MPI_Comm comm) {
    int rank, numProcs;
    MPI_Comm_rank(comm, &rank);
    MPI_Comm_size(comm, &numProcs);
  
    if (rank == root) {
      for(int other = 0; other < numProcs; other++) {
        if (other == rank) *recvbuf = sendbuf[root];
        else MPI_Recv(recvbuf + other, 1, MPI_INT, other, 0, comm, MPI_STATUS_IGNORE);
      }
      
    } else {
      MPI_Send(sendbuf, 1, MPI_INT, root, 0, comm);
    }

    return MPI_SUCCESS;
}


int main(int argc, char **argv) {
    MPI_Init(&argc, &argv);

    int rank, numProcs;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &numProcs);

    if (numProcs != 8) {
        if (rank == 0) {
            printf("You should execute this with 8 processes !\n");
        }
        MPI_Finalize();
        exit(0);
    }

    int tab[8] = {-1, -1, -1, -1, -1, -1, -1, -1};
    int root = 3;
    int result = -1;

    if (rank == root) {
        // Initialize the value of tab for the root process
        memcpy(tab, (int[]) {3, 1, 4, 1, 5, 9, 2, 6}, sizeof(tab));
    }

    // Test scattering the data to all processes
    MPI_ScatterSingleInt(tab, &result, root, MPI_COMM_WORLD);

    printf("My rank is %d and my attributed value is %d \n", rank, result);

    MPI_Barrier(MPI_COMM_WORLD);

    // Gathering the data back to the first process
    MPI_GatherSingleInt(&result, tab, 0, MPI_COMM_WORLD);

    if (rank == 0) {
        printf("tab = {");
        for (int i = 0; i < 8; i++) {
            printf("%d, ", tab[i]);
        }
        printf("};\n");
    }

    MPI_Finalize();
    return 0;
}
