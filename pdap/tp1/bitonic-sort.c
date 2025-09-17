#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mpi.h>

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))	

int compareInt(const void *p1, const void *p2) {
	return *((int *)p1) - *((int *)p2);
}

void readArray(int *arr, int N, char *fileName) {
	FILE *file = fopen(fileName, "r");

	if (!file) {
		printf("ERROR: Unable to open the file %s.\n", fileName);
		MPI_Abort(MPI_COMM_WORLD, 1);
	}

	for (int i = 0; i < N; i++) {
		fscanf(file, " %d", arr + i);
	}

	fclose(file);
}

void printArray(int *arr, int N) {
	for (int i = 0; i < N; i++) {
		printf("%d ", arr[i]);
	}
	printf("\n");
}

int checkSorted( int *arr, int N) {
	for (int i = 0; i < N - 1; i++) {
		if (arr[i] > arr[i + 1]) {
			return 0;
		}
	}
	return 1;
}

void printUsage() {
	printf("Usage: mpirun -np [num-procs/elements] ./bitonic-sort [bitonic-array-file] [sequential|parallel]\n");
}


void bitonicSortMPI(int *arr, int N, int procRank, int numProcs) {
  int val;
  MPI_Scatter(arr, 1, MPI_INT, &val, 1, MPI_INT, 0, MPI_COMM_WORLD);

  for (int n = N; n > 1; n /= 2) {
    int pair = (procRank + n / 2) % n;
    pair += (procRank / n) * n;
    int val2;

    if(procRank < pair) {
      MPI_Recv(&val2, 1, MPI_INT, pair, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      int min = MIN(val, val2);
      val2 = MAX(val, val2);
      val = min;

      MPI_Send(&val2, 1, MPI_INT, pair, 0, MPI_COMM_WORLD);
    } else {
      MPI_Send(&val, 1, MPI_INT, pair, 0, MPI_COMM_WORLD);
      MPI_Recv(&val, 1, MPI_INT, pair, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
  }

  MPI_Gather(&val, 1, MPI_INT, arr, 1, MPI_INT, 0, MPI_COMM_WORLD);

  ///////////////////////////////////////////////////////////////////////////
  /////////////////////  IMPLEMENT BITONIC SORT HERE   ////////////////////
  ///////////////////////////////////////////////////////////////////////////
}

void sequentialSort(int *arr, int N) {
  qsort(arr, N, sizeof(arr[0]), compareInt);
}

int main(int argc, char **argv) {
  int *arr = NULL;
  int N;       
  int procRank;  
  int numProcs;  

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &procRank);
  MPI_Comm_size(MPI_COMM_WORLD, &numProcs);

  N = numProcs;

  if (argc < 3 && procRank == 0) {
    printUsage();
    MPI_Abort(MPI_COMM_WORLD, 1);
  }
  MPI_Barrier(MPI_COMM_WORLD);

  arr = (int *)malloc(numProcs * sizeof(arr[0]));
  if (procRank == 0) {
    readArray(arr, N, argv[1]);
    printf("-> The array before sort:\n");
    printArray(arr, N);
  }

  double startTime, endTime, elapsed;

  if (strcmp(argv[2], "sequential") == 0) {
    if (procRank == 0) {
      startTime = MPI_Wtime();
      sequentialSort(arr, N);
      endTime = MPI_Wtime();
      elapsed = endTime - startTime;
    }
  } else if (strcmp(argv[2], "parallel") == 0) {
    MPI_Barrier(MPI_COMM_WORLD);
    startTime = MPI_Wtime();
    bitonicSortMPI(arr, N, procRank, numProcs);
    MPI_Barrier(MPI_COMM_WORLD);
    endTime = MPI_Wtime();
    elapsed = endTime - startTime;
  } else {
    if (procRank == 0) {
      printf("ERROR: Unknown array sort type %s.\n", argv[2]);
      MPI_Abort(MPI_COMM_WORLD, 1);
    }
  }

  MPI_Barrier(MPI_COMM_WORLD);

  if (procRank == 0) {
    printf("-> The array after sort:\n");
    printArray(arr, N);
    if (checkSorted(arr, N)) {
      printf("-> The array is sorted correctly!\n");
    } else {
      printf("-> The array does not seem to be sorted!\n");
    }
    printf("-> Elapsed time: %f seconds\n", elapsed);
  }

  MPI_Finalize();
  return 0;
}
