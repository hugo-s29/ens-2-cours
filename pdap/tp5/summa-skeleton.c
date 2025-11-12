#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <mpi.h>

#include "summa-solution.c"

/** Create a matrix of size nrows x ncols.
 *  If init is set to "random", elements are initialized randomly.
 *  If it is "zero", elements are initialized to zero.
 */
void createMatrix(
    double **pmat,
    int nrows,
    int ncols,
    char *init) {
    double *mat;
    int procRank;
    MPI_Comm_rank(MPI_COMM_WORLD, &procRank);
    *pmat = mat = (double*)malloc(nrows * ncols * sizeof(double));
    if (strcmp(init, "random") == 0) { // Initialize the matrix elements randomly
        for (int i = 0; i < nrows * ncols; i++)
            mat[i] = rand() / (double)RAND_MAX;
    } else if (strcmp(init, "ones") == 0) { // Setup the elements to one
        for (int i = 0; i < nrows * ncols; i++)
            mat[i] = 1;
    } else { // Set all matrix elements to zero
        memset(mat, 0, nrows * ncols * sizeof(double));
    }
}

/** Multiply two matrices a (of size m x k) and b (of size k x n),
 *  and add the result to c (of size m x n).
 */
void multiplyMatrix(
    double *a,
    double *b,
    double *c,
    int m,
    int k,
    int n) {
    int im, ik, in;
    for (im = 0; im < m; im++) {
        for (in = 0; in < n; in++) {
            for (ik = 0; ik < k; ik++) {
                c[im + in * m] += a[im + ik * m] * b[ik + in * k];
            }
        }
    }
}

void printMatrix(
	double *mat,
	int nrows,
	int ncols) {
	for (int i = 0; i < nrows; i++) {
		for (int j = 0; j < ncols; j++) {
			if (j == 0)
				printf("| ");
			printf("%f ", mat[j * ncols + i]);
			if (j == ncols - 1)
				printf("|");
		}
		printf("\n");
	}
}

void printUsage() {
    printf("Usage: mpirun -np [num-procs] ./summa N\n");
}

int main(int argc, char **argv) {
    MPI_Init(&argc, &argv);

    int procRank; MPI_Comm_rank(MPI_COMM_WORLD, &procRank);
    if (argc < 2 && procRank == 0) {
        printUsage();
        MPI_Abort(MPI_COMM_WORLD, 1);
    }

    MPI_Barrier(MPI_COMM_WORLD);
    int N = atoi(argv[1]);

    double start_time;
    if (procRank == 0)
        start_time = MPI_Wtime();

    MPI_Barrier(MPI_COMM_WORLD);

    srand(procRank + 1);
    summa(N);

    MPI_Barrier(MPI_COMM_WORLD);

    if (procRank == 0)
        printf("Time: %f\n", MPI_Wtime() - start_time);

    MPI_Finalize();
    return 0;
}

