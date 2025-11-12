/** Note: matrices are stored as arrays in column-major order
 *  (https://en.wikipedia.org/wiki/Row-_and_column-major_order).
 *
 *  Example:
 *
 *    Let A be the following matrix.
 *
 *    | 0 1 |
 *    | 2 3 |
 *    | 4 5 |
 *
 *    Then it is stored in the following array.
 *
 *    [0, 2, 4, 1, 3, 5]
 */

/** Multiply two matrices a (of size m x k) and b (of size k x n),
 *  and add the result to c (of size m x n).
 */
void multiplyMatrix(
		double *a,
		double *b,
		double *c,
		int m,
		int k,
		int n);

/** Create a matrix of size nrows x ncols.
 *  If init is set to "random", elements are initialized randomly.
 *  If it is "zero", elements are initialized to zero.
 */
void createMatrix(
		double **pmat,
		int nrows,
		int ncols,
		char *init);

/** Print a matrix of size nrows x ncols.
*/
void printMatrix(
		double *mat,
		int nrows,
		int ncols);

#include <math.h>

/* Parallel SUMMA matrix-matrix multiplication of two matrices
 * of size N x N.
 */
void summa(int n) {
  int proc, rank;

  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &proc);

  int p = n / proc;

  int row = rank / p;
  int col = rank % p;

  double* a;
  double* b;
  double* c;

  double* a_temp = malloc(sizeof(double) * p * p);
  double* b_temp = malloc(sizeof(double) * p * p);

  createMatrix(&a, p, p, "random");
  createMatrix(&b, p, p, "random");
  createMatrix(&c, p, p, "zero");

  MPI_Comm row_comm;
  MPI_Comm col_comm;

  MPI_Comm_split(MPI_COMM_WORLD, row, col, &col_comm);
  MPI_Comm_split(MPI_COMM_WORLD, col, row, &row_comm);

  for(int k = 0; k < p; k++) {
    if(k == row) {
      for(int i = 0; i < p * p; i++) {
        a_temp[i] = a[i];
      }
    }
    if(k == col) {
      for(int i = 0; i < p * p; i++) {
        b_temp[i] = b[i];
      }
    }

    MPI_Bcast(a_temp, p, MPI_DOUBLE, k, row_comm);
    MPI_Bcast(b_temp, p, MPI_DOUBLE, k, col_comm);

    multiplyMatrix(a_temp, b_temp, c, p, p, p);
  }

  free(a);
  free(b);
  free(c);
  free(a_temp);
  free(b_temp);
}

