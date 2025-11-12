#include <math.h>

/** Multiply two matrices a(of size mxk) and b(of size kxn), and add the result to c(of size mxn)
 */
void multiplyMatrix(
  double *a,
  double *b,
  double *c,
  int m,
  int k,
  int n);

/** Create a matrix of size nrowsxncols.
 *  If init is set to "random", elements are initialized randomly. If it is "zero", elements are initialized to zero.
 */
void createMatrix(
  double **pmat,
  int nrows,
  int ncols,
  char *init);


/* Parallel SUMMA matrix-matrix multiplication of two matrices of size NxN
 */
void summa(int N) {
  int rank, p;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &p);
  p = (int)sqrt(p);

  /* Create communicators */
  int row_color = rank / p;
  MPI_Comm row_comm;
  MPI_Comm_split(MPI_COMM_WORLD, row_color, rank, &row_comm);

  int col_color = rank % p + p;
  MPI_Comm col_comm;
  MPI_Comm_split(MPI_COMM_WORLD, col_color, rank, &col_comm);

  /* create matrices */
  double * Aloc, * Bloc, * Cloc;
  createMatrix(&Aloc, N / p, N / p, "random");
  createMatrix(&Bloc, N / p, N / p, "random");
  createMatrix(&Cloc, N / p, N / p, "zero");

  double * Atemp, * Btemp;
  createMatrix(&Atemp, N / p, N / p, "zero");
  createMatrix(&Btemp, N / p, N / p, "zero");

  int size = N * N / p / p;

  /* compute */
  for (int k = 0; k < p; ++k) {
    if (col_color == k + p)
      memcpy(Atemp, Aloc, size*sizeof(double)); // broadcast first column of A

    if (row_color == k)
      memcpy(Btemp, Bloc, size*sizeof(double)); // broadcast first line of B

    MPI_Bcast(Atemp, size, MPI_DOUBLE, k, row_comm);
    MPI_Bcast(Btemp, size, MPI_DOUBLE, k, col_comm);

    multiplyMatrix(Atemp, Btemp, Cloc, N / p, N / p, N / p);
  }

  /* cleanup */
  MPI_Comm_free(&row_comm);
  MPI_Comm_free(&col_comm);
  free(Aloc);
  free(Bloc);
  free(Cloc);
  free(Atemp);
  free(Btemp);
}

MPI_Comm col_comm, row_comm;

void shift(
  double *matrix,
  int size,
  int shiftSize,
  char shiftDirection) {
  MPI_Comm comm = shiftDirection == 'l' ? row_comm : col_comm;

  int rank, p;
  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &p);

  int receiving_from = (rank - shiftSize + p) % p;
  int sending_to = (rank + shiftSize) % p;

  MPI_Sendrecv_replace(
    matrix, size, MPI_DOUBLE,
    sending_to, 0,
    receiving_from, 0,
    comm, MPI_STATUS_IGNORE
  );
}

void cannon(int N) {
  int rank, p;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &p);
  p = (int)sqrt(p);

  /* Create communicators */
  int row_color = rank / p;
  MPI_Comm_split(MPI_COMM_WORLD, row_color, rank, &row_comm);

  int col_color = rank % p + p;
  MPI_Comm_split(MPI_COMM_WORLD, col_color, rank, &col_comm);

  /* create matrices */
  double * Aloc, * Bloc, * Cloc;
  createMatrix(&Aloc, N / p, N / p, "random");
  createMatrix(&Bloc, N / p, N / p, "random");
  createMatrix(&Cloc, N / p, N / p, "zero");

  int size = N * N / p / p;

  /* compute */
  shift(Aloc, size, rank / p, 'l');
  shift(Bloc, size, rank % p, 'u');

  for (int k = 0; k < p; k++) {
    multiplyMatrix(Aloc, Bloc, Cloc, N / p, N / p, N / p);

    shift(Aloc, size, 1, 'l');
    shift(Bloc, size, 1, 'u');
  }

  /* cleanup */
  // I ♡ MPI (that's a joke... obviously) 
  MPI_Comm_free(&row_comm);
  MPI_Comm_free(&col_comm);
  free(Aloc);
  free(Bloc);
  free(Cloc);
}
