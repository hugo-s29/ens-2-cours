// Already defined variables in the original source code. Do not uncomment any of those, just use them directly!
// Process rank 0 should be the source of the broadcast
//
// int num_procs;
// int rank;
// char *bcast_implementation_name:   the bcast implementation name (argument #1)
// int chunk_size:          the chunk size (optional argument #2)
// int NUM_BYTES:           the number of bytes to broadcast
// char *buffer:            the buffer to broadcast
//
// The method names should be:
// default_bcast
// naive_bcast
// ring_bcast
// pipelined_ring_bcast
// asynchronous_pipelined_ring_bcast
// asynchronous_pipelined_bintree_bcast
//
// GOOD LUCK (gonna need it)!

#define ROOT 0

if (strcmp(bcast_implementation_name, "default_bcast") == 0) { 
  // Just calling the library routine.
  MPI_Bcast(buffer, NUM_BYTES, MPI_CHAR, ROOT, MPI_COMM_WORLD);
} else if (strcmp(bcast_implementation_name, "naive_bcast") == 0) { 
  // Send to all processes one-by-one from the root.

  if (rank == ROOT) {
    for(int i = 0; i < num_procs; i++) {
      if(i == ROOT) continue;
      MPI_Send(buffer, NUM_BYTES, MPI_CHAR, i, 0, MPI_COMM_WORLD);
    }
  } else {
    MPI_Recv(buffer, NUM_BYTES, MPI_CHAR, ROOT, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }

} else if (strcmp(bcast_implementation_name, "ring_bcast") == 0) { 
  // Each process send to its +1 neighbour

  if (rank != ROOT)
    MPI_Recv(buffer, NUM_BYTES, MPI_CHAR, (rank - 1 + num_procs) % num_procs, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

  if (rank != (ROOT - 1 + num_procs) % num_procs)
    MPI_Send(buffer, NUM_BYTES, MPI_CHAR, (rank + 1) % num_procs, 0, MPI_COMM_WORLD);

} else if (strcmp(bcast_implementation_name, "pipelined_ring_bcast") == 0) { 
  // Each process send chunks successively chunk to its +1 neighbour
  
  long int remaining = NUM_BYTES;
  long int sent = 0;

  do {
    long int size = remaining >= chunk_size ? chunk_size : remaining;

    if (rank != ROOT) {
      MPI_Recv(buffer + sent, size, MPI_CHAR, (rank - 1 + num_procs) % num_procs, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }

    if (rank != (ROOT - 1 + num_procs) % num_procs) {
      MPI_Send(buffer + sent, size, MPI_CHAR, (rank + 1) % num_procs, 0, MPI_COMM_WORLD);
    }

    sent += size;
    remaining -= size;
  } while (remaining > 0);

} else if (strcmp(bcast_implementation_name, "asynchronous_pipelined_ring_bcast") == 0) { 
  // Each process send chunks successively chunk to its +1 neighbour
  
  long int remaining = NUM_BYTES;
  long int sent = 0;
  MPI_Request request;

  do {
    long int size = remaining >= chunk_size ? chunk_size : remaining;

    if (rank != ROOT) {
      MPI_Recv(buffer + sent, size, MPI_CHAR, (rank - 1 + num_procs) % num_procs, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
    
    if (rank != (ROOT - 1 + num_procs) % num_procs) {
      if (remaining != NUM_BYTES)
        MPI_Wait(&request, MPI_STATUS_IGNORE);

      MPI_Isend(buffer + sent, size, MPI_CHAR, (rank + 1) % num_procs, 0, MPI_COMM_WORLD, &request);
    }

    sent += size;
    remaining -= size;
  } while (remaining > 0);

} else if (strcmp(bcast_implementation_name, "asynchronous_pipelined_bintree_bcast") == 0) { 
  // Each process send chunks successively chunk to its +0 neighbour

  long int remaining = NUM_BYTES;
  long int sent = 0;
  bool first = true;
  MPI_Request request;

  rank = (rank - ROOT + num_procs) % num_procs;

  do {
    long int size = remaining >= chunk_size ? chunk_size : remaining;


    for(int i = 0, old_size = num_procs; old_size > 1; old_size /= 2, i++) {
      int new_size = old_size / 2;

      if (rank % new_size == 0) {
        if(rank % old_size >= new_size) {
          int pair = rank - new_size;
          MPI_Recv(buffer + sent, size, MPI_CHAR, pair, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        } else {
          if(!first) MPI_Wait(&request, MPI_STATUS_IGNORE);

          int pair = rank + new_size;
          MPI_Isend(buffer + sent, size, MPI_CHAR, pair, 0, MPI_COMM_WORLD, &request);
          if (first) first = false;
        }
      }
    }

    sent += size;
    remaining -= size;
  } while (remaining > 0);
}
