#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <mpi.h>
#include <math.h>
#include <assert.h>
#include <limits.h>
#define MIN(X, Y) (((X) < (Y)) ? (X) : (Y))
#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))
#define BOOL char
#define TRUE 1
#define FALSE 0

int nb_local_vertices(int nb_vertices)
{
    /** Retrieve the procs ranks */
    int rank = 0, proc_number = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &proc_number);

    return (rank < nb_vertices % proc_number) ? ((nb_vertices / proc_number) + 1) : (nb_vertices / proc_number);
}

int proc_of_vertex(int global_index, int nb_vertices)
{
    /** Retrieve the procs ranks */
    int proc_number = 0;
    MPI_Comm_size(MPI_COMM_WORLD, &proc_number);

    int step = (int)nb_vertices / proc_number;
    int local_proc = 0;
    // checks whether the vertex is owned by a processor with only step
    // local vertices and not step + 1
    if (global_index - (step + 1) * (nb_vertices % proc_number) >= 0)
    {
        global_index -= (step + 1) * (nb_vertices % proc_number);
        local_proc += (int)nb_vertices % proc_number + global_index / step;
    }
    else
        local_proc += (int)global_index / (step + 1);

    return local_proc;
}

int local_of_global_index(int global_index, int nb_vertices)
{
    /** Retrieve the proc number */
    int proc_number = 0;
    MPI_Comm_size(MPI_COMM_WORLD, &proc_number);

    int step = nb_vertices / proc_number;
    return (global_index - (step + 1) * (nb_vertices % proc_number) < 0) ? (global_index % (step + 1)) : ((global_index - (step + 1) * (nb_vertices % proc_number)) % step);
}

int global_of_local_index(int local_index, int nb_vertices)
{
    /** Retrieve the procs ranks */
    int rank = 0, proc_number = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &proc_number);

    int step = nb_vertices / proc_number;
    return (rank < nb_vertices % proc_number) ? (local_index + (step + 1) * rank) : (local_index + (step + 1) * (nb_vertices % proc_number) + step * (rank - nb_vertices % proc_number));
}

void free_graph(int **local_out_adjacency,
                int **local_out_adjacency_beginning,
                int **local_in_adjacency,
                int **local_in_adjacency_beginning)
{
    free(*local_out_adjacency);
    free(*local_in_adjacency);
    free(*local_out_adjacency_beginning);
    free(*local_in_adjacency_beginning);
}

void print_graph(int nb_vertices,
                 int nb_edge,
                 int source_id,
                 int target_id,
                 const int *local_out_adjacency,
                 const int *local_out_weights,
                 const int *local_out_adjacency_beginning)
{
    /** Retrieve the procs ranks: important to know which vertices
        needs to be followed */
    int rank = 0, size = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    int local_nb_vertices = nb_local_vertices(nb_vertices);
    if (rank == 0)
    {
        printf("==== global ====\n");
        printf("|V| = %d, |E| =  %d, s = %d, t = %d\n",
               nb_vertices, nb_edge, source_id, target_id);
    }
    for (int rk = 0; rk < size; rk++)
    {
        if (rank == rk)
        {
            printf("=== local to rank %d ===\n", rk);
            for (int i = 0; i < local_nb_vertices; i++)
            {
                printf("vertex %d", global_of_local_index(i, nb_vertices));
                for (int j = local_out_adjacency_beginning[i]; j < local_out_adjacency_beginning[i + 1]; j++)
                {
                    printf(" (%d,%d)", local_out_adjacency[j], local_out_weights[j]);
                }
                printf("\n");
            }
        }
        MPI_Barrier(MPI_COMM_WORLD);
    }
    MPI_Barrier(MPI_COMM_WORLD);
}

void parse_graph(char *file_name,
                 int *nb_vertices,
                 int *nb_edge,
                 int *source_id,
                 int *target_id,
                 int **local_out_adjacency,
                 int **local_out_weights,
                 int **local_out_adjacency_beginning,
                 int **local_in_adjacency,
                 int **local_in_weights,
                 int **local_in_adjacency_beginning,
                 int *in_degree_sum,
                 int *out_degree_sum)
{
    /** Retrieve the procs ranks: important to know which vertices
        needs to be followed */
    int rank = 0, size = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    /** Open the file in read mode and check that it succeeds */
    FILE *file = fopen(file_name, "r");
    if (file == NULL && rank == 0)
    {
        printf("ERROR: Unable to open the file %s.\n", file_name);
        MPI_Abort(MPI_COMM_WORLD, 1);
    }

    /** Get the first graph information */
    if (!fscanf(file, "%d %d %d %d\n",
                nb_vertices, nb_edge, source_id, target_id) &&
        rank == 0)
    {
        printf("error while reading file at line 1!\n");
        MPI_Abort(MPI_COMM_WORLD, 1);
    }

    /** Each vertex of the proc must know its indegree and outdegree
        to initialize data structure: we parse the file a first
        time to compute the degrees */
    int local_nb_vertices = nb_local_vertices(*nb_vertices);
    int *in_degree = (int *)malloc(sizeof(int) * local_nb_vertices);
    int *out_degree = (int *)malloc(sizeof(int) * local_nb_vertices);
    for (int i = 0; i < local_nb_vertices; i++)
    {
        in_degree[i] = 0;
        out_degree[i] = 0;
    }
    for (int i = 0, current_line_size = 0; i < *nb_vertices; i++)
    {
        if (!fscanf(file, "%d", &current_line_size) && rank == 0)
        {
            printf("error while reading file at line %d!\n", i + 2);
            MPI_Abort(MPI_COMM_WORLD, 1);
        }
        for (int j = 0, edge_end_point, edge_weight; j < current_line_size; ++j)
        {
            if (!fscanf(file, " (%d,%d)", &edge_end_point, &edge_weight))
            {
                printf("error while reading file at line %d!\n", i + 2);
                MPI_Abort(MPI_COMM_WORLD, 1);
            }
            if (rank == proc_of_vertex(i, *nb_vertices))
            {
                out_degree[local_of_global_index(i, *nb_vertices)]++;
            }
            if (rank == proc_of_vertex(edge_end_point, *nb_vertices))
            {
                in_degree[local_of_global_index(edge_end_point, *nb_vertices)]++;
            }
        }
    }
    fclose(file);

    /** We can now set the beginning indices of the adjacency lists
        and allocate the adjacency lists*/
    *in_degree_sum = 0;
    *out_degree_sum = 0;
    *local_in_adjacency_beginning = (int *)malloc(sizeof(int) * (local_nb_vertices + 1));
    *local_out_adjacency_beginning = (int *)malloc(sizeof(int) * (local_nb_vertices + 1));
    for (int i = 0; i < local_nb_vertices; i++)
    {
        (*local_in_adjacency_beginning)[i] = *in_degree_sum;
        (*local_out_adjacency_beginning)[i] = *out_degree_sum;
        *in_degree_sum += in_degree[i];
        *out_degree_sum += out_degree[i];
    }
    (*local_in_adjacency_beginning)[local_nb_vertices] = *in_degree_sum;
    (*local_out_adjacency_beginning)[local_nb_vertices] = *out_degree_sum;
    *local_out_adjacency = (int *)malloc(sizeof(int) * (*out_degree_sum));
    *local_in_adjacency = (int *)malloc(sizeof(int) * (*in_degree_sum));
    *local_out_weights = (int *)malloc(sizeof(int) * (*out_degree_sum));
    *local_in_weights = (int *)malloc(sizeof(int) * (*in_degree_sum));

    /** We can now go through the file once more and add the correct
        values */
    int *current_in_index = (int *)malloc(sizeof(int) * local_nb_vertices + 1);
    for (int i = 0; i < local_nb_vertices + 1; i++)
    {
        current_in_index[i] = (*local_in_adjacency_beginning)[i];
    }
    file = fopen(file_name, "r");
    if (!fscanf(file, "%d %d %d %d\n",
                nb_vertices, nb_edge, source_id, target_id) &&
        rank == 0)
    {
        printf("error while reading file at line 1!\n");
        MPI_Abort(MPI_COMM_WORLD, 1);
    }
    for (int i = 0, current_line_size = 0; i < *nb_vertices; ++i)
    {
        if (!fscanf(file, "%d", &current_line_size) && rank == 0)
        {
            printf("error while reading file at line %d!\n", i + 2);
            MPI_Abort(MPI_COMM_WORLD, 1);
        }
        for (int j = 0, edge_end_point, edge_weight; j < current_line_size; ++j)
        {
            if (!fscanf(file, " (%d,%d)", &edge_end_point, &edge_weight) && rank == 0)
            {
                printf("error while reading file at line %d!\n", i + 2);
                MPI_Abort(MPI_COMM_WORLD, 1);
            }
            if (rank == proc_of_vertex(i, *nb_vertices))
            {
                (*local_out_adjacency)[(*local_out_adjacency_beginning)[local_of_global_index(i, *nb_vertices)] + j] = edge_end_point;
                (*local_out_weights)[(*local_out_adjacency_beginning)[local_of_global_index(i, *nb_vertices)] + j] = edge_weight;
            }
            if (rank == proc_of_vertex(edge_end_point, *nb_vertices))
            {
                int local_index_of_end_point = local_of_global_index(edge_end_point, *nb_vertices);
                (*local_in_adjacency)[current_in_index[local_index_of_end_point]] = i;
                (*local_in_weights)[current_in_index[local_index_of_end_point]] = edge_weight;
                current_in_index[local_index_of_end_point] += 1;
            }
        }
    }

    /** Free what is not need anymore */
    fclose(file);
    free(in_degree);
    free(out_degree);
    free(current_in_index);
}

#include "max_flow-solution.c"

const char *EDMONDS = "edmonds-karp";
const char *DINIC = "dinic";

/** Abort computation and give instructions on
    how to use this program */
void print_usage()
{
    int rank = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    if (rank == 0)
    {
        printf("Usage: mpirun -np [num-procs] ./max_flow [graph-file-name] --mode=[%s|%s]\n"
               "Arguments:\n"
               "\t[num-procs]: The number of MPI ranks to be used. For the sequential algorithm it has to be 1\n"
               "\t[graph-file-name]: Name of the graph file. The file extension must be .gr\n"
               "\t[mode]: must be either %s or %s. Indicates which maximum flow algorithm to use\n",
               EDMONDS, DINIC, EDMONDS, DINIC);
    }
}

/** Check the arguments number and format.
    Call print_usage() if there is an issue
    Retrieve the arguments otherwise */
void parse_arguments(int argc, char **argv, char **graph_file_name, char **mode, void (**max_flow)(char *, int *))
{
    int proc_rank = 0, size = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &proc_rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    if (argc < 3)
    {
        printf("Not enough arguments (3 needed, found %d)\n", argc);
        print_usage();
        return;
    }

    if ((0 == strncmp(".gr",
                      argv[1] + strlen(argv[1]) - 3,
                      MAX(strlen(argv[1] + strlen(argv[1]) - 3), 3))) &&
        (0 == strncmp("--mode=",
                      argv[2],
                      7)))
    {
        *graph_file_name = argv[1];
        *mode = argv[2] + 7;
    }
    else if ((0 == strncmp(".gr",
                           argv[2] + strlen(argv[2]) - 3,
                           MAX(strlen(argv[2] + strlen(argv[2]) - 3), 3))) &&
             (0 == strncmp("--mode=",
                           argv[1],
                           7)))
    {
        *graph_file_name = argv[2];
        *mode = argv[1] + 7;
    }
    else
    {
        printf("Unknown mode\n");
        print_usage();
        return;
    }

    if (strlen(*graph_file_name) == 3)
    {
        printf("graph_file_name length erroneous\n");
        print_usage();
        return;
    }

    if (size == 1)
    {
        if (0 == strncmp(*mode, EDMONDS, MAX(12, strlen(*mode))))
        {
            *max_flow = max_flow_edmonds_karp_seq;
        }
        else if (0 == strncmp(*mode, DINIC, MAX(6, strlen(*mode))))
        {
            *max_flow = max_flow_dinic_seq;
        }
        else
        {
            printf("no sequential algorithm for mode %s\n", *mode);
            print_usage();
        }
    }
    else
    {
        if (0 == strncmp(*mode, EDMONDS, MAX(12, strlen(*mode))))
        {
            *max_flow = max_flow_edmonds_karp_par;
        }
        else if (0 == strncmp(*mode, DINIC, MAX(6, strlen(*mode))))
        {
            *max_flow = max_flow_dinic_par;
        }
        else
        {
            printf("no parallel algorithm for mode %s\n", *mode);
            print_usage();
        }
    }
}

int main(int argc, char **argv)
{
    /** Initialize MPI */
    MPI_Init(&argc, &argv);

    int proc_rank = 0, size = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &proc_rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    /** Parse the arguments */
    char *graph_file_name = NULL;
    char *mode = NULL;
    void (*max_flow)(char *, int *) = NULL;
    parse_arguments(argc, argv, &graph_file_name, &mode, &max_flow);
    if (mode == NULL)
        goto end;
    if (graph_file_name == NULL)
        goto end;

    /** Call the right algorithm */
    MPI_Barrier(MPI_COMM_WORLD);
    double start_time = MPI_Wtime();
    int max_flow_value = 0;
    max_flow(graph_file_name, &max_flow_value);

    /** Print computation time information */
    if (proc_rank == 0)
    {
        if (size == 1)
        {
            printf("Sequential maximum flow computation on graph from %s with algorithm %s took %e seconds with result %d.\n",
                   graph_file_name,
                   mode,
                   MPI_Wtime() - start_time,
                   max_flow_value);
        }
        else
        {
            printf("Parallel maximum flow computation on graph from %s with algorithm %s took %e seconds with result %d.\n",
                   graph_file_name,
                   mode,
                   MPI_Wtime() - start_time,
                   max_flow_value);
        }
    }

    /** End the program */
end:
    MPI_Finalize();

    return 0;
}
