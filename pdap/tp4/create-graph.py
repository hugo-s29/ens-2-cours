#!/usr/bin/env python3
import sys
import networkx as nx

def generate_graph(n: int, m: int, file: str):
    if m < n - 1:
        raise ValueError("Number of edges must be at least n - 1 to ensure connectivity.")
    if m > n * (n - 1) // 2:
        raise ValueError("Too many edges for an undirected simple graph.")

    while True:
        G = nx.gnm_random_graph(n, m)
        if nx.is_connected(G):
            break

    # Write in DOT format
    nx.drawing.nx_pydot.write_dot(G, f"{file}.dot")
    print(f"A connected graph with {n} vertices and {m} edges was written to {file}.dot")

    # Write in simple edge-list format
    with open(f"{file}.graph", "w") as f:
        f.write(f"{n} {m}\n")
        for u, v in G.edges():
            f.write(f"{u} {v}\n")
    print(f"A connected graph with {n} vertices and {m} edges was written to {file}.graph")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print(f"Usage: {sys.argv[0]} <vertex_nb> <edge_nb> <output_name>")
        sys.exit(1)

    n = int(sys.argv[1])
    m = int(sys.argv[2])
    filename = sys.argv[3]

    generate_graph(n, m, filename)
