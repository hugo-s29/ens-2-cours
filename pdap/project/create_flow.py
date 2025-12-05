#!/usr/bin/env python3

import sys
import random
import networkx as nx

if len(sys.argv) not in (5, 6):
  print(
      "Usage: python3 create-flow.py [num-vertices] [num-edges] [max_weight] [file-name] [seed (optional)]",
      file=sys.stderr,
  )
  exit(1)

n = int(sys.argv[1])
m = int(sys.argv[2])
w = int(sys.argv[3])
fileName = sys.argv[4]
seed = int(sys.argv[5]) if len(sys.argv) == 6 else random.randint(0, 1000000)

random.seed(seed)

if m > n * (n - 1):
  print("Invalid number of edges: too many edges", file=sys.stderr)
  exit(1)

if m < n - 1:
  print("Invalid number of edges : not enough edges", file=sys.stderr)
  exit(1)

# Pick random source and sink
s, t = random.sample(range(n), 2)

# Generate a random directed graph with networkx
G = nx.gnm_random_graph(n, m, directed=True, seed=seed)
while not nx.is_weakly_connected(G) or not nx.has_path(G, s, t):
  seed += 1
  G = nx.gnm_random_graph(n, m, directed=True, seed=seed)

# Assign random capacities
for u, v in G.edges():
  G[u][v]["capacity"] = random.randint(1, w)

# Write to file in the required format
with open(fileName, "w") as f:
  print(f"{n} {m} {s} {t}", file=f)
  for i in range(n):
    out_edges = [(v, G[i][v]["capacity"]) for v in G.successors(i)]
    print(
        f"{len(out_edges)} " + " ".join(f"({v},{cap})" for v, cap in out_edges),
        file=f,
    )

# Compute and print the max flow value for reference
flow_value, _ = nx.maximum_flow(G, s, t, capacity="capacity")
print(
    f"A graph with {n} vertices and {m} edges is written into the file {fileName}"
)
print(f"Source: {s}, Sink: {t}, Max flow (networkx): {flow_value}")
