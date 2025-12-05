#!/usr/bin/env python3

import subprocess
import sys
import os
import re
import random
import json
import time
import csv
from concurrent.futures import ThreadPoolExecutor

# ANSI color codes
GREEN = "\033[92m"
YELLOW = "\033[93m"
CYAN = "\033[96m"
RESET = "\033[0m"

NUM_BENCHS = 150


def run_create_flow(n, m, w, filename, seed):
  cmd = [
      sys.executable,
      "create_flow.py",
      str(n),
      str(m),
      str(w),
      filename,
      str(seed),
  ]

  result = subprocess.run(cmd, capture_output=True, text=True)
  if result.returncode != 0:
    print(
        YELLOW + f"Error running create-flow.py ({n=},{m=},{w=},{seed=}):" +
        RESET,
        result.stderr,
    )
    sys.exit(1)
  # Extract max flow value from output
  match = re.search(r"Max flow \(networkx\): (\d+)", result.stdout)
  if not match:
    print(YELLOW + "Could not parse max flow from create-flow.py output" +
          RESET)
    sys.exit(1)
  return int(match.group(1)), result.stdout


def run_c_implementation(graph_file, algorithm="edmonds-karp", num_procs=1):
  hostfile = f'hostfiles/complete-{num_procs}.txt'
  platform = f'platforms/complete-{num_procs}.xml'

  if not os.path.exists(hostfile) or not os.path.exists(platform):
    cmd = [
        sys.executable, "smpi-generate-complete.py",
        str(num_procs), "1000", "100", "10Gbps", "10us"
    ]
    subprocess.run(cmd, capture_output=True)

  cmd = [
      "smpirun", "-hostfile", hostfile, '-platform', platform, "./main",
      graph_file, "--mode=" + algorithm
  ]

  result = subprocess.run(
      cmd,
      capture_output=True,
      text=True,
  )

  # Extract flow value and  from output
  match = re.search(r"took\s*([\d.eE+-]+)\s*seconds with result\s*(\d+)",
                    result.stdout)
  elapsed = float(match.group(1)) if match else -1.0
  flow = int(match.group(2)) if match else -1
  return flow, elapsed, result.stdout


def print_bench_result(idx, n, m, w, seed, procs, flow, elapsed, valid):
  valid = f"{GREEN}PASS{RESET}" if valid else "{RED}FAIL{RESET}"
  print(
      f"\t{CYAN}{idx:3d}{RESET}\t | n={n:5d} m={m:5d} w={w:5d} seed={seed:8d} procs={procs:3d}\t | flow={flow:5d}\t | time={elapsed:8.4f}s {valid}"
  )


def initialize_bench(dense):
  bench = []

  def generate_bench(idx):
    while True:
      graph_file = f"benchs/graph-{str(idx).zfill(3)}.gr"

      procs = random.randint(10, 150)
      if dense:
        n = int(random.expovariate(1 / 1000)) + 1000
      else:
        n = int(random.expovariate(1 / 10000)) + 10

      # ensure n is divisible by procs
      n += (procs - n % procs)
      if dense:
        m = random.randint(n * (n - 1) // 3, n * (n - 1) // 2)
      else:
        m = random.randint(n - 1, min(n * (n - 1) // 2, 50 * n))
      w = random.randint(1, 100)

      seed = idx * 10000 + 42

      print(f"Adding bench #{idx} ({n=}, {m=}, {w=}, {procs=})")
      expected_flow, _ = run_create_flow(n, m, w, graph_file, seed)

      return {
          "graph_file": graph_file,
          "expected_flow": expected_flow,
          "params": [n, m, w, seed, procs],
      }

  with ThreadPoolExecutor(max_workers=7) as executor:
    bench = list(executor.map(generate_bench, range(1, NUM_BENCHS + 1)))

  with open("benchs/benchs.json", "w") as f:
    json.dump(bench, f)


def load_bench(dense):
  if not os.path.exists("benchs/benchs.json"):
    initialize_bench(dense)

  with open("benchs/benchs.json") as f:
    return list(json.load(f))


def run_bench(bench, algorithm, mode, csv_writer=None):
  print(
      f"{YELLOW}Benchmarking {NUM_BENCHS} flow networks for {algorithm} in mode {mode}...{RESET}"
  )
  print(f"\t{'Idx':>3}\t | {'Params':<49}\t | {'Flow':<10}\t | {'Time':<12}")
  print("\t" + "-" * 90)

  timings = []
  for idx, bench_item in enumerate(bench):
    graph_file = bench_item["graph_file"]
    expected_flow = bench_item["expected_flow"]
    num_procs = bench_item["params"][-1] if mode == "par" else 1
    n, m, w, seed = bench_item["params"][:-1]

    flow, elapsed, _ = run_c_implementation(graph_file, algorithm, num_procs)
    timings.append(elapsed)
    valid = flow == expected_flow
    print_bench_result(idx + 1, n, m, w, seed, num_procs, flow, elapsed, valid)

    if csv_writer:
      csv_writer.writerow({
          "idx": idx + 1,
          "n": n,
          "m": m,
          "w": w,
          "seed": seed,
          "procs": num_procs,
          "algorithm": algorithm,
          "mode": mode,
          "flow": flow,
          "expected_flow": expected_flow,
          "time": elapsed,
          "valid": int(valid)
      })

  print("\t" + "-" * 90)
  print(f"{CYAN}Average time: {sum(timings)/len(timings):.4f}s{RESET}")
  print(f"{CYAN}Min time: {min(timings):.4f}s{RESET}")
  print(f"{CYAN}Max time: {max(timings):.4f}s{RESET}")


if __name__ == "__main__":
  print('Choose the algorithm:')
  print('0. Parallel Dinic')
  print('1. Sequential Dinic')
  print('2. Parallel Edmonds-Karp')
  print('3. Sequential Edmonds-Karp')
  i = int(input())

  print('Sparse? (0 -> dense graph generator, 1 -> sparse graph generator)')
  print(
      'Must be chosen correctly when generating the tests, otherwise, run `make clean-benchs`'
  )
  sparse = int(input())

  bench = load_bench(dense=sparse == 0)

  with open(f"bench_results{i+4*sparse}.csv", "w", newline="") as csvfile:
    fieldnames = [
        "idx", "n", "m", "w", "seed", "procs", "algorithm", "mode", "flow",
        "expected_flow", "time", "valid"
    ]
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()

    if i == 0:
      run_bench(bench, algorithm="dinic", mode='par', csv_writer=writer)
    elif i == 1:
      run_bench(bench, algorithm="dinic", mode='seq', csv_writer=writer)
    elif i == 2:
      run_bench(bench, algorithm="edmonds-karp", mode='par', csv_writer=writer)
    elif i == 3:
      run_bench(bench, algorithm='edmonds-karp', mode='seq', csv_writer=writer)
