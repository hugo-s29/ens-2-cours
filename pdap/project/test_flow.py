#!/usr/bin/env python3

import subprocess
import sys
import os
import re
import random
import json
from concurrent.futures import ThreadPoolExecutor

# ANSI color codes
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
CYAN = "\033[96m"
RESET = "\033[0m"

NUM_TESTS = 1000

failed_tests = []


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

  result = subprocess.run(cmd, capture_output=True, text=True, timeout=3)
  if result.returncode != 0:
    print(
        RED + f"Error running create-flow.py ({n=},{m=},{w=},{seed=}):" + RESET,
        result.stderr,
    )
    sys.exit(1)
  # Extract max flow value from output
  match = re.search(r"Max flow \(networkx\): (\d+)", result.stdout)
  if not match:
    print(RED + "Could not parse max flow from create-flow.py output" + RESET)
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

  result = None

  try:
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=10  # Timeout after 10 seconds
    )

  except subprocess.TimeoutExpired:
    print(RED + "C implementation timed out." + RESET)
    print(' '.join(cmd))
    return -1, result.stdout if result is not None else ""

  if result.returncode != 0:
    print(
        RED + "Error running C implementation (" + " ".join(cmd) + "):" + RESET,
        result.stderr,
        result.stdout,
    )
    return -1, result.stdout

  # Extract flow value from output
  match = re.search(r"with result\s*(\d+)\.", result.stdout)

  if not match:
    print(result.stdout)
    print(RED + "Could not parse flow from C implementation output" + RESET)
    sys.exit(1)
  return int(match.group(1)), result.stdout


def print_result(idx, n, m, w, seed, procs, expected, computed, passed):
  status = GREEN + "PASS" + RESET if passed else RED + "FAIL" + RESET
  print(
      f"\t{CYAN}{idx:3d}{RESET}\t | n={n:5d} m={m:5d} w={w:5d} seed={seed:8d} procs={procs:3d}\t | expected={expected:5d} computed={computed:5d}\t | {status}"
  )


def initialize_tests():
  tests = []

  def generate_test(idx):
    while True:
      graph_file = f"tests/graph-{str(idx).zfill(3)}.gr"

      # Randomize number of procs between 2 and 10
      procs = random.randint(2, 5)

      # Randomize number of nodes between 5 and 10
      n = random.randint(1, 10)
      n += (procs - n % procs)
      # ensure n is divisible by procs
      # Randomize edges (connected to complete graph)
      m = random.randint(n - 1, n * (n - 1) // 2)
      # Randomize max weight between 1 and 100
      w = random.randint(1, 100)

      seed = idx * 1000 + 42  # Arbitrary, but reproducible

      try:
        print(f"Adding test #{idx} ({n=}, {m=}, {w=}, {procs=})")
        expected_flow, _ = run_create_flow(n, m, w, graph_file, seed)

        return {
            "graph_file": graph_file,
            "expected_flow": expected_flow,
            "params": [n, m, w, seed, procs],
        }

      except:
        pass

  with ThreadPoolExecutor() as executor:
    tests = list(executor.map(generate_test, range(1, NUM_TESTS + 1)))

  with open("tests/tests.json", "w") as f:
    json.dump(tests, f)


def load_tests():
  if not os.path.exists("tests/tests.json"):
    initialize_tests()

  with open("tests/tests.json") as f:
    return list(json.load(f))


num_actual_tests = 0
successes = 0


def run_tests(tests, algorithm, mode):
  global successes, num_actual_tests

  print(
      f"{YELLOW}Testing {NUM_TESTS} flow networks for {algorithm} in mode {mode}...{RESET}"
  )

  print(
      f"\t{'Idx':>3}\t | {'Params':<49}\t | {'Expected/Computed':<32}\t | Result"
  )
  print("\t" + "-" * 109)

  def do_test(a):
    idx, test = a
    expected_flow = test["expected_flow"]
    graph_file = test["graph_file"]
    num_procs = test["params"][-1] if mode == "par" else 1

    computed_flow, _ = run_c_implementation(graph_file, algorithm, num_procs)

    passed = expected_flow == computed_flow

    args = [
        idx + 1, *test["params"][:-1], num_procs, expected_flow, computed_flow,
        passed
    ]
    if not passed:
      failed_tests.append(args)
    print_result(*args)

    return (idx, test, computed_flow, expected_flow, passed)

  with ThreadPoolExecutor(max_workers=6) as executor:
    for *_, passed in executor.map(do_test, enumerate(tests)):
      if passed:
        successes += 1
      num_actual_tests += 1

  print("\t" + "-" * 109)


if __name__ == "__main__":
  tests = load_tests()

  run_tests(tests, algorithm='dinic', mode='par')
  run_tests(tests, algorithm='dinic', mode='seq')
  run_tests(tests, algorithm="edmonds-karp", mode='par')
  run_tests(tests, algorithm='edmonds-karp', mode='seq')

  if successes == num_actual_tests:
    print(GREEN + f"All {num_actual_tests} tests passed!" + RESET)
  else:
    print(
        RED +
        f"{num_actual_tests - successes} test(s) failed out of {num_actual_tests}."
        + RESET)

    for args in failed_tests:
      print_result(*args)
