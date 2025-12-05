#!/usr/bin/env python3
"""
examine_trace.py — visualize PAJE .trace files using the provided PajeParser

Usage:
    python examine_trace.py trace.trace out.png
"""

import argparse

import matplotlib
import matplotlib.pyplot as plt

from paje_parser import PajeParser


def examine_trace(trace: str, save_path: str = None):
  parser = PajeParser()
  parser.parse(trace)

  functions = {}
  for e in parser.events:
    if e.name == "PajeDefineEntityValue":
      functions[e.values["Alias"]] = e.values["Name"]

  actions = {}

  for e in parser.events:
    if e.name == "PajePushState":
      if "Container" in e.values:
        id = e.values["Container"]
        if id in actions:
          actions[id].append((e.values["Time"], functions[e.values["Value"]]))
        else:
          actions[id] = [(e.values["Time"], functions[e.values["Value"]])]

  cmap = matplotlib.colormaps["tab20"]
  color_map = {
      val: cmap(i / max(10, len(functions)))
      for i, val in enumerate(functions.values())
  }

  _, ax = plt.subplots(figsize=(10, 3))

  max_time = 0
  max_rank = 0

  for id in actions:
    for i, action in enumerate(actions[id]):
      if i == len(actions[id]) - 1:
        break
      start_time, rank = float(action[0]), int(id)
      end_time = float(actions[id][i + 1][0])
      ax.add_patch(
          plt.Rectangle(
              (start_time, rank),
              end_time - start_time,
              0.9,
              facecolor=color_map[action[1]],
              label=action[1],
          ))
      max_time = max(max_time, end_time)
      max_rank = max(rank, max_rank)

  ax.set_xlabel("Time [seconds]")
  ax.set_ylabel("Rank [count]")
  ax.set_xlim(0, max_time)
  ax.set_ylim(1, max_rank + 1)

  handles, labels = ax.get_legend_handles_labels()
  by_label = dict(zip(labels, handles))
  ax.legend(by_label.values(),
            by_label.keys(),
            loc="upper left",
            fontsize=8,
            ncol=4)

  ax.grid(False)
  plt.tight_layout()

  if save_path:
    plt.savefig(save_path, dpi=200)
    print(f"[examine_trace] saved figure to {save_path}")
  else:
    plt.show()


def main():
  parser = argparse.ArgumentParser(description="Visualize a PAJE .trace file.")
  parser.add_argument("trace", help="Path to .trace file")
  parser.add_argument(
      "out",
      nargs="?",
      default=None,
      help="Output image path (PNG/PDF). If omitted, show on screen.",
  )
  args = parser.parse_args()

  examine_trace(args.trace, save_path=args.out)


if __name__ == "__main__":
  main()
