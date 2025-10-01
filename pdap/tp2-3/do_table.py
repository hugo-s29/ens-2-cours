import re
from collections import defaultdict
from tabulate import tabulate

# Latency mapping (based on log order)
latencies = ["1 μs", "10 μs", "100 μs"]

# Pretty names for implementations
impl_names = {
    "default_bcast": "DEFAULT BROADCAST",
    "naive_bcast": "NAIVE BROADCAST",
    "ring_bcast": "RING BROADCAST",
    "pipelined_ring_bcast": "PIPELINED RING BROADCAST",
    "asynchronous_pipelined_ring_bcast": "ASYNC PIPELINED RING BROADCAST",
    "asynchronous_pipelined_bintree_bcast": "ASYNC PIPELINED BINARY TREE RING BROADCAST",
}

# Whether implementation has chunk sizes
pipelined_impls = {
    "pipelined_ring_bcast",
    "asynchronous_pipelined_ring_bcast",
    "asynchronous_pipelined_bintree_bcast",
}

# Normalize chunk size into percentage
def chunk_to_percent(chunksize, maxsize=100_000_000):
    return round(chunksize / maxsize * 100)

# Parse log file
def parse_log(path):
    data = defaultdict(lambda: defaultdict(list))  # impl -> chunksize -> [times...]
    line_re = re.compile(
        r"implementation:\s*(\S+)\s*\|\s*chunksize:\s*(\d+)\s*\|\s*time:\s*([\d.]+)\s*seconds"
    )
    with open(path) as f:
        for line in f:
            m = line_re.search(line)
            if not m:
                continue
            impl, chunk, time = m.groups()
            chunk, time = int(chunk), float(time)
            data[impl][chunk].append(time)
    return data

# Build table
def build_table(data):
    table = []
    for impl, chunks in data.items():
        pretty_impl = impl_names.get(impl, impl.upper())
        if impl not in pipelined_impls:
            # Single row, average over runs
            row = [pretty_impl]
            for i in range(3):
                times = list(chunks.values())[0]  # only one chunksize
                row.append(f"{times[i]:.3f} s" if i < len(times) else "")
            table.append(row)
        else:
            # Header row for pipelined implem
            table.append([pretty_impl, "", "", ""])
            # Sort chunks by percentage
            for chunk in sorted(chunks.keys()):
                percent = chunk_to_percent(chunk)
                row = [f"with a chunk size of {percent:3d} %"]
                times = chunks[chunk]
                for i in range(3):
                    row.append(f"{times[i]:.3f} s" if i < len(times) else "")
                table.append(row)
    return table

def main():
    data = parse_log("log.log")
    table = build_table(data)
    headers = ["", *latencies]
    print(tabulate(table, headers=headers, tablefmt="grid", stralign="center"))

if __name__ == "__main__":
    main()
