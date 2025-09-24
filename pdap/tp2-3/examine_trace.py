import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
import sys

def examine_trace(trace : str, save_path=None):
    cols = ["Nature", "Container", "Type", "Start", "End", "Duration", "Imbrication", "Value"]
    dta = pd.read_csv(trace, names=cols)

    df_states = (
        dta.assign(
            Rank=dta["Container"].str.replace("rank-", "", regex=True).astype(int),
            Operation=dta["Value"].str.replace("^PMPI_", "MPI_", regex=True)
        )
    )

    unique_vals = df_states["Value"].unique()
    cmap = matplotlib.colormaps["tab20"]
    color_map = {val: cmap(i / max(10, len(unique_vals))) for i, val in enumerate(unique_vals)}

    _, ax = plt.subplots(figsize=(10, 3))

    for _, row in df_states.iterrows():
        ax.add_patch(plt.Rectangle(
            (row["Start"], row["Rank"]),      
            row["End"] - row["Start"],
            0.9,
            facecolor=color_map[row["Value"]],            
            label=row["Value"],
        ))

    ax.set_xlabel("Time [seconds]")
    ax.set_ylabel("Rank [count]")
    ax.set_xlim(df_states["Start"].min(), df_states["End"].max())
    ax.set_ylim(df_states["Rank"].min(), df_states["Rank"].max() + 1)

    handles, labels = ax.get_legend_handles_labels()
    by_label = dict(zip(labels, handles))
    ax.legend(by_label.values(), by_label.keys(), loc="upper left", fontsize=8, ncol=4)

    ax.grid(False)
    plt.tight_layout()

    if save_path is not None:
        plt.savefig(save_path)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py <trace> <out_file>")
        sys.exit(1)
    
    trace = sys.argv[1] 
    out_file = sys.argv[2] 
    examine_trace(trace, out_file)