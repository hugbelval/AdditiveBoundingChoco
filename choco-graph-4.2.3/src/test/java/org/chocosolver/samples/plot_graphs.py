#!/usr/bin/env python3
"""
plot_graphs.py
--------------
Reads a text file containing multiple DOT digraph definitions separated by '---'
and renders each one successively using Graphviz's circo layout engine.

Usage:
    python plot_graphs.py <input_file.txt>

Navigation:
    Press any key or click 'Next' to advance to the next graph.
    Press 'q' or close the window to quit.
"""

import sys
import re
import subprocess
import tempfile
import os
import argparse
from pathlib import Path


# ── dependency check ──────────────────────────────────────────────────────────

def check_dependencies():
    """Verify graphviz (circo) and matplotlib are available."""
    try:
        import matplotlib  # noqa: F401
    except ImportError:
        sys.exit("Error: matplotlib is not installed.  Run: pip install matplotlib")

    result = subprocess.run(["circo", "-V"], capture_output=True)
    if result.returncode not in (0, 1):          # circo prints version to stderr, exits 1
        sys.exit("Error: Graphviz 'circo' not found.  Install Graphviz and ensure it is on PATH.")


# ── parsing ───────────────────────────────────────────────────────────────────

def split_graphs(text: str) -> list[str]:
    """
    Split the file content on '---' separators and return a list of
    non-empty DOT graph strings.
    """
    parts = re.split(r'\n\s*---\s*\n', text)
    graphs = [p.strip() for p in parts if p.strip()]
    return graphs


def extract_title(dot_source: str, index: int) -> str:
    """Try to pull a graph label from the DOT source, else fall back to index."""
    m = re.search(r'label\s*=\s*"([^"]+)"', dot_source)
    if m:
        return m.group(1)
    return f"Graph {index + 1}"


# ── rendering ─────────────────────────────────────────────────────────────────

def dot_to_png(dot_source: str) -> bytes:
    """
    Pipe DOT source through circo and return PNG bytes.
    Raises RuntimeError on failure.
    """
    result = subprocess.run(
        ["circo", "-Tpng"],
        input=dot_source.encode(),
        capture_output=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode())
    return result.stdout


# ── interactive viewer ────────────────────────────────────────────────────────

def view_graphs_interactive(graphs: list[str]) -> None:
    """Display graphs one by one in a matplotlib window with Prev / Next buttons."""
    import matplotlib.pyplot as plt
    import matplotlib.image as mpimg
    from matplotlib.widgets import Button
    import io

    n = len(graphs)
    state = {"idx": 0}

    fig, ax = plt.subplots(figsize=(10, 8))
    plt.subplots_adjust(bottom=0.12)
    ax.axis("off")

    # ── pre-render all graphs to PNG bytes ────────────────────────────────────
    print(f"Rendering {n} graph(s) with circo …", flush=True)
    png_cache: list[bytes | None] = [None] * n

    def get_png(i: int) -> bytes:
        if png_cache[i] is None:
            print(f"  Rendering graph {i + 1}/{n} …", flush=True)
            png_cache[i] = dot_to_png(graphs[i])
        return png_cache[i]

    # ── display helper ────────────────────────────────────────────────────────
    def show(i: int) -> None:
        png = get_png(i)
        img = mpimg.imread(io.BytesIO(png))
        ax.clear()
        ax.imshow(img)
        ax.axis("off")
        fig.suptitle(
            f"{extract_title(graphs[i], i)}   [{i + 1} / {n}]",
            fontsize=13, fontweight="bold",
        )
        fig.canvas.draw_idle()

    # ── buttons ───────────────────────────────────────────────────────────────
    ax_prev = plt.axes([0.35, 0.03, 0.12, 0.05])
    ax_next = plt.axes([0.53, 0.03, 0.12, 0.05])
    btn_prev = Button(ax_prev, "◀  Prev")
    btn_next = Button(ax_next, "Next  ▶")

    def on_prev(_event) -> None:
        if state["idx"] > 0:
            state["idx"] -= 1
            show(state["idx"])

    def on_next(_event) -> None:
        if state["idx"] < n - 1:
            state["idx"] += 1
            show(state["idx"])

    btn_prev.on_clicked(on_prev)
    btn_next.on_clicked(on_next)

    # ── keyboard navigation ───────────────────────────────────────────────────
    def on_key(event) -> None:
        if event.key in ("right", "n", " ", "return"):
            on_next(event)
        elif event.key in ("left", "p", "backspace"):
            on_prev(event)
        elif event.key in ("q", "escape"):
            plt.close("all")

    fig.canvas.mpl_connect("key_press_event", on_key)

    show(0)
    plt.show()


# ── batch / headless export ───────────────────────────────────────────────────

def export_pngs(graphs: list[str], out_dir: Path) -> None:
    """Render every graph to a numbered PNG file in out_dir (no display needed)."""
    out_dir.mkdir(parents=True, exist_ok=True)
    n = len(graphs)
    for i, g in enumerate(graphs):
        path = out_dir / f"graph_{i + 1:04d}.png"
        print(f"  [{i + 1}/{n}] → {path}", flush=True)
        png = dot_to_png(g)
        path.write_bytes(png)
    print(f"\nDone. {n} PNG(s) saved to '{out_dir}'.")


# ── CLI ───────────────────────────────────────────────────────────────────────

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Plot successive DOT digraphs (circo layout) from a text file."
    )
    p.add_argument("input_file", help="Path to the .txt file containing DOT graphs separated by ---")
    p.add_argument(
        "--export", metavar="DIR",
        help="Instead of an interactive window, export all graphs as PNGs to DIR.",
    )
    p.add_argument(
        "--start", type=int, default=1, metavar="N",
        help="Start at graph number N (1-based, default: 1).",
    )
    return p


def main() -> None:
    check_dependencies()

    parser = build_parser()
    args = parser.parse_args()

    src_path = Path(args.input_file)
    if not src_path.is_file():
        sys.exit(f"Error: file not found: {src_path}")

    text = src_path.read_text(encoding="utf-8", errors="replace")
    graphs = split_graphs(text)

    if not graphs:
        sys.exit("No graphs found in the file.")

    print(f"Found {len(graphs)} graph(s) in '{src_path.name}'.")

    if args.export:
        export_pngs(graphs, Path(args.export))
    else:
        # Slice to requested start index
        start = max(0, args.start - 1)
        if start >= len(graphs):
            print(f"Warning: --start {args.start} exceeds graph count; starting at 1.")
            start = 0
        view_graphs_interactive(graphs[start:])


if __name__ == "__main__":
    main()
