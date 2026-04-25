#!/usr/bin/env python3
"""
Exhaustive q = 4 terminal-host search.

This script attacks the first nontrivial terminal regularization case behind

  HasExactCardFixedSingleControlModularHostWitnessOfCard G 4 4

from the Lean development.

For each graph order n, it counts:

1. graphs with no regular induced subgraph of size at least 4;
2. among those, graphs that still admit a q = 4 exact-card single-control
   modular host witness.

If the second count is zero for all n < N and the first count is zero at N,
then the q = 4 terminal-host statement is settled for all graph orders:

- n < N was checked directly;
- n >= N is impossible because "having no regular induced 4-set" is hereditary.
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass
from itertools import combinations


Q = 4
TARGET_SIZE = 4


@dataclass(frozen=True)
class HostPattern:
    u_mask: int
    s_mask: int
    t_mask: int
    u_vertices: tuple[int, ...]


@dataclass(frozen=True)
class WitnessData:
    u_vertices: tuple[int, ...]
    s_vertices: tuple[int, ...]
    t_vertices: tuple[int, ...]
    drop_vertices: tuple[int, ...]
    host_degrees: tuple[int, ...]
    control_degrees: tuple[int, ...]
    drop_degrees: tuple[int, ...]
    internal_degrees: tuple[int, ...]


@dataclass(frozen=True)
class SearchSummary:
    n: int
    total_graphs: int
    regular_free_graphs: int
    host_counterexamples: int
    elapsed_seconds: float
    first_counterexample_edges: tuple[tuple[int, int], ...] | None = None
    first_counterexample_witness: WitnessData | None = None


def iter_nonempty_submasks(mask: int):
    submask = mask
    while submask:
        yield submask
        submask = (submask - 1) & mask


def iter_submasks(mask: int):
    yield 0
    yield from iter_nonempty_submasks(mask)


def vertices_from_mask(mask: int, n: int) -> tuple[int, ...]:
    return tuple(v for v in range(n) if (mask >> v) & 1)


def subset_masks_by_size(n: int) -> dict[int, list[int]]:
    return {
        k: [sum(1 << v for v in subset) for subset in combinations(range(n), k)]
        for k in range(n + 1)
    }


def regular_subset_candidates(n: int) -> list[tuple[int, tuple[int, ...]]]:
    masks = subset_masks_by_size(n)
    candidates: list[tuple[int, tuple[int, ...]]] = []
    for size in range(n, TARGET_SIZE - 1, -1):
        for mask in masks[size]:
            candidates.append((mask, vertices_from_mask(mask, n)))
    return candidates


def host_patterns(n: int) -> list[HostPattern]:
    masks = subset_masks_by_size(n)
    full_mask = (1 << n) - 1
    patterns: list[HostPattern] = []
    for u_mask in masks[TARGET_SIZE]:
        remaining = full_mask ^ u_mask
        for s_extra in iter_submasks(remaining):
            s_mask = u_mask | s_extra
            unused = full_mask ^ s_mask
            for t_mask in iter_nonempty_submasks(unused):
                patterns.append(
                    HostPattern(
                        u_mask=u_mask,
                        s_mask=s_mask,
                        t_mask=t_mask,
                        u_vertices=vertices_from_mask(u_mask, n),
                    )
                )
    return patterns


def edges_for_n(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def adjacency_masks(n: int, edge_mask: int, edges: list[tuple[int, int]]) -> list[int]:
    adj = [0] * n
    index = 0
    encoded = edge_mask
    while encoded:
        if encoded & 1:
            i, j = edges[index]
            adj[i] |= 1 << j
            adj[j] |= 1 << i
        encoded >>= 1
        index += 1
    return adj


def degree_on_mask(adj: list[int], vertex: int, subset_mask: int) -> int:
    return (adj[vertex] & subset_mask).bit_count()


def first_regular_induced_subset(
    adj: list[int], candidates: list[tuple[int, tuple[int, ...]]]
) -> tuple[int, ...] | None:
    for subset_mask, subset_vertices in candidates:
        target_degree = degree_on_mask(adj, subset_vertices[0], subset_mask)
        for vertex in subset_vertices[1:]:
            if degree_on_mask(adj, vertex, subset_mask) != target_degree:
                break
        else:
            return subset_vertices
    return None


def first_q4_terminal_host_witness(
    adj: list[int], n: int, patterns: list[HostPattern]
) -> WitnessData | None:
    for pattern in patterns:
        host_residue = None
        control_residue = None
        for vertex in pattern.u_vertices:
            current_host_residue = degree_on_mask(adj, vertex, pattern.s_mask) % Q
            current_control_residue = degree_on_mask(adj, vertex, pattern.t_mask) % Q
            if host_residue is None:
                host_residue = current_host_residue
                control_residue = current_control_residue
                continue
            if (
                current_host_residue != host_residue
                or current_control_residue != control_residue
            ):
                break
        else:
            drop_mask = pattern.s_mask ^ pattern.u_mask
            return WitnessData(
                u_vertices=pattern.u_vertices,
                s_vertices=vertices_from_mask(pattern.s_mask, n),
                t_vertices=vertices_from_mask(pattern.t_mask, n),
                drop_vertices=vertices_from_mask(drop_mask, n),
                host_degrees=tuple(
                    degree_on_mask(adj, vertex, pattern.s_mask)
                    for vertex in pattern.u_vertices
                ),
                control_degrees=tuple(
                    degree_on_mask(adj, vertex, pattern.t_mask)
                    for vertex in pattern.u_vertices
                ),
                drop_degrees=tuple(
                    degree_on_mask(adj, vertex, drop_mask)
                    for vertex in pattern.u_vertices
                ),
                internal_degrees=tuple(
                    degree_on_mask(adj, vertex, pattern.u_mask)
                    for vertex in pattern.u_vertices
                ),
            )
    return None


def edge_list_from_mask(edge_mask: int, edges: list[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
    return tuple(edge for index, edge in enumerate(edges) if (edge_mask >> index) & 1)


def analyze_graph_order(
    n: int, progress_step: int | None, stop_on_counterexample: bool
) -> SearchSummary:
    edges = edges_for_n(n)
    total_graphs = 1 << len(edges)
    regular_candidates = regular_subset_candidates(n)
    patterns = host_patterns(n)

    start = time.time()
    regular_free_graphs = 0
    host_counterexamples = 0
    first_edges: tuple[tuple[int, int], ...] | None = None
    first_witness: WitnessData | None = None

    for edge_mask in range(total_graphs):
        if progress_step and edge_mask and edge_mask % progress_step == 0:
            elapsed = time.time() - start
            print(
                f"  n={n}: checked {edge_mask:,}/{total_graphs:,} graphs "
                f"in {elapsed:.1f}s; regular-4-free so far: {regular_free_graphs:,}",
                flush=True,
            )

        adj = adjacency_masks(n, edge_mask, edges)
        if first_regular_induced_subset(adj, regular_candidates) is not None:
            continue

        regular_free_graphs += 1
        witness = first_q4_terminal_host_witness(adj, n, patterns)
        if witness is None:
            continue

        host_counterexamples += 1
        if first_edges is None:
            first_edges = edge_list_from_mask(edge_mask, edges)
            first_witness = witness
        if stop_on_counterexample:
            break

    return SearchSummary(
        n=n,
        total_graphs=total_graphs,
        regular_free_graphs=regular_free_graphs,
        host_counterexamples=host_counterexamples,
        elapsed_seconds=time.time() - start,
        first_counterexample_edges=first_edges,
        first_counterexample_witness=first_witness,
    )


def print_summary(summary: SearchSummary) -> None:
    print(
        f"n={summary.n}: checked {summary.total_graphs:,} graphs in "
        f"{summary.elapsed_seconds:.2f}s"
    )
    print(f"  regular-induced-4-free graphs: {summary.regular_free_graphs:,}")
    print(f"  host-witness counterexamples: {summary.host_counterexamples:,}")
    if summary.first_counterexample_edges is not None and summary.first_counterexample_witness is not None:
        witness = summary.first_counterexample_witness
        print("  first counterexample:")
        print(f"    edges: {list(summary.first_counterexample_edges)}")
        print(f"    U: {list(witness.u_vertices)}")
        print(f"    S: {list(witness.s_vertices)}")
        print(f"    T: {list(witness.t_vertices)}")
        print(f"    S \\\\ U: {list(witness.drop_vertices)}")
        print(f"    host degrees on U: {list(witness.host_degrees)}")
        print(f"    control degrees into T: {list(witness.control_degrees)}")
        print(f"    dropped-part degrees into S \\\\ U: {list(witness.drop_degrees)}")
        print(f"    internal degrees on U: {list(witness.internal_degrees)}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Exhaustively test the q=4 exact-card single-control host terminal statement."
        )
    )
    parser.add_argument(
        "--min-n",
        type=int,
        default=4,
        help="smallest graph order to inspect (default: 4)",
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=7,
        help="largest graph order to inspect (default: 7)",
    )
    parser.add_argument(
        "--progress-step",
        type=int,
        default=200_000,
        help="progress update cadence for exhaustive scans (default: 200000)",
    )
    parser.add_argument(
        "--stop-on-counterexample",
        action="store_true",
        help="stop immediately after the first host-witness counterexample",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.min_n < TARGET_SIZE:
        raise SystemExit(f"--min-n must be at least {TARGET_SIZE}")
    if args.max_n < args.min_n:
        raise SystemExit("--max-n must be at least --min-n")

    print("=" * 72)
    print("q = 4 exact-card single-control host search")
    print("=" * 72)
    print(
        "Counts graphs with no regular induced subgraph of size >= 4, and among\n"
        "those, counts graphs that still admit a q = 4 terminal host witness."
    )
    print()

    summaries: list[SearchSummary] = []
    for n in range(args.min_n, args.max_n + 1):
        summary = analyze_graph_order(
            n=n,
            progress_step=args.progress_step if n >= 7 else None,
            stop_on_counterexample=args.stop_on_counterexample,
        )
        summaries.append(summary)
        print_summary(summary)
        print()

        if summary.host_counterexamples:
            print("Counterexample found: the q = 4 terminal host statement fails.")
            return 1

        if summary.regular_free_graphs == 0:
            print(
                f"No regular-induced-4-free graphs remain at n={n}.\n"
                "Because this obstruction is hereditary, no larger graph order can produce one."
            )
            break

    last = summaries[-1]
    checked_small_orders = all(
        summary.host_counterexamples == 0
        for summary in summaries
        if summary.n < last.n or last.regular_free_graphs == 0
    )
    if last.regular_free_graphs == 0 and checked_small_orders:
        print("Conclusion:")
        print(
            "  The q = 4 terminal host statement survives exhaustive search.\n"
            f"  It holds directly on graph orders below {last.n}, and from order {last.n}\n"
            "  onward every graph already contains a regular induced 4-vertex subgraph."
        )
    else:
        print("Search completed without a counterexample in the requested range.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
