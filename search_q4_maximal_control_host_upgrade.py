#!/usr/bin/env python3
"""
SAT search for q = 4 maximal-control direct host-upgrade counterexamples.

This script searches for graphs on n vertices with a canonical witness candidate

  u = {0,1,2,3},  t = {4,5,6},  s = u ∪ host_extra

such that:

1. the host degrees on u inside G[s] are constant mod 4;
2. the control degrees into t are exact on u (equivalently constant mod 4,
   since |t| = 3 < 4);
3. there is no bounded exact single-control witness of size at least 4 and
   control size at most 3 anywhere in the graph.

By relabeling vertices, this covers the q = 4 instances of

  HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
    G 4 4 3

up to the choice of the host extra vertices.
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations
from pathlib import Path
from typing import Iterable

import z3


Q = 4
W = (0, 1, 2, 3)
T = (4, 5, 6)


def parse_host_extra(text: str) -> tuple[int, ...]:
    if not text.strip():
        return ()
    parts = [part.strip() for part in text.replace(" ", "").split(",") if part.strip()]
    return tuple(sorted(int(part) for part in parts))


def edge_pairs(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def all_host_extras(free_vertices: tuple[int, ...]) -> Iterable[tuple[int, ...]]:
    for size in range(len(free_vertices) + 1):
        yield from combinations(free_vertices, size)


def build_exact_candidates(n: int) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    verts = tuple(range(n))
    candidates: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for size in range(Q, n + 1):
        for s_vertices in combinations(verts, size):
            remaining = [v for v in verts if v not in s_vertices]
            for t_size in range(1, min(Q - 1, len(remaining)) + 1):
                for t_vertices in combinations(remaining, t_size):
                    candidates.append((s_vertices, t_vertices))
    return candidates


def solve_host_shape(
    n: int,
    host_extra: tuple[int, ...],
    exact_candidates: list[tuple[tuple[int, ...], tuple[int, ...]]],
    timeout_ms: int | None,
) -> tuple[str, tuple[tuple[int, int], ...] | None]:
    pairs = edge_pairs(n)
    edge = {pair: z3.Bool(f"e_{pair[0]}_{pair[1]}") for pair in pairs}

    def e(i: int, j: int):
        return edge[(i, j)] if i < j else edge[(j, i)]

    def deg(v: int, subset: tuple[int, ...]):
        return z3.Sum([z3.If(e(v, u), 1, 0) for u in subset if u != v])

    def const_mod(vertices: tuple[int, ...], subset: tuple[int, ...], q: int):
        if len(vertices) <= 1:
            return z3.BoolVal(True)
        base = vertices[0]
        base_deg = deg(base, subset)
        return z3.And([(deg(v, subset) - base_deg) % q == 0 for v in vertices[1:]])

    def const_exact(vertices: tuple[int, ...], subset: tuple[int, ...]):
        if len(vertices) <= 1:
            return z3.BoolVal(True)
        base = vertices[0]
        base_deg = deg(base, subset)
        return z3.And([deg(v, subset) == base_deg for v in vertices[1:]])

    def has_exact_witness_formula(s_vertices: tuple[int, ...], t_vertices: tuple[int, ...]):
        ambient = tuple(sorted(set(s_vertices) | set(t_vertices)))
        return z3.And(const_exact(s_vertices, ambient), const_exact(s_vertices, t_vertices))

    s_vertices = W + host_extra
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)
    solver.add(const_mod(W, s_vertices, Q))
    solver.add(const_exact(W, T))
    for candidate_s, candidate_t in exact_candidates:
        solver.add(z3.Not(has_exact_witness_formula(candidate_s, candidate_t)))

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        chosen_edges = tuple(
            pair
            for pair in pairs
            if z3.is_true(model.evaluate(edge[pair], model_completion=True))
        )
        return "sat", chosen_edges
    if result == z3.unsat:
        return "unsat", None
    return "unknown", None


def write_receipt(
    receipt_path: Path,
    *,
    n: int,
    shapes: list[tuple[int, ...]],
    free_vertices: tuple[int, ...],
    exact_candidates_count: int,
    timeout_ms: int | None,
    shape_results: list[dict[str, object]],
    final_status: str,
    searched_all_shapes: bool,
) -> None:
    payload = {
        "n": n,
        "q": Q,
        "u": list(W),
        "t": list(T),
        "free_vertices": list(free_vertices),
        "host_shapes_requested": [list(shape) for shape in shapes],
        "host_shapes_requested_count": len(shapes),
        "forbidden_exact_witnesses": exact_candidates_count,
        "timeout_ms": timeout_ms,
        "searched_all_shapes": searched_all_shapes,
        "final_status": final_status,
        "shape_results": shape_results,
    }
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True, help="graph order")
    parser.add_argument(
        "--host-extra",
        action="append",
        default=[],
        help="comma-separated host extra vertices outside u = {0,1,2,3}",
    )
    parser.add_argument(
        "--timeout-ms",
        type=int,
        default=None,
        help="optional per-host-shape z3 timeout",
    )
    parser.add_argument(
        "--receipt-path",
        type=Path,
        default=None,
        help="optional JSON file that records the full run summary and per-shape outcomes",
    )
    args = parser.parse_args()

    if args.n < 7:
        raise SystemExit("n must be at least 7 so that u and t fit")

    free_vertices = tuple(range(7, args.n))
    requested_shapes = [parse_host_extra(text) for text in args.host_extra]
    for shape in requested_shapes:
        invalid = tuple(v for v in shape if v not in free_vertices)
        if invalid:
            raise SystemExit(
                f"host-extra {shape} uses vertices outside the free range {free_vertices}: {invalid}"
            )
        if len(shape) != len(set(shape)):
            raise SystemExit(f"host-extra {shape} repeats a vertex")

    exact_candidates = build_exact_candidates(args.n)
    shapes = requested_shapes or list(all_host_extras(free_vertices))

    print(f"n = {args.n}")
    print(f"u = {W}")
    print(f"t = {T}")
    print(f"free vertices = {free_vertices}")
    print(f"host shapes to test = {len(shapes)}")
    print(f"forbidden exact witnesses = {len(exact_candidates)}")
    if args.timeout_ms is not None:
        print(f"per-shape timeout = {args.timeout_ms} ms")

    shape_results: list[dict[str, object]] = []
    saw_unknown = False
    for host_extra in shapes:
        status, chosen_edges = solve_host_shape(
            n=args.n,
            host_extra=host_extra,
            exact_candidates=exact_candidates,
            timeout_ms=args.timeout_ms,
        )
        s_vertices = W + host_extra
        shape_results.append(
            {
                "host_extra": list(host_extra),
                "s_vertices": list(s_vertices),
                "status": status,
                "edges": [list(edge) for edge in chosen_edges] if chosen_edges is not None else None,
            }
        )
        print(f"s={s_vertices} {status}", flush=True)
        if status == "sat":
            print(f"edges = {chosen_edges}", flush=True)
            if args.receipt_path is not None:
                write_receipt(
                    args.receipt_path,
                    n=args.n,
                    shapes=shapes,
                    free_vertices=free_vertices,
                    exact_candidates_count=len(exact_candidates),
                    timeout_ms=args.timeout_ms,
                    shape_results=shape_results,
                    final_status="sat",
                    searched_all_shapes=False,
                )
            return
        if status == "unknown":
            saw_unknown = True

    final_status = "unknown" if saw_unknown else "unsat"
    if args.receipt_path is not None:
        write_receipt(
            args.receipt_path,
            n=args.n,
            shapes=shapes,
            free_vertices=free_vertices,
            exact_candidates_count=len(exact_candidates),
            timeout_ms=args.timeout_ms,
            shape_results=shape_results,
            final_status=final_status,
            searched_all_shapes=True,
        )
    if saw_unknown:
        print("no sat host shape found; some tested host shapes are unknown", flush=True)
    else:
        print("all tested host shapes unsat", flush=True)


if __name__ == "__main__":
    main()
