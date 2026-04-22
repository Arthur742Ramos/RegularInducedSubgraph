#!/usr/bin/env python3
"""
Verify a q = 4 counterexample to the structured residue-upgrade route.

The graph has the canonical structured modular-host witness

- bucket u = {0, 1, 2, 3},
- host s = {0, 1, 2, 3, 7},
- control t = {4, 5, 6},

with |u| = 4 and |t| = 3 = q - 1.

On u, the host degrees inside G[s] are all 1 (hence constant mod 4) and the
control degrees into t are all exactly 1, so this is an exact-card fixed-modulus
single-control modular host witness with prescribed control size q - 1.

The script then exhaustively checks that the graph has no exact-card fixed-modulus
single-control residue host witness of size 4 with control size 3 anywhere in the
graph, so the structured residue-upgrade statement is false already at q = 4.

At the same time, the graph still has bounded exact single-control witnesses of
size 4 with control budget 3, so this does not refute the weaker direct exact
upgrade target.
"""

from __future__ import annotations

from itertools import combinations


Q = 4
N = 8
U = (0, 1, 2, 3)
S = (0, 1, 2, 3, 7)
T = (4, 5, 6)
EDGES = (
    (0, 3),
    (0, 5),
    (1, 4),
    (1, 7),
    (2, 6),
    (2, 7),
    (3, 6),
    (4, 5),
    (4, 7),
    (5, 6),
    (5, 7),
    (6, 7),
)


def build_adjacency() -> list[int]:
    adj = [0] * N
    for i, j in EDGES:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def mask(vertices: tuple[int, ...] | list[int] | set[int]) -> int:
    total = 0
    for v in vertices:
        total |= 1 << v
    return total


def vertices_of(subset_mask: int) -> tuple[int, ...]:
    return tuple(v for v in range(N) if subset_mask & (1 << v))


def degree_on_mask(adj: list[int], vertex: int, subset_mask: int) -> int:
    return (adj[vertex] & subset_mask).bit_count()


def host_degrees_mod_q(adj: list[int], u: tuple[int, ...], s_mask: int) -> tuple[int, ...]:
    return tuple(degree_on_mask(adj, vertex, s_mask) % Q for vertex in u)


def control_degrees(adj: list[int], u: tuple[int, ...], t_mask: int) -> tuple[int, ...]:
    return tuple(degree_on_mask(adj, vertex, t_mask) for vertex in u)


def drop_degrees_mod_q(adj: list[int], u: tuple[int, ...], s_mask: int, u_mask: int) -> tuple[int, ...]:
    drop_mask = s_mask & ~u_mask
    return tuple(degree_on_mask(adj, vertex, drop_mask) % Q for vertex in u)


def structured_modular_host_witnesses(
    adj: list[int],
) -> list[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]]:
    hits: list[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]] = []
    all_vertices = tuple(range(N))
    for u in combinations(all_vertices, Q):
        u_mask = mask(u)
        remaining = [v for v in all_vertices if not (u_mask & (1 << v))]
        for t in combinations(remaining, Q - 1):
            t_mask = mask(t)
            leftovers = [v for v in remaining if not (t_mask & (1 << v))]
            for host_extra_count in range(len(leftovers) + 1):
                for extra in combinations(leftovers, host_extra_count):
                    s_mask = u_mask | mask(extra)
                    host_vals = host_degrees_mod_q(adj, u, s_mask)
                    ctrl_vals = control_degrees(adj, u, t_mask)
                    if len(set(host_vals)) == 1 and len(set(ctrl_vals)) == 1:
                        hits.append((u, vertices_of(s_mask), t, host_vals, ctrl_vals))
    return hits


def structured_residue_host_witnesses(
    adj: list[int],
) -> list[
    tuple[
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
    ]
]:
    hits: list[
        tuple[
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
        ]
    ] = []
    all_vertices = tuple(range(N))
    for u in combinations(all_vertices, Q):
        u_mask = mask(u)
        remaining = [v for v in all_vertices if not (u_mask & (1 << v))]
        for t in combinations(remaining, Q - 1):
            t_mask = mask(t)
            leftovers = [v for v in remaining if not (t_mask & (1 << v))]
            for host_extra_count in range(len(leftovers) + 1):
                for extra in combinations(leftovers, host_extra_count):
                    s_mask = u_mask | mask(extra)
                    host_vals = host_degrees_mod_q(adj, u, s_mask)
                    ctrl_vals = control_degrees(adj, u, t_mask)
                    drop_vals = drop_degrees_mod_q(adj, u, s_mask, u_mask)
                    if (
                        len(set(host_vals)) == 1
                        and len(set(ctrl_vals)) == 1
                        and len(set(drop_vals)) == 1
                    ):
                        hits.append((u, vertices_of(s_mask), t, host_vals, ctrl_vals, drop_vals))
    return hits


def bounded_exact_witnesses(
    adj: list[int],
) -> list[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]]:
    hits: list[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]] = []
    all_vertices = tuple(range(N))
    all_mask = mask(all_vertices)
    for size in range(Q, N + 1):
        for s in combinations(all_vertices, size):
            s_mask = mask(s)
            remaining = [v for v in all_vertices if not (s_mask & (1 << v))]
            for t_size in range(1, min(Q - 1, len(remaining)) + 1):
                for t in combinations(remaining, t_size):
                    t_mask = mask(t)
                    ambient_mask = s_mask | t_mask
                    ambient_vals = tuple(degree_on_mask(adj, vertex, ambient_mask) for vertex in s)
                    ctrl_vals = tuple(degree_on_mask(adj, vertex, t_mask) for vertex in s)
                    if len(set(ambient_vals)) == 1 and len(set(ctrl_vals)) == 1:
                        hits.append((s, t, ambient_vals, ctrl_vals))
    return hits


def main() -> None:
    adj = build_adjacency()

    u_mask = mask(U)
    s_mask = mask(S)
    t_mask = mask(T)

    canonical_host = host_degrees_mod_q(adj, U, s_mask)
    canonical_ctrl = control_degrees(adj, U, t_mask)
    canonical_drop = drop_degrees_mod_q(adj, U, s_mask, u_mask)

    assert canonical_host == (1, 1, 1, 1)
    assert canonical_ctrl == (1, 1, 1, 1)
    assert canonical_drop == (0, 1, 1, 0)

    modular_hits = structured_modular_host_witnesses(adj)
    residue_hits = structured_residue_host_witnesses(adj)
    exact_hits = bounded_exact_witnesses(adj)

    assert modular_hits == [((0, 1, 2, 3), (0, 1, 2, 3, 7), (4, 5, 6), (1, 1, 1, 1), (1, 1, 1, 1))]
    assert not residue_hits
    assert exact_hits

    print("q = 4 structured residue-upgrade counterexample verified")
    print(f"u = {U}")
    print(f"s = {S}")
    print(f"t = {T}")
    print(f"edges = {EDGES}")
    print(f"host degrees on u in G[s] mod 4 = {canonical_host}")
    print(f"control degrees on u into t = {canonical_ctrl}")
    print(f"drop degrees on s \\\\ u mod 4 = {canonical_drop}")
    print("structured modular host witnesses with |u| = 4 and |t| = 3:")
    for hit in modular_hits:
        print(f"  {hit}")
    print("structured residue host witnesses with |u| = 4 and |t| = 3: none")
    print("bounded exact single-control witnesses of size 4 and budget 3:")
    for hit in exact_hits:
        print(f"  {hit}")


if __name__ == "__main__":
    main()
