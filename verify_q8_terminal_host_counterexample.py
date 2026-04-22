#!/usr/bin/env python3
"""
Verify an explicit q = 8 terminal-host counterexample.

The graph has:

- bucket u = {0, ..., 7},
- host s = {0, ..., 9},
- control t = {10},

and edges

  (0,8), (0,9), (1,6), (1,7), (2,6), (2,8), (3,8), (3,9),
  (4,8), (4,9), (5,8), (5,9), (7,8).

On u, the host degrees inside G[s] are all 2 and the control degrees into t
are all 0, so this is an exact-card fixed-modulus single-control modular host
witness of size 8 at modulus 8.

The script exhaustively checks all induced subsets of size at least 8 and
confirms that none is regular. It also exhaustively checks the weaker terminal
control-block modular cascade package at size 8 and finds no witness there
either.

Hence the direct terminal host statement at q = 8 is false, and the same graph
also rules out the budget-1 terminal host-to-cascade shortcut.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import combinations


Q = 8
TARGET_SIZE = 8
N = 11
U = tuple(range(8))
S = tuple(range(10))
T = (10,)
EDGES = (
    (0, 8),
    (0, 9),
    (1, 6),
    (1, 7),
    (2, 6),
    (2, 8),
    (3, 8),
    (3, 9),
    (4, 8),
    (4, 9),
    (5, 8),
    (5, 9),
    (7, 8),
)


def build_adjacency() -> list[int]:
    adj = [0] * N
    for i, j in EDGES:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def mask(vertices: tuple[int, ...] | list[int] | range) -> int:
    total = 0
    for v in vertices:
        total |= 1 << v
    return total


def degree_on_mask(adj: list[int], vertex: int, subset_mask: int) -> int:
    return (adj[vertex] & subset_mask).bit_count()


def regular_subsets_of_size_at_least(adj: list[int], k: int) -> list[tuple[tuple[int, ...], int]]:
    hits: list[tuple[tuple[int, ...], int]] = []
    for size in range(k, N + 1):
        for subset in combinations(range(N), size):
            subset_mask = mask(subset)
            target_degree = degree_on_mask(adj, subset[0], subset_mask)
            if all(degree_on_mask(adj, vertex, subset_mask) == target_degree for vertex in subset[1:]):
                hits.append((subset, target_degree))
    return hits


def subset_masks_of_size(
    vertices_mask: int, min_size: int, max_size: int | None = None
) -> list[int]:
    vertices = tuple(v for v in range(N) if vertices_mask & (1 << v))
    if max_size is None:
        max_size = len(vertices)
    hits: list[int] = []
    for size in range(min_size, max_size + 1):
        for subset in combinations(vertices, size):
            hits.append(mask(subset))
    return hits


def ambient_degree_is_constant_mod_q(adj: list[int], bucket_mask: int, ambient_mask: int) -> bool:
    residues = {degree_on_mask(adj, vertex, ambient_mask) % Q for vertex in range(N) if bucket_mask & (1 << vertex)}
    return len(residues) <= 1


def external_block_degrees_are_constant_mod_q(
    adj: list[int], host_mask: int, blocks: tuple[int, ...]
) -> bool:
    host_vertices = [vertex for vertex in range(N) if host_mask & (1 << vertex)]
    for block_mask in blocks:
        residues = {degree_on_mask(adj, vertex, block_mask) % Q for vertex in host_vertices}
        if len(residues) > 1:
            return False
    return True


def drop_degree_is_constant_mod_q(adj: list[int], bucket_mask: int, drop_mask: int) -> bool:
    residues = {degree_on_mask(adj, vertex, drop_mask) % Q for vertex in range(N) if bucket_mask & (1 << vertex)}
    return len(residues) <= 1


def nonempty_partitions(vertices_mask: int) -> list[tuple[int, ...]]:
    @lru_cache(maxsize=None)
    def go(mask_value: int) -> tuple[tuple[int, ...], ...]:
        if mask_value == 0:
            return ((),)
        vertices = tuple(v for v in range(N) if mask_value & (1 << v))
        first = vertices[0]
        rest_mask = mask_value & ~(1 << first)
        hits: set[tuple[int, ...]] = set()
        for submask in subset_masks_of_size(rest_mask, 0):
            block_mask = submask | (1 << first)
            remaining_mask = mask_value & ~block_mask
            for tail in go(remaining_mask):
                hits.add(tuple(sorted((block_mask,) + tail)))
        return tuple(sorted(hits))

    if vertices_mask == 0:
        return []
    return list(go(vertices_mask))


def has_fixed_modulus_control_block_modular_cascade_witness_of_card(
    adj: list[int], k: int
) -> bool:
    all_vertices_mask = (1 << N) - 1

    @lru_cache(maxsize=None)
    def has_cascade_from(host_mask: int, blocks: tuple[int, ...]) -> bool:
        block_union_mask = 0
        for block_mask in blocks:
            block_union_mask |= block_mask

        if host_mask.bit_count() == k:
            return ambient_degree_is_constant_mod_q(adj, host_mask, host_mask | block_union_mask) and (
                external_block_degrees_are_constant_mod_q(adj, host_mask, blocks)
            )

        for next_mask in subset_masks_of_size(host_mask, k, host_mask.bit_count() - 1):
            drop_mask = host_mask & ~next_mask
            if ambient_degree_is_constant_mod_q(adj, next_mask, host_mask | block_union_mask) and (
                drop_degree_is_constant_mod_q(adj, next_mask, drop_mask)
            ) and has_cascade_from(next_mask, blocks):
                return True
        return False

    for host_size in range(k, N):
        for host_vertices in combinations(range(N), host_size):
            host_mask = mask(host_vertices)
            external_vertices_mask = all_vertices_mask & ~host_mask
            for union_mask in subset_masks_of_size(external_vertices_mask, 1):
                for blocks in nonempty_partitions(union_mask):
                    if has_cascade_from(host_mask, blocks):
                        return True
    return False


def main() -> None:
    adj = build_adjacency()
    u_mask = mask(U)
    s_mask = mask(S)
    t_mask = mask(T)
    drop_mask = s_mask ^ u_mask

    host_degrees = tuple(degree_on_mask(adj, vertex, s_mask) for vertex in U)
    control_degrees = tuple(degree_on_mask(adj, vertex, t_mask) for vertex in U)
    internal_degrees = tuple(degree_on_mask(adj, vertex, u_mask) for vertex in U)
    drop_degrees = tuple(degree_on_mask(adj, vertex, drop_mask) for vertex in U)

    assert len(set(value % Q for value in host_degrees)) == 1
    assert len(set(value % Q for value in control_degrees)) == 1

    regular_hits = regular_subsets_of_size_at_least(adj, TARGET_SIZE)
    assert not regular_hits
    has_cascade_witness = has_fixed_modulus_control_block_modular_cascade_witness_of_card(
        adj, TARGET_SIZE
    )
    assert not has_cascade_witness

    print("q = 8 terminal-host counterexample verified")
    print(f"u = {U}")
    print(f"s = {S}")
    print(f"t = {T}")
    print(f"edges = {EDGES}")
    print(f"host degrees on u in G[s] = {host_degrees}")
    print(f"control degrees on u into t = {control_degrees}")
    print(f"internal degrees on u = {internal_degrees}")
    print(f"drop degrees on s \\\\ u = {drop_degrees}")
    print("regular induced subsets of size >= 8: none")
    print("fixed-modulus control-block modular cascade witnesses of size 8: none")


if __name__ == "__main__":
    main()
