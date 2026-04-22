#!/usr/bin/env python3
"""
Verify a trivial obstruction to the zero-cost empty-control external-block bridge.

Take the complete graph K_2. The whole vertex set is already a fixed-modulus cascade
witness of size q = 2 at modulus 2, since both induced degrees are 1 ≡ 1 [MOD 2].

But any conclusion of `HasPolynomialCostEmptyControlExternalBlockBridge 0` with m = q = 2
would need:

- a fixed-modulus cascade host whose terminal bucket has size exactly 2, and
- a nonempty separated control-block family outside that host.

On a graph with only two vertices, a host with terminal size 2 must already use every
vertex, leaving no room for any nonempty separated control block. So the D = 0 bridge
is false even in the smallest positive dyadic modulus.
"""

from __future__ import annotations

from itertools import combinations


Q = 2
N = 2
EDGES = ((0, 1),)


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


def has_fixed_modulus_cascade_witness_of_card_q(adj: list[int]) -> bool:
    full_mask = (1 << N) - 1
    residues = {degree_on_mask(adj, v, full_mask) % Q for v in range(N)}
    return len(residues) == 1


def has_d0_external_block_bridge_conclusion() -> bool:
    full_mask = (1 << N) - 1
    for host_vertices in combinations(range(N), Q):
        host_mask = mask(host_vertices)
        if host_mask != full_mask:
            continue
        external_vertices_mask = full_mask & ~host_mask
        if external_vertices_mask != 0:
            return True
    return False


def main() -> None:
    adj = build_adjacency()
    assert has_fixed_modulus_cascade_witness_of_card_q(adj)
    assert not has_d0_external_block_bridge_conclusion()

    print("D = 0 empty-control external-block bridge counterexample verified")
    print("graph = K_2")
    print("fixed-modulus cascade witness of size 2 at modulus 2: yes")
    print("nonempty separated external control-block family on a size-2 host in a 2-vertex graph: no")


if __name__ == "__main__":
    main()
