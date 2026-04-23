# q = 4 terminal host search

This note records the outcome of the exhaustive Python search in
`search_structured_q4.py`.

## Target

Test the first nontrivial terminal single-control host statement:

> If a graph `G` has an exact-card fixed-modulus single-control modular host witness of size
> `4` at modulus `4`, must `G` contain a regular induced subgraph on at least `4` vertices?

In the Lean names, this is the `j = 2` slice of
`HasExactCardFixedSingleControlHostTerminalRegularization`, namely

`HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G 4 4 ->
 HasRegularInducedSubgraphOfCard G 4`.

## Exhaustive counts

Running

```powershell
python search_structured_q4.py
```

checks every labelled graph on `n = 4, 5, 6, 7` vertices and records:

1. how many graphs have no regular induced subgraph of size at least `4`;
2. among those, how many still admit a `q = 4` exact-card single-control modular host witness.

The counts are:

- `n = 4`: `56` regular-induced-4-free graphs, `0` host-witness counterexamples.
- `n = 5`: `500` regular-induced-4-free graphs, `0` host-witness counterexamples.
- `n = 6`: `3480` regular-induced-4-free graphs, `0` host-witness counterexamples.
- `n = 7`: `0` regular-induced-4-free graphs, hence also `0` host-witness counterexamples.

## Consequence

The property "has no regular induced subgraph of size at least `4`" is hereditary under induced
subgraphs. Since the exhaustive search finds no such graph on `7` vertices, none can exist on any
larger number of vertices either.

So the `q = 4` terminal host statement survives exhaustive search:

- graph orders below `7` were checked directly;
- from graph order `7` onward, every graph already contains a regular induced `4`-vertex subgraph.

## Status

This is external computational evidence, not yet a Lean theorem. The search is intended to clear
the `q = 4` case off the critical path so the remaining work can focus on genuinely larger moduli.
