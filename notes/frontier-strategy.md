# Frontier Strategy Notes

This note records the sharpest reduction added in the current pass and the two proof programs it
suggests.

## 1. Exact regularity from a small control set

Let `s, t` be disjoint vertex sets.

If every vertex of `s` has

- the same degree in the ambient induced graph `G[s ∪ t]`, and
- the same number of neighbors in the control set `t`,

then every vertex of `s` has the same number of neighbors inside `s`, because

`deg_{G[s]}(v) = deg_{G[s ∪ t]}(v) - deg_t(v)`.

This is now formalized in `RegularInducedSubgraph.Basic` as
`inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree`.

Why this matters:

- A full neighborhood profile on a control set of size `m` has `2^m` possibilities.
- A degree into that same control set has only `m + 1` possibilities.

So any refinement scheme that only needs control-set degrees is exponentially cheaper than one
that stores full adjacency patterns.

## 2. Multiscale control-block program

The most plausible direct route now looks like this:

1. Pick a small control block `T_1`.
2. Bucket the remaining vertices by degree into `T_1`.
3. Pass to a large bucket.
4. Repeat with fresh disjoint control blocks `T_2, T_3, ...`.

If this can be organized so that, on the surviving bucket `S`,

- the degree vector into the control blocks is frozen, and
- the ambient degree inside `G[S ∪ T_1 ∪ ... ∪ T_r]` is also frozen,

then the control-set lemma gives an exactly regular induced graph on `S`.

The key open combinatorial task is therefore:

> Force a large bucket on which the ambient degree collapses without paying the full
> `2^{|T_1| + ... + |T_r|}` profile cost.

This is the point where a genuine superlogarithmic gain could enter.

## 3. Modular route

Another promising direction is to weaken exact equality first:

- find a large induced subgraph whose degrees are all congruent modulo `q`,
- then push `q` upward until the modulus exceeds the final degree range.

If one ever reaches an induced subgraph on `m` vertices with all degrees congruent modulo some
`q > m`, then the degrees are forced to be exactly equal, so the graph is regular.

Gallai's theorem on large even-degree induced subgraphs is the `q = 2` starting point for this
program. The difficult part is finding a modulus-lifting mechanism that survives restriction to
subgraphs.

This collapse is now formalized in `RegularInducedSubgraph.Modular`:

- `inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree`
  shows that congruence modulo any `q ≥ |S|` already forces exact regularity on `S`;
- `inducesModEqDegree_of_modEq_unionDegree_and_externalDegree`
  transports modular equality from ambient degrees in `G[S ∪ T]` and external degrees into `T`
  down to modular equality inside `G[S]`;
- `hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard`
  packages the finite equivalence between modular witnesses and exact regular induced subgraphs;
- `exists_large_mod_pair_of_mul_le_card` and `exists_large_subset_with_constant_mod_pair`
  give the finite pigeonhole step for paired residue data, with only `q^2` buckets;
- `eventualNatPowerModularDomination_iff_targetStatement`
  upgrades this to an asymptotic reduction along geometric scales.

So the modular program can now be stated cleanly as:

> Fix `b > 1`. For every `M`, show that for all large `k`, every graph on `b^k` vertices contains
> an induced subgraph `S` with `|S| >= M k` such that the degrees in `G[S]` are all congruent
> modulo some `q >= |S|`.

That statement is already equivalent to the original conjecture.

The next concrete modular-control target is therefore:

> Find disjoint sets `S, T` and a modulus `q` for which
> - the ambient degrees in `G[S ∪ T]` are constant modulo `q` on `S`,
> - the degrees into `T` are constant modulo `q` on `S`,
> - and `q` is eventually at least `|S|`.

This target is now formalized in `RegularInducedSubgraph.Modular` as
`HasSingleControlModularWitnessOfCard`, with asymptotic versions
`EventualNatPowerSingleControlModularDomination` and
`EventualNatPowerBoundedSingleControlModularDomination`.

The remaining obstruction is also formalized now: the residue-bucketing step naturally produces a
large subset `U ⊆ S` only after throwing away `S \ U`, so one still has to control the dropped-part
residue together with the control-set residue. This is packaged as the stronger witness
`HasSingleControlModularBucketingWitnessOfCard` and the asymptotic targets
`EventualNatPowerSingleControlModularBucketingDomination` /
`EventualNatPowerBoundedSingleControlModularBucketingDomination`.

The same obstruction is now packaged at the multiblock level as well:
`HasControlBlockModularBucketingWitnessOfCard` and
`EventualNatPowerControlBlockModularBucketingDomination`, together with bounded versions. This
separates the genuinely combinatorial question from the bookkeeping question: the new remaining step
is to force one of these modular bucketing witnesses in every large graph, not to prove new collapse
lemmas once such a witness is present.

That recursive version is now explicit too: `HasControlBlockModularCascadeWitnessOfCard` and
`EventualNatPowerControlBlockModularCascadeDomination` package the same dropped-part obstruction
across an entire cascade while keeping one modulus fixed. So the current frontier statement can now
be formulated cleanly either as a modular bucketing forcing theorem or as a modular cascade forcing
theorem, and the unbounded Lean targets now show these two formulations are equivalent.

The new pigeonhole lemmas show that freezing the first two quantities only costs `q^2` buckets,
not the full `2^|T|` neighborhood profile complexity.

## 4. Concrete next target

A strong enough intermediate theorem would be:

> There is a function `u(m) = o(m)` such that every sufficiently large graph contains disjoint
> sets `S, T` with `|S| >= m`, `|T| <= u(m)`, all vertices of `S` having the same degree in
> `G[S ∪ T]`, and all vertices of `S` having the same degree into `T`.

By the control-set lemma this would immediately imply an induced regular subgraph on `m` vertices.

That target is much closer to the conjecture than Ramsey, but it is still concrete enough to try
to formalize incrementally.
