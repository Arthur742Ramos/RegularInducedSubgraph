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

## 1.5. Singleton-control collapse on geometric scales

There is now also a clean converse on power scales:

> If `b > 1` and `F(b^k)` eventually dominates every linear function of `k`, then the much
> stronger-looking one-control exact target already follows with a **single control vertex**.

Reason:

1. On a graph with `b^k` vertices, peel off one vertex `t`.
2. Among the remaining `b^k - 1` vertices, one adjacency bucket to `t` has size at least
   `(b^k - 1) / 2`.
3. For `b > 1`, that large bucket contains `b^(k-1)` vertices; the endpoint case `b = 2` is still
   valid because `ceil((2^k - 1) / 2) = 2^(k-1)`.
4. Any regular induced subgraph inside those `b^(k-1)` vertices lifts back to an exact one-control
   witness using the fixed vertex `t`, because the external degree into `t` is already frozen.

This is now formalized in `RegularInducedSubgraph.Modular` as the implication

- `EventualNatPowerDomination b -> EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1)`
  for every `b > 1`,

and hence, again for `b > 1`,

- `EventualNatPowerSingleControlExactDomination b`,
- `EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1)`,
- and the original `EventualNatPowerDomination b`

are all equivalent. In particular, this already holds at base `2`, so the exact one-control route
is no longer a strictly stronger asymptotic target on any geometric scale covered by the threshold
reduction.

Because the bounded exact, bounded bucketing, bounded modular, and bounded modular-bucketing
single-control targets are already equivalent once the control budget is eventually smaller than the
demanded size, the singleton-budget versions of all four of those one-control targets now collapse
to the original power-sequence statement as well (again for every `b > 1`).

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

This exact multiblock packaging is now fully formalized, but it also collapses in the unbounded
story: `HasExactControlBlockWitnessOfCard`, `HasControlBlockBucketingWitnessOfCard`, and
`HasControlBlockCascadeWitnessOfCard` are all equivalent to the simpler one-control exact target
`HasSingleControlExactWitnessOfCard`. The remaining single-control refinements also collapse:
`HasSingleControlBucketingWitnessOfCard` and `HasSingleControlCascadeWitnessOfCard` are equivalent
to that same one-control exact target. So the real issue is no longer which exact package to use,
but how to force any of these equivalent exact witnesses in every large graph.

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
- `inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree` and the derived
  `hasRegularInducedSubgraphOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree` /
  `...externalBlockDegrees` bridges show that one can also collapse modular data to exact
  regularity once the internal degrees are trapped in any interval of width `< q`;
- `inducesModEqDegree_of_modEq_unionDegree_and_externalDegree`
  transports modular equality from ambient degrees in `G[S ∪ T]` and external degrees into `T`
  down to modular equality inside `G[S]`;
- `hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard`
  packages the finite equivalence between modular witnesses and exact regular induced subgraphs;
- `exists_large_mod_pair_of_mul_le_card` and `exists_large_subset_with_constant_mod_pair`
  give the finite pigeonhole step for paired residue data, with only `q^2` buckets;
- `exists_large_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound`
  turns those paired residue buckets into a large subset whose host degrees inside `G[S]` are all
  congruent modulo `q` after tracking the residue of the ambient degree on `G[S ∪ T]` together with
  the residue of the degree into `T`;
- `exists_large_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound`
  extends that same idea to any separated control-block family, paying only one extra factor of `q`
  on top of the `q ^ blocks.length` external-block bucketing cost to recover a large subset whose
  host degrees inside `G[S]` are all congruent modulo `q`;
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

The dropped-part obstruction is also formalized now: the residue-bucketing step naturally produces a
large subset `U ⊆ S` only after throwing away `S \ U`, so one still has to control the dropped-part
residue together with the control-set residue. This is packaged as
`HasSingleControlModularBucketingWitnessOfCard` and the asymptotic targets
`EventualNatPowerSingleControlModularBucketingDomination` /
`EventualNatPowerBoundedSingleControlModularBucketingDomination`. In the unbounded story this
single-control modular-bucketing layer now collapses back to `HasSingleControlModularWitnessOfCard`
itself, while the bounded version remains a useful budget-tracking refinement.

The same obstruction is now packaged at the multiblock level as well:
`HasControlBlockModularBucketingWitnessOfCard` and
`EventualNatPowerControlBlockModularBucketingDomination`, together with bounded versions.

That multiblock modular packaging has now collapsed one step further in the unbounded story:
`HasSingleControlModularWitnessOfCard`,
`HasSingleControlModularBucketingWitnessOfCard`,
`HasNonemptyControlBlockModularWitnessOfCard`,
`HasControlBlockModularBucketingWitnessOfCard`, and
`HasControlBlockModularCascadeWitnessOfCard` are all equivalent, as are their eventual nat-power
targets. So the cleanest current frontier statement is the plain one-control formulation
`EventualNatPowerSingleControlModularDomination`, with the single-control dropped-part, multiblock
control-block, bucketing, and cascade versions available as equivalent repackagings. The older
`HasControlBlockWitnessOfCard` still collapses all the way back to the plain modular witness via the
empty control-block family, so it is no longer the right frontier object.

The remaining step is therefore purely combinatorial: force one of these equivalent genuine modular
objects in every sufficiently large graph, rather than prove new collapse lemmas once such a witness
is present. The new block-level host-degree bucketing theorem means that arbitrary separated control
families can now be handled with only one extra ambient-residue factor, so the next real gap is to
turn that fixed-host forcing into self-consistent dropped-part / witness data.

The new pigeonhole lemmas, now packaged into
`exists_large_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound`, show that
freezing the first two quantities only costs `q^2` buckets, not the full `2^|T|` neighborhood
profile complexity.

## 4. Concrete next target

A strong enough intermediate theorem would be:

> There is a function `u(m) = o(m)` such that every sufficiently large graph contains disjoint
> sets `S, T` with `|S| >= m`, `|T| <= u(m)`, all vertices of `S` having the same degree in
> `G[S ∪ T]`, and all vertices of `S` having the same degree into `T`.

By the control-set lemma this would immediately imply an induced regular subgraph on `m` vertices.

That target is much closer to the conjecture than Ramsey, but it is still concrete enough to try
to formalize incrementally.
