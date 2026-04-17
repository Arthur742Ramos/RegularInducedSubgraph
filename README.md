# RegularInducedSubgraph

This repo is a Lean 4 + mathlib workspace for exploring the statement:

> Let `F(n)` be maximal such that every graph on `n` vertices contains a regular induced subgraph on at least `F(n)` vertices. Show that `F(n) / log n → ∞`.

The goal here is **not** to import literature about this exact problem. Instead, the project sets up the definitions cleanly and organizes a few first-principles proof directions that can be developed formally.

## Current formalization

- `RegularInducedSubgraph.Basic` defines:
  - induced graphs on finite vertex sets,
  - what it means for a finite set of vertices to induce a regular graph,
  - what it means for a graph to contain a regular induced subgraph of size at least `k`,
  - a control-set lemma: if every vertex of `s` has the same degree in `G[s ∪ t]` and the same
    number of neighbors in a disjoint control set `t`, then `G[s]` is regular,
  - a two-block refinement: if the ambient degree on `G[s ∪ t₁ ∪ t₂]` is constant on `s` and the
    degrees into each disjoint control block `t₁`, `t₂` are separately constant on `s`, then
    `G[s]` is regular,
  - a recursive block-family transport package: if the ambient degree on `G[s ∪ ⋃ blocks]` is
    constant on `s` and each separated control block contributes a separately constant external
    degree on `s`, then `G[s]` is regular.
- `RegularInducedSubgraph.Problem` defines:
  - `admissibleBounds n`,
  - the extremal function `F : ℕ → ℕ`,
  - `TargetStatement`, a filter-language version of `F(n) / log n → ∞`,
  - `EventualLogDomination`, a lower-bound formulation that is often easier to prove,
  - the bridge theorems relating `TargetStatement` and `EventualLogDomination`.
- `RegularInducedSubgraph.Ramsey` proves:
  - a finite Ramsey theorem on a prescribed finite vertex set,
  - the uniform lower bound `Nat.log 4 n + 1 ≤ F n` for `n > 0`,
  - the corresponding real-log estimate `(1 / log 4) * log n ≤ F n` for `n > 0`,
  - an eventual asymptotic version: some fixed positive multiple of `log n` is eventually bounded
    by `F n`,
  - equivalently, an eventual positive lower bound on the ratio `F n / log n`.
- `RegularInducedSubgraph.Threshold` adds:
  - monotonicity of `F`,
  - the inverse-scale forcing threshold `forcingThreshold k := sInf {n | k ≤ F n}`,
  - the exact bridge `k ≤ F n ↔ forcingThreshold k ≤ n`,
  - the Ramsey-side upper bound `forcingThreshold (k + 1) ≤ 4^k`,
  - the conjectural inverse formulation `EventualSubexponentialThreshold`.
  - the equivalence between `TargetStatement` and `EventualSubexponentialThreshold`,
  - a geometric-sequence formulation: for any fixed base `b > 1`, the conjecture is equivalent to
    eventual domination of every linear function along `F (b^k)`,
  - a fully discrete version of that reduction: for fixed `b > 1`, it is equivalent to requiring
    that for every `M : ℕ`, eventually `M * k ≤ F (b^k)`.
- `RegularInducedSubgraph.Modular` adds:
  - `InducesModEqDegree G s q`: all degrees in the induced graph `G[s]` are congruent modulo `q`,
  - `HasModularWitnessOfCard G k`: a size-`k` induced subgraph whose degrees are congruent modulo
    some modulus at least its cardinality,
  - a strengthened finite collapse lemma: if the degrees in `G[s]` are all congruent modulo `q`
    and every induced degree is `< q`, then `G[s]` is already regular (hence in particular when
    `|s| ≤ q`),
  - a modular control-set transport lemma: congruence of the ambient degrees in `G[s ∪ t]` and of
    the external degrees into a disjoint control set `t` forces congruence of the internal degrees
    in `G[s]`,
  - a two-block modular refinement: the same transport works from `G[s ∪ t₁ ∪ t₂]` when the
    degrees into each disjoint control block `t₁`, `t₂` are separately constant modulo `q`,
  - a recursive modular block-family transport package: the same idea now iterates over any
    separated list of control blocks with prescribed external residues modulo `q`,
  - `HasControlBlockWitnessOfCard G k`: a packaged finite witness built from a large set `s`, a
    modulus `q ≥ |s|`, and a separated list of control blocks whose ambient and external residue
    data force regularity on `G[s]`,
  - `HasExactControlBlockWitnessOfCard G k` and
    `HasBoundedExactControlBlockWitnessOfCard G k r`: stricter exact control-block witnesses with a
    nonempty control union, optionally using at most `r` control blocks, so the vacuous empty-block
    case is ruled out while still forcing a regular induced subgraph,
  - `HasSingleControlExactWitnessOfCard G k`: the one-control version from the frontier notes, where
    a single nonempty control set `t` freezes both the ambient degree on `G[s ∪ t]` and the degree
    into `t`,
  - `HasBoundedSingleControlExactWitnessOfCard G k r`: the same one-control witness with an explicit
    budget `|t| ≤ r` on the control set size,
  - `HasSingleControlBucketingWitnessOfCard G k` and
    `HasBoundedSingleControlBucketingWitnessOfCard G k r`: a large bucket `u ⊆ s` inside a host set
    with one disjoint nonempty control set `t`, where the ambient degree on
    `G[u ∪ ((s \ u) ∪ t)]`, the degree into the dropped part `s \ u`, and the degree into `t` are
    all frozen on `u`; these finite witnesses collapse to the exact one-control route,
  - `HasSingleControlCascadeWitnessOfCard G k` and
    `HasBoundedSingleControlCascadeWitnessOfCard G k r`: a fixed-control multistage cascade of
    nested buckets whose dropped layers become exact control blocks, collapsing to the existing
    exact control-block witness route,
  - `HasLowDegreeModularWitnessOfCard G k`: a sharper witness notion where the modulus only has to
    exceed the maximum induced degree, together with an equivalence to exact regular witnesses,
  - the exact graph-level equivalence
    `HasModularWitnessOfCard G k ↔ HasRegularInducedSubgraphOfCard G k`,
  - finite pigeonhole lemmas that extract large fibers for residue data in `Fin q` and paired
    residue data in `Fin q × Fin q`,
  - a finite exact degree-bucketing lemma: if the ambient degree on `G[s ∪ t]` is constant on `s`,
    then a pigeonhole over the `|t| + 1` possible degrees into `t` extracts a large subset on which
    the induced degree inside `G[s]` is constant,
  - a two-block refinement of the same idea: if the ambient degree on `G[s ∪ t₁ ∪ t₂]` is constant
    on `s`, then a pigeonhole over the `(|t₁| + 1)(|t₂| + 1)` possible external-degree pairs
    extracts a large subset on which the induced degree inside `G[s]` is constant,
  - an arbitrary separated-block refinement: for a separated control-block list `blocks`, if the
    ambient degree on `G[s ∪ controlBlockUnion blocks]` is constant on `s`, then bucketing by the
    full tuple of external degrees with cost `∏ (|tᵢ| + 1)` extracts a large subset on which the
    induced degree inside `G[s]` is constant,
  - the modular residue-bucketing analogue: if the ambient degrees on
    `G[s ∪ controlBlockUnion blocks]` are constant modulo `q` on `s`, then `q ^ blocks.length`
    residue buckets freeze all control-block residues and extract a large subset on which the host
    degree inside `G[s]` is constant modulo `q`,
  - the power-sequence modular reformulation: for any fixed base `b > 1`, the conjecture is
    equivalent to eventual existence of linearly large modular witnesses inside graphs on `b^k`
    vertices,
  - `EventualNatPowerExactControlBlockDomination b` and
    `EventualNatPowerBoundedExactControlBlockDomination b r`: genuine exact-control asymptotic
    targets whose eventual validity implies `TargetStatement`,
  - `EventualNatPowerSingleControlExactDomination b`: the one-control asymptotic target directly
    matching the frontier-strategy note, also implying `TargetStatement`,
  - `HasSingleControlModularWitnessOfCard G k` and
    `EventualNatPowerSingleControlModularDomination b`: the nonempty one-control modular target from
    the strategy note, sitting between the single-control exact target and the ordinary modular
    witness route and still implying `TargetStatement`,
  - `HasBoundedSingleControlModularWitnessOfCard G k r` and
    `EventualNatPowerBoundedSingleControlModularDomination b u`: the budgeted small-control modular
    version, which now also receives direct bridges from the bounded single-control bucketing route,
  - `HasSingleControlModularBucketingWitnessOfCard G k` and
    `EventualNatPowerSingleControlModularBucketingDomination b`: the dropped-part modular bucketing
    refinement of the small-control modular target, together with the bounded version
    `HasBoundedSingleControlModularBucketingWitnessOfCard G k r` /
    `EventualNatPowerBoundedSingleControlModularBucketingDomination b u`,
  - `EventualNatPowerBoundedSingleControlExactDomination b u`: the budgeted one-control asymptotic
    target, which records an explicit control-size allowance `u k` at scale `k` and still implies
    `TargetStatement`,
  - `EventualNatPowerSingleControlBucketingDomination b` and
    `EventualNatPowerBoundedSingleControlBucketingDomination b u`: asymptotic bucketing targets
    whose eventual validity feeds through the exact one-control bridge and therefore implies
    `TargetStatement`,
  - `HasControlBlockBucketingWitnessOfCard G k` and
    `HasBoundedControlBlockBucketingWitnessOfCard G k r`: multiblock bucketing witnesses that freeze
    one dropped-part degree together with a separated nonempty control-block family and collapse
    directly to exact control-block witnesses; in the unbounded case this is now equivalent to the
    exact and multiblock-cascade formulations, while the bounded version pays one extra control-block
    slot for the dropped part,
  - `HasControlBlockModularBucketingWitnessOfCard G k` and
    `HasBoundedControlBlockModularBucketingWitnessOfCard G k r`: the modular multiblock bucketing
    refinement, which keeps the dropped part as modular residue data, collapses to the modular
    control-block witness route, is equivalent to the modular multiblock cascade formulation in the
    unbounded case, and in the bounded version avoids paying the extra dropped-part slot,
  - `EventualNatPowerControlBlockBucketingDomination b` and
    `EventualNatPowerBoundedControlBlockBucketingDomination b r`: multiblock bucketing targets whose
    eventual validity feeds through the exact control-block route and therefore implies
    `TargetStatement`,
  - `EventualNatPowerControlBlockModularBucketingDomination b` and
    `EventualNatPowerBoundedControlBlockModularBucketingDomination b r`: modular multiblock
    bucketing targets sitting between the exact multiblock bucketing/cascade route and
    `EventualNatPowerControlBlockDomination b`,
  - `EventualNatPowerSingleControlCascadeDomination b` and
    `EventualNatPowerBoundedSingleControlCascadeDomination b r`: asymptotic cascade targets whose
    eventual validity feeds through the exact control-block route and therefore implies
    `TargetStatement`,
  - `HasControlBlockCascadeWitnessOfCard G k` and
    `HasBoundedControlBlockCascadeWitnessOfCard G k r`: fixed-block cascade witnesses that keep a
    separated nonempty control-block family in the background while repeatedly freezing dropped-part
    degrees, then collapse to exact control-block witnesses; in the unbounded case this is again
    equivalent to the exact and multiblock-bucketing formulations,
  - `EventualNatPowerControlBlockCascadeDomination b` and
    `EventualNatPowerBoundedControlBlockCascadeDomination b r`: asymptotic multiblock cascade
    targets whose eventual validity again feeds through the exact control-block route and therefore
    implies `TargetStatement`,
  - `HasControlBlockModularCascadeWitnessOfCard G k` and
    `HasBoundedControlBlockModularCascadeWitnessOfCard G k r`: fixed-modulus multiblock cascade
    witnesses that record dropped-part residues modulo one modulus all the way down the chain and
    collapse to the modular multiblock bucketing layer; in the unbounded story this is an equivalent
    re-packaging of the same modular frontier,
  - `EventualNatPowerControlBlockModularCascadeDomination b` and
    `EventualNatPowerBoundedControlBlockModularCascadeDomination b r`: asymptotic modular multiblock
    cascade targets sitting between the exact cascade route and the modular multiblock bucketing
    route,
  - `EventualNatPowerControlBlockDomination b`: a stronger many-block target on graphs with `b^k`
    vertices, together with a theorem that it implies `TargetStatement`,
  - `EventualNatPowerLowDegreeModularDomination b`: a sharper modular asymptotic target whose
    eventual validity also implies `TargetStatement`.

## Candidate approaches to try

1. **Control-set bucketing + refinement**  
   Partition vertices by their degree into a small control set `t` rather than by full adjacency
   profile. The new lemma in `Basic` shows that once one also freezes the ambient degree on
   `s ∪ t`, exact regularity on `s` follows immediately. This reduces the bookkeeping cost of a
   control set of size `|t|` from `2^|t|` profile buckets to only `|t| + 1` degree buckets.

2. **Iterative pruning toward near-regularity**  
   Start with the whole graph and delete vertices with degree too far from a moving target interval. Track how much mass is lost at each stage. If the interval width shrinks slowly enough, this could leave a large induced subgraph whose degrees are eventually forced to coincide.

3. **Modular lifting**  
   The new `Modular` file shows that, once the modulus reaches the size of the induced vertex set,
   congruence of all induced degrees already collapses to exact regularity. So to prove the
   conjecture it is enough, along a geometric subsequence `b^k`, to find linearly large induced
   subgraphs whose degrees are all congruent modulo some `q ≥ |S|`. The new modular control-set
   lemma reduces this further to freezing two scalar quantities modulo `q`: ambient degree in
   `G[s ∪ t]` and degree into the control set `t`.

4. **Repetition on ambient degree data**  
   Track the pair consisting of
   - degree into a bounded control set, and
   - degree inside the ambient induced graph on the control set plus the current bucket.
   Since the control-set lemma recovers exact regularity from equality of these two scalar
   quantities, one can hope for a multiscale pigeonhole argument that only follows low-complexity
   degree data instead of full neighborhood profiles. The new `Fin q × Fin q` bucketing lemmas in
   `Modular` formalize the basic residue-class extraction step for this program.

5. **Density-increment split**  
   Either a large piece is already close to regular, or there is a structural imbalance that lets us pass to a denser or sparser induced piece while keeping a quantitative lower bound on size. Iterating the increment should eventually terminate in a regular configuration.

## Build

```bash
lake exe cache get
lake build
```

## Suggested next formal steps

1. Attack one of the equivalent discrete targets:
   - inverse form: for every real `a > 1`, eventually
     `forcingThreshold k ≤ ceil(a^k)`,
   - power-sequence form: for every `M : ℕ`, eventually `M * k ≤ F (4^k)`.
2. Formalize one of the non-Ramsey refinement schemes above (degree bucketing, pruning, or
   density increment) to try to beat the logarithmic barrier.
3. Push the new modular reformulation: prove a genuine modulus-lifting theorem that, for large
   graphs on `b^k` vertices, forces an induced subgraph on `≫ k` vertices with all degrees
   congruent modulo some `q ≥ |S|`.
4. Use the new control-set lemma to formalize a multiscale bucketing scheme that tracks degree
   vectors into a bounded collection of control blocks instead of full adjacency profiles, now
   with the modular residue-pair bucketing lemmas available as the base pigeonhole step.
5. Isolate a reusable lemma turning a large near-regular induced subgraph into an exactly regular
   induced subgraph with controlled vertex loss.
