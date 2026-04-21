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
- `RegularInducedSubgraph.Modular` now re-exports a three-file modular development:
  - `RegularInducedSubgraph.Modular.Finite`,
  - `RegularInducedSubgraph.Modular.Cascade`,
  - `RegularInducedSubgraph.Modular.Asymptotic`.
- The modular family adds:
  - `InducesModEqDegree G s q`: all degrees in the induced graph `G[s]` are congruent modulo `q`,
  - `HasModularWitnessOfCard G k`: a size-`k` induced subgraph whose degrees are congruent modulo
    some modulus at least its cardinality,
  - a strengthened finite collapse lemma: if the degrees in `G[s]` are all congruent modulo `q`
    and lie in any interval of width `< q`, then `G[s]` is already regular; in particular this
    applies when every induced degree is `< q`, hence also when `|s| ≤ q`,
  - a modular control-set transport lemma: congruence of the ambient degrees in `G[s ∪ t]` and of
    the external degrees into a disjoint control set `t` forces congruence of the internal degrees
    in `G[s]`,
  - interval-controlled exactness bridges: combining that modular transport with an interval bound on
    the internal degrees of `G[s]` now yields direct exact-regularity corollaries for one-control
    and multiblock modular data,
  - a two-block modular refinement: the same transport works from `G[s ∪ t₁ ∪ t₂]` when the
    degrees into each disjoint control block `t₁`, `t₂` are separately constant modulo `q`,
  - a recursive modular block-family transport package: the same idea now iterates over any
    separated list of control blocks with prescribed external residues modulo `q`,
  - `HasControlBlockWitnessOfCard G k`: a packaged finite witness built from a large set `s`, a
    modulus `q ≥ |s|`, and a separated list of control blocks whose ambient and external residue
    data force regularity on `G[s]`; because the block list may be empty, this is now formally
    equivalent to the ordinary modular witness route and is not a genuine frontier target,
  - `HasExactControlBlockWitnessOfCard G k` and
    `HasBoundedExactControlBlockWitnessOfCard G k r`: stricter exact control-block witnesses with a
    nonempty control union, optionally using at most `r` control blocks, so the vacuous empty-block
    case is ruled out while still forcing a regular induced subgraph; in the unbounded story this
    multiblock exact package is now equivalent to the one-control exact, multiblock bucketing, and
    multiblock cascade formulations,
- `HasSingleControlExactWitnessOfCard G k`: the one-control version from the frontier notes, where
  a single nonempty control set `t` freezes both the ambient degree on `G[s ∪ t]` and the degree
  into `t`; direct constructors now package raw ambient/external degree data into this witness and
  its bounded variant, and this is now also equivalent to the unbounded multiblock exact
  control-block/bucketing/cascade witnesses,
  - `HasBoundedSingleControlExactWitnessOfCard G k r`: the same one-control witness with an explicit
    budget `|t| ≤ r` on the control set size,
  - `HasSingleControlBucketingWitnessOfCard G k` and
    `HasBoundedSingleControlBucketingWitnessOfCard G k r`: a large bucket `u ⊆ s` inside a host set
    with one disjoint nonempty control set `t`, where the ambient degree on
    `G[u ∪ ((s \ u) ∪ t)]`, the degree into the dropped part `s \ u`, and the degree into `t` are
    all frozen on `u`; these witnesses now collapse back to the plain one-control exact route, and
    in the unbounded story the corresponding nat-power targets are equivalent to
    `EventualNatPowerSingleControlExactDomination`,
  - `HasSingleControlCascadeWitnessOfCard G k` and
    `HasBoundedSingleControlCascadeWitnessOfCard G k r`: a fixed-control multistage cascade of
    nested buckets whose dropped layers become exact control blocks; the unbounded single-control
    cascade layer now also collapses back to the plain one-control exact target, while the bounded
    version still feeds through the exact control-block witness route,
  - `HasLowDegreeModularWitnessOfCard G k`: a sharper witness notion where the modulus only has to
    exceed the maximum induced degree, together with an equivalence to exact regular witnesses,
  - the exact graph-level equivalence
    `HasModularWitnessOfCard G k ↔ HasRegularInducedSubgraphOfCard G k`,
  - finite pigeonhole lemmas that extract large fibers for residue data in `Fin q` and paired
    residue data in `Fin q × Fin q`,
  - a finite modular host-degree bucketing lemma: for disjoint `s, t`, if `q^2 k ≤ |s|`, then
    bucketing vertices of `s` by the pair consisting of their degree modulo `q` in `G[s ∪ t]` and
    their degree modulo `q` into `t` yields a subset `u ⊆ s` with `|u| ≥ k` whose degrees inside
    `G[s]` are all congruent modulo `q`,
  - a separated-block modular refinement: if `blocks` is a separated control-block family, then one
    additional ambient-residue bucketing step on top of the `q ^ blocks.length` external-block
    bucketing cost yields a subset `u ⊆ s` of size at least `k` whenever
    `q ^ blocks.length * (q * k) ≤ |s|`, while preserving one ambient residue class together with the
    frozen modular external block data and forcing all degrees inside `G[s]` to be congruent
    modulo `q` on `u`,
  - the strengthened single-control and separated-block forcing lemmas now admit exact-cardinality
    variants: after extracting a large bucket with the preserved host/control data, one can trim to a
    subset of cardinality exactly `k` without losing the frozen external-degree or external-block
    data, the ambient residue class, or the induced host-degree conclusions,
  - these trimmed-bucket statements now also feed a recursive bridge: if `inducedOn G s` already
    contains a regular induced subgraph on `k` vertices, then the inherited exact or modular
    external block data on the smaller subset can be packaged back into ambient exact or modular
    control-block witnesses for `G`,
  - the interval-collapse route now has direct exact targets as well: if the host degrees on `G[s]`
    stay inside a width-`q` interval, the ambient degrees on `G[s ∪ controlBlockUnion blocks]`
    (or `G[s ∪ t]`) are congruent modulo `q`, and the control data is exact rather than merely
    modular, then the same collapse packages straight into exact multiblock or one-control witnesses;
    in particular the canonical `q ≥ |s|` special case now lands directly in those exact witness
    notions,
  - at the dropped-part witness layer, the same interval hypothesis now collapses raw modular
    bucketing data all the way to exact witnesses as soon as the surviving control data is exact:
    modular congruence for the ambient extended union plus the dropped part suffices to recover an
    exact witness on the survivor,
  - a finite exact degree-bucketing lemma: if the ambient degree on `G[s ∪ t]` is constant on `s`,
    then a pigeonhole over the `|t| + 1` possible degrees into `t` extracts a large subset on which
    the induced degree inside `G[s]` is constant,
  - a two-block refinement of the same idea: if the ambient degree on `G[s ∪ t₁ ∪ t₂]` is constant
    on `s`, then a pigeonhole over the `(|t₁| + 1)(|t₂| + 1)` possible external-degree pairs
    extracts a large subset on which the induced degree inside `G[s]` is constant,
  - an arbitrary separated-block refinement: for a separated control-block list `blocks`, if the
    ambient degree on `G[s ∪ controlBlockUnion blocks]` is constant on `s`, then bucketing by the
    full tuple of external degrees with cost `∏ (|tᵢ| + 1)` extracts a large subset while retaining
    the chosen exact external block data and forcing the induced degree inside `G[s]` to be constant,
  - the modular residue-bucketing analogue: if the ambient degrees on
    `G[s ∪ controlBlockUnion blocks]` are constant modulo `q` on `s`, then `q ^ blocks.length`
    residue buckets freeze all control-block residues, retain that modular block data explicitly, and
    extract a large subset on which the host degree inside `G[s]` is constant modulo `q`,
  - the power-sequence modular reformulation: for any fixed base `b > 1`, the conjecture is
    equivalent to eventual existence of linearly large modular witnesses inside graphs on `b^k`
    vertices,
  - `EventualNatPowerExactControlBlockDomination b` and
    `EventualNatPowerBoundedExactControlBlockDomination b r`: genuine exact-control asymptotic
    targets whose eventual validity implies `TargetStatement`,
  - `EventualNatPowerSingleControlExactDomination b`: the one-control asymptotic target directly
    matching the frontier-strategy note; it is now equivalent both to the single-control
    bucketing/cascade refinements and to the unbounded exact control-block, multiblock bucketing,
    and multiblock cascade targets, and still implies `TargetStatement`; moreover, for every
    integer base `b > 1`, it is now also equivalent to the original discrete power-sequence target
    `EventualNatPowerDomination b`,
  - `HasSingleControlModularWitnessOfCard G k` and
    `EventualNatPowerSingleControlModularDomination b`: the nonempty one-control modular target from
    the strategy note; in the unbounded story this is now equivalent both to the single-control
    modular-bucketing refinement and to the genuine multiblock modular control-block, modular
    bucketing, and modular cascade formulations, so it is the simplest canonical modular frontier
    object and still implies `TargetStatement`,
  - `HasBoundedSingleControlModularWitnessOfCard G k r` and
  `EventualNatPowerBoundedSingleControlModularDomination b u`: the budgeted small-control modular
  version, which now also receives direct bridges from the bounded single-control bucketing route;
  moreover, once the control budget is strictly smaller than the demanded bucket size, the modular
  witness collapses back to the bounded exact one because the control residues already determine the
  exact external degrees, and under an eventual `u k < (M + 1)k` hypothesis this makes the bounded
  modular target equivalent to the bounded exact one; in particular, for every base `b > 1`, the
  singleton-budget specialization `u k = 1` is already equivalent to `TargetStatement`,
  - `HasSingleControlModularBucketingWitnessOfCard G k` and
    `EventualNatPowerSingleControlModularBucketingDomination b`: the dropped-part modular bucketing
    refinement of the small-control modular target; unboundedly it now collapses back to the plain
    one-control modular witness, and the fixed-host forcing side now includes direct dropped-part
    bridge lemmas that package preserved host-degree data back into these one-control modular
    bucketing witnesses, together with the bounded version
    `HasBoundedSingleControlModularBucketingWitnessOfCard G k r` /
    `EventualNatPowerBoundedSingleControlModularBucketingDomination b u`; under the same eventual
    small-budget hypothesis, the bounded modular-bucketing target is likewise equivalent to both the
    bounded exact target and the bounded exact-bucketing target,
  - `EventualNatPowerBoundedSingleControlExactDomination b u`: the budgeted one-control asymptotic
    target, which records an explicit control-size allowance `u k` at scale `k` and still implies
    `TargetStatement`; in particular, for every base `b > 1`, the singleton-budget specialization
    `u k = 1` is already equivalent to `EventualNatPowerDomination b`,
  - `EventualNatPowerSingleControlBucketingDomination b` and
  `EventualNatPowerBoundedSingleControlBucketingDomination b u`: asymptotic bucketing targets;
  the unbounded one is equivalent to `EventualNatPowerSingleControlExactDomination`, while the
  bounded one is equivalent to `EventualNatPowerBoundedSingleControlExactDomination`, so both
  still imply `TargetStatement`; again, for every base `b > 1`, the bounded singleton-budget case
  `u k = 1` is already equivalent to `TargetStatement`,
  - `HasControlBlockBucketingWitnessOfCard G k` and
    `HasBoundedControlBlockBucketingWitnessOfCard G k r`: multiblock bucketing witnesses that freeze
    one dropped-part degree together with a separated nonempty control-block family and collapse
    directly to exact control-block witnesses; in the unbounded case this is now equivalent to the
    exact and multiblock-cascade formulations, while the bounded version pays one extra control-block
    slot for the dropped part,
  - `HasNonemptyControlBlockModularWitnessOfCard G k` and
    `HasBoundedNonemptyControlBlockModularWitnessOfCard G k r`: the genuine modular multiblock
    control-block target, requiring a nonempty separated control-block family so the old vacuous
    empty-block case is ruled out; in the unbounded story this is now equivalent to the one-control
    modular, modular bucketing, and modular cascade formulations, and in the bounded story it is
    equivalent to bounded modular multiblock bucketing,
  - `HasControlBlockModularBucketingWitnessOfCard G k` and
    `HasBoundedControlBlockModularBucketingWitnessOfCard G k r`: the one-shot modular multiblock
    bucketing refinement, which keeps the dropped part as modular residue data and is equivalent in
    the unbounded case to the genuine nonempty modular control-block witness and to the modular
    multiblock cascade formulation; in the bounded version it avoids paying the extra dropped-part
    slot,
  - `EventualNatPowerControlBlockBucketingDomination b` and
    `EventualNatPowerBoundedControlBlockBucketingDomination b r`: multiblock bucketing targets whose
    eventual validity feeds through the exact control-block route and therefore implies
    `TargetStatement`,
  - `EventualNatPowerNonemptyControlBlockModularDomination b` and
    `EventualNatPowerBoundedNonemptyControlBlockModularDomination b r`: the asymptotic genuine
    modular control-block targets; in the unbounded story they are now equivalent to the
    single-control modular, modular bucketing, and modular cascade targets, while in the bounded
    story they are equivalent to the bounded modular multiblock bucketing targets below; in
    particular their eventual validity implies `TargetStatement`,
  - `EventualNatPowerControlBlockModularBucketingDomination b` and
    `EventualNatPowerBoundedControlBlockModularBucketingDomination b r`: modular multiblock
    bucketing targets equivalent to the genuine nonempty modular control-block targets, presented in
    one-shot dropped-part form,
  - `EventualNatPowerSingleControlCascadeDomination b` and
    `EventualNatPowerBoundedSingleControlCascadeDomination b r`: asymptotic cascade targets; the
    unbounded one is equivalent to `EventualNatPowerSingleControlExactDomination`, while the bounded
    one still feeds through the exact control-block route and therefore implies `TargetStatement`,
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
    cascade targets; in the unbounded story these are equivalent to the genuine nonempty modular
    control-block and modular bucketing targets,
  - `EventualNatPowerControlBlockDomination b`: the older many-block modular target on graphs with
    `b^k` vertices; it still implies `TargetStatement`, but it allows empty control-block families
    and is now formally equivalent to the ordinary modular asymptotic route, so it is no longer the
    canonical frontier object,
  - `EventualNatPowerLowDegreeModularDomination b`: a sharper modular asymptotic target whose
    eventual validity also implies `TargetStatement`.

## Repository map

If you want a quick way into the artifact, the following declarations are the best entry points:

- `RegularInducedSubgraph.Problem.targetStatement_iff_eventualLogDomination`  
  Base equivalence between the main asymptotic statement and an eventual logarithmic lower bound.
- `RegularInducedSubgraph.Threshold.eventualNatPowerDomination_iff_targetStatement`  
  Geometric-scale reduction: the conjecture is equivalent to eventual domination along `F (b^k)`.
- `RegularInducedSubgraph.Ramsey.exists_pos_eventual_log_lower_bound`  
  Formal Ramsey-side baseline showing that `F n` is eventually bounded below by a positive multiple
  of `log n`.
- `RegularInducedSubgraph.inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree`  
  The core control-set transport lemma from `Basic`.
- `RegularInducedSubgraph.hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard`  
  Finite bridge between modular witnesses and ordinary exact regular induced subgraphs.
- `RegularInducedSubgraph.eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_one_lt`  
  Main singleton-control exact collapse theorem.
- `RegularInducedSubgraph.eventualNatPowerBoundedSingleControlModularDomination_one_iff_targetStatement_of_one_lt`  
  Main bounded singleton-budget modular collapse theorem.
- `RegularInducedSubgraph.hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_two_of_pos`  
  First unconditional base theorem in the composable fixed-modulus host package: every nonempty
  `n`-vertex graph already has a modulus-`2` one-control host witness on `⌊(n - 1) / 4⌋` vertices.
- `RegularInducedSubgraph.hasFixedModulusWitnessOfCard_two`  
  Gallai's parity base case in empty-control fixed-modulus form: every finite graph has an induced
  subgraph on at least `⌊n / 2⌋` vertices whose induced degrees are all congruent modulo `2`
  (equivalently, all even), with the stronger half-size partition statement exposed as
  `RegularInducedSubgraph.exists_large_even_induced_subgraph`.
- `RegularInducedSubgraph.hasFixedModulusCascadeWitnessOfCard_two`  
  The same Gallai theorem repackaged in the empty-control fixed-modulus cascade language
  `HasFixedModulusCascadeWitnessOfCard`, together with the asymptotic bookkeeping proposition
  `RegularInducedSubgraph.emptyControlDyadicParityBaseCase`.
- `RegularInducedSubgraph.not_dyadicParityBaseCase`  
  Formal obstruction showing that the naive terminal-capped parity base case is actually false:
  the terminal bucket in `HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q` always has
  size at most `q`, so the modulus-`2` version cannot force `n / 2` vertices.
- `RegularInducedSubgraph.targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge`  
  Corrected dyadic reduction: the true empty-control parity base case, together with a
  polynomial-cost empty-control dyadic lift and a polynomial-cost bridge into the terminal-capped
  control-block modular cascade package, already implies `TargetStatement`.
- `RegularInducedSubgraph.hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization`  
  Finite host-iteration reduction: if terminal-size bounded fixed-modulus control-block modular host
  witnesses already regularize on `q = 2^j` vertices, then the older one-control host bottleneck,
  and hence the fixed-witness terminal regularization step, follows one exponent later.
- `RegularInducedSubgraph.targetStatement_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one`  
  Stronger shortcut: a budget-`1` terminal bounded-host collapse already forces `TargetStatement`
  directly, via the cubic forcing-threshold bound
  `RegularInducedSubgraph.forcingThreshold_pow_two_le_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one`.
- `RegularInducedSubgraph.hasPolynomialCostFixedOneControlHostTerminalRegularization_iff_hasPolynomialCostFixedSingleControlHostTerminalRegularization`  
  The remaining one-control host bottleneck can now be stated with one explicit control set, rather
  than a bounded control-block host witness of budget `1`; the zero-cost case is exposed by
  `RegularInducedSubgraph.targetStatement_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero`.
- `RegularInducedSubgraph.hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization`  
  The zero-cost single-control host bottleneck reduces further to the exact-cardinality case
  `|u| = q`, exposed by
  `RegularInducedSubgraph.targetStatement_of_hasExactCardFixedSingleControlHostTerminalRegularization`.

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
   `G[s ∪ t]` and degree into the control set `t`. The current Lean-facing composable package for
   this bookkeeping is `HasFixedModulusControlBlockModularHostWitnessOfCard`.

4. **Repetition on ambient degree data**  
   Track the pair consisting of
   - degree into a bounded control set, and
   - degree inside the ambient induced graph on the control set plus the current bucket.
   Since the control-set lemma recovers exact regularity from equality of these two scalar
   quantities, one can hope for a multiscale pigeonhole argument that only follows low-complexity
   degree data instead of full neighborhood profiles. The new `Fin q × Fin q` bucketing lemmas in
   `Modular`, culminating in
   `exists_large_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound`, and its
   separated-block extension
   `exists_large_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound`,
   formalize the basic residue-class extraction step for this program.

5. **Density-increment split**  
   Either a large piece is already close to regular, or there is a structural imbalance that lets us pass to a denser or sparser induced piece while keeping a quantitative lower bound on size. Iterating the increment should eventually terminate in a regular configuration.

## Build

```bash
lake exe cache get
lake build
```

On the reviewed snapshot, this build succeeds but emits linter warnings, most visibly:

- unused section-variable / unused typeclass warnings in `RegularInducedSubgraph.Basic`,
- unused `simp` argument warnings in `RegularInducedSubgraph.Modular.Finite`.

These warnings are expected and do not prevent a successful build. On the current
snapshot they are concentrated in `RegularInducedSubgraph.Basic` (unused
section-variable / unused typeclass warnings) and
`RegularInducedSubgraph.Modular.Finite` (unused `simp` arguments).

The current toolchain is pinned in `lean-toolchain` as `leanprover/lean4:v4.30.0-rc1`. In the
review environment used for the accompanying paper draft, `elan` did not yet expose a tagged
`v4.30.0` stable release: `elan toolchain install leanprover/lean4:v4.30.0` currently reports
`error: no such release: 'v4.30.0'`. A backport attempt to `v4.29.1` failed in upstream
dependencies (`Batteries`, `mathlib`, `ProofWidgets`) before reaching this repository's own source
files.

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
6. Try the dyadic modulus-lifting program in [notes/dyadic-lift-program.md](notes/dyadic-lift-program.md):
   prove a polynomial-cost lift from modulus `2^j` to `2^(j+1)` in a composable fixed-modulus
   modular bucketing/cascade package. The current repo now contains both the empty-control packages
   `HasFixedModulusWitnessOfCard` and `HasFixedModulusCascadeWitnessOfCard`, with Gallai's
   modulus-`2` base theorems `RegularInducedSubgraph.hasFixedModulusWitnessOfCard_two` and
   `RegularInducedSubgraph.hasFixedModulusCascadeWitnessOfCard_two`, and the host-level package
   `HasFixedModulusControlBlockModularHostWitnessOfCard` with the weaker one-control base theorem
   `RegularInducedSubgraph.hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_two_of_pos`
   on about `n / 4` vertices. The new host-step / host-iteration lemmas reduce the old one-control
   host bottleneck to the terminal-size bounded-host hypothesis
   `HasBoundedFixedModulusControlBlockModularHostTerminalRegularization`, formalized by
   `RegularInducedSubgraph.hasPolynomialCostFixedOneControlHostTerminalRegularization_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization`
   and
   `RegularInducedSubgraph.hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization`.
   The same bottleneck is now equivalently packaged as
   `HasPolynomialCostFixedSingleControlHostTerminalRegularization`, which makes the open finite
   problem visibly about one host set, one bucket, and one explicit control set; the monotonicity
   theorem `RegularInducedSubgraph.hasPolynomialCostFixedSingleControlHostTerminalRegularization_of_zero`
   reduces all larger exponents to the literal terminal case `D = 0`, and
   `RegularInducedSubgraph.hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization`
   reduces that terminal case further to exact-cardinality buckets `|u| = 2^j`.
   A successful lift together with that terminal bounded-host collapse would yield
   `forcingThreshold (2^r) ≤ 2 ^ (O(r^2))`, hence `TargetStatement`.
   Even better, if the terminal bounded-host collapse can be proved already with budget `1`, then
   the direct cubic bound
   `RegularInducedSubgraph.forcingThreshold_pow_two_le_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one`
   yields `RegularInducedSubgraph.targetStatement_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one`
   without any dyadic lift.
   The corrected conditional reduction is now formalized by
   `RegularInducedSubgraph.forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge`
   and
   `RegularInducedSubgraph.targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge`.
   The old terminal-capped base case is now ruled out formally by
   `RegularInducedSubgraph.not_dyadicParityBaseCase`; what remains open is the actual empty-control
   dyadic lift theorem together with either that terminal bounded-host collapse or a polynomial-cost
   bridge from the empty-control fixed-modulus cascade package into the terminal-capped control-block
   modular cascade world (or an equivalent empty-control dropped-part reformulation of that world).
