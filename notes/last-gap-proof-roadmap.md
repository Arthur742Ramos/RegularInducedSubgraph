# Last-Gap Proof Roadmap

This note records the proof plan that currently looks most credible without further search,
reflection hacks, or new wrapper theorems.

The main point is simple:

- the concrete `q = 4` slice is now genuinely settled;
- the **real global frontier** is still the refinement-data exact self-bridge;
- the wrong target is the stripped residue-host upgrade, because that interface is already known to
  be false.

## 1. What the code already reduces the problem to

The current library already has the following finite pipeline.

1. From a bounded host witness at bucket `q * q`, `Cascade.lean` produces the refinement package
   `HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard`.
2. `Finite.lean` already proves the one-way implication
   `hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard`.
3. `Finite.lean` also already proves that drop-data are enough:
   `hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard`.
4. `Asymptotic.lean` packages these implications into the abstract targets
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge`,
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge`, and
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

So the honest finite theorem surface is already visible:

> start from the `q * q -> q` refinement output and collapse it directly to an exact single-control
> witness of size `q`.

This is the right target. We do not need more asymptotic repackaging.

## 2. The supporting algebra that matters

Fix `u ⊆ s`, and let `B` denote the separated control-block union. For a vertex `v ∈ u`, write

- `drop(v) := |N(v) ∩ (s \ u)|`,
- `ext(v) := |N(v) ∩ B|`.

Then the degree decompositions are

- `deg_G[s](v) = deg_G[u](v) + drop(v)`,
- `deg_G[u ∪ B](v) = deg_G[u](v) + ext(v)`,
- `deg_G[s ∪ B](v) = deg_G[s](v) + ext(v)`.

This is exactly why the private lemma
`modEq_dropDegree_and_extendedUnionDegree_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees`
goes through:

- host congruence on `G[s]`,
- small-ambient congruence on `G[u ∪ B]`,
- blockwise external congruence into `B`,

together imply

- congruence of `drop(v)` modulo `q`,
- and congruence in the larger ambient graph `G[s ∪ B]`.

The important negative conclusion is that this argument is **one-way**.  
Trying to invert it from the packaged data is the wrong move: the uncontrolled term is still the
contribution of `s \ u`, and nothing in the current stripped data lets us recover it for free.

This is the conceptual reason not to keep attacking the proof by “reconstructing the missing
residue package” after the fact.

## 3. Why the residue-host route is the wrong theorem target

The current evidence already prunes three tempting but false directions.

1. The budget-`1` terminal route is false at `q = 8`.
2. The zero-cost external-block bridge is false already at `q = 2`.
3. The strongest stripped residue-host upgrade is false already at `q = 4`.

The third point is the decisive one for the present gap. The statement to avoid is any theorem that
demands a same-shape residue-host witness as an intermediate object. The local `q - 1` control
structure can still be sufficient to force an exact witness, but it should not be expected to
upgrade to a full residue-host package first.

So the remaining theorem should be phrased directly at the level of

- the exact-card host bucket,
- the maximal control block of size `q - 1`,
- the surrounding refinement data,
- and the final exact single-control witness.

That is why the right frontier remains
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

## 4. The settled `q = 4` slice

Dyson-McKay now record `N_4 = 8`, so every graph on at least `8` vertices contains a regular induced
subgraph on `4` vertices. Since the dyadic host size is `q^2 = 16`, the `q = 4` instance of the pure
selection theorem is automatic.

So the split-graph argument below is no longer needed to justify the frontier, but it is still a
useful self-contained internal proof of the same fact.

The cleanest remaining finite theorem is therefore no longer “finish `q = 4`”, but rather “start at
`q = 8` with the corrected global formulation”.

For reference, the old `q = 4` slice was:

- `four_mem_admissibleBounds_seven`,
- `four_le_F_seven`,
- `four_le_F_of_seven_le`,
- `hasBoundedSingleControlExactWitnessOfCard_four_of_sixteen_le_card`,
- `hasBoundedFixedModulusControlBlockModularHostStepExactSelfBridge_four`.

The supporting mathematics is short and robust.

### Human proof of `4 ∈ admissibleBounds 7`

Take any graph `G` on `7` vertices.

If `G` contains any of the following induced subgraphs, we are done immediately:

- an induced `2K₂`, which is `1`-regular on `4` vertices;
- an induced `C₄`, which is `2`-regular on `4` vertices;
- an induced `C₅`, which is `2`-regular on `5` vertices.

Otherwise `G` is `{2K₂, C₄, C₅}`-free. By the Földes-Hammer characterization, `G` is a split graph.
So `V(G)` decomposes as

- a clique `K`,
- and an independent set `I`,

with `|K| + |I| = 7`. One of these two parts has size at least `4`. Therefore `G` has either

- a clique on at least `4` vertices, or
- an independent set on at least `4` vertices.

Either way, `G` contains a regular induced subgraph on at least `4` vertices.

So `4 ∈ admissibleBounds 7`.

### Why this milestone was worth isolating

This one theorem isolates the first nontrivial dyadic bucket:

- every bounded host witness at `(q, q * q) = (4, 16)` collapses to the exact single-control witness
  needed downstream.

It is a real theorem, it uses the current machinery rather than bypassing it, and it does not depend
on any conjectural global bridge.

In other words: this remains a good sanity-check proof, but it is no longer the live frontier.

## 5. The real global gap, stated correctly

After the `q = 4` slice, the actual remaining theorem should be attacked in the following form:

> From the existing `q * q -> q` refinement-data package, produce a bounded exact single-control
> witness of size `q` directly, without first upgrading to a same-shape residue-host witness.

Concretely, the proof should stay as close as possible to the data already produced by
`hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard`.

That package already gives, on a host bucket `w` of exact size `q`,

- an ambient set `s` with `w ⊆ s`,
- a control block `t` with `|t| = q - 1`,
- exact control degree into `t`,
- modular host-degree constancy on `G[s]`,
- modular degree constancy in the small ambient graph,
- and blockwise external residue data.

The global proof should use this data directly.

## 6. The key mathematical reformulation

For a set `u` of size `q`, every induced degree in `G[u]` lies in `{0, 1, ..., q - 1}`. Hence:

> if the induced degrees in `G[u]` are all congruent modulo `q`, then they are actually equal.

So the exact witness problem reduces to a modular one:

> find a size-`q` set on which the induced degrees are constant modulo `q`.

Inside the current refinement package, this means that the real finite selection problem is to
equalize the missing dropped-part term, not to reconstruct a larger witness class.

At the level of formulas, if `u ⊆ s`, then

- `deg_G[u](v) ≡ deg_G[s](v) - drop(v) [MOD q]`.

Since host degrees are already controlled modulo `q`, exact regularity on `u` will follow as soon as
the dropped-part residues are controlled modulo `q` on `u`.

That is the right local goal.

## 7. Roadmap for the actual last-gap proof

### Phase A. Freeze the target at the refinement-data level

Do not aim first at a new asymptotic statement.  
Do not aim first at a new residue-host upgrade.  
State and prove one finite theorem directly over the exact-card refinement package.

The proof object should consume the same data that `Cascade.lean` already produces. This keeps the
critical path short and avoids new wrapper code.

### Phase B. Prove a local selection lemma on the exact host bucket

The right local statement is not “upgrade to a residue-host witness”. It is something morally of the
form:

> from the maximal-control refinement data on a size-`q` host bucket, extract a size-`q` subset on
> which the dropped-part degree is constant modulo `q`, or directly extract exact regularity.

This is weaker than the false residue-host upgrade and is all the downstream exact theorem needs.

Two mathematically faithful routes now stand out for this local step:

1. a completion/discrepancy argument on near-regular `(q - 1)`-sets;
2. a fixed-`u` dyadic lifting argument via the half-obstructions `eta_m(u)`.

By contrast, naive balanced halving should be treated only as a strong sufficient detour, not as the
core formulation of the open problem.

### Phase C. Use maximal control size `q - 1` aggressively

The fact that the control block has exact size `q - 1` is special and should be treated as a proof
tool, not as bookkeeping noise.

Why it matters:

- exact control degree into `t` removes one whole source of fluctuation;
- on a size-`q` bucket, “constant modulo `q`” immediately upgrades to “constant exactly”;
- the only remaining obstruction is the tail `s \ w`, so the proof should isolate and attack that
  term directly.

This is the place where the current false residue route was too ambitious: it tried to package the
tail information into a stronger witness class instead of using it only to prove exact regularity.

### Phase D. Only then push back into the existing exact bridge

Once the local selection lemma is proved, the rest is already in the library:

- convert the resulting refinement statement to the exact single-control witness using the existing
  finite bridge;
- feed that into the positive-dyadic step-exact self-bridge;
- then let the existing asymptotic wrappers carry the rest.

This is why the real mathematical effort belongs in one finite theorem, not in more asymptotic
plumbing.

## 8. What I would not spend time on next

- No more finite brute-force reflection for the global theorem.
- No attempt to invert the existing small-ambient-to-drop implication.
- No effort to revive the stripped residue-host upgrade.
- No new wrapper theorems unless they expose genuinely new finite data.

## 9. Bottom line

The `q = 4` slice is already settled, so the first genuinely new case is `q = 8`.

If the goal is the real final global gap, attack exactly one theorem:

- the refinement-data exact self-bridge at positive dyadic modulus,

and attack it **directly at the exact-card refinement level**, using the maximal `q - 1` control
block and the dropped-part degree as the central local object.

The two routes worth preserving at that finite level are:

1. completion/discrepancy on near-regular `(q - 1)`-sets;
2. fixed-`u` dyadic lifting through the classes `eta_m(u)`.

That is the shortest proof roadmap I currently trust.
