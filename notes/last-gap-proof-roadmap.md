# Last-Gap Proof Roadmap

This note now records the proof plan that led to the closure of the last gap.

## Audit correction

The previous closure claim was too strong.

What remains justified after audit is:

1. the weighted-house route is now locally closed: Proposition `40.7` is repaired, and the
   false-clone shifted twin-breaker reduces back to the same `O_10` endpoint;
2. the prime weighted quotient branch is now locally closed, because the `C_5` seed is also
   eliminated internally from the current notes;
3. the refinement-data exact self-bridge is existential, not same-`w`; however, Section `10` needs a
   genuine compatible size-`q^2` completion `S`, while the formal refinement-data input does not by
   itself furnish such a completion; indeed bare refinement data do not imply it. The exact missing
   finite theorem is an anchored exact-`e` shell host theorem:
   - find `S` with `w ⊆ S ⊆ E_e(t)`, `|S| = q^2`, and all degrees in `G[S]` constant modulo `q`;
   - equivalently, in the shell graph `H := G[E_e(t)]`, find a mod-`q` regular `q^2`-vertex induced
     subgraph containing the anchor `w`;
   - peeling one non-anchor vertex gives an exact anchored mod-`q` near-regular completion theorem on
     `q^2 - 1` vertices inside `H`;
   - more sharply, for a fixed peeled set `T`, raw short packets of size `< q` are exact: a nonempty
     raw zero-packet exists if and only if every vertex in it is already a completer;
   - below that, the exact host-side frontier is simply completer positivity `c(T) > 0`,
     equivalently the existence of a weighted raw relation of total mass `< q`;
   - equivalently again, `c(T) > 0` is exactly the existence of some `U ⊆ O` with
     `e(L(T), U) - e(B(T), U) > (|L(T)| - 1) |U|`;
   - more sharply, if `Phi(U) := e(L(T), U) - e(B(T), U) - (|L(T)| - 1) |U|`, then
     `c(T) = max_{U ⊆ O} Phi(U)`;
   - because `U` is arbitrary, the putative one-error-strip theorem collapses to the **pointwise
     one-error witness** `∃ x in O, epsilon(x) <= 1`;
   - more sharply, one-defect witnesses carry a defect map `d : O_1 -> T`, and any witness with
     `d(x) notin w` swaps into `T` while preserving anchored near-regularity;
   - Hall already collapses pointwise: in the anchor-supported regime `h_T(Y) <= 0` for all
     `Y subseteq w` is equivalent to `mu(u) <= q - 1` on each anchor fiber;
   - so the residual host obstruction is **anchor-supported unique defects** together with a
     **multi-swap / compatibility theorem** for injective defect selections across anchor fibers;
   - the older `S = s ⊔ C` shell-selection/congruence problem is only a stronger sufficient route;
4. prime weighted quotient closure alone would still not finish the host-side theorem, because
   Theorem `17.5` also leaves the small bad-module alternative; Section `22`'s old universal target
   "every regular `A ⊆ M` lifts" is false, already for `K_{m,m,m}`. More sharply, branch-`(1)`
   depends on `A` only through its profile `(a, alpha)`; rewriting by codimension `s := q - a`,
   codimension `4` is already fully classified, and the next exact smaller theorem is
   **overlap-profile resolution** for `q in {9,10,11}` (while the current `q=8` branch collapses to
   an outside `C_4`);
5. the top-level asymptotic route still also needs `HasPolynomialCostEmptyControlDyadicLift`, or at
   least the weaker target family isolated by the dyadic-lift audit:
   - for the bridge exponent `D`, writing `A := D + 1`, it is enough to prove a terminal-exponent
     lift that upgrades a `2^j`-cascade witness of size `(2^j)^C (2^(j+1))^A` to a
     `2^(j+1)`-cascade witness of size `(2^(j+1))^A`;
   - Section `18` shows the fixed-support core is a residual-packet / `eta`-top-bit theorem, not
     naive layerwise divisibility;
   - more sharply, the packet-shadow sum is decomposition-independent and equals `bar eta_m(U)` in
     `M_2(U)`, so the exact theorem is `bar eta_m(U) = 0`;
   - equivalently, the live dyadic theorem is a **pairwise next-bit compensation theorem** on one
     fixed support `U`;
   - in dual/basis form, the exact smaller target is **pair-cut packet parity** for each
     `{u, u_0}`;
   - more sharply, every already-separated block with constant external degree mod `q` on `U` is
     silent for these functionals, so only the final undecomposed tail can contribute;
   - writing `rho_R(u) := |N(u) ∩ R|` for that last tail, the frozen first `m` bits give
     `rho_R = K_m 1_U + 2^m h_m`;
   - thus the exact remaining dyadic theorem is vanishing of the terminal-tail class
     `tau_m(R, U) := [h_m mod 2]`, equivalently one more row-divisibility step
     `rho_R = K_(m+1) 1_U + 2^(m+1) h_(m+1)`;
   - equivalently, the normalized difference cocycle
     `kappa_m(u,v) := (rho_R(u)-rho_R(v))/2^m [MOD 2]` is the coboundary of an aggregate
     complement-orbit class `beta_m`;
   - individual complement-orbit coefficients need not vanish: the exact smaller theorem is
     `beta_m = 0`, equivalently constant incidence parity / symmetric-difference-zero for the active
     complement-orbit family;
   - raw parity pairing on `R` is too weak, because it misses the carry contribution hidden inside
     those aggregate complement-orbit coefficients;
   - the Section `18` obstruction shows that current `m`-bit data alone do not force this, and
     low-rank shadow space by itself is not enough.

So the rest of this note should be read as a roadmap / reduction record, not as a completed proof.

The main point is simple:

- the concrete `q = 4` slice is now genuinely settled;
- the **real global frontier** remains the refinement-data exact self-bridge;
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

One further sharpening is now available inside the first route:

- around every near-regular `(q - 1)`-set, the outside discrepancy sequence automatically contains a
  nonempty zero-sum packet by Davenport;
- for proper near-regular targets `1 <= r <= q - 2`, any zero-sum packet of size strictly less than
  `q / 2` already forces a regular induced `q`-set;
- so after separating off the clique and independent-set endpoints, the real missing lemma is a
  **proper missing-pattern / short-packet forcing theorem**, not just a raw zero-sum identity.
- the strongest direct proof target sharpens this further: choose a minimal nonempty zero-packet and
  prove it must have size `< q / 2` (packet compression).
- within that direct route, the only surviving obstruction with `p < q` is the boundary
  `q / 2`-packet of anti-completers, but the isolated boundary anti-packet lemma is too weak:
  the last move must use global minimality across all proper near-regular sets.
- in that boundary case, the remaining layer `W` is itself a large zero-packet forced to compensate
  the anti-completer block by a fixed residue gap between `A` and `B`, but this does not force a
  short zero-subpacket: `(q/2-1)` anti-completers together with `2` empty-trace vertices already
  realize the same compensation.
- so the new direct target is a **supported seeding route**: the empty-trace vertices alone are too
  weak, and one must use them together with a large outside support set to pass to a different
  proper near-regular set `S'`, not to prove an abstract balancing extraction principle on the
  fixed `S`.
- more sharply, any such support must satisfy a **pointwise compensation law** between every
  surviving `a in A'` and `b in B'`, forcing many genuine `A`-over-`B` separator vertices whenever
  the deleted set is not more `B'`-heavy than `A'`-heavy.
- and now the cyclic part is completely rigid: after subtracting the cyclic contribution and the
  deleted-set bias, the off-cyclic level functions have total oscillation at most `2`, so any
  nonconstant compensation matrix yields a uniform extremal rectangle `A_+ × B_-`.
- one off-cyclic separator lowers the extremal compensation by exactly `1` on its separated
  subrectangle, which resolves `(1,0)`, `(0,1)`, `(2,0)`, and `(0,2)` by descent.
- the mixed `(1,1)` case also collapses by iterating descent to a terminal mixed rectangle and then
  excluding any remaining one-sided traces by the already-settled `(1,0)` / `(0,1)` branches.
- therefore the direct packet-compression / supported-seeding route is now **locally closed**.

Also, all vertex-transitive cases are done: every vertex-transitive graph on `q^2` vertices already
contains a regular induced `q`-set.

That is the shortest proof roadmap I currently trust.

## 10. What the `q = 8` probe actually generalized

The long `q = 8` reduction was not valuable as an end in itself.
Its value is that two of its main structural conclusions generalize cleanly.

### 10.1. Split prime quotients are dead in general

If the weighted prime quotient is split, then it is a spider.
For every even `q`, a spider on total bag weight `q^2` with all bags of size `< q` is already good:

- `q / 2` edge-bearing legs give `(q / 2) K_2`,
- `q / 2` non-clique body bags give `overline{(q / 2) K_2}`,
- avoiding `I_q` and `K_q` bounds the remaining total leg/body weight,
- and the head contributes at most `q - 1`,

so the total weight is forced below `q^2` unless a regular `q`-set already exists.

Thus the split prime quotient branch can be discarded uniformly, not just at `q = 8`.

### 10.2. `C_5` is not a fundamental seed

Assuming the standard theorem that every prime `{P_5, bar P_5}`-free graph is split or `C_5`, the
`C_5` seed also disappears as an independent branch.

The `q = 8` attachment analysis on `C_5` is actually graph-theoretic: every outside vertex is either

- a center,
- an anticenter,
- a true clone,
- a false clone,

or it immediately creates an induced `P_5` or `bar P_5`.

So a larger prime non-split quotient cannot remain genuinely `C_5`-only.

### 10.3. The real general prime-quotient frontier

After these two general reductions, the honest remaining prime-quotient problem is no longer:

- arbitrary prime weighted quotients,
- and not even the three-seed family `C_5`, `P_5`, `bar P_5`.

It is now:

- weighted attachment theorems over `bar P_5`.

Reason:

- `C_5` is eliminated by prime-graph structure;
- `P_5` is equivalent to `bar P_5` by weighted quotient complementation.

That is the main reason not to keep grinding `q = 8` locally.
The right next theorem should be phrased directly at the weighted-house-seed level, and then
connected back to the dropped-part refinement package.

More sharply, the current prime-quotient frontier is now:

1. a **double-reseating local theorem** on the `16` remaining `7`-vertex templates coming from the
   six double-house swap types plus one distinguisher;
2. a **packet-exchange theorem** for a stable house, where the only live symmetric move is the top
   packet `(T_b, T_c)` (equivalently the rim packet `(Q_0, B_b, B_c)`).

That is the exact general local theorem surface left by the `q = 8` probe.

After the overlap-symmetry reduction, the first item improves further:

- the double-reseating theorem is now only a theorem on `12` explicit local `7`-vertex templates.

And after one more direct reseating reduction, this sharpens again to:

- a **3-core self-loop theorem** (corner-2, shoulder-3, roof-edge, all with `epsilon = 1`),
- together with **two off-ramp templates** that already land in the stable exceptional sector.

So the local theorem frontier is now closed.

Reason:

- the old one-fiber same-side theorem and the corner/shoulder twin-bag theorem unify;
- the clone-bag shifted twin-breaker does not create a new infinite descent:
  after one more forced distinguisher it reproduces the exact `O_10` configuration;
- the stable-house side is done: the unique surviving `O_10` continuation forces an arbitrarily
  long half-graph ladder inside one finite fiber, so `O_10` is impossible;
- the old roof oscillation theorem reduces through `T_ε` and `U_1`, but those templates collapse
  back into the old reseating automaton, so they leave no genuinely new branch.

Consequently the weighted-house seed theorem is complete, and with the split / `C_5` / `P_5`
reductions from Section `33`, the general prime-quotient branch is closed.
