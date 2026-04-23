# Remaining Gap: The Obstruction Module

This note pushes the last-gap analysis one more step.

The main point is that the remaining theorem is not really about a literal pairing tree of binary
columns. The right object is the **obstruction class** of the internal tail in the quotient module

- `M_q(w) := (Z / qZ)^w / <1_w>`.

Vanishing of that class is exactly equivalent to same-bucket exactness.

This also exposes an important issue with the current dyadic-pairing surface in the code: as
presently defined, it is degenerate and only applies to the trivial tail case.

Throughout:

- `q = 2^j` with `j > 0`,
- `w = {v₁, ..., v_q}`,
- `R := s \ w`,
- for each `x ∈ R`, `c_x ∈ {0,1}^w` is the binary column of the adjacency of `x` to `w`.

Let

- `r := Σ_{x ∈ R} c_x ∈ N^w`,

so `r(v)` is the dropped-part degree of `v ∈ w` into `R`.

By the previous notes, the current bucket `w` is already an exact witness iff `r` is constant
modulo `q`.

## 1. The exact obstruction class

Work in the quotient module

- `M_q(w) := (Z / qZ)^w / <1_w>`,

where `1_w` is the all-ones vector on `w`.

Write `[u]` for the class of `u ∈ (Z / qZ)^w` in `M_q(w)`.

### Definition

The **tail obstruction class** of `R` on `w` is

- `Ω_R(w) := Σ_{x ∈ R} [c_x] ∈ M_q(w)`.

### Proposition 1.1

The following are equivalent:

1. `Ω_R(w) = 0` in `M_q(w)`;
2. the dropped-part degree vector `r` is constant modulo `q` on `w`;
3. `G[w]` is regular;
4. the current bucket `w` together with the current exact control block `t` is already a bounded
   exact single-control witness.

### Proof

By definition,

- `Ω_R(w) = Σ_{x ∈ R} [c_x] = [Σ_{x ∈ R} c_x] = [r]`.

So `Ω_R(w) = 0` iff `r` is a multiple of `1_w` in `(Z / qZ)^w`, i.e. iff the values `r(v)` are
all congruent modulo `q`.

By the previous memo, constancy modulo `q` of `r(v)` on `w` is equivalent to regularity of `G[w]`,
and regularity of `G[w]` is equivalent to same-bucket exactness with the current control block
`t`.

So all four conditions are equivalent.

### Corollary 1.2

Let

- `a(v) := deg_{G[w]}(v)`.

Then in `M_q(w)` one has

- `Ω_R(w) = -[a]`.

### Proof

The host-degree congruence on `w` says that for some residue class `H mod q`,

- `a(v) + r(v) ≡ H [MOD q]`

for all `v ∈ w`.

Passing to the quotient by the constant vector gives

- `[a] + [r] = 0`.

Since `[r] = Ω_R(w)`, the claim follows.

So the dropped-part obstruction is literally the internal irregularity class of `G[w]`.

## 2. Why the current pairing-tree surface is not the right theorem

The code currently defines:

- `DyadicPairCompression`: an equal pair compresses to itself, and a complementary pair compresses
  to the zero column;
- `DyadicPairingStep cols next`: the list `cols` is partitioned into pairs, each producing one
  compressed column in `next`;
- `HasDyadicPairingTree 0 []`;
- `HasDyadicPairingTree (m + 1) cols` if there exists `next` with
  `DyadicPairingStep cols next` and `HasDyadicPairingTree m next`.

### Proposition 2.1

For every depth `m`, the only list satisfying `HasDyadicPairingTree m cols` is `cols = []`.

### Proof

Induct on `m`.

If `m = 0`, this is exactly the base constructor.

Now suppose `HasDyadicPairingTree (m + 1) cols`. Then there exists `next` such that

- `DyadicPairingStep cols next`,
- `HasDyadicPairingTree m next`.

By induction, `next = []`.

But the only way `DyadicPairingStep cols []` can hold is the `nil` constructor, so `cols = []`.

This proves the claim.

### Consequence 2.2

In the present code, the theorem surface

- `HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard`

forces `cols = []`, hence forces

- `binaryColumnRowSum cols v = 0`

for every `v ∈ w`, i.e. it forces the dropped part `R = s \ w` to be anticomplete to `w`.

So that current pairing surface is much stronger than the intended dyadic obstruction and cannot be
the honest final theorem interface.

## 3. Even the intended equal/complementary pairing is too strong

Suppose one corrects the terminal condition and only asks for repeated equal/complementary pairings
through `j` levels without requiring the final compressed list to be empty.

That is still stronger than the actual modulo-`2^j` obstruction.

### Example 3.1

Take `q = 4` and the four columns

- `1000`,
- `0100`,
- `1100`,
- `0000`.

Their row-sum vector is

- `(2, 2, 0, 0)`,

which is constant modulo `2`.

So these columns already satisfy the first dyadic congruence bit.

But there is no equal pair and no complementary pair among them:

- all four columns are distinct;
- the complement of each column is absent from the list.

So parity-constancy of the row sums does **not** imply the existence of a first-level
equal/complementary pairing.

This shows that literal pairing is not the right first-bit theorem. The true level-`1` object is a
more general zero-sum relation in the quotient module.

## 4. The correct first-bit object: zero-sum packets in `M_q(w) / 2 M_q(w)`

Reduce the obstruction module modulo `2`:

- `M̄(w) := M_q(w) / 2 M_q(w)`.

Since `q = 2^j`, this is naturally an `F₂`-vector space.

Each tail column `c_x` determines a class

- `ĉ_x ∈ M̄(w)`.

### Definition

A finite multiset `P` of tail columns is a **binary zero-sum packet** if

- `Σ_{c ∈ P} ĉ = 0`

in `M̄(w)`.

Equal pairs and complementary pairs are special cases:

- if `a = b`, then `ĉ_a + ĉ_b = 2 ĉ_a = 0` in `M̄(w)`;
- if `b = 1 - a`, then `ĉ_b = -ĉ_a = ĉ_a` in characteristic `2`, so again `ĉ_a + ĉ_b = 0`.

But Example 3.1 shows that there are larger zero-sum packets that do not split into such pairs.

### Lemma 4.1

If the tail multiset `R` can be partitioned into binary zero-sum packets `P₁, ..., P_m`, then

- `Ω_R(w) ∈ 2 M_q(w)`.

### Proof

For each packet `P_i`, the packet sum vanishes in `M̄(w)`, so in `M_q(w)` it is divisible by `2`:

- `Σ_{c ∈ P_i} [c] = 2 η_i`

for some `η_i ∈ M_q(w)`.

Summing over the packet partition gives

- `Ω_R(w) = Σ_i Σ_{c ∈ P_i} [c] = 2 Σ_i η_i`.

So `Ω_R(w)` lies in `2 M_q(w)`.

This is the correct first dyadic divisibility step.

## 5. The correct dyadic induction

Because `q = 2^j`, the module `M_q(w)` is annihilated by `2^j`:

- `2^j M_q(w) = 0`.

So to prove exactness it is enough to prove that `Ω_R(w)` is divisible by `2^j`.

### Proposition 5.1

Assume one can construct classes

- `Ω₀, Ω₁, ..., Ω_j ∈ M_q(w)`

such that

- `Ω₀ = Ω_R(w)`,
- `Ω_m = 2 Ω_{m+1}` for every `m = 0, ..., j - 1`.

Then `Ω_R(w) = 0`, hence `w` is already exact.

### Proof

Iterating the identities gives

- `Ω_R(w) = 2^j Ω_j`.

But `2^j M_q(w) = 0`, so `Ω_R(w) = 0`.

By Proposition 1.1, that is exactly the desired exactness.

### Interpretation

The true dyadic proof problem is therefore:

> show the tail obstruction class is successively divisible by `2`, `4`, ..., `2^j`.

At the first bit, one needs binary zero-sum packets in `M̄(w)`.
At later bits, one needs the same divisibility statement for the resulting half-obstruction.

So the right induction lives in the quotient module `M_q(w)`, not in literal equal/complementary
pairs of columns.

## 6. The exact remaining theorem, now stated correctly

The previous notes already proved:

- the external blocks outside `s` are not the problem;
- the exact control block `t` is not the problem;
- the entire remaining obstruction is the internal tail `R = s \ w`.

This note sharpens that one more time:

> the exact self-bridge is equivalent to the vanishing of the internal tail class
> `Ω_R(w) ∈ M_q(w)`.

So the final finite theorem to prove is:

### Internal Tail Obstruction-Zero Theorem

In the current positive-dyadic refinement-data package, the tail obstruction class

- `Ω_{s \ w}(w) ∈ M_q(w)`

vanishes.

Equivalently, the internal tail contribution to the current bucket is constant modulo `q`.

Equivalently, `G[w]` is regular.

Equivalently, the current bucket `w` is already an exact single-control witness.

## 7. What this changes strategically

This note rules out two misleading formulations of the last gap.

First, the present code-level pairing tree is not the right frontier: it collapses to the empty-list
case.

Second, even the intended “equal/complementary pairing” theorem is still stronger than the actual
obstruction: modulo-`2` constancy already allows genuine higher-arity zero-sum packets in the
quotient module.

So the honest remaining proof problem is not

- “pair the tail columns into equal/complementary pairs”,

but rather

- “prove that the total tail class vanishes in the obstruction module, perhaps by a `2`-adic
  zero-sum packet induction.”

That is the mathematically correct kernel of the final gap.

## 8. The natural degree-into-`t` partition is not enough

The current `q * q -> q` host-step first creates the maximal exact control block `t` of size

- `|t| = q - 1`,

and then chooses the final bucket `w` by exact degree into `t`.

So the most obvious remaining partition of the internal tail `R := s \ w` is

- `R = ⊔_{d = 0}^{q - 1} R_d`,

where

- `R_d := {x ∈ R : |N(x) ∩ t| = d}`.

This is the strongest partition one gets for free from the exact control block alone.

### Proposition 8.1

Assume the current refinement-data package.  
If for every `d = 0, ..., q - 1` and all `v, v' ∈ w` one has

- `|N(v) ∩ R_d| ≡ |N(v') ∩ R_d| [MOD q]`,

then the current bucket `w` is already exact.

### Proof

The nonempty classes among the `R_d` form a partition of `R` into proof-blocks whose contributions are
constant modulo `q` on `w`.

So the Internal Tail Block Theorem from the proof-attack note applies directly, giving constancy of
the total dropped-part degree modulo `q` on `w`. By Proposition 1.1 above, that is equivalent to
vanishing of `Ω_R(w)`, regularity of `G[w]`, and same-bucket exactness.

So the degree classes would be enough **if** they were already residue-controlled on `w`.

### Theorem 8.2 (degree-class no-go)

Let `q = 2^j` with `j >= 2`.
Then there exist two graphs `G_good` and `G_bad` on the same disjoint vertex sets

- `w = {v₀, ..., v_{q-1}}`,
- `t = {u₁, ..., u_{q-1}}`,
- `R = {x₁, ..., x_{q-1}}`,

such that, writing `s := w ⊔ R`:

1. `|w| = q` and `|t| = q - 1`;
2. every vertex of `w ∪ R` has degree `0` into `t`, so in both graphs:
   - `w` is a bucket of exact degree `0` into `t`,
   - the natural partition by degree into `t` is the same single class `R_0 = R`;
3. the host degrees on `G[s]` are exactly `q` on all vertices of `w` in both graphs;
4. in `G_good`, the dropped-part degree vector on `w` is constant, so `Ω_R(w) = 0` and `G_good[w]`
   is regular;
5. in `G_bad`, the dropped-part degree vector on `w` is not constant modulo `q`, so `Ω_R(w) != 0`
   and `G_bad[w]` is not regular.

### Proof

Put no edges at all between `t` and `w ∪ R`. Then condition `2` will hold automatically.

For `G_good`:

- let `G_good[w]` be a perfect matching on `w` (possible because `q` is even);
- join every vertex of `R` to every vertex of `w`.

Then every vertex of `w` has internal degree

- `a_good(v) = 1`,

and dropped-part degree

- `r_good(v) = q - 1`.

So every vertex of `w` has host degree

- `a_good(v) + r_good(v) = 1 + (q - 1) = q`.

Also `r_good` is constant, so by Proposition 1.1 the obstruction class vanishes and `G_good[w]` is
regular.

For `G_bad`:

- let `G_bad[w]` be the star on `w` centered at `v₀`;
- join every vertex of `R` to every leaf `v₁, ..., v_{q-1}`;
- and join only `x₁` additionally to the center `v₀`.

Then the internal degrees on `w` are

- `a_bad(v₀) = q - 1`,
- `a_bad(v_i) = 1` for `i >= 1`,

while the dropped-part degrees are

- `r_bad(v₀) = 1`,
- `r_bad(v_i) = q - 1` for `i >= 1`.

Hence every vertex of `w` again has host degree

- `a_bad(v) + r_bad(v) = q`.

So the host congruence data on `w` are identical in `G_good` and `G_bad`.

But `r_bad` is not constant modulo `q`: for `q >= 4`,

- `1 ≠ q - 1 [MOD q]`.

Therefore `Ω_R(w) = [r_bad]` is nonzero in `M_q(w)` by Proposition 1.1, so `G_bad[w]` is not
regular and the current bucket is not exact.

Thus both graphs have:

- the same bucket size `|w| = q`,
- the same maximal control size `|t| = q - 1`,
- the same exact control degree into `t` on `w` (namely `0`),
- the same natural degree partition `R_0 = R`,
- and the same host degrees on `G[s]` over `w`,

but opposite outcomes for the tail obstruction.

### Corollary 8.3

The partition of `R` by exact degree into `t`, even together with the host congruence data on `w`,
does **not** determine the dropped-part residue on `w`.

So this degree-class partition alone cannot finish the positive-dyadic refinement exact self-bridge.
Any successful theorem along this route must add genuinely new information *inside* the classes
`R_d`—for example residue-controlled block data on `w`, or a dyadic packet/divisibility structure in
the obstruction module.

The same conclusion survives in the full refinement-data package, because the old separated external
blocks only contribute constant residues on `w` and therefore do not alter `Ω_R(w)`.

## 9. What survives at the preimage level

The previous sections show that the current terminal refinement package is too weak to force
same-bucket exactness.

One possible escape remained:

> perhaps a genuine size-`q^2` fixed-modulus host witness carries additional structure *outside* the
> chosen bucket `w`, and perhaps that extra preimage structure is exactly what kills the obstruction.

This section isolates that extra structure precisely.

### The padded terminal setup

Fix a terminal refinement package with:

- a bucket `w`,
- a control block `t`,
- a tail `R`,
- `|w| = q`,
- `|t| = q - 1`,
- `s = w ⊔ R`,
- exact control degree `e` into `t` on `w`,
- host degree `H mod q` on `w`.

If `|s| <= q^2 - q + 1`, add a disjoint filler set `F` of size

- `|F| = q^2 - q + 1 - |s|`,

anticomplete to `w`, and place every vertex of `F` in any fixed degree class `d != e` into `t`.

Then:

- `w` is still the exact-degree-`e` bucket into `t`,
- the dropped-part obstruction on `w` is unchanged,
- and `w ⊔ (R ⊔ F)` now has size exactly `q^2 - q + 1`.

Write

- `C := R ⊔ F ⊔ t`.

For `x in C`, define

- `c(x) := |N(x) ∩ w|`.

### Theorem 9.1 (preimage-completion obstruction)

With the notation above, the padded terminal example lifts to a genuine size-`q^2` modular host
witness if and only if one can complete the graph on `C` so that

- `deg_C(x) ≡ H + e - c(x) [MOD q]`

for every `x in C`.

### Proof

Assume first that the padded terminal example has been completed to a genuine host witness of size
`q^2`, using the same bucket `w` and the same control block `t`.

Every vertex `v in w` has:

- host degree `H mod q` inside `G[s]`,
- and exact degree `e` into `t`.

So in the full preimage host `w ⊔ C`, every `v in w` has degree

- `deg_{G[w ⊔ C]}(v) ≡ H + e [MOD q]`.

Now fix `x in C`. Its neighbors in `w ⊔ C` split into:

- its `c(x)` neighbors in `w`,
- and its neighbors inside `C`.

Hence

- `deg_{G[w ⊔ C]}(x) = c(x) + deg_C(x)`.

Since the preimage host witness has constant host degree modulo `q` on all of `w ⊔ C`, this must be
congruent to the same residue `H + e`, i.e.

- `c(x) + deg_C(x) ≡ H + e [MOD q]`,

which is exactly the displayed congruence.

Conversely, if the graph on `C` is completed so that

- `deg_C(x) ≡ H + e - c(x) [MOD q]`

for every `x in C`, then every vertex of `C` has degree congruent to `H + e` in `G[w ⊔ C]`, while
every vertex of `w` already has degree congruent to `H + e` there.

So `w ⊔ C` is a size-`q^2` host with constant degree modulo `q`, and the old control block `t`
still has exact degree `e` on `w`. Adding one external control vertex if needed packages this as a
genuine fixed-modulus single-control modular host witness of size `q^2`.

This proves the equivalence.

### Corollary 9.2 (the bad terminal package really lifts)

For every dyadic `q = 2^j >= 4`, the bad terminal example from Theorem 8.2 admits such a completion.

Hence there exist genuine size-`q^2` modular host witnesses whose distinguished terminal bucket `w`
has nonzero obstruction `Ω_R(w)`.

### Proof

In Theorem 8.2, take:

- `e = 0`,
- `H ≡ 0 [MOD q]`,
- and pad by a filler set `F` anticomplete to `w` and of any fixed nonzero degree into `t`.

Then for every vertex of `t ⊔ F`, one has `c(x) = 0`, so the target residue in Theorem 9.1 is `0`.

For the tail vertices in `R`, the bad example has:

- one exceptional vertex `x_1` with `c(x_1) = q`,
- and the remaining `q - 2` vertices with `c(x) = q - 1`.

So the target residues on `C` are:

- `0` on `t ⊔ F ⊔ {x_1}`,
- `1` on the other `q - 2` vertices of `R`.

Since `q - 2` is even, choose a perfect matching on those `q - 2` special vertices of `R`, and put
no other edges inside `C`.

Then:

- every matched special vertex has degree `1` inside `C`,
- every other vertex of `C` has degree `0` inside `C`.

So the congruence demanded by Theorem 9.1 holds exactly.

Therefore the bad terminal package lifts to a genuine size-`q^2` modular host witness.

Because its obstruction `Ω_R(w)` is still nonzero, the distinguished terminal bucket is still not
exact.

### Consequence 9.3

The extra preimage structure carried by an honest size-`q^2` host witness is **not** enough to repair
same-bucket exactness.

So any theorem that finishes the bridge must be genuinely existential:

- it cannot prove that the distinguished bucket `w` is exact;
- it cannot rely only on the degree-into-`t` partition of the tail;
- it cannot rely only on the canonical degree buckets in the source host;
- and it cannot rely only on first-bit / packet information in the obstruction module.

### The surviving honest theorem target

After all of the no-go results above, the mathematically honest positive theorem is now:

> **Preimage Completion Exact-Witness Theorem.**
> For every dyadic `q = 2^j`, every genuine size-`q^2` fixed-modulus single-control modular host
> witness contains a bounded exact single-control witness of size `q`, but the witness may lie
> somewhere else in the completed preimage graph and need not be the distinguished host-step bucket.

This is exactly the remaining existential statement not ruled out by the current mathematics.

## 10. The global host-subset reformulation

Section 9 shows that no theorem can force the **distinguished** bucket `w` to be exact after passing
to a genuine size-`q^2` completion.

But the surviving existential theorem can be sharpened in a different direction: once a genuine
size-`q^2` host witness exists, the old control data are no longer the issue. The only issue is to
find the right size-`q` subset **somewhere inside the completed host**.

So fix a genuine size-`q^2` fixed-modulus single-control modular host witness, and write:

- `S` for its size-`q^2` host set,
- `t` for its distinguished control block,
- `e` for the exact degree into `t` on `S`,
- `H mod q` for the common host-degree residue on `S`.

For any subset `U ⊆ S` with `|U| = q`, write

- `R_U := S \ U`,
- `a_U(v) := deg_{G[U]}(v)`,
- `r_U(v) := |N(v) ∩ R_U|`,
- `Ω_{R_U}(U) := Σ_{x ∈ R_U} [c_x^U] ∈ M_q(U)`,

where `c_x^U` is the binary adjacency column of `x` into `U`.

### Proposition 10.1 (host-internal exactness criterion)

For every `U ⊆ S` with `|U| = q`, the following are equivalent:

1. using the **inherited** control block `t`, the pair `(U, t)` is a bounded exact single-control
   witness of size `q`;
2. `G[U]` is regular;
3. the complement degrees `r_U(v)` are constant modulo `q` on `U`;
4. `Ω_{R_U}(U) = 0` in `M_q(U)`.

### Proof

Because `t` has exact degree `e` on all of `S`, it also has exact degree `e` on `U`.
Because the host degrees on `G[S]` are constant modulo `q` on all of `S`, they are constant modulo
`q` on `U`.

So the proofs of Proposition 1.1 above and Proposition 2.1 / Proposition 3.1 from the math memo
apply verbatim with:

- `w := U`,
- `s := S`,
- `R := R_U`.

This gives the equivalence of the four displayed conditions.

### Corollary 10.2 (the exact remaining host-side theorem)

To prove the Preimage Completion Exact-Witness Theorem, it is enough to prove the following
purely host-internal statement:

> **Global Host Obstruction-Zero Theorem.**
> For every genuine size-`q^2` fixed-modulus single-control modular host witness with host set `S`,
> there exists a subset `U ⊆ S` of size `q` such that
> 
> - `Ω_{S \ U}(U) = 0` in `M_q(U)`.

Equivalently, there exists `U ⊆ S` of size `q` such that:

- the degrees `|N(v) ∩ (S \ U)|` are constant modulo `q` on `U`;
- equivalently, `G[U]` is regular;
- equivalently, `(U, t)` is already an exact size-`q` witness with the inherited control block.

### Proof

If such a subset `U` exists, Proposition 10.1 shows that `(U, t)` is already a bounded exact
single-control witness of size `q`.

So the original existential theorem reduces to finding **some** size-`q` subset of the completed
host whose complement obstruction vanishes.

This is strictly sharper than the old same-bucket target:

- Section 9 shows that the special host-step bucket `w` can have nonzero obstruction even in a
  genuine size-`q^2` completion;
- Theorem 8.2 / Corollary 8.3 show that the natural degree-into-`t` partition of the tail is still
  too weak to determine that obstruction.

Thus the honest surviving theorem is not about a canonical bucket any more. It is about the
existence of **some** `q`-subset `U` of the completed host with vanishing obstruction.

### A still sharper purely graph-theoretic sufficient theorem

If one forgets the control block completely, the remaining host-side content is:

> **Modular `q^2 -> q` Regular Selection Theorem.**
> Every graph on `q^2` vertices whose degrees are all congruent modulo `q` contains a regular
> induced subgraph on `q` vertices.

Indeed, applying this to the host graph `G[S]` yields such a subset `U`, and then Proposition 10.1
reuses the inherited control block `t` to package `U` as the desired exact witness.

This theorem is stronger than the current existential target, but it is not ruled out by any of the
existing no-go results. Those results only show that particular **canonical** size-`q` subsets can
fail, not that every size-`q` subset fails.

## 11. What the pure `q^2 -> q` theorem still survives

Section 10 isolates the last honest theorem:

> every graph on `q^2` vertices whose degrees are all congruent modulo `q`
> contains a regular induced subgraph on `q` vertices.

The remaining question is therefore no longer about the host-step output, the canonical terminal
bucket, or the exact control block. It is about the existence of **some** good `q`-subset.

This section records three further facts about that pure theorem.

### 11.1 The canonical bad family is not a global counterexample

The bad completed family from Corollary 9.2 has:

- the canonical bucket `w = {v_0, ..., v_{q-1}}`,
- the tail `R = {x_1, ..., x_{q-1}}`,
- `G[w]` equal to a star centered at `v_0`,
- every `x_i` joined to all leaves of the star,
- `x_1` also joined to the center `v_0`,
- and the vertices `x_2, ..., x_{q-1}` paired by a perfect matching.

The distinguished bucket `w` is bad: its obstruction is nonzero.

But the alternative set

- `U := {v_0} ⊔ R`

has size `q`, and the induced graph `G[U]` is a perfect matching:

- `v_0` is adjacent only to `x_1`,
- `x_1` is adjacent only to `v_0`,
- each `x_i` for `i >= 2` is adjacent only to its matching partner in `R`.

So `G[U]` is `1`-regular on `q` vertices.

### Consequence 11.1

The bad same-bucket / bad canonical-bucket constructions do **not** refute the pure `q^2 -> q`
selection theorem.

They only prove:

- the **distinguished** bucket can fail,

not:

- every `q`-subset fails.

So any genuine counterexample would need a **global** obstruction surviving for all `q`-subsets.

### 11.2 The naive additive route is too strong

Let `S = V(G)` with `|S| = q^2`, and suppose all degrees in `G` are congruent modulo `q`.

For each `x in S`, let:

- `b_x in (Z / qZ)^S`

be the full adjacency column of `x`, and let:

- `g_x := [b_x] in N := (Z / qZ)^S / <1_S>`.

Because the column sum is the degree vector, which is constant modulo `q`, one has:

- `Σ_{x in S} g_x = 0` in `N`.

If one could find a `q`-subset `U` with:

- `Σ_{u in U} g_u = 0`,

then the degree into `U` would be constant modulo `q` on **all** of `S`, hence in particular on
`U`, and `G[U]` would be regular.

So this is a stronger sufficient condition than the obstruction-zero condition in Section 10.

However, as a pure zero-sum problem in an exponent-`q` abelian group, this is too much to expect:
there are length-`q^2` zero-sum sequences in `C_q^{q^2-1}` with no `q`-term zero-sum subsequence.

### Consequence 11.2

No off-the-shelf Erdős-Ginzburg-Ziv / Olson / vector zero-sum theorem on a fixed ambient abelian
group can prove the pure `q^2 -> q` theorem by itself.

Any successful additive proof must use extra graph structure:

- symmetry of the adjacency matrix,
- `0 / 1` columns,
- or the fact that the obstruction module changes with the chosen `q`-subset.

### 11.3 The naive dyadic-halving route does not stack

The Section 10 obstruction criterion says that for a `q`-subset `U` one needs:

- `Ω_{S \ U}(U) = 0`.

In the `2`-adic language of Sections 4 and 5, this means proving successive divisibility:

- `Ω_0 = Ω_{S \ U}(U)`,
- `Ω_m = 2 Ω_{m+1}` for `m = 0, ..., j - 1`.

So a genuine dyadic proof must create **all** binary digits of the complement obstruction, not only
the first one.

The basic failure of naive halving is this.

Suppose one builds a nested chain

- `S = S_0 ⊋ S_1 ⊋ ... ⊋ S_j = U`,

and writes

- `D_m := S_{m-1} \ S_m`.

Then for `v in U`,

- `deg_{G[U]}(v) ≡ λ - Σ_{m=1}^j |N(v) ∩ D_m| [MOD q]`,

where `λ` is the common degree residue on `S`.

So a residue bit made constant on some intermediate `S_m` is **not** preserved automatically:
later deleted layers still contribute new residue on the final `U`.

### Consequence 11.3

Parity/Gallai-type halving can at best control one bit unless every later deleted layer is itself
already residue-controlled on the final set.

So a successful dyadic proof still needs a new theorem of one of the following forms:

- a residue-controlled decomposition of the deleted layers,
- a binary tail-coding principle,
- or a direct divisibility argument in the varying obstruction modules `M_q(U)`.

## 12. Final mathematical frontier

After Sections 8–11, the strongest mathematically honest statement not ruled out is exactly:

> **Modular `q^2 -> q` Regular Selection Theorem.**
> Every graph on `q^2` vertices whose degrees are all congruent modulo `q = 2^j`
> contains a regular induced subgraph on `q` vertices.

Equivalently, for every such graph there exists a `q`-subset `U` with:

- `Ω_{V \ U}(U) = 0` in `M_q(U)`.

This theorem is:

- stronger than the current existential host-witness target,
- not contradicted by any of the bad canonical-bucket constructions,
- and not currently implied by the generic additive or naive dyadic arguments above.

So this is the exact remaining finite theorem.

## 13. Why the classical almost-regular subgraph theorems still do not close it

The 1984 paper of Alon, Friedland, and Kalai proves the following two relevant facts.

1. If every vertex of a graph has degree `k` or `k + 1`, and `k > 2q - 2`, then the graph contains a
   `q`-regular subgraph.
2. More generally, every simple graph with maximal degree `Δ > 2q - 2` and average degree
   `d > ((2q - 2)/(2q - 1))(Δ + 1)` contains a `q`-regular subgraph.

These are genuine and powerful regular-subgraph theorems, but they do **not** settle the present
induced-subgraph problem.

The reason is twofold.

### 13.1 They produce subgraphs, not induced subgraphs

A `q`-regular subgraph on a vertex set `U` need not imply that the induced graph `G[U]` is regular.
Extra edges of `G[U]` that are not used by the regular subgraph may destroy induced regularity.

So even if the host graph `G[S]` from Section 10 contains a `q`-regular subgraph, this does not by
itself produce a `q`-subset `U` with `Ω_{S \ U}(U) = 0`.

### 13.2 Quantitative modular-congruence theorems of order `q + 2` are still too weak

Suppose one had a theorem guaranteeing an induced subgraph on `q + 2` vertices whose degrees are
all congruent modulo `q`.

Even that would not settle the problem.

For `q = 8`, the cycle `C_{10}` has:

- `q + 2 = 10` vertices,
- all degrees equal to `2`, hence all degrees congruent modulo `8`,

but it contains **no** regular induced subgraph on `8` vertices.

Indeed, every induced `8`-vertex subgraph of `C_{10}` is obtained by deleting two vertices, hence is
a disjoint union of two paths whose total order is `8`. Such a graph is never regular.

So a theorem producing only a `(q + 2)`-vertex induced subgraph with constant degree residue mod `q`
would still not be enough in general.

### Consequence 13.3

The remaining theorem really must be an **induced regular selection theorem**:

> not a regular-subgraph theorem,
> not a same-bucket theorem,
> and not merely a theorem producing a slightly larger induced graph with constant residue modulo `q`.

It must find a `q`-subset `U` whose induced graph is already regular, equivalently

- `Ω_{V \ U}(U) = 0` in `M_q(U)`.

## 14. Edge-extremal and local-exchange arguments do not suffice

The next natural attack on the pure `q^2 -> q` theorem is:

- maximize the induced edge count `e(U)` over all `q`-subsets `U`,
- or minimize a first-order surrogate such as degree spread,
- and then prove that every local optimum is already regular.

This route is false.

### Theorem 14.1 (edge-extremal no-go)

For every dyadic `q = 2^j >= 4`, there exists a graph `G_q` on `q^2` vertices such that:

1. every vertex degree is congruent to `0 mod q`;
2. `G_q` contains a regular induced subgraph on `q` vertices;
3. the unique `q`-subsets maximizing `e(U)` are nonregular;
4. those maximizers are strict one-vertex-exchange local maxima of `e(U)`;
5. for `q >= 8`, those same sets are also strict one-vertex-exchange local minima of degree spread.

### Construction

Let

- `W = {a, b, c_1, ..., c_{q-2}}`,
- `Y = {alpha, beta, z_1, ..., z_{q-2}}`,
- `I` a set of `q^2 - 2q` isolated vertices.

Define `G_q` by:

- `G_q[W] = K_q - ab`,
- `G_q[Y] = K_q - alpha beta`,
- cross-edges:
  - `alpha a`, `alpha b`, `beta a`, `beta b`,
  - `c_i z_i` for `1 <= i <= q - 2`,
- and `I` anticomplete to everything.

Then every vertex of `W ∪ Y` has degree exactly `q`, while every vertex of `I` has degree `0`.
So all degrees are `0 mod q`.

Also any `q` vertices of `I` form an induced `0`-regular graph, so a good `q`-subset exists.

### Why the edge-maximizers are bad

Both `W` and `Y` induce `K_q` minus one edge, hence

- `e(W) = e(Y) = (q choose 2) - 1`,

and neither is regular.

Every mixed `q`-subset `U` meeting both `W` and `Y` loses at least two edges relative to a clique,
because the only cross-edges are the `K_{2,2}` between `{a, b}` and `{alpha, beta}` together with the
matching `c_i z_i`. A direct count shows:

- `e(U) <= (q choose 2) - 2`

for every mixed `U`.

Any `q`-subset using a vertex of `I` satisfies

- `e(U) <= (q - 1 choose 2) < (q choose 2) - 1`.

So `W` and `Y` are the unique edge-maximizers, and both are bad.

### Why one-swap local search also fails

If `u in W` and `x notin W`, then

- `e(W - u + x) - e(W) = |N(x) ∩ (W \ {u})| - deg_{G[W]}(u)`.

Now every `u in W` has induced degree `q - 2` or `q - 1`, while every `x notin W` sees at most two
vertices of `W`. Hence every one-vertex swap strictly decreases `e(U)`.

For `q >= 8`, the degree spread on `W` is `1`, while after any one-vertex swap the new vertex has
induced degree at most `2` and some surviving `c_i` still has induced degree at least `q - 2`, so
the new spread is at least `q - 4 > 1`.

### Consequence 14.2

The pure `q^2 -> q` theorem cannot be proved by:

- maximizing `e(U)`,
- first-order swap optimality,
- or, for `q >= 8`, local descent of degree spread.

Any successful extremal proof must use a genuinely stronger global invariant.

## 15. The single-degree-class and abstract matrix routes are false

Two further plausible reductions also fail.

### Proposition 15.1 (abstract constant-row-sum matrix package is false)

Let `n = q^2`. Choose distinct numbers

- `a_1, ..., a_n in q Z`

with

- `a_1 + ... + a_n = 0`.

Define a symmetric integer matrix `B` by:

- `B_{ij} = a_i + a_j` for `i != j`,
- `B_{ii} = -(n - 2) a_i`.

Then every row sum of `B` is exactly `0`, and every diagonal entry is a multiple of `q`.

But for every `q`-subset `U` and every `i in U`,

- `rowSum_i(B[U]) = (sum_{u in U} a_u) - (n - q) a_i`
- `                = (sum_{u in U} a_u) - q (q - 1) a_i`.

Since the `a_i` are distinct, the `q` row sums of `B[U]` are distinct.
So no principal `q x q` submatrix of `B` has constant row sum.

Therefore the theorem cannot be reduced to the statement:

> every symmetric constant-row-sum matrix with diagonal entries in `q Z`
> has a principal `q x q` constant-row-sum submatrix.

### Proposition 15.2 (one exact degree class can carry any bad `q`-graph)

For every graph `H` on `q` vertices, there exists a graph `G` on `q^2` vertices such that:

1. every degree of `G` is divisible by `q`;
2. `G` has an exact degree class `D` of size `q`;
3. `G[D]` is exactly `H`.

### Construction

Let `D` be a copy of `V(H)`.
Let `X` be a disjoint set of size `q (q - 1)`.

For each `v in D`, choose a disjoint set `F_v subseteq X` of size `deg_H(v)`.
Join `v` to every vertex of `X \ F_v`.
On `union_v F_v`, add a perfect matching.

Then:

- every `v in D` has degree
  - `deg_H(v) + |X \ F_v|`
  - `= deg_H(v) + q (q - 1) - deg_H(v)`
  - `= q (q - 1)`,
- every `x in X` has degree exactly `q`:
  - if `x in F_v`, it is joined to all vertices of `D \ {v}` and to one matching partner;
  - if `x notin union_v F_v`, it is joined to all `q` vertices of `D`.

So all degrees are `0 mod q`, and `D` is an exact degree class of size `q` carrying the arbitrary
induced graph `H`.

### Consequence 15.3

No proof can focus on a single exact degree class and expect that class alone to contain the desired
regular induced `q`-subgraph.

So the remaining theorem is genuinely global.

## 16. Homogeneous substitution graphs with `q + 2` bags are never counterexamples

The next natural counterexample source is a homogeneous substitution graph:

- the vertex set is partitioned into bags `B_i`,
- each bag is either a clique or an independent set,
- and between two bags the bipartite graph is either complete or empty.

Write:

- `n_i := |B_i|`,
- `epsilon_i in {0, 1}` for the bag type (`0` independent, `1` clique),
- and `R` for the reduced graph on the bags.

For such a graph:

- global degree congruence is exactly
  - `epsilon_i (n_i - 1) + sum_{j ~ i} n_j ≡ lambda [MOD q]`,
- and a regular induced `q`-subgraph is exactly a choice
  - `0 <= x_i <= n_i`,
  - `sum_i x_i = q`,
  - with
    - `epsilon_i (x_i - 1) + sum_{j ~ i} x_j = d`
    - for every `i` with `x_i > 0`.

### Lemma 16.1 (same-type heavy pair)

If two bags have the same type and each has size at least `q / 2`, then they already contain a
regular induced `q`-subgraph.

### Proof

There are four cases.

1. Two clique-bags joined to each other: any split `a + b = q` gives a clique `K_q`.
2. Two independent bags anticomplete to each other: any split gives an independent set on `q`
   vertices.
3. Two clique-bags anticomplete to each other: taking `q / 2` vertices from each bag gives
   `K_{q/2} ⊔ K_{q/2}`, which is `(q / 2 - 1)`-regular.
4. Two independent bags joined to each other: taking `q / 2` vertices from each bag gives
   `K_{q/2, q/2}`, which is `q / 2`-regular.

Here `q / 2` is an integer because `q = 2^j`.

### Theorem 16.2 (`q + 2` bags always work)

Every homogeneous substitution graph on `q^2` vertices with `q + 2` bags contains a regular induced
subgraph on `q` vertices.

### Proof

Let the bag sizes be `n_1, ..., n_{q+2}` with

- `n_1 + ... + n_{q+2} = q^2`.

If some `n_i >= q`, that bag alone contains:

- either a clique on `q` vertices,
- or an independent set on `q` vertices.

So assume every `n_i <= q - 1`.
Write

- `n_i = (q - 1) - t_i`

with `t_i >= 0`.
Then

- `t_1 + ... + t_{q+2} = (q + 2) (q - 1) - q^2 = q - 2`.

So at most `q - 2` of the `t_i` are positive, and therefore at least `4` bags have size exactly
`q - 1`.

Among those `4` bags, two have the same type.
Each has size `q - 1 >= q / 2`, so Lemma 16.1 applies.

Thus the graph already contains a regular induced `q`-subgraph.

### Consequence 16.3

The first genuinely open substitution regime is **not** `q + 2` bags.

In fact, any substitution counterexample must avoid two same-type bags of size at least `q / 2`.
So there can be at most:

- one clique-bag of size at least `q / 2`,
- one independent bag of size at least `q / 2`.

If `m` is the number of bags, then

- `q^2 <= 2 (q - 1) + (m - 2) (q / 2 - 1)`,

hence

- `m >= 2 q + 2 + ceil (4 / (q - 2))`.

So any substitution counterexample must have at least:

- `12` bags when `q = 4`,
- `2 q + 3` bags when `q >= 8`.

Thus all low-complexity bag-counterexamples are ruled out.

## 17. Modular decomposition only reduces to small bad modules or prime weighted quotients

The next natural structural attack is modular decomposition.
It gives a real reduction, but not all the way down to ordinary prime graphs.

Call a graph `q`-bad if:

- all degrees are congruent modulo `q`,
- but there is no regular induced subgraph on `q` vertices.

### Proposition 17.1 (modules inherit `q`-modularity)

If `M` is a module of a `q`-modular graph `G`, then `G[M]` is also `q`-modular.

### Proof

Every vertex of `M` has the same outside degree

- `lambda_M := |N_G(v) \ M|`.

So for `v in M`,

- `deg_{G[M]}(v) = deg_G(v) - lambda_M`.

If the degrees of `G` are all congruent modulo `q`, then the same is true on `M`.

### Consequences 17.2

1. If `|M| = q`, then `G[M]` is automatically regular, so `M` itself is a good `q`-subset.
2. If `|M| < q`, then congruence modulo `q` already implies exact equality on `M`.
   So every module of size `< q` is regular.

Thus a counterexample cannot contain a module of size exactly `q`.

### Proposition 17.3 (quotient formula)

Suppose

- `G = Q[H_1, ..., H_m]`

is a modular substitution decomposition, with bags `B_i := V(H_i)`, bag sizes `n_i := |B_i|`,
and quotient graph `Q`.

If each bag `H_i` is `q`-modular with residue `rho_i`, then `G` is `q`-modular if and only if

- `rho_i + sum_{j ~_Q i} n_j`

is independent of `i` modulo `q`.

### Proof

For `v in B_i`,

- `deg_G(v) = deg_{H_i}(v) + sum_{j ~_Q i} n_j`,

and the claim follows by reducing modulo `q`.

### Consequence 17.4

Modular decomposition does **not** reduce the theorem to ordinary prime graphs.
It reduces it to:

- prime quotient graphs,
- together with bag-size labels `n_i`,
- and bag residues `rho_i`.

So the true irreducibles are **prime weighted/residue quotients**, not plain prime graphs.

### Theorem 17.5 (prime-or-small reduction)

If a `q`-bad graph on `q^2` vertices exists, then it contains a `q`-bad module `M` such that either:

1. `q + 1 <= |M| <= 2 q - 2`, or
2. the top quotient of `M` is prime, and all its bags are regular of size `< q`.

### Proof

Choose an inclusion-minimal `q`-bad module `M`.

Every proper `q`-bad module would contradict minimality, so every proper module of `M` has size
`< q`, hence is regular by Consequence 17.2.

Let `B_1, ..., B_m` be the maximal proper strong modules of `M`.
Then every `B_i` is regular and has size at most `q - 1`.

If the top quotient of `M` is prime, we are in case (2).

Otherwise the top quotient is degenerate (complete or edgeless), so any union of children is again
a module.
Since each `|B_i| < q`, taking a greedy union of children until the size first crosses `q` yields a
module `U` with

- `q <= |U| <= 2 q - 2`.

By minimality of `M`, such a proper `q`-bad submodule cannot exist.
So this forces `U = M`.
Because `|M| != q`, one gets

- `q + 1 <= |M| <= 2 q - 2`.

That is case (1).

### Consequence 17.6

The obstruction interval `q < n < 2 q` is genuine.

For every `q >= 4`, the cycle `C_{q+1}` is `q`-modular (all degrees equal `2`), but it has no
regular induced subgraph on `q` vertices:

- every induced `q`-vertex subgraph is a path `P_q`,
- hence is not regular.

So modular decomposition cannot prove the theorem by a simple induction on module size.

## 18. The dyadic obstruction after freezing `m` bits is the half-obstruction `eta_m`

The naive dyadic-halving program already failed.
But one can sharpen the failure and identify the exact object that survives after freezing `m`
binary digits.

Fix a `q`-subset `U`, and write

- `r_U(v) := |N(v) ∩ (V \ U)|`,
- `Omega(U) := [r_U] in M_q(U) := (Z / q Z)^U / <1_U>`.

As before:

- `G[U]` is regular if and only if `Omega(U) = 0`.

### Proposition 18.1 (fixed-`U` dyadic lift identity)

Assume `q = 2^j`, and `r_U` is constant modulo `2^m`.
Choose `c_m` with

- `r_U ≡ c_m 1_U [MOD 2^m]`,

and define

- `eta_m(U) := [(r_U - c_m 1_U) / 2^m] in M_{q / 2^m}(U)`.

Then:

1. `eta_m(U)` is well-defined;
2. under the natural injective map `M_{q / 2^m}(U) -> M_q(U)`, one has
   - `Omega(U) = 2^m eta_m(U)`;
3. therefore
   - `G[U]` regular `iff Omega(U) = 0 iff eta_m(U) = 0`;
4. the lift from modulus `2^m` to modulus `2^(m+1)` on this fixed `U` is exactly:
   - `eta_m(U)` lies in `2 M_{q / 2^m}(U)`.

So after the first `m` binary digits are frozen, the remaining obstruction is not more first-bit
data. It is precisely the **half-obstruction**

- `eta_m(U) in M_{q / 2^m}(U)`.

### Theorem 18.2 (layerwise `m`-bit divisibility still does not force exactness)

For every `1 <= m < j`, there is a graph on `q^2` vertices, all degrees `0 mod q`, and a `q`-set
`U` such that:

1. every active deleted layer already contributes only a class in `2^m M_q(U)`;
2. but
   - `Omega(U) in 2^m M_q(U) \ 2^(m+1) M_q(U)`,
3. so `G[U]` is not regular.

### Construction

Let

- `U = {v_0} ⊔ L` with `|L| = q - 1`.

On `L`, choose any `(2^m - 2)`-regular graph.
Join `v_0` to all of `L`.
Then inside `U`:

- `deg_U(v_0) = q - 1`,
- `deg_U(ell) = 2^m - 1` for `ell in L`.

Now let

- `R = {x_*} ⊔ Y`,
- `|Y| = q - 2^m`.

Join `x_*` to all of `U`.
Join each `y in Y` to all of `L` and not to `v_0`.
Put a perfect matching on `Y`.
Add isolated fillers so the total size is `q^2`.

Then every vertex of `U ∪ R` has degree exactly `q`, and every filler has degree `0`.
So all degrees are `0 mod q`.

For this `U`, the complement-degree vector is

- `r_U = (1, q - 2^m + 1, ..., q - 2^m + 1)`
- `    = 1_U + 2^m (0, 2^(j-m) - 1, ..., 2^(j-m) - 1)`.

Hence

- `Omega(U) = 2^m eta`,

where

- `eta = [(0, -1, ..., -1)] in M_{q / 2^m}(U)`.

This class is nonzero, and its reduction modulo `2` is still nonzero.
So:

- `Omega(U)` is divisible by `2^m`,
- but not by `2^(m+1)`.

Thus `G[U]` is not regular even though every deleted layer is already harmless through the first
`m` dyadic bits.

### Consequence 18.3

The honest missing lift object is:

- not more parity data on deleted layers,
- but the residual class `eta_m(U) in M_{q / 2^m}(U)`.

So any successful dyadic proof must control `eta_m(U)` itself, not merely the first `m` bits of the
individual deleted layers.

## 19. Affine-line forcing is false

Because `q = 2^j` is a prime power, one can label the `q^2` vertices by `F_q^2` and ask whether some
affine line of size `q` must already be good.

For a direction `D in P^1(F_q)` and a vertex `v`, write

- `delta_D(v) := |N(v) ∩ ((v + D) \ {v})|`.

Then:

- `deg(v) = sum_D delta_D(v)`,
- and for an affine line `L = a + D`, the induced graph `G[L]` is regular if and only if `delta_D`
  is constant on `L`.

For `q = 2`, every line has two vertices, so every line is automatically regular.
For `q >= 4`, the line-selection theorem is false.

### Theorem 19.1 (no affine line need work)

For every `q >= 4`, there exists a graph on `F_q^2` such that:

1. all vertex degrees are congruent modulo `q`;
2. no affine line induces a regular graph.

### Construction

Choose a fixed-point-free permutation `sigma` of the `q + 1` directions.
For each direction `D`, let `T_D := sigma(D)` denote the origin-line in direction `sigma(D)`.
For each affine line `L parallel D`, let

- `c(L) := L ∩ T_D`.

On every affine line `L`, place exactly the star `K_{1, q - 1}` centered at `c(L)`.
This is a well-defined graph because every edge of the affine plane lies on a unique affine line.

Then every affine line is a star, hence nonregular.

If `m(v)` denotes the number of incident lines for which `v` is the chosen center, then:

- `m(0) = q + 1`,
- `m(v) = 1` for every `v != 0`.

Therefore

- `deg(v) = m(v) (q - 1) + (q + 1 - m(v))`
- `       = q + 1 + (q - 2) m(v)`.

So:

- `deg(0) = q^2 - 1 ≡ -1 [MOD q]`,
- `deg(v) = 2 q - 1 ≡ -1 [MOD q]` for `v != 0`.

Thus all degrees are congruent modulo `q`, but no affine line is regular.

### Consequence 19.2

An affine-plane proof cannot simply show:

- some line has constant directional degree,
- or some line/coset must flatten by averaging over directions.

Any successful affine or finite-geometry proof must use genuinely stronger cross-direction structure.

## 20. Stronger convex and lexicographic extremal functionals also fail

Section 14 already ruled out:

- maximizing the induced edge count,
- one-swap edge descent,
- and local degree-spread descent.

The same graph `G_q` from Section 14 kills a much larger family of global extremal functionals.

Let `d(U) = (d_1 >= ... >= d_q)` be the induced degree sequence of a `q`-subset `U`, and define

- `w := (q - 1, ..., q - 1, q - 2, q - 2)`

with `q - 2` copies of `q - 1`.

### Theorem 20.1 (majorization no-go)

In the graph `G_q` from Section 14, every `q`-subset `U` satisfies:

- `d(U)` is weakly majorized by `w`,

with equality only for the two bad maximizers `W` and `Y`.

### Consequences 20.2

1. The descending degree sequence is lexicographically maximized exactly by `W` and `Y`, both
   nonregular.
2. For every increasing convex function `phi`, the functional
   - `Phi_phi(U) := sum_{u in U} phi(deg_U(u))`
   is maximized at `W` or `Y`; for strictly increasing `phi`, uniquely so.

In particular, this kills:

- `sum deg_U(u)^2`,
- every `l_p`-type concentration functional with `p > 1`,
- and lexicographic maximization of the sorted induced degree sequence.

### Caveat 20.3

This does **not** kill variance minimization itself:

- in `G_q`, a set of `q` isolated vertices has variance `0`.

So a variance-minimization obstruction would have to come from a genuine counterexample to the target
theorem, not from the `G_q` family.

## 21. The natural finite-field polynomial routes are ruled out

The polynomial method is tempting because it can encode:

- exact cardinality `|U| = q`,
- and equality of the selected degrees.

But the most natural finite-field encodings fail for two different reasons.

### Proposition 21.1 (characteristic-2 linear-form encodings see only parity)

Let `x_v in {0, 1}` indicate membership in a chosen set `U`.
Over any field of characteristic `2`, the natural linear forms are:

- `S(x) := sum_v x_v`,
- `D_v(x) := sum_u A_{vu} x_u`.

These only record:

- `|U| mod 2`,
- and `deg_U(v) mod 2`.

So any polynomial system using only the natural field sums `S(x)` and `D_v(x)` can distinguish only
parity data.

### Consequence 21.2

Such encodings cannot characterize regular induced `q`-subgraphs.

Indeed, in the canonical bad completed family from Section 11.1:

- the bad set `U_bad := w` induces the star `K_{1, q - 1}`,
- the good set `U_good := {v_0} ⊔ R` induces a perfect matching,

but in both cases:

- `|U| = q` is even,
- every selected vertex has odd induced degree.

So characteristic-2 linear-form encodings treat the bad and good sets identically.

### Proposition 21.3 (Lucas-bit repair is exact but too high-degree)

Over `F_2`, one can recover the full binary digits of `|U|` and `deg_U(v)` by using the Lucas-digit
polynomials

- `e_{2^r}(x)`,

whose values on Boolean inputs record the `r`-th binary digit of the relevant count.

This gives an **exact** finite-field encoding of:

- `|U| = q`,
- and equality of all selected degrees.

But the degree cost is enormous:

- exact cardinality already requires essentially full Boolean-cube degree,
- and the full Lucas system lies far outside the degree range where Chevalley-Warning / Ax style
  divisibility arguments apply.

### Consequence 21.4

The natural finite-field polynomial routes are ruled out:

1. linear-form encodings in characteristic `2` are too weak;
2. the exact Lucas-bit repair is too high-degree for the classical finite-field counting theorems.

So the only plausible algebraic arena left is genuinely `2`-adic:

- one would need a new counting or nonvanishing theorem over `Z / 2^m Z`,
- not a standard finite-field Nullstellensatz / Chevalley-Warning argument.

## 22. Small bad modules do not lift automatically

Section 17 reduced any counterexample to either:

1. a `q`-bad module `M` with `q + 1 <= |M| <= 2 q - 2`, or
2. a prime weighted/residue quotient with regular bags of size `< q`.

The first branch does not collapse automatically.

Let:

- `W := V(G) \ M`,
- `X := {w in W : w is complete to M}`,
- `Y := {w in W : w is anticomplete to M}`.

Write:

- `|M| = q + r` with `1 <= r <= q - 2`.

Then the outside graph `H := G[W]` satisfies:

- `deg_H(x) ≡ lambda - |M| [MOD q]` for `x in X`,
- `deg_H(y) ≡ lambda [MOD q]` for `y in Y`.

So the module exports exactly **two** residue classes to the outside world, separated by

- `|M| ≡ r != 0 [MOD q]`.

### Proposition 22.1 (exact lifting criterion)

Let `S = A ⊔ B` be a `q`-subset with:

- `A subseteq M`,
- `B subseteq W`,
- `|A| = a`,
- `|B| = q - a`,
- `s := |B ∩ X|`.

Then `S` is regular if and only if:

1. `A` is already `alpha`-regular for some `alpha`, and
2. the outside vertices satisfy:
   - `deg_B(x) = alpha + s - a` for `x in B ∩ X`,
   - `deg_B(y) = alpha + s` for `y in B ∩ Y`.

### Consequences 22.2

1. The outside world cannot repair irregularity inside `M`: it adds the same amount to every vertex
   of `A`.
2. Any mixed regular `q`-set must start from an **already regular** induced subgraph inside `M`.

More explicitly:

- if `B subseteq Y`, then `A` and `B` must be regular of the same degree;
- if `B subseteq X`, then `A` and `B` must be regular with degree difference `q - 2 a`;
- if `B` meets both `X` and `Y`, then `B` must be `X / Y`-biregular with degree gap exactly `a`.

Also, if both `B ∩ X` and `B ∩ Y` are nonempty, then:

- `a <= q / 2 - 1`.

So any lift using at least `q / 2` vertices of `M` must use outside vertices all of one type.

### Consequence 22.3

There is no automatic theorem of the form:

> every `q`-bad module in the small window lifts to a good `q`-set using the outside world.

The exact remaining small-window statement is:

> for each regular induced `A subseteq M` with `|A| = a < q`, must the outside graph contain a
> `(q - a)`-vertex `X / Y`-colored induced subgraph with the required degree pattern?

That is the honest finite branch-(1) problem.

## 23. Prime weighted/residue quotient data is still insufficient

Now consider branch (2):

- `G = Q[H_1, ..., H_m]`,
- `Q` prime,
- each bag `H_i` is `rho_i`-regular of size `n_i < q`,
- and
  - `rho_i + sum_{j ~_Q i} n_j ≡ lambda [MOD q]`.

### Proposition 23.1 (whole-bag criterion)

If `I subseteq [m]` satisfies:

- `sum_{i in I} n_i = q`,

and

- `D_I(i) := rho_i + sum_{j in I, j ~_Q i} n_j`

is independent of `i in I`, then the union of those whole bags is a regular induced `q`-subgraph.

Because `D_I(i) <= q - 1`, constancy modulo `q` is already exact constancy for whole-bag selections.

### Proposition 23.2 (exact profile criterion)

For each bag define its regular profile:

- `P(H_i) := {(s, delta) : H_i has an induced delta-regular s-vertex subgraph}`.

Then `G` has a regular induced `q`-subgraph if and only if there exist profile choices

- `(s_i, delta_i) in P(H_i)`

and a common degree `d` such that:

- `sum_i s_i = q`,
- `delta_i + sum_{j ~_Q i} s_j = d`

for every active bag `i` with `s_i > 0`.

So the true quotient branch is not a weighted-residue problem.
It is a **bag-profile feasibility problem**.

### Caution 23.3 (the first `q = 8`, `P_4` profile example does not separate weighted data)

The first attempted `q = 8` example on the prime quotient `P_4` with weighted data

- bag sizes `(7, 4, 5, 2)`,
- residues `(2, 2, 0, 1)`,

does **not** prove that weighted/residue data alone are insufficient.

Indeed, taking:

- `H_1^- = C_7`,
- `H_2 = C_4`,
- `H_3 = I_5`,
- `H_4 = K_2`,

already yields an induced independent set on `8` vertices:

- bags `1` and `3` are anticomplete in the quotient `P_4`,
- `alpha(C_7) = 3`,
- `alpha(I_5) = 5`,

so these two bags contain an induced `I_8`.

Thus the recorded `P_4` gadget is not a genuine obstruction.

### Universal-profile refinement

For an `n`-vertex `rho`-regular graph, define the universal profile

- `U(n, rho) := intersection over all n-vertex rho-regular graphs H of P(H)`.

Then any quotient theorem based only on bag size and bag residue must pass through the finite CSP:

- choose `(s_i, delta_i) in U(n_i, rho_i)`,
- with `sum_i s_i = q`,
- and `delta_i + sum_{j ~_Q i} s_j = d` on every active bag.

This is the sharp quotient problem justified by the current evidence.

### Consequence 23.4

The honest remaining quotient statement is:

> given a prime quotient `Q`, regular bags `H_i` of size `< q`, and either their exact profiles
> `P(H_i)` or at least their universal profiles `U(n_i, rho_i)`, must there always exist profile
> choices solving the common-degree system above?

At present, prime weighted/residue quotient data by itself is still unresolved.

## 24. Natural local `2`-adic algebraic routes are also ruled out

Section 21 ruled out the most natural **finite-field** polynomial routes.
One plausible escape was to work directly over `Z / 2^m Z`, where the full dyadic structure is
visible.

This does produce an exact algebraic encoding, but the natural local `2`-adic lifting routes still
fail.

Fix:

- `q = 2^j`,
- `n = q^2`,
- Boolean variables `x_v`,
- `S(x) := sum_v x_v`,
- `D_v(x) := sum_u A_{vu} x_u`.

### Proposition 24.1 (exact Mahler projectors)

Define:

- `kappa_q(s) := sum_{a = q}^n (-1)^(a - q) (a choose q) (s choose a)`,
- `delta_t(z) := sum_{a = t}^{q - 1} (-1)^(a - t) (a choose t) (z choose a)` for `0 <= t < q`.

Then on the integer ranges `0 <= s <= n` and `0 <= z < q`:

- `kappa_q(s) = 1_{s = q}`,
- `delta_t(z) = 1_{z = t}`.

So the `2`-adic/Mahler polynomial

- `F_G(x) := kappa_q(S(x)) * sum_{t = 0}^{q - 1} prod_v (1 - x_v + x_v * delta_t(D_v(x)))`

is an **exact** indicator for:

> the selected set `U_x` has size `q` and `G[U_x]` is regular.

So there is no issue of expressive power. The issue is what one can actually force from this
encoding.

### Proposition 24.2 (digit truncation only sees the first `m` binary digits)

For `0 <= r < j`, Lucas gives

- `(z choose 2^r) mod 2 =` the `r`-th binary digit of `z`.

Hence modulo `2`, each `delta_t(z)` depends only on the binary digits of `z`, and truncating to the
first `m` Lucas digits sees only:

- `z mod 2^m`.

So any local `2`-adic criterion built only from the first `m` Mahler/Lucas digits of the degree
coordinates can only test:

- `D_v(x) mod 2^m`.

### Theorem 24.3 (no-go for digit-truncated Mahler tests and fixed-support Hensel lifting)

For every `1 <= m < j`, there exist:

1. a **good** pair `(G^+, U^+)` with
   - `G^+[U^+] = K_q`,
   - one outside vertex complete to `U^+`,
   - all other outside vertices isolated,
   - so `Omega(U^+) = 0`;
2. a **bad** pair `(G^-, U^-)` using the construction of Theorem 18.2, with
   - `Omega(U^-) = 2^m [(0, -1, ..., -1)] != 0`,
   - equivalently `eta_m(U^-) != 0`;

such that the complement-degree coordinates satisfy:

- `r_{U^+}(v) ≡ 1 [MOD 2^m]` for all `v in U^+`,
- `r_{U^-}(v) ≡ 1 [MOD 2^m]` for all `v in U^-`.

So the first `m` dyadic/Mahler digits of the complement-degree vector are identical in the good and
bad cases, but one has:

- `Omega(U) = 0`,

and the other does not.

### Consequences 24.4

No universal criterion depending only on the first `m` dyadic/Mahler digits of the complement-degree
coordinates can characterize:

- `Omega(U) = 0`.

Equivalently:

1. digit-truncated Mahler tests cannot prove the theorem;
2. support-preserving Hensel lifting on a fixed `q`-subset cannot prove the theorem.

The surviving `2`-adic possibility is therefore strictly global:

> one would need a support-varying `2`-adic counting or nonvanishing theorem that controls the full
> projector `F_G`, or directly controls the residual classes `eta_m(U)`, not merely their first
> `m` binary digits.

## 25. The first explicit `q = 8` synthesis attempts also fail

The structural reductions above still leave open the possibility of building a genuine counterexample
either:

1. from a small bad module `M` with `q + 1 <= |M| <= 2 q - 2`, or
2. from a prime quotient with carefully chosen bag profiles.

The first two concrete `q = 8` attempts both fail.

### Proposition 25.1 (the recorded `P_4` profile gadget is not bad)

Consider the `q = 8` weighted-profile example from Section 23 with prime quotient `Q = P_4`, bags:

- `H_1^- = C_7`,
- `H_2 = C_4`,
- `H_3 = I_5`,
- `H_4 = K_2`.

Then the resulting graph already contains an induced independent set on `8` vertices.

### Proof

In any substitution graph `G = Q[H_i]`, if `I subseteq V(Q)` is independent and

- `sum_{i in I} alpha(H_i) >= q`,

then one obtains an induced independent set on `q` vertices by taking independent subsets from the
bags over `I`.

Here `Q = P_4`, so `{1, 3}` is independent.
Also:

- `alpha(C_7) = 3`,
- `alpha(I_5) = 5`.

So the bags `H_1^-` and `H_3` already contain an induced `I_8`.

Thus this weighted-profile configuration is not a counterexample and cannot be inflated into one.

### Proposition 25.2 (`C_9` cannot serve as the bad module on `64` vertices)

Let `q = 8`, and suppose `M = C_9` is a bad module inside a graph on `64` vertices whose degrees are
all congruent modulo `8`.

Let:

- `X := {w outside M : w is complete to M}`,
- `Y := {w outside M : w is anticomplete to M}`.

Then this is impossible.

### Proof sketch

First, an edge in `Y` together with a `6`-vertex induced matching inside `C_9` would give a regular
induced `8`-set. So `Y` must be independent.

Also, if `|Y| >= 4`, then an independent `4`-set in `Y` together with an independent `4`-set inside
`C_9` gives an induced `I_8`.
Hence:

- `|Y| <= 3`.

Therefore:

- `|X| >= 64 - 9 - 3 = 52`.

Now if `alpha(X) >= 4`, then an independent `4`-set in `X` together with an independent `4`-set in
`C_9` again gives an induced `I_8`.
So:

- `alpha(X) <= 3`.

By the Ramsey bound `R(4, 6) = 35`, every graph on at least `35` vertices with independence number at
most `3` contains a clique `K_6`.
Since `|X| >= 52`, the graph `G[X]` contains `K_6`.

Take any edge in `C_9`. It is a `2`-vertex induced `1`-regular graph.
Adding the `K_6 subseteq X` yields an `8`-vertex induced regular graph, exactly as in the
`X`-only case of Proposition 22.1 with:

- `a = 2`,
- `alpha = 1`,
- outside degree difference `q - 2 a = 4`,

which is realized by a `K_6`.

Contradiction.

So `C_9` cannot be the small bad module in a `64`-vertex counterexample.

### Consequence 25.3

The first explicit `q = 8` synthesis attempts are dead:

1. the recorded `P_4` weighted-profile gadget is already good;
2. the most obvious small-window bad module `C_9` cannot occur inside a `64`-vertex counterexample.

So a genuine `q = 8` counterexample would need:

- a different bad module `M` with `9 <= |M| <= 14`,

or:

- a different prime quotient with enough bag-profile rigidity to defeat every `8`-vertex profile
  solution.

## 26. Universal profiles are now explicit for all regular bags of size `< 8`

To make the prime quotient branch concrete, define the universal profile

- `U(n, rho) := intersection over all n`-vertex `rho`-regular graphs `H` of `P(H)`.

The quotient CSP from Section 23 can be relaxed from exact profiles `P(H_i)` to universal profiles
`U(n_i, rho_i)`.

### Proposition 26.1 (general universal-profile facts)

Assume `n rho` is even, so `n`-vertex `rho`-regular graphs exist.

1. **Complement symmetry**
   - `(s, delta) in U(n, rho)` if and only if `(s, s - 1 - delta) in U(n, n - 1 - rho)`.
2. **Universal independent and clique lines**
   If
   - `alpha_*(n, rho) := min_H alpha(H)`,
   - `omega_*(n, rho) := min_H omega(H)`,
   then
   - `(s, 0) in U(n, rho)` for `0 <= s <= alpha_*(n, rho)`,
   - `(s, s - 1) in U(n, rho)` for `0 <= s <= omega_*(n, rho)`.
3. The crude lower bounds are
   - `alpha_*(n, rho) >= ceil(n / (rho + 1))`,
   - `omega_*(n, rho) >= ceil(n / (n - rho))`.

### Proposition 26.2 (exact easy families)

1. `U(n, 0) = {(s, 0) : 0 <= s <= n}`.
2. `U(n, n - 1) = {(s, s - 1) : 0 <= s <= n}`.
3. If `n = 2 m`, then
   - `U(2 m, 1) = {(s, 0) : 0 <= s <= m} union {(2 t, 1) : 1 <= t <= m}`.
4. By complement symmetry:
   - `U(2 m, 2 m - 2) = {(s, s - 1) : 0 <= s <= m} union {(2 t, 2 t - 2) : 1 <= t <= m}`.

### Proposition 26.3 (exact formula for `rho = 2`)

Every `2`-regular graph is a disjoint union of cycles, so induced regular subgraphs can only have
degree `0`, `1`, or `2`.
One gets:

- `U(n, 2)`
- `= {(s, 0) : 0 <= s <= ceil(n / 3)}`
- `  union {(2 t, 1) : 1 <= t <= ceil(n / 5)}`
- `  union {(n, 2)}`.

The three parts come from:

1. independent sets in cycle unions;
2. induced matchings in cycle unions;
3. the whole graph itself in the cycle case `C_n`.

By complement symmetry this also determines `U(n, n - 3)`.

### Consequence 26.4 (`q = 8` bags are completely covered)

For every feasible regular bag with `n < 8`, the universal profile is now explicit:

- `rho = 0, 1, 2` are known directly,
- `rho = n - 1, n - 2, n - 3` follow by complement symmetry,
- and the remaining parity-obstructed cases do not occur because `n rho` would be odd.

So for `q = 8`, the prime quotient branch is now a fully explicit finite CSP in the variables

- `(s_i, delta_i) in U(n_i, rho_i)`.

## 27. The `q = 8` prime quotient branch reduces to a tiny weighted cubic CSP

With the universal profiles from Section 26, the `q = 8` prime weighted quotient branch can be cut
down sharply.

### Proposition 27.1 (complement symmetry for the quotient CSP)

A quotient CSP solution

- `(s_i, delta_i, d)`

for a quotient instance `(Q, n_i, rho_i)` yields a solution

- `(s_i, s_i - 1 - delta_i, 7 - d)`

for the complemented instance

- `(\bar Q, n_i, n_i - 1 - rho_i)`.

So it is enough to analyze common degree:

- `d <= 3`.

### Proposition 27.2 (large active bags are isolated when `d <= 3`)

If `d <= 3` and some active bag has `s_i >= 4`, then that bag is isolated in the active quotient.

### Proof

Any active neighbor contributes at least `4` external selected vertices to one side or the other,
which already exceeds the allowed common degree budget `d <= 3`.

So every interacting active bag must have:

- `s_i in {1, 2, 3}`.

### Consequence 27.3 (the only local atoms for `q = 8`, `d <= 3`)

From the explicit universal profiles, the only local pieces that can appear on interacting bags are:

- `(1, 0)`,
- `(2, 0)`,
- `(2, 1)`,
- `(3, 0)`,
- `(3, 2)`.

### Proposition 27.4 (degree-by-degree collapse)

For `q = 8`, after complement symmetry:

1. `d = 0` is exactly the weighted independent-set problem;
2. `d = 1` yields only
   - `4 K_2`;
3. `d = 2` yields only
   - `C_8`,
   - `C_5 ⊔ C_3`,
   - `2 C_4`;
4. `d = 3` is the only genuinely new case.

In the cubic case:

- any `(3, 2)` bag forces an isolated `K_4`, hence the whole solution is `2 K_4`;
- any selected size-`4` bag also forces `2 K_4`;
- any selected size-`6` bag leaves only `2` vertices and is impossible.

So every genuinely new cubic solution uses only bags of selected size:

- `1` and `2`.

### Consequence 27.5 (the residual cubic micro-CSP)

After all previous reductions, the only unresolved `q = 8` quotient family is the weighted cubic
micro-CSP with weights `1` and `2` summing to `8`:

- `2^3 1^2`,
- `2^2 1^4`,
- `2 1^6`,
- `1^8`.

Here a selected size-`2` bag is either:

- a false-twin pair `(2, 0)`, or
- a true-twin pair `(2, 1)`.

### Proposition 27.6 (cubic templates)

Let `H` be the cubic `8`-vertex graph obtained by expanding such a whole-bag cubic solution.
Then:

1. if `H` contains a false twin pair, deleting it leaves degree sequence `3^3 1^3`, which is unique;
   so there is at most one false-twin cubic template `H_F`;
2. if `H` contains a true twin pair, deleting it leaves degree sequence `3^4 1^2`, and there are
   only two possibilities:
   - `2 K_4`,
   - one connected true-twin template `H_T`.

Therefore the only residual cubic whole-graph patterns are:

- `2 K_4`,
- `H_T`,
- `H_F`.

### Consequence 27.7

For `q = 8`, the prime quotient branch is no longer an infinite family of weighted prime quotients.
It is reduced to:

1. the explicit non-cubic patterns
   - `I_8`,
   - `4 K_2`,
   - `C_8`,
   - `C_5 ⊔ C_3`,
   - `2 C_4`,
   - `2 K_4`,
   and complements;
2. the tiny residual cubic micro-CSP encoded by the two connected templates `H_T` and `H_F`.

### Proposition 27.8 (the residual cubic branch collapses to two active quotient templates)

The two connected cubic templates are not excluded outright: they already arise from prime weighted
quotients.

1. **Template `T`.**
   Collapsing the two true-twin pairs in `H_T` yields the prime quotient `C_6` with weighted bags:
   - `(2, 1), (1, 0), (1, 0), (2, 1), (1, 0), (1, 0)`,
   where each pair denotes `(bag size, bag residue)`.
   Every quotient vertex has
   - `rho_i + sum_{j ~ i} n_j ≡ 3 [MOD 8]`.

2. **Template `F`.**
   Collapsing the unique false-twin pair in `H_F` yields a prime `7`-vertex quotient `F` with one
   weighted vertex `(2, 0)` joined to three leaves, each leaf joined to a distinct vertex of a
   triangle, and the six remaining bags all `(1, 0)`.
   Again every quotient vertex has
   - `rho_i + sum_{j ~ i} n_j ≡ 3 [MOD 8]`.

So the quotient problem is not to prove these templates impossible. It is to understand how inactive
bags can interact with them.

### Consequence 27.9 (honest remaining quotient problem for `q = 8`)

The last quotient branch is a finite active-template problem:

1. active quotient `T = C_6` with weights `2, 1, 1, 2, 1, 1`, where the two weight-`2` bags must be
   true-twin bags;
2. active quotient `F` with weights `2, 1, 1, 1, 1, 1, 1`, where the unique weight-`2` bag must be a
   false-twin bag.

Writing

- `epsilon_i := rho_i - delta_i`

for the active bags, the chosen `8`-set is regular exactly when the inactive bags contribute a
constant correction:

- `epsilon + sum_k n_k 1_{S_k} ≡ c 1 [MOD 8]`,

where `S_k` is the active neighborhood of the inactive bag `k`.

So the quotient side has now collapsed to a finite inactive-neighborhood correction problem on the
two explicit active templates `T` and `F`.

## 28. In the `q = 8` small-window branch, any module containing `2 K_2` is impossible

Section 25 reduced the surviving `q = 8` small bad modules to graphs `M` with:

- `9 <= |M| <= 14`,
- `alpha(M) = omega(M) = 3`,
- `M` contains an induced `C_4`,
- `M` contains no induced `C_5`,
- and `M` is still `8`-modular and `8`-bad.

The first concrete survivor from that reduction was `L(K_{3,3})`.
But the branch-(1) embedding analysis cuts the residual family down further.

### Proposition 28.1

Let `M` be a small-window bad module in the `q = 8` branch-(1) setup.
If `M` contains an induced `2 K_2`, then `M` cannot embed inside a `64`-vertex `8`-modular host
that is itself `8`-bad.

### Proof

Take `A subseteq M` inducing `2 K_2`.
Then:

- `|A| = 4`,
- and `A` is `1`-regular.

By Proposition 22.1, any lift of `A` to a regular induced `8`-set must have the form:

- `A ⊔ B`,
- with `|B| = 4`.

Since here `a = 4 > q / 2 - 1 = 3`, the mixed `X / Y` case is impossible.
So `B` must lie entirely in `X` or entirely in `Y`.
In either case Proposition 22.1 forces `B` itself to be `1`-regular, i.e. an induced `2 K_2`.

Therefore:

- `G[X]` is `2 K_2`-free,
- `G[Y]` is `2 K_2`-free.

From Section 25 we already know:

- `G[X]` is `{C_4, C_5, K_5}`-free,
- `G[Y]` is `{C_4, C_5, I_5}`-free.

So:

- `G[X]` is `{2 K_2, C_4, C_5}`-free,
- `G[Y]` is `{2 K_2, C_4, C_5}`-free.

By the Földes-Hammer theorem, such graphs are split.

Write:

- `X = C_X ⊔ I_X` with `C_X` a clique and `I_X` independent,
- `Y = C_Y ⊔ I_Y` with `C_Y` a clique and `I_Y` independent.

Because `G[X]` is `K_5`-free:

- `|C_X| <= 4`.

Hence, if `|X| >= 12`, then:

- `|I_X| >= 8`,

which gives an induced `I_8 subseteq X`, contradicting that the whole host is `8`-bad.
So:

- `|X| <= 11`.

Dually, because `G[Y]` is `I_5`-free:

- `|I_Y| <= 4`.

Hence, if `|Y| >= 12`, then:

- `|C_Y| >= 8`,

which gives an induced `K_8 subseteq Y`, again contradicting `8`-badness.
So:

- `|Y| <= 11`.

Therefore:

- `|W| = |X| + |Y| <= 22`.

But:

- `|W| = 64 - |M| >= 50`,

since `9 <= |M| <= 14`.
Contradiction.

### Consequence 28.2

Every surviving `q = 8` small bad module must be:

- induced-`2 K_2`-free.

So the residual family is now:

- `9 <= |M| <= 14`,
- `alpha(M) = omega(M) = 3`,
- `M` contains an induced `C_4`,
- `M` contains no induced `C_5`,
- `M` is induced-`2 K_2`-free,
- and `M` is still `8`-modular and `8`-bad.

Equivalently, the only remaining `4`-vertex regular profile inside `M` is:

- `C_4`,

never `2 K_2`.

In particular, `L(K_{3,3})` is eliminated, since it contains an induced `2 K_2`.

### Proposition 28.3 (the residual branch-(1) family is only `K_{3,3,3}`)

Let `M` be a surviving `q = 8` small-window bad module in the branch-(1) setup of Theorem 17.5.
Then:

- `M ≅ K_{3,3,3}`.

### Proof

By Theorem 17.5, branch (1) comes from a minimal bad module whose top quotient is degenerate, so
`M` is a substitution of regular bags `B_i` of size `< 8`, with top quotient either edgeless or
complete.

If the top quotient were edgeless, then some bag `B` must already contain an induced `C_4`, since
`M` does. Any other bag containing an edge would, together with an opposite edge of that `C_4`,
create an induced `2 K_2`, impossible by Consequence 28.2. So every other bag is independent.
Because `|B| < 8` and `|M| >= 9`, there are at least two vertices outside `B`, and they are
independent from all of `B`. Hence:

- `alpha(M) >= alpha(B) + 2 >= 4`,

contrary to `alpha(M) = 3`.

So the top quotient is complete:

- `M = B_1 vee ... vee B_t`.

Then:

- `omega(M) = sum_i omega(B_i) = 3`,

so `t <= 3`.

Each bag is regular, induced-`2 K_2`-free, and induced-`C_5`-free.

1. If `omega(B_i) = 1`, then `B_i` is independent.
2. If `omega(B_i) = 2`, then `B_i` is triangle-free. A shortest odd cycle in `B_i` would be induced;
   its length cannot be `5`, and any odd cycle of length at least `7` contains an induced `2 K_2`.
   So `B_i` is bipartite. Bipartite induced-`2 K_2`-free graphs are chain graphs, and a regular
   chain graph is exactly `K_{m,m}`.

Since `|B_i| < 8`, the only such regular bags with clique number `2` are:

- `K_{2,2} = C_4`,
- `K_{3,3}`.

Therefore `M` is a complete tripartite graph:

- `M ≅ K_{a,b,c}`

with `a, b, c <= 3`.

Now `alpha(M) = max(a, b, c) = 3`, and:

- `9 <= |M| = a + b + c <= 14`.

The only possibility is:

- `(a, b, c) = (3, 3, 3)`.

So `M ≅ K_{3,3,3}`.

### Proposition 28.4 (`K_{3,3,3}` cannot embed in a `64`-vertex `8`-bad host)

Let `M = K_{3,3,3}` be a module in a `64`-vertex graph `G` whose degrees are all congruent modulo
`8`. Then `G` is not `8`-bad.

### Proof

Keep the notation from Section 22:

- `X := {w outside M : w is complete to M}`,
- `Y := {w outside M : w is anticomplete to M}`.

First choose:

- `A subseteq M` inducing `K_{2,2,2}`.

Then `|A| = 6` and `A` is `4`-regular. By Proposition 22.1, any regular induced `8`-set extending
`A` must have:

- `|B| = 2`,
- and, because `a = 6 > q / 2 - 1 = 3`, the set `B` lies entirely in `X` or entirely in `Y`.

The `Y`-only case is impossible, since it would require a `2`-vertex `4`-regular graph.
In the `X`-only case, Proposition 22.1 gives:

- `deg_B = 4 + 2 - 6 = 0`,

so `B` must be an induced nonedge.

Therefore, if `X` contained any nonadjacent pair, `A ⊔ B` would be a regular induced `8`-set.
Hence:

- `X` is a clique.

Now take an edge:

- `A' subseteq M`

with `|A'| = 2` and `A'` `1`-regular. If `X` contained a clique `K_6`, then Proposition 22.1 in the
`X`-only case would give a regular induced `8`-set, because:

- `deg_B = 1 + 6 - 2 = 5`.

So:

- `X` is `K_6`-free.

Since `X` is itself a clique, this forces:

- `|X| <= 5`.

Therefore:

- `|Y| = 64 - 9 - |X| >= 50`.

Next, `M` contains an independent `3`-set (one whole part of `K_{3,3,3}`).
So if `Y` contained an independent `5`-set, we would get an induced `I_8`.
Hence:

- `alpha(Y) <= 4`.

Also `M` contains an induced `C_4` (take two vertices from each of two parts).
If `Y` contained an induced `C_4`, Proposition 22.1 in the `Y`-only case would produce a regular
induced `8`-set. So:

- `Y` is `C_4`-free.

Write `n := |Y|`, so `n >= 50`.
Because `alpha(Y) <= 4`, the complement `\bar Y` is `K_5`-free. By Turán:

- `e(\bar Y) <= 3 n^2 / 8`.

Hence:

- `e(Y) >= C(n, 2) - 3 n^2 / 8 = n (n - 4) / 8`.

For `n >= 50`, this gives:

- `e(Y) >= 288`.

On the other hand, `Y` is `C_4`-free, so by the Reiman bound:

- `e(Y) <= ex(n, C_4) <= n / 4 * (1 + sqrt(4 n - 3))`.

At `n = 50`, the right-hand side is already less than `188`, and it remains far below `288` for all
`n >= 50`.
Contradiction.

So `K_{3,3,3}` cannot occur as a small bad module in a `64`-vertex `8`-modular host.

### Consequence 28.5

The entire `q = 8` small-window branch is impossible.

So after Sections 27 and 28, the only surviving `q = 8` obstruction is the prime weighted quotient
branch, already reduced to the two active templates `T` and `F` from Consequence 27.9.

## 29. The residual `q = 8` quotient branch is really a labelled induced-subgraph problem

The active-template reduction from Section 27 can be sharpened further.
For the residual cubic branch, one does not need the full universal-profile machinery.
Only the coarse bag labels

- `E` := the bag contains an edge (`rho > 0`),
- `N` := the bag contains a nonedge (`rho < n - 1`)

matter.

Thus:

- a clique bag is `E` but not `N`,
- an independent bag is `N` but not `E`,
- a mixed bag is both `E` and `N`,
- a singleton bag is neither.

### Proposition 29.1 (labelled template forcing)

Let `G = Q[H_v]` be a prime weighted quotient instance in the residual `q = 8` branch.

1. If `Q` contains an induced `C_6 = v_1 ... v_6` and the opposite bags `H_{v_1}` and `H_{v_4}` are
   `E`-bags, then `G` contains the cubic `8`-vertex template `H_T`.
2. If `Q` contains an induced copy of the `7`-vertex template `F` from Proposition 27.8, and the
   center bag is an `N`-bag, then `G` contains the cubic `8`-vertex template `H_F`.

### Proof

For (1), choose an edge from each of the opposite `E`-bags `H_{v_1}` and `H_{v_4}`, and choose one
vertex from each of the four remaining bags on the induced `C_6`.
Because the quotient copy is induced and the selected pairs are edges, the resulting induced
`8`-vertex graph is exactly `H_T`.

For (2), choose a nonedge from the center `N`-bag, and one vertex from each of the remaining six
bags in the induced copy of `F`.
Again the quotient copy is induced, so the resulting induced `8`-vertex graph is exactly `H_F`.

### Consequence 29.2 (the cubic quotient branch is no longer a profile CSP)

A bad prime quotient must avoid:

1. an induced `C_6` whose opposite marked bags are both `E`, and
2. an induced `F` whose center bag is `N`.

So the last `q = 8` quotient branch is not primarily about the fine profile sets `P(H_i)` or even
the universal profiles `U(n_i, rho_i)`.
It is now a **labelled induced-subgraph problem on the prime quotient**.

### Candidate Theorem 29.3 (the labelled-prime quotient theorem for `q = 8`)

Every prime weighted quotient instance for `q = 8` contains at least one of the following:

1. one of the already-settled non-cubic good patterns from Consequence 27.7;
2. an induced `C_6` with opposite `E`-bags;
3. an induced `F` with `N`-center.

Proving this theorem would finish the `q = 8` case.

So the remaining `q = 8` obstruction is now reduced to a much smaller explicit statement:

> classify prime weighted quotients that avoid the non-cubic good patterns, avoid induced `C_6`
> with opposite `E`-bags, and avoid induced `F` with `N`-center.

## 30. Candidate Theorem 29.3 reduces to split spiders and corrected non-split seeds

The labelled-prime quotient statement can be sharpened once more.
To prove Candidate Theorem 29.3, it is enough to rule out two explicit classes of prime quotients.

### Proposition 30.1 (split reduction)

If a prime weighted quotient `Q` is split, then `Q` is a spider (thin or thick) with head size at
most `1`.

If such a spider has `t >= 8` legs, then:

- either the body gives a clique on `8` bags,
- or the legs give an independent set on `8` bags,

so one gets `K_8` or `I_8`, hence a settled non-cubic good pattern.

Therefore the only split quotients that can still matter are prime spiders with:

- `2 <= t <= 7`.

### Proof sketch

The structure theorem for prime split graphs gives the spider description with head size at most `1`.
If there are at least `8` body bags then they form a quotient clique on `8` vertices; if there are at
least `8` leg bags then they form a quotient independent set on `8` vertices.
In either case, taking one whole vertex from each bag yields `K_8` or `I_8`.

### Proposition 30.1A (prime split quotients are already good)

Let `Q` be a prime split quotient for `q = 8`, and write the corresponding weighted instance as:

- `G = Q[H_v]`,

with total bag weight `64`.
Then `G` already contains a settled good pattern.

### Proof

A prime split graph is a spider: body bags are pairwise complete, leg bags are pairwise
anticomplete, and the head has size at most `1`.

If four leg bags are `E`-bags, choose one edge from each of them.
Because the legs are pairwise anticomplete, this gives an induced:

- `4 K_2`.

So at most three leg bags are `E`.
Every other leg bag is independent, and since the legs are pairwise anticomplete, the union of all
those independent legs is itself independent.
Avoiding `I_8` forces that union to have total size at most `7`.
Hence the total leg weight is at most:

- `7 + 3 · 7 = 28`.

Dually, if four body bags are `N`-bags, choose one nonedge from each of them.
Because the bodies are pairwise complete, this gives an induced:

- `overline{4 K_2}`.

So at most three body bags are `N`.
Every other body bag is a clique, and since the bodies are pairwise complete, their union is a
clique.
Avoiding `K_8` forces that clique-union to have total size at most `7`.
Hence the total body weight is at most:

- `7 + 3 · 7 = 28`.

The head contributes at most `7`.
Therefore the total weight is at most:

- `28 + 28 + 7 = 63`,

contradicting the assumed total weight `64`.

So every prime weighted split quotient already forces one of:

- `I_8`,
- `K_8`,
- `4 K_2`,
- `overline{4 K_2}`,

all of which are settled good patterns.

### Proposition 30.2 (non-split reduction to three corrected `5`-seeds)

Suppose `Q` is prime and non-split.
Then `Q` contains an induced prime non-split seed `S` such that:

- `S in {C_5, P_5, bar P_5}`.

Moreover, writing:

- `c_S(v) := sum_{x in Q \ S, x ~ v} n_x [MOD 8]`,

the weighted congruence on `Q` restricts on `S` to:

- `rho(v) + sum_{u in N_S(v)} n_u + c_S(v) ≡ lambda [MOD 8]`.

So the remaining non-split problem is a corrected-seed classification on exactly three prime
`5`-vertex cores.

### Proof sketch

A standard prime/split theorem says that every prime non-split graph contains an induced:

- `P_5`,
- `bar P_5`,
- or `C_5`.

Choose `S` inclusion-minimal among prime non-split induced subgraphs of `Q`.
Then `S` must itself be one of those three graphs.
The displayed congruence is just the quotient degree formula, with all outside neighbors absorbed
into the correction term `c_S(v)`.

### Consequence 30.3 (the non-split `q = 8` branch is a `5`-seed attachment problem)

For the three possible seed types, the congruence system becomes:

1. **`C_5` seed**
   - `rho_i + n_{i-1} + n_{i+1} + c_i ≡ lambda [MOD 8]`.
2. **`P_5` seed**
   - `rho_1 + n_2 + c_1 ≡ rho_2 + n_1 + n_3 + c_2 ≡ ... ≡ rho_5 + n_4 + c_5 ≡ lambda [MOD 8]`.
3. **`bar P_5` seed**
   - the analogous equations read off from the house adjacencies.

So the honest remaining non-split theorem is:

> classify realizable outside attachment types to `C_5`, `P_5`, and `bar P_5` whose weighted
> corrections force neither a settled good pattern nor a labelled `C_6` nor a labelled `F`.

### Consequence 30.4 (the exact remaining `q = 8` barrier)

Candidate Theorem 29.3 now reduces to the conjunction of:

1. **no prime split quotient survives** by Proposition 30.1A, and
2. **corrected `5`-seed attachments over `C_5`, `P_5`, and `bar P_5`**.

So the surviving `q = 8` obstruction is no longer a broad weighted-prime-graph problem.
It has become the finite-looking task:

> classify corrected attachments to the three prime non-split `5`-seeds, under the weighted
> congruence constraint and the labelled `C_6` / `F` avoidance rules.

## 31. The `C_5` seed is either eliminable or reduces to a 16-case clone theorem

Write the cycle seed as:

- `S = v_0 v_1 v_2 v_3 v_4 v_0`.

### Proposition 31.1 (outside attachment types to `C_5`)

Up to the dihedral automorphism group of `C_5`, an outside vertex `x` has one of the following
neighborhood types on `S`:

1. `emptyset` (anticenter),
2. `S` (center),
3. `{v_0}`,
4. `{v_0, v_1}`,
5. `{v_1, v_4}`,
6. `{v_0, v_1, v_4}`,
7. `S \ {v_0, v_2}`,
8. `S \ {v_0}`.

Moreover, four of these types already force a different `5`-seed:

1. `{v_0}` gives an induced `P_5` on `x, v_0, v_1, v_2, v_3`;
2. `{v_0, v_1}` gives an induced `P_5` on `x, v_1, v_2, v_3, v_4`;
3. `S \ {v_0, v_2}` gives an induced `bar P_5` on `x, v_0, v_1, v_3, v_4`;
4. `S \ {v_0}` gives an induced `bar P_5` on `x, v_0, v_1, v_3, v_4`.

So the only outside vertices that preserve the `C_5` seed type are:

- **false clones** of `v_i`, with neighborhood `{v_{i-1}, v_{i+1}}`,
- **true clones** of `v_i`, with neighborhood `{v_{i-1}, v_i, v_{i+1}}`,
- centers,
- anticenters.

In particular, replacing `v_i` by any true or false clone of `v_i` yields another induced `C_5`.

### Consequence 31.2 (congruence collapse on the `C_5` seed)

Let:

- `a_i` be the total outside weight of false clones of `v_i`,
- `b_i` be the total outside weight of true clones of `v_i`,
- `z` be the total outside weight of centers.

Then anticenters contribute nothing, and centers contribute the same amount to every seed vertex.
After absorbing `z` into the common residue, the corrected congruence system becomes:

- `rho_i + n_{i-1} + n_{i+1} + a_{i-1} + a_{i+1} + b_{i-1} + b_i + b_{i+1} ≡ lambda' [MOD 8]`.

So only the clone weights matter.

### Proposition 31.3 (conditional elimination of the `C_5` seed)

Assume the standard prime-graph theorem:

> every prime `{P_5, bar P_5}`-free graph is either split or `C_5`.

Then the `C_5` seed is not an independent remaining branch.
Indeed, any prime non-split quotient larger than `C_5` must contain an induced `P_5` or `bar P_5`.

### Proof

If the quotient contains an outside vertex that is not a center, anticenter, true clone, or false
clone relative to the chosen `C_5`, Proposition 31.1 already produces an induced `P_5` or
`bar P_5`.

So a genuine `C_5`-only obstruction would have every outside vertex among those four `C_5`-preserving
types. Then the whole quotient is `{P_5, bar P_5}`-free.
If it is prime and non-split, the quoted theorem forces the quotient itself to be `C_5`.
But a `5`-vertex quotient cannot carry total bag weight `64`, since every bag has size `< 8`, so the
total weight would be at most `35`.
Contradiction.

### Consequence 31.4 (internal exact barrier for a self-contained `C_5` proof)

If one does not invoke Proposition 31.3, the `C_5` branch still reduces to a tiny finite local
statement.

Choose a true or false clone `x` of `v_0`.
Then `{v_0, x}` is a twin pair relative to the other four seed vertices, so primeness gives a
distinguisher `y`.

Up to the reflection fixing `v_0`, the pair `(x, y)` has only finitely many possibilities:

- `x in {F_0, T_0}`,
- `y` in one of the eight local types `A, C, F_0, F_1, F_2, T_0, T_1, T_2`,

with the edge `x y` forced by whether `y` distinguishes `x` from `v_0`.

So the entire self-contained `C_5` branch collapses to a finite:

- **16-case clone-distinguisher theorem on `S ∪ {x, y}`**.
