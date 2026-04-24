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

### Consequence 17.7 (branch `(1)` is genuinely infinite)

For every dyadic `q >= 8`, let:

- `m := ceil((q + 1) / 3)`,
- `M_q := K_{m, m, m}`.

Then:

1. `q < |M_q| = 3 m <= q + 2 <= 2 q - 2`;
2. every vertex degree in `M_q` is:
   - `2 m`,
   so `M_q` is `q`-modular;
3. every proper module of `M_q` has size `< q`;
4. no induced `q`-vertex subgraph of `M_q` is regular.

So the small bad-module branch from Theorem `17.5` is a genuine infinite family, not a bookkeeping
artifact of the prime weighted quotient reduction.

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

### Proposition 18.4 (exact residual-packet reformulation)

Fix `U` and `m` as above, and write:

- `N := q / 2^m`.

Call a packet `P subseteq V \ U` **`m`-admissible** if there is some residue `a_P` such that

- `Σ_{x in P} c_x ≡ a_P 1_U [MOD 2^m]`.

For such a packet define

- `nu_m(P) := [(Σ_{x in P} c_x - a_P 1_U) / 2^m] in M_N(U)`,

and let:

- `bar nu_m(P) in M_2(U)`

be its reduction modulo `2`.

If:

- `V \ U = ⊔_i P_i`

is any `m`-admissible packet decomposition, then:

- `eta_m(U) = Σ_i nu_m(P_i)`.

Reducing modulo `2`, one gets:

- `bar eta_m(U) = Σ_i bar nu_m(P_i)` in `M_2(U)`.

So the total packet-shadow sum is **independent of the chosen admissible packetization**.
Hence the next dyadic lift on this fixed support is **exactly** equivalent to:

- `eta_m(U) in 2 M_N(U)` if and only if `Σ_i bar nu_m(P_i) = 0` in `M_2(U)`.

Equivalently:

- `eta_m(U) in 2 M_N(U)` if and only if `bar eta_m(U) = 0`.

So the top-bit theorem is precisely the vanishing of the **decomposition-independent** packet-shadow
sum `bar eta_m(U)` in `M_2(U)`.

### Consequence 18.5 (Section 18 data do not force packet-shadow cancellation)

The residual-packet reformulation is exact, but it is not automatic.

In the obstruction from Theorem `18.2`, the outside columns are only:

- `0`,
- `1`,
- `d := 1 - e_0`,

with `d` repeated exactly:

- `q - 2^m = 2^m (N - 1)`

times.

For any `m`-admissible packet `P`, if `b(P)` denotes the number of `d`-columns in `P`, then:

- admissibility forces `b(P) ≡ 0 [MOD 2^m]`,
- and `bar nu_m(P)` is either `0` or the same nonzero class
  `bar alpha`, where `alpha := [(0, 1, ..., 1)] in M_N(U)`.

So in every `m`-admissible packetization of `V \ U`, all nonzero packet shadows are identical, and
their total sum is:

- `(N - 1) bar alpha = bar alpha != 0`.

Therefore no `m`-admissible packet decomposition has zero-sum packet shadows.

So Section `18`'s current data do **not** force the next top bit of `eta_m(U)` to vanish.

The exact missing dyadic theorem is therefore simply:

> for some fixed support `U`, prove that
> - `bar eta_m(U) = 0`
> in `M_2(U)`.

Equivalently, fixing any basepoint:

- `u_0 in U`,

this is exactly the **pairwise next-bit compensation theorem**:

- `r_U(u) - r_U(u_0) ≡ 0 [MOD 2^(m+1)]` for every `u in U`.

In dual form, if:

- `delta_u : M_2(U) -> F_2`

denotes the functional:

- `delta_u(x) := x(u) + x(u_0)` for `u != u_0`,

then these `delta_u` form a basis of `M_2(U)^*`, and:

- `bar eta_m(U) = 0` if and only if `delta_u(bar eta_m(U)) = 0` for every `u != u_0`.

Packetwise, `delta_u(bar nu_m(P))` is exactly the parity of whether the packet shadow separates the
pair `{u, u_0}`. So the exact basis-level reduction is the **pair-cut packet parity theorem**:

> for every `u != u_0`, packets with odd `{u, u_0}`-shadow occur with even parity.

The packet language remains useful only as a way to force that vanishing. In particular, one now
needs genuine control on the **distribution of packet shadows**, not merely the fact that deleted
layers are harmless through the first `m` bits.

A sharper reading of the current bookkeeping is:

1. for each `u != u_0`,
   - `delta_u(bar eta_m(U)) = (r_U(u) - r_U(u_0)) / 2^m`
     in `F_2`;
2. if a block `D` already has constant external degree modulo `q = 2^j` on `U`, then for every
   `m < j`,
   - `(|N(u) ∩ D| - |N(u_0) ∩ D|) / 2^m ≡ 0 [MOD 2]`;
   so every already-separated control / cascade block is `delta_u`-silent;
3. letting `R` denote the final undecomposed tail and
   - `rho_R(u) := |N(u) ∩ R|`,
   the frozen first `m` bits imply
   - `rho_R = K_m 1_U + 2^m h_m`
     on `U`;
4. therefore the exact unresolved one-functional theorem is already **terminal-tail only**: prove that
   the terminal-tail class
   - `tau_m(R, U) := [h_m mod 2]`
     vanishes in `M_2(U)`;
   equivalently,
   - `rho_R = K_(m+1) 1_U + 2^(m+1) h_(m+1)`;
5. equivalently, the normalized difference cocycle
   - `kappa_m(u, v) := (rho_R(u) - rho_R(v)) / 2^m [MOD 2]`
   vanishes identically; fixing a basepoint `u_0`, this is exactly the basis family
   - `rho_R(u) - rho_R(u_0) ≡ 0 [MOD 2^(m+1)]`
     for all `u in U`;
6. if `n_A := # {x in R : N(x) ∩ U = A}` and
   - `n_A = 2^m q_A + r_A`
     with `0 <= r_A < 2^m`,
   then
   for pair-cut functionals only complement-orbits matter: if
   - `chi_A(u, v) = 1`
     exactly when one of `u, v` lies in `A`, then
   - `kappa_m(u, v) = Σ_[A] floor((n_A + n_(U \ A)) / 2^m) chi_A(u, v) [MOD 2]`,
     where the sum runs over complement-pairs `[A] = {A, U \ A}`;
7. equivalently, the aggregate complement-orbit class is
   - `beta_m := Σ_[A] epsilon_[A] [1_A]`
     where
   - `epsilon_[A] := floor((n_A + n_(U \ A)) / 2^m) [MOD 2]`,
   and one has
   - `kappa_m = partial beta_m`;
8. hence
   - `kappa_m = 0`
     if and only if
   - `beta_m = 0`,
   equivalently if and only if the symmetric difference of the active complement-orbits is either
   `∅` or `U` (equivalently, active-orbit incidence parity is constant on `U`);
9. the visible top digit and the pure carry do not vanish separately: they cancel **inside each
   complement pair** via
   - `floor((n_A + n_(U \ A)) / 2^m) ≡ q_A + q_(U \ A) + floor((r_A + r_(U \ A)) / 2^m) [MOD 2]`;
10. raw parity pairing on vertices of `R` is too weak for `m >= 1`: parity-only arguments miss exactly
   the carry contribution `floor((r_A + r_(U \ A)) / 2^m)`.

So individual orbit coefficients do **not** need to vanish. The smallest exact complement-orbit
statement is the triviality of the aggregate class `beta_m`.

Equivalently, one still needs a dyadic row-divisibility chain for the tail profile `rho_R`, and
packet shadows remain only a language for forcing that last tail cancellation.

Low-rank shadow space by itself is **not** enough: the standard obstruction from Theorem `18.2`
already has all nonzero packet shadows in a `1`-dimensional subspace while still giving

- `bar eta_m(U) != 0`.

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

In fact the stronger universal target

> for each regular induced `A subseteq M` with `|A| = a < q`, must the outside graph contain a
> `(q - a)`-vertex `X / Y`-colored induced subgraph with the required degree pattern?

is false.

Indeed, by Proposition `22.1`, a regular induced `A subseteq M` of size `a` and internal degree
`alpha` can be completed only if at least one of the following holds:

- mixed `X / Y` completion: `a <= q / 2 - 1`;
- `Y`-only completion: `alpha <= q - a - 1`;
- `X`-only completion: `alpha >= 2 a - q`.

So there is a dead zone

- `a > q / 2 - 1` and `q - a <= alpha < 2 a - q`

in which no completion exists, regardless of the outside graph.

Section `17`'s family

- `M_q := K_{m,m,m}`, with `m := ceil((q + 1) / 3)`,

already contains such a regular piece. Take `A` to be the union of two parts, so

- `A ≅ K_{m,m}`,
- `a = 2 m`,
- `alpha = m`,
- `q - a = q - 2 m ∈ {m - 1, m - 2}`.

Then:

- mixed completion is impossible because `a > q / 2 - 1`;
- `Y`-only completion would require an `m`-regular graph on at most `m - 1` vertices;
- `X`-only completion would require degree `q - 3 m ∈ {-1, -2}`.

So this `A` is intrinsically uncompletable.

Thus the honest small-window branch-`(1)` theorem is **existential in `A`**, not universal:

> given a `q`-modular host `G` and a `q`-bad module `M` with `q + 1 <= |M| <= 2 q - 2`, either
> `G[W]` already contains a regular induced `q`-set, or there exists some regular induced
> `A subseteq M` and some `B subseteq W` with `|A| + |B| = q` such that, writing
> `a := |A|`, `alpha := deg_A`, and `s := |B ∩ X|`,
>
> - `deg_B(x) = alpha + s - a` for `x in B ∩ X`,
> - `deg_B(y) = alpha + s` for `y in B ∩ Y`.

Equivalently, the missing theorem is a host-side **admissible-`A` / `X / Y` completion theorem**:
the extra host structure must either find the regular `q`-set entirely outside `M`, or force at
least one extendable regular induced `A subseteq M`.

More sharply, branch-`(1)` depends on the choice of regular `A` only through its profile

- `(a, alpha) := (|A|, deg_A)`.

For each size `a`, define the extremal regular degrees

- `alpha_min(a) := min {alpha : exists alpha-regular induced A subseteq M with |A| = a}`,
- `alpha_max(a) := max {alpha : exists alpha-regular induced A subseteq M with |A| = a}`.

Then:

1. some `Y`-only completion of size `a` exists if and only if
   - `alpha_min(a) <= q - a - 1`;
2. some `X`-only completion of size `a` exists if and only if
   - `alpha_max(a) >= 2 a - q`;
3. mixed completion depends only on `a`, namely
   - `a <= q / 2 - 1`.

So the next exact small-window theorem is not an existential theorem over arbitrary regular
`A subseteq M`, but a **profile-completion theorem**, indeed already an **extremal-profile
completion theorem**.

Two positive slices are immediate:

- if `M` contains an independent set `I_a` with `a > q / 2`, then any completion must be `Y`-only,
  so the outside task collapses to finding an independent `(q - a)`-set in `Y`;
- if `M` contains a clique `K_a` with `a > q / 2`, then any completion must be `X`-only, so the
  outside task collapses to finding a clique `K_(q - a)` in `X`.

It is cleaner to rewrite in terms of codimension

- `s := q - a`.

For `a > q / 2` (equivalently `s < q / 2`), mixed completion is impossible, so one needs purely:

- `Y`-side completion from some
  - `alpha in P_M(q - s) ∩ RegDeg(s)`;
- or `X`-side completion from some
  - `alpha in P_M(q - s) ∩ (q - 2 s + RegDeg(s))`,

where `P_M(t)` is the realized regular-degree set on `t`-vertex induced regular subgraphs of `M`, and
`RegDeg(s)` is the set of regular degrees realizable on `s` vertices.

So `alpha_min(a)` and `alpha_max(a)` give only **window compatibility** inside `M`; they do not by
themselves solve the outside realization problem.

The first codimensions collapse quickly:

1. `s = 1`: trivial;
2. `s = 2`: exact theorem is easy, since regular `2`-sets are only edge / nonedge;
3. `s = 3`: still Ramsey-level, since regular `3`-sets are only `I_3` or `K_3`.

Thus the first genuinely new case is:

> **codimension-4 completion theorem**.

Indeed the regular `4`-vertex targets are exactly:

- `I_4`,
- `2 K_2`,
- `C_4`,
- `K_4`.

If `A subseteq M` is induced `alpha`-regular with `|A| = q - 4`, and `B subseteq W` has `|B| = 4`,
then Proposition `22.1` gives:

- `deg_B(x) = alpha + s - (q - 4)` for `x in B ∩ X`,
- `deg_B(y) = alpha + s` for `y in B ∩ Y`,

where `s := |B ∩ X|`.

So if `1 <= s <= 3`, then:

- `deg_B(y) - deg_B(x) = q - 4 >= 4`,

which is impossible on a `4`-vertex graph. Therefore mixed completion is impossible for codimension
`4` (for `q >= 8`), and only pure `X`- or pure `Y`-side completions remain.

Hence the feasible internal degrees are exactly:

- `alpha in {0, 1, 2, 3}` on the `Y`-side,
- `alpha in {q - 8, q - 7, q - 6, q - 5}` on the `X`-side,

with the outside target determined by:

- `0` / `q - 8`  <->  `I_4`,
- `1` / `q - 7`  <->  `2 K_2`,
- `2` / `q - 6`  <->  `C_4`,
- `3` / `q - 5`  <->  `K_4`.

So codimension `4` is already completely classified. The only genuine ambiguity is overlap between the
two degree windows.

If `q >= 12`, the windows are disjoint, so `alpha` alone already forces the side and the outside
target. Therefore the next exact smaller theorem is:

> **overlap-profile resolution** for `q in {9, 10, 11}`.

In the current `q = 8` bad-module branch the windows coincide, and the surviving internal
`4`-vertex regular profile is `C_4`, so the codimension-`4` problem there collapses to:

> the outside `4`-set must also be a `C_4` (in `X` or in `Y`).

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

### Proposition 31.5 (clone-fiber closure lemma)

Fix:

- `K := S \ {v_0} = v_1 - v_2 - v_3 - v_4`,

and define the position-`0` clone fiber:

- `D_0 := {u : N_K(u) = {v_1, v_4}}`.

This contains:

- `v_0`,
- every false clone of `v_0`,
- every true clone of `v_0`.

Take:

- `p, q in D_0`,

and let:

- `y`

distinguish `p` and `q`.
Then:

- `y in D_0`.

### Proof

The cycle:

- `p - v_1 - v_2 - v_3 - v_4 - p`

is again an induced `C_5`.
Relative to this reseated cycle:

- `q` is a false clone of `p` iff `p q = 0`,
- `q` is a true clone of `p` iff `p q = 1`.

Now apply Proposition `31.1` to `y` on that reseated cycle.
If `y` is not a clone of `p`, then it has one of the six remaining local types.
Because `y` distinguishes `p` from `q`, each of those six types immediately reseeds:

1. anticenter gives a singleton-at-`p` attachment, hence an induced `P_5`;
2. center gives a complement-of-singleton attachment, hence an induced `bar P_5`;
3. the `F_1` type gives a singleton middle attachment, hence an induced `P_5`;
4. the `T_1` type gives a consecutive-pair attachment, hence an induced `P_5`;
5. the `F_2` type gives a complement-of-nonadjacent-pair attachment, hence an induced `bar P_5`;
6. the `T_2` type gives a complement-of-singleton attachment, hence an induced `bar P_5`.

So the only distinguishers that survive are again the clone types of `p`, i.e. the vertices of
`D_0`.

### Consequence 31.6 (internal elimination of the `C_5` seed)

Let `Q` be a prime non-split graph containing an induced `C_5`:

- `S = v_0 v_1 v_2 v_3 v_4 v_0`,

and assume `Q` contains no induced `P_5` or `bar P_5`.
Then:

- `Q = S`.

### Proof

By Proposition `31.1`, every outside vertex is either:

1. a center,
2. an anticenter,
3. a true clone of some `v_i`,
4. or a false clone of some `v_i`.

If every clone fiber `D_i` is trivial, then every outside vertex is a center or anticenter, hence is
uniform on `S`.
So `S` is a nontrivial module of `Q`, contradicting primeness unless `Q = S`.

Therefore some `D_i` is nontrivial.
By rotation symmetry, take `i = 0`.
Proposition `31.5` says that every distinguisher of two vertices in `D_0` also lies in `D_0`.
So every vertex outside `D_0` is uniform on `D_0`, i.e. `D_0` is a proper nontrivial module of `Q`.
Again this contradicts primeness.

Hence the only prime `{P_5, bar P_5}`-free graph containing an induced `C_5` is `C_5` itself.

### Consequence 31.7 (the `C_5` seed is not independent)

The `C_5` seed is not an independent remaining branch.
Any prime non-split graph larger than `C_5` that contains an induced `C_5` must already contain an
induced `P_5` or `bar P_5`.

## 32. The house seed reduces to four exceptional orbit families

Write the house seed as the `4`-cycle:

- `a - b - c - d - a`,

with roof:

- `r ~ b, c`.

Define the two skew correction parameters:

- `alpha := c_a - c_d`,
- `beta := c_b - c_c`.

From the weighted congruence on the seed:

- `alpha ≡ (rho_d - rho_a) + (n_a + n_c - n_b - n_d) [MOD 8]`,
- `beta ≡ (rho_c - rho_b) + (n_b + n_d - n_a - n_c) [MOD 8]`.

### Proposition 32.1 (one-vertex reseeding from the house)

The only `4`-vertex induced subgraphs of the house that can extend to a `P_5` or `C_5` are the two
paths:

- `d - a - b - r`,
- `a - d - c - r`.

Hence an outside vertex `x` immediately reseeds to `P_5` or `C_5` if:

1. `N_S(x) ∩ {d, a, b, r}` is one of
   - `{d}`, `{r}`, `{d, r}`;
2. or `N_S(x) ∩ {a, d, c, r}` is one of
   - `{a}`, `{r}`, `{a, r}`.

Up to the house automorphism `(a d)(b c)`, the forbidden one-vertex orbits are:

- `{r}`,
- `{a}`,
- `{a, b}`,
- `{a, r}`,
- `{b, r}`,
- `{a, b, r}`.

### Consequence 32.2 (surviving house orbit types)

After removing the immediate `P_5 / C_5` reseeding orbits, the remaining outside attachment orbits
split into three classes.

1. **Trivial orbits**
   - `emptyset`,
   - `S`.

2. **House-reseating orbits**, each of which produces another induced house on `x` plus four seed
   vertices:
   - `{a, c}`,
   - `{a, b, d}`,
   - `{a, c, r}`,
   - `{a, b, c, r}`,
   - `{b, c}`,
   - `{b, c, r}`,
   - `{a, d}`,
   - `{a, d, r}`.

3. **Exceptional orbits**
   - `B := {b} ~ {c}`,
   - `T := {a, b, c} ~ {b, c, d}`,
   - `U := S \ {b} ~ S \ {c}`,
   - `Q := S \ {r}`.

So after quotienting out trivial and house-reseating attachments, only the four exceptional orbit
families `B, T, U, Q` remain.

### Consequence 32.3 (congruence collapse on the exceptional house orbits)

Let:

- `u_b, u_c` be the total outside weights in the two `B`-orbits,
- `t_b, t_c` the total outside weights in the two `T`-orbits,
- `v_b, v_c` the total outside weights in the two `U`-orbits,
- `q` the total outside weight in the `Q`-orbit.

Then, modulo the house-reseating part:

- `alpha ≡ t_b - t_c [MOD 8]`,
- `beta ≡ u_b - u_c + v_c - v_b [MOD 8]`.

The `Q`-orbit changes only the common constant part and can be absorbed into `lambda`.

### Consequence 32.4 (the exact remaining house barrier)

The `bar P_5` branch is now a finite local theorem on only:

- the four exceptional orbit families `B, T, U, Q`,
- the two skew residues `(alpha, beta)`,
- and the labelled `C_6 / F` avoidance rules.

So the house seed is not eliminated, but it has collapsed to a very small explicit attachment
theorem.

## 33. Two genuinely general theorems extracted from the `q = 8` analysis

The `q = 8` case study should not be treated merely as a terminal finite grind.
Two of its main outputs in fact generalize cleanly to arbitrary even modulus `q`.

### Proposition 33.1 (general prime split weighted quotients are always good)

Let `q >= 4` be even, and let:

- `G = Q[H_v]`

be a weighted quotient instance such that:

1. `Q` is prime and split,
2. every bag has size `< q`,
3. the total bag weight is `q^2`.

Then `G` contains an induced regular subgraph on exactly `q` vertices.

### Proof

Because `Q` is prime and split, it is a spider: its body bags are pairwise complete, its leg bags
are pairwise anticomplete, and the head has size at most `1`.

Call a bag an `E`-bag if it contains an edge, and an `N`-bag if it contains a nonedge.

If there were `q / 2` leg bags that are `E`-bags, choose one edge from each of them.
Since distinct leg bags are pairwise anticomplete, this would give an induced:

- `(q / 2) K_2`,

which is `1`-regular on `q` vertices.
Therefore at most `q / 2 - 1` leg bags are `E`.

Every remaining leg bag is independent.
Since the legs are pairwise anticomplete, the union of all those independent leg bags is itself
independent.
Avoiding an induced `I_q` forces the total weight of the non-`E` legs to be at most `q - 1`.
Each `E`-leg bag has size at most `q - 1`, so the total leg weight is at most:

- `(q - 1) + (q / 2 - 1) (q - 1) = (q / 2) (q - 1)`.

Dually, if there were `q / 2` body bags that are `N`-bags, choose one nonedge from each of them.
Since distinct body bags are pairwise complete, this gives an induced:

- `overline{(q / 2) K_2}`,

which is `(q - 2)`-regular on `q` vertices.
Therefore at most `q / 2 - 1` body bags are `N`.

Every remaining body bag is a clique.
Since the body bags are pairwise complete, the union of all those clique bags is itself a clique.
Avoiding an induced `K_q` forces the total weight of the non-`N` body bags to be at most `q - 1`.
Hence the total body weight is also at most:

- `(q / 2) (q - 1)`.

Finally the head contributes at most one bag, of size at most `q - 1`.
So the total bag weight is at most:

- `(q / 2) (q - 1) + (q / 2) (q - 1) + (q - 1) = q^2 - 1`,

contradicting the assumed total weight `q^2`.

So some induced regular `q`-vertex subgraph must already exist.

### Consequence 33.2 (the split prime quotient branch is dead in general)

For every even `q`, the prime weighted quotient branch of the last-gap problem can ignore split
quotients entirely.

They are always already good before any residue or profile analysis.

### Proposition 33.3 (general elimination of the `C_5` seed)

Let `q >= 4`, and let `Q` be a prime non-split weighted quotient with:

- total bag weight `q^2`,
- every bag of size `< q`.

Then `Q` cannot have `C_5` as its only prime non-split seed.
It must contain an induced `P_5` or `bar P_5`.

### Proof

Fix an induced `C_5` in `Q`.
By Proposition 31.1, any outside vertex that is not a center, anticenter, true clone, or false
clone of that cycle already produces an induced `P_5` or `bar P_5`.

So if `Q` had no induced `P_5` or `bar P_5`, every outside vertex would have to be one of those
four `C_5`-preserving types.
Then the underlying prime graph of `Q` would be `{P_5, bar P_5}`-free and would contain an induced
`C_5`.
By Consequence `31.6`, that underlying graph would have to be `C_5` itself.

But a `5`-vertex quotient with all bags of size at most `q - 1` has total weight at most:

- `5 (q - 1)`,

and for every `q >= 4` one has:

- `5 (q - 1) < q^2`.

So `Q` cannot have total weight `q^2`.
Contradiction.

### Consequence 33.4 (general seed frontier)

By Proposition `33.3`, the general non-split prime quotient branch no longer needs a separate
`C_5` seed theorem.

The honest remaining general seed-attachment frontier is:

- `P_5`,
- and `bar P_5`.

In other words, the `q = 8` analysis does suggest a real general theorem shape:

> kill split prime quotients by a uniform weight count,
> eliminate `C_5` by prime-graph structure,
> and attack the last gap through weighted attachment theorems over `P_5` and `bar P_5`.

### Proposition 33.5 (weighted quotient complementation)

Let `G = Q[H_v]` be a weighted quotient instance at modulus `q`.
Then:

- `bar G = bar Q[bar H_v]`.

Moreover:

1. bag sizes are unchanged;
2. primeness of the quotient is unchanged;
3. if the weighted degree congruence on `Q` is
   - `rho(v) + sum_{u ~ v} n_u ≡ lambda [MOD q]`,
   then on `bar Q` it becomes
   - `(n_v - 1 - rho(v)) + sum_{u not~ v} n_u ≡ -1 - lambda [MOD q]`;
4. an induced regular `q`-set in `G` is equivalent to an induced regular `q`-set in `bar G`.

So the weighted prime-quotient problem is complement-invariant.

### Consequence 33.6 (the `P_5` branch is not independent)

Every general `P_5`-seed instance is equivalent by complementation to a
`bar P_5`-seed instance.

So the general non-split prime quotient frontier is not really:

- `P_5` and `bar P_5`,

but just:

- `bar P_5`.

### Proposition 33.7 (direct local collapse of the `P_5` branch)

Even without appealing immediately to complementation, the one-vertex attachment analysis on `P_5`
already collapses almost completely.

Up to reflection of the path `1 - 2 - 3 - 4 - 5`, the only surviving nontrivial outside attachment
families are:

- `M := {3}`,
- `T := {2, 3} ~ {3, 4}`,
- `B := {1, 2, 3, 4} ~ {2, 3, 4, 5}`.

All other one-vertex orbits are either:

1. trivial (`emptyset`, `S`),
2. immediate `P_5`,
3. or immediate `C_5 / bar P_5`.

If:

- `m` is the total outside weight in the `M`-orbit,
- `t_2, t_4` are the total outside weights in the two `T`-orbits,
- `b_1, b_5` are the total outside weights in the two `B`-orbits,

then, modulo a common constant, the correction vector is:

- `(c_1, ..., c_5) ≡ (b_1, t_2 + b_1 + b_5, m + t_2 + t_4 + b_1 + b_5, t_4 + b_1 + b_5, b_5)`.

Equivalently the adjacent difference equations are:

- `delta_12 = t_2 + b_5`,
- `delta_23 = m + t_4`,
- `delta_34 = - (m + t_2)`,
- `delta_45 = - (t_4 + b_1)`.

So if one insists on a direct `P_5` theorem, the exact remaining local statement is already a
finite theorem on the three orbit families `M, T, B`.

### Consequence 33.8 (the actual general prime-quotient frontier)

Combining Propositions 33.1, 33.3, and 33.5, the general weighted prime-quotient problem has now
collapsed to a single genuine seed family:

- the house / `bar P_5` branch.

So the cleanest current general theorem target is:

> classify weighted attachments to a prime house seed under the modular weighted-degree equations,
> then show that every such attachment already yields a regular induced `q`-set.

## 34. The general house branch reduces to reseating plus a stable exceptional theorem

Let the house seed be:

- `a - b - c - d - a`,

with roof:

- `r ~ b, c`.

Write `tau := (a d)(b c)` for the house automorphism.

### Proposition 34.1 (general outside-vertex trichotomy for the house)

For every outside vertex `x`, up to the automorphism `tau`, exactly one of the following holds.

1. **Trivial**
   - `N_S(x) = emptyset`,
   - or `N_S(x) = S`.
2. **`P_5 / C_5` reseeding**
   - `{r}`,
   - `{a}`,
   - `{a, b}`,
   - `{a, r}`,
   - `{b, r}`,
   - `{a, b, r}`.
3. **House-reseating**
   - `{a, c}`,
   - `{a, b, d}`,
   - `{a, c, r}`,
   - `{a, b, c, r}`,
   - `{b, c}`,
   - `{b, c, r}`,
   - `{a, d}`,
   - `{a, d, r}`.
4. **Exceptional**
   - `B_b := {b}`,
   - `B_c := {c}`,
   - `T_b := {a, b, c}`,
   - `T_c := {b, c, d}`,
   - `U_b := S \ {b}`,
   - `U_c := S \ {c}`,
   - `Q_0 := S \ {r}`.

Thus the genuine general house branch is:

- a house-reseating automaton,
- plus the seven exceptional orbit types above.

### Consequence 34.2 (stable house seeds)

Call a house seed **stable** if there are no outside vertices of house-reseating type relative to it.

Then every general house-seed instance reduces to two separate problems:

1. a **reseating-descent theorem**, showing that repeated house-reseating can be replaced by a stable
   house seed (or by an already-good configuration);
2. a **stable exceptional house theorem**, where all outside vertices lie only in the trivial or
   exceptional orbit families.

### Proposition 34.3 (stable exceptional congruence system)

Assume the house seed is stable.
Let:

- `Z` be the total outside weight in the center orbit `S`,
- `B_b, B_c, T_b, T_c, U_b, U_c, Q_0`

denote the total outside weights in the seven exceptional orbit types.

Then the seed congruences are exactly:

- `rho_a + n_b + n_d + Z + Q_0 + T_b + U_b + U_c ≡ lambda [MOD q]`,
- `rho_d + n_a + n_c + Z + Q_0 + T_c + U_b + U_c ≡ lambda [MOD q]`,
- `rho_b + n_a + n_c + n_r + Z + Q_0 + B_b + T_b + T_c + U_c ≡ lambda [MOD q]`,
- `rho_c + n_b + n_d + n_r + Z + Q_0 + B_c + T_b + T_c + U_b ≡ lambda [MOD q]`,
- `rho_r + n_b + n_c + Z + U_b + U_c ≡ lambda [MOD q]`.

### Consequence 34.4 (the skew sector)

From the previous system, the skew correction parameters satisfy:

- `alpha := c_a - c_d ≡ T_b - T_c [MOD q]`,
- `beta := c_b - c_c ≡ (B_b - B_c) + (U_c - U_b) [MOD q]`.

So the orbit families `T_b, T_c` control the `a/d` skew, while `B_b, B_c, U_b, U_c` control the
`b/c` skew.

### Consequence 34.5 (the exact remaining general barrier)

The general prime-quotient branch is therefore reduced to exactly this:

> **Stable exceptional house theorem, plus reseating descent.**
>
> Show that every prime weighted attachment to a stable house seed using only
> `emptyset, S, B_b, B_c, T_b, T_c, U_b, U_c, Q_0` and satisfying the displayed congruences is
> already good.

What is still missing is the control of the **symmetric sector** of that stable system; the skew
equations alone do not yet finish the argument.

## 35. The stable exceptional house system has only one genuine `tau`-even parameter

Keep the stable house setup from Section 34, and define:

- `P_b := B_b - U_b`,
- `P_c := B_c - U_c`,
- `t := T_b + T_c`,
- `p := P_b + P_c`.

### Proposition 35.1 (stable-house correction vector)

Modulo constants on the seed, the correction vector is:

- `(c_a - c_r, c_b - c_r, c_c - c_r, c_d - c_r) ≡ (Q_0 + T_b, Q_0 + t + P_b, Q_0 + t + P_c, Q_0 + T_c)`.

Hence:

- `alpha = T_b - T_c`,
- `beta = P_b - P_c`.

So the skew sector is already completely controlled by:

- the `T_b / T_c` imbalance,
- and the `P_b / P_c` imbalance.

### Proposition 35.2 (the symmetric equations)

Adding and subtracting the five seed congruences gives two independent `tau`-even equations:

- `2 Q_0 + t ≡ kappa_1 [MOD q]`,
- `p + t ≡ kappa_2 [MOD q]`,

where:

- `kappa_1 := - (rho_a + rho_d - 2 rho_r + n_a + n_d - n_b - n_c)`,
- `kappa_2 := - (rho_b + rho_c - rho_a - rho_d + 2 n_r)`.

So after the skew data are fixed, the symmetric sector is governed only by:

- `Q_0`,
- `p`,
- `t`,

subject to those two congruences.

### Proposition 35.3 (seed-invisible null directions)

The seed-pattern identities are exact:

- `B_b + U_b = S`,
- `B_c + U_c = S`,
- `T_b + T_c = Q_0 + B_b + B_c`.

Therefore:

- `Z`,
- `B_b + U_b`,
- `B_c + U_c`

are seed-invisible null directions.

So the stable exceptional system is not really a `7`-parameter problem.

### Consequence 35.4 (the true stable-house obstruction)

After quotienting out the null directions and fixing the skew pair `(alpha, beta)`, the stable
exceptional system has only one genuine `tau`-even affine parameter left, which may be taken to be:

- `t = T_b + T_c`.

Necessarily:

- `t ≡ alpha [MOD 2]`,
- `p ≡ beta [MOD 2]`.

So the exact remaining stable-house theorem is:

> **`tau`-even stable-house theorem.**
>
> Control the single symmetric parameter `t` (equivalently the `tau`-even residual class) in every
> prime weighted attachment to a stable house seed.

In particular, congruences alone do not finish the proof: the true remaining obstruction is exactly
this one-parameter `tau`-even sector.

## 36. Reseating descent reduces to 16 local `7`-vertex templates

Let `S` be a house seed, and let `x` be a house-reseating vertex.
Choose a reseated house `S'` using `x`.
Then `S'` shares exactly four vertices with `S` and omits a unique vertex `v in S`.

### Proposition 36.1 (all reseating moves are one-vertex swaps)

The eight house-reseating orbits collapse to three seed roles:

- `corner`,
- `shoulder`,
- `roof`,

together with one bit `epsilon in {0,1}` recording whether:

- `x ~ v`.

So there are only six double-house templates:

- `D_(corner,0)`,
- `D_(corner,1)`,
- `D_(shoulder,0)`,
- `D_(shoulder,1)`,
- `D_(roof,0)`,
- `D_(roof,1)`.

### Consequence 36.2 (one-step descent is never final)

In the reseated house `S'`, the omitted vertex `v` is itself again a house-reseating vertex of the
same role-type.

So `S union {x}` alone never yields final stability.

### Proposition 36.3 (primality forces a distinguisher)

If `Q` is prime, then the pair `{v, x}` cannot be a module.
Hence there exists a vertex:

- `y notin S union {x}`

such that:

- `y v != y x`.

Thus every failure of reseating descent is already witnessed on at most `7` vertices:

- one of the six double-house templates,
- plus one distinguisher `y`.

### Proposition 36.4 (overlap-trace reduction)

Let `O := S cap S'` be the common `4`-vertex overlap, and write:

- `A := N(y) cap O`.

After swapping `x` and `v` if necessary, assume:

- `y x = 1`,
- `y v = 0`.

Then relative to the two houses:

- `y` sees `A` on `H_v := O union {v}`,
- `y` sees `A union {x}` on `H_x := O union {x}`.

So if either `A` or `A union {x}` is an immediate bad house trace, we already fall into:

1. immediate `P_5 / C_5` reseeding, or
2. the exceptional stable sector.

Hence any genuine counterexample lies in the intersection of the non-bad traces for both houses.

### Consequence 36.5 (the first local reseating barrier)

That intersection is explicit and finite.
The only overlap traces where `y` is reseating for both houses are:

1. **corner**
   - `{b, d}`,
   - `{b, c, r}`;
2. **shoulder**
   - `{a, d}`,
   - `{a, c, r}`;
3. **roof**
   - `{a, c}`,
   - `{b, d}`,
   - `{a, d}`,
   - `{b, c}`.

Therefore the genuinely hard reseating residue is only:

- `8` double-reseating overlap traces,

and hence:

- `16` local `7`-vertex templates after the bit `epsilon in {0,1}` is included.

### Proposition 36.6 (symmetry reduction from `16` to `12`)

The `16` templates reduce further by the internal symmetries of the overlap graph.

1. **Roof role.**
   The overlap is a `C_4`, so `D_(roof, epsilon)` has an automorphism exchanging the two roof-swap
   diagonals and the two roof-swap edges.
   Hence:
   - `{a, c}` is equivalent to `{b, d}` (diagonal type),
   - `{a, d}` is equivalent to `{b, c}` (edge type).
   So the roof role contributes only:
   - `2` trace types, not `4`.

2. **Corner / shoulder roles.**
   The overlap is a `P_4`, whose only symmetry is reversal.
   That symmetry preserves trace size, so the two hard traces in each role remain distinct:
   - corner: `{b, d}` and `{b, c, r}`,
   - shoulder: `{a, d}` and `{a, c, r}`.

So the symmetry-reduced local list is:

- `corner-2`,
- `corner-3`,
- `shoulder-2`,
- `shoulder-3`,
- `roof-diagonal`,
- `roof-edge`,

each with:

- `epsilon in {0, 1}`.

### Consequence 36.7 (the exact local reseating barrier)

The double-reseating theorem is therefore a finite local theorem on only:

- `12` explicit local `7`-vertex templates.

To finish reseating descent, it now suffices to show that each of those `12` templates either:

1. gives immediate `P_5 / C_5` reseeding,
2. lands in the stable exceptional sector,
3. or contradicts primeness/module structure.

### Proposition 36.8 (`12 -> 5` by direct reseating)

Using canonical `x`-roles

- corner: `x ~ {b, d}` or `{a, b, d}`,
- shoulder: `x ~ {a, c, r}` or `{a, b, c, r}`,
- roof: `x ~ {b, c}` or `{b, c, r}`,

and reseating on `y`, one gets the following direct reductions.

1. **corner-2**
   - `y ~ {b, d}` gives a new house `y b c d r`,
   - and `x` becomes corner with `epsilon = 1`.

2. **corner-3**
   - `y ~ {b, c, r}` gives a new house `a b c d y`,
   - if `epsilon = 0`, then `x` becomes shoulder with `epsilon = 1`,
   - if `epsilon = 1`, then `x in U_c`, an exceptional off-ramp.

3. **shoulder-2**
   - `y ~ {a, d}` gives a new house `a b c d y`,
   - if `epsilon = 0`, then `x` becomes shoulder with `epsilon = 1`,
   - if `epsilon = 1`, then `x in T_b`, an exceptional off-ramp.

4. **shoulder-3**
   - `y ~ {a, c, r}` gives a new house `a y c d r`,
   - and `x` becomes shoulder with `epsilon = 1`.

5. **roof diagonal / edge**
   - reseating on `y` always gives `a b c d y`,
   - and `x` becomes roof with `epsilon = 1`;
   - moreover roof-`epsilon = 1` always folds to the edge subtype because the old roof `r` is an
     edge-type distinguisher.

### Consequence 36.9 (the exact reseating core)

Every `epsilon = 0` template either gives a module contradiction (if no fresh distinguisher exists)
or propagates, by primeness, to an `epsilon = 1` template.

Therefore the `12`-template list collapses to exactly:

1. **three genuine self-loop cores**
   - corner-2 with `epsilon = 1`,
   - shoulder-3 with `epsilon = 1`,
   - roof-edge with `epsilon = 1`;
2. **two exceptional off-ramps**
   - corner-3 with `epsilon = 1`  `-> U_c`,
   - shoulder-2 with `epsilon = 1` `-> T_b`.

So the reseating-descent problem is no longer a `12`-template theorem.
It is now:

- a `3`-core self-loop theorem,
- together with routing of the two off-ramp templates into the stable exceptional sector.

### Proposition 36.10 (`3 -> 2` by clone normalization)

Each of the three self-loop cores normalizes to a false/true clone pair on a single fixed house.

1. **corner-2, `epsilon = 1`**
   After reseating to the house:
   - `H_c := y - b - c - d - y`
   with roof `r`, the old omitted vertex `a` has:
   - `N_{H_c}(a) = {b, d}`,
   while `x` has:
   - `N_{H_c}(x) = {y, b, d}`.
   So `(a, x)` is a false/true corner-clone pair.
   Any fresh distinguisher of `{a, x}` is either:
   - another corner-2 trace (same loop),
   - or corner-3, hence the known off-ramp `-> U_c`.

2. **shoulder-3, `epsilon = 1`**
   After reseating to the house:
   - `H_s := a - y - c - d - a`
   with roof `r`, the old omitted vertex `b` has:
   - `N_{H_s}(b) = {a, c, r}`,
   while `x` has:
   - `N_{H_s}(x) = {a, y, c, r}`.
   So `(b, x)` is a false/true shoulder-clone pair.
   Any fresh distinguisher is either:
   - shoulder-3 again,
   - or shoulder-2, hence the known off-ramp `-> T_b`.

3. **roof-edge, `epsilon = 1`**
   After reseating to the house:
   - `H_r := a - b - c - d - a`
   with roof `y`, the old roof `r` has:
   - `N_{H_r}(r) = {b, c}`,
   while `x` has:
   - `N_{H_r}(x) = {b, c, y}`.
   So `(r, x)` is a false/true roof-clone pair on a fixed `C_4`.
   Any diagonal roof distinguisher folds back to the edge case, since the old roof `r` is already an
   edge-type distinguisher.

### Consequence 36.11 (the true reseating residue)

The `3`-core theorem is equivalent to only:

1. a **corner/shoulder twin-bag theorem**:
   a house cannot support an endless chain of false-clone distinguishers of one seed vertex without
   hitting the off-ramp or creating a module;
2. a **roof opposite-edge oscillation theorem** on a fixed `C_4`.

So the off-ramp cases are already integrated into the stable exceptional sector.
The genuine reseating residue is no longer three two-house templates, but just these two
clone-distinguisher statements.

## 37. The `tau`-even stable sector is a packet-exchange theorem

The `tau`-even reduction from Section 35 can be sharpened one step further.

### Proposition 37.1 (packet identity)

On the seed columns `(a, b, c, d, r)`, one has exactly:

- `T_b + T_c = Q_0 + B_b + B_c`.

So after fixing `(alpha, beta)`, the only free `tau`-even move is:

1. add one **top packet**
   - `D := {T_b, T_c}`,
2. equivalently add one **rim packet**
   - `E := {Q_0, B_b, B_c}`,

because these two packets have the same seed shadow.

### Consequence 37.2 (packet-exchange theorem)

The remaining stable theorem is no longer primarily arithmetic.
It is the following local structural statement:

> **Packet-exchange theorem for a stable house.**
>
> In a prime stable-house attachment, every occurrence of the symmetric top packet
> `(x_b in T_b, x_c in T_c)` is harmless.

Equivalently, it suffices to classify the induced graphs on:

- `S union {x_b, x_c, z}`,

where `z` is one further outside vertex of type, up to `tau`,

- `emptyset`,
- `S`,
- `B`,
- `U`,
- `Q_0`,
- `T`.

If every such local template either:

1. yields immediate goodness,
2. falls into reseating descent,
3. or contradicts primeness by creating a module,

then the stable exceptional house theorem is proved.

### Consequence 37.3 (the exact current general barrier)

The entire remaining prime-quotient frontier is now reduced to two finite local theorems:

1. the `3`-core reseating self-loop theorem (plus two off-ramps) from Section 36;
2. the packet-exchange theorem from Section 37.

### Proposition 37.4 (first packet reduction)

Let:

- `C_b := a - d - x_c - b - a`,
- `C_c := d - a - x_b - c - d`,

and, when `x_b x_c = 1`,

- `C_* := a - x_b - x_c - d - a`.

If some vertex sees exactly one edge of one of these `C_4`'s, then those five vertices induce a
house.
So such a template is harmless by reseeding.

### Consequence 37.5 (the `x_b x_c = 0` case is done)

If:

- `x_b x_c = 0`,

then `x_b` is the roof on `C_b` (equivalently `x_c` is the roof on `C_c`), so the template
reseats immediately.

Thus only the case:

- `x_b x_c = 1`

can survive.

### Proposition 37.6 (immediate reseating and decoupling in the packet theorem)

Assume `x_b x_c = 1`.

Then the following cases are already harmless:

1. **Immediate reseating**
   - `z in B_b` with `z x_c = 1` (and by `tau`, `z in B_c` with `z x_b = 1`);
   - `z in U_b` with `z x_c = 0` (and by `tau`, the reflected case);
   - `z in T_b` with `z x_c = 0` (and by `tau`, the reflected case);
   - `z in emptyset` or `B` and `z` adjacent to both `x_b, x_c` (roof on `C_*`);
   - `z in S`, `U`, or `Q_0` and `z` adjacent to neither `x_b, x_c` (roof on `C_*`).

2. **Trivial decoupling**
   - `z in emptyset` with `z x_b = z x_c = 0`,
   - `z in S` with `z x_b = z x_c = 1`.

   In these cases `z` is locally isolated or universal from the packet, so it can be ignored.

### Proposition 37.7 (same-side top packets reduce by primeness)

If:

- `z in T_b`,
- and `z x_c = 1`,

then every vertex of `S union {x_c}` sees `x_b` and `z` identically.
So `{x_b, z}` is a module unless some further vertex distinguishes them.

Thus this case reduces to a:

- `9`-vertex twin-distinguisher theorem.

### Consequence 37.8 (the exact packet residual barrier)

Up to `tau` and weighted-quotient complementation (`emptyset <-> S`, `B <-> U`), the packet-exchange
theorem is reduced to:

1. `x_b x_c = 1`, and one of
   - `z in emptyset` with `N_{ {x_b, x_c} }(z) = {x_b}`;
   - `z in B_b` with `z x_c = 0` (two subcases according to `z x_b = 0/1`);
   - `z in Q_0` with `z` adjacent to at least one of `x_b, x_c` (up to `tau`: `{x_b}` or `{x_b, x_c}`);
   - `z in T_b`, `z x_c = 1`, together with a distinguisher `y` for `{x_b, z}`.

So the stable packet theorem is not yet proved, but it has collapsed to:

- about `6` local `8`-vertex templates,
- plus one `9`-vertex twin-distinguisher template.

### Proposition 37.9 (canonical packet residuals)

Up to `tau` and house-complement symmetry, the surviving `8`-vertex packet templates are exactly:

- `A0`: `z in emptyset`, with `(z x_b, z x_c) = (1, 0)`;
- `A1`: `z in B_b`, with `(z x_b, z x_c) = (0, 0)`;
- `A2`: `z in B_b`, with `(z x_b, z x_c) = (1, 0)`;
- `R1`: `z in Q_0`, with `(z x_b, z x_c) = (1, 0)`;
- `R2`: `z in Q_0`, with `(z x_b, z x_c) = (1, 1)`.

Structurally:

- `A0, A1` are leaf-type templates,
- `A2` is simplicial with clique neighborhood `{b, x_b}`,
- `R1` has antineighborhood `{r, x_c}`,
- `R2` has unique nonneighbor `r`.

So no further one-step roofing argument exists at this point.

### Proposition 37.10 (the mixed `9`-vertex case reduces to one fiber)

Assume:

- `x_b, z in T_b`,
- `x_b x_c = z x_c = 1`,
- and `y` distinguishes `{x_b, z}`.

Since `x_b` and `z` have the same trace on `S union {x_c}`, necessarily:

- `y notin S union {x_c}`.

Now split by the type of `y`.

1. `y in emptyset` (or `S` by complement): this is exactly `A0`.
2. `y in B_b` (or `U_b` by complement): either immediate reseating by Proposition 37.6, or one of
   `A1, A2`.
3. `y in B_c` (or `U_c`): whichever of `x_b, z` is adjacent to `y`, that vertex together with `x_c`
   is a top packet while the other `T_b`-vertex is a Proposition 37.6 reseating witness. So this is
   impossible in a minimal obstruction.
4. `y in Q_0`: exactly `R1, R2`.
5. `y in T_c`: if `y` distinguishes, it is adjacent to exactly one of `x_b, z`; then the adjacent
   one together with `y` is a top packet, and the other `T_b`-vertex has `0` to the `T_c` side, so
   Proposition 37.6 reseats immediately. So this is impossible.

Therefore the only surviving distinguisher type is:

- `y in T_b` with `y x_c = 1`.

### Consequence 37.11 (the one-fiber same-side theorem)

Let:

- `T_b^+(x_c) := {u in T_b : u x_c = 1}`.

After excluding the five `8`-vertex residuals `A0, A1, A2, R1, R2`, any distinguisher of two
vertices of `T_b^+(x_c)` must itself lie in `T_b^+(x_c)`.

Hence the `9`-vertex barrier is not an arbitrary mixed twin-distinguisher problem.
It is only:

- three vertices `x_1, x_2, x_3 in T_b^+(x_c)`,
- with the induced graph on `{x_1, x_2, x_3}` nonhomogeneous.

Up to relabeling, that leaves only two internal `3`-vertex shapes:

- `K_2 + K_1`,
- `P_3`.

### Consequence 37.12 (the exact packet residual barrier)

The packet theorem is therefore reduced to:

1. **five explicit `8`-vertex templates**
   - `A0, A1, A2, R1, R2`;
2. **two explicit internal `9`-vertex templates**
   - `K_2 + K_1`,
   - `P_3`,

inside one fiber `T_b^+(x_c)`.

So the genuine remaining stable-house theorem is now:

> **one-fiber same-side theorem.**
>
> In a prime stable-house attachment, once `A0, A1, A2, R1, R2` are excluded, no
> `T_b^+(x_c)` can contain an induced `K_2 + K_1` or `P_3`.

## 38. The exact current local frontier

At this point the prime-quotient branch is no longer a broad structural problem.
It has been reduced to three tiny local theorems:

1. **corner/shoulder twin-bag theorem**
   - on a fixed `4`-frame `K`, a clone bag with fixed trace cannot support an endless chain of
     false-clone distinguishers without hitting the off-ramp or creating a module;
2. **roof one-bit theorem**
   - the opposite-edge roof oscillation on a fixed `C_4` must be harmless;
3. **one-fiber same-side theorem**
   - once the five packet residuals `A0, A1, A2, R1, R2` are excluded, a single fiber
     `T_b^+(x_c)` cannot contain an induced `K_2 + K_1` or `P_3`.

The first and third items already have a common flavor:

- a fixed seed frame,
- a fixed attachment trace/fiber,
- and a nonhomogeneous induced graph inside that one fiber.

So the last genuinely conceptual step may be a unified:

> **same-fiber nonhomogeneity theorem** for prime weighted house attachments.

### Proposition 38.1 (closed-fiber reduction)

Let `F` be a fixed trace/fiber over a fixed seed frame.
Assume:

- every vertex outside `F` that distinguishes two vertices of `F` already lands in a known
  off-ramp or residual configuration.

Then, after excluding those off-ramps, every outside vertex is uniform on `F`.
Hence:

1. any module of `G[F]` is a module of the ambient prime quotient;
2. so in a minimal bad case, `G[F]` has no nontrivial module;
3. therefore `G[F]` cannot be a cograph, and so contains an induced `P_4`.

### Consequence 38.2 (same-fiber `P_4` theorem)

Both same-fiber residuals now reduce to one local barrier:

> **closed-fiber `P_4` theorem.**
>
> No externally closed fixed fiber in a prime weighted house attachment contains an induced `P_4`.

Indeed:

1. **stable-house one-fiber case**
   - by Consequence 37.11, after excluding `A0, A1, A2, R1, R2`, the fiber `T_b^+(x_c)` is
     externally closed;
   - so the old target “no `K_2 + K_1` / no `P_3`” reduces to “no induced `P_4` in
     `T_b^+(x_c)`”.

2. **corner/shoulder twin-bag case**
   - after the normalization from Proposition 36.10, the same-loop clone bag is externally closed
     modulo the two off-ramps `U_c, T_b`;
   - so this case also reduces to “no induced `P_4` in the fixed clone bag”.

### Consequence 38.3 (the sharpened local frontier)

At this stage, the non-roof side reduces to:

1. **same-trace `P_3` theorem** on the residual fixed fibers.

### Proposition 38.4 (prime closed fibers contain a prime `P_4`)

Let `F` be an externally closed fixed fiber in a minimal bad prime weighted house attachment.
Then:

1. any module of `G[F]` is a module of the ambient quotient;
2. so `G[F]` is prime;
3. a prime cograph on more than one vertex cannot exist;
4. hence `G[F]` is not a cograph and contains an induced `P_4`;
5. by Gallai's prime-subgraph theorem, one may take a prime induced `4`-vertex subgraph of `G[F]`,
   and the only prime graph on `4` vertices is `P_4`.

So every counterexample contains an induced:

- `P_4 = x_1 - x_2 - x_3 - x_4`

inside one fixed fiber, with all `x_i` having the same trace on the seed frame.

### Consequence 38.5 (trace-labelled `P_4` templates)

The closed-fiber theorem is therefore not an abstract closure statement anymore.
It is the explicit local problem of killing the following trace-labelled `P_4` templates:

1. **stable-house branch**
   - `S union {x_c}` together with four vertices of `T_b^+(x_c)` inducing `P_4`;
2. **clone-bag branch**
   - the normalized fixed house / `C_4` frame together with four vertices in the fixed clone bag
     inducing `P_4`, modulo the known off-ramps.

Equivalently, the endpoints `x_1, x_4` are a same-trace twin pair over the frame, and `x_2, x_3`
are opposite internal distinguishers of that pair.

So the real remaining `P_4` task is to eliminate those trace-labelled `8/9`-vertex local templates.

### Proposition 38.6 (`P_4 -> P_3` inside one fixed fiber)

Let `F` be one of the two residual fixed fibers:

1. `F = T_b^+(x_c)` in the stable-house branch, after excluding `A0, A1, A2, R1, R2`;
2. `F` the normalized fixed clone bag in the corner/shoulder branch, after excluding the off-ramps.

If `F` contains an induced:

- `x_1 - x_2 - x_3 - x_4`,

then already:

- `x_1, x_2, x_3`

induce an induced `P_3` in the same fixed fiber.

So the `P_4` template adds no new `4`-vertex phenomenon.

### Consequence 38.7 (same-trace internal-distinguisher theorem)

The real fixed-fiber barrier is therefore:

> **same-trace internal-distinguisher theorem.**
>
> In the residual fixed fiber, no three vertices of one trace class induce `P_3`.

Equivalently, no same-trace twin pair over the seed frame admits an internal distinguisher from the
same fiber.

Branch-by-branch this means:

1. **stable-house branch**
   - `S union {x_c}` together with three vertices of `T_b^+(x_c)` inducing `P_3`;
2. **clone-bag branch**
   - the normalized fixed frame together with three vertices in the fixed clone bag inducing `P_3`.

### Consequence 38.8 (the sharpened non-roof frontier)

The non-roof side is no longer a `P_4` theorem.
It is exactly the same-trace `P_3` theorem on those two residual fibers.

## 39. The roof branch reduces to a single five-roof theorem

Fix:

- `K = a - b - c - d - a`.

Write:

- `B` for roofs on edge `b c`,
- `D` for roofs on edge `a d`.

Assuming the current roof reduction, a persistent roof obstruction is exactly:

- `B = {x_0, x_1}`,
- `D = {y_0, y_1}`,

with:

- `x_i` adjacent exactly to `b, c` on `K`,
- `y_i` adjacent exactly to `a, d` on `K`,
- cross-edges alternating:
  - `x_0 y_0 = x_1 y_1 = 1`,
  - `x_0 y_1 = x_1 y_0 = 0`,
- same-side edges constant with one bit `epsilon`:
  - `x_0 x_1 = y_0 y_1 = epsilon`.

Call this `8`-vertex skeleton:

- `S_epsilon := K union B union D`.

### Proposition 39.1 (any continuation is another roof)

Let `z` be any outside vertex in a minimal counterexample extending `S_epsilon`.
If the trace of `z` on `K` is not a roof trace on one of the two opposite edges, then `z` already
falls into one of the settled cases:

1. immediate reseeding,
2. stable exceptional landing,
3. or module / primeness contradiction.

So every genuinely new continuation of `S_epsilon` is another roof on `b c` or on `a d`.

### Proposition 39.2 (nonhomogeneous same-side roofs are not a roof-specific problem)

Suppose:

- `z in B` (the `D`-case is symmetric).

If `z` is nonhomogeneous on its own side `{x_0, x_1}`, then inside the fixed roof fiber `B` one
already has a nonhomogeneous induced graph on one trace class.
That is exactly the closed-fiber `P_4` theorem from Section 38, not a genuinely new roof
phenomenon.

So the roof-specific residue is when every new roof is homogeneous on its own side and distinguishes
only the opposite pair.

### Consequence 39.3 (five-roof theorem `T_epsilon`)

Up to dihedral symmetry and swapping `B` with `D`, the only remaining roof-specific local theorem is:

- fixed `C_4 = a b c d`,
- three `b c`-roofs `x_0, x_1, x_2`,
- two `a d`-roofs `y_0, y_1`,
- cross-edges:
  - `x_0 y_0 = x_2 y_0 = 1`,
  - `x_0 y_1 = x_2 y_1 = 0`,
  - `x_1 y_0 = 0`,
  - `x_1 y_1 = 1`,
- same-side edges constant with the same bit `epsilon`.

Call this local theorem:

- **five-roof alternating theorem `T_epsilon`**.

### Consequence 39.4 (the roof rigid case)

The case `epsilon = 1` is self-dual:

- the four roof vertices `x_0 - x_1 - y_1 - y_0 - x_0` form another `C_4`,
- and the original cycle vertices become opposite-edge roofs over it.

So `T_1` is the genuinely rigid roof case, while `T_0` should be the easier branch.

### Consequence 39.5 (the intermediate roof frontier)

The roof side reduces first to:

1. **five-roof alternating theorem `T_epsilon`**.

### Proposition 39.6 (roof twin-pair reduction)

In both `T_0` and `T_1`, the vertices:

- `x_0, x_2`

are true twins inside:

- `{a, b, c, d, x_0, x_1, x_2, y_0, y_1}`.

So in a prime ambient graph there must exist some vertex:

- `z`

distinguishing `x_0` and `x_2`.

By the previous reduction, if `z` is a `b c`-roof then that is exactly the closed-fiber same-trace
branch.
So the only genuinely roof-specific residue is:

- `z` an `a d`-roof distinguishing `x_0, x_2`.

### Consequence 39.7 (two twin-breaker templates)

Up to the symmetry `x_0 <-> x_2`, there are only two opposite-side patterns:

- `(z x_0, z x_1, z x_2) = (1, 0, 0)`,
- `(z x_0, z x_1, z x_2) = (1, 1, 0)`.

Call the resulting local templates:

- `U_epsilon^0`,
- `U_epsilon^1`.

### Proposition 39.8 (`T_0` is harmless)

For `epsilon = 0`, every prime resolution of the twin pair already falls into a settled case.

1. In `U_0^0` with pattern `(1,0,0)`, the vertices:
   - `x_1 - y_1 - a - z - x_0`
   induce a `P_5`.
2. In `U_0^1` with pattern `(1,1,0)`, the vertices:
   - `x_2 - y_0 - x_0 - z - x_1`
   induce a `P_5`.

So every prime resolution of the twin pair in `T_0` gives either:

- same-side nonhomogeneity, hence the fixed-fiber branch,
- or immediate `P_5` reseeding.

Therefore:

- `T_0` is done.

### Consequence 39.9 (the exact roof residue)

The genuinely rigid roof branch is only:

> **`U_1` twin-breaker theorem.**
>
> Start from `T_1`, add one opposite-side roof `z`, and require
> `(z x_0, z x_1, z x_2) = (1, t, 0)` with `t in {0,1}`.

So the prime-quotient frontier is now reduced to exactly:

1. **same-trace `P_3` theorem** on the residual fixed fibers;
2. **the two explicit rigid roof templates**
   - `U_1^0`,
   - `U_1^1`.

### Proposition 39.10 (`U_1` collapses back to reseating)

Let:

- `eta := z y_0 = z y_1`,

the roof-specific homogeneity bit on the `D`-side.

1. If `eta = 0`, both templates reseed immediately to `C_5`:
   - in `U_1^0`, the cycle `x_1 - y_1 - a - z - x_0 - x_1` is an induced `C_5`;
   - in `U_1^1`, the cycle `x_2 - y_0 - a - z - x_1 - x_2` is an induced `C_5`.

2. If `eta = 1`, both templates cease to be roof-specific.
   Then:
   - `a - b - x_0 - z - a`
   is an induced `C_4`, and `c` is a roof on the edge `b x_0`.
   So:
   - `H := (a, b, x_0, z ; c)`
   is a new induced house.

   Relative to this new house, all remaining outside vertices lie in house-reseating orbits from
   Section 34.

So both `U_1^0` and `U_1^1` are harmless:

- either they give an immediate `C_5`,
- or they reseed to a house whose remaining outside vertices are entirely in the old house-reseating
  automaton.

### Consequence 39.11 (there is no new roof-specific branch)

The roof side is therefore completely absorbed by the already-isolated house reseating / same-trace
machinery.

So the prime-quotient frontier is now reduced to only:

- **same-trace `P_3` theorem** on the residual fixed fibers.

## 40. The same-trace endgame reduces to two local theorems

### Proposition 40.1 (four explicit labelled obstructions)

After the closed-fiber reduction, the residual fixed fiber is itself the relevant trace class.
So a same-trace `P_3` obstruction is already witnessed on the frozen frame plus three vertices:

- `x_1 - x_2 - x_3`

of one trace class.

Up to the previous reductions, this yields exactly four labelled local obstructions:

1. **stable-house template `Sigma_st`**
   - frame `a - b - c - d - a` with roof `r`,
   - fixed `x_c in T_c`,
   - each `x_i` lies in `T_b^+(x_c)`, so
     - `x_i ~ {a, b, c, x_c}`,
     - `x_i !~ {d, r}`,
   - and:
     - `x_1 x_2 = x_2 x_3 = 1`,
     - `x_1 x_3 = 0`.

2. **corner false-clone template `Sigma_cor`**
   - normalized false-clone trace `{b, d}`,
   - three same-trace vertices inducing `P_3`.

3. **shoulder false-clone template `Sigma_sh`**
   - normalized false-clone trace `{a, c, r}`,
   - three same-trace vertices inducing `P_3`.

4. **roof false-clone template `Sigma_rf`**
   - normalized false-clone trace `{b, c}`,
   - three same-trace vertices inducing `P_3`.

### Proposition 40.2 (`Sigma_cor` and `Sigma_sh` are equivalent)

House-complement symmetry sends the corner false-clone trace `{b, d}` to the shoulder
false-clone trace `{a, c, r}`.
Since `P_3` is self-complementary, `Sigma_cor` and `Sigma_sh` are the same local theorem.

### Proposition 40.3 (`Sigma_rf` is not a new roof branch)

The roof false-clone trace `{b, c}` does not create a genuinely new local theorem.
Any opposite-side breaker is already handled by the `T_epsilon / U_1` roof collapse from Section 39,
so every persistent continuation either:

1. reseeds immediately,
2. returns to the old house-reseating machinery,
3. or lands back in the same internal fixed-fiber problem.

Therefore `Sigma_rf` is harmless as a separate roof phenomenon.

### Consequence 40.4 (the false-clone side reduces to one descent theorem)

By the house-complement symmetry from Proposition `40.2` and the roof collapse from Proposition
`40.3`, it is enough to treat the **corner false-clone trace**:

- `{b, d}`.

Let `H` be a minimal counterexample in that normalized false-clone fiber.
Then the endpoint-twin argument gives:

- `H` is a prime induced subgraph entirely inside one false-clone fiber.

Now start from an induced:

- `x_1 - x_2 - x_3`

in `H`, and let `x_4` distinguish `x_1, x_3`.

1. If `x_4 !~ x_2`, then:
   - `x_4 - x_1 - x_2 - x_3`
   is an induced `P_4`.

2. If `x_4 ~ x_2`, then `G[{x_1, x_2, x_3, x_4}]` is a paw, and `x_1, x_4` are twins over the
   frozen frame together with `x_2, x_3`.
   So primeness gives `x_5` distinguishing `x_1, x_4`.

   Split by `(x_5 x_2, x_5 x_3)`:

   - `(0,0)` gives an induced `P_4`;
   - `(0,1)` gives an induced house;
   - `(1,1)` gives an induced gem;
   - `(1,0)` gives a **shifted same-fiber `P_3`**
     - `x_5 - x_1 - x_4`.

So the clone-bag side no longer requires a general false-clone-fiber prohibition.
It reduces to the single descent statement:

> **shifted twin-breaker descent theorem.**
>
> In a prime normalized corner false-clone fiber, the `(1,0)` shifted same-fiber `P_3` case
> cannot iterate indefinitely.

If that descent theorem is proved, the whole false-clone side is done.

### Proposition 40.5 (the stable-house side reduces to one internal twin-breaker)

Let:

- `F := T_b^+(x_c)`.

After excluding the packet residuals `A0, A1, A2, R1, R2`, every vertex outside `F` is uniform on
`F`.
So in a minimal prime counterexample, `G[F]` is itself prime.

Start from a stable-house same-trace `P_3`:

- `x_1 - x_2 - x_3`

inside `F`.

Then:

1. `x_1, x_3` are twins in `G[{x_1, x_2, x_3}]`, so primeness gives `y in F` distinguishing them.
   Normalize:
   - `y x_1 = 1`,
   - `y x_3 = 0`.

2. If `y x_2 = 0`, then:
   - `y - x_1 - x_2 - x_3`
   is an induced `P_4`.

3. If `y x_2 = 1`, then `x_1, y` are true twins in the paw
   - `G[{x_1, x_2, x_3, y}]`.
   So primeness gives `z in F` distinguishing `x_1, y`.
   Normalize:
   - `z x_1 = 1`,
   - `z y = 0`.

   Now split by `(z x_2, z x_3)`:

   - `(0,0)` gives `z - x_1 - x_2 - x_3` as an induced `P_4`;
   - `(0,1)` gives `z - x_3 - x_2 - y` as an induced `P_4`;
   - `(1,1)` gives `x_3 - z - x_1 - y` as an induced `P_4`;
   - only `(1,0)` survives.

So every stable-house same-trace `P_3` either already yields a same-trace `P_4`, or contains the
unique `5`-vertex residue:

- `H`

with:

- `x_1 x_2 = x_2 x_3 = 1`,
- `y, z` complete to `{x_1, x_2}`,
- `y z = x_1 x_3 = y x_3 = z x_3 = 0`.

Equivalently:

- `x_3` is a leaf at `x_2`,
- and `y, z` are false twins on `{x_1, x_2}`.

### Consequence 40.6 (the stable-house microtheorem `O_10`)

The pair `{y, z}` is a module in `G[H]`, so primeness forces `w in F` distinguishing `y, z`.
Normalize:

- `w y = 1`,
- `w z = 0`,
- `w x_2 = 1`,
- `w x_1 = alpha`,
- `w x_3 = beta`,

with `alpha, beta in {0,1}`.

This gives four labelled `6`-vertex continuations:

- `O_{alpha beta}`.

Among them:

- `O_00` contains `w - y - x_1 - z` as an induced `P_4`;
- `O_01` contains `w - y - x_1 - z` as an induced `P_4`;
- `O_11` contains `z - x_1 - w - x_3` as an induced `P_4`;
- only **`O_10`** is not immediately a `P_4`.

Therefore the stable-house side reduces to the single internal theorem:

> **stable-house `O_10` theorem.**
>
> The unique surviving stable-house continuation `O_10` cannot occur inside the closed fiber
> `T_b^+(x_c)`.

### Proposition 40.7 (`O_10` is impossible)

Write:

- `A_1 := y`,
- `B_1 := z`,
- `A_2 := w`,

and keep:

- `x_1, x_2, x_3`

fixed.

Inside `O_10`, the pair `{y, w}` is a true-twin pair.
So primeness gives a distinguisher:

- `B_2 := v`.

Normalize:

- `v y = 1`,
- `v w = 0`.

We first force the full pattern of `B_2`.

1. If `v x_3 = 1`, then:
   - `x_3 - v - y - w`
   is an induced `P_4`.

2. If `v x_3 = 0` and `v x_2 = 0`, then:
   - `v - y - x_2 - x_3`
   is an induced `P_4`.

3. Assume now `v x_2 = 1`.
   - If `v x_1 = 0` and `v z = 0`, then:
     - `z - x_1 - y - v`
     is an induced `P_4`.
   - If `v x_1 = 0` and `v z = 1`, then:
     - `w - x_1 - z - v`
     is an induced `P_4`.
   - If `v x_1 = 1` and `v z = 1`, then:
     - `w - y - v - z`
     is an induced `P_4`.

So the only surviving pattern is:

- `v` adjacent exactly to `{x_1, x_2, y}`,
- `v` nonadjacent to `{x_3, z, w}`.

Thus:

- `A_1, A_2` are adjacent,
- `B_1, B_2` are nonadjacent,
- `B_1` sees no `A_i`,
- `B_2` sees exactly `A_1`.

Now inductively build vertices:

- `A_n, B_n in F`

for `n >= 2`, such that:

1. every `A_i` and every `B_i` is adjacent to `x_1, x_2` and nonadjacent to `x_3`;
2. `A_1, ..., A_n` is a clique;
3. `B_1, ..., B_n` is an independent set;
4. for every `j`, the vertex `B_j` is adjacent exactly to:
   - `A_1, ..., A_{j-1}`.

The base case `n = 2` is exactly the configuration just established.

Assume now that `A_1, ..., A_n, B_1, ..., B_n` are built.
By (1)-(4), the pair:

- `A_n, B_n`

is a false-twin pair over:

- `{x_1, x_2, x_3, A_1, ..., A_{n-1}, B_1, ..., B_{n-1}}`.

So primeness gives a new vertex:

- `A_{n+1}`

with:

- `A_{n+1} A_n = 1`,
- `A_{n+1} B_n = 0`.

This new vertex is forced.

1. If `A_{n+1} A_i = 0` for some `i < n`, then:
   - `A_{n+1} - A_n - A_i - B_n`
   is an induced `P_4`.

2. Therefore `A_{n+1}` is adjacent to all:
   - `A_1, ..., A_n`.

3. If `A_{n+1} B_j = 1` for some `j < n`, then:
   - `B_j - A_{n+1} - A_j - B_n`
   is an induced `P_4`.

4. Therefore `A_{n+1}` is nonadjacent to all:
   - `B_1, ..., B_n`.

5. If `A_{n+1} x_2 = 0`, then:
   - `B_n - x_2 - A_n - A_{n+1}`
   is an induced `P_4`.

6. If `A_{n+1} x_1 = 0`, then:
   - `z - x_1 - y - A_{n+1}`
   is an induced `P_4`.

7. If `A_{n+1} x_3 = 1`, then:
   - `x_3 - A_{n+1} - x_1 - z`
   is an induced `P_4`.

So `A_{n+1}` is adjacent to:

- `x_1, x_2, A_1, ..., A_n`,

and nonadjacent to:

- `x_3, B_1, ..., B_n`.

Hence `A_n, A_{n+1}` are true twins over the current ladder.
So primeness gives a new vertex:

- `B_{n+1}`

with:

- `B_{n+1} A_n = 1`,
- `B_{n+1} A_{n+1} = 0`.

Again this new vertex is forced.

1. If `B_{n+1} B_j = 1` for some `j ≤ n`, then:
   - `B_j - B_{n+1} - A_n - A_{n+1}`
   is an induced `P_4`.

2. Therefore `B_{n+1}` is nonadjacent to all:
   - `B_1, ..., B_n`.

3. If `B_{n+1} A_i = 0` for some `i < n`, then:
   - `B_{n+1} - A_n - A_i - B_n`
   is an induced `P_4`.

4. Therefore `B_{n+1}` is adjacent to all:
   - `A_1, ..., A_n`.

5. If `B_{n+1} x_1 = 0`, then:
   - `B_{n+1} - A_n - x_1 - z`
   is an induced `P_4`.

6. If `B_{n+1} x_3 = 1`, then:
   - `x_3 - B_{n+1} - A_n - A_{n+1}`
   is an induced `P_4`.

7. If `B_{n+1} x_2 = 0`, then:
   - `B_{n+1} - A_n - x_2 - x_3`
   is an induced `P_4`.

So `B_{n+1}` is adjacent to:

- `x_1, x_2, A_1, ..., A_n`,

and nonadjacent to:

- `x_3, A_{n+1}, B_1, ..., B_n`.

Thus the induction continues forever.

So `O_10` forces arbitrarily long half-graph ladders inside the finite fiber `F`, impossible.
Hence:

- **`O_10` cannot occur.**

Therefore the stable-house branch is completely closed.

### Proposition 40.8 (the shifted twin-breaker collapses to `O_10`)

Start from the surviving first shift in the corner false-clone fiber:

- `x_1 - x_2 - x_3`,
- `x_4 ~ {x_1, x_2}`,
- `x_4 !~ x_3`,
- `x_5 ~ {x_1, x_2}`,
- `x_5 !~ {x_3, x_4}`.

So:

- `x_5 - x_1 - x_4`

is the new same-fiber `P_3`, and `x_4, x_5` are twins over:

- the frozen frame together with `x_1, x_2, x_3`.

Let `x_6` distinguish `x_5, x_4`.
Normalize:

- `x_6 x_5 = 1`,
- `x_6 x_4 = 0`,
- `x_6 x_1 = 1`,

since otherwise:

- `x_6 - x_5 - x_1 - x_4`

is an induced `P_4`.

Then the old anchor trace is forced:

- if `(x_6 x_2, x_6 x_3) = (0,0)`, then `x_6 - x_5 - x_2 - x_3` is an induced `P_4`;
- if `(x_6 x_2, x_6 x_3) = (0,1)`, then `x_6 - x_3 - x_2 - x_4` is an induced `P_4`;
- if `(x_6 x_2, x_6 x_3) = (1,1)`, then `x_4 - x_1 - x_6 - x_3` is an induced `P_4`.

So only:

- `(x_6 x_2, x_6 x_3) = (1,0)`

survives.

Now relabel:

- `y := x_5`,
- `z := x_4`,
- `w := x_6`.

Then:

- `x_1 - x_2 - x_3` is the initial path,
- `y, z` are complete to `{x_1, x_2}`,
- `y z = 0`,
- `y, z` are anticomplete to `x_3`,
- `w ~ {y, x_1, x_2}`,
- `w !~ {z, x_3}`.

This is exactly the stable-house configuration `O_10` from Proposition `40.7`.
Therefore the surviving shifted twin-breaker case is impossible.

### Consequence 40.9 (shifted twin-breaker descent theorem)

In a prime normalized corner false-clone fiber, the surviving `(1,0)`
shifted same-fiber `P_3` case cannot occur.

So the false-clone side is completely closed.

### Consequence 40.10 (same-trace closure)

Both residual sides are closed:

1. the stable-house side by Proposition `40.7`;
2. the false-clone side by Consequence `40.9`.

Hence the same-trace internal-distinguisher theorem holds.

### Consequence 40.11 (weighted-house closure)

Sections `34` through `40` prove the weighted house / `bar P_5`
attachment theorem:

> every prime weighted house attachment satisfying the modular weighted-degree equations
> already yields a good induced `q`-set.

### Consequence 40.12 (prime weighted quotient closure)

Combine:

1. the general split theorem from Section `33`;
2. the elimination of `C_5` as an independent seed from Proposition `33.3`;
3. the weighted quotient complementation reducing `P_5` to the house branch;
4. Consequence `40.11`.

Then every prime weighted quotient on total
bag weight `q^2` is already good.

So, under those assumptions, the prime-quotient obstruction module is finished.

### Consequence 40.13 (audit correction on the global bridge)

The previous bridge claim was too strong.

The named refinement exact self-bridge is existential: it asks only for **some** exact witness of
size `q`, not for exactness on the distinguished bucket `w`.
So the old same-`w` objection is not the real issue.

However, Section `10` above still needs a genuine completed host

- `S`

of size `q^2`, compatible with the refinement-data package, in order to search for some subset

- `U ⊆ S`

with vanishing obstruction.

And this is not merely unproved: compatible completion from bare refinement data is false in
general. One can take:

- `s = w`,
- `blocks = []`,
- `G[w]` regular,
- every `v in w` having exact degree `e` into `t`,

and then add arbitrarily many vertices outside `w ∪ t` that are anticomplete to `w` but have
degree into `t` different from `e`. The same tuple `(w, s, t, e, blocks)` still witnesses the
refinement-data package, but no compatible size-`q^2` completion using the same control block `t`
can contain those vertices.

So the exact missing host-side statement is better phrased as an **anchored exact-`e` shell host
theorem**.

Write

- `E_e(t) := {x ∉ t : |N(x) ∩ t| = e}`.

Then the missing finite theorem is:

> find a set `S` with
> - `w ⊆ S ⊆ E_e(t)`,
> - `|S| = q^2`,
> - all degrees in `G[S]` congruent modulo `q`.

Equivalently, if

- `H := G[E_e(t)]`,

then the exact host-side problem is an **anchored modular completion problem inside the shell graph**:

> find `S ⊆ V(H)` with
> - `w ⊆ S`,
> - `|S| = q^2`,
> - all degrees in `H[S]` congruent modulo `q`.

This is the exact theorem because:

1. any genuine compatible host `S` with control block `t` and exact `t`-degree `e` on `S`
   automatically satisfies `S ⊆ E_e(t)`;
2. conversely, any such `S ⊆ E_e(t)` is already a genuine size-`q^2` fixed-modulus single-control
   host witness with the inherited control block `t`.

If one insists on the stronger sufficient form

- `S = s ⊔ C`,

then one must additionally require that every vertex already in `s` has exact degree `e` into `t`,
and then, writing `R := s \ w`, it suffices to choose

- `C ⊆ E_e(t) \ s`

of size `q^2 - |s|` and a residue shift `delta` such that:

- `|N(v) ∩ C| ≡ delta [MOD q]` for every `v in w`;
- `deg_{G[s]}(y) + |N(y) ∩ C| ≡ H + delta [MOD q]` for every `y in R`, where `H` is the common
  host-degree residue on `w`;
- `deg_{G[C]}(x) ≡ H + delta - |N(x) ∩ s| [MOD q]` for every `x in C`.

So the old `s ⊔ C` shell-selection problem remains a useful stronger sufficient route, but the exact
bridge target is the anchored shell theorem above.

Writing `S = w ⊔ U`, this anchored shell theorem is further equivalent to the existence of

- `U ⊆ V(H) \ w`,
- `|U| = q^2 - q`,

and a residue `delta` such that:

- `|N_H(v) ∩ U| ≡ delta - deg_{H[w]}(v) [MOD q]` for every `v in w`;
- `deg_{H[U]}(x) + |N_H(x) ∩ w| ≡ delta [MOD q]` for every `x in U`.

So after passing to the shell graph, the remaining data from refinement theory are only:

1. the anchor `w ⊆ V(H)`;
2. the shell graph `H`;
3. the anchored irregularity class of `deg_{H[w]}` modulo constants on `w`.

No further exact reduction follows from bare refinement data alone.

There is, however, one further exact reformulation **inside the shell problem itself**:

### Proposition 40.14 (anchored near-regular completion on `q^2 - 1` vertices)

The anchored shell host theorem is exactly equivalent to the following.

There exist:

- `T ⊆ V(H)` with `w ⊆ T` and `|T| = q^2 - 1`,
- a residue `delta in Z / q Z`,
- a low set
  - `L(T) := {y in T : deg_{H[T]}(y) ≡ delta - 1 [MOD q]}`,

such that:

1. every `y in T` has `deg_{H[T]}(y) ≡ delta` or `delta - 1 [MOD q]`;
2. `|L(T)| ≡ delta [MOD q]`;
3. there exists `x ∉ T` with
   - `N_H(x) ∩ T = L(T)`.

### Proof

If `S` is an anchored shell witness, choose any:

- `x in S \ w`

(possible because `q^2 > q`) and put:

- `T := S \ {x}`.

Then every vertex of `T` loses either one neighbor or none, so each degree in `H[T]` is congruent to
either `delta - 1` or `delta`. The low set is exactly:

- `L(T) = N_H(x) ∩ T`.

Also:

- `deg_{H[S]}(x) = |L(T)| ≡ delta [MOD q]`.

Conversely, if `T` has those properties and `x ∉ T` satisfies `N_H(x) ∩ T = L(T)`, then adding `x`
raises precisely the low vertices to degree `delta`, while `x` itself has degree

- `|L(T)| ≡ delta [MOD q]`.

So `T ∪ {x}` is an anchored shell witness.

Thus the exact next host-side theorem beyond the shell formulation is an **anchored mod-`q`
near-regular completion theorem on `q^2 - 1` vertices**.

For a fixed such `T`, one may define the anchored discrepancy class:

- `d_x^T := [1_{N_H(x) ∩ T} - 1_{L(T)}] in M_q(T)`.

Then:

- `x` completes `T` if and only if `d_x^T = 0`.

This is an exact completer test for the fixed anchored near-regular set `T`, but unlike the old
global completion/discrepancy route there is no automatic zero-sum identity for

- `Σ_{x ∉ T} d_x^T`,

because the shell graph `H` carries no global modular degree hypothesis outside the final host.

There is, however, a sharper exact reformulation in the **raw** discrepancy space
`(Z / q Z)^T`.

### Proposition 40.15 (exact anchored short-packet theorem)

For `x ∉ T`, define the raw discrepancy:

- `Delta_x^T := 1_{N_H(x) ∩ T} - 1_{L(T)} in (Z / q Z)^T`.

Then:

1. `x` completes `T` if and only if `Delta_x^T = 0`;
2. for every `1 <= p < q`, if `P ⊆ V(H) \ T` with `|P| = p`, then
   - `Σ_{x in P} Delta_x^T = 0`
     if and only if every `x in P` completes `T`.

### Proof

The first part is immediate from the definition.

For the second, assume:

- `Σ_{x in P} Delta_x^T = 0`

with `|P| = p < q`.

Fix `y in T`.

If `y ∉ L(T)`, then the `y`-coordinate says:

- `#{x in P : y in N_H(x)} ≡ 0 [MOD q]`.

But this count lies in `[0, p]` with `p < q`, so it must be `0`.

If `y ∈ L(T)`, then the `y`-coordinate says:

- `#{x in P : y in N_H(x)} ≡ p [MOD q]`.

Again the count lies in `[0, p]`, so it must be exactly `p`.

Thus every `x in P` is adjacent to every vertex of `L(T)` and to no vertex of `T \ L(T)`, i.e.

- `N_H(x) ∩ T = L(T)`,

so every `x in P` completes `T`. The converse is immediate.

So the anchored near-regular completion theorem is exactly equivalent to either of the following:

1. there exists `T` with a completer `x`;
2. there exists `T` and some nonempty raw zero-packet `P` of size `< q`.

This sharpens the host-side frontier to an **exact anchored short-packet problem** on the peeled
`q^2 - 1` set.

There is a useful strict strengthening in the same raw space.

### Proposition 40.16 (weighted raw short-packet rigidity)

Let:

- `m_x in {0, ..., q - 1}` for `x ∉ T`,
- `M := Σ_{x ∉ T} m_x`,

and assume:

- `M < q`,
- `Σ_{x ∉ T} m_x Delta_x^T = 0` in `(Z / q Z)^T`.

Then every `x` with `m_x > 0` completes `T`.

### Proof

For `y ∉ L(T)`, the `y`-coordinate gives a count congruent to `0 [MOD q]`, but lying in `[0, M]`
with `M < q`, so it is `0`.

For `y ∈ L(T)`, the `y`-coordinate gives a count congruent to `M [MOD q]`, again lying in `[0, M]`,
so it is exactly `M`.

Thus every contributing vertex is adjacent to every vertex of `L(T)` and to no vertex of
`T \ L(T)`, hence completes `T`.

So any nontrivial raw relation of total mass `< q` is already a certificate of completers.

There is also a simple exact counting identity. Write:

- `O := V(H) \ T`,
- `B := T \ L(T)`,
- `epsilon(x) := |N_H(x) ∩ B| + |L(T) \ N_H(x)|`.

Then:

1. `x` completes `T` if and only if `epsilon(x) = 0`;
2. one has
   - `Σ_{x in O} epsilon(x) = Σ_{y in B} deg_O(y) + Σ_{z in L(T)} (|O| - deg_O(z))`;
3. consequently
   - `# {completers} >= |O| - Σ_{x in O} epsilon(x)`.

So if the right-hand side is positive, one already gets a completer (equivalently a raw zero-packet
of size `1 < q`).

Therefore the exact host-side frontier sharpens once more to:

> for some anchored near-regular `T`, prove that the completer count
> - `c(T) > 0`.

Equivalently, for any `U subseteq O := V(H) \ T`, the following are equivalent:

1. `U` contains a completer;
2. there is a nonzero weighted raw relation
   - `Σ_{x in U} m_x Delta_x^T = 0`
   of total mass `< q`.

So the exact host-side target can be phrased either as completer positivity or as the existence of a
small weighted raw relation.

There is also a pointwise exact reformulation. Writing:

- `B := T \ L(T)`,
- `epsilon(x) := |N_H(x) ∩ B| + |L(T) \ N_H(x)|`,
- `beta(x) := |N_H(x) ∩ L(T)| - |N_H(x) ∩ B| = |L(T)| - epsilon(x)`,

one has:

1. `x` completes `T` if and only if `epsilon(x) = 0`, equivalently if and only if
   - `beta(x) = |L(T)|`;
2. for every `U subseteq O`,
   - `e(L(T), U) - e(B, U) = Σ_{x in U} beta(x)`
   - `                         = |L(T)| |U| - Σ_{x in U} epsilon(x)`;
3. therefore
   - `c(T) > 0`
     if and only if there exists `U subseteq O` such that
   - `e(L(T), U) - e(B, U) > (|L(T)| - 1) |U|`.

In fact a singleton `U = {x}` already captures this equivalence.

More generally:

- `e(L(T), U) - e(B, U) - (|L(T)| - 1) |U|`
- `  = c_U(T) - Σ_{x in U, epsilon(x) >= 2} (epsilon(x) - 1)`.

So the old edge-bias criterion is not merely sufficient: it is the exact existential formulation of
completer positivity. On the one-error strip `epsilon(x) in {0, 1}`, it even counts completers
exactly.

Define:

- `Phi(U) := e(L(T), U) - e(B, U) - (|L(T)| - 1) |U|`
- `       = Σ_{x in U} (1 - epsilon(x))`.

Then in fact:

- `c(T) = max_{U subseteq O} Phi(U)`.

Indeed a maximizer is obtained by taking every vertex with `epsilon = 0` and any subset of the
vertices with `epsilon = 1`, while every vertex with `epsilon >= 2` lowers `Phi`.

Because `U subseteq O` is arbitrary, this "one-error-strip extraction" collapses immediately to the
pointwise statement:

> **pointwise one-error witness**: there exists `x in O` such that
> - `epsilon(x) <= 1`.

There is therefore no additional subset combinatorics in the strip formulation.

A useful averaged sufficient route is:

> if some `W subseteq O` satisfies
> - `Σ_{x in W} epsilon(x) < 2 |W|`,
>   equivalently
> - `e(L(T), W) - e(B, W) > (|L(T)| - 2) |W|`,
> then some `x in W` has `epsilon(x) <= 1`.

But to finish positivity one needs a **zero-error witness**:

> - `c(T) > 0` if and only if there exists `x in O` with `epsilon(x) = 0`.

So the real residual obstruction after the pointwise one-error witness is the degenerate case where
all near-ideal vertices have exactly one defect. The next genuine structural input would have to be a
**defect-multiplicity / Hall-type bound** limiting how often the same unique defect can repeat.

This one-defect regime has an exact swap structure. Let:

- `O_1 := {x in O : epsilon(x) = 1}`.

For `x in O_1`, exactly one of the following holds:

1. **miss-type:** `x` is complete to `L(T) \ {z}`, anticomplete to `B`, and misses a unique
   - `z in L(T)`;
2. **add-type:** `x` is complete to `L(T)`, has a unique neighbor
   - `y in B`,
   and no other neighbors in `B`.

Define the defect map:

- `d : O_1 -> T`

by sending `x` to that unique defect site `z` or `y`.

Then:

> **anchored one-defect escape:** if there exists `x in O_1` with
> - `d(x) notin w`,
> then swapping out the defect site and inserting `x` preserves anchored near-regularity.

So, if `c(T) = 0`, the irreducible one-defect obstruction is exactly:

- `d(O_1) subseteq w`.

Repeated unique defects are therefore measured by the defect-fiber multiplicities

- `mu(u) := # d^(-1)(u)` for `u in T`,

and one can package the anchor-capacity obstruction by

- `h_T(Y) := # {x in O_1 : d(x) in Y} - (q - 1) |Y|`
  for `Y subseteq T`.

But in the anchor-supported regime this Hall condition collapses immediately. Since `d` is a
function, for every `Y subseteq w`,

- `h_T(Y) = Σ_{u in Y} (mu(u) - (q - 1))`,

so

- `h_T(Y) <= 0` for all `Y subseteq w`
  if and only if
- `mu(u) <= q - 1` for every `u in w`.

Thus the only immediate Hall obstruction is an overloaded anchor fiber:

- some `u in w` with `mu(u) >= q`.

Equivalently, if:

- `|O_1| > (q - 1) |w|`,

then some anchor fiber is overloaded.

So Hall is already exhausted. In any irreducible case one must have:

- `d(O_1) subseteq w`,
- `mu(u) <= q - 1` for every `u in w`.

Hence `O_1` decomposes into at most `q - 1` layers on which the defect map is injective.

Therefore the next genuine host-side bridge is not Hall capacity but a **multi-swap / compatibility
theorem**:

> if `X subseteq O_1` and `d | X` is injective, then under the right compatibility hypothesis,
> `(T \ d(X)) ⊔ X`
> is again anchored near-regular.

Thus the exact host-side frontier is:

> prove that some subset of outside vertices has strictly positive `L(T)`-vs-`B(T)` bias above the
> trivial slope `( |L(T)| - 1 )`, equivalently that `c(T) > 0`.

Equivalently:

- `Z_p(T) = (c(T) choose p)` for every `1 <= p < q`,

so the short-packet problem is not really separate: it is just another way of asking for
`c(T) > 0`.

Anchor data alone still do not force this positivity; some genuine shell structure is needed.

Moreover, even conditional Consequence `40.12` only addresses the prime weighted quotient branch,
while Theorem `17.5` also leaves the alternative of a small bad module.

So the present notes do **not** yet prove the named refinement exact self-bridge.

### Consequence 40.17 (audit correction on the top-level route)

The previous claim that the conjecture follows is also too strong.
The current asymptotic wrappers still require the open theorem

- `HasPolynomialCostEmptyControlDyadicLift`,

or at least the weaker one-parameter target family isolated by the dyadic-lift audit.

More precisely, if `D` is the bridge exponent and `A := D + 1`, it is enough to prove a
terminal-exponent lift that upgrades a `2^j`-cascade witness of size

- `(2^j)^C (2^(j+1))^A`

to a `2^(j+1)`-cascade witness of size

- `(2^(j+1))^A`.

Section `18` shows that the true fixed-support core is then a residual-packet / top-bit theorem:
one must force the normalized obstruction `eta_m(U)` to vanish modulo `2` on one fixed support
`U`, not merely prove naive layerwise divisibility.

So the top-level conjecture is not finished by the present notes.
