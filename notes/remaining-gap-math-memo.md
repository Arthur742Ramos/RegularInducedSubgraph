# Remaining Gap: Detailed Math Memo

This note goes deeper than the short roadmap. It is meant to isolate the exact mathematical core of
the remaining gap and to record the most plausible proof programs before touching more Lean code.

The standing live target is

- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

Everything below is written for a fixed dyadic modulus

- `q = 2^j` with `j > 0`.

The main message is:

> once the current host-step has produced a bucket `w` of size `q` and a control block `t` of size
> `q - 1`, the only real remaining issue is to prove that `G[w]` is regular.

All other data are either already exact, or are only useful insofar as they help prove that one fact.

## 1. The structured package we actually have

From the current `Cascade.lean` host-step output, after exact-card reduction, we have:

- a bucket `w` with `|w| = q`,
- a host set `s` with `w ⊆ s`,
- a distinguished control block `t` with `|t| = q - 1`,
- a list of further separated control blocks `blocks`,
- an exact scalar `e` such that every vertex of `w` has exactly `e` neighbors in `t`,
- congruence of host degrees on `G[s]` modulo `q`,
- congruence of ambient degrees on `G[s ∪ B]` modulo `q`, where
  `B := controlBlockUnion ((t, e) :: blocks)`,
- and constant external residues modulo `q` into every block of `((t, e) :: blocks)`.

This is exactly the content of
`HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard`.

## 2. First reduction: the final exact witness is really about `G[w]`

Let `R := s \ w`.

For `v ∈ w`, define:

- `a(v) := deg_{G[w]}(v)`,
- `r(v) := |N(v) ∩ R|`,
- `b(v) := |N(v) ∩ t| = e`.

Then for every `v ∈ w`,

- `deg_{G[s]}(v) = a(v) + r(v)`,
- `deg_{G[w ∪ t]}(v) = a(v) + e`.

The exact single-control witness we want at the end has control budget `q - 1`, and the current
block `t` already has the correct size and already has exact external degree `e`. So:

## Proposition 2.1

Keeping the same bucket `w` and the same control block `t`, the following are equivalent:

1. `(w, t)` is already a bounded exact single-control witness of size `q` and control size `q - 1`.
2. `G[w]` is regular.

### Proof

If `(w, t)` is an exact witness, then the ambient degrees on `G[w ∪ t]` are constant, and the
degrees into `t` are all exactly `e`. Subtracting `e`, the degrees inside `G[w]` are constant.

Conversely, if `G[w]` is regular of degree `d`, then every vertex of `w` has degree `d + e` in
`G[w ∪ t]`, while the external degree into `t` is already exactly `e`. So `(w, t)` is an exact
single-control witness.

So from this point on, the problem is just to prove that `G[w]` is regular.

## 3. Second reduction: regularity of `G[w]` is exactly the dropped-part residue

Because the host degrees in `G[s]` are constant modulo `q`, there is some residue `H mod q` such
that

- `a(v) + r(v) ≡ H [MOD q]`

for every `v ∈ w`.

Therefore

- `a(v) ≡ H - r(v) [MOD q]`.

Now `|w| = q`, so every induced degree in `G[w]` lies in `{0, 1, ..., q - 1}`. Hence congruence
modulo `q` on `G[w]` is the same as exact equality.

## Proposition 3.1

For the current bucket `w`, the following are equivalent:

1. `G[w]` is regular.
2. The values `a(v)` are constant modulo `q` on `w`.
3. The dropped-part degrees `r(v) = |N(v) ∩ (s \ w)|` are constant modulo `q` on `w`.

### Proof

`1 ⇒ 2` is immediate.

`2 ⇒ 1` holds because `0 ≤ a(v) ≤ q - 1`.

`2 ⇔ 3` follows from the congruence

- `a(v) + r(v) ≡ H [MOD q]`.

So the direct exact-upgrade problem on the current bucket is *exactly* the missing dropped-part
residue problem.

This is the core identity behind the whole gap.

## 4. Third reduction: the outside control blocks are only a bridge to `r(v)`

Let

- `B := controlBlockUnion ((t, e) :: blocks)`.

Because every block in `((t, e) :: blocks)` contributes a constant residue modulo `q` on `w`, there
is some total residue `E mod q` such that

- `|N(v) ∩ B| ≡ E [MOD q]`

for every `v ∈ w`.

Hence

- `deg_{G[w ∪ B]}(v) = a(v) + |N(v) ∩ B| ≡ a(v) + E [MOD q]`.

Therefore:

## Proposition 4.1

Under the refinement-data hypotheses, the following are equivalent:

1. `G[w]` is regular.
2. The degrees on `G[w ∪ B]` are constant modulo `q` on `w`.

### Proof

If `G[w]` is regular, then `a(v)` is constant, so `deg_{G[w ∪ B]}(v)` is constant modulo `q`
because the contribution of each control block is constant modulo `q`.

Conversely, if the degrees on `G[w ∪ B]` are constant modulo `q`, subtract the block contribution
`E`. Then `a(v)` is constant modulo `q`, hence exact.

So the “small ambient” target is not auxiliary decoration. It is literally another way of phrasing
regularity of `G[w]`.

Combined with Proposition 3.1, we get the exact triangle:

- regularity of `G[w]`,
- small-ambient congruence on `w ∪ B`,
- dropped-part residue on `s \ w`,

and any one of these implies the other two in the presence of the current refinement package.

This is the cleanest conceptual explanation of why
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge` and
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge` are the right
finite surfaces.

## 5. Matrix formulation of the remaining unknown

The unknown part is entirely the bipartite graph between `w` and `R := s \ w`.

Write the `q × |R|` adjacency matrix as

- `M = (m_{v,x})`,

where `m_{v,x} = 1` if `v ~ x` and `0` otherwise.

Then

- `r(v) = Σ_{x ∈ R} m_{v,x}`.

So the remaining theorem is:

> prove that the row sums of `M` are all congruent modulo `q`.

Everything else in the current package is already known.

This viewpoint is useful because it makes two facts explicit.

### Fact 5.1

The exact control block `t` does **not** change the problem on the fixed bucket `w`.

Indeed, adding a control block with constant row sum `e` only shifts the row sums by the same
constant.

### Fact 5.2

The further separated control blocks in `blocks` also do **not** change the problem on the fixed
bucket `w`.

They matter only as a way to compare two ambient graphs modulo `q`; they contribute the same residue
to every row of `M`.

So for the current bucket, the whole difficulty is the matrix `M`.

## 6. Why the false residue-host route was too strong

The stronger residue-host target asked for a package that still looks like the same structured
single-control modular host witness, but now also includes the dropped-part residue and the exact
control degree, i.e. the full
`HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard`.

That target is stronger than necessary. By Proposition 2.1, the real objective is only that `G[w]`
be regular; no same-shape residue-host witness is logically required once we are willing to work
directly with the existing `w` and `t`.

The counterexample at `q = 4` therefore fits the mathematics:

- there can be enough structure to force exact regularity on some bucket,
- without enough structure to force a whole residue-host witness of the same shape.

So the correct target is not “recover the stronger package”, but “prove regularity of `G[w]` by
using the extra refinement data.”

## 7. Small-ambient collapse revisited

The existing small-ambient lemma says that if the whole graph has size at most `2q - 1`, then the
refinement package already collapses.

Mathematically this is completely transparent:

- `|w| = q`,
- `|t| = q - 1`,
- so if `|V| ≤ 2q - 1`, there is no room for any extra dropped part beyond `w` and `t`.

Equivalently, `R = s \ w` is forced to be empty, hence `r(v) = 0` for all `v`.

Then Proposition 3.1 immediately gives regularity of `G[w]`.

This is the first sanity check any future proof should preserve: the global theorem must specialize
to this trivial tail-free case.

## 8. A genuinely useful reformulation of the finite gap

For the current bucket, the exact theorem can be stated with no mention of control blocks at all.

## Finite Core Statement

Let `q = 2^j` and suppose we have:

- a set `w` of size `q`,
- a host `s` with `w ⊆ s`,
- congruence of the host degrees on `G[s]` modulo `q`,
- and enough extra data to prove that `r(v) = |N(v) ∩ (s \ w)|` is constant modulo `q`.

Then `G[w]` is regular, hence `(w, t)` is already a bounded exact single-control witness as soon as
there is any nonempty control block `t` of size at most `q - 1` with exact constant external degree.

The current refinement package already supplies the final clause for `t`.  
So the only missing mathematical statement is:

> show that the row sums of the tail matrix `M` are constant modulo `q`.

That is the exact remaining finite theorem.

## 9. What a proof must actually do

A successful proof now has only three realistic shapes.

### Program A. Prove the small-ambient congruence directly

By Proposition 4.1, it is enough to prove that the degrees on `G[w ∪ B]` are constant modulo `q`
on `w`.

This is conceptually attractive because the graph `G[w ∪ B]` throws away the unknown tail `R`.

But the tail is not really gone: proving small-ambient congruence is equivalent to proving that the
tail row sums are constant modulo `q`. So this route is only a rephrasing of the same problem.

Still, it is the right *formal* route if the proof can compare `G[s ∪ B]` and `G[w ∪ B]` by a new
selection theorem.

### Program B. Carry the tail as explicit proof-blocks

This is the most plausible route inside the present modular-control language.

The current host-step theorem packages:

- one exact control block `t`,
- the old external control blocks,
- but **not** the internal dropped part `s \ w`.

The missing theorem should therefore strengthen the host-step so that the dropped part is itself
carried as a structured family of auxiliary blocks whose contributions are already constant modulo
`q` on `w`.

If one had such a partition

- `s \ w = D₁ ⊔ ... ⊔ D_m`

with each `|N(v) ∩ D_i|` constant modulo `q` on `w`, then

- `r(v) = Σ_i |N(v) ∩ D_i|`

would automatically be constant modulo `q`, and the proof would be over.

This program is attractive because it matches the existing control-block machinery:

- the whole library already knows how to add residues of separated blocks,
- and the only issue is that the dropped part is currently still an undifferentiated tail.

So, from a mathematical standpoint, the most natural finite strengthening is:

> not “upgrade to a residue-host witness”, but
> “decompose the internal tail into finitely many residue-controlled proof-blocks.”

This is strictly weaker than the false residue-host route and exactly strong enough for the direct
exact collapse.

### Program C. Use the dyadic structure bit-by-bit

This is the only genuinely new idea that seems to fit the `q^2 -> q` numerology.

The dropped-part degree `r(v) mod q` has `j` binary digits because `q = 2^j`.

If one could find `j` independent two-way tests during the passage from the original `q^2`-sized
host bucket down to the final `q`-bucket, and if those tests determined the `j` bits of the final
dropped-part residue, then one could equalize those tests one bit at a time:

- each bit costs a factor `2`,
- `j` bits cost a factor `2^j = q`,
- starting from `q^2` vertices, that leaves `q` vertices.

This is the exact right counting budget.

That is the key heuristic:

> a viable dyadic proof should spend one factor `2` per binary digit of the dropped-part residue,
> not one factor `q` on an all-at-once `q`-way bucketing.

The current host-step spends its whole budget on one `q`-way bucketing, namely the exact degree
into the `q - 1` control block. That is why it gets only one exact block but no tail residue.

So a truly dyadic improvement should replace the current one-shot `q`-class argument by a
bit-by-bit argument.

I do not yet have a clean graph-theoretic realization of those `j` tests inside the present
language, but this is the first proof program whose combinatorial budget matches the `q^2 -> q`
theorem exactly.

## 10. A concrete binary-coding dream principle

Program C can be formulated as the following ideal principle.

### Binary Tail Coding Principle

During the descent from a `q^2`-sized host bucket to a final `q`-bucket, one would like to produce
auxiliary test sets

- `C₀, C₁, ..., C_{j-1}`

so that, for every vertex surviving to the final bucket, the binary expansion of its eventual
dropped-part residue modulo `q` is determined by the parities of the degrees `|N(v) ∩ C_m|`.

If this principle held, then one could repeatedly pass to a half-sized subbucket on which each
parity is frozen, and after `j` stages one would reach a size-`q` bucket with constant
dropped-part residue modulo `q`.

This is not yet a proof. But it explains exactly what a successful dyadic argument must look like:

- not a stronger same-shape residue package,
- not a brute-force `q^2`-class bucketing,
- but a binary encoding of the unknown tail residue.

## 11. Why this memo points away from more wrapper code

The math now says very clearly:

1. The final exact witness on the current bucket is equivalent to regularity of `G[w]`.
2. Regularity of `G[w]` is equivalent to constancy modulo `q` of the dropped-part row sums.
3. The current package already contains all other ingredients.

So no new wrapper theorem will move the frontier unless it adds one of the following:

- direct small-ambient congruence,
- direct dropped-part residue,
- a partition of the internal tail into residue-controlled blocks,
- or a genuinely dyadic binary control of the tail residue.

Anything else is bookkeeping.

## 12. Most realistic next theorem to target

If the proof is going to stay within the current graph/control-block language, the strongest target
that still looks realistic is:

> a strengthened host-step theorem that carries the internal dropped part `s \ w` as explicit
> residue-controlled proof-blocks.

Reason:

- it attacks exactly the missing matrix `M`,
- it does not ask for the false same-shape residue-host package,
- and it uses the library’s existing algebra for adding modular contributions of separate blocks.

If one wants a genuinely new combinatorial idea, then the only route whose counting works cleanly is
the dyadic bit-by-bit program in Section 10.

## 13. Bottom line

The remaining math is no longer mysterious.

For the current bucket `w` of size `q`, the whole problem is:

- prove that the row sums of the bipartite adjacency matrix between `w` and `s \ w` are constant
  modulo `q`.

Everything else in the existing refinement package is already enough to turn that statement into the
desired exact witness.

So the next genuine proof effort should be one of these two:

1. strengthen the host-step so the internal dropped part is itself decomposed into
   residue-controlled proof-blocks;
2. find a dyadic bit-by-bit argument that freezes the dropped-part residue modulo `2^j` using only
   a factor `2` per binary digit.

That is the deepest mathematical reduction I currently trust.
