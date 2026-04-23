# Remaining Gap: Proof Attack

This note records the strongest clean mathematical statements I can now prove on paper from the
current formal surfaces, together with the one finite strengthening that would close the live gap.

The point is to stop speaking vaguely about “the missing residue” and state exactly what is left.

Throughout:

- `q = 2^j` with `j > 0`,
- `w` is the size-`q` bucket produced by the host-step,
- `s` is the current host with `w ⊆ s`,
- `t` is the distinguished exact control block with `|t| = q - 1`,
- `B := controlBlockUnion ((t, e) :: blocks)`,
- `R := s \ w`.

The current exact-card refinement package gives:

- `|w| = q`,
- `|t| = q - 1`,
- exact constancy of `|N(v) ∩ t| = e` on `w`,
- constancy modulo `q` of the host degrees on `G[s]` over `w`,
- constancy modulo `q` of the block contributions into every block of `((t, e) :: blocks)`.

## 1. Same-bucket exactness criterion

Let

- `a(v) := deg_{G[w]}(v)`,
- `r(v) := |N(v) ∩ R|`.

Then for every `v ∈ w`,

- `deg_{G[s]}(v) = a(v) + r(v)`,
- `deg_{G[w ∪ t]}(v) = a(v) + e`.

### Proposition 1

Keeping the same bucket `w` and the same control block `t`, the following are equivalent:

1. `(w, t)` is already a bounded exact single-control witness of size `q` and control budget
   `q - 1`.
2. `G[w]` is regular.
3. The numbers `a(v)` are constant on `w`.

### Proof

`1 ⇒ 2`: exact ambient degree on `w ∪ t` and exact degree `e` into `t` imply exact degree
`deg_{G[w]}(v) = deg_{G[w ∪ t]}(v) - e`, independent of `v`.

`2 ⇒ 1`: if `G[w]` is regular of degree `d`, then every vertex of `w` has ambient degree `d + e`
in `G[w ∪ t]`, and exact degree `e` into `t`, so `(w, t)` is an exact witness.

`2 ⇔ 3` is tautological.

So any proof that keeps the current `w` and `t` only has to prove that `G[w]` is regular.

## 2. Dropped-part residue is exactly the obstruction

Because the host degrees on `G[s]` are constant modulo `q` on `w`, there is a residue class
`H mod q` such that

- `a(v) + r(v) ≡ H [MOD q]`

for every `v ∈ w`.

Also, since `|w| = q`, every value `a(v)` lies in `{0, 1, ..., q - 1}`.

### Proposition 2

The following are equivalent:

1. `G[w]` is regular.
2. The values `a(v)` are constant modulo `q` on `w`.
3. The dropped-part degrees `r(v)` are constant modulo `q` on `w`.

### Proof

`1 ⇒ 2` is immediate.

`2 ⇒ 1`: every `a(v)` lies in `[0, q - 1]`, so congruence modulo `q` implies equality.

`2 ⇔ 3`: from

- `a(v) + r(v) ≡ H [MOD q]`,

the residue of `a(v)` is constant iff the residue of `r(v)` is constant.

This is the sharpest exact reformulation of the gap on the current bucket:

> to make `(w, t)` an exact witness, it is enough and necessary to show that the dropped-part degree
> into `R = s \ w` is constant modulo `q` on `w`.

## 3. Small-ambient congruence is another exact reformulation

Because every block in `((t, e) :: blocks)` contributes a constant residue modulo `q` on `w`,
there is some total residue `E mod q` such that

- `|N(v) ∩ B| ≡ E [MOD q]`

for every `v ∈ w`.

Hence

- `deg_{G[w ∪ B]}(v) = a(v) + |N(v) ∩ B| ≡ a(v) + E [MOD q]`.

### Proposition 3

The following are equivalent:

1. `G[w]` is regular.
2. The degrees on `G[w ∪ B]` are constant modulo `q` on `w`.

### Proof

If `G[w]` is regular, then `a(v)` is constant, so `deg_{G[w ∪ B]}(v)` is constant modulo `q`.

Conversely, if the degrees on `G[w ∪ B]` are constant modulo `q`, subtract the fixed block residue
`E` to see that `a(v)` is constant modulo `q`; then Proposition 2 gives exact regularity.

So the three formulations are interchangeable on the current bucket:

- exact regularity of `G[w]`,
- dropped-part residue on `R`,
- small-ambient congruence on `w ∪ B`.

## 4. The strongest same-bucket sufficient theorem

The cleanest finite theorem that would close the live gap *without changing the bucket* is the
following.

### Internal Tail Block Theorem

Assume the current refinement package for `(w, s, t, blocks, e)`.  
Assume in addition that the dropped part `R = s \ w` admits a partition

- `R = D₁ ⊔ ... ⊔ D_m`

such that for every `i` and all `v, v' ∈ w`,

- `|N(v) ∩ D_i| ≡ |N(v') ∩ D_i| [MOD q]`.

Then `(w, t)` is already a bounded exact single-control witness of size `q` and control budget
`q - 1`.

### Proof

Summing over the partition gives

- `r(v) = Σ_i |N(v) ∩ D_i|`,

so `r(v)` is constant modulo `q` on `w`. By Proposition 2, `G[w]` is regular. By Proposition 1,
the same bucket `w` together with the same control block `t` is already a bounded exact
single-control witness.

This is a genuine theorem, not just a heuristic.

It identifies the exact finite strengthening that would settle the same-bucket version of the gap:

> decompose the internal tail `s \ w` into residue-controlled proof-blocks.

## 5. Why this is the right strengthening of the host-step

The current host-step already turns one internal piece of the old host into an exact control block
`t` of size `q - 1`. The theorem above shows exactly what remains:

- not another wrapper,
- not a same-shape residue-host witness,
- but a structured decomposition of the *remaining* internal tail.

This is the right target because:

1. it is strictly weaker than the already-false residue-host route;
2. it is exactly strong enough to prove same-bucket exactness;
3. it fits the existing control-block algebra, since modular contributions of separate blocks
   already add correctly in the library.

## 6. The one finite theorem that would close the live bridge

The previous theorem suggests the following strengthened host-step statement.

### Strengthened Host-Step Claim

From a bounded fixed-modulus control-block modular host witness at bucket `q * q`, one can produce:

- a bucket `w` of size `q`,
- a host `s` with `w ⊆ s`,
- a distinguished exact control block `t` of size `q - 1`,
- the old external blocks outside `s`,
- and a partition of the internal tail `s \ w` into finitely many proof-blocks `D_i`,

such that:

- every `D_i` contributes a constant residue modulo `q` on `w`,
- `t` contributes an exact constant degree on `w`,
- the host degrees on `G[s]` are constant modulo `q` on `w`.

### Theorem 6.1

If the Strengthened Host-Step Claim holds, then
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge` holds.

### Proof

Apply the strengthened host-step to get the partition `R = ⊔ D_i`. Then the Internal Tail Block
Theorem applies, so `(w, t)` is already a bounded exact single-control witness of size `q` and
control budget `q - 1`.

That is exactly the conclusion required by
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

So the live bridge is mathematically reduced to one finite theorem about the internal tail.

## 7. Why the existing refinement package does not itself prove exactness

The current refinement package controls:

- the host residue on `G[s]`,
- the exact degree into `t`,
- the external residues into blocks outside `s`.

But it does **not** separately control the contributions of the vertices in `R = s \ w`.

Since Proposition 2 shows that exactness on the current bucket is equivalent to the constancy modulo
`q` of the dropped-part degree `r(v)`, this missing control on `R` is literally the entire problem.

This is the cleanest mathematical explanation of why the present theorem surface stalls where it
does.

## 8. Updated global conclusion

The same-bucket internal-tail theorem is still the right **local** statement for the distinguished
bucket produced by the host-step. But it is no longer the best **global** formulation of the open
problem.

Three points matter.

1. The distinguished bucket need not be exact inside a genuine size-`q^2` completion, so the final
   theorem cannot be phrased as “the canonical terminal bucket works”.
2. The small cases `q = 2` and `q = 4` are now genuinely settled:
   - `q = 2` is trivial;
   - `q = 4` is automatic from Dyson-McKay's `N_4 = 8`, since every `16`-vertex graph already has a
     regular induced `4`-set.
3. So the first genuinely new dyadic case is `q = 8`.

The honest remaining theorem is therefore:

> find **some** size-`q` subset `U` of the size-`q^2` host with
> - `Omega_{V \ U}(U) = 0`.

Equivalently:

- `G[U]` is regular;
- the complement-degree vector on `U` is constant modulo `q`;
- the inherited control block already turns `(U, t)` into an exact witness.

## 9. Completion-discrepancy reformulation

Fix `q = 2^j`, and let `G` be a graph on `q^2` vertices whose degrees are all congruent modulo `q`.

For a `(q - 1)`-set `S`, say that `S` has **target degree** `r` if:

- every vertex of `G[S]` has degree in `{r - 1, r}`;
- exactly `r` vertices of `S` have degree `r - 1`.

Write

- `L(S) := {s in S : deg_{G[S]}(s) = r - 1}`.

Then an outside vertex `x notin S` completes `S` to an `r`-regular `q`-set if and only if

- `N(x) ∩ S = L(S)`.

Define the completion count

- `T(G) := sum_r sum_{S target-r} #{x in V \ S : N(x) ∩ S = L(S)}`.

Each regular induced `q`-set contributes exactly `q` such pairs `(S, x)`, one for each deleted
vertex, so:

- `T(G) = q * #{regular induced q-sets}`.

Hence the global theorem is equivalent to:

> `T(G) > 0`.

Now fix a target-`r` near-regular `(q - 1)`-set `S`, put `R := V \ S`, let `c_x^S` be the adjacency
column of `x` into `S`, and define the discrepancy class

- `d_x^S := [c_x^S - 1_{L(S)}] in M_q(S) := (Z / q Z)^S / <1_S>`.

Because all full degrees are congruent modulo `q`, one gets the local zero-sum identity

- `sum_{x in R} d_x^S = 0` in `M_q(S)`.

A completer is exactly an outside vertex with

- `d_x^S = 0`.

So a counterexample would have to satisfy:

- `sum_{x in R} d_x^S = 0`,
- but `d_x^S != 0` for every `x in R`,

for every target near-regular `(q - 1)`-set `S`.

This is the cleanest completion-theoretic version of the obstruction currently on the table.

## 10. The dyadic route worth keeping

The naive halving lemma should now be treated only as a strong sufficient detour:

> perhaps one can repeatedly halve the ambient set while preserving degree constancy modulo `q`.

That route is probably too strong and is not faithful to the actual obstruction, because changing the
ambient set introduces new deleted layers whose contribution is not automatically controlled on the
final `q`-set.

The corrected dyadic route should instead keep the **same final** `q`-set `U` and study the
successive half-obstructions. Concretely, once the complement-degree vector on `U` is constant modulo
`2^m`, one should track

- `eta_m(U) := [(r_U - c_m 1_U) / 2^m] in M_{q / 2^m}(U)`,

and try to prove that some fixed `U` survives all lifts

- `eta_m(U) in 2 M_{q / 2^m}(U)`,

for `m = 0, ..., j - 1`.

This avoids the deleted-layer problem because it measures the obstruction on one fixed support rather
than on a chain of shrinking ambient halves.

## 11. Bottom line

The strongest honest summary I currently trust is:

- `q = 2, 4` are proved;
- the general dyadic theorem is open;
- the live target is to force some `q`-set `U` with `Omega_{V \ U}(U) = 0`.

The two routes worth keeping are:

1. the completion/discrepancy route on near-regular `(q - 1)`-sets;
2. the fixed-`U` dyadic lifting route via the classes `eta_m(U)`.

The naive balanced-halving lemma is now best viewed as a possible sufficient shortcut, not as the
central formulation of the gap.
