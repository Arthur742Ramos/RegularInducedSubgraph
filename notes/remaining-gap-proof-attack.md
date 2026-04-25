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

The strongest honest summary at this earlier checkpoint was:

- `q = 2, 4` are proved;
- the general dyadic theorem was open;
- the live target is to force some `q`-set `U` with `Omega_{V \ U}(U) = 0`.

The two routes worth keeping are:

1. the completion/discrepancy route on near-regular `(q - 1)`-sets;
2. the fixed-`U` dyadic lifting route via the classes `eta_m(U)`.

The naive balanced-halving lemma is now best viewed as a possible sufficient shortcut, not as the
central formulation of the gap.

## 12. A genuine positive class: all vertex-transitive cases

There is one clean family where the theorem is already done.

### Proposition 12.1

Let `q = 2^j`. If `G` is vertex-transitive on `q^2` vertices, then `G` contains a regular induced
subgraph on `q` vertices.

In fact one has the stronger statement:

> if `G` is vertex-transitive on `2^n` vertices, then for every `m <= n`, `G` has a
> vertex-transitive induced subgraph on `2^m` vertices.

### Proof

Let `Gamma <= Aut(G)` act transitively on `V(G)`, and fix `v in V(G)`. Since

- `|V(G)| = q^2 = 2^(2 j)`,

one has

- `[Gamma : Gamma_v] = 2^(2 j)`.

Let `P <= Gamma` be a Sylow `2`-subgroup. The index `[Gamma : P]` is odd, so

- `[P : P_v] = 2^(2 j)`,

and therefore `P` is itself transitive on `V(G)`.

Now write `K := P_v`. Then

- `[P : K] = q^2`.

Because `P` is a finite `2`-group, there exists an intermediate subgroup

- `K <= H <= P`

with

- `[H : K] = q`.

Take

- `U := H . v`.

Then `|U| = q`, and `H` acts transitively on `U`. Since `H <= Aut(G)`, the induced graph `G[U]`
is vertex-transitive, hence regular.

### Consequence 12.2

Any counterexample to the theorem must be highly asymmetric:

- it cannot be vertex-transitive;
- in particular it cannot be a Cayley graph on a group of order `q^2`;
- more generally, no automorphism subgroup can supply a transitive `q`-orbit.

So the theorem, if false, fails only in genuinely nonhomogeneous configurations.

## 13. Zero-sum packets are automatic around every near-regular `(q - 1)`-set

The completion/discrepancy formulation can be sharpened by a standard `p`-group zero-sum theorem.

Fix a near-regular `(q - 1)`-set `S` of target degree `r`, with low set `L = L(S)`, and define

- `d_x^S := [c_x^S - 1_L] in M_q(S) := (Z / q Z)^S / <1_S>` for `x notin S`.

As before,

- `sum_{x notin S} d_x^S = 0`.

Also:

- `|V \ S| = q^2 - q + 1`,
- `M_q(S) ~= C_q^(q - 2)`.

For the `p`-group `C_q^(q - 2)`, the Davenport constant is

- `D(M_q(S)) = (q - 2) (q - 1) + 1 = q^2 - 3 q + 3`.

Since

- `q^2 - q + 1 > q^2 - 3 q + 3`,

the outside discrepancy sequence always contains a nonempty zero-sum subpacket.

### Corollary 13.1

For every near-regular `(q - 1)`-set `S`, there exists a nonempty packet

- `P subseteq V \ S`

such that

- `sum_{x in P} d_x^S = 0`.

So the issue is no longer whether zero-sum packets exist. They always do. The issue is how short
one can force them to be.

## 14. Proper short packets already force the theorem

The crucial new observation is that the short-packet rigidity argument works cleanly for
**proper** near-regular sets, i.e. for targets

- `1 <= r <= q - 2`,

so that both `L(S)` and `S \ L(S)` are nonempty.

### Proposition 14.1 (proper short-packet lemma)

Assume `q >= 4`. Let `S` be a near-regular `(q - 1)`-set of proper target `r`, with low set
`L = L(S)`, and let `P subseteq V \ S` satisfy

- `0 < |P| < q / 2`,
- `sum_{x in P} d_x^S = 0`.

Then every `x in P` satisfies

- `N(x) ∩ S = L`,

and hence `G` contains a regular induced subgraph on `q` vertices.

### Proof

Write `p := |P|`. For each `s in S`, let

- `a_s := #{x in P : s in N(x)}`.

Because the packet sum vanishes in the quotient, there is some `lambda in Z / q Z` such that

- `a_s - p 1_L(s) equiv lambda [MOD q]`

for all `s in S`.

Since `S \ L(S)` is nonempty, choose `s notin L(S)`. Then

- `0 <= a_s <= p < q / 2 < q`,

so in fact `a_s = lambda`, and hence `lambda in {0, 1, ..., p}`.

Since `L(S)` is nonempty, choose `t in L(S)`. Then

- `a_t equiv lambda + p [MOD q]`.

But `0 <= lambda + p <= 2 p < q`, so there is no modular wraparound, and therefore

- `a_t = lambda + p`.

Since also `a_t <= p`, it follows that

- `lambda + p <= p`,

hence `lambda = 0`.

Therefore:

- `a_s = 0` for every `s notin L(S)`,
- `a_t = p` for every `t in L(S)`.

Because the adjacency indicators are `0 / 1`, this means every `x in P` is adjacent to every vertex
of `L(S)` and to no vertex of `S \ L(S)`. So

- `N(x) ∩ S = L(S)`

for every `x in P`. Any one such `x` completes `S` to a regular induced `q`-set.

### Consequence 14.2

The theorem would follow as soon as one can prove:

> either `G` already contains an independent or complete `q`-set, or there exists a proper
> near-regular `(q - 1)`-set `S` carrying a zero-sum packet of size `< q / 2`.

This is the corrected short-packet forcing target.

## 15. Endpoint repair

The endpoint cases must be handled separately.

### Proposition 15.1

Let `S` be a near-regular `(q - 1)`-set of endpoint target `r = 0` or `r = q - 1`.

1. If `r = 0`, then `S` is independent and `L(S) = emptyset`.
2. If `r = q - 1`, then `S` is a clique and `L(S) = S`.

In either case, a zero discrepancy class

- `d_x^S = 0`

does **not** distinguish between the true completer pattern and the opposite endpoint pattern.

### Explanation

If `r = 0`, then `1_{L(S)} = 0`, so

- `[c_x^S - 1_{L(S)}] = [c_x^S]`.

Both of the endpoint patterns

- `c_x^S = 0`,
- `c_x^S = 1_S`

map to `0` in `M_q(S)` because `[0] = [1_S] = 0`.

Similarly, if `r = q - 1`, then `1_{L(S)} = 1_S`, and again both endpoint patterns produce the
same zero class in the quotient.

So the packet rigidity argument cannot identify completers in the endpoint cases purely from the
quotient relation.

### Consequence 15.2

The proper short-packet lemma should be paired with the separate endpoint alternatives:

> either there is an independent `q`-set, or there is a complete `q`-set, or there is a proper
> near-regular `(q - 1)`-set admitting a short zero-sum packet.

## 16. Proper missing-pattern count

The corrected proof target can be phrased as a single counting statement.

For `r = 1, ..., q - 2`, define

- `T_prop(G)`

to be

- `sum_r sum_{S near-regular target-r} #{x notin S : N(x) ∩ S = L(S)}`.

Then:

### Proposition 16.1

`T_prop(G)` counts proper regular induced `q`-sets with multiplicity exactly `q`:

- `T_prop(G) = q * #{proper regular induced q-sets}`.

### Proof

If `U` is a regular induced `q`-set of degree `r` with `1 <= r <= q - 2`, then deleting any
vertex `u in U` yields a proper near-regular `(q - 1)`-set `S := U \ {u}` of target `r`, and the
deleted vertex `u` satisfies

- `N(u) ∩ S = L(S)`.

So each proper regular `q`-set contributes exactly `q` counted pairs `(S, x)`.

Conversely, every counted pair `(S, x)` reconstructs a regular induced `q`-set `S ∪ {x}`.

### Consequence 16.2

Assuming `G` has no independent `q`-set and no complete `q`-set, the theorem is equivalent to

- `T_prop(G) > 0`.

So the remaining lemma can be stated as:

> **Proper missing-pattern forcing lemma.**
> For every graph `G` on `q^2` vertices with all degrees congruent modulo `q`, if `G` has no
> independent `q`-set and no complete `q`-set, then `T_prop(G) > 0`.

## 17. What this says in the first open case `q = 8`

For `q = 8`, after excluding independent and complete `8`-sets, the remaining target is:

> prove that some proper near-regular `7`-set `S` has its forced pattern `L(S)` realized by an
> outside vertex.

Equivalently:

> show that `T_prop(G) > 0`.

The additive reformulation remains:

- every proper near-regular `7`-set produces a zero-sum discrepancy sequence in `M_8(S) ~= C_8^6`;
- the missing proof step is to show that these quotient zero-sum constraints cannot all be realized
  without producing an actual completing pattern.

This is the sharpest corrected formulation I currently trust.

## 18. The strongest direct route: minimal zero-packets

The missing-pattern count `T_prop(G) > 0` is the cleanest exact formulation. But if one wants the
most attackable **direct proof route**, there is now a sharper extremal reduction.

Fix a proper near-regular `(q - 1)`-set `S`. Since

- `sum_{x notin S} d_x^S = 0`,

the whole outside layer `V \ S` is a zero-packet. So among all proper near-regular `(q - 1)`-sets
and all nonempty zero-packets attached to them, one may choose a packet `P` of minimum possible
size.

Write

- `p := |P|`.

If `p < q / 2`, then Proposition 14.1 already gives a completer, so the theorem follows.

Therefore the whole proof reduces to the inequality

- `p < q / 2`.

This motivates the following conditional target.

### Packet compression theorem

Let `q = 2^j` with `j >= 2`. Let `G` be a graph on `q^2` vertices whose degrees are all congruent
modulo `q`, and assume `G` has no independent `q`-set and no complete `q`-set.

Let `S` be a proper near-regular `(q - 1)`-set, and let `P subseteq V \ S` be a minimal nonempty
zero-packet:

- `sum_{x in P} d_x^S = 0`.

Then

- `|P| < q / 2`.

If this packet-compression theorem holds, then the main theorem follows immediately.

## 19. Structure of a minimal zero-packet for `q / 2 <= p < q`

Assume now that `P` is minimal and

- `q / 2 <= p < q`.

Write

- `A := L(S)`,
- `B := S \ L(S)`,
- `t := q - p`,

so `1 <= t <= q / 2`.

For each `s in S`, let

- `a_s := #{x in P : s in N(x)}`.

Because `sum_{x in P} d_x^S = 0`, there is some `lambda in Z / q Z` such that

- `a_s equiv lambda + p 1_A(s) [MOD q]`.

Since `0 <= a_s <= p < q`, this forces the exact two-level form

- `a_s = lambda` for `s in B`,
- `a_s = lambda - t` for `s in A`,

with

- `t <= lambda <= p`.

So every vertex of `A` receives exactly `t` fewer neighbors from `P` than every vertex of `B`.

This is the key rigid obstruction between the packet and the near-regular set.

### Boundary case `p = q / 2`

When `p = q / 2`, one has `t = q / 2` as well, so necessarily `lambda = q / 2`. Therefore

- `a_s = 0` for `s in A`,
- `a_s = q / 2` for `s in B`.

Since `|P| = q / 2`, this means:

- every `x in P` is nonadjacent to every vertex of `A`,
- every `x in P` is adjacent to every vertex of `B`.

Thus a threshold packet is an **anti-completer packet**:

- `N(x) ∩ S = B = S \ L(S)` for every `x in P`.

So the obstruction at the boundary is not arbitrary. It is already highly structured.

## 20. The remaining compression step

The direct strategy is now clear:

1. choose a minimal zero-packet `P`;
2. show that if `|P| >= q / 2`, then the rigid two-level packet structure can be compressed to a
   smaller zero-packet;
3. contradict minimality.

This compression is the only unresolved step in the current direct proof line.

The two live subcases are:

1. `q / 2 <= |P| < q`, where the packet has the exact two-level incidence pattern above;
2. `|P| >= q`, where one must show that such a large minimal zero-packet cannot occur in the first
   place.

The first subcase looks more promising, because one already has rigid incidence data with deficit

- `t = q - |P|`.

The second subcase is more global, and probably needs an additional argument beyond generic additive
combinatorics.

## 21. Current sharp direct target

So there are now two equivalent ways to state the open finite frontier:

1. the exact existence/count form:
   - `T_prop(G) > 0`;
2. the strongest direct extremal form:
   - every minimal nonempty zero-packet has size `< q / 2`.

The first is the cleanest exact theorem statement.  
The second is the most attackable direct proof route.

## 22. The packet-compression route reduces to one specific obstruction

The analysis above can be pushed one step further.

Inside the direct extremal route, the only unresolved obstruction with `p < q` is now the boundary
case

- `p = q / 2`.

Indeed:

1. if `p < q / 2`, Proposition 14.1 gives a completer immediately;
2. if `q / 2 <= p < q`, Section 19 gives a rigid two-level incidence pattern;
3. and when `p = q / 2`, that pattern collapses all the way to an anti-completer block.

So the only surviving obstruction inside the `p < q` regime is:

> a packet `P` of size `q / 2` such that every `x in P` satisfies
> - `N(x) ∩ S = B = S \ L(S)`.

Equivalently, if

- `g_S := [1_B - 1_A] in M_q(S)`,

then the boundary packet is exactly

- `q / 2` copies of the same class `g_S`,

and `g_S` has exact order `q / 2` in `M_q(S)`.

This is the true `2`-torsion atom at the packet-compression boundary.

## 23. Boundary elimination

Write

- `W := V(G) \ (S \cup P)`.

In the boundary case `|P| = q / 2`, every `x in P` is complete to `B` and anticomplete to `A`.
Therefore:

- `deg_G(a) = (r - 1) + 0 + deg_W(a)` for `a in A`,
- `deg_G(b) = r + q / 2 + deg_W(b)` for `b in B`.

Since all degrees are congruent modulo `q`, it follows that

- `deg_W(b) - deg_W(a) equiv q / 2 - 1 [MOD q]`

for every `a in A` and `b in B`.

So the leftover layer `W` must compensate the anti-completer block by seeing `A` and `B` with a
fixed nonzero residue gap.

There are three further exact consequences worth recording.

1. **Internal structure of `S`.**  
   Because vertices of `A` have degree `r - 1 = |A| - 1` inside `S`, one has
   - `deg_B(a) = #{non-neighbors of a inside A}` for `a in A`.
   And because vertices of `B` have degree `r = |A|` inside `S`,
   - `deg_B(b) = |A| - deg_A(b)` for `b in B`.
   So the anti-packet `P` sees `A` and `B` in exactly the opposite way from a true completer.

2. **`P` is a module relative to `S`.**  
   Every vertex of `P` has the same trace into `S`, namely `B`. So relative to `S`, the packet is a
   module. The only remaining unknowns are:
   - `G[P]`,
   - the graph between `P` and `W`,
   - the graph inside `W`,
   - and the traces of `W` into `S`.

3. **`W` is itself a zero-packet.**  
   Since the full outside layer `V \ S` has zero total discrepancy and the packet `P` already has
   zero sum, one also gets
   - `sum_{w in W} d_w^S = 0`.
   So in the boundary case, the leftover set `W` is a large zero-packet with no short zero-subpacket
   of size `< q / 2`, if `P` was chosen globally minimal.

This is the refined contradiction target: a huge zero-packet `W` with no short zero-subpacket, but
with exactly the residue bias needed to compensate the anti-completer block.

However, the isolated boundary anti-packet lemma is probably too weak as stated. The local data

- `P \perp A`,
- `P \sim B`

only control the cut between `P` and `S`; they leave

- `G[P]`,
- `G[W]`,
- `G[P, W]`,
- and the traces of `W` into `S`

essentially free. So one should not expect a direct implication

> anti-packet block `=>` regular `q`-set.

The correct final move must use the fact that `P` was chosen **globally minimal among all nonempty
zero-packets attached to proper near-regular `(q - 1)`-sets**.

For any balanced swap

- `S' := (S \ Y) \cup Z`,

with `Y \subseteq S`, `Z \subseteq W`, and `|Y| = |Z| = k`, the degree change of a surviving
vertex `s in S \ Y` is

- `\Delta(s) = deg_Z(s) - deg_Y(s)`.

Hence the surviving `A/B`-vertices satisfy

- `deg_{S'}(a) = (r - 1) + \Delta(a)` for `a in A \ Y`,
- `deg_{S'}(b) = r + \Delta(b)` for `b in B \ Y`.

So the exact balancing equation needed to flatten the old `A/B` gap is

- `\Delta(a) = \Delta(b) + 1`,

equivalently

- `deg_Z(a) - deg_Z(b) = deg_Y(a) - deg_Y(b) + 1`.

The boundary congruence on `W`

- `deg_W(b) - deg_W(a) equiv q / 2 - 1 [MOD q]`

suggests a small-support extraction principle from `W`. But this proposed balancing-compression step
is false in abstract form.

Indeed, write

- `q = 2m`,
- `u := [-1_A] in M_q(S)`,
- `g := [1_B - 1_A] in M_q(S)`.

Then in the quotient by constants,

- `g = [1_S - 2 1_A] = [-2 1_A] = 2u`.

So:

- an anti-completer contributes `g = 2u`,
- an empty-trace vertex contributes `u`,
- and `u` has order `q = 2m`, while `g` has order `m`.

Now take a packet in `W` consisting of

- `m - 1` anti-completers,
- `2` empty-trace vertices.

Its total discrepancy is

- `(m - 1) g + 2u = (m - 1)(2u) + 2u = 2m u = q u = 0`,

so this is a zero-packet of size `m + 1`.

But any nonempty subpacket has the form

- `a g + b u = (2a + b) u`,

with `0 <= a <= m - 1` and `0 <= b <= 2`. If moreover `a + b < m`, then

- `0 < 2a + b < 2m`,

so `(2a + b)u != 0`. Therefore this `m + 1` packet has **no nonempty zero-subpacket of size
`< m = q / 2`**.

Worse, it realizes exactly the same boundary compensation:

- each anti-completer contributes `1` to every `b in B` and `0` to every `a in A`,
- each empty-trace vertex contributes `0` to both sides,

so altogether

- `deg_W(b) - deg_W(a) = m - 1 = q / 2 - 1`.

Thus

> boundary anti-packet `+` modular compensation from `W`
> **does not imply** a small balancing witness or a short zero-subpacket.

So the balancing-compression lemma is dead in this abstract form. The surviving route must use
information from **other near-regular sets**, not just the fixed packet algebra for the current
`S = A \sqcup B`.

### Revised final target

The new obstruction is:

> replace one `m`-block of anti-completers by `(m - 1)` anti-completers plus `2` empty-trace
> vertices.

This still satisfies the exact boundary compensation, while evading every short zero-subpacket.
Therefore the next viable target is no longer a pure packet-compression lemma on the fixed `S`.
Instead one must show that the presence of those empty-trace vertices creates a **different proper
near-regular set** `S'` in which a genuine completer appears.

The important positive information here is a **seeding viewpoint**:

- the pure anti-completer part is rigid but locally sterile;
- the only genuinely new atoms in the obstruction are the `2` empty-trace vertices;
- so the realistic boundary attack is to use those empty-trace vertices as **seeds** for a new
  proper near-regular set.

In other words, the obstruction does not merely kill the abstract balancing-compression lemma. It
also points to the only viable replacement: track how the two empty-trace vertices interact with
`A`, `B`, `P`, and each other after one changes the ambient near-regular set. If a new proper
near-regular `S'` can be grown around those seeds, then one may recover a genuine completer or a
smaller packet in that new ambient set.

### Proposition 23.1 (the two-empty-trace seeds are too weak by themselves)

Keep the boundary setup above, and let:

- `u, v in W`

be empty-trace vertices, so:

- `N(u) ∩ S = N(v) ∩ S = emptyset`.

Consider a general reseating

- `S' := (S \ Y) ∪ Z`,

where:

- `Y = Y_A ⊔ Y_B subseteq A ⊔ B`,
- `Z = E ⊔ X ⊔ T`,
- `E := {u, v}`,
- `X subseteq P`,
- `T subseteq W \ E`,
- `|Y| = |Z|`.

Then exact degree bookkeeping gives:

- for `a in A \ Y_A`,
  - `deg_{S'}(a) = (r - 1) - deg_Y(a) + deg_T(a)`;
- for `b in B \ Y_B`,
  - `deg_{S'}(b) = r - deg_Y(b) + |X| + deg_T(b)`;
- for `z in E`,
  - `deg_{S'}(z) = deg_{X ∪ T}(z) + 1_{uv}`;
- for `x in X`,
  - `deg_{S'}(x) = |B| - |Y_B| + deg_{X \ {x}}(x) + deg_E(x) + deg_T(x)`.

From these formulas one gets three sharp negative consequences:

1. **Pure two-seed swap fails.**  
   If `Z = E`, then both seeds have degree `0` or both have degree `1`, so they can never create a
   proper near-regular `(q - 1)`-set.
2. **Adding one anti-completer is still too weak.**  
   If `Z = E ∪ {x}` with `x in P`, then one is forced into tiny-target exceptional cases
   (`r' <= 2`, at most `2` retained `B`-vertices, and in particular `r <= 3` if any old `B`-vertex
   survives).
3. **General seeded reseating needs large support.**  
   If `T = emptyset` and `|X| = x`, then the seeds force `r' <= x + 1`, but every inserted
   anti-completer sees all retained `B`-vertices, so:
   - `|B| - |Y_B| <= x + 1`.
   Moreover, if any old `B`-vertex survives, then:
   - `x >= r - 2`.

So the boundary seeding idea does **not** yet yield a theorem: the two empty-trace vertices alone
cannot build the new proper near-regular set.

There is, however, one further exact law on any successful supported reseating.

### Proposition 23.2 (pointwise compensation / separator law)

Keep the notation above, and write:

- `A' := A \ Y_A`,
- `B' := B \ Y_B`,
- `x := |X|`,
- `t := |T|`.

If `S'` is proper near-regular of target degree `r'`, then:

1. **seed/anti-completer size bound**
   - `r' <= x + t + 1`,
   - `|B'| <= r' <= x + t + 1`,
   so
   - `t >= |B'| - x - 1 = q - 2 - r - |Y_B| - x`.

2. **exact pairwise compensation law**  
   For every `a in A'`, `b in B'`,
   - `deg_{S'}(b) - deg_{S'}(a) = 1 + x + deg_Y(a) - deg_Y(b) + deg_T(b) - deg_T(a) in {-1,0,1}`.
   Hence for some `sigma_{ab} in {0,1,2}`,
   - `deg_T(a) - deg_T(b) = x + deg_Y(a) - deg_Y(b) + sigma_{ab}`.

3. **separator extraction**  
   Let:
   - `T_{a \bar b} := {t in T : t ~ a, t ⋢ b}`.
   Then:
   - `|T_{a \bar b}| >= max(0, x + deg_Y(a) - deg_Y(b))`.
   So if any surviving pair satisfies `deg_Y(a) >= deg_Y(b)`, the support `T` already contains at
   least `x` genuine `A`-over-`B` separators.

4. **averaged positive slice**  
   Averaging the pairwise law over `A' × B'` gives
   - `e(T, A') / |A'| - e(T, B') / |B'| >= x + e(A', Y) / |A'| - e(B', Y) / |B'|`.
   In particular, if the deleted set is not more `B'`-heavy than `A'`-heavy on average, then:
   - `t >= x`.

So a successful supported reseating cannot be built from vague extra mass in `W`: the support must
compensate the anti-completer block **pointwise**, and in particular must supply many `A`-over-`B`
separator vertices.

What remained missing at this stage was therefore no longer arbitrary large support, but a genuine
**support-extraction theorem** forcing such separators from global minimality:

1. seed-anti-completer incidences `N(u) ∩ P`, `N(v) ∩ P`;
2. seed-support incidences inside `W`;
3. the internal graph on the recruited support;
4. and enough traces into `A` and `B` to force the pairwise compensation law above.

One can push the global-minimality bookkeeping one step further.

### Proposition 23.3 (cyclic filter and off-cyclic separators)

Keep the boundary setup, write:

- `q = 2 m`,
- `u := [-1_A]`,
- `g := [1_B - 1_A] = 2 u`.

Then:

1. **global-minimality cyclic filter**  
   Let `R ⊆ W` with `|R| = s < m`, and assume
   - `Σ_{r in R} d_r^S = k u`
     in the cyclic subgroup `<u>`.
   Then necessarily:
   - `k <= 2 s + 1`.
   Otherwise one could complete that cyclic residue to `0` using fewer than `m` atoms (`anti`-completers
   if `k` is even, or one empty-trace seed plus anti-completers if `k` is odd), contradicting global
   minimality of the boundary packet.

   In fact this can be sharpened. Writing:

   - `n_R(y) := deg_R(y)` for `y in S`,

   the relation

   - `Σ_{r in R} d_r^S = k u`

   implies

   - `n_R |_A ≡ alpha`,
   - `n_R |_B ≡ beta`,
   - `beta - alpha = k - s`.

   So every small cyclic subset is already **exactly two-level** across `A` and `B`, and in
   particular:

   - `0 <= k <= 2 s`.

   Thus the older target `k > 2 |R| + 1` is impossible a fortiori.

2. **only three one-vertex cyclic classes are realizable**  
   If a single vertex `x` satisfies
   - `d_x^S in <u>`,
   then in fact:
   - `d_x^S in {0, u, 2 u}`,
   corresponding respectively to:
   - a completer,
   - an empty-trace vertex,
   - an anti-completer.
   So every genuine separator is necessarily **off-cyclic**.

3. **direct separator-mass extraction**  
   From Proposition `23.2`, the support `T` satisfies:
   - `Σ_{t in T} deg_{A'}(t) (|B'| - deg_{B'}(t))`
     `>= Σ_{a in A', b in B'} max(0, x + deg_Y(a) - deg_Y(b))`.
   Hence some `t in T` separates at least the average value of the right-hand side divided by `|T|`.

   Moreover, cyclic vertices contribute only constants to the compensation matrix

   - `D_{ab} := deg_T(a) - deg_T(b)`.

   Indeed:

   - completer contributes `+1`,
   - empty-trace contributes `0`,
   - anti-completer contributes `-1`.

   So all variation of `D_{ab}` across `A' × B'` comes from the off-cyclic support. Writing:

   - `T = T_cyc ⊔ T_off`,
   - `kappa := #(completers in T_cyc) - #(anti-completers in T_cyc)`,
   - `alpha(a) := deg_{T_off}(a)`,
   - `beta(b) := deg_{T_off}(b)`,
   - `p(a) := alpha(a) - deg_Y(a)`,
   - `q(b) := beta(b) - deg_Y(b)`,

   Proposition `23.2` becomes

   - `p(a) - q(b) = x - kappa + sigma_{ab}`,
   - with `sigma_{ab} in {0, 1, 2}`.

   Therefore there is one fixed integer `c` such that

   - `c <= p(a) - q(b) <= c + 2`

   for all `a in A'`, `b in B'`. Equivalently:

   - `osc_{A'} p + osc_{B'} q <= 2`.

   This is the exact **off-cyclic cancellation theorem**: after subtracting the deleted-set bias, all
   off-cyclic variation collapses to at most three adjacent levels total.

   In particular, if the compensation matrix is nonconstant and we write

   - `A_+ := {a : p(a) = max p}`,
   - `B_- := {b : q(b) = min q}`,
   - `delta := osc_{A'} p + osc_{B'} q`,

   then every pair `(a, b) in A_+ × B_-` satisfies

   - `sigma_{ab} = delta in {1, 2}`.

   So the extremal rectangle is a **uniform positive slice**.

So the supported-seeding route has now reduced one step further to a **one-vertex extremal descent /
freezing theorem**:

> if some `z in T_off` separates a nonempty extremal slice `A_z × B_z`, then either the unseparated
> remainder already yields a strictly smaller zero-packet, or after trimming to a nonempty rectangle
> `A_* × B_* subseteq A_z × B_z` all other support vertices are slice-constant there, so inserting `z`
> gives a supported reseating with `z` a completer.

Normalizing `min q = 0`, the width bound `osc_A p + osc_B q <= 2` leaves exactly five residual
patterns:

- `(1, 0)`,
- `(0, 1)`,
- `(2, 0)`,
- `(1, 1)`,
- `(0, 2)`.

One extremal descent finishes the first two cases immediately and reduces the third and fifth to those.
So the only genuinely new irreducible case is the mixed two-by-two pattern:

- `(1, 1)`.

Thus the only remaining irreducible direct case is the mixed `(1, 1)` pattern.

But this mixed case can itself be resolved by iterated one-vertex extremal descent.

Write:

- `A = A_0 ⊔ A_1`,
- `B = B_0 ⊔ B_1`,

with:

- `p | A_1 = 1`, `p | A_0 = 0`,
- `q | B_1 = 1`, `q | B_0 = 0`,

so the extremal rectangle is:

- `E_0 := A_1 × B_0`.

For a support vertex `z`, and a current mixed rectangle `E = R × C`, define:

- `U_z := R ∩ N_A(z)`,
- `V_z := C ∩ N_B(z)`.

If `z` is genuinely mixed on `E` (so `∅ ⊊ U_z ⊊ R` and `∅ ⊊ V_z ⊊ C`), descend to

- `E' := (R \ U_z) × V_z`.

This remains mixed and has strictly smaller area. Iterating, one reaches a terminal mixed rectangle
with no doubly-mixed support vertex. On the final separated slice cut out by the last separator:

- doubly mixed traces are impossible by terminality,
- one-sided traces fall into the already-resolved `(1, 0)` / `(0, 1)` descent,
- hence every remaining support trace is slice-constant.

So the mixed case is also resolved.

The only exact sublemma one can still isolate is:

> **terminal one-sided exclusion**: on a terminal mixed rectangle, any remaining nonconstant support
> trace on the final separated slice is one-sided, hence already reducible to the settled
> `(1, 0)` / `(0, 1)` cases.

Therefore the direct supported-seeding / packet-compression route is now **locally closed**.

## 24. Present status of the direct proof line

So the strongest honest direct reduction is now:

1. choose a minimal nonempty zero-packet `P`;
2. if `|P| < q / 2`, finish by proper short-packet rigidity;
3. if `q / 2 <= |P| < q`, reduce to the rigid two-level packet structure;
4. at the boundary `|P| = q / 2`, reduce further to a `q / 2`-block of anti-completers;
5. use global minimality together with the empty-trace part of the boundary obstruction to recruit a
   support set satisfying the **pointwise compensation / separator law**;
6. observe that every small cyclic subset is already rigid two-level and satisfies `k <= 2 |R|`;
7. subtract the cyclic contribution and the deleted-set bias to obtain off-cyclic level functions with
   total oscillation at most `2`;
8. use one off-cyclic separator to lower the extremal compensation by exactly `1` on its separated
   subrectangle;
9. reduce the residual patterns `(1, 0)`, `(0, 1)`, `(2, 0)`, `(0, 2)` by one descent;
10. iterate descent in the mixed `(1, 1)` case until a terminal mixed rectangle with no doubly-mixed
    support remains;
11. exclude terminal one-sided traces by the already-settled `(1, 0)` / `(0, 1)` branches, so the
    mixed case closes as well.

In other words:

> **The packet-compression route now closes locally: in the boundary case, `(m - 1)` anti-completers
> plus `2` empty-trace vertices can mimic the exact modular compensation without creating any short
> zero-subpacket, so one must pass through the exact pointwise compensation / separator law of
> Proposition `23.2`. Proposition `23.3` then rigidifies the cyclic part and bounds the off-cyclic
> width by `2`; one-vertex extremal descent resolves all non-mixed patterns, and the mixed `(1, 1)`
> case also collapses by iterating descent to a terminal mixed rectangle and invoking terminal
> one-sided exclusion.**
