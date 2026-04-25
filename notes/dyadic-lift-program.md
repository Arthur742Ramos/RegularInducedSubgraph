# Dyadic Modulus-Lifting Program

This note records the concrete forcing route for the dyadic modulus-lifting step of the regular
induced subgraph proof.

## 1. The quantitative target

Write informally

- `W_q(n)` for the largest `m` such that every graph on `n` vertices contains
  an induced subgraph on `m` vertices whose degrees are all congruent modulo
  `q`.

The current formal development already shows:

- once `q` dominates the final bucket size, a `q`-modular witness collapses to
  an exact regular induced subgraph;
- the one-control, dropped-part, multiblock, and cascade modular packages are
  all equivalent asymptotically after one passes to the canonical frontier.

So a fixed-modulus lifting theorem of the form

> large `q`-modular witness `=>` smaller `2q`-modular witness

is enough to attack the conjecture directly, and the terminal-tail program below isolates the missing
dyadic obstruction-vanishing input for this lift.

## 2. The strong finite statement to aim for

The cleanest informal version is:

> **Polynomial-cost dyadic lift.**
> There is an absolute constant `C` such that for every power of two
> `q = 2^j` and every `m`, every graph that contains a `q`-modular witness on
> at least `q^C * m` vertices also contains a `2q`-modular witness on at least
> `m` vertices.

This statement is stronger than what the existing Lean objects literally
package, because composition across one lift step still has to remember the
deleted part. The likely Lean-facing version should therefore be formulated not
for plain modular witnesses, but for a fixed-modulus modular bucketing/cascade
object that keeps the dropped-part residue data explicit across the lift.

Still, the plain statement is the right quantitative benchmark: if a lift with
cost `q^C` exists in any composable witness package, then the conjecture
follows.

## 3. Why this would prove the conjecture

The parity base case is Gallai's theorem:

> every `n`-vertex graph contains an induced subgraph on at least `n / 2`
> vertices whose degrees are all even.

In the notation above, this is `W_2(n) >= n / 2`.

Assume now the polynomial-cost dyadic lift. Iterating from modulus `2` to
modulus `2^r` yields

`W_(2^r)(n) >= n / (2 * product_{j=1}^{r-1} (2^j)^C)`

and therefore

`W_(2^r)(n) >= n / 2^(1 + C * r * (r - 1) / 2)`.

If the final witness size is at most the final modulus, then the existing
collapse lemmas turn it into an exact regular induced subgraph. So it is enough
to choose `r` such that

`2^r <= n / 2^(1 + C * r * (r - 1) / 2)`.

Equivalently,

`log_2 n >= 1 + r + C * r * (r - 1) / 2`.

Hence one may take `r` on the order of `sqrt(log n)`, and the final exact
regular induced subgraph then has size

`2^r = exp(Omega(sqrt(log n)))`.

That is vastly larger than `log n`, so it proves

`F(n) / log n -> infinity`.

From the threshold point of view, the same argument gives

`forcingThreshold(2^r) <= 2^(O(r^2))`,

which is already subexponential in `2^r`. The existing threshold equivalence in
the repo then implies the conjecture.

## 4. Why this route matches the current machinery

The current Lean development already supplies the normalization needed after a
successful lift:

- `HasControlBlockModularCascadeWitnessOfCard`,
- `HasControlBlockModularBucketingWitnessOfCard`,
- `HasNonemptyControlBlockModularWitnessOfCard`,
- `HasSingleControlModularBucketingWitnessOfCard`,
- `HasSingleControlModularWitnessOfCard`,

are all equivalent in the unbounded asymptotic story.

So the real forcing problem is not which witness package to use. It is to prove
a composable fixed-modulus lift theorem inside one of those packages.

The main obstacle is the one already visible in the finite bucketing lemmas:

- ambient modular degree data survive restriction cheaply;
- the deleted-part residue must also be tracked;
- naive restriction of a `q`-modular induced subgraph does not by itself
  produce a `2q`-modular induced subgraph.

That is exactly why the likely formal target is a fixed-modulus modular
cascade/bucketing lift rather than a plain induced-subgraph lift.

## 5. Lean-facing formulation to try next

The most useful extra object to add is probably a fixed-modulus witness notion,
for example

`HasFixedModulusWitnessOfCard G k q`

meaning that `G` contains an induced subgraph on at least `k` vertices whose
degrees are all congruent modulo that specific modulus `q`.

The composable version should then be a fixed-modulus cascade or bucketing
object, for example an empty-control analogue of

- `HasControlBlockModularBucketingWitnessOfCard`,
- `HasControlBlockModularCascadeWitnessOfCard`,

where the modulus is fixed in advance and the dropped-part residues are carried
explicitly across one refinement step.

The finite theorem to aim for is now better phrased in the terminal-exponent form actually sufficient
for the current wrappers:

> **Terminal-exponent dyadic lift step.**
> Let `A := D + 1`, where `D` is the bridge exponent. For `q = 2^j`, prove that a fixed-modulus `q`
> cascade witness of size
> - `q^C (2q)^A`
> yields a fixed-modulus `2q` cascade witness of size
> - `(2q)^A`.

Once that is available, the downstream bridge already present in the repo consumes exactly the final
`(2^r)^A = (2^r)^D 2^r` witness needed for `TargetStatement`.

The fixed-support core isolated by the audit is sharper still:

> after freezing `m` bits on one final support `U`, force the residual class `eta_m(U)` to lie in
> `2 M_{q / 2^m}(U)`.

Equivalently:

> the decomposition-independent top packet-shadow sum
> - `bar eta_m(U) in M_2(U)`
> must vanish.

Equivalently again, fixing one basepoint `u_0 in U`, it is enough to prove the pairwise next-bit
congruences

> - `r_U(u) - r_U(u_0) ≡ 0 [MOD 2^(m+1)]`
>   for every `u in U`.

Moreover, every already-separated block `D` on which the external degree is constant modulo `q`
across `U` is silent for these pairwise next-bit functionals. So only the final undecomposed tail can
contribute to the missing top bit.

Writing `R` for that tail and `rho_R(u) := |N(u) ∩ R|`, the frozen first `m` bits give

> - `rho_R = K_m 1_U + 2^m h_m`.

So the next exact theorem is the vanishing of the terminal-tail class

> - `tau_m(R, U) := [h_m mod 2]`,

equivalently one more row-divisibility step

> - `rho_R = K_(m+1) 1_U + 2^(m+1) h_(m+1)`.

Equivalently, the normalized difference cocycle

> - `kappa_m(u, v) := (rho_R(u) - rho_R(v)) / 2^m [MOD 2]`

must vanish. Fixing a basepoint `u_0`, this basis family is already the smallest exact linear target.

If the tail neighborhood multiplicities are written

> - `n_A = 2^m q_A + r_A`,

then the exact cocycle depends only on complement-pairs `[A, U \ A]`, via the coefficients

> - `epsilon_[A] := floor((n_A + n_(U \ A)) / 2^m) [MOD 2]`.

Equivalently, the aggregate complement-orbit class

> - `beta_m := Σ_[A] epsilon_[A] [1_A]`

satisfies

> - `kappa_m = partial beta_m`.

In fact one has the exact identity:

> - `tau_m(R, U) = beta_m`
>   in `M_2(U)`.

For the fixed-witness dyadic lift there is one additional affine term.  The ambient q-modular support
`A = U union R` need not have all degrees congruent modulo `2q`; after fixing the common q-residue, write

> - `deg_A(u) = d + q b_A(u) [MOD 2q]`, with `b_A(u) in F_2`.

Then the target is not `beta_m = 0` by itself, but

> - `beta_m + b_A = 0`
>   in `M_2(U)` modulo constants.

Equivalently, the tail must be affine-complete:

> - `rho_R(u) = C + q b_A(u) [MOD 2q]`
>   for every `u in U`.

This is exactly the identity `deg_U(u)=deg_A(u)-rho_R(u)` written at the next dyadic bit.  The older
untwisted `beta_m` formulation is the special case in which the ambient support already has constant
top bit modulo `2q`.

Pairwise, the affine obstruction is the alternating form

> - `lambda_R(u,v) := ((rho_R(u)-rho_R(v))-(deg_A(u)-deg_A(v))) / q [MOD 2]`.

The lift holds exactly when `lambda_R` is identically zero.  If it is not, choose a basepoint `u_0`; the
bad cut is

> - `X = {u : lambda_R(u,u_0)=1}`.

Thus every affine carry obstruction has a single oriented-pair witness across `X`.  This is the pair
chamber that must either promote to a label-transporting q-complete descent packet or become one of the
support-local square breakers (`host-orient115`, `host-opppair123`, `host-silentedge128`).

In host notation that pair chamber is the reduced two-fiber overlap table: the one-sided repair classes
`Omega_10` and `Omega_01` are nonempty, and the affine obstruction is exactly the absence of a common
`0111` witness.  Filling the overlap makes `lambda_R` vanish on the pair; failure to fill it must expose
the complete shared-slack side that becomes the next q-complete descent packet.

After the standard local exits, this overlap atom has the split-marker quotient
`K_(q-2) disjoint_union H` with `H in {K_2, 2K_1}`.  The remaining finite selection is a clique in the
one-sided compensator/provenance fiber: size `(q-4)/2` for the adjacent pair `H=K_2`, and size
`q/2-1` for the independent pair `H=2K_1`, apart from the proper-divisor bypass.  Therefore the dyadic
carry endpoint is now the same common-package routing theorem as the host split-marker endpoint: absence
of the required compensator clique must produce Section-40 closure, a proper marker-complete split, or a
packet refinement.

With first-return interpreted in the saturated exchange complex `FR^sat`, this routing theorem is closed
by the saturated provenance/support-decrease proposition: the compensator components are admissible
modules, and any ambient splitter either becomes a saturated boundary row, gives a local/branch exit, or
exposes a smaller exchange-complete q-marker.  Therefore the strict higher-bit affine dyadic lift has no
remaining carry obstruction in the saturated proof pipeline; only the external path-saturation comparison
can distinguish the historical path-only convention.

The first bit `q=2` is different: the same affine equation reads
`rho_T(v)=c+2b_A(v) [MOD 4]` on the retained set, but the terminal marker has size `2`, so the
split-marker compensator quotient has no large marker side.  Gallai supplies the parity shadow only.  The
remaining first-bit input is exactly the loss-64 affine selector from parity-regular supports to
mod-4-regular supports.  Equivalently, after Gallai reduces the odd-parity case to an even induced
bucket, it is enough to prove the loss-32 even selector: every induced even-degree graph contains a
`1/32`-large induced subgraph whose degrees are congruent modulo `4`.  With an Eulerian orientation of
the even graph, the zero/two-residue strengthening asks for a large induced set `W` and a bit `r` with
both `out_W(v)` and `in_W(v)` equal to `r` modulo `2` on all retained vertices.  This bidirected parity
selector is sufficient but not equivalent, because the full selector may also return all degrees `1` or
`3 mod 4`.  In matrix language, the exact first-bit obstruction left after the higher-bit q-marker
closure is the deterministic principal-submatrix theorem for symmetric zero-diagonal matrices with even
row sums: find a `1/32`-large principal submatrix whose row sums are constant modulo `4`.  Edge-count
zero-sum partitions and random-graph modulo partitions do not imply this vertex-degree statement.  Nor do
the currently checked Scott/Ferber--Krivelevich parity tools: Scott gives a real bipartite mod-`k`
linear bound and frames the arbitrary-graph linear residue problem as a target, while
Ferber--Krivelevich and its prescribed-label extension remain mod-`2` inputs.  The primary-source
Alon--Friedland--Kalai theorem is also not enough: it produces non-induced regular subgraphs under
almost-regular/density hypotheses, so it does not select a large principal submatrix of an arbitrary
Eulerian witness.

The current internal attack is the exposed-layer refinement diagnostic.  Once a discarded layer has been
exposed and the retained set is refined by degree into that layer modulo `4`, its contribution remains
constant forever.  The desired constant would follow if the final self-layer contribution could be
synchronized without another factor; this is exactly the missing terminal self-layer lemma.

So if `beta_m != 0`, there is a unique proper nonempty subset `S_m ⊊ U`, up to complement, such
that:

> - `beta_m = [1_(S_m)]`,
> - `kappa_m = delta(S_m)`.

Equivalently, the bad next bit is always a single two-level split:

> - `rho_R(u) ≡ C [MOD 2^(m+1)]` on one side of the cut,
> - `rho_R(u) ≡ C + 2^m [MOD 2^(m+1)]` on the other.

Fixing a basepoint `u_0`, orient each complement-pair `[A]` by the unique representative `A^∘`
avoiding `u_0`. Then:

> - `S_m = Δ_[A active] A^∘`.

So a bad next bit is a canonical symmetric-difference cut obstruction, not an arbitrary orbit
pattern. Any symmetry preserving the coefficients `epsilon_[A]` preserves the partition
`{S_m, U \ S_m}`; in particular:

> - profile-primitivity forces `beta_m = 0`,
> - profile-transitivity forces `|S_m| = |U| / 2`.

More generally, if `Gamma` is the symmetry group of the terminal tail profile, then:

> - `beta_m in M_2(U)^Gamma`,

so the residual obstruction is exactly a fixed-space / invariant-cut problem. In particular:

> - if `M_2(U)^Gamma = 0`, then `beta_m = 0`;
> - if `dim M_2(U)^Gamma = 1`, then the whole obstruction reduces to one explicit cut-template.

At the actual last bit `m = j - 1`, there is one further exact exclusion:

> - a balanced cut `|S_(j-1)| = q / 2` is impossible.

Indeed the bad split would force `G[U]` itself to have two exact degree levels differing by `q / 2`
on equal halves, hence:

> - `|e_G(S_(j-1)) - e_G(U \ S_(j-1))| = q^2 / 8`,

which exceeds the extremal bound:

> - `(q / 2 choose 2) = q^2 / 8 - q / 4`

for the number of edges inside a `q / 2`-set. Therefore the actual last-bit obstruction cannot
survive any transitive terminal profile.

There is also a stronger orbit-level sharpening. Let `Gamma_prof` be the full symmetry group of the
terminal tail profile, i.e. the permutations preserving every multiplicity `n_A`. Then:

> - `rho_R`, `h_m`, and therefore `beta_m` are `Gamma_prof`-invariant;
> - every bad cut `S_m` is a union of `Gamma_prof`-orbits;
> - if `Gamma_prof` is transitive, then `beta_m = 0` for every `m`.

So the actual residual dyadic obstruction is not an arbitrary nontransitive cut, but a
**nonbalanced union-of-profile-orbits**. In particular, if the full profile action has exactly two
orbits on `U`, there is only one cut-template left up to complement.

More sharply:

> - if the full profile action has at most two orbits, the only possible last-bit obstruction is the
>   unequal two-orbit split;
> - the first genuinely unresolved case is therefore three full profile orbits;
> - in that case every bad cut is already a singleton-orbit template (one orbit versus the other
>   two).

This is sharp at the level of orbit data alone: every orbit-union class is fixed by the product of
the within-orbit symmetric groups, so any further closure must use arithmetic of the actual
multiplicities `n_A`, not just orbit structure.

In the three-orbit last-bit case, that arithmetic already collapses to the three exact orbit averages:

> - `r_i := (1 / |O_i|) sum_A n_A |A ∩ O_i|`;

and a bad bit is exactly one `q / 2`-outlier among them. Equivalently, the remaining obstruction is a
single orbit-average congruence template, together with the total-edge and active-pair parity tests
that detect the candidate bad orbit.

More sharply, those parity tests already kill every odd-outlier template. Writing:

> - `s_i := |O_i|`,
> - `E_i := sum_A n_A |A ∩ O_i|`,
> - `Delta_ab := s_b E_a - s_a E_b`,

the only parity-invisible case is the **even-outlier determinant template**:

> - `e_G(U, R) ≡ 0 [MOD q]`,
> - at least two orbit sizes are even,
> - the bad orbit is detected exactly by full `q`-divisibility on the opposite determinant and
>   half-`q`-exact `2`-adic valuation on the two determinants meeting the bad orbit.

Even more sharply, after normalizing:

> - `Theta_ab := Delta_ab / ((q / 2) |O_a| |O_b|)`,

the opposite-determinant condition is redundant: vanishing means all `Theta_ab` are even, and the
bad orbit is determined by the parity of the two normalized determinants that meet it. Choosing a
base orbit `O_3`, the entire three-orbit residual is the two-bit code:

> - `(L_1, L_2) := (Theta_13, Theta_23) [MOD 2] in F_2^2`,

with:

> - `(0,0)` = vanishing,
> - `(1,0)` = bad orbit `O_1`,
> - `(0,1)` = bad orbit `O_2`,
> - `(1,1)` = bad orbit `O_3`.

If exactly one orbit is odd and `e_G(U, R) ≡ 0 [MOD q]`, then that odd orbit cannot be bad, so the
whole dyadic front reduces to one concrete divisibility condition on the multiplicities:

> - `q |O_1| |O_2| | Delta_12`.

In the remaining all-even case, there is still a canonical first bit. Reorder so the unique
minimal-valuation pair is:

> - `v_2(|O_1|) = v_2(|O_2|) < v_2(|O_3|)`,

and define:

> - `B := (Delta_13 + Delta_23) / (2^(nu - 1) q |O_3|)`.

Then:

> - `B ≡ L_1 + L_2 [MOD 2]`.

So:

> - `B` odd means the bad orbit lies in `{O_1, O_2}`;
> - `B` even means the only possibilities are `0` and `[1_(O_3)]`.

Branchwise, the even side is already one divisibility test:

> - `q |O_1| |O_3| | Delta_13`,

while on the odd side only one nonzero pattern survives up to swapping `O_1, O_2`.

This determinant package is now branchwise sharp: explicit singleton-neighborhood models realize
vanishing, the minimal-pair branch, and the large-orbit branch. So no further manipulation of
`B, L_1, L_2` alone can finish the theorem; the remaining work is genuinely host-side template
exclusion.

Equivalently, the dyadic frontier is now exactly two host-side fixed-`D` positivity theorems:

- `H_min`: the minimal-pair singleton support `D = O_1` (up to swapping `O_1, O_2`);
- `H_big`: the large-orbit singleton support `D = O_3`.

In the all-even regime, Lemma `18.16J` forces `|O_1|` even and `4 | |O_3|`, so these supports never
meet the new `|D| = 5` host frontier. Thus the formerly first open sizes were:

- `H_min` at `|O_1| >= 6`,
- `H_big` at `|O_3| >= 8`.

Moreover, even-size deleted candidates are impossible. So the formerly first outside-candidate normal
forms are:

- `H_min(6)` with `r in {0,2}`,
- `H_big(8)` with `r in {0,2,4}`.

Thus `H_min(6)` is one finite rooted `7`-vertex theorem, while at `H_big(8)` only the regular-`8`
branch and the balanced marked-quad branch are genuinely new.

More sharply:

- `H_min(6)` is already a finite rooted `19`-template problem (`8` regular templates and `11`
  marked-pair templates);
- the regular-`8` branch reduces to the explicit low-degree cases `I_8`, `4 K_2`, `C_8`,
  `C_5 ⊔ C_3`, `2 C_4`, plus the cubic `8`-vertex regular list;
- the `r = 2` and `r = 4` branches of `H_big(8)` are genuinely new only through
  non-equitable localization failure.

More sharply now:

- `H_min(6)` is reduced to five non-equitable rooted templates;
- the regular-`8` branch is exactly the five cubic `8`-vertex graphs after the explicit low-degree
  cases;
- in `H_big(8), r = 4`, rooted complement normalizes to `m <= 4`, and the genuinely new cases start
  only at non-equitable `4 + 4` cuts for `m in {2, 3, 4}`.

More sharply now:

- the entire `H_min(6), m = 2` slice is the rooted two-factor catalogue `C_7 / (C_4 ⊔ K_3)`;
- therefore `H_min(6)` is down to exactly three genuinely new rooted templates;
- on the balanced `H_big(8), r = 4` side, the non-equitable `m = 2` slice is explicit
  (`P_6 ⊔ K_2` or `K_3 ⊔ P_3 ⊔ K_2`).

More sharply now:

- the `H_min(6)` residual splits as two cubic-root `m = 3` templates plus one explicit
  complementary `m = 4` lift of `P_4 ⊔ K_2`;
- the balanced `H_big(8), r = 4` branch is finite and explicit:
  - `m = 3` is an exact nine-pair catalogue,
  - `m = 4` is an exact eleven-pair catalogue,
  - up to rooted complement this is a finite `15`-catalogue,
  - equivalently, after removing the three equitable seeds `(I_4, 2 K_2)`, `(2 K_2, C_4)`,
    `(C_4, K_4)`, it is the single canonical `4 + 4` kernel of non-regular `4`-vertex pairs with
    edge gap `2`,
  - and this kernel always descends by one-vertex localization to a `3 + 3` edge-gap-one pair, so
    there is no separate irreducible balanced `r = 4` carry branch beyond the old `r = 2`
    localization-failure mechanism.

More sharply now:

- this is the minimal balanced carry kernel on the large-orbit side: any irreducible balanced carry
  obstruction already occurs at the smaller `3 + 3` edge-gap-one localization-failure branch;
- so the whole balanced `H_big(8)` carry frontier is a single host-side theorem at size `3 + 3`,
  still governed by the carry class `beta_m = tau_m` rather than parity-only pairing.

More sharply now:

- the `3 + 3` edge-gap-one kernel is completely explicit: up to swapping sides the only ordered
  pairs are `(I_3, K_2 ⊔ K_1)`, `(K_2 ⊔ K_1, P_3)`, `(P_3, K_3)`;
- rooted complement merges the first and third, and equitability is impossible at edge gap `1` on
  `3` vertices, so the balanced large-orbit carry frontier is exactly two minimal non-equitable
  kernels, the extreme kernel `I_3 / (K_2 ⊔ K_1)` and the middle kernel `(K_2 ⊔ K_1) / P_3`.

More sharply now:

- at the first open balanced case `q = 8`, the large-orbit obstruction is a single order-`4`
  anti-completer class `g = [1_B - 1_A]` on a proper target-`4` near-regular `7`-set;
- this explains exactly why `beta_m = tau_m` survives parity-only pairing: `2g ≠ 0` but `4g = 0`,
  so the old marked-quad `4 + 4` branch is just four copies of one order-`4` class before
  localization to the two explicit `3 + 3` kernels.

More sharply now:

- localization already supplies the support needed for the local packet-compression route on those
  two explicit `3 + 3` kernels, so pointwise compensation, cyclic rigidity, the off-cyclic
  oscillation bound, and one-vertex extremal descent eliminate both kernels;
- therefore no nonzero balanced carry survives on `H_big(8)`, and the dyadic frontier is reduced to
  `H_min(6)` alone, namely the two cubic-root `m = 3` templates and the complementary `m = 4` lift
  of `P_4 ⊔ K_2`.

More sharply now:

- there is now an analogous `P_4 -> P_3` descent on the remaining `H_min(6)` side: the complementary
  `m = 4` lift of `P_4 ⊔ K_2` is not localization-irreducible, because endpoint localization on the
  `P_4` side lands in the `m = 3` slice;
- hence the localization-primitive dyadic frontier is already the two cubic-root `m = 3` templates,
  and any theorem excluding those two templates automatically removes the residual `m = 4` lift as
  well.

More sharply now:

- even those two dyadic cubic roots are just localized forms of the old connected cubic closures
  `H_T` and `H_F`: restoring the peeled minimal-pair vertex recovers one of those two closures,
  while localizing back forgets only the true-twin / false-twin sign on the restored pair;
- therefore the primitive localized support is the same-trace `P_3` kernel, and the whole residual
  `H_min(6)` side is already absorbed by the previously closed cubic / same-trace package;
- the same-trace `P_3` kernel itself is already excluded by the closed internal-distinguisher
  theorem on the residual fixed fiber, so neither cubic root survives;
- hence the finite dyadic host frontier is empty: `H_big(8)` is closed, `H_min(6)` is empty, and
  the remaining issue for a general dyadic lift is no longer a surviving small host template.

So the exact smaller theorem is **not** individual orbitwise vanishing `epsilon_[A]=0`, but the
triviality of the aggregate class `beta_m`, equivalently that the active-orbit family has constant
vertex-incidence parity (or symmetric difference `∅` / `U`). The visible top digit and the pure carry
cancel only after this aggregation.

There is a useful compression of the remaining aggregation problem.  Suppose `beta_m != 0`, and let

> - `S_m ⊊ U`

be the corresponding bad cut.  Since `S_m` is a union of full terminal profile orbits, a purely
set-theoretic coarsening always turns it into a three-block singleton-cut obstruction:

- if both sides of the cut contain at least two profile orbits, split one side as `A_1 ⊔ A_2` and
  take the other side as `B`; then `beta_m` is, up to complement, the singleton block `B`;
- if one side is already a single profile orbit, split the other side into two nonempty unions of
  orbits and again get a three-block singleton-cut model;
- if there are only two profile orbits, this is the two-block endpoint of the same picture.

On these three coarse blocks the normalized row residue has exactly two next-bit levels, so the
determinant code is nonzero on precisely the pairs crossing the cut.  A weight-splitting theorem
would supply the needed stability under replacing genuine profile orbits by arbitrary unions of
profile orbits; only then would the closed `H_min/H_big` singleton-support analysis force
`beta_m=0`.

This identifies the global aggregation step more sharply.  It is not another finite
`H_min/H_big` template, and it is not orbitwise coefficient vanishing.  It is a
**coarsening-stability / many-orbit projection theorem**: a nonzero aggregate cut can be
localized to a genuine fixed-`D` host instance after merging all irrelevant profile orbits, even
though the merged blocks need not be homogeneous terminal profile orbits.

Equivalently, the coarsened obstruction is presently only a **weighted fixed-`D` obstruction**.  A
coarse block that is a union of profile orbits carries the orbit sizes and the internal multiplicity
distribution of the orbits it contains.  The next-bit residue is constant on the coarse side of the
cut, but the lower profile data inside that side need not be homogeneous.  The closed `H_min/H_big`
analysis applies to an ordinary singleton support `D` coming from one genuine profile orbit; it does
not automatically apply to a weighted union of several orbits.  The exact projection is supplied by
the weight-splitting theorem below:

- a **weight-splitting theorem**: any weighted coarse singleton-cut obstruction contains an ordinary
  homogeneous suborbit obstruction of the same `H_min/H_big` type; or
- a **weighted `H_min/H_big` theorem**: the finite host-template closures remain valid for the
  weighted orbit-union support produced by the coarsening.

The first formulation is not a formal linear consequence.  The parity-invisible determinant branch
can appear only after merging: for example two odd profile orbits may have no individual
all-even/minimal-valuation template, while their union has even size and can become the minimal-pair
or large-orbit support in the coarsened three-block quotient.  Similarly, normalized determinants
can have the required half-`q` valuation only after adding the two orbit contributions.  Thus a
nonzero weighted coarse cut need not contain an immediately visible bad single orbit.  Any
weight-splitting proof must use extra host structure (for instance, a vertex-level localization or
convexity theorem), not just the determinant algebra.  Absent that, the honest target is the weighted
`H_min/H_big` closure.

The weighted obstruction nevertheless has the same mixed-trace shape as the host square-breaker
frontier.  If a coarse block `B` is a union of genuine profile orbits and no single orbit inside `B`
already carries an ordinary `H_min/H_big` obstruction, then the first place where the merged
determinant obtains the forbidden valuation is a boundary between two lower-profile suborbits whose
individual contributions are harmless but whose sum is not.  Across that internal boundary the
current `m`-bit tail data are fixed, while the next lower profile data distinguish the two sides.
Thus the obstruction is a weighted mixed-trace breaker inside the merged block: fixed-trace
distinguishers are absorbed by the closed same-trace / cubic templates, and the only surviving
non-split case is a dirty mixed-trace row whose contribution becomes visible only after coarsening.

Consequently the remaining dyadic bridge can be phrased as a weighted version of the same terminal
host theorem:

> **Weighted mixed-trace splitting target.** Every weighted orbit-union singleton-cut obstruction either
> contains an ordinary homogeneous suborbit obstruction, or its first internal profile boundary is an
> admissible mixed-trace breaker and can be split off without destroying the bad cut.

Candidate proof and audit gap.  Pass to primitive carry support: divide all internal orbit-boundary coefficients by their
common `2`-adic factor and retain the odd primitive boundaries.  Refining a coarse block `B` along an
odd primitive boundary `B=B_0⊔B_1` preserves the formal aggregate class in `M_2(U)`:

> `[1_B]=[1_{B_0}]+[1_{B_1}]`.

This identity is not enough by itself.  It does not prove that one side still carries the full bad
determinant/carry cut, and it does not prove that a minimal nonsplitting primitive cycle is constant
against every outside row of the prime quotient.  Fixed-trace primitive boundaries are absorbed by the
closed same-trace/cubic templates, and clean primitive boundaries by the marked-add catalogue.  The
host audit below reduces the remaining dirty primitive boundary to first-return five-vertex
seed-packaging, and then closes it by the low-set update.  In the dyadic setting the same pointwise
marked-trace closure respects orbit-size weights, so the later weighted carry audit proves
`beta_m=0`.

The exact two-child carry endpoint can be stated without the surrounding determinant language.  Let a
coarse orbit-union block split as `B=B_0⊔B_1`, and let `c_i` be the primitive normalized carry
contribution of `B_i` to the relevant cut after dividing by the common `2`-adic factor.  The endpoint
case is:

> `c_0 ≡ c_1 ≡ 0` in every homogeneous child test, but `c_0+c_1 ≡ 1` in the coarse block test.

Equivalently, neither child exposes an `H_min/H_big` singleton support, while the carry
`floor((r_0+r_1)/2^m)` of the two lower residues is odd.  This shows why weight-splitting cannot be
proved by valuation algebra alone: the bad bit is created by the addition operation itself.  A proof
must identify the boundary between `B_0` and `B_1` with an ordered host-local separator, so that the
two-child carry either produces a homogeneous child after all or localizes to the binary
trace-coalescence / pair-chamber endpoint.

The sharpened host endpoint says more precisely what this ordered separator has to remember.  The
boundary between the two children must not merely define a mod-`2` cut; it must orient an elementary
two-row turn.  If the carry boundary supplies a sign depending only on the residual pair-chamber
cylinder, reversal kills the turn by the pair-chamber orientation normal form.  If it cannot supply
such a sign, then the two-child carry must localize a turn of the associated skew cycle to one
Section-`40` residual fixed fiber.  Thus the dyadic obstruction is now conditional on the same
oriented two-row holonomy localization theorem as the host binary endpoint.

With the turn-parity refinement, a dyadic carry boundary has only two irreducible host images.  If it
reverses the active separator side, the local host quartet must be balanced (`rs=xy`), so the carry is
exactly the two-fiber flip atom `{0101,0011}` with no `0111` row.  If it preserves the separator
side, the carry boundary sits on a same-side skew cycle, and the missing input is boundary
distinguisher routing: promote the first external boundary of that cycle without losing the weighted
bad cut.  Thus valuation algebra has been narrowed to two concrete host-local tasks, but it still
does not prove weight-splitting.

For the opposite-side flip, the arithmetic part is already harmless after common packaging.  The two
children contribute opposite raw defects `e_x-e_y` and `e_y-e_x`; in a single anchored discrepancy
space their sum is a zero relation of total mass `2<q`, so `40.16` would make both children
homogeneous completers.  Hence a two-child carry can survive only if the two children have not been
placed in one common discrepancy package, or if the carry lives on the same-side boundary-routing
branch.  The dyadic version of common discrepancy packaging is therefore: identify the same active
low/high pair and the same peeled set across the two weighted child boundaries before applying the
raw short-packet theorem.

The packaging audit separates unary data from pair-status data.  Pair-chamber equality fixes the
unary witness incidences of the two child boundaries, but the weighted raw vector also needs the
binary status of the chosen child representatives against the other local fibers.  Thus the dyadic
carry cannot be killed by `40.16` until the same binary pair-status constancy on the median fiber is
proved.

Equivalently, the weighted carry can still hide in the successor-side `0001` square: a single
pair-status coordinate is zero on the predecessor rail and first becomes one at the far successor
corner.  This is a pure mixed second-difference atom; all unary chamber data vanish on it, so it is
invisible to parity pairings and one-coordinate persistence.

The same-side carry boundary has no separate algebraic endpoint: an external boundary distinguisher
of the weighted same-side cycle is again one pair-status coordinate, and the first noncoalesced
boundary reduces to the same successor-side `0001` square.  Thus both the opposite-side carry and the
same-side carry are now controlled by this single hidden-square atom plus the raw two-packet
argument.

In dyadic language this atom is the anchored first-return positive AND carry: both lower child tests
have zero one-coordinate increment, but the mixed increment across the two children is one, and the
clean-corridor / first-return minimality conditions rule out predecessor-side shortcuts.  If either
successor edge coalesces, Section `40` removes the host image; otherwise the carry is exactly the
anchored first-return fully skew positive AND square.  This explains why parity and valuation data
still miss the endpoint: they see the child increments, not the oriented mixed second difference.

Geometrically, the same endpoint is the anchored first-return common-shadow failure: the two child
boundaries should determine one common Section-`40` shadow over the visible median point, but the
current data place them only in the ambient binary cylinder.  A common shadow would put the rooted
`P_5` seed in one frame and return the carry to the clean marked-add catalogue.

Sharpening the geometry, the dyadic carry endpoint is a two-shadow intersection problem.  Over the
forced visible median point `s_*`, the two child boundaries define fixed-frame shadow sets
`Sh_H, Sh_J` in the median fiber.  The carry is discharged exactly when `Sh_H cap Sh_J` is nonempty.
If one shadow is empty, this is the one-corner ambient-to-fixed lift gap.  If both shadows are
nonempty and separated, the closest-boundary argument leaves only the fully skew successor-side
first-return AND square.  The q-marker audit reduces that square to carrier/marker coupling, so
`beta_m=0` is reduced to that host-local endpoint rather than to additional determinant or parity
refinement; the product-firewall transport closure below discharges that endpoint.

Equivalently, the dyadic child shadows must be placed in one peeled Section-`40` package before raw
short-packet rigidity can act.  Without package equality the two child discrepancies live in different
coordinate spaces, so their carries cannot be added as a single relation of mass `< q`.  This is why
the dyadic carry was reduced to the first-return fixed peeled-package theorem, i.e. the same binary
pair-status constancy that identifies all raw discrepancy coordinates across the successor median
fiber.

The same warning applies to the endpoint degree-mass calculation.  In a terminal child square the
only positive mixed row is `0001`, and the only negative mixed row is `0111`; aggregate mass can only
say that positive carry rows are compensated by negative overlap rows after the rows have been put in
one coordinate package.  Thus the dyadic endpoint is now more sharply conditional on paired-compensator
routing: every positive first-return carry row must be paired with a negative `0111` overlap row in
the same peeled Section-`40` package, or else coalesce.  Only then does the aggregate carry
cancellation become a genuine mixed relation in one coordinate space.  A further unary-residual
alignment is still required before `40.16` can kill the carry as a raw short-packet relation: `0111`
cancels the mixed part of `0001` but contributes two unary successor increments.  Thus the dyadic root
is the same two-layer theorem as the host root: mixed compensator routing plus successor unary-leak
routing.

The unary-leak layer is the dyadic image of the one-corner ambient-to-fixed lift.  A leaked singleton
successor increment means the child transport is present in the ambient binary cylinder but has no
fixed-frame shadow over the forced median point.  Hence the dyadic full-residual carry endpoint
depends on exactly two host inputs: mixed compensator routing for the `0001/0111` mixed term and the
one-corner lift for the unary successor residuals.

The one-corner lift contribution is again the single hidden-square sign law: a child carry can hide in
a `0001` square whose lower child tests vanish and whose only positive bit is the double successor
corner.  This local model satisfies the visible unary data, so the dyadic carry cannot be removed by
endpoint mass or chamber components unless the host sign law or the full mixed-compensator bypass is
proved.

In host coordinates, that sign law is now the no-shared-slack theorem.  The fixed-witness interval
calculus shows the only positive `0001` failure is double same-sign spending of a one-unit slack row.
The coalesced and clean marked-add branches are closed; the dyadic carry can therefore survive only
through the dirty budget-one `Abs(1)` / prime-shell reanchor cycle-breaker endpoint, or through an
independent full mixed-compensator bypass.

That apparent bypass has the same obstruction on audit.  A `0001/0111` pair cancels the primitive
mixed carry but leaves the two unary successor increments of `0111`.  Any unary leak outside the
common peeled package is a one-corner shadow failure, and after marking it the only noncoalesced,
nonclean survivor is dirty budget-one `Abs(1)`.  Thus the dyadic carry endpoint is not split into two
independent final theorems: full compensator routing requires the same prime-shell reanchor
cycle-breaker unless a new, non-shadow proof aligns both unary increments at once.

Inside that cycle-breaker, same-defect reanchor turns are closed.  The reverse and forward outside
vertices at a same-defect middle state have identical trace over the fixed peeled package; primeness
plus Section `40.10` eliminates the resulting false-clone breaker.  Hence a dyadic carry cannot hide
in a pure token reanchor cycle.  It can survive only in a defect-switching turn, i.e. the two-defect
square where two different singleton repairs spend the same slack row and the missing fourth corner is
the `0001` carry atom.

The same shortest-cycle argument removes longer dyadic holonomy: after same-defect turns are closed,
the first inserted vertex that returns gives a clean corridor, and if the terminal defect-switching
square filled the return could be commuted earlier.  Thus an irreducible dyadic budget-one cycle has a
missing fourth corner, which is exactly the first-return `0001` carry square by the interval
calculus.

The remaining first-return carry square reduces by the same five-vertex audit.  After local
marked/root-edge failures are removed, the inserted-root degree tests force the two defect sites in a
positive shared-slack square to have the same miss/add type.  Two miss defects give an induced `P_4`
or house; two add defects give an induced `P_5` or `C_5`.  Section `40` closes all four weighted
quotient templates only after they are packaged in one fixed-fiber / prime weighted-quotient
attachment.  Thus the dirty budget-one carry endpoint is reduced to the same five-vertex
seed-packaging theorem.

The seed-packaging audit identifies the weighted dyadic version of the same missing datum.  The
five-vertex carry seed is combinatorially fixed, but the quotient equations still need the low-set
residue correction to be internalized or bypassed by a valid q-marker carrier/marker coupling theorem.

The host-local residue obstruction reduces before a weighted quotient package is needed.  The exact
low-set update for the first singleton reanchor forces the two deleted defects in a defect-switching
shared-slack square to form a marked two-class quartet: `{d,e}` and `{x,y}` are same-trace pairs whose
traces differ exactly on the shared-slack marker `R`, inducing `C_4` in the miss/miss case and `2K_2`
in the add/add case.  This is Section-`40`-shaped but not yet a Section-`40.10` same-trace `P_3`.
The marked two-class endpoint is not yet closed.  A minimal marker that is not split is a proper
module in the prime shell, and a preserved-side split gives a smaller first-return marker.  In the
fully skew splitter case, the dirty-split proof collapses only the active carrier to a binary crossing
component; it does not bound the number of retained slack rows in the marker.

The low-set congruence narrows the conditional host endpoint further.  For either same-type singleton
reanchor, the low-set update changes `|L|` to `|L|-|R|`; since both the original and reanchored states
have low-set size congruent to the same residue modulo `q`, any surviving shared-slack marker has
`|R| congruent 0 [MOD q]`.  Sub-`q` markers are impossible by congruence; q-markers remain conditional
on carrier/marker coupling in the fully skew splitter branch.

The latest audit also rules out a purely static degree-coupling closure.  A size-`q` fully skew marker
can be embedded in a `q^2-1` anchored near-regular residue table by taking
`L=R union {d,e}`, making `R` a perfect matching, adding `de`, and filling the high part with a
degree-`2` cycle.  This model is not claimed to survive first-return admissibility or Section `40`;
it only shows that static low/high residues alone cannot prove q-marker localization.  The missing
host input must be history-sensitive: a provenance-admissible fully skew splitter theorem, where the
splitter arises as a first failed row / transverse breaker, or a first-return side-marker theorem.
The admissibility branch also needs provenance selection: a nonmodule q-marker must have a splitter
inside that first-return failed-row / transverse-breaker family, not only an arbitrary prime
distinguisher.
Equivalently, the dyadic carry now depends on the q-marker provenance/support-decrease theorem:
an interval-nonadmissible provenance splitter must produce a first failed row whose support is a
genuine smaller first-return shared-slack marker.
This includes the row-to-breaker transport step: the failed interval row must become a valid
first-return breaker/candidate before the smaller-marker congruence can be applied.
It also includes the ordered first-return choice of that row; a static splitter can fail many interval
rows at once, and an unordered failure set does not define a descent.
Finally, the smaller support must be marker-complete: q-marker minimality applies only after the
failed support is identified with the whole shared-slack set of a new marked two-class quartet.
Non-marker first failures must instead be routed to local Section `40`, marked-add, or completer
exits; they do not give a smaller q-marker.
Thus the dyadic endpoint waits on the same three subclaims: provenance selection, local non-marker
exit, and marker-complete descent.
The provenance-selection subclaim requires a real routing theorem: primeness may produce only an
arbitrary splitter of the marker, while all ordered first-return/provenance rows could be constant on
the marker in the abstract local table.
Omni-saturation does not remove this selection issue, because it ranges over valid dirty-row /
repair-boundary traces rather than arbitrary ambient prime distinguishers.  The dyadic handoff needs
the same ambient-to-provenance routing bridge before `beta_m=0` can be claimed.
Once an ordered provenance row is available, non-marker first failures are local exits: inserted-root,
old-defect, and filler-row failures are absorbed by the same marked/root-edge, same-trace, or
marked-add catalogues used in the host proof.  The dyadic dependency is therefore provenance selection
plus marker-complete descent, not this local bookkeeping clause.
If the selected row has full square-provenance, marker-complete descent is also formal: the full
marker-internal wall-failure set is the shared-slack marker of the transported first-return square,
so congruence and minimality rule it out.  The dyadic dependency can therefore be sharpened to
ambient-to-square-provenance selection.
At exact marker size `|R|=q`, degree residues further force a state-internal splitter: if `T\R` were
constant on `R`, then `G[R]` would be regular and already supply a good `q`-set.  For larger markers
`|R|=m q`, this only gives internal degree congruence modulo `q`, not exact regularity.  Thus the
dyadic endpoint first needs a large-marker-to-exact-marker reduction, or a direct regular `q`-set
extraction from the larger congruent marker block; only then does state-internal splitter routing
become the final issue.
The natural missing input is an ordered-prefix/no-q-jump theorem for first-return wall failures: the
first marker-internal prefix with size divisible by `q` should have size exactly `q`, unless a
simultaneous wall block of size at least `q` already localizes or contains a regular `q`-set.
The frozen same-trace part of this extraction is now elementary: if a q-divisible marker block has
outside contribution constant on it, then its internal degrees are congruent modulo `q`; an induced
same-trace `P_3` is the roof false-clone Section-`40` template over the marked quartet, while a
`P_3`-free block is a union of cliques with congruent sizes and contains a regular induced `q`-set by
the `gcd(s,q)` clique selection.  The only
irreducible jump is therefore a non-frozen simultaneous wall block whose leftover rows avoid both
same-trace localization and marker-internal splitting after an exact `q`-prefix is selected.
Using the downstream positive-cost external-block bridge for that non-frozen block would still be
circular; the dyadic q-marker proof needs ordered first-return wall structure to provide the
extraction.
In trace-fiber language, the survivor is a zero-sum atom: every complete outside-trace fiber has
nonzero size modulo `q`, the total marker residue is zero, and no proper zero-sum union is known to be
first-return-complete.  A zero-residue fiber would close by the frozen cluster/P3 lemma, and a proper
first-return-complete zero-sum union would contradict marker minimality.  The ordered wall theorem
must therefore either produce such a real union, reduce to the exact two-splitter branch, or localize.
Tie-breaking a simultaneous wall is not enough, because arbitrary prefixes are not known to be
complete first-return shared-slack markers.
This routing is not a static degree-balancing fact; an internal filler may split `R` merely to equalize
the marker degrees.  The missing dyadic/host input remains ordered first-return geometry.
At exact size the host splitter is normalized as either low universal to `{d,e,x,y}` or high null to
that quartet; dyadic packaging still needs that splitter to become a Section-`40` package or a
square-provenance wall.
The low universal case has a `q+1` trap: if `R union {v}` has no second splitter, its induced degrees
are congruent modulo `q` and therefore exactly equal.  The high null case is not covered by this trap
without an additional residue conversion, because the splitter has the high residue rather than the
marker-row low residue.
With no second splitter, high null instead gives a one-excess `(q+1)` graph; if a neighbor of the high
splitter is isolated inside the marker, deleting it yields a regular `q`-set.  The residual
one-excess blocker is nonempty as a finite degree pattern already at `q=8`, but it necessarily
contains an induced same-trace `P_3` in the marker: otherwise the marker graph is a disjoint union of
cliques, the neighbor set `A` of the high splitter has size `a+1` but must be tiled by cliques of size
`a`, forcing `a=1` and the isolated-neighbor deletion.  This `P_3` is the Section-`40` roof
false-clone template: miss/miss gives the `C_4` `d-e-x-y-d` with marker trace `{x,y}`, and add/add is
the complement.  Thus high-null with no second splitter is closed by Consequence `40.10`; the dyadic
high-null dependency is only the two-splitter branch.  The exact-size dyadic dependency is therefore:
a normalized state-internal splitter `v` exists, and a second vertex `w` splits `R union {v}`; `w`
either splits the marker again or distinguishes only `v`.  Routing these marker-splitting and
singleton-lift alternatives to square-provenance or a local Section-`40`/marked-add/completer exit is
the remaining exact-marker input.
The singleton-lift alternative is now closed by the roof false-clone machinery: a second row constant
on `R` makes the marker one roof bag, and `v,w` form the `U_1` opposite-side breaker handled by
Proposition `39.10` and Proposition `40.3`.  Hence the dyadic exact-size dependency is only the
marker-splitting two-splitter branch.
This branch is the dyadic zero-sum atom.  The perfect-matching sign-vector table is only an
incidence-level warning because its marker is regular; an irreducible dyadic atom must be nonregular
inside `R`, with outside trace fibers compensating the low residues.  The complete outside-trace fiber
residues still sum to zero only all together.  The dyadic proof therefore needs a
first-return/provenance exclusion of such atoms; parity or static trace-fiber cancellation alone is
insufficient.
After Section `40.10`, the residual marker graph is a clique union, and Sections `39`--`40` also
remove any provenance splitter that cuts an internal clique.  Hence the dyadic zero-sum atom is
clique-coherent: splitters act only on the weighted clique quotient.
Each complete outside-trace packet is then a collection of equal-size cliques, so the dyadic atom is a
minimal zero-sum sequence of nonzero packet weights `n_i s_i` in `Z/qZ`.
It must also be divisor-sparse: for every `h | q`, fewer than `q/h` marker cliques have size at least
`h`, or a regular `q`-set is obtained by taking `h` vertices from each.
The arithmetic conditions are not contradictory: at `q=8`, `K_5 disjoint_union K_3` gives packet
weights `5` and `3`, a minimal zero-sum sequence.  Thus dyadic closure also needs provenance or
weighted-quotient packaging.
For exact markers, minimal zero-sum is automatic because the positive packet weights sum to `q`; no
zero-sum subsequence theorem can close that case.
If the resulting sub-`q` packets package into the prime weighted quotient theorem `40.12`, the dyadic
atom closes; hence the remaining dyadic obstruction is exactly weighted-quotient packaging for this
minimal zero-sum packet atom.
The local version needed at exact size is a packet-quotient regular-selection theorem of total weight
`q`; full `40.12` is sufficient but stronger than necessary.
This is an integral quotient-feasibility statement: choose marker-clique slices and
splitter/provenance packet weights of total `q` with one common induced degree.
For two marker clique packets `a>b`, a compensator clique of size `(a-b)/2` complete to the smaller
packet and anticomplete to the larger already gives a regular `q`-selection.
The converse holds in this quotient: any regular `q`-selection meeting both marker cliques and the
one-sided compensator side forces the selected compensators to be a clique of size at least
`(a-b)/2`.
Residue balance asks first-return order to provide this as a half-excess clique in the one-sided
compensator fiber.
Static same-trace data do not force the clique: at `q=8`, `K_6 disjoint_union K_2` with four
independent one-sided compensators has the right excess but no compensator `K_2`.
The same static packet-subquotient obstruction works for every even `q>=8` with
`K_{q-2} disjoint_union K_2` and `q-4` independent compensators complete only to the `K_2`.
It applies only in add/add or before the marked quartet is packaged: in miss/miss, `x,y` are adjacent
and complete to the marker, so the `K_{q-2}` packet plus `x,y` gives `K_q`.
More generally, miss/miss leaves no marker clique of size `q-2` or `q-1`.
In either same-type orientation a `q-1` marker clique closes by adjoining one inserted root, since
both roots are complete to the slack marker.  Thus the root-unclosed extremal clique is exactly the
add/add `q-2` case.
At exact marker size, this leaves only marker weight `2` outside that clique, so the missing
half-excess must be supplied by a genuine first-return/provenance packet.
If a one-defect/provenance row splits the clique, it isolates at most one slack row; any
marker-complete side is then sub-`q` and forbidden by the same low-set congruence.
An arbitrary ambient splitter is not yet a Section-`40` breaker, because the same-trace closure needs
one residual fixed fiber; the missing dyadic/host input is the same fixed-fiber routing.
Using the exact-marker internal-splitter reduction, a surviving add/add `q-2` clique is therefore
constant to every state-internal/provenance row; the internal splitter can only separate the residual
two marker rows.  The live endpoint is ambient-only clique-module routing from ambient breakers to
fixed-fiber or marker-complete data.
Any live ambient breaker has `epsilon>=2`; completers and one-defect breakers are already the closed
host/admissible-split cases.
Internally the endpoint marker is `K_{q-2} disjoint_union H` with `H` on the two residual rows:
mixed adjacency from a residual row to the clique gives a same-trace `P_3`, while complete adjacency
gives `K_q` with an inserted root.  Thus all remaining compensation is outside/provenance data.
The `H=2K_1` version closes if the compensator fiber contains a clique of size `q/2-1`; the
independent-compensator model is the static obstruction because it has no such clique.
At `q=4` both residual-pair cases close (`2K_2` directly, or `2K_2` using the single compensator), so
the live cross-split endpoint has `q>=6`.
For `H=K_2`, `q=6` also closes by the half-excess-one compensator selection; that branch is live only
for `q>=8`.
The two live branches are `H=K_2,q>=8` with missing `(q-4)/2` compensator clique and
`H=2K_1,q>=6` with missing `q/2-1` compensator clique; both need the same common-package routing.
Writing this size as `k(H)`, the `U`-using finite endpoint is absence of a `k(H)`-clique in the
one-sided compensator fiber; a same-trace `P_3` in that fiber would be Section `40` material after
fixed-fiber packaging.  There is also a divisor bypass avoiding `U`: for a proper divisor `h|q`, `h`
vertices from `A` and from `q/h-1` compensator components of size at least `h` give a regular disjoint
union of `K_h`'s.
These two alternatives exhaust the static split quotient: using `U` forces one compensator component
large enough to contain a `k(H)`-clique, and avoiding `U` forces equal selected clique sizes, hence the
proper-divisor pattern.
There is no hidden selection that spreads a `U`-using repair over many small compensator components:
equality with the `A`-degree first makes all selected component sizes equal, and the residual-row degree
then forces a single component (apart from the odd total-size `7` exceptional equation in the
independent-pair algebra, irrelevant for even `q`).  Hence multi-component selections are exactly the
`U`-free divisor bypass.
After those finite selections are removed, the cross-split packet is conditional only on
fixed-package routing.  If the ambient breaker of `A`, the provenance `U`-splitter, and the relevant
compensator component live in one peeled package, the breaker gives a proper sub-`q` marker wall and
the opposite `U` defects give a raw zero pair killed by `40.16`.  If they do not, the failure is the
same one-corner fixed-shadow / positive `0001` obstruction that controls `host-silentedge128`,
`host-opppair123`, and `host-orient115`.  Equivalently, after the visible median and unary chambers are
fixed, the only unfixed package coordinate is binary pair-status on the forced median fiber.
The positive coordinate is not a literal singleton at the irreducible endpoint: the double corner fails
on a whole shared-slack set `R`, and the low-set update forces `|R|=0 [MOD q]`.  Thus the dyadic
obstruction reaches the same q-marker carrier/marker coupling problem rather than a separate
single-coordinate parity failure.
The marked quartet cannot replace this clique in the live range: selecting `d` or `e` forces selected
degree at most one and hence too few clique vertices for `q>=6`.
If the fiber is `P_3`-free and has no `k(H)`-clique, it has at least three clique components by the
total-excess count.
Those components are first-return/provenance modules unless fixed-fiber or marker-complete subpacket
splitting closes them, so ambient component breakers are the same high-error routing problem.
Adding a high-error ambient splitter of the large clique while keeping all provenance rows constant on
it restores ambient primeness but not provenance splitting, so the routing input is genuine.
Equivalently, the exact endpoint is a cross-split between a provenance cut on the residual pair and an
ambient high-error cut on the large clique; forcing them into one first-return square is the packet
form of pair-chamber separation.
This is the product firewall form of the dyadic endpoint: the finite split quotient has no remaining
regular selection, while the two available cuts live in different packet coordinates.  The carry proof
therefore needs the same order-sensitive routing theorem as the host proof, not another valuation or
static packet-counting identity.
In dyadic terms this routing theorem is first-boundary completeness: when a minimal ambient packet
breaker is promoted to the next boundary row, its first failed interval test must either be local or
must expose an entire square-provenance wall on the split packet.  A single failed row is not enough;
the wall must be complete so that the low-set congruence can be applied before any carry summation.
The fixed-trace/coalesced and clean marked-support versions are already closed by Section `40` and the
marked-add catalogue, respectively.  Thus the weighted carry endpoint needs only the dirty
packet-internal completeness part of this statement.
For a clique-coherent packet, that completeness follows as soon as the ambient breaker is an ordered
boundary row: all packet rows differ only in their adjacency to that breaker, so the failed wall is a
whole breaker side (or the whole packet).  The dyadic obstruction therefore also reduces to
row-to-boundary transport/provenance selection for the ambient high-error breaker.
The product-firewall transport obstruction is sub-`q`: if transport failed, the square-breaker
reduction would produce a dirty shared-slack marker inside one side of the split packet.  The relevant
packets are the `q-2` clique or compensator components of size `<k(H)`, so the low-set congruence
excludes that marker.  Hence the weighted carry has no residual product-firewall escape once the host
packet quotient reaches this form.
The residual-pair cut is balanced modulo `q`: opposite provenance incidences on the two rows of `U`
must have equal mass after constant rows are removed, or else the branch is the anti-Horn/no-split
failure.
Once opposite `U`-splitters of total mass `<q` live in one peeled package, `40.16` kills them as a raw
zero-packet; the remaining issue is common-package identification.
Its packet quotient is split/disconnected, so the dyadic first-return input can be stated as
packet-primality/packaging: prime/non-split quotients fall to `40.12`, while split quotients must
produce a proper marker, half-excess clique, or local exit.
This is another ambient-to-provenance routing requirement: arbitrary breakers of packet modules must
be promoted to first-return/provenance packet refinements.

Likewise, the weighted quotient closure cannot simply absorb the whole marker as a seed bag: the bag
has size `q`, while the prime weighted quotient reduction uses bags of size `<q`; modulo `q` the whole
marker has zero weight.  Any split into smaller bags is exactly the submarker case already ruled out
unless first-return/admissibility supplies a genuine smaller marker.

After q-marker carrier/marker coupling, the weighted check is formal.  The marked-trace reduction is pointwise on
each support representative and marks the whole shared-slack set, so orbit weights only multiply the
same local configuration.  A nonzero weighted primitive carry would contain a representative dirty
boundary; the host-local low-set update routes that representative to the marked two-class kernel.
Weighted mixed-trace splitting and `beta_m=0` remain conditional on eliminating that kernel by
carrier/marker coupling.

Equivalently, the dyadic carry endpoint has become the dirty shared-slack / `Abs(1)` boundary.  The
carry is a double spend of one slack row.  Clean support is already removed by the marked-add
catalogue, and coalesced support by Section `40`; the remaining case is the prime no-holonomy theorem
for anchor-supported unique-defect reanchors.  The q-marker minimality/module argument closes only the
no-split and preserved-side parts; beta-vanishing still depends on the fully skew carrier/marker
coupling theorem.

The host reduction shows this is the same theorem as dirty split active-pair preservation.  A
weighted two-child carry can be split only after proving that the dirty boundary preserves an active
bad pair on one side, or else localizes to the fixed-fiber catalogues.  If neither side preserves the
active pair, the boundary is exactly the fully skew positive AND square / dirty shared-slack atom.
Thus the dyadic lift is now conditional on the same prime-shell mixed two-coordinate preservation
theorem as the host endpoint.

The host-side omni-saturation repair proves the split/localization disjunction: in a minimal carrier
saturated against every outside row that preserves an active pair, a dirty boundary either keeps an
active pair on one side or collapses to the binary endpoint; fixed-fiber and clean turns are already
closed.  Hence the dyadic carry no longer depends on a separate side-selection theorem.  The only
remaining carry endpoint is the fully skew positive AND / dirty shared-slack atom.

Raw parity pairings on vertices of `R` are therefore too weak for `m >= 1`, because carries after
division by `2^m` matter.

Any `m`-admissible packet decomposition is only a tool for certifying that vanishing; it does not
create extra freedom, since every such decomposition has the same total shadow.

## 6. Immediate experiments

1. Formalize the parity base case in a fixed-modulus form (`q = 2`).
2. Add a fixed-modulus dropped-part witness package, even if only as a local
   finite notion at first.
3. Try the first nontrivial lift `2 -> 4` with explicit bookkeeping, rather than
   attacking general `q -> 2q` immediately.
4. Isolate which part of the `2 -> 4` lift genuinely needs a control family and
   which part can be done with dropped-part residues alone.

I do not yet know whether the dyadic lift statement is true. The point of this
note is that it is now a precise quantitative theorem whose proof would already
settle the conjecture.
