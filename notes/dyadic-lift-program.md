# Dyadic Modulus-Lifting Program

This note records a concrete forcing route that would already prove the
regular induced subgraph conjecture if one missing finite theorem can be
established.

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

would be enough to attack the conjecture directly.

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

That is vastly larger than `log n`, so it would prove

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

The remaining fixed-support core is sharper still:

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

So the exact smaller theorem is **not** individual orbitwise vanishing `epsilon_[A]=0`, but the
triviality of the aggregate class `beta_m`, equivalently that the active-orbit family has constant
vertex-incidence parity (or symmetric difference `∅` / `U`). The visible top digit and the pure carry
cancel only after this aggregation.

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
