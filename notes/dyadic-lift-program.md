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

The finite theorem to aim for is then:

> **Dyadic lift step.**
> For `q = 2^j`, every fixed-modulus `q` cascade witness of order `q^C * m`
> contains a fixed-modulus `2q` cascade witness of order `m`.

Once that is available, the asymptotic normalization already present in the repo
should convert it into a proof of `TargetStatement`.

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
