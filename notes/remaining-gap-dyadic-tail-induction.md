# Remaining Gap: Dyadic Tail Induction

This note extracts a rigorous binary induction theorem from the last-gap analysis.

It does **not** prove the full bridge by itself. What it does prove is:

> if the internal dropped part can be organized into an iterated equal/complementary pairing tree,
> then the current bucket `w` is already an exact witness.

This is the cleanest formal version of the “bit-by-bit dyadic” idea so far.

## 1. The matrix form of the dropped-part problem

Fix the current refinement package at dyadic modulus

- `q = 2^j`, `j > 0`.

Let

- `w = {v₁, ..., v_q}`,
- `R := s \ w`.

For each `x ∈ R`, let `c_x ∈ {0,1}^q` be the column vector of the adjacency of `x` to `w`:

- `(c_x)_i = 1` if `x ~ v_i`,
- `(c_x)_i = 0` otherwise.

Then the dropped-part degree of `v_i` is exactly the `i`-th row sum

- `r_i := Σ_{x ∈ R} (c_x)_i`.

By the earlier memo, the current bucket `w` is already exact iff the row sums `r_i` are all
congruent modulo `q = 2^j`.

So the problem is:

> prove that `Σ_{x ∈ R} c_x` is a constant vector modulo `2^j`.

## 2. The basic binary pairing move

Take two columns `a, b ∈ {0,1}^q`.

Suppose either:

1. `a = b`, or
2. `a + b = 1`, where `1` denotes the all-ones vector.

Then in either case there exists `ε ∈ {0,1}` and a new binary column `d ∈ {0,1}^q` such that

- `a + b = ε·1 + 2d`.

Indeed:

- if `a = b`, take `ε = 0` and `d = a`;
- if `a + b = 1`, take `ε = 1` and `d = 0`.

So an equal/complementary pair contributes a vector whose parity is constant across all rows, and
whose half-remainder is again binary.

This is the key binary compression step.

## 3. Dyadic pairing tree

We now define the exact recursive structure that makes the `2^j`-divisibility theorem go through.

### Definition

Let `q = 2^j`.

A **dyadic pairing tree of depth `j` on the dropped part `R` relative to `w`** consists of the
following recursive data.

At level `0`, the leaves are the original columns `c_x ∈ {0,1}^q`.

For each level `m = 1, ..., j`, the multiset of columns present at level `m-1` is partitioned into
pairs, and for every pair `(a, b)` one has either

- `a = b`, or
- `a + b = 1`.

For each such pair, one defines the compressed column `d` by

- `a + b = ε·1 + 2d`

with `ε ∈ {0,1}` and `d ∈ {0,1}^q`.

The multiset of all these compressed columns `d` is then the level-`m` multiset.

At the final level `j`, no further condition is imposed on the level-`j` multiset.

Equivalently: every original leaf has been merged through `j` consecutive equal/complementary
pairings, so that the original total sum becomes

- `K·1 + 2^j S_j`

for some integer `K` and some binary-column sum `S_j`.

## 4. Main dyadic induction theorem

### Theorem 4.1

Assume the dropped-part columns admit a dyadic pairing tree of depth `j`. Then the row sums

- `r_i = |N(v_i) ∩ R|`

are all congruent modulo `2^j`.

Hence, in the current refinement-data setting, the bucket `w` is already a bounded exact
single-control witness of size `q` with control budget `q - 1`.

### Proof

We prove by induction on `m = 0, 1, ..., j` the following stronger claim:

> after compressing through level `m`, the original total row-sum vector has the form
>
> - `K_m·1 + 2^m S_m`,
>
> where `K_m` is an integer and `S_m` is the sum of the level-`m` compressed columns.

At level `0`, this is tautological with

- `K_0 = 0`,
- `S_0 = Σ_{x ∈ R} c_x`.

Now assume the claim holds at level `m`.

At level `m+1`, the level-`m` columns are partitioned into equal/complementary pairs `(a, b)`.
For each pair,

- `a + b = ε·1 + 2d`

for some `ε ∈ {0,1}` and binary compressed column `d`.

Summing over all pairs gives

- `S_m = E_m·1 + 2S_{m+1}`

for some integer `E_m`.

Therefore

- `K_m·1 + 2^m S_m`
  `= K_m·1 + 2^m(E_m·1 + 2S_{m+1})`
  `= (K_m + 2^m E_m)·1 + 2^{m+1} S_{m+1}`.

So the claim holds at level `m+1`.

At the final level `j`, the original row-sum vector therefore has the form

- `K_j·1 + 2^j S_j`.

Reducing modulo `2^j`, the second term vanishes. Hence the row-sum vector is constant modulo
`2^j`.

So all row sums are congruent modulo `2^j = q`.

By the previous memo, constancy of the dropped-part degree modulo `q` on `w` is equivalent to
regularity of `G[w]`, and regularity of `G[w]` together with the existing exact control block `t`
of size `q - 1` is equivalent to the desired bounded exact single-control witness on the same
bucket.

This proves the theorem.

## 5. What the theorem actually buys us

The theorem gives a fully rigorous criterion for finishing the bridge on the current bucket.

It says that the remaining hard proof can be attacked by proving **one** concrete structural fact
about the dropped-part columns:

> the columns can be recursively paired so that every pair is equal or complementary at each binary
> compression step.

This is much sharper than “control the dropped-part residue somehow”.

## 6. Why equal/complementary pairings are the right dyadic notion

The condition

- `a = b` or `a + b = 1`

is not ad hoc. It is exactly the condition under which a pair contributes a row vector whose parity
is constant across all rows, so that one binary digit is resolved and the problem divides by `2`.

In other words:

- identical pairs give parity `0`,
- complementary pairs give parity `1`,
- and both cases compress to a new binary column after removing the constant parity bit.

So the pairing tree is the natural `2`-adic analogue of the one-shot `q`-class pigeonhole step used
to create the control block `t`.

## 7. Relation to the current host-step

The current host-step already proves a one-shot statement:

- one can choose a control block `t` of size `q - 1`,
- and then choose `q` vertices with the same exact degree into `t`.

The dyadic pairing theorem suggests the right strengthening:

> after selecting the terminal bucket `w`, the remaining internal tail should not be left as one
> undifferentiated set; it should be recursively paired into equal/complementary columns relative to
> `w`.

If such a recursive pairing theorem can be extracted from the current host-step or proved by a
refinement of it, then the exact self-bridge is finished.

## 8. The concrete finite theorem now worth targeting

The rigorous remaining finite target can now be stated as follows.

### Dyadic Tail Pairing Theorem

In the exact-card refinement-data package at dyadic modulus `q = 2^j`, the dropped-part columns of
`R = s \ w` relative to the terminal bucket `w` admit a dyadic pairing tree of depth `j`.

### Consequence

The Dyadic Tail Pairing Theorem implies

- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`,

by Theorem 4.1.

## 9. Bottom line

This note turns the dyadic heuristic into a theorem:

- if the dropped part can be recursively paired into equal/complementary columns, then the bridge is
  done.

So the last remaining hard proof is no longer vague. It is now the very concrete combinatorial
statement that the dropped-part tail admits this `2`-adic pairing tree.
