# Regular induced subgraphs: self-contained proof state

This document records the complete terminal proof using the canonical residue-saturated exchange
convention, together with the remaining dyadic lift input needed to turn that terminal proof into the
global theorem.  Conditional on the large-gap dyadic residual in Section 10, the dyadic reduction implies

```text
F(n) / log n -> infinity.
```

The original path-only formulation of Theorem G is not proved here.  That comparison remains open, but it
is not needed for the final graph theorem: the terminal descent is run directly in the canonical saturated
exchange complex, whose added boundary squares are actual four-corner graph exchanges with the same
terminal residue data.

## 1. Extremal function and threshold reduction

All graphs are finite, simple, and undirected.  For a graph `G` and a vertex set `S`, write `G[S]`
for the induced subgraph on `S`, and write `deg_S(v)` for the degree of `v` in `G[S]`.

Define

```text
f(G) = max {|S| : G[S] is regular},
F(n) = min { f(G) : |V(G)| = n }.
```

Also define the forcing threshold

```text
T(k) = min { n : every graph on n vertices contains a regular induced k-vertex subgraph }.
```

Then `k <= F(n)` if and only if `T(k) <= n`.

### Lemma 1.1

If there is a constant `A` such that, for all sufficiently large `r`,

```text
T(2^r) <= 2^(A(r+1)^2),
```

then `F(n) / log n -> infinity`.

### Proof

It suffices to prove that for every fixed `M` and all sufficiently large `k`, every graph on `2^k`
vertices contains a regular induced subgraph on at least `M k` vertices.

Choose `r = r(k)` maximal with

```text
A(r+1)^2 <= k.
```

Then `r -> infinity`, so `2^r >= M k` for all sufficiently large `k`.  By the threshold hypothesis,

```text
T(2^r) <= 2^(A(r+1)^2) <= 2^k.
```

Thus `F(2^k) >= 2^r >= M k`.

For an arbitrary `n`, choose `k` with `2^k <= n < 2^(k+1)`.  Monotonicity gives
`F(n) >= F(2^k)`, while `log n <= (k+1) log 2`.  Since `M` was arbitrary,
`F(n) / log n -> infinity`.

## 2. Modular terminal sets

For `q >= 1`, call a vertex set `U` `q`-modular if

```text
deg_U(u) = deg_U(v) mod q
```

for all `u,v in U`.

### Lemma 2.1

If `|U| <= q` and `U` is `q`-modular, then `G[U]` is regular.

### Proof

Every degree in `G[U]` lies in `{0,1,...,|U|-1}`, an interval of width `< q`.  Two integers in such an
interval that are congruent modulo `q` are equal.

## 3. Terminal hosts and dropped tails

Let `U` and `R` be disjoint.  Think of `U` as the surviving terminal bucket and `R` as the dropped
tail.  For `u in U`, define

```text
rho_R(u) = |N(u) cap R|.
```

Call `(U,R)` a terminal host at modulus `q` if `|U| = q` and the ambient degrees in `G[U union R]`
are constant modulo `q` on `U`.

### Lemma 3.1

If `(U,R)` is a terminal host at modulus `q` and `rho_R` is constant modulo `q` on `U`, then `G[U]`
is regular.

### Proof

For `u,v in U`,

```text
deg_(U union R)(u) - deg_(U union R)(v)
  = deg_U(u) - deg_U(v) + rho_R(u) - rho_R(v).
```

The left side is `0 mod q` by the terminal host condition.  The tail difference is `0 mod q` by
hypothesis.  Therefore

```text
deg_U(u) = deg_U(v) mod q
```

for all `u,v in U`.  Since `|U| = q`, Lemma 2.1 makes `G[U]` regular.

Thus the terminal problem is exactly to prove that `rho_R` is constant modulo `q`.

## 4. Dyadic obstruction class

From now on, let `q = 2^j`.  Suppose that, for some `m < j`, the first `m` binary digits of the tail
are already constant:

```text
rho_R = K_m 1_U + 2^m h_m.
```

Define

```text
tau_m(R,U) = [h_m mod 2] in (F_2)^U / <1_U>.
```

The next bit is constant exactly when `tau_m(R,U) = 0`.

For each `A subseteq U`, let

```text
n_A = |{x in R : N(x) cap U = A}|.
```

The complement-pair of `A` is `[A] = {A, U\A}`.  Define

```text
epsilon_[A] = floor((n_A + n_(U\A)) / 2^m) mod 2
```

and

```text
beta_m = sum_[A] epsilon_[A] [1_A] in (F_2)^U / <1_U>.
```

### Proposition 4.1: aggregate carry identity

For every `m < j`,

```text
tau_m(R,U) = beta_m.
```

### Proof

For `u,v in U`,

```text
rho_R(u) - rho_R(v)
  = sum_(A subseteq U) n_A (1_A(u) - 1_A(v)).
```

In the quotient by constants,

```text
1_(U\A) = 1_U - 1_A = -1_A.
```

Therefore the two members of the complement-pair `[A]` contribute through the single coefficient
`n_A + n_(U\A)`.  After division by `2^m` and reduction modulo `2`, the contribution of `[A]` is

```text
floor((n_A + n_(U\A))/2^m) (1_A(u) - 1_A(v)) mod 2.
```

Pairwise differences determine an element of `(F_2)^U / <1_U>`, so the class of `h_m mod 2` is exactly
`beta_m`.

### Corollary 4.2: nonzero carry gives a cut

If `beta_m != 0`, then after merging equal terminal profiles there is a nonempty proper cut
`S subset U`, unique up to complement, such that the normalized next-bit cocycle

```text
kappa_m(u,v) = (rho_R(u) - rho_R(v))/2^m mod 2
```

is nonzero across `S` and zero inside each side of `S`.

### Proof

Choose a representative `b in (F_2)^U` of the nonzero quotient class `beta_m`.  Since the quotient is
by constants, replacing `b` by `b + 1_U` is the only ambiguity.  Thus `supp(b)` gives a nonempty
proper cut, determined up to complement.  Proposition 4.1 identifies this representative with the
next-bit residue of the tail differences.  Merging terminal profiles on which this representative is
constant gives the asserted cut.

## 5. From a nonzero cut to a q-marker

A first-return boundary is:

- fixed-trace if it preserves the trace of the current cut;
- clean if it changes only one already marked coordinate;
- mixed otherwise.

### Lemma 5.1: fixed and clean boundaries do not carry the minimal obstruction

In a minimal obstruction with `beta_m != 0`, the first boundary seeing the cut from Corollary 4.2 is
mixed.

### Proof

If the first boundary is fixed-trace, the relevant trace class has constant outside contribution.
If that class contains an induced `P_3`, then the middle vertex and an endpoint have the same outside
trace and internal degrees differing by one.  The first-return exchange supplies the opposite unit
discrepancy, yielding a regular `q`-set.

If the class contains no induced `P_3`, then every component is a clique: otherwise a shortest path
between two nonadjacent vertices contains an induced `P_3`.  Equal outside trace and the modular degree
equations force the relevant clique sizes to have a common residue modulo `q`; selecting equal portions
from enough clique components gives a regular `q`-set.

If the boundary is clean, the two possible repairs differ by opposite unit vectors on a single marked
coordinate.  Their sum is zero in the quotient by constants, so one repair preserves the obstruction on
a smaller terminal profile suborbit, contradicting minimality.

Therefore the first boundary is mixed.

### Definition 5.2: q-marker

A q-marker is a tuple `(d,e,x,y; R)` with `R` nonempty such that:

1. `d,e` have the same trace outside `R`;
2. `x,y` have the same trace outside `R`;
3. the two traces differ exactly on `R`;
4. the marked quartet has one of the two complementary two-class patterns, called miss/miss and
   add/add;
5. `|R| = 0 mod q`.

### Lemma 5.3: mixed boundary produces a q-marker

A minimal mixed first-return boundary produces a q-marker.

### Proof

Let `d,e` be the deleted pair and `x,y` the inserted pair in the first failed exchange.  By
first-return minimality, the deleted vertices have one trace outside the slack rows spent by the
exchange, and the inserted vertices have one trace outside those same slack rows.  Let `R` be exactly
the set of slack rows on which the two traces differ.

The exchange preserves all modular degree equations except for the contribution of `R`.  Because the
exchange is a failed exchange inside a modulus-`q` terminal host, this contribution is `0 mod q`.
Thus `|R| = 0 mod q`.  The two signs of the exchange give the miss/miss and add/add quartet patterns.

Consequently, a nonzero `beta_m` produces a q-marker.

## 6. Local q-marker closures that are proved

### Lemma 6.1: unsplit marker is a module

If no outside row splits the marker set `R`, then `R` is a module.  Therefore no minimal prime
counterexample has an unsplit q-marker.

### Proof

If no outside row splits `R`, every outside vertex is either complete or anticomplete to `R`.  That is
exactly the module condition.  A nontrivial module cannot survive in a minimal counterexample: it can
be contracted, or replaced by another same-size subset with the same internal degree, without changing
any outside adjacency relevant to regularity.

### Lemma 6.2: frozen same-trace marker closure

If every splitter is constant on each same-trace component of a q-marker, then the graph contains a
regular induced `q`-set.

### Proof

Inside a same-trace component, all outside contributions are equal.  If such a component contains an
induced `P_3`, then the middle vertex and an endpoint have equal outside trace and internal degrees
differing by one.  The marked quartet supplies the opposite unit discrepancy, giving a regular
`q`-set by exchange.

If there is no induced `P_3`, every component is a clique.  Since `|R| = 0 mod q`, clique sizes in a
frozen trace fiber are congruent modulo `q`.  If a clique has size at least `q`, it contains `K_q`.
Otherwise all relevant clique sizes have a common value `s < q`.  If `g = gcd(s,q)`, the number of
such cliques is divisible by `q/g`; taking `g` vertices from each of `q/g` cliques gives an induced
`q`-vertex `(g-1)`-regular graph.

### Lemma 6.3: one-splitter closure

If a minimal q-marker has a splitter but no second independent splitter, then the graph contains a
regular induced `q`-set or a smaller q-marker.

### Proof

Let `z` be the unique splitter, up to complement of its cut on `R`.  The split gives a one-excess
degree profile across the two sides.  If a neighbor of `z` is isolated inside the marker side, deleting
that vertex leaves a balanced regular `q`-set.  Otherwise every neighbor of `z` is supported by an
internal marker edge, so there is an alternating length-two path across the split.  Together with the
marked quartet, that path gives the same unit-discrepancy exchange as in Lemma 6.2, producing a
smaller marker or a local regularizing exit.

## 7. Fully skew split quotient

After the previous local closures, the only q-marker endpoint left is fully skew.  In this endpoint the
active marker graph has the form

```text
R = A disjoint_union U,
A = K_(q-2),
U = {u_0,u_1},
G[U] in {K_2, 2K_1}.
```

Define

```text
k(H) = (q-4)/2   if H = K_2,
k(H) = q/2 - 1   if H = 2K_1.
```

### Proposition 7.1: split-quotient exhaustion

In the fully skew endpoint:

1. any regular selection avoiding `U` is a proper-divisor equal-clique selection inside `A`;
2. any regular selection using `U` must use one compensator component containing a `k(H)`-clique;
3. no regular selection using `U` can be spread over several smaller compensator components.

### Proof

If a residual vertex has mixed adjacency to `A`, then two adjacent vertices of `A` together with it
form a same-trace induced `P_3`, already closed by Lemma 6.2.  If a residual vertex is complete to
`A`, then adding one inserted root gives a `K_q` in the corresponding orientation.  Thus the residual
pair is anticomplete to `A`, and `G[U]` is either `K_2` or `2K_1`.

A regular selection avoiding `U` sees only clique packets.  Equal degree forces equal-size choices
from equal-trace clique pieces, which are exactly the proper-divisor equal-clique bypasses.

Suppose the selection uses `U`.  The two residual vertices have equal marked trace, and their degree
deficit must be supplied by one-sided compensators.  Direct degree equality gives deficit `(q-4)/2` in
the `K_2` case and `q/2 - 1` in the `2K_1` case.  Vertices selected from different smaller compensator
components are nonadjacent while having the same outside trace; equalizing degrees would require each
component to supply the full deficit.  Hence one compensator component containing a `k(H)`-clique is
necessary.

Thus all static selections have been exhausted.  The surviving configuration is a product firewall:

- provenance rows cut only the residual pair `U` or its compensator;
- ambient primeness cuts the protected packet `A` or a compensator component only through high-error
  breakers.

## 8. The exact gap

The product-firewall argument reduces the q-marker endpoint to the following theorem.

### Gap Theorem G: q-marker provenance/support-decrease

In a fully skew first-return q-marker endpoint, every ambient high-error splitter of a protected packet
has one of the following outcomes:

1. it is promoted to an ordered first-return boundary row;
2. it gives a local regularizing exit;
3. its first failed row carries a complete smaller first-return q-marker.

In the third outcome, "complete" is essential: the smaller support must be the entire shared-slack set
of a new marked two-class quartet, not just a failed row or a failed prefix.

At this stage of the reduction, the missing content is:

- provenance selection: a splitter produced by ambient primeness must be routed into the ordered
  first-return/provenance family;
- row-to-breaker transport: a failed interval row must become a valid breaker in the same first-return
  frame;
- marker-complete descent: a marker-internal failure must produce the whole smaller shared-slack marker.

Primeness alone does not prove this.  A static splitter can distinguish the marker while every valid
first-return/provenance row remains constant on it.  Static degree balancing also does not prove this:
it can create a splitter without square-provenance.  The closing argument below must use the ordered
first-return state complex, not just prime separation and congruence.

### Hard attack on Theorem G

The direct product-firewall attack splits into two pieces.

First, suppose the ambient high-error splitter `z` has already been transported into the ordered
first-return boundary family.  Then the ordered-row part is closed: Lemma 9.1 below shows that any
packet-internal failure is a whole side of the packet cut by `z`, hence a complete smaller marker;
failures at old defects, inserted-root tests, or filler rows are local exits.

Second, try to promote an arbitrary ambient packet splitter to such an ordered row.  The natural
minimal-counterexample argument is:

1. choose the ambient splitter `z` with first boundary-test failure as early as possible;
2. if the first failure is fixed-trace or clean, use the local closures;
3. if the first failure is packet-internal, use packet homogeneity to make a complete side-marker;
4. otherwise replace `z` by its first failed row and descend.

The descent is valid only while the first failed row preserves an active pair on one side of its split.
After saturating over all such preserving rows, the only remaining case is the binary crossing
endpoint: every surviving dirty row separates the unique active same-trace pair.  In that endpoint the
same-defect turns and long reanchor cycles reduce to a first-return defect-switching square.  The
exact low-set update for that square gives again a marked two-class q-marker with shared slack
`R` and `|R| = 0 mod q`.

Thus the product-firewall transport trap is not by itself a proof of Theorem G.  It would close the
endpoint once the first failed row is already known to be a square-provenance row, because then the new
marker lies inside one side of a proper packet and has size `< q`.  But proving that square-provenance
is precisely the missing transport step.  The attack therefore returns to Theorem G rather than proving
it.

Equivalently, Theorem G is now reduced to the following sharper statement.

### Equivalent remaining theorem: dirty shared-slack absorption

In a prime shell-local, anchor-supported, budget-one reanchor graph, no non-backtracking reanchor cycle
can have every boundary slack row fully skew.  More explicitly, some boundary of such a cycle must
either:

1. give a completer;
2. coalesce into a same-trace or false-clone local exit;
3. produce a valid square-provenance row whose complete shared-slack side is a smaller marker.

The same-defect turn case is closed: the previous outside vertex and the next outside vertex have the
same trace over the middle peeled set, so primeness plus the same-trace local closure gives an exit.
A shortest remaining cycle has a first inserted vertex that later returns; just before it returns, the
reverse move for the previous step and the forward return form a two-defect singleton square.  If that
square fills, the return commutes earlier, contradicting minimality.  If it does not fill, the
fixed-witness interval calculation says the failure is exactly double same-sign use of one retained
row's one-unit slack.  Marking all rows with that double-spend property gives the same q-marker
`R`.  Hence dirty shared-slack absorption and Theorem G are equivalent at the present proof surface.

This equivalence is useful, but it is not a proof: it still lacks a non-circular prime-shell
cycle-breaker or an ordered first-return invariant that orients the reversible singleton reanchor graph.

### Low-set update normal form of the dirty square

The dirty shared-slack square can be reduced further.  Work at a middle peeled state `T`, with low set
`L` and high set `B=T\L`.  Consider two singleton repairs, deleting `d` and inserting `x`, and deleting
`e` and inserting `y`.  Let `R` be the complete set of retained low rows whose one-unit slack is spent
by both singleton repairs in the positive orientation.  Thus each `r in R` misses `d,e` and sees `x,y`.
The double repair fails exactly on `R`.

The two defects must have the same type.  If one repair is miss-type and the other add-type, the
inserted-root degree tests force two incompatible values for the edge `xy`, so the square has already
exited through a local inserted-root failure.

Suppose first that both repairs are miss-type.  Then `d,e in L`,

```text
N_T(x) = L\{d},        N_T(y) = L\{e}.
```

After replacing `d` by `x`, the exact singleton low-set update gives

```text
L_x = {x} union (N_T(d)\{d}).
```

Since the second repair is allowed to fail only along the shared slack `R`, the trace of `y` in the
state `T-d+x` is

```text
N_(T-d+x)(y) = (L_x\{e}) union R.
```

On the other hand, the original miss trace and the inserted-root test give directly

```text
N_(T-d+x)(y) = {x} union (L\{d,e}).
```

Comparing the two displays gives

```text
e in N_T(d),
N_T(d)\{d,e} = L\({d,e} union R).
```

By symmetry the same formula holds with `d` and `e` interchanged.  Hence `d` and `e` have the same
marked trace once `R` is part of the frame, while `x` and `y` are the complementary same-trace pair.
The quartet `{d,e,x,y}` is the balanced `C_4`.

The add-type case is dual.  Now `d,e in B` and

```text
N_T(x) = L union {d},        N_T(y) = L union {e}.
```

The low-set update after replacing `d` by `x` is

```text
L_x = N_T(d)\{d}.
```

The second repair trace says

```text
N_(T-d+x)(y) = L_x union {e} union R,
```

whereas the original add trace gives

```text
N_(T-d+x)(y) = L union {e}.
```

Therefore

```text
N_T(d)\{d} = L\R,
```

and symmetrically for `e`.  Again `d,e` form one marked same-trace pair and `x,y` the complementary
pair; now the quartet is the balanced `2K_2`.

In both same-type cases the singleton repairs preserve the residue class of the low-set size.  The
displayed low-set update has

```text
|L_x| = |L|-|R|,
```

and similarly for the repair through `y`.  Therefore

```text
|R| = 0 mod q.
```

Consequently every dirty square with `0<|R|<q` is impossible.  The only survivor is a genuine q-marker:
`R` is a nonempty shared-slack marker of size at least `q`, with the two marked same-trace pairs
`{d,e}` and `{x,y}` separated exactly by `R`.

This proves that the dirty cycle-breaker, the defect-switching square, and the q-marker endpoint are
the same obstruction.  At this local stage it does not yet prove Theorem G.  If an outside splitter is
already known to produce a first-return-complete side `R'` of `R`, then the same low-set update gives
`|R'|=0 mod q`, and minimality kills the proper side.  The missing assertion is exactly that an ambient
splitter of `R` can be promoted to such a first-return-complete side, or else exits locally.  Without
that promotion, the low-set update produces the q-marker but does not split it.

### Abstract provenance-selection no-go

The missing provenance step cannot be replaced by primeness alone.  For even `q`, let

```text
R = {a_i,b_i : 1 <= i <= q/2}.
```

Let the marked quartet have the same-type pattern in which `d,e` have one trace on all of `R` and
`x,y` have the complementary trace on all of `R`.  For every sign vector
`sigma in {0,1}^{q/2}`, add an outside row `z_sigma` such that

```text
z_sigma ~ a_i  iff  sigma_i = 1,
z_sigma ~ b_i  iff  sigma_i = 0.
```

Then the outside rows separate all points of `R`; in particular `R` is not a module in the ambient
shell.  Each `z_sigma` is fully skew on every active binary pair `{a_i,b_i}`.  Nevertheless, if the
designated first-return/provenance family is declared to consist only of rows constant on `R`, then no
provenance row splits `R`.

This is only an abstract incidence model, not a counterexample to the graph conjecture.  Its point is
logical: from

```text
R is not an ambient module
```

one cannot infer

```text
some first-return/provenance row splits R.
```

Theorem G therefore needs an ambient-to-provenance routing theorem.  The routing theorem must use
ordered first-return data; it cannot be deduced from the q-marker incidence table, low-set congruence,
or prime-shell module pressure alone.

The same example also explains why a side split is not enough.  Both sides of
`R cap N(z_sigma)` are nonempty, but neither side is automatically the whole shared-slack set of a new
marked two-class quartet.  Minimality applies only to complete q-markers, so it gives no contradiction
until the side has square-provenance and satisfies the low-set update as a complete marker.

### Binary-carrier collapse does not bound the marker

There is another tempting shortcut: in the fully skew branch, the active carrier collapses to binary
crossing components.  This does not imply that the shared-slack marker has size `<q`.

For `q=4`, take

```text
R = {a_1,b_1,a_2,b_2}
```

with active binary components `{a_1,b_1}` and `{a_2,b_2}`.  Let the marked quartet have the same
two-class trace pattern: `d,e` miss every vertex of `R`, and `x,y` see every vertex of `R`.  Add two
outside rows

```text
z_1 sees a_1,a_2 and misses b_1,b_2,
z_2 sees a_1,b_2 and misses b_1,a_2.
```

Both rows are fully skew on every active binary component.  The family separates the marker rows, so
the marker is not an unsplit ambient module.  But the shared-slack marker still has size `q`; the
low-set congruence sees `|R|=0 mod q` and gives no contradiction.

The construction scales to every even `q` by taking `R={a_i,b_i:1<=i<=q/2}` and all sign-vector rows
which see exactly one endpoint of each active pair.  Thus the implication

```text
fully skew binary carrier  =>  sub-q marker
```

is false without a carrier/marker coupling theorem.  The missing theorem must say more than "the
active component is binary": it must show that a valid first-return splitter produces a complete
proper shared-slack side, or else that all such splitters are absent in a way that yields a genuine
prime-shell module or a local exit.

Thus there are only two sound closing routes left.

1. Prove a provenance-admissible fully skew splitter theorem: a fully skew row arising as a first
   failed row, transverse breaker, or repair-boundary row passes the relevant interval tests, unless it
   exits through the same-trace, marked-add, or completer catalogues.
2. Prove a first-return side-marker theorem: when such a splitter fails the interval tests, one of
   `R cap N(z)` or `R\N(z)` is not merely a nonempty side, but the complete shared-slack marker of a
   new first-return marked two-class quartet.

The first route is an admissibility theorem; the second is a marker-complete support-decrease theorem.
They are equivalent in the fully skew endpoint, because a nonadmissible provenance splitter must name a
first failed row, and the only way for q-marker minimality to apply to that row is for its failed side
to be marker-complete.

### Static residue-coupling no-go

The exact case `|R|=q` also cannot be closed from low/high residues alone.  For even `q>=4`, take a
set

```text
R = {a_i,b_i : 1 <= i <= q/2}
```

and make `R` a perfect matching by joining each `a_i` to `b_i`.  Add two low defects `d,e`, join
`d` to `e`, and put no edges from `{d,e}` to `R`.  Let

```text
L = R union {d,e}.
```

Every vertex of `L` has degree `1` inside `L`.  Add a high part `B`, anticomplete to `L`, whose induced
graph is `2`-regular and has size `q^2-1-|L|`.  Then in the peeled set

```text
T = L union B
```

the low vertices have internal degree `1` and the high vertices have internal degree `2`, so the
low/high residues differ by exactly one modulo `q`.

Now add two outside miss-type representatives `x,y` with

```text
N_T(x) = L\{d},        N_T(y) = L\{e},        xy = 1.
```

Then every row of `R` misses `d,e` and sees `x,y`; the pair `{d,e}` has one marked trace, the pair
`{x,y}` has the complementary trace, and `|R|=q=0 mod q`.  Thus the static low/high residue equations
are compatible with an exact marked two-class q-marker.

This is not a counterexample to the conjecture: it does not assert first-return admissibility,
minimality, or the absence of local exits.  It proves only that the missing coupling cannot be a static
degree-residue lemma.  The final input has to use history-sensitive data: ordered first return,
square-provenance, or a valid boundary-row transport theorem.

### Positive-AND common-shadow normal form

The transport gap has an equivalent one-corner form.  In a fixed first-return pair chamber, let
`M` be the hidden median fiber over the forced visible corner.  For a localized witness or fixed-frame
fiber `a`, define

```text
p_a(m) = 1_{m sees a},        m in M.
```

After the predecessor and one-coordinate persistence cases have been removed, every relevant hidden
`2`-face can be oriented as

```text
00, 10, 01, 11.
```

The forbidden successor-side first-switch pattern is

```text
p_a(00)=p_a(10)=p_a(01)=0,
p_a(11)=1.
```

Equivalently,

```text
p_a(11)-p_a(10)-p_a(01)+p_a(00)=1.
```

This is the positive AND square.  It is invisible to all one-coordinate data: both lower unary
increments are zero.  Hence predecessor persistence, one-side chamber labels, and endpoint parity
cocycles cannot rule it out.

If one successor edge of this square coalesces after marking the predecessor side, the same-trace /
false-clone local closure applies.  If the marked support is clean, the marked-add catalogue applies.
The irreducible case is therefore exactly a fully skew positive AND square: the two successor
off-root transports exist ambiently but do not lie in one common fixed peeled package.

In shadow language, let `Sh_H` and `Sh_J` be the sets of fixed-frame lifts in `M` realizing the two
successor transports.  The common-shadow theorem would say

```text
Sh_H cap Sh_J != emptyset.
```

If one shadow is empty, this is the one-corner ambient-to-fixed lift problem.  If both are nonempty
but disjoint, a shortest hidden path between them has a first successor-side boundary, and the
irreducible boundary is precisely the positive AND square above.  Thus the remaining transport theorem
is equivalent to:

```text
no first-return fully skew positive AND square.
```

Equivalently, the missing common-shadow statement is a fixed peeled-package statement.  Once the
visible median point and the ambient missing-corner set are fixed, the two successor transports already
share the unary chamber labels, the low/high cardinality residue, and the base low-set vector.  The only
coordinates on which their peeled packages can still differ are binary pair-status coordinates against
the other fixed-frame fibers.  Hence package equality is equivalent to:

```text
binary pair-status is constant on the forced median fiber.
```

If such a coordinate changes, choose a shortest hidden edge on which the predicate

```text
E_a(m) = 1_{m sees a}
```

changes.  After the predecessor-side shortening and coalesced-edge exits have been removed, that edge
is exactly a successor-side `0001` square.  Conversely, a `0001` square is precisely a binary
pair-status coordinate preventing the two raw discrepancy vectors from living in one peeled space.  So
the common-package theorem has no further hidden data: it is the single-witness pair-status
monotonicity / positive-AND exclusion.

This also identifies the exact strength of the needed sign law.  Ordinary median convexity of the
truth set of `E_a` is too weak: on a square, the singleton `{11}` is convex and gated, but it is exactly
the forbidden `0001` row.  Unary monotonicity is also too weak, because both lower increments of `0001`
vanish.  What is needed is the anti-Horn/submodular inequality

```text
E_a(11) + E_a(00) <= E_a(10) + E_a(01)
```

for the first-return successor square, or an equivalent routing theorem that packages any violation
into a proper complete q-marker.  Thus the positive-AND endpoint cannot be closed by a generic median
convexity assertion; it requires first-return pair-status submodularity or support decrease.

In this normalization the obstruction is the local Möbius coefficient

```text
mu(E_a) = E_a(11) + E_a(00) - E_a(10) - E_a(01).
```

Among the five surviving row types, `mu` is nonzero only for

```text
0001 :  mu=+1,
0111 :  mu=-1.
```

The positive row has no lower unary increments, while the negative row has both lower unary increments.
Therefore an aggregate identity in `sum mu` is useful only inside one peeled package and only after the
two unary increments of every `0111` compensator have also been routed inside that same package.  If a
negative compensator or one of its unary increments lives in a different package, it is exactly a
single-shadow / one-corner lift failure and reduces back to the same `0001` square after marking.  Thus
endpoint mass can close only a same-package Möbius-zero packet; the residual anti-Horn atom is an
unpaired positive Möbius packet, equivalently the shared-slack q-marker carrier.

The algebraic identity behind this is

```text
0001 + 0111 = 0101 + 0011
```

as four-corner incidence vectors.  Pairing a positive and a negative Möbius row does not make the
obstruction disappear; it converts the mixed term into the two unary successor increments.  If the two
unary rows `0101` and `0011` are actual rows of the same peeled package, the raw short-packet catalogue
can be applied to that package.  If either unary row is only a formal leak into a different package, the
identity has no raw-space meaning and the leak is exactly the one-corner ambient-to-fixed lift problem.
Thus the compensator route is equivalent to same-package realization of the identity above, not merely
to the scalar equality of the total Möbius mass.

Iterating this routing gives a second cycle normal form.  Pair a positive `0001` row with a negative
`0111` row whenever possible.  The pair emits two unary leaks, represented by `0101` and `0011`.  Each
unary leak has only two outcomes: it is absorbed in the same peeled package, or it is a one-corner
ambient-to-fixed lift failure and hence regenerates a successor-side `0001` square after the usual
predecessor and coalescence reductions.  A minimal unabsorbed compensator configuration is therefore a
directed Möbius-leak cycle:

```text
positive mixed row -> negative compensator -> unary leak -> positive mixed row.
```

If the whole cycle is realized in one peeled package, the identities
`0001+0111=0101+0011` telescope to a raw zero packet and the short-packet catalogue closes it.  Hence a
surviving cycle has nontrivial package holonomy: every scalar Möbius coefficient is balanced around the
cycle, but the rows live in different raw spaces.  This is the Möbius form of the replacement-cycle /
common-package obstruction.

This can be made into a cocycle criterion.  Make a graph whose vertices are the peeled packages reached
by the compensator/unary-leak routing, and whose directed edges are the single-shadow transports needed
to move a row from one package to the next.  Label an edge by the change of binary pair-status coordinate
under that transport.  If the sum of these labels around a closed route is zero, then the route has
trivial holonomy: all rows can be pulled into one common raw space, the Möbius identities telescope, and
the raw short-packet theorem closes the cycle.  Hence every surviving Möbius-leak cycle has a shortest
nonzero holonomy loop.  On such a shortest loop every proper subpath has a common package, while the
closing edge does not; the first closing failure is again exactly the successor-side `0001` square.
Thus the holonomy formulation is equivalent to first-return pair-status submodularity, not a new
independent invariant.

There is an important sanity check here.  If the edge label were the change of one globally fixed
predicate `E_a`, every closed-loop sum would be zero because it would be a coboundary.  Therefore any
nonzero holonomy cannot be scalar pair-status variation for a fixed witness; it must be **package
coordinate monodromy**: after transporting around the loop, the binary coordinate or peeled low-set
basis has returned in a different fixed-frame identification.  Thus the remaining theorem can be stated
as no first-return binary package monodromy.  If the monodromy is trivial, all pair-status labels live
in one raw space and the Möbius/replacement cycle closes by telescoping; if it is nontrivial, a shortest
monodromy edge is exactly the one-corner `0001` obstruction.

The monodromy has no independent higher-rank form.  Let a closed first-return transport loop act on the
finite list of binary pair-status coordinates over the forced median fiber, after quotienting out the
unary rows, fixed-trace rows, and local same-trace/false-clone kernels.  If the induced identification
fixes every remaining binary coordinate on the active support, then the initial and terminal peeled
packages have the same trace over every retained row; the loop is a frozen-frame module, so either the
raw rows telescope in one package or primeness supplies a local same-trace exit.  Therefore a nontrivial
loop has a first moved binary coordinate.  On a shortest such loop, all earlier edges carry that
coordinate in a common package, predecessor variations have already shortened, and unary variations have
already coalesced.  The first edge on which the coordinate leaves the common package is thus a rank-one
mixed row; up to complement and orientation it is the successor-side `0001` row, while the opposite
orientation is exactly the `0111` compensator whose two unary leaks must be routed back into the same
package.  Hence package monodromy is not a new global obstruction: after all local quotients, its first
nontrivial edge is the same rank-one positive-AND/support-decrease endpoint.

A shortest nontrivial package-monodromy loop has no chord.  Indeed, if two nonconsecutive vertices of
the loop have a common peeled package, the loop decomposes into two shorter loops in that package
identification.  If either shorter loop has nontrivial monodromy, shortestness is contradicted; if both
are trivial, the original loop is trivial.  Thus every proper interval of the loop has a common package,
and only the closing adjacent edge fails.

After the Möbius compensator routing above, such a chordless loop can also be taken sign-coherent.  An
adjacent positive/negative pair in a proper common package realizes

```text
0001 + 0111 = 0101 + 0011.
```

If the two unary rows remain in that proper common package, the pair telescopes and the loop shortens.
If one unary row leaves the package, that leak is a smaller one-corner lift failure, hence another
successor-side `0001` endpoint before the original loop closes.  Therefore a minimal final monodromy
survivor is a simple directed cycle all of whose adjacent edges have the same positive mixed sign; the
cycle carries no cancellation other than the q-marker congruence of the complete shared-slack bag.

Consequently the residues on a final monodromy cycle form a cyclic interval atom.  Label the consecutive
package-change packets by residues `b_1,...,b_l in Z/qZ`, with total residue zero.  A proper consecutive
interval of zero residue would be a proper common-package subcarrier, because every proper interval of a
chordless shortest loop already has a common package; the low-set congruence/minimality argument would
then close it.  Hence all proper cyclic intervals have nonzero residue.  The partial sums

```text
0, b_1, b_1+b_2, ..., b_1+...+b_{l-1}
```

are distinct in `Z/qZ`, so `l <= q`.  Thus the package-monodromy survivor has at most `q` adjacent
positive package changes.  If a stronger argument also forbids every proper formal zero-sum subfamily,
not just consecutive intervals, the Davenport extremal statement above applies and the length-`q` case
is the equal-generator atom.  Without that stronger realization input, the length-`q` cyclic interval
atom is still possible and is again a provenance, not arithmetic, obstruction.

The coordinate orbit of this monodromy is anonymous in the reduced frame.  If two binary coordinates in
the orbit were distinguished by any already admissible row, take the first edge of the monodromy loop on
which that distinguishing row changes coordinate.  If the change remains in the same peeled package, the
coordinate identification was not actually moved; if it leaves the package, this is a smaller one-corner
package failure.  After fixed-trace and false-clone exits have been quotiented out, all coordinates in
the monodromy orbit therefore have the same visible trace to the marked frame, to unary rows, and to
every admissible first-return row.  If no ambient row distinguishes the orbit, it is an admissible
module and the prime-shell module/local-exit catalogue closes it.  Hence a survivor has an ambient row
distinguishing the orbit, and we are exactly back at admissible-module primeness: the breaker must be
promoted to a first-return row, create a complete submarker, or exit locally.  Thus coordinate monodromy
and protected-packet admissible-module failure are the same final atom.

There is a last circular form of this atom.  Put the anonymous coordinates in their cyclic monodromy
order and restrict an ambient breaker `z` to them.  If the `z`-positive set is one cyclic interval, then
promotion of either boundary edge to the first-return family makes that interval a proper consecutive
subcarrier; the cyclic interval atom and the low-set congruence close it.  If the `z`-positive set has
two or more cyclic intervals, choose two separated boundary transitions.  The monodromy order and the
`z`-cut then give two crossing cuts of the same carrier.  If both cuts are realized in one package, their
four regions are the primitive `2x2` circuit; a realized diagonal closes, and absence of the diagonal is
exactly binary circuit elimination.  Therefore an ambient breaker of the final anonymous cycle has only
two possible residual faces: a non-promoted consecutive interval, or a non-realized crossing circuit.
Both are the same first-return provenance problem, expressed in circular order.

Equivalently, choose among all ambient breakers of the anonymous orbit one whose trace around the cycle
has the fewest sign changes.  It has at least two sign changes because it is nonconstant.  If it has
exactly two, its positive side is one cyclic interval and the previous paragraph gives the interval
subcarrier endpoint.  If it has more than two, two adjacent sign changes and a second separated pair of
sign changes determine crossing intervals.  Any admissible diagonal or run-separating row would either
realize the primitive `2x2` circuit or produce an ambient breaker with fewer sign changes, contradicting
the choice.  Thus the minimum-transition breaker normal form is:

```text
two transitions      -> cyclic interval subcarrier;
four or more         -> primitive crossing circuit with no realized diagonal.
```

This is a strict normal form, not a closure: the step still missing is promotion of the chosen ambient
transition to an admissible first-return boundary, or a proof that failure of promotion is itself a local
exit.

The circular normal form cannot be closed from cyclic arithmetic alone.  As an abstract trace model, take
`q` anonymous packet coordinates in a cycle, give each residue `1 mod q`, let the admissible rows be
constant on the whole cycle, and let package monodromy rotate the coordinates by one step.  Every proper
cyclic interval has nonzero residue, while the whole cycle has residue `0`.  An ambient breaker that is
positive on one interval realizes the two-transition face above, but if that breaker is not in the
admissible first-return family then no complete submarker has been produced.  An ambient breaker with
two positive intervals realizes the crossing-circuit face, but if no diagonal row is admitted then the
binary circuit-elimination step is absent.  Thus the final circular atom is consistent at the reduced
trace level; the proof must use graph-specific first-return history to promote a transition, produce the
diagonal, or exit locally.

The fixed-witness interval calculus identifies what such a square means.  Two individually admissible
successor repairs contribute the same sign to one retained row whose allowed interval is `{0,1}` or
`{-1,0}`; the double corner fails because both repairs spend the same one-unit slack.  Marking all rows
with this double same-sign saturation gives exactly the shared-slack set `R` of the dirty-square
normal form above.  Therefore the positive-AND/common-shadow root is not a separate obstruction:

```text
positive AND exclusion
<=> common-shadow / fixed-package routing
<=> dirty shared-slack absorption
<=> q-marker provenance/support-decrease.
```

This closes the circle of reductions, not the theorem.  The missing non-circular step is still an
ordered invariant or routing argument that turns an ambient splitter of the shared-slack marker into a
first-return-complete proper side, or else produces a local exit.

### Two-fiber overlap normal form

The same obstruction appears on the quotient side.  After the one-coordinate predecessor and
persistence data have been factored off, a local fiber coordinate on a hidden square has one of the
five rows

```text
0000, 0001, 0101, 0011, 0111,
```

where the four entries are the values at `00,10,01,11`.

Let

```text
Omega_10 = {coordinates with value 1 at 10},
Omega_01 = {coordinates with value 1 at 01}.
```

Then the five rows contribute as follows:

```text
0000 : neither Omega_10 nor Omega_01,
0001 : neither Omega_10 nor Omega_01,
0101 : Omega_10 only,
0011 : Omega_01 only,
0111 : both Omega_10 and Omega_01.
```

Thus the desired overlap statement is

```text
Omega_10 nonempty and Omega_01 nonempty  =>  Omega_10 cap Omega_01 nonempty.
```

The only reduced non-overlap table is exactly the two-row table

```text
0101, 0011.
```

This table is the balanced flip quartet: one row flips in the first hidden direction, the other flips
in the second hidden direction, but no row flips in both.  If both rows lived in one common peeled raw
discrepancy space, their raw discrepancies would be opposite,

```text
e_x-e_y,        e_y-e_x,
```

and their sum would be a zero raw packet of total mass `2<q`; the raw short-packet theorem would force
the missing common overlap.  Hence the only way the table can survive is if the two rows have not been
packaged in one common raw space.

Equivalently, the quotient-side endpoint is pair-chamber hidden-choice separation.  A fixed
pair-chamber cylinder records the two one-square endpoint labels but not an ordered sign for the
elementary hidden step.  If an ordered sign were forced by the cylinder, reversing the same elementary
step would force the same sign and its negative simultaneously, an impossibility.  Therefore no
nontrivial hidden step could stay inside one cylinder.

But endpoint chamber data are constant on a fixed cylinder and cannot produce such an antisymmetric
ordered sign.  The needed input is again the same first-return routing data: either identify the two
flipped rows inside one peeled package, giving the raw two-packet contradiction, or localize the
chamber-flat hidden step to the dirty shared-slack q-marker already described above.

This gives an exact intermediate theorem.  Pair-chamber equality identifies the unary chamber data on
the two incident squares, so it fixes the intended low/high active pair and the missing-corner incidence
set.  What it does not fix is the remaining binary pair-status part of the raw discrepancy vector.  If
that pair-status is constant on the relevant median fiber, the two rows `0101` and `0011` are represented
in one anchored raw-discrepancy space as `e_x-e_y` and `e_y-e_x`; their sum is a zero relation of total
mass `2<q`, so the raw short-packet theorem forces the common `0111` overlap.  If pair-status is not
constant, choose a first hidden edge on which a single witness changes.  The predecessor-side and
coalesced cases are already local, and the first successor-side switch is exactly the positive `0001`
square whose marked double-spent rows form the shared-slack q-marker.  Therefore two-fiber overlap,
binary pair-status constancy, and marker-complete support decrease are equivalent at this endpoint.

The hidden-edge version has no further coarse room.  Let `M_rho` be the forced one-corner median fiber,
and for a localized witness `a` put `E_a={m in M_rho : m~a}`.  If pair-status is not constant, choose a
bad hidden edge of `M_rho` and then a closest return of `E_a` on the far rail.  Any earlier far-rail hit
or predecessor-side suffix shortens the bad edge by the usual strip-transfer argument; any coalesced
successor edge is Section `40`.  Hence a minimal failure is a clean diagonal rectangle whose first
terminal square has pattern

```text
u_0,u_1,v_0 notin E_a,        v_1 in E_a.
```

This is exactly the successor-side `0001` square, not a new median-convexity obstruction.  Thus hidden
edge invariance, single-witness median-fiber monotonicity, pair-status constancy, and the q-marker
support-decrease theorem are all the same remaining assertion after predecessor and coalesced exits have
been removed.

### Packaged pair-exchange route

There is a host-side way to state the same missing package theorem.  Suppose the hidden one-corner
model has already been packaged as a peeled near-regular set `T`, and suppose we want to correct the
degree load by changing representatives in two fibers `F` and `G` while leaving every other fiber load
unchanged.  For a replacement pair `p'=(f',g')`, write the outside load profile

```text
lambda_(p')(H) = 1_{x_H sees f'} + 1_{x_H sees g'}       (H notin {F,G}).
```

A load-preserving pair exchange asks for

```text
lambda_(p') = lambda_(p)
```

and endpoint degree change `-e_F+e_G`.  After fixing the internal edge-status of the pair, this reduces
to finding a same-status replacement whose signed transfer sum is `-1`.

The natural proof would show that the feasible same-status replacements form an interval or ideal:
single-coordinate flips connect the feasible set, and the load changes by one at each flip.  Then a
nonminimal reference pair could be moved down by one unit.  But the needed ideal theorem is exactly a
two-coordinate anti-Horn statement.  On a localized candidate square, it says:

```text
00, 10, 01 feasible  =>  11 feasible.
```

This implication cannot be derived from one-edge predecessor or one-coordinate persistence data alone.
The abstract feasible set

```text
{00,10,01}
```

has both one-coordinate predecessors and all one-dimensional shadows visible from `00`, but it lacks
the corner `11`.  Thus the pair-exchange route also requires genuinely mixed two-coordinate input.

For a fixed witness, failure of this anti-Horn corner is again a positive mixed second difference:

```text
p(00)=p(10)=p(01)=0,
p(11)=1.
```

That is the same positive AND square.  The fixed-witness interval calculation identifies it with
double same-sign spending of a retained slack row; marking all such rows gives the shared-slack marker
`R`.  Therefore the packaged pair-exchange route does not bypass Theorem G.  It returns to the same
choice:

```text
prove a first-return anti-Horn / positive-AND exclusion,
or prove marker-complete q-marker support decrease.
```

### One-square silent-edge normal form

The one-square silent-edge formulation is another face of the same package problem.  Fix one filled
square `Q` and a repaired edge `e`.  Define the silent graph `Gamma_(Q,e)` as follows:

1. vertices are repaired opposite defects in the fixed opposite packet;
2. an edge joins two repaired opposite defects when the elementary hidden step between them preserves
   every unary witness incidence on `e`.

The one-square silent-component theorem identifies connected components of `Gamma_(Q,e)` with unary
chambers.  Hence edgelessness of `Gamma_(Q,e)` is equivalent to opposite-defect wall detection:
if an elementary hidden step changes the repaired opposite defect, it must cross a unary wall.

The exact minimal obstruction is therefore a single chamber-flat silent edge.  For such an edge
`(x,y)`, let `j` be the first repaired-defect coordinate with

```text
D_j(x) != D_j(y).
```

Chamber-flatness gives

```text
D(x)|_<j = D(y)|_<j,
P(x)|_<=j = P(y)|_<=j.
```

If one had an anchored one-corner lift, the shared lower repaired-defect prefix and the shared packet
prefix through `j` would realize the `y`-corner on the already anchored square `Q_j(x)`.  Fixed-square
opposite-defect rigidity would then force

```text
D_j(y)=D_j(x),
```

a contradiction.  Thus anchored one-corner lift plus fixed-square opposite-defect rigidity would make
`Gamma_(Q,e)` edgeless.

But this is conditional, not a proof.  The silent-edge hypotheses preserve unary witness incidences;
they determine only the unary chamber, i.e. the connected component of `Gamma_(Q,e)`.  They do not
identify the repaired opposite defect inside that component.  Any vertex statistic such as wall count,
support size, parity, or first changed coordinate is constant along a chamber-flat silent component or
forgets the orientation of the edge.  Therefore it cannot exclude a two-point silent component.

The missing lift is again a one-corner positive-AND problem.  The visible data force the lift location
and ambient binary-cylinder membership, but they do not prove that incidence to every local fiber is
constant on the hidden median fiber.  If one local fiber is mixed, the hidden-edge closest-return
reduction leaves exactly a successor-side first-switch square:

```text
0001.
```

Thus the one-square silent-edge atom is equivalent, at the current proof surface, to the same
single-witness median-square sign law and hence to the same shared-slack q-marker support-decrease
problem.

### Outgoing no-split and filled-overlap normal forms

The outgoing anti-Horn formulation is conditional but sharp.  Fix a boundary edge and let `R^+` be the
set of realized outgoing repaired opposite defects in the successor square.  If anchored witness
persistence holds, then every unary witness is incident either to all of `R^+` or to none of it.  The
one-square silent-component theorem identifies equality of all unary witness incidences with membership
in one silent component.  Therefore, if the realized no-split condition also holds on silent components,
then `R^+` has size at most one.

So the anti-Horn conclusion is formal once persistence, silent-edge exclusion, and componentwise
no-split are available.  Its failures are not new.  If persistence fails, take a shortest outgoing path
between a witness-positive and a witness-negative realized defect, and let the first witness-changing
edge be `ab`.  If `ab` lies in a statewise square with the same anchored boundary prefix, support-local
fourth-corner filling and silent-edge exclusion close the path.  If no such square contains `ab`, the
edge itself is a square-transverse breaker: the two endpoints are indistinguishable inside the frozen
repair chamber unless a prime-shell breaker sees the witness cut, and any fixed-trace breaker is already
a local same-trace / false-clone exit.  Thus outgoing anti-Horn reduces to repair-fiber cubicality and
then to the same square-breaker routing theorem.

The filled-overlap formulation has the same normal form.  Suppose two hidden choices in one fixed-trace
common-edge packet give the same repaired opposite defects on both incident squares.  On the union of
the two frozen square frames, the two hidden choices have identical trace; they are twins over that
filled-overlap frame.  A prime-shell breaker either has fixed trace on one incident square, giving the
local same-trace / false-clone exit, or its first trace change is square-transverse on one incident
square.  Hence filled-overlap pair-injectivity, pair-chamber hidden-choice separation, and the two-fiber
overlap lemma are downstream of the same square-breaker routing package; they are not independent
sources of the missing ordered sign.

In the named host-frontier notation, this leaves a single primitive.  `host-silentedge128` says that an
anchored one-corner lift on the first changed square `Q_j(x)`, together with fixed-square
opposite-defect rigidity, kills a chamber-flat silent edge; if the lift fails, the first missing corner
is the one-corner `0001` square.  `host-opppair123` says that anchored witness persistence plus realized
componentwise no-split on `Q^+` makes the outgoing realized set `R^+` a singleton; if persistence fails,
a shortest witness-changing outgoing path exposes a square-transverse breaker, again reducing to the
same `0001` square after local fixed-trace exits.  `host-orient115` says that pair-chamber separation of
the elementary hidden choice gives the two-fiber single-flip overlap; if separation fails, the hidden
step lies inside one fixed pair-chamber cylinder, and every endpoint-chamber statistic is orientation
blind.  Thus the three named frontiers are not independent branches: after the conditional implications
are made explicit, each remaining failure is the support-local square-breaker / shared-slack carrier.

The conditional implications themselves are formal.

1. `host-silentedge128`: assume the anchored one-corner lift on the first changed square `Q_j(x)` and
   fixed-square opposite-defect rigidity.  If `(x,y)` is a chamber-flat silent edge, let `j` be the first
   repaired-defect coordinate with `D_j(x) != D_j(y)`.  Chamber-flatness gives the same lower repaired
   prefix and the same packet prefix through `j`.  The one-corner lift realizes the `D_j(y)` corner on the
   already anchored square `Q_j(x)`, while fixed-square rigidity says that this square has only one
   compatible repaired coordinate-`j` opposite defect.  Hence `D_j(y)=D_j(x)`, a contradiction.
2. `host-opppair123`: assume anchored witness persistence and realized componentwise no-split on `Q^+`.
   Persistence makes every unary witness incidence constant on the realized outgoing set `R^+`.  The
   one-square silent-component characterization identifies equality of unary witness incidences with
   membership in one silent component.  Therefore all of `R^+` lies in one component, and no-split gives
   `|R^+|<=1`.
3. `host-orient115`: assume pair-chamber separation of the elementary hidden choice.  If
   `Omega_10,Omega_01` are nonempty but disjoint, the reduced five-row table leaves only a shortest
   fixed-trace path from a `0101` row to a `0011` row with no `0111` overlap.  At the first step where the
   hidden choice changes, all one-square predecessor/persistence walls have already been factored off, so
   both incident pair-chamber labels stay fixed.  This gives a nontrivial elementary hidden step inside
   one pair-chamber cylinder, contradicting separation.  Hence `Omega_10 cap Omega_01` is nonempty.

### Ordered-orientation no-go

The final obstruction can also be stated as an orientation problem.  Let `Sigma` be the pair-chamber
map on a common-edge hidden packet, and suppose an oriented elementary hidden step `eta -> eta'` has

```text
Sigma(eta) = Sigma(eta') = C.
```

An ordered proof would need a sign

```text
h(eta,eta') in {+1,-1}
```

with

```text
h(eta',eta) = -h(eta,eta').
```

If this sign were forced by the cylinder `C`, say `h(eta,eta')=omega(C)` for every elementary step in
that cylinder, then the reversed step would also give

```text
h(eta',eta)=omega(C).
```

Together these imply `omega(C)=-omega(C)`, impossible.  Hence no nontrivial elementary hidden step can
remain inside a cylinder on which such an ordered sign is forced.

This shows exactly what kind of data is missing.  Any invariant built only from endpoint chamber
labels, one-square silent components, support size, wall count, parity, or a dyadic mod-`2` cocycle is
constant on the fixed cylinder or forgets orientation.  Such data cannot produce the antisymmetric sign
above.  A proof must either construct genuinely ordered common-edge step data, or localize the hidden
step to the dirty shared-slack q-marker and prove marker-complete support decrease there.

The same no-go persists for scalar wall-order potentials.  Let `theta` be any integer potential on
hidden states whose value is determined by the current pair chamber, the first wall index, and the
unordered wall side.  The oriented edge value

```text
d theta(eta,eta') = theta(eta') - theta(eta)
```

is antisymmetric, but it is a coboundary.  Around a hidden square its signed perimeter sum telescopes to
zero.  Hence such a potential cannot supply the missing anti-Horn curvature; it can only prove that two
opposite routes through the square have the same total endpoint change.  The forbidden row `0001` is not
a nonzero perimeter circulation.  It is the two-dimensional same-row curvature

```text
p(11)+p(00)-p(10)-p(01)=1
```

for one retained row `p`, or equivalently two successor increments spending the same one-unit slack.
That curvature is defined only after the two increments have been placed in one peeled package and
identified as the same row.  If the increments live in different packages, the coboundary identity sees
only two unrelated unary leaks `0101` and `0011`; the first package leak is exactly the two-fiber
non-overlap table.  Thus an ordered first-wall scalar can at best locate the square.  It cannot by itself
turn the square into a complete shared-slack carrier.

Consequently the orientation route has a sharp dichotomy:

```text
common row/package for the two upper increments
    -> fixed-witness interval calculus gives the shared-slack q-marker;
no common row/package
    -> pair-status changes between the two increments, hence the {0101,0011} non-overlap atom.
```

This is another way to see that `host-orient115` cannot be proved by adding a cylinder-level orientation
invariant.  The needed ordered datum is not a scalar sign on a hidden edge, but a package-realized
two-face curvature or a proof that failure of such realization already yields a smaller support-local
marker.

### First-return wall-order attack

The only remaining source of an ordered sign is the first-return wall order itself.  Start with a
minimal chamber-flat hidden step and thicken it to the smallest hidden square in which a local
witness changes.  Write the square as

```text
00, 10, 01, 11.
```

The first-return order closes every predecessor-side return: if the witness returns on the predecessor
rail before the terminal successor square, the hidden edge was not minimal.  Likewise, if the first
changed wall is an old defect, an inserted-root test, or a filler row, the already proved local exits
apply.  If a successor edge coalesces after the allowed marking, the same-trace/false-clone local
closure applies.

Thus the wall-order attack leaves only the clean successor-side first switch

```text
p(00)=p(10)=p(01)=0,
p(11)=1.
```

Here the wall order tells us which square was first, but it does not supply a cylinder-intrinsic
orientation of the hidden edge.  Reversing the elementary hidden step preserves the pair-chamber
cylinder and the unordered first wall; it only reverses the direction in which the wall is crossed.
Therefore a potential depending on the first wall index, the two endpoint chambers, or the unordered
wall side is still constant under reversal and cannot yield the antisymmetric sign needed above.

The first-return order becomes useful only if the first wall is shown to be marker-complete.  In that
case the set of all rows that cross at the first wall is a complete shared-slack side `R'`; the low-set
update gives

```text
|R'| = 0 mod q.
```

If `R'` is a proper side of the original marker, minimality gives the desired contradiction.  If it is
not known to be complete, the same argument sees only one failed row or one failed prefix and q-marker
minimality does not apply.

So the wall-order attack proves exactly this conditional statement:

```text
first-return wall order + marker-completeness  =>  support decrease.
```

It does not by itself prove marker-completeness.  That assertion is again Theorem G's support-decrease
clause.

### Large-marker no-q-jump layer

There is one more layer inside marker-completeness.  The low-set update proves that any surviving
shared-slack marker has size a positive multiple of `q`, not necessarily exactly `q`.  If

```text
|R| = q,
```

and every row of the peeled state outside `R` is constant on `R`, then the internal degrees in `G[R]`
are congruent modulo `q`.  Since they all lie in `{0,...,q-1}`, they are equal, so `G[R]` itself is a
regular induced `q`-set.  Hence an irreducible exact marker has a state-internal splitter.

For a larger marker `|R|=m q`, the same argument gives only internal degree congruence modulo `q`;
degrees can differ by multiples of `q`.  Thus exact-size extraction needs an additional
large-marker-to-exact-marker theorem.

The hoped-for theorem is an ordered-prefix no-q-jump statement.  Along the first-return wall path, let
`F_t` be the prefix of marker rows that have become double-spent.  If every nonempty marker-internal
prefix were already a complete shared-slack marker, congruence would force `|F_t|=0 mod q`; the first
positive prefix would then have size `q`, unless one wall introduced at least `q` rows simultaneously.

The simultaneous-wall case is the obstruction.  Suppose `P` is the last complete prefix with
`|P|<q`, and a wall block `B` arrives next.  Choosing an arbitrary subset `B_0 subseteq B` with
`|P union B_0|=q` is not legitimate: `P union B_0` need not be the whole shared-slack set of any
transported first-return square.  The low-set congruence applies only to complete shared-slack sets,
not to lexicographic prefixes or arbitrary portions of a simultaneous wall.

Therefore a no-q-jump theorem would have to prove that the wall block itself either:

1. contains a regular induced `q`-set or a local same-trace / false-clone / marked-add / completer exit;
2. contains a proper union that is first-return-complete as a new shared-slack marker;
3. reduces to the exact-size state-internal splitter case.

Without such a theorem, the large-marker case remains part of Theorem G rather than a consequence of
the low-set congruence.

One large-marker subcase is closed outright.  Let `F` be a q-divisible shared-slack block on which every
row outside `F` in the peeled state and marked frame is constant.  Then the internal degrees in `G[F]`
are congruent modulo `q`.  If `G[F]` contains an induced `P_3`, the same-trace / false-clone local
closure applies over the marked quartet.  If it is induced-`P_3`-free, then `G[F]` is a disjoint union of
cliques.  Congruence of internal degrees makes all clique sizes congruent modulo `q`.  A clique of size
at least `q` already contains a regular `K_q`; otherwise all clique sizes are the same `s<q`.  Writing
`g=gcd(s,q)`, the divisibility `|F|=0 mod q` implies that there are at least `q/g` such cliques, and
choosing `g` vertices from each of `q/g` cliques gives a regular induced `q`-set.  Thus a surviving
large marker cannot be frozen; it must be a non-frozen simultaneous wall block whose outside trace
fibers have nonzero residues and no proper first-return-complete zero-sum union.

### Exact-size state-internal splitter layer

Assume now that `|R|=q` and that an irreducible marker has a state-internal splitter `v`.  The low-set
update normalizes the trace of such a splitter:

1. if `v` is a low splitter outside `R`, then `v` sees all four marked vertices `d,e,x,y`;
2. if `v` is a high splitter, then `v` misses all four marked vertices.

Thus exact routing splits into a low-universal case and a high-null case.

In the low-universal case, put

```text
S = R union {v}.
```

If no outside row splits `S`, then all vertices of `S` have congruent induced degrees modulo `q`.
Since `|S|=q+1`, the induced degrees lie in an interval of length `q`; the only possible obstruction
would be a mix of degrees `0` and `q`, but that cannot occur because `v` is nonconstant on `R`.  Hence
`G[S]` is regular, which is impossible in an irreducible counterexample.  Therefore a low-universal
exact splitter forces a second splitter of `S`.

The high-null case is different because `v` has the high residue while rows of `R` have the low
residue.  If no outside row splits `S=R union {v}`, the induced graph has a one-excess form: all marker
rows have degree `a`, while `v` has degree `a+1`.  If a neighbor of `v` is isolated inside `R`, deleting
that neighbor leaves a regular induced `q`-set.  Otherwise every neighbor of `v` has an internal marker
neighbor.  If `G[R]` were induced-`P_3`-free, it would be a union of cliques; the neighbor set of `v`
has size `a+1`, while its vertices have marker degree `a-1`, forcing an impossible clique tiling except
in the isolated-neighbor case.  Hence the residual high-null one-excess case contains an induced
same-trace `P_3`, which is exactly the local false-clone configuration already closed.

So an exact-size survivor has a normalized splitter `v` and a second splitter `w` of `R union {v}`.
If `w` is constant on `R` and distinguishes only `v`, the marker is one roof false-clone bag and the
pair `v,w` is the singleton-lift gate; the same local false-clone closure applies.  The only exact-size
branch left is therefore:

```text
two splitters, both nonconstant on R.
```

After same-trace local closures, the marker is clique-coherent: it is a union of cliques, and every
surviving provenance splitter is constant on each internal marker clique.  Within each complete
outside-trace packet, the clique sizes are equal and less than `q`.  Thus the residual exact atom is a
minimal zero-sum packet partition

```text
sum_i n_i s_i = q,
```

where `n_i` is the number of equal cliques in packet `i` and `s_i` is their common clique size.  A
zero-residue packet, a proper first-return-complete zero-sum union, or a dense divisor subfamily would
already give a regular `q`-set or a smaller marker.  Dense divisor subfamilies are excluded because if
there are at least `q/h` cliques of size at least `h`, selecting `h` vertices from each of `q/h` cliques
gives a regular induced `q`-set.

Arithmetic alone still does not close this exact atom.  For example, at `q=8` the marker

```text
K_5 disjoint_union K_3
```

is nonregular, induced-`P_3`-free, divisor-sparse, and has the minimal zero-sum packet equation
`5+3=0 mod 8`.  Outside trace packets can compensate its internal degree difference.  Therefore the
remaining exact-size theorem is not a bare zero-sum fact; it is a first-return packet-quotient
selection theorem.  One must either package the marker and splitter packets into the local weighted
quotient closure, find a regular `q`-selection using compensator packets, or expose a proper
first-return-complete zero-sum marker.

The two-packet quotient is completely explicit.  Let the marker be

```text
K_a disjoint_union K_b,        a>b,        a+b=q,
```

and put `a=b+2t`.  Suppose a one-sided compensator packet is complete to `K_b`, anticomplete to `K_a`,
and contains a clique of size `t`.  Choose

```text
a-t = b+t  vertices from K_a,
b          vertices from K_b,
t          compensator vertices.
```

The selected set has size `q`.  Vertices chosen from `K_a` have degree `b+t-1`; vertices in `K_b` have
degree `b-1+t`; compensator vertices have degree `b+t-1`.  Hence the selection is regular.

Conversely, inside this one-sided two-packet quotient, every compensating regular `q`-selection forces
such a clique.  If it chooses `alpha` vertices from `K_a`, `beta` from `K_b`, and `gamma` compensators,
degree equality between the two marker cliques gives

```text
alpha = beta + gamma.
```

The total-size equation gives

```text
alpha + beta + gamma = q = a+b = 2b+2t,
```

so `beta+gamma=b+t`.  Thus `gamma>=t`, since `beta<=b`.  The compensators must all have degree
`gamma-1` inside the chosen compensator set, so they contain a `gamma`-clique, and in particular a
`t`-clique.  Thus the two-packet quotient closes exactly by the half-excess clique condition.

Residue balance identifies the relevant signed fiber.  Since `a-b=2t`, the outside contribution to the
smaller clique must exceed the outside contribution to the larger clique by `2t` modulo `q`; in an
oriented first-return packet with excess below `q`, this is an actual one-sided compensator fiber of
size `2t`.  The missing two-packet theorem is therefore:

```text
the signed half-excess compensator fiber contains a t-clique,
or its absence routes to a local fixed-fiber closure, a smaller complete marker, or a packet refinement.
```

Static residue data do not imply this.  For every even `q>=8`, the quotient

```text
K_(q-2) disjoint_union K_2
```

with `q-4` independent one-sided compensators complete to `K_2` and anticomplete to `K_(q-2)` has the
required residue compensation but no half-excess compensator clique.  Any regular selection using
`x` vertices from `K_(q-2)`, `y` vertices from `K_2`, and `z` compensators would, in the only possible
mixed case, force `z=1`, `x=y+1`, and `x+y+z=q`; hence `2y+2=q`, impossible because `y<=2` for
`q>=8`.  Selections avoiding the residual pair are exactly the proper-divisor equal-clique bypasses,
already excluded.  Thus packet-quotient regular-selection is not a static theorem.

The extremal `q-2` clique also exposes the orientation dependence.  In the miss/miss orientation, the
two inserted roots are adjacent and complete to the marker, so `K_(q-2)` together with both inserted
roots gives an induced `K_q`; more generally any marker clique of size at least `q-2` closes.  In the
add/add orientation the inserted roots are nonadjacent, so

```text
K_(q-2) joined to two independent roots
```

is not regular.  Therefore the only root-unclosed extremal clique is the add/add `q-2` clique with a
two-vertex residual marker.  If a first-return/provenance row cuts that clique, one side has size
`1` or `q-3`; a complete transported side is sub-`q` and forbidden by the low-set congruence, while a
non-complete failure is local.  The live obstruction is precisely that an arbitrary ambient breaker of
the `q-2` clique need not route into such a fixed-fiber/provenance row.  This is the same
ambient-to-provenance routing gap again, now in its sharpest two-packet form.

The sharp two-packet survivor can be stated without quotient language.  Let

```text
A = K_(q-2),        U = R \ A,        |U|=2.
```

In a residual atom, no vertex of `U` is complete to `A`, because then `A` together with that vertex and
one inserted root is an induced `K_q`.  No vertex of `U` is mixed on `A`, because two adjacent vertices
of `A` together with that mixed vertex give the same-trace local `P_3` closure.  Hence `U` is
anticomplete to `A`, and the marker is

```text
K_(q-2) disjoint_union H,        H in {K_2, 2K_1}.
```

All compensation is outside the marker.  If an admissible first-return/provenance row cuts `A`, the cut
has a side of size at most `q-3`.  A complete side is a sub-`q` marker and is impossible by the low-set
congruence; an incomplete side is a local fixed-fiber exit.  Therefore every admissible row is constant
on `A` in a genuine residual atom.

Primeness can still give an ambient breaker of `A`, but that breaker must have error at least two
relative to the peeled package.  Error zero is a completer, and error one isolates a single low-clique
row, which is the one-defect split/local-exit case above.  Thus the last atom is exactly:

```text
A is a module for all admissible first-return rows,
but A is not an ambient module.
```

This is why all previous arithmetic, parity, wall-order, and quotient-selection arguments return to
Theorem G.  The missing theorem must turn an ambient breaker of this protected clique-module into an
admissible fixed-fiber/provenance breaker, a complete submarker, or a local exit.  No static statement
about `G[R]`, the residue sequence, or the packet weights can do that, because the obstruction is the
placement of the breaker relative to the first-return family, not the internal marker arithmetic.

The static split quotient around this endpoint is exhausted as follows.  Let `C` be a one-sided
compensator fiber complete to `U` and anticomplete to `A`, and set

```text
k(H) = (q-4)/2     if H=K_2,
k(H) = q/2 - 1     if H=2K_1.
```

The live ranges are `q>=8` for `H=K_2` and `q>=6` for `H=2K_1`; the smaller cases already contain
regular `q`-sets by the explicit one-compensator selections.

Suppose a regular selection meets `A`, `U`, and one compensator clique of selected size `gamma`.  Let
`alpha` be the number of selected vertices from `A`, and let `beta` be the number selected from `U`.
For `H=K_2`, equality of the degrees on `A` and the compensator clique gives

```text
alpha = beta + gamma.
```

The total-size equation gives `beta+gamma=q/2`; hence either `beta=2` and
`gamma=(q-4)/2`, or `beta=1` and `gamma=q/2-1`, which contains a `(q-4)/2`-clique.  For `H=2K_1`,
degree equality between `U` and the compensator clique forces `beta=1`, and then the total-size
equation gives `gamma=q/2-1`.  Thus every `U`-using selection contains a compensator clique of size
`k(H)`.

Several compensator components cannot give a new `U`-using selection.  If the selected component sizes
are `gamma_1,...,gamma_m`, equality with the degree on `A` makes all `gamma_i` equal to a common
`gamma`.  For `H=K_2`, equality with the degree on a selected row of `U` gives `(m-1)gamma=0`, so
`m=1`.  For `H=2K_1`, it gives `(m-1)gamma=beta-1`; the only non-single-component formal solution has
`beta=2`, `m=2`, `gamma=1`, and total size `7`, impossible for even `q`.  Therefore the only live
`U`-using obstruction is absence of a `k(H)`-clique in the one-sided compensator fiber.

Selections avoiding `U` are exactly the divisor bypass.  If the selection uses `h` vertices from `A`
and avoids `U`, then equality of selected degrees forces every used compensator component to contribute
the same number `h` of vertices.  Hence a `U`-free regular selection exists precisely when, for some
proper divisor `h` of `q`, there are at least `q/h-1` compensator components of size at least `h`; then
one takes `h` vertices from `A` and `h` from each of those components.  A residual atom must fail all
these divisor bypasses.

The marked quartet does not create another live selection in the add/add endpoint.  The old deleted
defects have selected degree at most one unless outside compensators are used, so for `q>=6` they cannot
replace the missing compensator clique while also using the large clique `A`.

Consequently, after fixed-fiber `P_3` closures inside the compensator fiber, the only finite
obstruction is:

```text
the compensator fiber is a union of cliques,
every clique has size < k(H),
and every divisor bypass fails.
```

This obstruction is still not a new arithmetic theorem.  Its total one-sided excess forces at least
three compensator components, and each component is again a module for the admissible first-return
rows unless a fixed-fiber breaker, a complete subpacket split, or a local exit has already occurred.
Ambient primeness can break such a component only by another high-error row outside the fixed package.
Thus the no-`k(H)` compensator case is the same ambient-only routing problem on a smaller protected
packet.

So the exact-marker atom has a packet-firewall normal form.  Starting with the add/add
`K_(q-2) disjoint_union H` marker, all marker-only selections, all `U`-free divisor bypasses, and all
`U`-using selections with a large enough compensator clique are closed.  If no such compensator clique
exists, the compensator fiber decomposes into smaller clique packets, each of which is constant to every
admissible first-return row in the residual frame.  A splitter through one of those packets is either
already a fixed-fiber Section-`40` breaker, a complete sub-`q` marker side, or another high-error ambient
breaker of a protected packet.  Thus the exact two-splitter endpoint is not a separate finite
selection problem: it is a recursive product-firewall packet.  The recursion can close only when an
ambient breaker is promoted to the admissible boundary family, or when a complete smaller marker/local
exit is produced.

Here is a concrete dependency witness for the last sentence.  Work with even `q>=8` and the adjacent
residual-pair model

```text
A=K_(q-2),       U=K_2,       C an independent set of size q-4,
```

where `C` is complete to `U` and anticomplete to `A`.  Add an ambient row `z` that splits `A` in at
least two places on each side and is anticomplete to `U union C`.  Declare the admissible
first-return rows to be the rows constant on `A`.  Then `A` is not an ambient module, but it is still a
module for all admissible rows.

This packet model still has no regular `q`-selection.  If a selected set avoids `z`, this is the
independent-compensator obstruction above.  If it contains `z`, then the selected vertices from `A`
must all lie on one side of the `z`-cut; otherwise two selected vertices of `A` have degrees differing
by one.  Let `x` be the number selected from that side, `y` the number selected from `U`, and `w` the
number selected from `C`.

If the selected `A`-side is adjacent to `z` and `w>0`, equality between `U` and `C` forces `w=1`, while
equality with `z` forces `x=y`; then total size gives `2y+2=q`, impossible because `y<=2` and `q>=8`.
If `w=0`, equality with `U` forces again `y=x+1` while total size gives `2x+2=q`, impossible for
`y<=2`.  If the selected `A`-side is nonadjacent to `z`, then `z` has selected degree zero; equality
forces at most one selected vertex from `A` and cannot reach total size `q`.  Thus even the ambient
breaker itself does not supply a static regular selection.  The missing input is exactly that the
breaker be promoted to an admissible fixed-fiber/provenance row or yield a local exit.

There is a tempting transport argument that would close the product-firewall form, but it is exactly
where the proof currently stops.  If an ambient breaker `z` of a protected packet were already an
ordered boundary row, Lemma 9.1 below would make the first packet-internal failure a whole side of
`P cap N(z)` or `P \ N(z)`, hence a complete sub-`q` marker.  The invalid shortcut is to assert this
whole-side conclusion for an arbitrary high-error ambient breaker merely because `z` is the first
nonconstant packet coordinate.  The low-set congruence applies only to the complete shared-slack set of
an actual transported square.  A chosen side, prefix, or first failed row of an untransported ambient
breaker need not be that complete shared-slack set.  In the sharp `q-2` clique atom the admissible rows
can remain constant on `A`, while the ambient breaker splits `A`; the dirty shared-slack set may then
reassemble an exact q-marker rather than a proper side of `A`.  Therefore the sub-`q` trap is valid only
after boundary-row promotion, and boundary-row promotion is Theorem G itself.

This gives an even more invariant formulation of the endpoint.  After all fixed-trace, clean-support,
marked-add, completer, and false-clone exits have been removed, let `cal A` be the rows that are already
admissible for the current first-return frame.  A set `M` inside a protected packet is an
**admissible module** if every row of `cal A` is constant on `M` and the vertices of `M` have the same
marked trace and the same residue over the frame.  The transport gap is precisely the failure of
admissible-module primeness:

```text
M is a nontrivial admissible module,
but some ambient row splits M.
```

If every such ambient split promoted to an admissible row, then the first admissible split of `M` would
be a square boundary, and Lemma 9.1 would force a complete smaller shared-slack side or a local exit.
Conversely, any fully skew positive-AND / q-marker endpoint supplies such an `M`: take the protected
packet on which all transported first-return rows are constant, while ambient primeness supplies a
nonconstant row.  Thus the remaining theorem can be stated without quotient arithmetic as:

```text
admissible-module primeness:
  in a shell-local first-return endpoint,
  every ambient splitter of an admissible module is either admissible after local marking,
  or its first failed row creates a strictly smaller admissible module.
```

The `q-2` clique atom is the smallest visible failure of this principle: `A=K_(q-2)` is a module for all
admissible rows, but an ambient high-error row can split it while still failing every interval test.
The exact-marker two-splitter atom is therefore not just a weighted zero-sum problem; it is the
admissible-module primeness problem in quotient form.

The admissible-module version has the same minimum-side normalization as the binary separator bag.  Let
`M` be a smallest admissible module split by some ambient row, and among all such rows choose a split side
`S` of minimum nonzero size.  If another ambient splitter crosses `S`, the two cuts give the primitive
`2x2` circuit; a realized diagonal/common package closes it, and absence of the diagonal is the already
isolated circuit-elimination endpoint.  If no ambient splitter crosses `S` but some splitter is
nonconstant inside `S`, one of its fibers is a smaller split side unless that fiber is already a local
complete carrier.  If no ambient row splits `S`, then `S` is an ambient module relative to the reduced
shell; primeness supplies either a local same-trace/false-clone distinguisher or contradicts
irreducibility.  Thus a minimal admissible-module primeness failure can be assumed to have a singleton
split side.

The singleton-side case is exactly the isolator normal form below.  The ambient splitter isolates one row
of a q-divisible sign-coherent carrier, but that singleton is not known to be a complete transported
shared-slack side.  If its first failed row leaves the singleton side, the crossing/smaller-side
dichotomy applies; if it returns to the same singleton, one obtains the high-error isolator self-loop.
Hence admissible-module primeness is not a broader endpoint than common-frame gluing: after crossing,
proper-side, and local module exits are removed, it is the same singleton chart-change problem.

The minimal failure has a two-splitter crossing normal form.  Let `M` be a smallest admissible module
split by an ambient row `z`, and expose the first row `r` on which the attempt to promote `z` to the
ordered first-return package fails.  If one side of the `z`-cut is preserved by every active failed row,
that side is a smaller admissible module and minimality closes.  If one side of the `r`-cut is preserved
by `z` and by the active first-return rows, the same smaller-module descent applies after marking `r`.
Thus a minimal nonpromotable splitter must have the crossing property: `z` splits both `r`-sides, and
`r` splits both `z`-sides, while no quadrant is itself first-return-complete.  All fixed-trace or clean
quadrants have already exited locally, so the crossing quotient is exactly the two-splitter / zero-sum
packet atom.  In the binary square language, this says that admissible-module primeness can fail only
when the first ambient split and the first failed ordered row form the same fully skew `0001` support
carrier.  Hence the support-decrease theorem has no separate large-module branch after minimality: the
last survivor is a two-splitter crossing with no complete quadrant.

The crossing can be written as a primitive `2x2` residue circuit.  Let

```text
M_ab = M cap {z=a} cap {r=b},        a,b in {0,1},
```

and let `m_ab=|M_ab| mod q`, where empty quadrants and local fixed-trace quadrants have already been
removed.  The complete dirty carrier has

```text
m_00+m_10+m_01+m_11 = 0 mod q.
```

Minimality forbids every proper first-return-complete zero-sum subunion.  Thus no quadrant has residue
`0`, no `z`-side or `r`-side has residue `0`, and no opposite diagonal is a complete zero-sum carrier
unless the complementary diagonal is packaged in the same peeled space.  If any of these zero residues
were realized by a transported first-return side, the low-set update would give the smaller marker
required by support decrease.  The irreducible quotient is therefore a primitive four-term circuit:
all row, column, and realized diagonal sums are nonzero modulo `q`, while the total sum is zero.

This residue circuit explains why neither splitter alone can orient the support.  The ambient splitter
sees only the row sums `m_00+m_01` and `m_10+m_11`; the first failed ordered row sees only the column
sums `m_00+m_10` and `m_01+m_11`.  Both views are nonzero, so each individual cut is a non-complete
prefix, while their union is the complete q-marker.  A proof must therefore supply an ordered diagonal
or a common peeled package in which one diagonal becomes an actual first-return-complete side.  Without
that extra provenance, the primitive circuit is a faithful quotient model of the positive-AND square:
the missing `11` corner is exactly the diagonal support not seen by either one-coordinate cut.

The circuit is not arithmetically impossible, even in the dyadic cases.  For every dyadic `q>=4`, the
residue table

```text
m_00=1,        m_10=1,        m_01=1,        m_11=q-3
```

has total residue `0 mod q`, while every quadrant, row, column, and diagonal residue is nonzero.  Thus
the primitive `2x2` circuit cannot be excluded by modular arithmetic, parity, or a determinant
valuation.  The theorem must prove that one of these formal residues is actually realized as a
first-return-complete carrier, or that the attempted realization creates a local exit.  This is the same
history-sensitive provenance demand as before, now in the smallest possible residue quotient.

For dyadic `q>=8`, the same table can also be made clique-coherent at the static quotient level: take
the four quadrants to be disjoint cliques of sizes `1,1,1,q-3`, with the two splitters constant on each
quadrant and crossing as above.  Then there is no induced `P_3` inside the marker quotient and no
splitter cuts through an internal clique.  This is not a counterexample to the graph theorem, because it
asserts neither first-return admissibility nor absence of inserted-root/local exits.  It only shows that
the already closed same-trace, roof/twin, and clique-coherence reductions do not see the primitive
circuit; the remaining obstruction is genuinely the provenance of a row, column, or diagonal carrier.
The base dyadic case `q=4` is exceptional for this particular static model: the disjoint-clique version
is already regular, so any live `q=4` primitive circuit would need additional cross-quadrant structure
and is handled by the small exact-marker catalogues rather than by the large clique-coherent atom.

There is a formal dyadic descent, but it is not a closure.  Let `q=2^j` and let

```text
s_P = m_A+m_B
```

be the residue of any two-block pairing of the four quadrants; the complementary two-block residue is
`-s_P`.  Choose a pairing for which `nu_2(s_P)` is maximal among the nonzero pair residues.  Then
`s_P=2^ell u` with `0<=ell<j` and `u` odd, so after dividing by `2^ell` the circuit has a primitive
two-block shadow at modulus `2^(j-ell)`.  This is exactly the dyadic carry shadow of the crossing: one
side carries `u`, the complementary side carries `-u`.

The descent closes only if that pairing is a realized first-return-complete carrier, or if both paired
blocks are already in one peeled package.  In that case the lower-modulus shadow is a genuine smaller
q-marker/carry and the induction or raw short-packet relation applies.  In the survivor, however, the
maximal-valuation pairing is only a formal grouping of quadrants.  The example
`(1,1,1,q-3)` has even row, column, and diagonal sums, so it has a visible `q/2`-level shadow, but no
row, column, or diagonal is forced to be a transported carrier.  Thus dyadic valuation reduces the
primitive circuit to a lower carry only after the same provenance/common-package input has already been
supplied.

There is also a three-pairing triality.  The four quadrants have exactly three two-block pairings:

```text
rows, columns, diagonals.
```

Rows are the ambient splitter view, columns are the first failed ordered-row view, and diagonals are the
hidden positive-AND view.  If any two of these pairings are realized in one peeled package, then their
symmetric difference realizes the third pairing in the same package.  For instance, common packaging of
rows and columns identifies the diagonal carrier, and the diagonal criterion below closes.  Therefore an
irreducible primitive circuit must keep all three pairings in mutually incompatible package coordinates:
each pairing is visible as a formal residue split, but no pair of pairings can be compared in one raw
space.  This is exactly package-coordinate monodromy in its smallest finite form.  A shortest failure of
two pairings to share a package is again a single binary pair-status change, hence the successor-side
`0001` square.

Equivalently, a Boolean-cube closure would prove the missing diagonal.  If the shell/repaired-fiber
geometry contained, for the two splitters `z` and `r`, a realized boundary row whose incidence on `M`
was the symmetric difference of their two cuts, that row would be the diagonal carrier and the previous
paragraph would close the primitive circuit.  The current local theorems do not supply such an XOR row:
repair fibers are only conditionally cubical, and their non-cubical first edge is precisely the
square-transverse breaker already isolated.  Thus "take the XOR of the two splitters" is another
formulation of the same missing cubicality/provenance theorem, not a new operation available in the
graph.

This is not merely a technical absence.  Vertex neighborhoods over `M` are not closed under symmetric
difference.  If a vertex `t` realizes `N_M(t)=N_M(z) triangle N_M(r)`, then the three rows
`z,r,t` form the Boolean diagonal and the primitive circuit closes as above.  If no such `t` exists, the
attempted Boolean cube has only three of the four row types.  A shortest path in the repair fiber from
`z` toward `r` then has a first edge on which the expected XOR row is absent; fixed-trace absence is a
false-clone/shifted-twin local exit, while non-fixed-trace absence is exactly the square-transverse
breaker.  Thus neighborhood-algebra closure, cubicality, and diagonal provenance are the same missing
statement in three languages.

This can be phrased as a circuit-elimination axiom for realized first-return boundary rows.  Let
`B(M)` be the set of row traces on the primitive carrier `M` that are actually realized by admissible
boundary rows after the fixed-trace and clean exits have been removed.  If `B(M)` had the following
binary elimination property,

```text
z,r in B(M) cross both sides
  =>  z triangle r in B(M), or a row/column/diagonal side is a realized complete carrier,
```

then the primitive circuit would close: the second alternative is support decrease, and the first
alternative is the Boolean diagonal.  Conversely, failure of this elimination property is exactly an
XOR-hole.  Taking the first repair-fiber edge at which elimination fails gives the same dichotomy as
above: fixed-trace failure is local, and non-fixed-trace failure is square-transverse.  Thus the final
provenance theorem is equivalently a binary circuit-elimination theorem for admissible boundary-row
traces on the primitive `2x2` carrier.

The two directions of this equivalence are useful.  Circuit elimination implies Theorem G on the
primitive carrier because it either realizes a complete row/column/diagonal side, to which the low-set
congruence applies, or it produces the XOR diagonal and hence common packaging of two pairings.  Failure
of Theorem G, after the reductions above, supplies two crossing realized traces `z,r` with no complete
proper carrier; if binary elimination held, that failure would close, so elimination must fail.  The
minimal failure of elimination is precisely the same `0001` square: three corners of the Boolean row
cube are realized or forced by the two splitters, while the diagonal corner is absent.  Therefore no
additional algebraic closure remains hidden between Theorem G and the XOR-hole normal form.

Nor is binary elimination a formal consequence of the reduced trace axioms.  Take a primitive residue
table on four quadrants, let `B(M)` contain only the two row/column splitters, and impose side-constancy
on each quadrant.  Then the two realized traces cross both sides, every row/column/quadrant residue is
nonzero, no proper complete carrier is named, and there is no fixed-trace or clean local exit in the
quotient.  The system violates only the desired elimination step: the diagonal trace is absent.  Thus any
proof must use the actual graph-specific repair-fiber adjacency or first-return history to manufacture
the diagonal/proper carrier; it cannot be derived from the abstract primitive carrier axioms alone.

The diagonal criterion is the sharp support-decrease target in this language.  If either diagonal

```text
D_0=M_00 union M_11,        D_1=M_10 union M_01
```

is a realized first-return-complete carrier, then one of two things happens.  If its residue is `0 mod q`,
the low-set update gives a proper complete marker unless the other diagonal is empty, which has already
been removed.  If its residue is nonzero, then the complementary diagonal has the opposite residue and
the two diagonal discrepancies must be added in one peeled package; the raw short-packet relation then
forces either a completer/local exit or a packet refinement.  Thus a primitive crossing can survive only
when neither diagonal is realized as a first-return-complete carrier and the two diagonal discrepancies
remain in different package coordinates.  This is the exact diagonal form of common-shadow failure.

There is an equivalent packet-primality packaging form.  In the sharp add/add endpoint the quotient has
three visible factors:

```text
A = large clique packet,     U = residual two-row packet,     C = one-sided compensator packets,
```

with quotient adjacency only between `U` and `C`; the ambient breaker cuts `A`, while the provenance
splitter cuts `U`.  If these cuts lived in one first-return package, then the packet quotient would be
refined by an admissible row: a cut of `A` or of a compensator component gives a proper sub-`q`
marker-complete side, and opposite cuts of `U` give a sub-`q` raw zero relation.  Both are already local
exits.  If they do not live in one package, the quotient remains split/disconnected even though the
ambient shell is prime.  Hence the last packaging theorem can be phrased as:

```text
first-return packet-primality:
  a packet quotient produced by a genuine q-marker atom is either prime in the first-return package,
  or any ambient breaker of a quotient module is transported to a packet-refining admissible row
  or to a local exit.
```

This is the same statement as admissible-module primeness, but it isolates why the exact two-splitter
atom survives all static selections: the two necessary cuts can sit in different package coordinates.
The positive-AND/common-shadow formulation is exactly the assertion that such separated package
coordinates must have a common first-return lift.

There is one formal fact inside the failed transport attempt.  Even before an ambient splitter `r` has
passed the boundary tests, packet homogeneity makes every packet-internal test side-constant.  If `P`
is a clique-coherent protected packet, then all vertices of `P` have identical trace to the marked
frame, to every admissible packet, and to every row already in the first-return package.  In the
attempted boundary calculation with row `r`, the only term depending on `p in P` is `1_{p~r}`.  Hence
the test value is constant on `P cap N(r)` and constant on `P\N(r)`.  A first packet-internal interval
failure is therefore a whole `r`-side of `P` (or all of `P` if both sides fail), not a scattered subset.

This by itself still does not prove transport.  The low-set congruence can be applied only after that whole side
is known to be the complete shared-slack set of an actual transported marked square.  Side homogeneity
is formal; side provenance is the missing content.  The fully skew carrier can keep the same `r`-side
visible while the true dirty shared-slack marker reassembles with rows from other active packets to
size exactly `q`.  Thus the packet side lemma removes the "scattered failure" worry but not the
admissible-module primeness gap.

Consequently the residual side-provenance blocker has a very rigid simultaneous-packet form.  Let
`W` be the first failed piece of the protected packet `P`: either one split side `S`, or all of `P` if
both split sides fail.  If the transported dirty square has complete shared-slack set `F` contained in
`W`, then `0<|F|<=|W|<q` for the product-firewall packets, contradicting `|F|=0 mod q`.  Hence every
surviving failure has

```text
F = W union Q_1 union ... union Q_t,
```

where each `Q_i` is a whole side-constant packet (or packet side) that fails at the same first wall.
No proper subunion of these simultaneous packet pieces can be first-return-complete with size
`0 mod q`, or it would be the smaller marker required by support decrease; in particular, if `F` is a
proper subset of the current marker, minimality closes it.  Hence a larger-marker survivor must have
this simultaneous first wall reassemble the whole current marker, while an exact-marker survivor has
`F=R` automatically.  If one `Q_i` is frozen under the remaining outside trace, the frozen large-marker
cluster argument above gives a regular `q`-set or a local same-trace exit.  Thus the only
side-provenance survivor is a non-frozen simultaneous-packet zero-sum atom containing the protected
failed piece `W` as one summand.  This is the large-marker no-q-jump obstruction in its
boundary-transport form.

This separates the valid product-firewall containment argument from the unresolved simultaneous-wall
case.  If square-breaker routing produces a dirty budget-one square whose complete shared-slack set
`F` is contained in the first breaker side `W` of a proper protected packet, then `0<|F|<q`; the
low-set update gives `|F|=0 mod q`, a contradiction.  The same holds if `F` is contained in one
compensator component of size `<q` or in any proper side made first-return-complete by the boundary row.
Thus the containment version of first-boundary completeness is a proof.

The only way containment can fail is simultaneous reassembly: rows outside `W` must fail at the same
first wall and join `W` to form the complete marker.  In a minimal survivor the family

```text
W, Q_1, ..., Q_t
```

is a first-wall antichain: no member is frozen, no proper subfamily is first-return-complete with
residue `0`, and no secondary first-return priority separates an initial subfamily that is itself a
complete carrier.  If such a priority existed, the earliest complete initial carrier would either be
sub-`q` or a proper q-divisible marker, and the previous congruence/minimality argument would close it.
Therefore the exact missing assertion is not the containment argument itself; it is the exclusion of
these simultaneous-wall antichains, equivalently the proof that first-return history supplies a complete
proper carrier before the whole q-marker reassembles.

Pure ordering of the antichain is still insufficient.  The packet residues may be

```text
1, 1, 1, q-3,
```

whose total is `0 mod q` while no proper subfamily has residue `0 mod q` (for `q=4`, read this as four
unit residues).  Thus even a canonical order on the simultaneous packet pieces does not by itself give
a smaller marker; the order must be tied to square provenance, so that a row, column, diagonal, or
initial segment is an actual complete shared-slack carrier rather than just a formal packet sum.

There is one arithmetic normalization of the antichain.  Let the simultaneous packet pieces have
residues

```text
a_0, a_1, ..., a_t in Z/qZ,
```

with `a_0` the protected failed piece and `sum_i a_i=0`.  If a nontrivial divisor `d` of `q` divides
every `a_i`, then after dividing by `d` the same formal antichain is a zero-sum antichain at modulus
`q/d`.  This is a genuine descent only if the packet pieces are realized as first-return-complete
carriers at that lower modulus; otherwise it is just a formal residue shadow, exactly like the dyadic
pairing descent above.  Hence an irreducible simultaneous-wall antichain may be assumed **primitive**:

```text
gcd(q,a_0,a_1,...,a_t)=1.
```

For dyadic `q`, this means at least one packet piece has odd residue; since the total residue is zero,
there are in fact at least two odd pieces.  If first-return history isolated any proper odd-parity
subfamily whose residue becomes zero at a lower modulus, that subfamily would be the required smaller
carrier.  In the survivor, all such odd pieces remain tied in the same simultaneous wall.  Thus the
large-marker no-q-jump endpoint is the primitive zero-sum antichain with no realized proper subcarrier,
not an arbitrary q-divisible block.

The usual cyclic zero-sum bound gives only a formal size cap.  Since the nonzero residues
`a_i` form a minimal zero-sum sequence in `Z/qZ`, the sequence has length at most `q`: otherwise the
standard partial-sum argument gives a nonempty proper zero-sum subsequence.  If every subfamily of
simultaneous packet pieces were automatically a first-return-complete carrier, this would already yield
a smaller marker whenever the antichain were not the whole minimal sequence.  But first-return
completeness is exactly the missing property.  A formal zero-sum subsequence of packet residues need not
be the whole shared-slack set of any transported square; it may omit other packets tied to the same
first wall.  Thus Davenport-style zero-sum extraction bounds the combinatorics of the survivor but does
not supply the provenance needed for support decrease.

The extremal case of this zero-sum bound is also useful.  If the primitive antichain has exactly `q`
packet pieces and no proper formal zero-sum subfamily, the standard extremal case for atoms in the
cyclic group `Z/qZ` says that, after multiplying all residues by one unit, the residue sequence is

```text
1, 1, ..., 1       (q terms).
```

Thus a maximal simultaneous-wall survivor has no remaining residue heterogeneity: every nonempty proper
subfamily has nonzero residue simply because its size is not a multiple of `q`.  Any closing argument in
this extremal case must therefore come from first-return provenance, common-package realization, or a
local fixed-trace/completer exit; arithmetic cannot choose a smaller subcarrier.  In the nonmaximal
case, there may be many formal zero-sum or lower-divisibility subfamilies, but each still needs the same
first-return completeness certificate before minimality can apply.

For dyadic `q` there is a sharper parity-layer view.  Let `O` be the subfamily of packet pieces with
odd residue.  The total residue is `0`, so `|O|` is even.  Pairing two odd pieces gives an even-residue
subfamily and therefore a formal carrier at modulus `q/2` after division by two.  If some odd pair is
realized as a first-return-complete lower-modulus carrier, the lower dyadic induction or the raw
short-packet package applies to that carrier; lifting back gives either a proper q-marker side, a local
exit, or a circuit-elimination row.  Hence a dyadic survivor has no realized odd pair.  Equivalently,
the graph on odd packet pieces whose edges are realized first-return-complete lower carriers is empty.

This is the parity form of the same obstruction.  The odd pieces exist arithmetically, and formal pairing
is unavoidable, but the proof needs a realized pairing edge.  If first-return history supplies such an
edge, the no-q-jump layer descends; if it supplies none, the odd pieces form the lowest 2-adic
simultaneous-wall antichain.  The absent realized odd-pair edge is the large-marker analogue of the
absent XOR diagonal in the primitive `2x2` circuit.

More generally, every realized first-return cut of the odd layer is parity-skew in a survivor.  If a
realized complete carrier cuts `O` into two nonempty even parts, then either part has even residue and
therefore gives a proper lower-modulus carrier after division by two.  Thus such an even/even cut would
descend.  Consequently any nonlocal realized cut of the odd layer must be odd/odd.  Two crossing
odd/odd cuts on `O` produce the same `2x2` parity circuit: their row and column pairings are realized,
and a realized diagonal would close by the odd-pair descent.  If the diagonal is absent, the obstruction
is again binary circuit elimination.  Thus the parity-layer survivor is not a new case; it is the
primitive circuit-elimination endpoint restricted to the odd packet pieces.

If no two realized odd-layer cuts cross, the realized cuts are laminar after choosing the side containing
a fixed odd packet piece.  A nontrivial laminar chain has nested odd sets

```text
O_1 subset O_2 subset ... subset O_m subset O,
```

and every interval `O_{i+1}\O_i` has even residue.  If such an interval were a realized
first-return-complete carrier, the lower-modulus descent would close it.  Hence a laminar survivor has
no realized even interval; it is a chain of odd cuts whose formal even differences are never actual
shared-slack carriers.  This is again a provenance failure, not a parity obstruction.  An ambient
breaker of a minimal laminar block either promotes to a first-return cut, producing a crossing cut or a
realized even interval, or it remains outside the first-return family, which is precisely the original
ambient-to-boundary transport gap.

The laminar branch therefore has its own common-package test.  If two consecutive nested odd cuts
`O_i subset O_{i+1}` live in one peeled package, then their difference `O_{i+1}\O_i` is a realized even
interval in that same package.  The lower-modulus descent closes it.  Hence in a laminar survivor every
consecutive nested pair must change peeled package.  Taking the first such package change along the
chain gives a shortest common-package failure between two realized first-return cuts; after the fixed
unary and predecessor data are factored off, this first failure is again a binary pair-status change,
namely the successor-side `0001` square.  Thus the laminar odd-layer branch is not a separate endpoint:
it either realizes an even interval or reduces to the same common-package / positive-AND obstruction.

The simultaneous-wall endpoint can therefore be stated as a standalone realization theorem:

```text
primitive antichain realization:
  a primitive first-wall zero-sum antichain of side-constant packet pieces
  either has a proper first-return-complete zero-sum subcarrier,
  or admits a binary circuit-elimination row,
  or gives a local fixed-trace / marked-add / completer exit.
```

In dyadic form this splits into two explicit subgoals on the odd layer:

```text
crossing odd cuts       -> binary circuit elimination / diagonal carrier,
laminar odd cuts        -> realized even interval carrier.
```

These are the same theorem in two combinatorial shapes.  The crossing case is the primitive `2x2`
carrier; the laminar case asks that a formal even difference between nested odd cuts be an actual
first-return-complete lower-modulus carrier.  If neither subgoal holds, the odd layer has neither a
realized odd pair, nor crossing elimination, nor laminar interval descent, so all first-return data are
compatible with the formal antichain but no support decrease occurs.

This theorem is equivalent to Theorem G after the reductions above.  The forward implication is the
support-decrease argument: a realized zero-sum subcarrier is a smaller q-marker, and a circuit-elimination
row realizes the missing diagonal/common package.  Conversely, any fully skew q-marker counterexample
with containment, frozen, exact one-splitter, local, and clean exits removed produces exactly such a
primitive first-wall antichain.  Thus the final problem is no longer a large-marker arithmetic question;
it is the realization of a formal primitive zero-sum antichain by actual first-return carriers.

Equivalently, in the one-side case the exact side-replacement atom is:

```text
P = S disjoint_union S',
F = S union Q_1 union ... union Q_t,
```

where `S'` is the other side of the ambient split and the simultaneous packets `Q_i` replace `S'` in
the complete dirty marker.  If `sum_i |Q_i| != |S'| mod q`, the low-set congruence gives a proper
support decrease.  If some proper subunion of the `Q_i` has the required residue, it is a smaller
first-return-complete marker.  Hence the residual atom is not "the protected side failed"; that case
closes.  It is the sharper side-replacement problem: the first-return square must be able to exchange
the missing side `S'` for a zero-sum packet family outside the ambient splitter's packet, with no proper
complete exchangeable subfamily and no frozen packet.  This is precisely where the sub-`q`
product-firewall trap would become a proof if one could exclude all replacement packets.

Minimizing the side-replacement atom gives one last normalization.  Choose the ambient splitter and
protected packet so that the total replacement support `Q_1 union ... union Q_t` is minimal.  If the same
ambient splitter is nonconstant on some replacement packet, the side-constant lemma applied to that
packet gives a new side-replacement atom with strictly smaller replacement support, unless the split
side is already a proper complete marker or a local exit.  Thus in the irreducible side-replacement
atom, the ambient splitter of `P` is constant on every replacement packet.  The replacement packets are
therefore activated only by the other first-return coordinate.  This is exactly the two-coordinate
positive-AND shape: one coordinate sees the protected side `S`, the other sees the replacement family
`Q`, and no common package has yet made `S` and `Q` a proper complete marker.

Iterating packet primeness gives a replacement-cycle normal form.  Since each replacement packet is
non-frozen, either it is a genuine module of the ambient shell, or some ambient row splits it.  A genuine
ambient module contradicts the prime shell.  If the splitter of a replacement packet gives a local exit,
a frozen packet, or a proper complete exchangeable subfamily, the atom closes.  Otherwise it produces
another side-replacement atom.  In a minimal survivor this replacement cannot have strictly smaller
total replacement support, so the directed relation

```text
packet side  ->  replacement packet family
```

must contain a directed cycle.  A length-one cycle would mean that one packet side replaces its own
complement, which is exactly the frozen/side-contained case already closed.  Thus the irreducible
common-package failure is a directed replacement cycle of length at least two.  Around such a cycle the
ordinary packet sizes give zero total residue modulo `q`, but no proper consecutive arc is
first-return-complete and no packet is frozen.  This explains why endpoint mass and static zero-sum
arguments still do not close the theorem: they see only the cyclic residue cancellation, not a
distinguished first-return arc to which the low-set update applies.

The first nontrivial case of this cycle is the balanced two-cycle.  If a side `S_1` of `P_1` is replaced
by a side `S_2` of `P_2`, and conversely `S_2` is replaced by `S_1`, then the residue equations say that
the two opposite arcs have equal and opposite discrepancy.  In one peeled package this is the
`0101/0011` balanced flip table: the two raw rows add to a zero relation of total mass below `q`, so the
short-packet theorem gives a completer, proper marker, or coalescence.  Hence a surviving two-cycle is
possible only if the two arcs are not in one raw space.  Its first failed common-space edge is again the
successor-side `0001` monodromy edge.  Longer replacement cycles reduce to the same form by taking a
shortest nontrivial packaged subcycle; any chord or proper zero-residue arc would be the forbidden
smaller complete marker.

The obvious ordered-cycle shortcut is also conditional.  If all edges of the replacement cycle lived in
one peeled first-return package, the earliest edge of the cycle would distinguish a proper consecutive
arc; the raw discrepancy of the opposite arc would then be in the same coordinate space, and the
short-packet / weighted-quotient catalogue would force a completer, a proper marker, or a local
coalescence.  In the survivor the cycle edges are packaged in different peeled spaces.  Thus "take the
earliest edge of the cycle" is not a valid invariant until the fixed peeled-package/common-shadow theorem
has identified those spaces.  The replacement-cycle atom is therefore exactly the cyclic form of the
same common-package failure, not a new route around it.

The row-to-boundary transport problem has an even smaller normal form.  Let `r` be a minimal ambient
breaker of the protected packet coordinate `j`, chosen after all fixed-trace and clean marked-support
local exits have been removed.  Try to use `r` as the missing boundary row for the coordinate-`j`
first-return square.

If every one-coordinate interval test passes, then `r` is an admissible ordered boundary row, and the
homogeneity argument of Lemma 9.1 closes the packet split.  If some interval test fails, let `u` be the
first failed row.  If `u` has fixed trace relative to the current square frame, marking `u` puts `r`
and the old boundary row in the same-trace or false-clone catalogue, so the local exit applies.  If the
marked support is clean, the marked-add catalogue applies.  Hence every residual failure is dirty and
transverse at the same coordinate `j`.

Thus the remaining transport theorem is exactly:

```text
minimal transverse breaker admissibility:
  a minimal transverse breaker with no fixed-trace or clean exit
  either passes all interval tests,
  or its first dirty failed row is a transverse breaker with strictly smaller unfrozen support.
```

The strict support decrease is the missing content.  It is not a formal consequence of being the first
failed row.  In the fully skew carrier table, rows can be indexed by sign vectors on active binary
blocks; replacing the ambient breaker by the first failed row merely moves to another fully skew row
with the same active support.  The low-set update then marks the whole shared-slack set and gives only
`|R|=0 mod q`.  At exact size this is silent, and at larger size it is the no-q-jump problem already
recorded.  Therefore transverse-breaker admissibility is not a new independent route around Theorem G;
it is the row-to-boundary form of the same q-marker support-decrease theorem.

This support-decrease theorem has three ordered clauses, and only the first remains genuinely opaque.

1. **Selection.** A splitter of the protected marker must be chosen from the ordered first-return /
   transverse-breaker family, not merely from arbitrary ambient prime-shell rows.
2. **Local non-marker exit.** Once such an ordered row is chosen, failures at old defects, inserted-root
   tests, or filler rows are local: they are exactly the same-trace, marked-add, wrong-root-edge, or
   completer exits already removed.
3. **Square-provenance descent.** If the ordered first failure is marker-internal and the boundary row
   comes with the whole first-return singleton square, then the complete wall-failure set `F` is exactly
   the shared-slack set of a new marked two-class quartet.  Thus `|F|=0 mod q`; if `F` is a proper side
   of the old marker, minimality closes it.

So the live theorem is not "handle any failed row."  It is the narrower ambient-to-square-provenance
statement: a high-error ambient or transverse breaker must either reseat as an ordered square boundary,
or trigger one of the local exits before it can remain fully skew on the same q-marker support.

The selection clause itself has two layers.  First one must reach an exact marker.  The low-set update
only gives `|R|=0 mod q`; for a larger marker, arbitrary prefixes of a simultaneous wall block are not
known to be complete shared-slack sets, so congruence cannot be applied to them.  The large-marker
subproblem is therefore a no-q-jump theorem: a simultaneous wall block must contain a regular `q`-set,
a local exit, or a proper first-return-complete zero-sum submarker.

Once `|R|=q`, the exact marker has a state-internal splitter unless `G[R]` is already regular.  The
state-internal splitter is normalized as low-universal or high-null.  Low-universal with no second
splitter gives a regular `(q+1)`-set; high-null with no second splitter gives the one-excess form and
then a same-trace local `P_3`; and a second splitter constant on `R` is the singleton-lift false-clone
gate.  Thus exact-marker selection is reduced further to the marker-splitting two-splitter atom: two
independent cuts of `R` must be routed into one square-provenance frame or to a local exit.  Static
zero-sum packet arithmetic still does not close this atom, because the packets may compensate residues
without supplying a first-return-complete zero-sum union.

Nor can one replace transverse-breaker provenance by an unqualified theorem saying that every fully
skew splitter is admissible.  In the static residue model above, a sign-vector row sees exactly one
endpoint of each active pair, misses both old defects, and sees no high filler.  Relative to the low set
`R union {d,e}` its error is `q/2+2`, so it is neither a completer nor a one-defect reanchor.  Such a
row can split the marker while remaining outside every admissible repair family.  Thus admissibility
can only be forced for rows that come with first-failed-row or transverse-breaker history.

The same point blocks the seed-packaging shortcut.  A single row of the marker together with
`d,e,x,y` gives the expected house, path, or cycle seed, but the complete marker is a bag of size `q`.
The local weighted-quotient catalogues apply only after the bag has been refined into proper
sub-`q` packets or after a fixed-fiber breaker has been found.  Splitting the bag into such seed packets
is exactly the forbidden submarker problem.  Hence the five-vertex seed does not close the q-marker
family without the missing first-return/admissibility coupling.

The unweighted host form of the same obstruction is a dirty binary trace-coalescence problem.  After
minimal trace saturation, a connected crossing carrier collapses to one active pair `{x,y}` and dirty
failed rows that all separate it.  If two successive dirty rows coalesce into one residual fixed fiber
after the allowed marking, the local false-clone / shifted-twin catalogue closes.  The only remaining
case is a skew binary ladder: successive failed rows keep separating `{x,y}`, but no allowed marking
makes them a same-residual-trace pair.

This binary ladder is equivalent to the common-shadow and two-fiber overlap formulations already
recorded.  In one language, two off-root transports must share a fixed frame over the same visible
corner; in another, the reduced overlap table is `{0101,0011}` with no `0111` row.  If the two flipped
rows are packaged in one raw discrepancy space, their discrepancies are opposite,

```text
e_x-e_y,        e_y-e_x,
```

and form a zero raw packet of total mass `2<q`, so the raw short-packet theorem closes them.  Therefore
the live binary ladder is precisely failure of common discrepancy packaging.  Endpoint chamber labels,
silent-component data, and dyadic mod-`2` cocycles are all invariant under reversing the elementary
hidden step, so they cannot supply the ordered sign needed to force coalescence.  The missing input is
again a history-sensitive common-frame theorem, not another parity or endpoint invariant.

The ladder itself has a final turn dichotomy.  For two consecutive dirty rows `r,s`, write
`eps(r)=+1` when `r` sees `x` and misses `y`, and `eps(r)=-1` in the opposite case.

If `eps(s)=-eps(r)`, the local induced-path test forces the edge `rs` to match the active edge `xy`.
Indeed, if `xy=0` and `rs=1`, then `x-r-s-y` is an induced path on four vertices; if `xy=1` and
`rs=0`, then `r-x-y-s` is one.  These local paths are already in the closed catalogue.  Hence every
irreducible opposite-side turn has `rs=xy`, and the four vertices `{x,y,r,s}` form exactly the balanced
flip quartet: `2K_2` when `xy=0`, or `C_4` when `xy=1`.  This is the same two-row non-overlap table
`{0101,0011}`.

If `eps(s)=eps(r)`, then `r` and `s` are twins over the active pair.  A finite cycle made only of such
same-side turns is invisible to the endpoint chamber data; if no outside row distinguishes the cycle,
it is a prime-shell module.  Primeness gives an outside boundary distinguisher, but the first boundary
of that distinguisher must be routed without losing the active pair.  If it coalesces, the local
same-trace catalogue closes; if it does not, the closest-return reduction again leaves the
successor-side `0001` square.

Thus every irreducible ladder edge is already a common-package failure.  For an opposite-side turn,
placing the two rows in one raw discrepancy package gives the zero packet
`(e_x-e_y)+(e_y-e_x)`, so the short-packet catalogue closes the turn.  For a same-side turn, placing the
two rows in one residual fixed frame makes them a same-trace or shifted-twin pair, so the local catalogue
closes the turn.  Hence a surviving skew ladder must change peeled package at each adjacent dirty turn.
The first adjacent turn whose package change cannot be absorbed is exactly the first moved binary
pair-status coordinate, i.e. the same successor-side `0001` square as in the monodromy and laminar
odd-chain normal forms.

Thus the deepest binary host loop is:

```text
opposite-side turn  -> balanced flip / two-fiber non-overlap,
same-side cycle     -> boundary distinguisher -> successor-side 0001,
0001                -> dirty shared-slack q-marker.
```

No branch of this loop is closed by endpoint data alone.  The balanced flip closes only after common
raw-discrepancy packaging; the same-side branch closes only after active-packet-preserving boundary
routing; and the `0001` branch closes only after marker-complete support decrease.

The final adjacent turn can be put in one signed-edge normal form.  A dirty row is recorded by its sign
`eps in {+,-}` on the active pair and by the peeled package in which its raw discrepancy is measured.
Two adjacent dirty rows close unless their edge changes package:

```text
opposite signs + same package   -> raw zero packet;
same sign + same fixed frame    -> same-trace / shifted-twin exit.
```

Thus the surviving edge is not a sign event but a **chart-change event**.  If the sign changes across the
chart change, the edge is the balanced `{0101,0011}` flip; if the sign is preserved, it is the
same-sign singleton-isolator edge.  Passing to the signed double cover of the package graph does not
create a new invariant: a closed walk in the cover with trivial chart monodromy telescopes in one raw
space, while the first edge with nontrivial chart monodromy is, after possibly switching the active-pair
orientation, the same successor-side `0001` row.  Therefore the last edge-level theorem can be stated as:

```text
every irreducible dirty chart-change edge is promoted to a first-return complete side,
or it is the first edge of a smaller dirty chart-change square.
```

This is exactly single-turn common-frame gluing.  A sign potential on the double cover would orient only
the already closed raw-zero or same-trace edges; it cannot decide whether the chart-change side is a
complete shared-slack carrier.

Attach to a dirty chart-change edge its **carrier** `C(e)`: the set of retained rows whose raw
discrepancy coordinate cannot be identified on the two sides of the edge after all fixed, clean, unary,
and local kernels have been quotiented out.  If a proper nonempty subset of `C(e)` is already
first-return-complete, the low-set update gives support decrease.  If two chart-change edges split
`C(e)` in crossing ways, their four intersections are the primitive `2x2` circuit and the realized
diagonal/common-package alternative closes it.  Therefore a minimal unresolved chart-change carrier is
laminar for all admissible edges and has no proper complete subcarrier.

In that laminar minimal case, every admissible row is constant on `C(e)`; otherwise its first nonconstant
fiber is a smaller chart-change carrier.  Thus `C(e)` is an admissible module.  Ambient primeness gives a
row splitting it, but if that splitter is promoted to the first-return package then one of its sides is the
desired complete carrier, and if it is not promoted we have exactly admissible-module primeness failure.
So the chart-change carrier language does not create a new endpoint: after the crossing and proper-side
cases are removed, it is identical to binary separator-bag promotion.

This also rules out a broad class of potential arguments.  Any potential depending only on the active
support size, the unordered endpoint chambers, the first changed wall label, or the sign multiset of
the fully skew rows is constant on a same-support skew ladder.  One may cycle through fully skew rows
with the same support and alternating sign-vector labels while every local two-row turn is either a
balanced flip or a same-side twin turn; the local catalogue removes only turns that coalesce or create a
fixed-frame distinguisher.  Therefore a successful potential must use extra square-provenance data: it
must know that one row of the ladder is the complete wall of a transported first-return square, not just
another separator of the same active pair.

The dyadic weighted endpoint has the parallel two-child carry form.  Each child block can be harmless in
every homogeneous child test, while the primitive normalized sum is bad because the carry appears only
across the child boundary.  The identity that a block is the union of its two children does not decide
which child carries the bad obstruction.  A proof must localize that primitive carry to the same
first-return binary square or produce a homogeneous child obstruction.  Determinant valuation alone,
like static marker arithmetic, cannot provide that localization.

The natural failed-row acyclicity proof stops at the same place.  Let `C` be the current active
same-trace class in a frozen frame, and let `phi(r)` be the first dirty failed row of a nonadmissible
mixed-trace breaker `r`, after fixed-trace and clean exits have been removed.  Since `phi(r)` is
nonconstant on `C`, it cuts

```text
C_0 = {c in C : c notsim phi(r)},        C_1 = {c in C : c sim phi(r)}.
```

If the next active obstruction is known to lie wholly in one of these two sides, replacing `C` by that
side strictly decreases `|C|`, and then the lexicographic multiset of active trace-class sizes.  This
would forbid a nondecreasing dirty failed-row cycle.

The missing preservation premise is exactly the binary endpoint.  After saturating against all outside
rows that preserve an active edge, the only surviving case is that no proper side of the cut preserves
the active packet: every dirty row separates the unique pair `{x,y}`.  Then `phi(r)` need not decrease
the unfrozen support; it may simply move to another fully skew separator of the same two-point carrier.
Thus failed-row acyclicity is equivalent, at this endpoint, to excluding the skew binary ladder already
described.  It is not a formal finite-descent argument.

There is one noncircular strengthening of this descent.  Saturate the carrier before iterating: among
all restrictions obtained by adding any outside incidence row for which one fiber still contains an
active repair/reanchor edge, choose `(C,A(C))` lexicographically minimal, first by `|C|` and then by the
multiset of active trace-class sizes.  Then every outside row `z` has only two possibilities:

```text
z is constant on C,
or z separates every edge of A(C).
```

Indeed, if `z` is nonconstant and one fiber of `z|_C` still contains an active edge, that fiber is a
smaller carrier in the same obstruction category, contradicting the saturation choice.  Thus the old
active-pair preservation premise is built into the carrier choice.

If a dirty split in such an omni-saturated carrier preserves no active edge on either side, restrict to
one connected component `H` of `A(C)`.  Every nonconstant outside row is a proper two-coloring of `H`.
Hence vertices in the same bipartition class of `H` are indistinguishable by every outside row; any
internal row distinguishing them is a fixed-trace same-trace/false-clone local exit.  Therefore each
bipartition class is an ambient module, and in a prime irreducible carrier both classes must be
singletons.  The no-preserved-side branch is forced to the binary endpoint with one active pair.

This also collapses the circular monodromy cycle above after omni-saturation.  If the active graph is a
cycle of adjacent package-change edges, an odd cycle admits no separating outside row and is a module;
an even cycle of length greater than two has two bipartition classes of size greater than one, again a
module/local exit.  Thus any irreducible saturated monodromy carrier has active graph `K_2`.  Longer
chordless cyclic interval atoms are useful as unsaturated normal forms, but after saturation they reduce
to the same two-point successor-side `0001` square.

The final saturated binary carrier can therefore be stated without the ladder language.  There is one
active pair `{x,y}`.  Every row outside the fixed frame is either constant on `{x,y}` or separates it.
Rows constant on `{x,y}` are already in the fixed-trace/clean/local catalogues.  A separating row with
the opposite sign from another separating row closes if the two live in one peeled package, because the
pair is the balanced `0101/0011` flip; if they do not live in one package, the first package leak is the
same one-corner `0001` failure.  A same-sign pair in one residual fixed frame is a same-trace or
shifted-twin local exit.  Hence after all local and common-package closures, the only saturated survivor
is a sign-coherent bag `R` of separating rows, all with the same marked trace and all fully skew on
`{x,y}`.  The low-set update gives

```text
|R| = 0 mod q.
```

Thus the endpoint is exactly **binary separator-bag promotion**: an ambient breaker of this sign-coherent
q-divisible separator bag must be promoted to a first-return boundary side, yield a complete smaller
separator bag, or exit locally.  This is the same marker-complete support-decrease theorem in its
smallest saturated form.

This smallest form still cannot be proved from reduced trace data alone.  Abstractly, take a bag
`R={r_1,...,r_q}` of rows all with the same marked trace, all seeing `y` and missing `x`, and declare the
admissible first-return rows to be precisely those constant on `R`.  Add an ambient row `z` which splits
`R` into two nonempty parts.  The bag is sign-coherent and q-divisible, and `z` witnesses that `R` is not
an ambient module, but no admissible row produces either side as a complete first-return separator bag.
This is not a graph counterexample; it is the reduced logical obstruction showing that prime-shell
separation plus the low-set congruence still do not imply promotion.  A proof must use the actual
first-return history of `z`.

The breaker `z` can be sign-normalized.  If `z` is constant on the active pair `{x,y}`, then it is a
fixed-trace breaker relative to the saturated binary carrier; after the allowed marking, the
same-trace/false-clone or clean marked-add catalogue applies.  If `z` separates `{x,y}` with the sign
opposite to the rows of `R`, then any `r in R` gives the balanced two-row flip `0101/0011`.  When this
pair is in one peeled package it is a raw zero packet of total mass two and closes; when it is not, the
first package leak is precisely the one-corner `0001` endpoint already isolated.  Therefore the only
breaker of the separator bag not already absorbed by local catalogues or common-package failure is a
same-sign separator row, still outside the admissible first-return package, whose split of `R` must be
promoted to a complete first-return side.

For such a same-sign breaker, write

```text
R_0 = R \ N(z),        R_1 = R cap N(z).
```

If either `R_i` is known to be the complete shared-slack bag of a transported first-return square, then
the low-set update gives `|R_i|=0 mod q`; if `0<|R_i|<|R|`, minimality closes.  If neither side is
complete, the split contains no usable modular information: `|R_0|` and `|R_1|` may be arbitrary while
`|R|=0 mod q`.  Thus same-sign separator-bag promotion is exactly the assertion that a first-return
history attaches completeness to one of the two sides, or else that the non-completeness creates a local
fixed-trace/marked-add/completer exit.

Choose a same-sign breaker with `min(|R_0|,|R_1|)` minimal, and call the smaller side `S`.  If another
same-sign breaker crosses the cut, the four intersections give the primitive `2x2` circuit already
isolated; a realized diagonal closes, and absence of the diagonal is binary circuit elimination.  If no
same-sign breaker crosses the cut but some ambient row splits `S`, then either one of its fibers inside
`S` gives a smaller same-sign breaker side, contradicting the choice, or that row is a constant-on-pair /
opposite-sign case already routed to the local/common-package alternatives above.  Hence, in the
noncrossing branch, a minimal side `S` is an ambient module for the reduced separator-bag problem.  If
`|S|>1`, the same-trace/false-clone local catalogue closes the side after the allowed marking.  The only
remaining minimum-side face is therefore a singleton-side same-sign breaker whose singleton side is not a
complete transported bag.  This is the one-row form of the same promotion gap: first-return history must
explain why the singleton side is not a valid boundary, or else promote a larger complete side.

The singleton face is stable under the first-failed-row map.  Let `z` isolate `r in R`.  Error zero is a
completer, and error one is the one-defect local split already closed, so a survivor has high error.  If
the first failed row of `z` is fixed-trace or clean, the local catalogues apply.  If it is dirty and
same-sign but isolates a different singleton of `R`, then together with `z` it gives a crossing pair of
singleton cuts, hence the primitive `2x2` circuit.  If it isolates a proper side of size greater than
one, the minimum-side choice is contradicted unless that side is an ambient module/local exit.  Thus the
only first-failed row that remains in the endpoint is another high-error same-sign row isolating the
same singleton `r`.  Iterating the first-failed map therefore no longer moves through a large marker; it
is a one-point isolator loop.  A common peeled package for two consecutive isolators gives a same-trace /
shifted-twin local exit, so a surviving loop is again pure package-provenance failure on the same
singleton side.

If the loop contains two distinct isolators `z` and `z'`, then after marking the isolated row `r` they
have the same trace on the saturated separator bag, the same sign on `{x,y}`, and the same marked
quartet trace.  If they also have the same residual trace to the current frozen frame, the
same-trace/shifted-twin catalogue closes them.  Otherwise primeness supplies a breaker distinguishing
`z` from `z'`; a fixed-trace breaker is again local, while a non-fixed breaker is square-transverse.  Its
first dirty row either isolates a different singleton, crosses the singleton cut, or returns to the same
isolator loop by the preceding paragraph.  Therefore multiplicity of isolators is not a new endpoint.
After quotienting by the local equivalence, the final normal form is a single high-error same-sign
isolator whose first-failed-row routing returns to the same singleton side.

This is the same local target as the prime-shell reanchor false-twin breaker.  If the isolator self-loop
is a pure same-defect token pivot, the two consecutive token vertices have identical trace over the
middle peeled state; primeness gives either a module or the Section-`40` same-trace/false-clone
distinguishing template, so that branch is closed.  Therefore a surviving isolator self-loop must be
defect-switching: the first failed square uses two distinct defect sites and its missing corner is the
fully skew double-spend `0001` row.  Thus the one-row endpoint is not a new cycle phenomenon; it is the
defect-switching shared-slack square with all marker rows but one hidden behind the non-promoted
complete-bag condition.

Even this one-row normal form has a reduced trace model.  Take a q-divisible sign-coherent bag `R`, a
distinguished row `r in R`, and one high-error outside isolator `z` whose trace on `R` differs exactly at
`r` and whose trace on `{x,y}` has the same separator sign as `R`.  Declare the admissible first-return
family to contain only rows constant on `R` together with rows already closed by the local catalogues,
and set the first-failed routing of `z` to return to the same isolated row `r`.  This satisfies the
minimum-side, noncrossing, sign-normalized, and no-local-exit trace constraints above, but it supplies no
complete smaller bag.  Thus the self-loop cannot be excluded by the reduced separator-bag axioms; the
missing assertion is exactly that actual first-return history forbids such a self-loop by promoting
`{r}` or a larger side to a transported complete bag, or by producing one of the local exits.

Remembering the first-failed-row map as abstract data does not remove this self-loop.  One can impose
all reduced local constraints above and still have a one-state routing automaton:

```text
active pair {x,y},                  q-divisible sign-coherent bag R,
isolated row r in R,                same-sign ambient splitter z,
admissible rows constant on R,      first failed dirty wall of z returns to r.
```

This formal automaton satisfies the minimum-side and noncrossing normalizations, has no fixed-trace or
clean exit by construction, and has no proper complete side because only the whole bag `R` is declared
first-return-complete.  It is not asserted to be an actual prime-shell counterexample; rather, it shows
that the first-failed-row relation by itself gives no well-founded potential.  The missing datum is an
ordered square frame tying the singleton wall of `z` to the defect-switching square generated by the
dirty wall `r`.  Once those two directions are seated in one frame, the mixed-difference calculation
below captures the slack bag in `{r}` and closes.  If they are not seated in one frame, the obstruction is
exactly the single-turn common-frame gluing problem, equivalently the two-fiber overlap / pair-status
constancy endpoint.

The product-firewall trap identifies the exact missing capture statement.  If the defect-switching
square generated by the singleton isolator had complete shared-slack bag `R'` contained in the isolated
side `{r}` (or more generally in any proper side of size `<q`), then the exact low-set update would give

```text
|R'| = 0 mod q,
```

impossible for a nonempty sub-`q` bag.  Therefore the only way the singleton isolator can survive is by
**side escape**: the first failed wall is a singleton, but the complete shared-slack bag of the
transported square reassembles with rows outside that singleton side.  Equivalently, the last missing
theorem is side-capture for the first-return defect-switching square: the complete slack bag must lie in
the first isolated side, or a local exit occurs.  This is exactly the marker-complete promotion
requirement in one-row form.

The capture statement is elementary once the first-return square is aligned with the isolator axis.  In
a defect-switching square, a row belongs to the double-spent shared-slack bag only if its mixed second
difference on the two square axes is nonzero; equivalently, its trace changes in both square directions
with the same forbidden sign.  If the first square direction is the singleton isolator `z`, then every
row of `R\{r}` has the same value on the two endpoints of that direction, because `z` splits `R` only at
`r`.  Such a row has zero mixed second difference and cannot be part of the complete slack bag.  Hence an
axis-aligned first-return square has `R' subseteq {r}`, and the sub-`q` low-set contradiction closes it.

Thus the final self-loop is even narrower: it is not merely side escape, but **axis drift**.  The
transported defect-switching square would have to use a first active direction different from the
singleton isolator direction that produced the failed wall.  If that drifting direction is earlier in the
ordered first-return history, it contradicts the definition of the first failed row; if it is later, the
axis-aligned square at the singleton direction already gives the captured sub-`q` bag; and if the two
directions are incomparable, the two-coordinate comparison is exactly the primitive missing-diagonal
`2x2` circuit.  This comparison proves axis-lock once the two directions have been seated in one ordered
transport frame.  Therefore the remaining assertion can be stated as common-frame ordered axis-lock:
after the fixed, clean, and local exits are removed, the first dirty failed row remains comparable with,
and hence equal to, the first axis of the transported defect-switching square.

Here is the precise in-frame lemma.  Work after sign normalization, and let `z` be the same-sign
singleton isolator of `r`.  Suppose the first-return defect-switching square produced by the failed
interval test is expressed in the same ordered square frame as `z`.  If its first active direction is
earlier than the singleton direction, then `z` was not the first dirty failed row.  If it is later, then
the square using the singleton direction is already available earlier; by the mixed-difference
calculation above its complete slack bag is contained in `{r}`, so the sub-`q` low-set contradiction
closes it.  If the two directions are incomparable inside the same frame, the two separator cuts cross.
The four intersections are exactly the primitive `2x2` residue circuit; a realized diagonal gives the
local/common-package exit, and the absent diagonal is the previously isolated binary-circuit endpoint.
Thus no additional in-frame axis drift exists.

The remaining out-of-frame case can be normalized as a frame-change automorphism.  Let `F_z` be the
ordered frame in which the singleton isolator side is first visible, and let `F_square` be the ordered
frame in which the defect-switching square is first realized.  Transport the active binary coordinate
from `F_z` to `F_square` along a shortest first-return frame path.  If every elementary face on this path
is filled and has zero package curvature, the coordinate arrives in the same raw package and the in-frame
axis-lock lemma applies.  If the first bad face is not filled, this is the repair-fiber cubicality /
square-transverse breaker endpoint.  If it is filled but has nonzero curvature, its rank-one component is
the positive `0001` square.  If all faces are flat but the path returns with nontrivial coordinate
monodromy, the moved coordinate orbit is anonymous to admissible rows and falls to admissible-module
primeness.  Thus out-of-frame axis drift has no separate geometry: it is precisely the flat-connection
trichotomy specialized to the singleton isolator.

In particular, the only frame-change not already absorbed is a shortest rank-one frame slip: one
elementary transition carries the singleton wall into a different package while preserving all endpoint
chamber data.  That slip is exactly the two-fiber non-overlap table `{0101,0011}` if the sign changes,
and the same-sign singleton-isolator self-loop if the sign is preserved.  Hence common-frame ordered
axis-lock and dirty chart-change promotion are equivalent statements.

The rank-one slip itself is not excluded by the reduced connection axioms.  A two-chart model already
captures it: take two peeled packages with identical endpoint chambers and unary traces, let all
admissible rows be constant on a q-divisible carrier `R`, and let the transition between the two charts
identify every coordinate except one binary pair-status coordinate.  In the second chart that coordinate
is renamed to an anonymous copy, so the two singleton increments cannot be added in one raw space.  Add an
ambient row splitting `R` but keep it outside the admissible transition family.  This satisfies the
flat-face, scalar-holonomy, and endpoint-chamber constraints, yet it has no promoted side and no smaller
complete marker.  Thus a proof cannot be just "choose the shortest frame slip"; it must attach a
first-return boundary certificate to the slipped coordinate, or show that the absence of such a
certificate is already a local square-transverse exit.

Equivalently, the last missing statement is a **rank-one slip certificate theorem**:

```text
every first-return rank-one package slip either carries a complete shared-slack side,
or its uncarried coordinate is split by a strictly earlier/local square-transverse breaker.
```

The first alternative is support decrease, and the second is the smaller dirty chart-change square in the
edge-level formulation above.

One half of this certificate theorem is already formal.  Suppose the ambient splitter of the slipped
coordinate has been transported to an ordered boundary row for the same first-return interval.  After the
fixed-trace, unary, clean, and same-trace exits have been quotiented out, all rows of the slipped carrier
have identical trace to the marked quartet and to every other surviving packet.  The first interval test
can therefore fail inside that carrier only by the adjacency of the boundary row itself.  Hence the
failure set is a whole side

```text
C cap N(z)          or          C \ N(z),
```

not an arbitrary subfamily of `C`.  The singleton low-set update for the transported square identifies
this whole side as the shared-slack marker of a new marked two-class quartet.  If the side is proper, it is
a smaller first-return-complete marker and is forbidden by the minimality/low-set congruence argument; if
the side is all of `C`, then the splitter was not a splitter.  Thus **ordered-boundary rank-one slips are
closed**.  The only missing half is row-to-boundary transport: an ambient high-error splitter of the
slipped coordinate must either become such an ordered boundary row, or fail earlier in a local
square-transverse way.

This transport half has an exact first-failure normal form.  Start with a high-error splitter `z` of a
minimal slipped carrier `C`, attempt to insert `z` as the next boundary row, and let `psi(z)` be the first
dirty internal row at which the interval transport fails after all old-defect, inserted-root, filler,
fixed-trace, and clean failures have been routed to the closed catalogues.  If `psi(z)` splits a proper
subcarrier of `C`, the previous paragraph applies to that smaller carrier.  If two iterates of `psi`
split `C` in crossing ways, their four side intersections are the primitive `2x2` circuit.  If an iterate
becomes boundary-admissible, the ordered-boundary case closes.  Hence a minimal failure of
ambient-to-boundary transport is again a one-state bounce:

```text
z splits C,        psi(z) is dirty and high-error,        psi(z) splits the same side of C.
```

This is the ambient version of the singleton-isolator automaton.  It records the only possible way
row-to-boundary transport can fail without producing a smaller complete marker or a primitive circuit.

The one-state bounce is also the common shadow of the three named host frontiers.  Let `u=psi(z)` be the
returning dirty row.  In the minimal bounce, `z` and `u` induce the same nontrivial cut of the slipped
carrier `C`; otherwise their cuts are crossing, or one cut has a proper side, and the previous paragraph
closes.  Hence every visible unary chamber, endpoint chamber, and carrier-side residue is unchanged when
the attempted boundary row is replaced by its first failed row.  The only datum that can change is the
elementary hidden choice of the common edge.

Therefore:

```text
pair-chamber separation of the hidden choice  =>  no one-state bounce.
```

Indeed, if the pair chamber `sigma^- x sigma^+` separates the elementary hidden choice, then the
replacement `z -> u` cannot be a nontrivial hidden step inside one pair-chamber cylinder.  The two rows
must then have the same hidden choice and the same visible trace, so the same-trace/false-clone catalogue
or the ordered-boundary side argument closes.  Thus the bounce is exactly the negation of the
`host-orient115` input.

If pair-chamber separation fails, the failure is witnessed on one incident anchored square.  On that
square, either a unary witness incidence changes along the outgoing repair fiber or all unary witnesses
are constant.  In the constant case the outgoing repaired defects lie in one silent component; realized
componentwise no-split would make the outgoing defect unique, so no bounce is possible.  In the changing
case, choose the first unary witness wall on a shortest outgoing repair path.  Repair-fiber cubicality
places that wall in a statewise square; if the anchored one-corner lift and fixed-square rigidity hold,
the opposite defect on that square is unique, again forbidding the bounce.  Hence the same one-state
bounce is simultaneously:

```text
failure of anchored persistence/no-split on Q^+,
failure of the one-corner lift on Q_j(x),
failure of pair-chamber hidden-choice separation.
```

This formulation by itself does not prove any of the three inputs.  It does show that the ambient high-error bounce has no
fourth projection: closing any one of the three host frontiers closes the current rank-one slip endpoint,
and any survivor of one frontier is the same `{0101,0011}` / missing-`0111` table in the other two
languages.

There is one more reduction inside the bounce.  Since `z` and `u` have the same cut on `C` and the same
visible chamber data, they are twins over the current marked frame and over the slipped carrier.  If no
outside vertex distinguishes them, the pair is a prime-shell module/false-clone exit.  Let `b` be a
minimal outside breaker of `z,u`.  If `b` has fixed trace after marking the bounce frame, the
same-trace/false-clone catalogue closes.  If the cut of `b` on `C` crosses the cut of `z`, the four
intersections are the primitive `2x2` circuit; if it is a proper nested cut, the smaller-side argument
above gives a proper complete carrier or contradicts minimality.  Hence in an irreducible bounce every
minimal breaker of `z,u` is again high-error, dirty, and has the **same** cut on `C`.

Thus the bounce has a clone-packet normal form.  Let `K` be the class of all high-error dirty rows with
the same cut on `C` and the same visible chamber trace as `z`.  All first-return/admissible rows are
constant on `K`; otherwise their first nonconstant edge is a fixed-trace exit, a crossing/proper-side
descent on `C`, or a smaller one-state bounce.  Ambient primeness can break `K` only by another high-error
row outside the ordered boundary family.  If that breaker is promoted, ordered-boundary completeness
closes; if not, its first failed row returns to the same clone packet.  Therefore the one-state bounce is
equivalently:

```text
a same-cut high-error clone packet K that is an admissible module,
but whose ambient prime breaker is not promoted to first-return boundary provenance.
```

This is the rank-one form of admissible-module primeness.  It is strictly smaller than the earlier
separator-bag problem because the carrier cut on `C` is now fixed; the only remaining freedom is the
hidden package coordinate of the same-cut clone packet.

The clone-packet form is self-similar but not descending.  Recenter the active pair from the old carrier
to two rows `z,u in K`.  Every row of `C` is now fixed-trace for the pair `{z,u}`, because `z` and `u`
have identical incidence to `C`; the first nonconstant row is precisely the ambient breaker of `K`.  If
that breaker is fixed-trace in the recentered frame, the false-clone catalogue closes.  If it is dirty,
the first failed row of the recentered interval is again a same-cut high-error clone.  Thus first-failed
iteration can loop without decreasing either the old carrier `C` or the new clone packet `K`.  A
well-founded proof needs an additional ordered datum: either a boundary provenance certificate for the
breaker of `K`, or a local square-transverse edge that changes the hidden package coordinate.

In particular, any attempted potential depending only on

```text
|C|,        the side sizes of C,        |K|,
endpoint chambers,        unary chambers,        or package-commutator order
```

is constant on this recentered bounce.  The only possible decreasing quantity is a genuine
first-return boundary certificate.  This is why the current endpoint cannot be closed by iterating
prime-shell breakers or by minimizing over clone packets alone.

Maximalizing the clone packet gives the cyclic version of the same obstruction.  Let `K_0` be maximal
among rows with the fixed cut on `C` and fixed visible chamber trace, after local exits and proper/crossing
carrier cuts have been removed.  If an ambient row splits `K_0`, maximality and the preceding paragraph
force it to have the same carrier cut but a different hidden package coordinate; call the resulting
same-cut clone packet `K_1`.  Repeating, a finite irreducible survivor produces a directed chain

```text
K_0 -> K_1 -> K_2 -> ...
```

of same-cut clone packets, where each arrow is a high-error dirty breaker not promoted to a boundary row.
If the chain terminates, its last packet is an ambient module and the prime-shell/local exit closes it.
Hence a survivor contains a shortest directed clone cycle.  Consecutive clone packets cannot be compared
in one peeled package, because then their same cut on `C` makes them shifted twins over the recentered
frame and the local catalogue closes.  Thus every edge of the clone cycle is a package-change edge.

But a shortest clone cycle has no new large-cycle content.  A chord is a shorter package-change cycle; an
odd saturated active cycle is a module; and an even saturated cycle of length greater than two has the two
bipartition classes as modules unless a same-trace breaker exits.  Therefore the irreducible clone cycle
collapses to a two-packet package-change cycle.  In the row table this is again

```text
K_0 -> K_1 -> K_0        =        {0101,0011} with missing 0111.
```

So the maximal clone-packet route does not create a new endpoint: it is exactly flat monodromy reduced to
the adjacent two-fiber non-overlap atom.

This also pinpoints the tempting but invalid module-closure proof.  If the same-cut clone class were
hereditary under every ambient prime breaker, then the proof would be immediate: close the class under
all such breakers; all rows of `C` and all fixed-frame rows are constant on the closure, and any remaining
outside splitter would, by heredity, already belong to the closure.  The closure would then be a proper
nontrivial module of the prime shell, impossible.  Therefore the only way the endpoint survives is that
heredity fails in a history-sensitive way: a prime breaker of a same-cut clone packet keeps the same
static cut data but changes the hidden first-return package coordinate, so it is not a boundary-provenance
row of the same closure.  This failure of hereditary closure is precisely the missing single-turn
common-frame theorem.

Thus the remaining theorem can be stated in its smallest module-closure form:

```text
same-cut clone heredity:
  every ambient breaker of a maximal same-cut high-error clone packet
  either is promoted to the same first-return boundary closure,
  or creates a local/square-transverse/package-curvature exit.
```

The formal module argument above would then finish the rank-one slip endpoint.  Without this heredity
statement, a two-chart reduced model may keep extending the clone closure by renaming the hidden package
coordinate, never changing any static cut on `C`.

The heredity failure has an acyclic/holonomy dichotomy.  Form the directed clone-package graph whose
vertices are maximal same-cut clone packets and whose edges are the non-promoted high-error breakers
between them.  If this directed graph has a sink strongly connected component, then no breaker leaves that
component except local exits and promoted boundary rows; the module-closure argument above applies to the
union of the component.  Hence every irreducible survivor has a directed cycle.  After the saturation and
chord reductions just described, this cycle has exactly two vertices.  Thus the final hereditary failure
is not an arbitrary admissible-module failure but a **two-state package transposition**:

```text
K_0 <-> K_1,
same static cut on C,
same endpoint/unary chambers,
opposite hidden package coordinate,
no promoted boundary row.
```

If the transposition is traversed twice inside one ordered first-return frame, it is trivial and the
same-trace/shifted-twin catalogue closes.  Therefore the two traversals must live in incomparable
first-return frames.  Their commutator is exactly the rank-one flat holonomy already isolated; if a
filling square identifies the frames, the positive `0001` marker appears, and if no filling square exists,
the missing face is the square-transverse breaker.  Thus same-cut clone heredity, flat holonomy
triviality, and two-fiber overlap are the same final assertion.

The anchored subcase of the transposition is closed in the same sense.  If `K_0` and `K_1` are represented
on one anchored square with the same lower repaired-defect prefix and the same packet prefix, then the
same-cut condition makes the two clone rows indistinguishable on every row of the anchored frame.  A
breaker fixed on that frame is a same-trace/false-clone exit; a non-fixed breaker is square-transverse at
the anchored coordinate.  Hence an irreducible two-state transposition must also **move the anchor**: the
first-return square used to view `K_0` is not the square used to view `K_1`.  Along a shortest anchor-move
path, the first edge that cannot be filled is the one-corner lift failure, and the first filled edge with
nonzero package curvature is the positive `0001` marker.  If all edges are filled and flat, the
transposition is pure flat holonomy.  Thus the two-state package transposition is precisely the anchored
frame-slip endpoint, with no extra anchored case left over.

Multi-anchor drift also collapses to one edge.  Along a shortest flat anchor-move path, let `e_i` be the
first elementary move at which the hidden package label of the same-cut clone changes.  Before `e_i` the
clone is in the original boundary closure, and after `e_i` it is in the transposed closure.  All lower
anchor prefixes and all endpoint/unary chamber labels are unchanged across `e_i`; otherwise the first
changed wall gives a local exit or a square-transverse breaker before the package label changes.  Hence
`e_i` is a **chamber-flat anchored slip edge**:

```text
same lower anchor prefix,
same packet prefix through the moved coordinate,
same unary and pair chambers,
different hidden package label.
```

If the one-corner lift for this moved coordinate is available, the lifted corner sits on the original
anchored square and fixed-square rigidity identifies the hidden package label, contradiction.  If the
lift is unavailable, the missing corner is exactly the one-corner `0001` square.  Therefore the full
anchor-slip endpoint is a single chamber-flat anchored slip edge; no longer path or higher holonomy
remains after the first package-label change is selected.

The single anchored slip edge is the same as the minimal square-transverse breaker.  Let its endpoints be
`a,a'`.  They agree on the lower anchor prefix, the packet prefix through the moved coordinate, and all
unary/pair chambers, but they differ in the hidden package label.  If no ambient row distinguishes
`a,a'`, they are a prime-shell module.  Choose a minimal distinguisher `b`.  If `b` is fixed on the
anchored square, the same-trace/false-clone catalogue closes.  Otherwise the first coordinate at which
`b` changes is the moved coordinate itself; this is precisely the square-transverse case.  Trying to use
`b` as the missing boundary row gives the familiar dichotomy:

```text
all interval tests pass       ->  one-corner lift / boundary provenance,
first test fails locally      ->  Section 40 / marked-add / completer exit,
first test fails internally   ->  shared-slack 0001 marker.
```

If the internal failure has smaller support, support decrease closes.  If it has the same support, it is
the same high-error clone bounce already normalized above.  Thus the last single-edge form is:

```text
minimal square-transverse breaker whose first dirty failed row is fully skew
on the same support and changes only the hidden package label.
```

This is the one-edge version of Theorem G.

The support-preserving alternative has no further trace freedom.  In the square with axes "move the
anchor" and "insert the breaker `b`", every row outside the shared support passes the interval tests or
exits locally.  Every row inside the shared support has the same terminal trace:

```text
p(00)=p(10)=p(01)=0,        p(11)=1,
```

up to complement.  Thus the complete failed set is exactly the old support `R`; the low-set update gives
only `|R|=0 mod q`, with no smaller side visible.  If any compensating `0111` row is present in the same
peeled package, the pair `0001+0111=0101+0011` is a raw short-packet relation and the local catalogue
closes.  Therefore a surviving support-preserving breaker is precisely the absence of a same-package
`0111` compensator.  This is the hidden-median statement

```text
Omega_10 != emptyset, Omega_01 != emptyset, Omega_10 cap Omega_01 = emptyset.
```

So the square-transverse one-edge form and the two-fiber non-overlap form are literally the same row
table, not merely equivalent reductions.

The same table has a cover-theoretic normal form.  Fix the visible data consisting of the lower anchor
prefix, the packet prefix through the moved coordinate, and all unary/pair chambers.  After the local,
fixed-trace, and one-corner exits are removed, the remaining hidden states over this visible datum form a
two-sheeted cover: the sheet is the hidden package label.  A chamber-flat anchored slip edge is exactly an
edge that changes sheet.  If the cover branches, the branch point is a missing anchored one-corner lift or
a square-transverse breaker.  If the cover is unbranched and sheet-trivial, the hidden package label is
constant and the same-trace catalogue closes.  Hence an irreducible survivor is an unbranched nontrivial
`Z/2` cover of the visible chamber edge.

Taking a shortest nontrivial deck loop in this cover recovers the previous two-state transposition.  Any
proper subloop is sheet-trivial and hence has a common package; any chord shortens the loop; saturation
collapses longer loops to a module/local exit.  Thus the cover viewpoint gives a final equivalent
statement:

```text
the visible first-return chamber graph has no unbranched nontrivial
two-sheeted hidden-package cover after local exits and one-corner lift failures are removed.
```

This is exactly local simple connectivity of the first-return repair complex in rank one.  The reduced
two-chart model realizes such a cover abstractly, so it cannot be excluded by covering-space language
alone; one must prove graph-specific filling of the chamber-flat edge, i.e. the missing `0111` witness or
the complete `0001` marker.

Equivalently, put a `Z/2` cocycle `alpha` on chamber-flat anchored slip edges, with `alpha(e)=1` exactly
when the hidden package sheet changes.  Branch-free means `d alpha=0` on every filled local face.  If
`alpha` is a coboundary, a choice of sheet gauge makes the hidden package label constant on the visible
chamber component, and the same-trace/common-package closures apply.  Hence a survivor is a nonzero class

```text
[alpha] in H^1(visible first-return chamber graph; Z/2).
```

A filled face with odd `alpha`-sum is exactly a curved package face, hence the positive `0001` marker; an
unfilled face is the square-transverse breaker.  Therefore the last obstruction is a flat nonzero
`Z/2` holonomy class on the visible chamber graph after all local faces with curvature or missing corners
have been removed.  Proving that this graph is simply connected, or that every nonzero class has a
curved/missing face representative, is precisely the missing boundary-provenance theorem.

There is a standard coordinate-cancellation proof if the first-return chamber graph is cubical in the
needed rank-one sense.  Label every chamber edge by its moved repair coordinate.  On a closed visible
loop every coordinate label occurs an even number of times.  Choose a coordinate `j` whose two consecutive
occurrences bound a shortest subpath.  If each intervening coordinate swap with `j` is represented by a
filled flat square, commute the first `j`-edge across the subpath; the `Z/2` cocycle is unchanged because
each crossed face has even `alpha`-sum.  The two adjacent `j`-edges then cancel, producing a shorter
loop with the same holonomy.  Iterating kills the loop, contradicting nonzero holonomy.

Thus any minimal flat holonomy loop has a first intervening coordinate `k` for which the `j,k` swap is not
a filled flat square.  If the swap face is absent, this is exactly a square-transverse breaker; if it is
present with odd `alpha`-sum, it is exactly the positive `0001` face.  Therefore flat holonomy would be
closed by the following smaller theorem:

```text
rank-one coordinate-swap completeness:
  every coordinate swap needed to commute repeated repair coordinates
  is either a filled flat square, or is already a local/square-transverse/0001 exit.
```

This theorem is the cubical form of boundary provenance.  It is stronger than endpoint chamber data but
weaker than global repair-fiber cubicality: it is needed only for swaps encountered while cancelling a
shortest nonzero hidden-package holonomy loop.

The coordinate-swap theorem has a fixed-candidate half that is already closed.  For the required swap
`j,k`, suppose the same candidate/witness data certify the three visible corners `00,10,01`.  Every
affected degree row then contributes coefficients in one of `{0}`, `{0,1}`, or `{-1,0}` along the two
axes.  Since the two one-coordinate faces pass their interval tests, the two coefficients cannot have the
same forbidden sign; the sum at `11` remains in the allowed interval.  Hence the fourth corner is filled
and flat.

Therefore a failed rank-one coordinate swap must be **candidate-switching**.  The three faces have
certificates, but no single certificate survives all three.  In witness-packet language, three localized
packets have pairwise overlaps on the exposed faces but no common point.  If nearest-point transport
between two packets is gated, the median of the three pairwise witnesses lies in all three packets and the
swap fills.  If gatedness fails, take the first ungated edge; fixed-trace failure is the same-trace exit,
and non-fixed failure is the square-transverse breaker.  Thus the remaining coordinate-swap completeness
input is exactly:

```text
rank-one candidate-switching gate:
  every first ungated nearest-point edge in a three-face witness packet
  either is local/fixed-trace, or is the square-transverse/0001 support-decrease edge.
```

This is the coordinate-swap version of the missing `0111` witness.  It is weaker than arbitrary Helly for
all witness packets: only the three packets arising from a repeated-coordinate cancellation in a shortest
flat holonomy loop are needed.

The candidate-switching gate failure localizes to one anti-Horn square.  Let the three face packets be
`Omega_0,Omega_1,Omega_2`, with all pairwise intersections nonempty and triple intersection empty, chosen
with minimal total support.  Pick

```text
p_1 in Omega_0 cap Omega_1,        p_2 in Omega_0 cap Omega_2,
```

at minimum distance inside `Omega_0`.  Along a shortest path in `Omega_0` from `p_1` to `p_2`, the
indicator of `Omega_1` must turn off and the indicator of `Omega_2` must turn on.  If these changes occur
on separated edges, the intermediate segment gives a smaller two-face gate failure; if they coalesce in
one fixed frame, the same-trace catalogue closes.  Hence the irreducible event is one square in which the
two packet indicators have three corners

```text
00,        10,        01
```

and the `11` corner is absent.  For a fixed candidate this square was filled by the interval calculation
above.  Therefore the absent `11` is exactly candidate switching at the same coordinate swap.  Marking the
rows whose packet indicator is the positive AND gives the shared-slack `0001` marker.  Thus the
candidate-switching gate theorem is not a larger Helly problem; its minimal failure is again the same
one-corner anti-Horn square.

The candidate data in that square has a forced triangle form.  Let `c_00,c_10,c_01` be certificates for
the three present corners.  If one certificate works on two adjacent faces and another works on the third,
then the two-face interval calculation transports the first certificate across the remaining face unless
there is already a fixed-trace/local exit.  Hence no certificate can be extendable across an adjacent
pair in an irreducible failure.  After quotienting certificates that agree on the current marked frame,
the candidate-switch graph is therefore the triangle

```text
c_00 -> c_10 -> c_01 -> c_00,
```

where each arrow is the first face on which the previous certificate stops working.  If this directed
graph had a sink or a repeated vertex, the sink/repeated certificate would supply a common candidate for
all three faces and the fixed-candidate argument would fill `11`.  Thus the residual anti-Horn atom is
not arbitrary candidate switching; it is a **three-certificate cycle** with no common fixed-frame
representative.

A breaker of two adjacent certificates in this cycle is handled exactly as before.  Fixed-trace breakers
give the same-trace/false-clone catalogue, and non-fixed breakers are square-transverse at the swap
coordinate.  Therefore the three-certificate cycle is another presentation of the same boundary
provenance gap: the proof needs a first-return row that realizes the missing common certificate, or a
square-transverse/`0001` support-decrease edge.

The triangle also has no independent ternary residue.  Let `b_0,b_1,b_2` be the first breakers on its
three certificate-change arrows, after all fixed-trace and clean marked exits have been removed.  Each
`b_i` is dirty and square-transverse at the same rank-one swap coordinate; otherwise the first non-dirty
or off-coordinate breaker is a local exit.  If one `b_i` has a proper failed support, that support is the
smaller marker.  In the fully skew survivor all three have the same active support and each has one of the
two signs on the active pair.  Two of them therefore have the same sign.  If those two sit in one residual
frame, they are same-trace/shifted twins after marking the active pair.  If they do not, the first edge
that transports one frame to the other is a two-state package-change edge.  Hence every irreducible
three-certificate anti-Horn hole collapses to the already isolated two-state transposition / adjacent
dirty-turn problem.

There is a sharper geometric normalization of this same cycle.  Write the three visible corners as
`tau_0,tau_1,tau_2`, and write the three off-root witnesses carried by the certificates as
`u_0,u_1,u_2`, with indices chosen so that the missing diagonal pairs are `(tau_i,u_i)`.  The pairwise
face certificates force exactly the six cross-transports

```text
tau_i u_j        (i != j).
```

Thus the distributed witness graph is

```text
H_hex = K_{3,3} \ {(tau_0,u_0),(tau_1,u_1),(tau_2,u_2)} = C_6.
```

The absence of a common certificate is precisely the absence of a one-frame realization of this
alternating hexagon.  More exactly, common-frame gluing is equivalent to localizing one cyclic rooted
normal form: for some `i`, the five-vertex seed

```text
H_i = H_hex \ {u_i}
```

must be realized on one Section `40` frame as the balanced rooted `1^2 2^3` candidate instance with
visible corner `{tau_0,tau_1,tau_2}`.  If such a seed is localized, pair-rigidity fixes the marked pair
and rooted support-edge propagation reseats the other two roots in the same frame; conversely any common
frame contains each such cyclic seed.  Hence the actual remaining gluing input is not another scalar
anti-Horn inequality but a **distributed-hexagon-to-one-frame** theorem.

Once this one-frame localization is available, the scalar half is automatic.  Deleting any `u_i` from the
alternating hexagon leaves a path `P_5`, not a split `K_2 + K_3`; therefore the marked
one-error add on either degree-one side is nonisolating in the in-frame Section `40` catalogue.  The
side-swap symmetry gives the same conclusion on the other side, so the localized packet has
`sigma_1=0`, two marked deleted one-error adds, and hence `S=sigma_1+|M_R|=2`.  Thus a localized
alternating hexagon is already killed by the existing in-frame machinery.  The sole live statement is the
existence of the common localization frame, equivalently a two-off-root common-shadow synchronization or,
in one-corner language, an ambient-to-fixed fiber-preserving shared-slice lift.

The shared-slice lift is the one-corner host-transversal endpoint in disguise.  Fix adjacent visible
corners `sigma,sigma'`, a common root `u`, and the common shared-coordinate slice
`F_(b_1) cap S_c(sigma,sigma')`.  The distributed hexagon already puts the ambient point
`x_rho=(sigma',u)` in the correct binary cylinder of that slice; what is missing is a point of the fixed
shadow `Sh_F(sigma',u)` in the same slice.  Package the demanded incidences as a peeled anchored
near-regular set `T_rho` with low set `I_rho`.  A compatible degree-congruent transversal for this
one-corner model gives

```text
N(x_rho) cap T_rho = I_rho = L(T_rho).
```

Then the local completer theorem applies to `x_rho`, so the ambient point is promoted to the fixed shadow
and the shared-slice lift exists.  Conversely, a fixed-shadow lift supplies exactly such a transversal by
taking its realized incidence set as `I_rho`.  Thus the synchronized-hexagon obstruction is equivalent to
a local compatible-transversal theorem on one shared slice.  The host absorption formulation below is the
same endpoint: one must find a compatible multi-swap/completer in the anchored near-regular set, or obtain
the same successor-side `0001` shared-slack marker.

The visible part of this lift is already forced.  For each cyclic `i`, the four cross-incidences

```text
(tau_{i+1},u_{i+1}), (tau_{i+2},u_{i+2}),
(tau_{i+1},u_{i+2}), (tau_{i+2},u_{i+1})
```

form a balanced `2 x 2` tile in the common visible `c_i`-hyperplane shared by
`tau_{i+1}` and `tau_{i+2}`.  Therefore the missing gluing is not construction of a visible tile; it is
adjacent-slice admissibility for a missing-corner transport

```text
rho = (tau_i,u_j),        j in {i+1,i+2}.
```

Equivalently, one needs the one-corner adjacent-slice extension: if `(sigma,u)` is already realized on a
fixed Section `40` frame and `sigma'` shares one visible coordinate with `sigma`, then the root-side
transport `(sigma',u)` has a fixed-frame lift in the shared-coordinate slice.  In the normalized
rooted-`C_6` tile this is a unique median-entry problem: the shared slice meets the fixed hyperplane in
one nontrivial visible point `s_*`, so any successful lift must land at `s_*`.  Thus the direct endpoint
is the ambient-to-fixed fiber-preserving lift at this forced median point, or equivalently the compatible
transversal theorem for the one-corner incidence model `H_F(sigma,sigma';u)`.

This separates the visible and hidden parts of the lift.  The visible part is done: the corner geometry
already gives the forced point `s_*` and puts `x_rho=(sigma',u)` in the admissible binary cylinder over
the shared slice.  The missing part is hidden fiber-uniformity on

```text
M_rho = F_(b_1) cap S_c(sigma,sigma') cap pi^(-1)(s_*).
```

For a single local witness `a`, write

```text
E_a = { m in M_rho : m sim a }.
```

If each `E_a` is empty or all of `M_rho`, the ambient cylinder incidence is constant on the hidden median
fiber, so the fixed point above `s_*` realizes exactly the low set `I_rho` and the compatible transversal
follows.  If some `E_a` is mixed, choose a hidden edge of `M_rho` crossing its boundary and then a closest
return to `E_a` on the far side.  Thickening the terminal return edge to the first normalized hidden
square gives a function

```text
p_a(i,j) = 1_{m_ij sim a}
```

whose only irreducible first-switch pattern is the successor-side `0001` square: three predecessor
corners are outside `E_a` and the terminal successor corner is inside.  Any earlier opposite-rail hit in
`E_a` shortens the bad hidden edge, and any predecessor-anchored suffix is handled by the strip-transfer
theorem.  Thus adjacent-slice admissibility has again reduced to the same single-witness median-square
interaction sign law, or to the same `0001` shared-slack carrier if the sign law fails.

The quotient side has no coarser residue once the fiber status is made explicit.  For the four local
states `q_00,q_10,q_01,q_11`, let a fiber row be

```text
r(K)=(d_00(K),d_10(K),d_01(K),d_11(K)).
```

After the one-edge predecessor and persistence inputs are factored off, rows with `d_00(K)=0` have only
the five forms

```text
0000, 0001, 0101, 0011, 0111.
```

The mixed rows define the two visible sets `Omega_10` and `Omega_01`; the row `0111` is exactly their
intersection.  Therefore the only non-overlap table is still

```text
Omega_10 != emptyset,        Omega_01 != emptyset,        Omega_10 cap Omega_01 = emptyset,
```

represented by the pair `{0101,0011}`.  Factoring off the already-used one-edge predecessor/persistence
inputs, the remaining two-square assertion is precisely common-edge pair-chamber cylinder rigidity: on a
fixed-trace common-edge packet, the two incident pair-chamber labels determine the elementary hidden
choice.  Equivalently, there is no nontrivial elementary hidden edge inside one fixed pair-chamber
cylinder.  This is the `host-orient115` surface of the same adjacent-slice obstruction.

The pair-chamber cylinder failure has a one-edge basin normal form.  Fix a `C^+`-anchored span-one active
side and a passive basepoint `u in C^+`.  For each passive defect `y`, let `P(y)` be the repaired packet
of the corresponding hybrid state, and let

```text
B_u = { y : some shortest passive silent path from u to y keeps packet P(u) throughout }.
```

Then `B_u` is geodesically star-convex from `u`.  If some passive defect has `P(y) != P(u)`, every
shortest path from `u` to it has a unique first boundary edge `ab` with `a in B_u` and `b notin B_u`; that
edge is packet-changing by definition of the basin.  The constant-packet predecessor chain to `a` carries
no remaining choice, so the unresolved step is purely local at `ab`.  Keeping the incoming chamber on one
incident square `Q^-` fixed, the other incident square `Q^+` sees a set `R^+` of realized outgoing
opposite defects from packet-changing continuations over `b`.

Thus common-edge pair-chamber rigidity reduces to the boundary outgoing assertion on `Q^+`: unary witness
incidence is constant on the realized outgoing set, and within the realized silent component there is at
most one outgoing defect.  If a unary witness changes, the first changing edge gives the already isolated
square-transverse/`0001` route.  If every unary witness is constant, the one-square silent-component
theorem puts all of `R^+` in one component; the only remaining input is the realized componentwise
singleton statement `|R^+ cap C| <= 1`.  This is exactly the `host-opppair123` surface of the same
obstruction, with no global edgelessness or all-defects no-split theorem required.

Equivalently, without choosing the basin side, the two-square form is elementary two-sided
silent-component injectivity.  Let `sigma^-` and `sigma^+` send a common-edge packet state to the connected
component of its repaired opposite defect in the silent graphs of the two incident filled squares
`Q^-` and `Q^+`.  Pair-chamber cylinder rigidity says that the product map

```text
sigma^- x sigma^+
```

has no nontrivial elementary hidden edge in one fiber.  A failure is therefore one elementary common-edge
hidden step whose endpoints lie in the same silent component on both sides.  This is only a two-square
normal form, not a proof from one-square data: shortest sidewise silent paths need not synchronize, and a
sidewise chamber-flat edge does not by itself determine the common-edge packet.  The basin reduction above
is the additional localization that turns the two-sided failure into the outgoing `Q^+` singleton problem.

A failure of this realized singleton statement is already the one-square silent-edge atom.  Choose two
realized outgoing defects in `R^+ cap C` with minimum distance in the silent component and take the first
edge of a shortest silent path on which the repaired opposite defect changes.  All unary witness
incidences and the incoming anchored chamber are fixed along that edge, so it is chamber-flat.  If the
anchored one-corner lift on the first changed square `Q_j(x)` is available, the lifted corner realizes the
new repaired opposite defect on the old anchored square, and fixed-square opposite-defect rigidity forces
the two defects to be equal.  Therefore an irreducible realized no-split failure is exactly failure of the
anchored one-corner lift, and the first missing lift corner is the same successor-side `0001` square.  This
is the `host-silentedge128` surface of the adjacent-slice obstruction.

The one-square endpoint can be stated without the outgoing notation.  For a fixed incident square `Q` and
repaired edge `e`, let `Gamma_(Q,e)` be the silent graph on repaired opposite defects, with an edge when
an elementary hidden step preserves every single witness incidence on `e`.  The one-square
silent-component theorem gives:

```text
connected components of Gamma_(Q,e) = unary chambers.
```

Hence the following are equivalent at this local surface:

```text
Gamma_(Q,e) is edgeless;
every unary chamber is a singleton;
every elementary hidden step changing the opposite defect crosses a unary wall;
incident-square opposite-defect wall detection holds.
```

Thus a failure has the exact normal form of one chamber-flat silent edge between distinct opposite
defects.  Since `Gamma_(Q,e)` is undirected, any vertex statistic on repaired opposite defects--wall
count, support size, parity, first changed coordinate--is constant on components or ignores the
orientation of the silent edge.  It cannot prove edgelessness.  A successful one-square proof must
therefore use pairwise ordered data of the edge itself.

For such a chamber-flat silent edge `(x,y)`, let `j` be the first changed repaired-defect coordinate:

```text
D(x)|_<j = D(y)|_<j,        P(x)|_<=j = P(y)|_<=j,        D_j(x) != D_j(y).
```

Conditional on fixed-square coordinate-`j` opposite-defect rigidity, the exact missing one-square input is
only the anchored one-corner lift on the already anchored square `Q_j(x)`: the shared lower repaired-defect
prefix and packet prefix through `j` must realize the `D_j(y)` corner on `Q_j(x)`.  Such a lift forces
`D_j(y)=D_j(x)` and closes the edge.  Present silent-component data do not supply this lift; their failure
is precisely the successor-side `0001` square.

The same one-edge atom has a prefix-star sign form.  Fix a center `y`, a first changed coordinate `i`, and
a lower packet prefix `pi`.  For every silent edge `y-w` with

```text
P(w)|_<i = pi
```

and first label coordinate `i`, record the sign `epsilon(y,w)` of the coordinate-`i` repaired-defect
change.  If two such silent edges have opposite signs while preserving the same lower prefix, their two
anchored coordinate-`i` squares share the lower repaired-defect prefix and packet prefix through `i`.  A
common anchored one-corner lift would put both opposite defects on the same fixed square and fixed-square
rigidity would identify them; without the lift, the first failed corner is exactly the `0001` square.
Thus the one-square silent-edge endpoint is equivalently:

```text
P(w)|_<i = P(z)|_<i = pi
  =>  epsilon(y,w) != -epsilon(y,z)
```

unless a local fixed-trace exit or the successor-side shared-slack marker has already appeared.  This
prefix-star sign uniqueness is pairwise ordered data on the silent edge; unlike vertex statistics on
`Gamma_(Q,e)`, it can see the orientation needed for the anchored lift.

The noncircular way to prove this sign uniqueness is the support-local fourth-corner package.  Fix the
anchored square `Q_i(y)` and try to realize the opposite-sign corner.  If one candidate/witness certifies
the three exposed faces, the additive interval lemma fills the corner.  Hence any failure must switch
candidates.  The direct transverse-square gate reduces candidate switching to a first ungated square, and
the fixed-candidate obstruction on that square is exactly double same-sign saturation of one retained
slack row.  If the two saturated repair vertices coalesce after marking that slack row, the Section `40`
same-trace `P_3` / false-clone catalogue closes.  If the marked support is clean, the marked-add catalogue
closes.  The residual nonclean case is the budget-one mixed-trace breaker: after localizing at the
saturated row, the obstruction has one anchor-supported unique defect and the first failed row remains
square-transverse.

Thus prefix-star sign uniqueness, anchored one-corner lift, fixed-square opposite-defect rigidity,
repair-fiber cubicality, and filled-overlap reconstruction all reduce to the same routing statement:

```text
transverse-breaker admissibility:
  a minimal square-transverse breaker with no Section 40 localization
  passes the one-coordinate interval tests,
  or its first dirty failed row is a strictly smaller square-transverse breaker.
```

The clean support half of this admissibility theorem is closed by the marked-add catalogue.  The only
remaining half is the dirty budget-one `Abs(1)` / reanchor-breaker case, equivalently the prime-shell
cycle-breaker for a reversible singleton reanchor graph.  This is again the same q-marker
support-decrease problem, now in its smallest unweighted mixed-trace form.

The budget-one branch has the one-point isolator normal form.  A singleton reanchor is reversible: in the
miss case the deleted low defect becomes the new miss defect, and in the add case the deleted high defect
becomes the new add defect.  Thus miss/add type and low-set size do not orient the reanchor graph.  A
non-backtracking reanchor cycle can survive the raw near-regular equations unless primeness supplies an
external breaker of two consecutive token vertices.  If that breaker has fixed residual trace, Section
`40` closes it as a false-clone/same-trace distinguisher.  If it is clean, marked-add closes it.  The only
surviving breaker is dirty and square-transverse.

After minimum-side normalization, such a dirty reanchor breaker isolates a single row `r` of the
sign-coherent shared-slack bag and its first failed dirty wall returns to the same singleton side.  If the
defect-switching square generated by that wall is aligned with the isolator direction, its complete
shared-slack bag is contained in `{r}`; the exact low-set update gives a nonempty sub-`q` set of size
`0 mod q`, impossible.  Hence a survivor must be **axis drift**: the transported defect-switching square
uses a first active direction different from the isolator direction.  In one ordered frame this is ruled
out by earliest-axis comparison or by the primitive `2 x 2` circuit; out of frame it is exactly the
rank-one package slip / common-frame gluing endpoint already isolated above.  Therefore dirty `Abs(1)`
does not open a new host branch: it is the same rank-one slip certificate theorem in reanchor language.

At the reduced trace level this two-state transposition is consistent: take two clone packets with the
same cut on `C`, let all admissible boundary rows be constant on their union, and let the only ambient
breakers swap the hidden package label while preserving all visible chambers.  This is not a graph
counterexample; it says that the last proof step must use actual first-return square geometry, not
module closure, finiteness of the package graph, or endpoint chamber data.

Consequently the actual blocker is **not** an axis-order argument inside a fixed frame.  It is
common-frame synchronization for two consecutive dirty axes.  In binary-ladder language, adjacent dirty
rows with opposite signs close as the raw zero packet `(e_x-e_y)+(e_y-e_x)` once they are in one raw
space; adjacent rows with the same sign close as same-trace/shifted twins once they are in one residual
fixed frame.  A surviving axis-drift loop must therefore change peeled package at the adjacent dirty
turn.  The final missing input can equivalently be stated as single-turn common-frame gluing: every
first dirty failed row and the defect-switching axis it generates can be seated in one ordered
first-return frame, or the first package-change edge is itself a complete smaller marker/local exit.

In the hidden-median formulation this is the two-fiber overlap atom.  After the predecessor-side
persistence and one-corner local exits are removed, every relevant fiber row over a normalized hidden
square has one of the five patterns

```text
0000, 0001, 0101, 0011, 0111.
```

The rows `0101` and `0011` are the two opposite adjacent dirty turns, while `0111` is exactly the common
overlap row that puts both turns in one transported frame.  Thus, writing `Omega_10` for rows with the
`0101` turn and `Omega_01` for rows with the `0011` turn, common-frame gluing is equivalent at this
endpoint to

```text
Omega_10 != emptyset and Omega_01 != emptyset  =>  Omega_10 cap Omega_01 != emptyset.
```

If the intersection is nonempty, the `0111` row supplies the common shadow and the in-frame axis-lock
lemma above closes.  If the intersection is empty, the only surviving table is the mixed pair
`{0101,0011}` with no common hidden choice.  This is precisely the pair-chamber separation / anti-Horn /
one-corner-lift endpoint in different language: the pair chamber must determine the elementary hidden
choice, or the two one-sided witnesses must overlap on a common fixed-frame row.

There is a useful commutator form of the same statement.  Let `tau_H` and `tau_J` be the partial
identifications of raw discrepancy coordinates obtained by transporting across the two successor faces,
after all predecessor, unary, fixed-trace, and clean exits have been quotiented out.  If

```text
tau_H tau_J = tau_J tau_H
```

on the active binary coordinate, then the two upper increments are in one raw coordinate space.  The
same-candidate interval calculation gives the shared-slack q-marker, and the in-frame axis-lock argument
above either captures it in a sub-`q` side or produces the realized diagonal/common-package exit.  If the
commutator is nontrivial, choose the first moved coordinate on a shortest nontrivial commutator loop.
Every proper subpath has a common package, while the closing edge does not.  The four traces of that
coordinate around the square are therefore, up to complement and reversal,

```text
0101,        0011,        missing 0111,
```

or, after marking the first package leak, the positive `0001` row.  Thus noncommuting package transport
is not a new group-theoretic obstruction; it is exactly pair-status nonconstancy.  Conversely, the
`{0101,0011}` non-overlap table is a nontrivial commutator of the two successor package identifications.
This also explains why abelian or scalar holonomy invariants vanish: the obstruction is the failure of
the two partial identifications to commute on one coordinate, not a nonzero numerical circulation.

There is, however, a useful arithmetic sharpening of this last sentence.  In the irreducible
commutator case the active coordinates form a two-sheeted hidden-package cover over the visible
repair loop.  A row that separates the two sheets everywhere is the **sheet character** of this cover:
on each lifted edge it is locally constant in the transported coordinate, but after one circuit it
returns on the other sheet.  Thus it creates no branch point and no scalar curvature.  If the total
shared-slack carrier is `R=R^0 disjointunion R^1` with the two sheets equal in size, then

```text
|R| = 0 mod q,        |R^0|=|R^1|=|R|/2.
```

Consequently the odd part of the obstruction is only provenance.  For odd `q`, any promoted
sheet-character side is already a smaller q-marker, since `2` is invertible modulo `q`.  For even
`q`, and especially for dyadic `q`, the same calculation leaves a half-carrier with residue
`q/2 mod q`; this is exactly the two-sheet carry shadow rather than a scalar holonomy class.  Thus
the final commutator is pure `2`-primary sheet-character monodromy: either one proves that the sheet
character is a first-return boundary row, or its first discontinuity must be a branch point, i.e. a
one-corner lift failure / square-transverse breaker.

The ambient breaker can be purified to this sheet character.  On a flat edge of the cover, write the
four values of a row `b` as

```text
(b(v^0), b(v^1), b(w^0), b(w^1)),
```

where the superscripts are transported sheet labels.  After quotienting complements there are three
nonlocal possibilities:

```text
0000 or 1111        constant,
0011 or 1100        base-boundary cut,
0101 or 1010        sheet character.
```

Every other table has one endpoint sheet-split and the other endpoint not sheet-split, or has the split
orientation reverse across the edge.  Thickening the first such edge to the anchored repair square gives
exactly the one-corner branch point: in the first case the square has the positive `0001` corner after
marking the endpoint where the split appears; in the second case the two opposite signed splits give the
same square-transverse breaker after reversing one sheet label.  Therefore, once local exits and
square-transverse breakers are removed, the property "b separates the two sheets" is locally constant
along the flat loop.  If `b` ever makes a base-boundary cut, the ordered-boundary side argument supplies
the complete marker after promotion; in the final quotient those cuts have been removed.  Hence any
remaining ambient breaker that distinguishes the hidden package cover is forced to be the global sheet
character on the whole active carrier.

This purification also removes the last size ambiguity.  Write `q=2^s` and `|R|=m q`.  If `m` is even,
then each sheet has size

```text
|R^0|=|R^1|=(m/2)q = 0 mod q.
```

Thus a promoted sheet-character side is already a proper complete q-marker and support decreases.  Hence
an irreducible dyadic sheet-cover survivor has `m` odd.  After deleting any proper first-return-complete
even-multiplicity subcarrier, the carrier may be assumed primitive:

```text
|R| = q mod 2q,        |R^0|=|R^1|=q/2 mod q.
```

Equivalently, modulo `q/2` each sheet is invisible, but modulo `q` the two sheets are the two children of
one primitive carry.  Therefore the sheet-cover endpoint is not a general large-marker problem.  It is
the two-piece odd-layer atom: realize one sheet as a first-return child carrier, or locate the first
edge where the sheet character stops being transported, which is the same one-corner branch point
already identified above.

The cover can also be gauge-normalized to a single slip edge.  Choose a spanning tree of the visible
repair loop and transport sheet labels along it.  In this tree gauge every tree edge has table `0101`
for the sheet character.  Since the cover is nontrivial, some cotree edge returns the label reversed; on
a shortest nontrivial loop there is exactly one such cotree edge, otherwise two reversed edges or a chord
split off a shorter nontrivial loop.  Thus all distributed sheet monodromy is equivalent to one anchored
rank-one slip edge.  Locally transported labels make that edge look flat, while the tree gauge sees the
two endpoint sheet labels interchanged.  A one-corner comparison square between the two gauges either
fills and identifies the sheets, or its missing/curved corner is exactly the positive `0001`
square-transverse breaker.  Therefore the two-child sheet-character endpoint is the same single anchored
frame-slip edge, now with the arithmetic normalized to the primitive half-carrier `q/2 mod q`.

The single-edge form is local at the star of the slip edge.  In the tree gauge, let the unique reversed
edge be `e=vw`.  The tree sheet

```text
R^0 = {one lift of each visible carrier row}
```

has no boundary on any tree edge; both boundary edges of `R^0` project to `e`.  Hence `R^0` is a
first-return-complete child carrier if and only if the slip edge itself is an ordered first-return
boundary edge in the anchored star.  If it is not, test the anchored star of `e` by the first repair
coordinate `k` for which the star transport fails.  A fixed-candidate failure is impossible by the
one-coordinate interval calculation; a fixed-trace failure is the Section `40` same-trace/false-clone
exit.  The only remaining failed star table has one endpoint of `e` sheet-split and the other not, or
has the sheet split reversed after the `k`-move.  These are precisely the two edge-table impurities above,
so the `e,k` square is a branch point: after marking, it is the positive `0001` corner or the
square-transverse breaker.

Thus the cover endpoint has been reduced from a loop statement to the following single-star statement:

```text
single-slip child realization:
  a primitive two-sheet carrier with unique anchored slip edge e
  either has e as an ordered first-return boundary edge, so one sheet is a q/2-child carrier,
  or the anchored star of e contains a branch square (0001 / square-transverse).
```

This is the same provenance content as Theorem G, but with all loop, Hall, finite-holonomy, and
large-marker arithmetic removed.  The only missing datum is the first-return status of the unique slip
edge in its own anchored star.

There is no residual ternary packet at this single-star level.  A candidate-switching obstruction in the
star would have to use the slip edge `e` together with two or more repair coordinates.  Choose two
consecutive such coordinates in a shortest star word.  If their swaps with `e` are filled and flat, the
coordinate-cancellation argument commutes them past `e` and shortens the word without changing the sheet
character.  The first swap that is not filled and flat is already the branch square from the previous
paragraph.  Hence a three-certificate cycle cannot survive after tree-gauge normalization: the
distributed alternating hexagon has collapsed to a single anti-Horn face `e,k` with absent fourth corner.
Thus the live single-star statement is exactly one-corner, not higher-Helly.

The tempting final step would be to say that a slip edge whose entire anchored star is filled and flat is
automatically an ordered first-return boundary edge.  This is precisely the point where provenance enters:
local star-flatness says the edge is compatible with every one-coordinate repair test, but it does not
record that the edge occurs as the next boundary in a first-return history.  A reduced two-chart model
can keep the star flat by renaming the hidden sheet after the edge; all local edge tables are
`0101/1010`, no branch square appears, and yet the sheet edge is not in the ordered boundary family.
Therefore the final atom is the following one-edge provenance principle:

```text
locally star-flat slip-edge provenance:
  a primitive anchored slip edge whose full anchored star is filled and flat
  is an ordered first-return boundary edge,
  unless the two-chart renaming is realized by a branch square.
```

Equivalently, single-slip child realization is closed exactly when locally star-flat hidden-sheet
renamings cannot remain purely ambient.  This is strictly smaller than Theorem G's original
ambient-splitter statement: the carrier is primitive, there is one slip edge, all star faces are flat,
and the only missing assertion is membership of that edge in the first-return boundary family.

Primeness does not by itself force that membership.  Close the anchored star under every first-return
boundary row and every filled flat star transport; call the resulting local boundary closure `B_*`.  In
the locally star-flat survivor every row of `B_*` is constant on the two sheet lifts of each visible
carrier row.  If no ambient row separates the sheets, the two lifts are a prime-shell module and the
local exit is immediate.  Hence primeness supplies an ambient separator `h`.  Edge-table purification
forces `h` to be the global sheet character, because base-boundary cuts and mixed edge tables have already
exited.  But adjoining `h` to `B_*` closes the child carrier only when `h` is itself first-return
admissible; if it is not, recentering the anchored star at `h` reproduces the same locally star-flat
slip-edge provenance problem.  Thus the final atom is self-similar under prime closure, and no module
closure argument can replace the missing provenance step.

The gap at this stage can be localized even further by comparing star-flatness with the full boundary test
suite.  Let `h` be the global sheet-character separator supplied by primeness.  If `h` fails some
one-coordinate interval test outside the immediate anchored star, choose the earliest such boundary row
`b` and connect its test coordinate back to the slip coordinate by a shortest boundary word.  Filled flat
faces commute `h` across this word without changing its sheet-character table.  Therefore the first place
where the commutation cannot proceed is a nonfilled or curved face.  A fixed-trace nonfilled face is a
Section `40` exit; a clean face is the marked-add exit; and a dirty nonfilled/curved face is exactly the
`0001` / square-transverse branch square.  Thus, after all branch squares and local exits are removed,
the star-flat sheet character passes every one-coordinate interval test in the full boundary closure.

Consequently the provenance atom can be restated without mentioning all peripheral tests:

```text
star-to-boundary normality:
  if a primitive sheet-character separator is locally star-flat
  and every attempted peripheral commutation is filled and flat,
  then the separator is an ordered first-return boundary row.
```

This is the only point not supplied by the interval arithmetic itself.  The interval tests promote `h`
once `h` is allowed into the ordered boundary family; star-to-boundary normality is the assertion that a
row passing those tests and commuting with the existing boundary history is actually allowed by the
first-return provenance order.

Equivalently, the missing assertion is an exchange closure for boundary words.  Let

```text
gamma = g_1 g_2 ... g_t
```

be the ordered first-return word from the common anchored prefix to the star containing the slip edge, and
suppose `h` is the transported sheet-character edge at the endpoint of `gamma`.  If, for each suffix
position, the current translate of `h` and the preceding generator `g_i` span an actual filled flat
first-return square, then `h` can be commuted one step earlier.  Inducting on `i=t,t-1,...,1` moves `h`
to the common prefix.  At that point `h gamma` is an ordered first-return word with `h` as its first new
boundary edge, so the tree sheet is a first-return child carrier.  Therefore every failure of
star-to-boundary normality is precisely a place where a statically filled flat commutation square is not
available as an ordered first-return exchange square.  The first such place is the remaining
provenance/cubicality atom.

Thus the final statement can be made completely categorical:

```text
rank-one boundary exchange closure:
  every filled flat rank-one commutation square encountered while moving
  a sheet-character edge backward along a first-return word
  is an exchange square in the first-return category,
  unless it exposes a local exit or a 0001 / square-transverse branch.
```

This is equivalent to locally star-flat slip-edge provenance.  It is also the exact gap between the
reduced two-chart trace model and the graph-specific proof: the trace model has statically flat squares,
but no reason for those squares to be first-return exchange squares.

The first static-but-not-first-return square has a sharper exposed-edge normal form.  Let `S` be the
earliest filled flat commutation square, with coordinates `h` and `g_i`, that is present in the ambient
repair graph but not admitted as a first-return exchange.  Since the square is statically filled and
flat, the obstruction is not the fourth vertex or a degree interval; it is that one of the two commuting
orders crosses the boundary of the ordered first-return chamber.  Let `ab` be the first boundary edge of
that failed order.  All earlier edges are in the first-return category and all earlier commutation faces
are exchange squares.

If every admissible boundary row is constant on the two sides of `ab`, then the side pair is a bridge
module inside the fixed chamber, and ambient primeness supplies a breaker.  If a breaker has fixed trace
after marking the exchange prefix, Section `40` gives the same-trace/false-clone exit; if its marked
support is clean, marked-add closes it.  Otherwise its first nonconstant coordinate is precisely the
commutation coordinate of `S`, so the breaker is square-transverse.  Thus a genuine failure of
rank-one boundary exchange closure is not a new provenance object.  It is exactly a minimal
square-transverse breaker for the exposed exchange-gate edge `ab`.

In particular the equivalence chain has closed back on itself:

```text
static filled square not first-return
  -> exposed exchange-gate edge
  -> prime breaker of the gate
  -> fixed-trace/clean exit or minimal square-transverse breaker.
```

Therefore the boundary-exchange atom is the cubicality face of transverse-breaker admissibility.  The
only remaining work is again to prove that the first dirty failed row of this minimal exchange-gate
breaker strictly reduces support, or else realizes the `0001` branch square.

The exchange-gate breaker has no additional support patterns.  Let `r` be the prime breaker of the
exposed gate edge `ab`, and let `u` be the first dirty failed row when `r` is tested as an exchange
boundary.  If `u` is constant on one sheet side, the failed side is a proper first-return-complete child
carrier after the already exchanged prefix, so support decreases.  If `u` crosses the sheet side in the
opposite orientation, the two cuts form the primitive `2 x 2` circuit; a realized diagonal is the local
exit and the absent diagonal is exactly the `0001` branch square.  The only support-preserving case is
that `u` is parallel to `r` on the sheet carrier and differs only by the hidden package label after the
failed exchange.  But then `u` is another global sheet-character separator for the same primitive
two-sheet cover, and recentering the boundary closure at `u` gives the locally star-flat slip-edge
provenance atom again.

Thus exchange-gate transverse-breaker admissibility has the exact terminal form

```text
first dirty exchange-gate row
  -> proper child carrier / primitive circuit / branch square,
  or gate-parallel sheet-character bounce.
```

The gate-parallel bounce is the same two-chart renaming obstruction.  No new degree, Hall, or cubical
invariant remains after this reduction.

The order-two nature of the bounce also gives no descent.  The sheet flip squared is the identity on the
visible carrier, but the corresponding slack set is

```text
R^0 disjointunion R^1 = R,
```

the original q-marker support.  In the primitive dyadic case each sheet has residue `q/2 mod q`, so a
single flip is not a q-marker and two flips only reconstruct the old complete marker.  Thus finite order
of the local renaming is invisible to support decrease.  The irreducible gate-parallel normal form is an
idempotent one-edge boundary-normality failure:

```text
one primitive slip edge e,
one global sheet-character h,
all h-commutations filled and flat,
h^2 trivial on visible data,
but h not admitted as a first-return boundary edge.
```

This is the smallest current statement of the gap.  Any proof must add one genuinely ordered fact: the
idempotent hidden-sheet flip either occurs in the first-return boundary category or is witnessed by a
branch square.

There is no higher-rank deck group left inside this atom.  Suppose two nontrivial sheet-character
separators `h_1,h_2` survive on the same primitive carrier and both commute flatly with the boundary
history.  If they induce different sheet partitions, then `h_1 h_2` is a base-boundary cut on some
visible carrier row; after promotion this is a proper child carrier, and without promotion its first gate
failure is the exchange-gate square-transverse breaker above.  If they induce the same sheet partition,
they agree on the carrier and differ only by fixed-trace data, so Section `40` identifies them or gives a
false-clone exit.  Hence the ambient deck normalizer of the irreducible carrier has rank one:

```text
N_ambient(B_*) / B_* = {1, h}.
```

The final obstruction is therefore not a finite-holonomy or multi-sheet problem.  It is a central
extension problem for the first-return boundary category: the unique nontrivial central involution `h`
normalizes the boundary closure and is locally represented by filled flat exchange faces, but is not a
morphism of the boundary category itself.  Equivalently, the missing theorem is **rank-one boundary
category fullness**:

```text
every primitive central deck involution of the ambient rank-one repair normalizer
that is locally represented by filled flat exchange squares
belongs to the first-return boundary category,
unless some local representative is a branch square.
```

This fullness statement is exactly the previous star-to-boundary normality phrased without choices of
tree gauge or exchange word.

The fullness atom is not a formal consequence of the reduced boundary-category axioms.  There is an
index-two model: take a primitive carrier with two sheets `R^0,R^1`, let the first-return boundary
category act trivially on the sheet label and transitively on the visible carrier, and adjoin one central
ambient involution `h` swapping the sheets.  Declare every square involving `h` and a boundary generator
to be statically filled and flat.  Then all local commutation, interval, chamber, and scalar holonomy
tests pass; the quotient normalizer is exactly `{1,h}`; each sheet has residue `q/2 mod q`; and `h` is
not a first-return morphism by construction.  This is not asserted as a graph counterexample.  It shows
that the missing proof must use the actual construction of first-return boundaries, not only the abstract
boundary category with its filled flat faces.

Thus the rank-one boundary-category fullness theorem is the precise remaining graph-specific input:
the real first-return category must be full in this index-two ambient normalizer, or the attempted
central involution must be witnessed by a branch square.

The same atom is visible from the lower-modulus side.  In the primitive dyadic normal form

```text
|R^0|=|R^1|=q/2 mod q,
```

each sheet is `0 mod q/2`.  Hence, if either sheet is first-return-complete as a child carrier, the
lower-modulus induction / raw short-packet package closes it before the original q-marker can survive.
So an irreducible central-involution survivor must keep both sheets outside the lower first-return
carrier family as well.  Attempt to insert the sheet edge `h` at the beginning of the first-return word
`gamma`.  Because `h` commutes flatly with every boundary generator, every later obstruction can be
commuted to an earlier prefix.  The earliest invalid prefix is therefore either:

```text
old-defect / inserted-root / filler / fixed-trace / clean,     hence local;
dirty square-transverse,                                      hence branch;
or h itself is not recognized as a first-return child edge.
```

Thus modulus lowering contributes no extra arithmetic obstruction.  It restates boundary-category
fullness as **prefix-insertion fullness**: a central sheet edge that commutes through the first-return
word and whose sheet is a lower-modulus zero carrier must itself be a first-return child edge, unless the
first invalid prefix is one of the local/branch exits above.

After this prefix insertion, the boundary history can be erased.  If every commutation of `h` past
`gamma` is a first-return exchange square, the only remaining possible failure is at the common anchored
prefix itself.  At that prefix all previously admitted boundary rows are sheet-constant, and the ambient
separator `h` cuts the primitive lower-modulus child

```text
R^0,        |R^0|=0 mod q/2,        |R^0|!=0 mod q.
```

If `h` is admitted, lower-modulus support decrease closes.  If `h` is not admitted and no branch square
starts at the prefix, then the root prefix has an ambient separator of a primitive child carrier that is
invisible to every first-return boundary row.  This is the **root-edge fullness** atom:

```text
root-edge fullness:
  at an anchored prefix, an ambient separator of a primitive q/2-child carrier
  is a first-return child edge, or produces a local/branch exit.
```

Thus all non-root history, holonomy, exchange, and star-cubicality have been removed.  What remains is the
original ambient-to-boundary promotion problem in its root primitive child form.

Root-edge fullness is exactly a reseating statement.  If the first-return construction may be restarted
with the ambient separator `h` placed first, then `h` is a first-return child edge by definition, the
sheet `R^0` is a lower-modulus complete carrier, and the dyadic descent closes.  Therefore an
irreducible root-edge failure is not a local obstruction at the prefix; it is the failure of
first-return **reseating invariance**:

```text
root reseating invariance:
  an ambient separator of a primitive child carrier can be chosen
  as the first boundary of an equivalent terminal descent,
  unless that reseating changes the anchored prefix through a local/branch exit.
```

This is the graph-specific content still absent from the proof.  The abstract index-two model forbids
reseating by decree; the real graph proof must show that terminal descent can be reseated at such a
central separator, or that the attempt to reseat exposes the branch square.

Root reseating has two logically separate parts:

```text
profile realization:      some ambient row has the primitive child cut;
selector admissibility:   such a row may be used as the first-return boundary.
```

In the present atom profile realization is already supplied by the ambient separator `h`.  The missing
part is selector admissibility.  The aggregate carry identity cannot supply it: it records only the
multiplicities of complement-paired tail profiles, and remains unchanged if the first-return selector is
declared to ignore the sheet label.  Thus the root atom is not "find a row with the child cut"; it is:

```text
root selector fullness:
  every realized ambient row with the primitive child cut is selectable
  as an initial first-return boundary,
  unless selecting it exposes an old-defect / root-edge / branch-square exit.
```

This is equivalent to root reseating invariance.  It is the rooted version of the abstract
provenance-selection no-go above: ambient profile realization plus primeness does not imply selector
admissibility without a graph-specific first-return argument.

There is one more reduction inside selector admissibility.  Let `P` denote the anchored prefix after all
commuting boundary history has been erased, and let `E(P)` be the set of rows that are eligible to start a
terminal first-return descent from `P`.  If eligibility is prefix-local, i.e. determined only by the trace
of the candidate row on the anchored prefix together with the already closed old-defect, inserted-root,
filler, fixed-trace, clean, and square-transverse tests, then the ambient separator `h` must lie in
`E(P)`: it is central on the erased boundary category, cuts the primitive child, and every noncentral
failure has already been classified as a local or branch exit.  Therefore a root selector counterexample
has the sharper form

```text
hidden selector memory:
  h passes every prefix-local eligibility test at the anchored prefix,
  but h is rejected because it was not present in the original terminal word.
```

Thus root reseating invariance is equivalent to a memory-free selector theorem:

```text
memory-free selector theorem:
  after all boundary history commutes flatly past a candidate child edge,
  first-return eligibility depends only on the final anchored prefix;
  any dependence on the erased history yields a nonflat exchange square
  or a previously closed local exit.
```

This is strictly sharper than the previous promotion theorem.  It no longer asks to promote an arbitrary
ambient splitter through a live word; the word has already been commuted away.  It asks only to rule out a
selector whose only obstruction is historical provenance with no remaining local trace.

Under a global restart-minimal choice of terminal descent, hidden selector memory would be impossible.
Indeed, choose the counterexample and then the terminal descent lexicographically over all admissible
restarts from the same anchored prefix.  If the `h`-started descent is admissible and has no local or
branch defect, then it is a competing terminal descent whose first boundary realizes the primitive child
cut.  It is either equivalent to the original descent, in which case `h` is selected and the lower-modulus
child closes, or it first diverges from the original descent at an exchange square.  The first divergence
is nonflat, not filled, or static-but-not-first-return; these are exactly the exchange-gate / branch /
local exits already removed.  Therefore a genuine survivor cannot be hidden memory alone.  It must fail
the premise:

```text
restart admissibility:
  the ambient child separator h, placed first, is itself an admissible
  terminal descent step in the same anchored-prefix comparison class.
```

Thus the root atom has been compressed once more.  Either terminal descents are globally restartable, and
root selector fullness follows by minimality, or the remaining obstruction is a restart-admissibility
failure: starting with `h` changes the terminal host comparison class before any local/branch defect is
visible.

The restart-admissibility failure can be named arithmetically.  A terminal descent step is tested by a
finite list of residue functions: the current ambient degree residue, the dropped-tail residue, and the
residues against the separated control blocks used by the exchange template.  Let

```text
Delta_h(P)
```

be the vector of changes in these residues when the anchored prefix `P` is restarted with `h` first.
If `Delta_h(P)=0`, then `h` lies in the same comparison class and the restart-minimal argument admits it.
If `Delta_h(P) != 0`, choose the first nonzero coordinate in the ordered control list.  A nonzero ambient
degree coordinate is an old-defect or inserted-root failure; a nonzero dropped-tail coordinate is a
fixed-trace/clean boundary failure; and a nonzero separated-control coordinate is precisely the first
nonflat exchange square, hence the square-transverse branch.  All three exits have already been removed
from the irreducible endpoint.

Consequently a restart-admissibility survivor would require an unrecorded comparison residue:

```text
hidden restart residue:
  Delta_h vanishes on every residue function used by the terminal template,
  but the h-started descent is still declared outside the comparison class.
```

So the remaining assertion is no longer a geometric promotion statement.  It is residue completeness for
terminal descent comparisons: the finite residue list used to define a terminal step must contain every
invariant that can obstruct restarting at a central child separator.

Equivalently, saturate the first-return boundary family at a prefix `P` by declaring

```text
Sat(P) = { rows z : Delta_z(P)=0 and z passes the local prefix tests }.
```

All previous ordered-row arguments are monotone under this saturation: adding a row to the admissible
family can only create an earlier local exit, an earlier complete child marker, or the desired selected
boundary.  Hence if every row of `Sat(P)` has an actual singleton exchange square, then hidden restart
residue is impossible by definition of `Sat(P)`, and the root selector atom closes.

Thus a hidden restart residue is the same as a residue-zero non-square row:

```text
residue-zero non-square row:
  Delta_z(P)=0 and all prefix-local tests pass,
  but z is not realized by an exchange square in the first-return state complex.
```

The first obstruction to realizing such a square is again local.  If one of the four singleton corners is
missing, the missing-corner test is an inserted-root or filler exit.  If all corners exist but the two
orders give different terminal residues, then the first differing residue coordinate is an
old-defect/fixed-trace/clean exit.  If all residues agree but the square is not filled, that is precisely
the square-transverse branch.  Therefore the only residue-zero non-square row that can survive is a
pure provenance gap: the square is present in the static residue table and has all four corners, but is
not admitted as a first-return square for no residue-visible reason.

This renames the final atom one last time:

```text
provenance-saturation:
  the first-return state complex is saturated by residue-zero singleton squares;
  any residue-zero static square not admitted to the complex exposes a local or branch exit.
```

Provenance-saturation would prove root selector fullness, hence root reseating, hence the reduced form of
Theorem G.  At this point the gap is exactly provenance-saturation at the anchored prefix.

There is a clean way to make this atom formal.  Replace the path-only first-return family at each prefix
by its residue-saturated exchange complex:

```text
FR^sat(P) =
  the smallest family containing the original first-return edges
  and every singleton exchange square whose four corners exist,
  whose two orders have the same terminal-template residue vector,
  and whose boundary rows pass the prefix-local tests.
```

Every reduction above is monotone under the replacement `FR(P) subseteq FR^sat(P)`.  The local exits do
not disappear; adding edges can only make their first occurrence earlier.  A complete child marker remains
complete because the shared-slack set is defined by the four corners of the exchange square, not by the
chosen history.  Minimality remains valid because any support decrease found in the saturated complex is
an actual graph exchange on actual singleton corners.  Therefore, if the proof is allowed to choose the
terminal descent inside `FR^sat` rather than inside a fixed unsaturated first-return path, provenance
saturation is automatic and the root selector atom closes.

Thus the current proof obligation has become a compatibility audit:

```text
saturation compatibility:
  the q-marker / terminal-host construction may be run in FR^sat
  without changing the meaning of "first-return-complete" support.
```

If saturation compatibility holds, the anchored-prefix provenance atom is closed.  If it fails, the
failure itself must identify a singleton square whose four graph corners exist and whose residues agree
but whose shared-slack set is not accepted as first-return-complete; that is now the only remaining
place where Theorem G can hide.

The compatibility audit separates a definitional issue from a mathematical one.  Define a support `S` to
be exchange-complete at `P` if it is the full shared-slack set of an actual singleton square based at `P`
whose four corners exist and whose two orders have the same terminal-template residue vector.  With this
definition, saturation compatibility is immediate: every `FR^sat`-complete support is an exchange-complete
support, and every exchange-complete support has exactly the data used in the low-set update.  The
q-marker congruence, the proper-support minimality contradiction, and Lemma 9.1 depend only on that
four-corner exchange data, not on the historical path by which the square was found.

Thus no new graph-theoretic obstruction appears when passing from path-only first returns to `FR^sat`.
The only possible objection is terminological:

```text
path-saturation equivalence:
  every exchange-complete support in FR^sat may be treated as first-return-complete
  for the terminal-host descent, or else it yields a local/branch exit.
```

If "first-return-complete" is defined intrinsically by exchange-completeness, the root atom closes.  If it
is defined extrinsically by membership in one previously chosen path, the old abstract
provenance-selection no-go reappears as a naming obstruction rather than a residue obstruction.  Hence the
mathematical content left in the unsaturated formulation is exactly path-saturation equivalence: prove
that the historical path convention is replaceable by the intrinsic exchange-complete convention.

This gives a proved saturated version of the gap theorem.

### Proposition 8.1: canonical saturated provenance/support-decrease

From this point on, interpret "ordered first-return boundary" and "first-return-complete" in the
canonical residue-saturated exchange complex `FR^sat`, with support minimized first and a fixed
lexicographic tie-break afterward.  In a fully skew q-marker endpoint, every ambient high-error splitter
of a protected packet has one of the following outcomes:

1. it is promoted to an ordered saturated boundary row;
2. it gives a local or branch regularizing exit;
3. its first packet-internal failed row carries a complete smaller q-marker.

### Proof

Let `z` be an ambient high-error splitter at prefix `P`.  Run the prefix-local tests in the fixed order:
old defects, inserted roots, filler rows, fixed-trace rows, clean rows, and square-transverse rows.  If
one of these tests fails, the corresponding closure already gives outcome 2.

Assume all prefix-local tests pass.  Compute the terminal-template residue vector `Delta_z(P)`.  If the
first nonzero coordinate is an ambient degree coordinate, the failure is an old-defect or inserted-root
exit.  If it is a dropped-tail coordinate, the failure is fixed-trace or clean.  If it is a separated
control coordinate, the first disagreement is a nonflat exchange square, hence the square-transverse
branch.  These are again outcome 2.

Therefore `Delta_z(P)=0`.  By definition of `FR^sat`, the singleton exchange square generated by `z` is an
ordered saturated boundary square, so `z` is promoted and outcome 1 holds unless the first later failure
is packet-internal.  In the packet-internal case, the square has all four graph corners and equal terminal
residues.  The full failure set is therefore exchange-complete.  The low-set update gives its size
`0 mod q`; if it is proper, minimality gives outcome 3, and if it is not proper we have returned to the
same q-marker support with no support decrease, the root selector atom already disposed of by the
saturation step.  Thus the saturated theorem holds.

This proves the canonical saturated analogue of Theorem G.

### Theorem 8.2: saturated descent is sufficient

The q-marker exclusion and terminal-regularization arguments below remain valid when "ordered first-return
boundary" and "first-return-complete" are interpreted in the canonical saturated exchange complex
`FR^sat`.  Consequently Proposition 8.1 is sufficient for the terminal proof.

### Proof

The final theorem is a statement about the original graph, not about a chosen provenance convention.
Changing the terminal descent convention is legitimate provided every boundary object used by the proof is
an actual graph object and every descent contradiction still decreases an actual support.

The saturated convention has exactly these properties.  An added `FR^sat` square is admitted only when its
four singleton graph corners exist, its two orders have the same terminal-template residue vector, and all
prefix-local tests pass.  Therefore an `FR^sat` boundary row has the same data used by the local catalogues
and by Lemma 9.1: adjacency to the promoted row, the marked quartet, the protected packet, and the
terminal residue vector.  No downstream argument uses the historical path by which the row was first
found.

The low-set update is also unchanged.  For a packet-internal saturated square, the failed set is the full
shared-slack set of an actual marked two-class quartet.  Equal terminal residues give the same congruence
as in the path-only proof, so if that set is proper it is a genuine smaller q-marker support in the
original graph.  Since the host is finite, choosing a survivor minimal with respect to saturated complete
supports makes this descent well-founded.

Thus any terminal q-marker survivor may be minimized in the saturated convention.  Proposition 8.1 applies
to that survivor.  Its local or branch exits are actual graph exits; its complete smaller marker outcome
contradicts saturated minimality; and its promoted boundary-row outcome is handled by Lemma 9.1.  Hence
the terminal proof only needs the saturated theorem, not a comparison with an extrinsically chosen
path-only first-return path.

To recover the original path-only Theorem G as a separate statement, one would still have to compare the
canonical saturated path with the actual minimal first-return path used by the historical terminal descent:

```text
path-saturation equivalence:
  the minimal path-only first-return path is homotopic, through residue-zero
  exchange squares and local/branch exits, to the canonical saturated path.
```

Arbitrary extrinsic paths need not satisfy this: one can choose a path that avoids a saturated square.
The desired path-only theorem would have to show that such an avoiding path is not minimal in the
first-return descent once the support and lexicographic tie-breaks are imposed.

### Open target 8.3: path-saturation equivalence

For the support-minimal, lexicographically first terminal descent path, the path-only first-return family
and the canonical saturated family have the same complete supports, up to local or branch exits.

### Attempted reduction

Suppose not, and choose a counterexample with minimal terminal support and then a shortest pair
`(gamma, gamma^sat)` of path-only and saturated first-return paths from the same anchored prefix to the
same terminal comparison class that are not related by residue-zero exchange squares and local/branch
exits.  Their concatenation gives a shortest nontrivial loop `L` in the saturated exchange complex after
all local and branch exits are removed.

The loop `L` has no repeated state and no chord; otherwise it splits into shorter comparison loops, one of
which is still nontrivial.  It also has no consecutive independent singleton moves with equal
terminal-template residue vector: the four corners of such a pair form, by definition, a residue-zero
square in `FR^sat`, and the loop can be shortened across that square.

Therefore each consecutive pair on `L` has one of three defects.  A missing corner is an inserted-root or
filler exit.  A first residue disagreement is old-defect, fixed-trace, clean, or separated-control
nonflatness, hence a local or square-transverse exit.  These are excluded by the construction of `L`.
The only remaining possibility is active-coordinate dependence: every turn of `L` is a rank-one package
change on the same anonymous binary coordinate orbit.

The active carrier of `L` is omni-saturated in the sense of the saturation argument above.  Indeed, let
`C` be the set of active coordinate states visited by `L`, and let `A(C)` be the cycle graph whose edges
are the consecutive package-change turns of `L`.  Suppose an outside row `z` is nonconstant on `C` and
one fiber of `z|_C` contains an edge of `A(C)`.  Restrict the two comparison paths to that fiber and keep
the first edge on which the restricted paths disagree.  If the restricted paths still have different
complete supports, this is a path-saturation counterexample on smaller support, contradicting the choice
of `L`.  If they do not, the first re-entry to the other `z`-fiber supplies a four-corner exchange square
with the same terminal-template residue vector; by definition this is an `FR^sat` square, hence a chord of
`L`, contradicting chordlessness.  Thus every outside row is either constant on `C` or separates every
edge of `A(C)`.

Now apply this dichotomy to a connected component `H` of `A(C)`.  A row that separates every edge of `H`
is a proper two-coloring of `H`.  If `H` is an odd cycle, no such row exists, so every outside row is
constant on `H`; then `H` is an admissible module, forbidden by primeness except for a local exit.  If
`H` is an even cycle of length greater than two, every separating row is one of the two bipartition
colorings, so vertices in the same bipartition class have identical outside trace.  Any internal row
distinguishing such vertices is a fixed-trace same-trace/false-clone local exit; with those exits removed,
each bipartition class is an ambient module of size greater than one, again impossible in a prime
irreducible carrier.  Hence an irreducible saturated comparison loop has no active component except
`K_2`.

Now take the shortest such rank-one loop.  Fixed-trace, unary, and false-clone kernels have already been
quotiented out, so if an admissible row distinguishes a proper suborbit, the first distinguishing edge is
a smaller one-corner package failure, contrary to minimality.  If no admissible row distinguishes the
orbit, then the orbit is an admissible module.  Ambient primeness supplies a breaker; if the breaker is
not prefix-local, it is one of the local exits above, while if it is prefix-local and residue-zero then it
is an `FR^sat` boundary and gives a chord of `L`.  Thus the module case is impossible.

The remaining rank-one loop is the two-state package transposition.  But a two-state transposition has
exactly four singleton corners and equal terminal-template residues; it is one of the residue-zero
exchange squares used to define `FR^sat`.  Hence it is filled and cannot be a nontrivial loop.  If every
shortest comparison loop could be reduced to this case, the final contradiction would prove
path-saturation equivalence.

This reduction is not yet a proof of Open target 8.3.  The unjustified step is the collapse from an arbitrary shortest
saturated loop to the rank-one package-transposition loop: the argument assumes that every longer flat
loop has a chord, an admissible-module splitter, or a local/branch exit.  That is exactly the
path-saturation equivalence still to be proved.  Therefore Proposition 8.1 proves only the canonical
`FR^sat` analogue of Theorem G, which is enough for the saturated descent by Theorem 8.2; the original
path-only Theorem G remains open at this comparison.

Nor does finite order of the commutator give a descent.  Let `K` be a shortest nontrivial orbit of the
package commutator on anonymous binary coordinates.  If an admissible row distinguishes a proper suborbit
of `K`, the first edge of the orbit where that row changes is a smaller pair-status failure.  If no
admissible row distinguishes any proper suborbit, then `K` is an admissible module.  Ambient primeness
supplies a splitter of `K`, but a promoted splitter is exactly support decrease and a non-promoted splitter
is exactly admissible-module primeness failure.  Thus the commutator-orbit argument only repackages the
same theorem.  At the reduced trace level, a `q`-cycle of equal-residue anonymous coordinates with all
admissible rows constant and with the two successor transports acting by noncommuting partial rotations
satisfies the scalar, parity, chamber, and first-wall constraints while producing no proper realized
carrier.  The missing input is again graph-specific promotion of one commutator boundary to a
first-return-complete side.

This is a flat-connection formulation of the endpoint.  Regard each peeled package as a coordinate chart
for raw discrepancy rows, and each admissible single-shadow transport as a partial transition map between
charts.  If the repair/chamber graph were simply connected after the closed local exits are removed, and
if every elementary square had trivial package curvature

```text
tau_H tau_J tau_H^(-1) tau_J^(-1)=1
```

on the active binary coordinates, then all first-return transports would have path-independent raw
coordinates.  Pair-status would be globally constant on the median fiber, the mixed rows `0101` and
`0011` would live in one raw discrepancy space, and the two-fiber overlap theorem would follow.  Thus a
flat simply connected repair connection would prove Theorem G.

The two hypotheses are exactly the old blockers.  A nonfilled elementary face is the repair-fiber
cubicality / square-representation failure from the `host-opppair123` route; a filled face with nontrivial
curvature is the positive-AND `0001` square; and a flat connection on a nontrivial loop is the anonymous
package-monodromy orbit above, whose first ambient breaker is admissible-module primeness.  Hence the
connection language gives no fourth branch:

```text
nonfilled face       -> square-transverse breaker,
curved face          -> shared-slack q-marker,
flat nontrivial loop -> admissible-module primeness / breaker promotion.
```

This is useful because it identifies the exact non-circular strengthening that would finish the
common-frame problem: prove local simple connectivity of the first-return repair complex after
square-transverse breakers are routed, and prove zero curvature on every filled square by the
same-candidate interval calculus plus same-package witness persistence.  Each failure is already one of
the named host endpoints, so the flat-connection route is a clean equivalence rather than a new proof.

There is no hidden higher-polygon obstruction inside the flat loop case.  Choose a shortest flat loop with
nontrivial package monodromy.  It is chordless, because a common-package chord splits it into shorter
loops, and a proper subloop with nontrivial monodromy contradicts shortestness while two trivial subloops
make the original loop trivial.  Saturate the active carrier against every outside row that preserves one
edge of the loop.  If a nonconstant outside row preserves an edge on one side of its cut, that side is a
smaller carrier and contradicts saturation.  Thus every remaining outside row either is constant on the
loop carrier or separates every active edge.  An odd active cycle then has no proper separating row and is
an admissible module; an even active cycle of length greater than two has two bipartition classes that are
modules unless a local same-trace breaker exits.  Hence the only irreducible flat monodromy loop after
saturation is the two-point active carrier.  In the package language this is the adjacent dirty turn:
opposite signs give the balanced `{0101,0011}` flip, and same signs give the singleton-isolator
package-change edge.  Therefore local simple connectivity fails, in the final quotient, only as the same
single-turn common-frame gluing problem.

This also eliminates an independent ternary endpoint.  Take three consecutive dirty rows over the final
active pair.  If two have opposite signs and lie in one peeled package, they form the raw zero packet
`(e_x-e_y)+(e_y-e_x)` and the short-packet catalogue closes the turn.  If two have the same sign and lie
in one residual fixed frame, they are same-trace or shifted-twin after marking the active pair, and the
local catalogue closes.  Hence a surviving ternary configuration must change package on every adjacent
pair.  The three package changes form either a flat monodromy triangle, already collapsed by the
saturated-loop argument to a two-point carrier, or a curved face whose first missing corner is the
positive `0001` row.  Thus the ternary silent-edge/one-corner-lift atom has no residual third-order
content after saturation; its first failure is again the adjacent package-change edge.

The same warning applies to fixed-square opposite-defect rigidity.  The raw short-packet theorem
controls nonzero raw relations of total mass `<q`; it does not say that a fixed anchored square has at
most one local completer.  If two repaired opposite defects `p,p'` both complete the same frozen square,
then they are twins over the frozen square frame.  In a prime shell there is a breaker `r` with
different adjacency to `p` and `p'`.  If `r` has fixed residual trace after marking one square side, the
same-trace / false-clone catalogue closes.  The only remaining case is again square-transverse: the
first coordinate on which `r` changes is the repaired square coordinate itself.  Therefore fixed-square
opposite-defect uniqueness is downstream of the same transverse-breaker admissibility theorem, not a
consequence of short-packet algebra alone.

Consequently the support-local fourth-corner route is conditional.  With one candidate/witness fixed,
the additive interval lemma fills the fourth corner: every affected row has coefficients in
`{0}`, `{0,1}`, or `{-1,0}`, and the two-term face tests force the full sum to remain in the allowed
interval.  A genuine fourth-corner failure must therefore switch candidate or witness.  The direct
transverse-square gate then reduces the failure to double same-sign saturation of a dirty slack row.
If the two saturated repairs coalesce after marking that row, the same-trace catalogue closes; if the
marked support is clean, the marked-add catalogue closes.  The residual dirty case is again the
budget-one mixed-trace breaker / skew-ladder endpoint.

Thus the conditional implication is sound:

```text
failed-row acyclicity + transverse-breaker routing
  => support-local fourth-corner filling
  => silent-edge exclusion, outgoing no-split, and pair-chamber separation.
```

But the implication is not a proof of its hypotheses.  The three host frontiers all factor through the
same adjacent-slice admissibility problem: dirty failed rows must either coalesce into a fixed frame or
strictly reduce support.  The q-marker carrier is exactly the case where neither has been proved.

The common-shadow formulation gives the same endpoint in fixed-frame language.  Over the forced visible
median point, let `Sh_H` and `Sh_J` be the fixed-frame shadow sets for the two successor transports.
The desired theorem is

```text
Sh_H cap Sh_J != emptyset.
```

If one shadow is empty, this is the one-corner ambient-to-fixed lift problem.  If both shadows are
nonempty and disjoint, take a closest hidden-coordinate path between them.  Predecessor-side boundaries
shorten the bad edge or fall to the already closed strip-transfer cases; a successor boundary that
coalesces with the localized witness falls to the same-trace / false-clone catalogue.  The only
irreducible separated case is again the successor-side `0001` square.  Thus the two-shadow theorem,
one-corner lift, binary pair-status constancy, and adjacent-slice admissibility are the same endpoint
after the closed predecessor and coalesced cases have been removed.

If the shadow sets were known to be gated convex subsets of the hidden median fiber, the closest-point
argument would close this: the first boundary edge between two disjoint shadows would be a gate edge,
and the first-return square would either shorten or coalesce.  But gatedness is not supplied by the
current local theorems.  The existing route to gatedness passes through silent-edge exclusion and
support-local fourth-corner filling, both of which are consequences of the same adjacent-slice
admissibility being sought.  Thus convex Helly is a valid sufficient package theorem, not an independent
proof.

The support-local fourth-corner route has no hidden degree-theoretic quartic term.  If one fixed
candidate/witness certifies all three exposed faces of a four-corner cube, each affected degree row is
an additive sum of coefficients in one admissible interval `{0}`, `{0,1}`, or `{-1,0}`; the two-face
tests forbid two coefficients with the same forbidden sign, so every larger partial sum stays in the
same interval.  Hence a genuine fourth-corner failure must switch candidates between faces.  The
candidate-switching obstruction is exactly the non-gated shadow-packet problem: pairwise face overlaps
exist, but the three witness packets may have no common point.  A direct transverse gate theorem would
close it, and its fixed-candidate failure is again precisely double same-sign shared-slack saturation.
Without such a gate theorem, Helly is false in the abstract: three witness packets can have pairwise
overlaps `{a,b}`, `{b,c}`, `{c,a}` and empty triple intersection.  The graph-specific content is exactly
to rule out this candidate-switching cycle by proving that nearest-point transport between adjacent
faces is gated, or else to convert the first ungated transverse square into the shared-slack marker.

The gate theorem has an exact square form.  For a localized witness packet `Omega` in the hidden median
fiber, nearest-point gate compatibility across one transverse square is the implication

```text
00, 10, 01 in Omega  =>  11 in Omega.
```

If this implication holds for every localized packet, the median of the pairwise face witnesses lies in
all three packets, and the support-local fourth corner is filled.  If it fails, choose a first square
where `00,10,01` remain in the packet but `11` leaves it.  The indicator of leaving the packet is then
the same positive-AND row `0001`; for a fixed candidate the interval calculation turns it into double
same-sign spending of one slack row, and for candidate switching the first packet that loses gatedness
is the square-transverse breaker.  Thus gated Helly, Boolean/XOR diagonal closure, and repair-fiber
cubicality are all equivalent sufficient packages for the same missing anti-Horn theorem.  None is
available without proving that the first ungated square supplies a complete shared-slack carrier.

Endpoint mass does not close this endpoint.  In a terminal square, each local coordinate row is one of

```text
0000, 0001, 0101, 0011, 0111.
```

The mixed second difference is positive only for `0001` and negative only for `0111`.  A mass identity
can pair positive `0001` rows with negative `0111` rows only after they have been placed in one common
coordinate space.  But producing that common space is exactly the missing fixed-package theorem.  Even
after such a mixed pairing, an `0111` row carries two unary successor increments; those increments must
also be absorbed in the same peeled package, or else they expose the one-corner lift failure again.
Therefore the compensator route is not independent: it is mixed compensator routing plus unary-leak
routing, both of which bottom out at the same successor-side `0001` square.

Equivalently, there are only two possible noncircular ways to use endpoint mass.  The first is a
pointwise sign law:

```text
Delta_H Delta_J p_a <= 0
```

for every first-return pair-status coordinate in the successor-side normalization.  This would exclude
`0001` directly.  The second is paired-compensator routing: every positive `0001` coordinate must be
routed with a negative `0111` coordinate in the same peeled package, with the two unary increments of
the `0111` row cancelled inside that same package.  The first route is exactly the missing
single-witness submodularity theorem; the second route is exactly mixed compensator routing plus
unary-leak routing.  No endpoint-mass identity proves either route before common package equality is
available.

The fixed-witness degree calculus sharpens what the sign law must forbid.  On a normalized repair
square, each retained row has admissible interval `{0}`, `{0,1}`, or `{-1,0}`; two individually
compatible successor repairs fail together only when they spend the same one-unit slack with the same
sign.  Thus a `0001` coordinate is a double same-sign shared-slack row.  But the exact low-set update
does not isolate a single row: the set `R` of retained rows whose one-unit slack is spent twice has
cardinality `0 mod q`.  Therefore a pointwise sign proof can only work if first-return minimality makes
this shared-slack set sub-`q`, or if a proper submarker of it localizes to the closed local catalogue.
Otherwise the selected coordinate is only one visible member of a full q-marker carrier.

The budget-one reanchor version has the same structure.  Same-defect singleton turns are closed: the
old outside vertex and the new outside vertex have identical trace over the middle peeled state, so
prime-shell pressure either gives a same-trace / false-clone local exit or the pair is a module.  Long
reanchor cycles reduce to a defect-switching square: in a shortest cycle, take the first inserted
vertex that is later deleted; just before deletion, the reverse move for the previous edge and the
forward deletion move form a two-defect square.  If that square filled, the deletion would commute
earlier, contradicting first return.  Hence the missing corner is again double same-sign saturation of a
dirty slack row, i.e. successor-side `0001`.

The defect-switching square has no remaining local case-table mystery.  Mixed miss/add defect types are
excluded by the inserted-root tests.  Two miss defects give the marked `C_4` orientation, and two add
defects give the marked `2K_2` orientation; in both cases the retained slack rows have one marked
two-class trace and the inserted pair has the complementary trace.  The local seed is one of the
expected house/path/cycle templates, but the missing step is packaging the whole slack bag into a
fixed-fiber or weighted-quotient object with the correct modular residue.  The low-set correction is
exactly the characteristic vector of the low set, and assuming a completer to supply it would be
circular.  The exact low-set update therefore returns once more to the marked two-class q-marker:
sub-`q`, no-split, and preserved-side branches close, while the fully skew carrier branch remains.

The weighted dyadic carry has no separate valuation-only escape.  In the two-child endpoint, both child
tests may be harmless while the primitive normalized sum is bad because the carry is supported on the
mixed successor corner.  Geometrically the two child boundaries define the same two shadow sets
`Sh_H,Sh_J`; their intersection is exactly the common fixed package needed to add the two child
discrepancies as one raw relation.  Without that package equality, the child discrepancies live in
different coordinate spaces and the raw short-packet theorem cannot see their sum.

The endpoint-mass calculation has the same defect.  A positive `0001` carry row can be paired with a
negative `0111` overlap row only after both are routed into the same peeled package.  Even then, the
`0111` row contributes two unary successor increments, so a full compensator theorem must also absorb
those unary leaks.  If either unary leak is outside the package, it is exactly the one-corner
ambient-to-fixed lift failure; after marking it, coalesced cases are local, clean cases are in the
marked-add catalogue, and the dirty survivor is the same budget-one reanchor breaker.  Thus mixed
compensator routing and unary-leak routing are not two independent final theorems; both fold back to
the anchored first-return `0001` square.

Consequently, the dyadic endpoint is the host endpoint in weighted language:

```text
two-child primitive carry
  -> common-shadow / package equality
  -> successor-side 0001 or one-corner lift
  -> dirty shared-slack q-marker.
```

Any proof of the next dyadic bit must therefore supply the same history-sensitive input as Theorem G:
either a common package for the two successor transports, or a marker-complete support decrease for the
resulting q-marker carrier.  Parity, determinant valuation, and aggregate child identities see only the
separate child tests; they do not see the oriented mixed second difference.

The host-side absorption route reaches the same endpoint.  For a peeled anchored near-regular set `T`,
let `L` be the low set and `B=T\L`.  For an outside vertex `x`, let `epsilon(x)` be its number of wrong
incidences relative to the completer trace: a completer has `epsilon=0`, and a one-defect vertex has
`epsilon=1`.  For any outside set `U`,

```text
e(L,U) - e(B,U) - (|L|-1)|U| = sum_(x in U) (1 - epsilon(x)).
```

Thus completer positivity is pointwise: `c(T)>0` is equivalent to the existence of one outside vertex
with `epsilon=0`, and the weaker one-error strip is just existence of one `epsilon<=1` vertex.  There is
no hidden subset/Hall amplification at this level.

In the irreducible one-defect regime every `epsilon=1` vertex has a unique defect site `d(x) in T`.
If some defect lies off the anchor, the singleton swap preserves anchored near-regularity and reanchors.
Therefore the residual case is anchor-supported: `d(O_1) subseteq w`.  Hall capacity then collapses to
the pointwise bounds

```text
mu(u) = |d^(-1)(u)| <= q-1        for u in w.
```

If an anchor fiber is overloaded, a q-sized same-defect packet gives a local raw relation or a completer;
if all fibers satisfy the bounds, Hall supplies no further information.  The remaining theorem is
compatible-transversal positivity: choose an injective set of one-defect vertices over several anchor
fibers so that the simultaneous reanchor has `c(T_X)>0`.  Singleton reanchors are reversible, so this
compatibility theorem is exactly a higher-face/gating problem in the promotion complex.  Its first
nontrivial failure is the same candidate-switching fourth-corner obstruction above, and its dirty
two-face failure is again double same-sign shared-slack saturation.  Hence host absorption, Hall
capacity, and compatible multi-swap positivity do not bypass the q-marker endpoint; they repackage it.

## 9. Saturated q-marker exclusion

### Lemma 9.1: ordered boundary completeness

Assume an ambient high-error protected-packet splitter has already been promoted to an ordered
first-return boundary row `z`.  If `z` splits a protected packet `P`, then the first packet-internal
failed set is a union of whole sides of the split:

```text
P cap N(z),     P \ N(z),     or     P.
```

In particular, if `P` is proper, this failed set has size `< q`.

### Proof

All vertices of `P` have the same trace to the marked quartet and to every packet other than `P`.
The boundary test can distinguish vertices of `P` only through adjacency to `z`.  Hence the failure
indicator is constant on `P cap N(z)` and constant on `P \ N(z)`.

First failure cannot select a proper nonempty subset of one side, because an omitted and an included
vertex on the same side have identical boundary data.  Therefore the failed set is one whole side or
both whole sides.  In the fully skew endpoint, the protected packets are the `q-2` clique and
compensator components of size `< k(H) < q`; hence the failed set has size `< q`.

### Proposition 9.2: saturated q-marker exclusion

With first-return completeness interpreted in `FR^sat`, no minimal fully skew q-marker survives.

### Proof

Let a fully skew q-marker survivor be chosen minimally among saturated complete supports.  By Proposition
7.1, all static regular selections have been removed and the survivor has product-firewall form.  Ambient
primeness supplies a high-error splitter of a protected packet.

Apply Proposition 8.1 in the saturated convention, justified for the terminal proof by Theorem 8.2.  A
local regularizing exit contradicts survival.  A complete smaller saturated q-marker contradicts
minimality.  If the splitter is promoted to an ordered boundary row, Lemma 9.1 says that the first
packet-internal failed set is a whole side of a proper protected packet.  Hence it is nonempty and has
size `< q`.  The low-set update makes that side a q-marker, so its size must be `0 mod q`, impossible for
a nonempty set of size `< q`.

Thus no fully skew q-marker survives.

### Theorem 9.3: terminal dyadic theorem

Let `q = 2^j > 1`, and choose the terminal host `(U,R)` minimal under the saturated descent convention at
modulus `q`.  Then `rho_R` is constant modulo `q`, and `G` contains a regular induced `q`-set.

### Proof

Suppose `rho_R` is not constant modulo `q`, and let `m` be the first bit at which constancy fails.
Then `tau_m(R,U) != 0`, so `beta_m != 0` by Proposition 4.1.  Corollary 4.2 gives a nonconstant cut.
Lemma 5.1 shows that the first boundary seeing this cut is mixed, and Lemma 5.3 converts that mixed
boundary into a q-marker.

The local closures of Lemmas 6.1, 6.2, and 6.3 remove the no-split, frozen, and one-splitter cases.
The remaining case is fully skew, and Proposition 9.2 excludes it.  This contradiction shows that no bit
fails.  Hence `rho_R` is constant modulo `q`, and Lemma 3.1 gives a regular induced `q`-set.

## 10. Terminal regularization and the global implication

### Lemma 10.1: parity base

Every graph on `n` vertices has a modulus-`2` witness of size at least `n/2`.

### Proof

Use Gallai's parity partition.  Over `F_2`, let `L` be the graph Laplacian and let `d` be the degree
parity vector.  Since `d` annihilates `ker L`, the symmetric-image identity gives a solution

```text
Lx = d.
```

Let `V_0={v:x_v=0}` and `V_1={v:x_v=1}`.  For a vertex in `V_1`, the equation says that the number of
neighbors in `V_1` is even.  For a vertex in `V_0`, subtracting the already controlled neighbors in
`V_1` from the total degree gives that the number of neighbors in `V_0` is even.  Thus both induced
parts are Eulerian, and the larger part has size at least `n/2`.

### Lemma 10.2: terminal regularization landing surface

There is a constant `C` such that, for every dyadic `q = 2^j`, every fixed-modulus witness of size
`q^C q` at modulus `q` contains a regular induced `q`-set.

### Proof

The finite host-iteration reductions convert a fixed-modulus witness of size polynomially larger than
`q` into a bounded control-block terminal host witness of size `q`, at the cost of increasing the fixed
constant `C`.  Choose such a terminal host minimal under the saturated complete-support order.

Theorem 9.3 applies to that saturated terminal host and gives a regular induced `q`-set.  This is only a
terminal regularization statement.  It does not assert the stronger terminal-cascade package in which the
regularizing bucket is itself returned as a capped cascade witness.

### Remark 10.3: terminal-cascade is stronger and not used

At `q=2`, the live terminal-cascade slice is unconditional: the two-vertex terminal bucket is already
regular and the drop-data-to-cascade conversion supplies the exact capped package.  At `q=4`, the current
finite base gives terminal regularization from a bounded host witness at bucket `16`, but not the stronger
terminal-cascade package.  The obstruction is real: a regular set of size at least `4` need not contain an
exact regular `4`-set; there is a seven-vertex graph with a regular `5`-set and no regular `4`-set.

Therefore the `q >= 4` terminal-cascade bridge cannot be recovered by merely tightening the finite
`4 in admissibleBounds 7` route.  The asymptotic argument above lands on terminal regularization instead,
which is the weakest fixed-witness landing surface needed for the final graph theorem.

### Target Lemma 10.4: large-gap positive fixed-witness dyadic lift

Let `q=2^j`, with `0 < j`, and let `m >= 7`.  Assume the residual large-gap/Ramsey-window hypotheses

```text
j * 6 < 2 * (m - 1),
m < 2^(2 * (m - 1) - j * 6),
n < binom(2m - 2, m - 1).
```

The target statement is: if `G` has a fixed-modulus witness of size `q^6 m` modulo `q`, then `G` has a
fixed-modulus witness of size `m` modulo `2q`.

Equivalently, this is the mathematical content of

```text
HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7.
```

### Status

The residual is now split.  The first dyadic bit still needs the separate loss-64
parity-to-mod-4 theorem below.  For `j>=2`, the high-modulus slice is terminal, and the genuinely
small-modulus slice is closed in the saturated exchange convention by Lemmas 10.4e--10.4i.  The only
remaining distinction is external to the dyadic carry: whether one insists on the historical path-only
first-return convention rather than the intrinsic `FR^sat` convention used in the terminal proof.

A tempting shortcut would be a general linear theorem saying that every `N`-vertex graph has an induced
subgraph of size `N/O(Q)` whose degrees are congruent modulo `Q`, but that statement is not available in
the needed form and is too strong for large `Q`: when `Q` exceeds the selected subgraph size it would force
polynomial-size regular induced subgraphs.  The Alon-Friedland-Kalai theorem instead concerns non-induced
`q`-divisible edge subgraphs and regular subgraphs under almost-regular hypotheses, so it does not supply
this fixed-witness lift.

Thus the proof of the higher-bit residual uses the special input that the starting witness is already
degree-congruent modulo `q`, together with the Ramsey-small/large-gap window and saturated
provenance/support-decrease.

### Lemma 10.4a: current sharp residual split

The open residual may be sharpened in two harmless ways.

First, it is enough to prove the stricter large-gap slice

```text
2m < 2^(2 * (m - 1) - 6j).
```

The complementary slice is already ruled out by the central-binomial half-bound used in the formal
Ramsey-window reduction.

Second, the first dyadic bit can be isolated.  If the following parity-to-mod-4 loss-64 lift is proved:

```text
every graph whose induced degrees are congruent modulo 2 contains
a subset of at least a 1/64 fraction of its vertices whose induced degrees
are congruent modulo 4,
```

then every `j=1` instance of Lemma 10.4 is closed, because the input witness has size
`2^6 m = 64m`, and the loss-64 lift returns a mod-4 witness of size at least `m`.

A stronger sufficient first-bit target is the all-zero version:

```text
every graph contains an induced subgraph on at least a 1/64 fraction of its vertices
whose degrees are all 0 modulo 4.
```

This immediately implies the parity-to-mod-4 loss-64 lift, without using the parity-regularity of the
input witness.  It is a useful finite target, but it is still an input here, not a theorem proved by the
terminal q-marker argument.

Consequently the remaining strict residual can be assumed to have `j >= 2`.  In that range the first
live target is `m=10`: if `m <= 7`, then `6j < 2(m-1)` fails for `j >= 2`; if `m=8`, then
`2(m-1)-6j <= 2`, so `2^(2(m-1)-6j) <= 4 < 16 = 2m`; and if `m=9`, then
`2(m-1)-6j <= 4`, so `2^(2(m-1)-6j) <= 16 < 18 = 2m`.  These contradict the strict gap.

### Lemma 10.4b: the high-modulus slice is not residual

In Lemma 10.4, the case

```text
q = 2^j >= m
```

is already closed by the saturated terminal theorem.

Indeed, let `S` be the input fixed-modulus witness, so `|S| >= q^6 m` and `G[S]` has all degrees
congruent modulo `q`.  Since `q^6 m >= q`, choose any `q` vertices `U subseteq S` and put
`R := S \ U`.  Then `(U,R)` is a terminal host at modulus `q`: the whole top set `U union R = S` has
constant degree modulo `q`, and `|U| = q`.  Run the saturated terminal descent from Section 9 on a
minimal such terminal host.  Theorem 9.3 gives a regular induced `q`-set `W`.

Because `q >= m`, this same `W` is already a fixed-modulus witness of card at least `m` modulo `2q`:
all degrees in `G[W]` are equal, hence congruent modulo every modulus.  Thus the strict higher-bit
residual may be sharpened further to

```text
2^j < m.
```

Combined with `j >= 2`, the remaining large-gap problem is therefore the genuinely small-modulus
window

```text
4 <= q = 2^j < m,
2m < 2^(2(m-1)-6j),
n < binom(2m-2,m-1),
HasFixedModulusWitnessOfCard G (q^6 m) q.
```

This reduction is important: the unresolved dyadic lift no longer includes the range where congruence
modulo `q` is already a terminal-size condition.

### Lemma 10.4c: the remaining small-modulus case is not a generic divisible-degree theorem

The remaining window cannot be closed by replacing the input with a generic theorem of the form

```text
every N-vertex graph contains a (2q)-divisible induced subgraph
of size at least N / q^O(1).
```

Such a theorem is false at the scale needed here.  If `q` is allowed to grow and the guaranteed set has
size below `2q`, then "all degrees divisible by `2q`" means "independent".  Taking `N` polynomial in
`q`, a polynomial-loss divisible-degree theorem would force polynomial-size independent sets in arbitrary
graphs, contradicting the usual random-graph/Ramsey obstruction.  Thus the original hypothesis that the
starting set is already `q`-modular is essential.

Nor is the residual just the high-modulus terminal case in disguise.  When

```text
q < m < 2q,
```

a desired modulus-`2q` witness of card at least `m` would have to be an exact regular `m`-set whenever
the witness has exactly `m` vertices, since every internal degree is `<2q`.  The already proved terminal
regularization gives exact regular `q`-sets from terminal `q`-hosts, but it does not by itself enlarge
them to regular `m`-sets.  Therefore the live small-modulus residual must use deleted-part/cascade
structure: one has to keep enough residue information while passing from the large `q`-modular witness to
the final `m`-vertex support.

The precise next target is consequently a **fixed-modulus cascade lift**, not an unstructured induced
divisible-degree selection:

```text
from a q-modular witness of size q^6 m, extract a residue-controlled
cascade whose deleted layers remain silent through the first j bits;
then the beta_m/tau_m argument and saturated q-marker exclusion force
the next bit to vanish on a support of size at least m.
```

This is exactly the information absent from a plain fixed witness and exactly the information carried by
the dropped-part packages in the formal handoff.

### Lemma 10.4d: minimal q-witness descent isolates the missing deletion theorem

There is a useful way to state the remaining fixed-witness obstruction without mentioning the full
cascade language.

Call a nonempty set `D subseteq A` **q-complete for A** if deleting it preserves q-modularity on the
survivor:

```text
G[A] has all degrees congruent modulo q,
G[A \ D] has all degrees congruent modulo q.
```

Equivalently, the external degree from every vertex of `A \ D` into `D` is constant modulo `q`.
If `|A \ D| >= m`, then `D` is a legitimate descent packet for the fixed-witness problem.

Starting with the input q-modular witness `S`, repeatedly delete q-complete packets while the survivor
has size at least `m`.  Since the graph is finite, this process terminates at a q-modular witness `A`
with `|A| >= m` and with no q-complete packet whose deletion keeps size at least `m`.

Thus the q-shadow of Target Lemma 10.4 follows from the following two q-shadow assertions.  They are useful for
locating the support descent, but they do not yet remember the top dyadic bit; Lemma 10.4e below adds
that missing label.

1. **No large minimal q-witness.**  If a q-modular witness `A` has `|A| >= m + q` and is not already
   2q-modular, then it contains a q-complete packet `D` with

   ```text
   0 < |D| <= |A| - m.
   ```

2. **Near-terminal q-witness closure.**  If `m <= |A| < m + q`, `q < m`, and `G[A]` is q-modular but has
   no q-complete deletion packet preserving size at least `m`, then `G[A]` contains a 2q-modular witness
   of size at least `m`.

The first assertion is exactly the large-marker no-q-jump theorem in deletion language.  The low-set
update supplies q-complete packets only when the failed wall is a complete transported shared-slack set;
an arbitrary lexicographic part of a simultaneous wall is not known to be q-complete.  Therefore the
missing point is not divisibility of `|D|` but completeness/provenance of `D`.

The second assertion is the exact-marker/near-terminal routing layer.  Since `|A|-m<q`, any positive
q-complete packet has size too large to delete while staying above `m`; the argument must instead route
the first internal splitter to a local regularizing exit or to a genuine 2q-modular support.

This formulation is the unlabeled shadow of the cascade obstruction above: the large-gap residual is
closed once every nonzero next-bit obstruction produces either a size-preserving q-complete deletion
packet carrying the correct top-bit update, or a direct 2q-modular witness.

### Lemma 10.4e: the exact lift is affine q-completeness

The previous q-complete language is still missing one datum.  A q-complete deletion preserves
q-modularity, but a dyadic lift must also track which of the two residues above the common q-residue each
vertex has.

Let `A` be q-modular, with `q > 0`, and fix the common residue `d` modulo `q`.  For `v in A`, define the
top-bit label

```text
b_A(v) in F_2 by deg_A(v) == d + q b_A(v) [MOD 2q].
```

This label is well defined up to adding one global constant, so all pairwise differences
`b_A(u)-b_A(v)` are canonical.  If `W subseteq A` and `T := A \ W`, write
`rho_T(v) := |N(v) cap T|` for `v in W`.  Then:

```text
G[W] is 2q-modular
iff
there is c mod 2q such that rho_T(v) == c + q b_A(v) [MOD 2q]
for every v in W.
```

Indeed, for `v in W`,

```text
deg_W(v) = deg_A(v) - rho_T(v).
```

Thus the right-hand condition makes all `deg_W(v)` congruent modulo `2q`; conversely, if all
`deg_W(v)` are congruent, subtracting from `deg_A(v) == d + q b_A(v)` gives the displayed affine form for
`rho_T(v)`.

Modulo `q`, this says exactly that the retained set `W` is q-complete relative to its dropped tail.  The
extra quotient condition is the real dyadic bit:

```text
kappa_A,T(u,v)
  := ((rho_T(u)-rho_T(v)) - (deg_A(u)-deg_A(v))) / q [MOD 2]
   = 0.
```

Equivalently, the terminal beta class is not just `beta_T`; it is the **affine** class

```text
beta_T + b_A in M_2(W) / constants.
```

The desired lift is exactly the vanishing of this affine class.  If it is nonzero, it is a canonical
two-level cut on `W`, just as in the beta discussion in `notes/dyadic-lift-program.md`; the only change is
that the ambient top-bit label `b_A` twists the cut.

The same label explains how a q-complete cascade should be formalized.  If `D subseteq A` is q-complete
and, on `A \ D`,

```text
rho_D(v) == e + q c_D(v) [MOD 2q],
```

then the survivor `A' := A \ D` is q-modular and its top-bit label satisfies

```text
b_A'(v) = b_A(v) - c_D(v)        in F_2,
```

again up to a global constant.  Hence a deletion packet is not merely "complete"; it also transports the
affine label.  A cascade closes the dyadic lift exactly when the transported final label is constant.

So the Lean-facing residual should be stated as an affine selector:

```text
from a q-modular S with |S| >= q^6 m, find W subseteq S with |W| >= m
such that S \ W is affine-complete for (S, b_S) over W.
```

This statement is tautologically equivalent to the fixed-witness dyadic lift, but it exposes the actual
missing mathematics.  The old q-complete deletion theorem is only its modulo-`q` shadow.  The large-gap
proof must show that a nonzero affine-beta cut either gives a label-transporting q-complete descent packet
or routes to one of the already isolated support-local square-breakers (`host-orient115`,
`host-opppair123`, `host-silentedge128`).

### Lemma 10.4f: affine-beta localizes to one oriented pair

The affine obstruction is not a high-dimensional object.  Once the modulo-`q` shadow has been made
constant on a retained set `W`, failure of the `2q` lift is witnessed by a single oriented pair.

Let `A` be q-modular with top-bit label `b_A`, let `W subseteq A`, and put `T := A \ W`.  Assume first
that `W` is q-complete relative to `T`, so `rho_T(u)-rho_T(v)` is divisible by `q` for all `u,v in W`.
Define

```text
lambda_T(u,v)
  := ((rho_T(u)-rho_T(v)) - (deg_A(u)-deg_A(v))) / q   in F_2.
```

Then `G[W]` is `2q`-modular iff `lambda_T(u,v)=0` for every pair `u,v in W`.  Therefore, if the lift
fails, there are `u,v in W` such that

```text
rho_T(u)-rho_T(v) == deg_A(u)-deg_A(v) + q [MOD 2q].
```

Equivalently, the two vertices have the same q-shadow but opposite affine top bit after the tail is
removed.  The global affine beta cut is just the transitive closure of this pair relation: fixing a
basepoint `u_0`, the bad side is

```text
X = {x in W : lambda_T(x,u_0)=1}.
```

So a nonzero affine-beta class always has an oriented-pair chamber `(u,v;T)` whose q-shadow is already
flat and whose only remaining defect is the missing top bit.

This is the exact point where the three host-frontier formulations enter.  In pair language:

1. If the oriented pair can be separated inside the fixed pair chamber, `host-orient115` forbids the
   hidden choice.
2. If the pair is realized on the outgoing anchored square `Q^+`, anchored persistence and no-split give
   the anti-Horn contradiction of `host-opppair123`.
3. If the first changed coordinate is exposed, the anchored one-corner lift on `Q_j(x)` gives the missing
   fourth corner, which is `host-silentedge128`.

Thus the dyadic residual has been reduced from a global tail class to the following local statement:

```text
every q-flat oriented pair chamber with lambda_T=1 either promotes to a
label-transporting q-complete descent packet, or is one of the three
support-local square-breakers above.
```

The first outcome gives a smaller affine cascade state; the other outcomes are exactly the named host
frontiers.  No further dyadic carry type remains after this localization: any two bad pairs in the same
component differ by summing their `lambda` values, so cancelling pairs are already absorbed by the affine
cut `X`, and noncancelling pairs contain a single bad edge across `X`.

### Lemma 10.4g: the oriented-pair obstruction is the two-fiber overlap atom

For an oriented bad pair `(u,v;T)`, the q-shadow says that the two one-sided repairs are separately
available: one can correct the `u` side or the `v` side without changing the lower q-residue.  In the
host notation these two one-sided repair classes are `Omega_10` and `Omega_01`.

The affine equation `lambda_T(u,v)=1` says precisely that these two repairs do not currently share the
same top-bit lift.  If a common witness existed in

```text
Omega_10 cap Omega_01,
```

then the same repair would fill the `0111` corner, the tail would become affine-complete on the pair, and
the contribution to `lambda_T(u,v)` would vanish.  Conversely, if the intersection is empty after all
one-square predecessor, fixed-trace, and persistence exits have been factored off, the reduced table is

```text
0101, 0011 present; 0111 absent.
```

This is exactly the positive-AND / one-corner `0001` atom.  Thus the local dyadic obstruction has the
same normal form as the host-frontier endpoint:

```text
lambda_T(u,v)=1
  <=>  Omega_10 and Omega_01 are nonempty but have no common 0111 witness,
```

up to the already classified local exits.  The proof of the dyadic lift therefore needs no new carry
calculus beyond the host theorem "two one-sided repairs have a filled overlap or yield support decrease."
When that theorem supplies the overlap, `lambda` vanishes; when it supplies support decrease, the
label-transporting q-complete deletion packet is the complete shared-slack side produced by the same
filled-overlap argument.

### Lemma 10.4h: the overlap atom has a two-row split-marker quotient

After the local same-trace, fixed-fiber, marked-add, and one-corner exits are removed, the two-fiber
overlap atom has a forced finite quotient.

Let `R` be the exact q-marker carrier attached to the bad oriented pair.  The large clique part is a
`q-2` marker clique `A`, and the residual marker set is a two-row set `U`.  Any row of `U` with mixed
adjacency to `A` gives a same-trace induced `P_3` over the marked quartet and is already closed by the
Section `40` catalogue.  A row of `U` complete to `A` completes `A` with an inserted root to an induced
`K_q`.  Hence in a residual atom `U` is anticomplete to `A`, and the internal marker graph is exactly

```text
K_(q-2) disjoint_union H,       H in {K_2, 2K_1}.
```

All remaining degree compensation must come from a one-sided compensator/provenance fiber `C` which is
complete to `U` and anticomplete to `A` in the reduced quotient.  The static regular-selection calculation
is then exhaustive.

If `H=K_2`, a regular q-selection using both rows of `U` requires a clique in `C` of size

```text
k(H) = (q-4)/2.
```

This branch is live only for `q >= 8`; for `q=4` the marker quotient itself closes, and for `q=6` one
compensator already gives a regular q-set.

If `H=2K_1`, a regular q-selection using `U` must use exactly one row of `U` and a clique in `C` of size

```text
k(H) = q/2 - 1.
```

This branch is live from `q=6` onward.  Selections avoiding `U` are exactly the proper-divisor bypass:
for some proper divisor `h|q`, there are at least `q/h-1` compensator clique components of size at least
`h`, and choosing `h` vertices from `A` plus `h` from each such component gives a disjoint union of
`q/h` copies of `K_h`.

Therefore, once the divisor bypass is removed, the final overlap atom is:

```text
H in {K_2, 2K_1},
no compensator clique of size k(H),
and no proper-divisor bypass.
```

This static obstruction is real; independent compensator fibers show that the clique is not forced by
residue counts alone.  The missing input is first-return provenance.  The needed theorem is:

```text
if the compensator/provenance fiber has no required clique and no divisor bypass,
then its absence routes to a fixed-fiber Section-40 closure, a proper
marker-complete split, or a packet refinement.
```

In the dyadic descent, the last two outcomes are exactly the desired support decrease: the proper
marker-complete split or packet refinement supplies the label-transporting q-complete deletion packet.
Thus the high-level dyadic residual has now been reduced to a common-package routing theorem for this
two-row split-marker quotient.

### Lemma 10.4i: saturated provenance closes the compensator routing theorem

In the canonical saturated exchange convention of Proposition 8.1, the routing theorem required in
Lemma 10.4h is no longer an extra assumption.

Indeed, after the fixed-fiber `P_3`/Section-`40` exits and the divisor bypasses are removed, every clique
component of the compensator fiber is constant for all currently admissible first-return rows.  Its
vertices have the same marked trace to `A`, to `U`, to the marked quartet, and to the rest of the
compensator packet, except for the internal clique edges of the component itself.  Hence each component,
and every union of consecutive components in the first-return order, is an admissible module in the sense
of Proposition 8.1.

Let `M` be a smallest such compensator module split by an ambient row `z`.  Proposition 8.1 applies to
this ambient high-error splitter.

1. If `z` fails a prefix-local test, the corresponding local/branch exit is precisely the fixed-fiber
   Section-`40`, marked-add, clean, or square-transverse closure allowed in Lemma 10.4h.
2. If `z` is promoted to a saturated boundary row, the first packet-internal failure is the full
   exchange-complete shared-slack side.  The low-set congruence makes that side `0 mod q`; since `M` was
   chosen smallest and every compensator clique has size `<k(H)<q`, the side is a proper marker-complete
   split unless it is empty.  This is the label-transporting q-complete descent packet.
3. If the first packet-internal failed row occurs before promotion, Proposition 8.1 gives a complete
   smaller q-marker directly, again the required packet refinement.

The independent-compensator examples only show that the clique-selection theorem is false without
provenance; they do not survive saturated provenance.  In `FR^sat`, a compensator no-clique/no-divisor
atom must either close locally or produce a proper exchange-complete shared-slack side.  Therefore the
split-marker compensator theorem is proved in the saturated convention.

Combining Lemmas 10.4e--10.4i gives the strict higher-bit small-modulus lift, in the saturated convention:

```text
j >= 2,  q=2^j < m,
HasFixedModulusWitnessOfCard G (q^6 m) q
  => HasFixedModulusWitnessOfCard G m (2q),
```

under the same large-gap/Ramsey-window hypotheses.  The remaining unsaturated issue is not a dyadic carry
issue; it is exactly the path-saturation comparison from Section 8.  Since the graph proof above runs the
terminal descent in `FR^sat`, the higher-bit dyadic residual is closed for the saturated proof pipeline.

### Lemma 10.4j: the remaining first bit is the q=2 affine selector

After Lemma 10.4i, the only dyadic lift input not supplied by the saturated q-marker proof is the first
bit:

```text
parity-regular on 64m vertices  =>  mod-4-regular on m vertices.
```

It has the same affine form as Lemma 10.4e with `q=2`, but no large exact q-marker is available because
the terminal marker size is only `2`.

Let `A` be parity-regular and let `d in {0,1}` be the common parity of `deg_A(v)`.  Define

```text
b_A(v) := (deg_A(v)-d)/2 [MOD 2].
```

For `W subseteq A` and `T=A\W`, the exact criterion is:

```text
G[W] is mod-4-regular
iff
rho_T(v) == c + 2 b_A(v) [MOD 4]  for all v in W.
```

The modulo-`2` shadow of this condition is just parity-regularity of `W`.  Gallai's theorem supplies a
large parity-regular bucket, but it does not control the affine top-bit label `b_A`; this is why the
first bit cannot be discharged by the higher-bit split-marker argument.

Thus the exact remaining theorem is:

```text
First-bit affine selector:
for every parity-regular A, there is W subseteq A with |W| >= |A|/64
such that rho_(A\W)(v) == c + 2 b_A(v) [MOD 4] on W.
```

This is precisely `HasParityToModFourLoss64FixedWitnessLift`.  The stronger all-zero theorem
`HasModFourZeroLossFiveInducedSubgraph` remains only a possible external sufficient input; it should not
be treated as established by the q-marker proof.

### Lemma 10.4k: the first bit is a separate modulus-four selection problem

The affine selector also explains why the first bit cannot be hidden inside the higher-bit q-marker
argument.  For `q=2`, the criterion in Lemma 10.4e becomes

```text
rho_T(v) = c + 2 b_A(v) mod 4.
```

The compensator side used in Lemma 10.4h degenerates: the quotient `K_(q-2) disjoint_union H` has no
large clique marker, and the proper-divisor bypass is empty.  Thus the first bit is exactly the
fixed-loss modulus-four congruent-degree selection target

```text
HasParityToModFourLoss64FixedWitnessLift.
```

One must not replace this target by a uniform theorem saying that every `N`-vertex graph has an induced
`N/(Q+1)`-vertex subgraph with degrees congruent modulo `Q` for arbitrary `Q`: choosing
`Q ~ sqrt(N)` would give regular induced subgraphs of order `sqrt(N)`, far beyond the known general
regular-induced-subgraph bounds.  The usable first-bit input must therefore be either a genuine
modulus-four fixed-loss theorem or a proof that exploits the parity-regular witness.

There is, however, a sharper exact normal form for the first-bit problem.

First reduce to the even case.  If the parity-regular witness has odd common parity, Gallai's
even-even partition gives an induced even-degree bucket of size at least half of the witness.  Thus
`HasParityToModFourLoss64FixedWitnessLift` follows from the following even selector with loss `32`:

```text
every induced even-degree graph E contains W with |W| >= |E|/32
such that all degrees in E[W] are congruent modulo 4.
```

Do not try to linearize the zero/two-residue subcase by fixing an Eulerian orientation of the ambient
even graph.  If `E[W]` is even, it has its own Eulerian orientation, and in that post-selected
orientation the parity of an out-degree is `deg_{E[W]}(v)/2 [MOD 2]`.  But the restriction of a fixed
Eulerian orientation of `E` to `E[W]` need not be Eulerian.  Even when `E[W]` is even, a vertex can have
two selected outgoing edges and no selected incoming edges in the inherited orientation, so inherited
out-parity does not determine `deg_{E[W]}(v)/2 [MOD 2]`.  Thus the modulus-four lift is not reduced to
a one-sided or bidirected parity selector for a fixed orientation.  The reliable formulation is the
intrinsic carry condition below.  The full first-bit theorem also allows all retained degrees to be
`1` or `3 mod 4`, so even a correct zero/two-only criterion would be only a subcase.  The higher-bit
q-marker machinery does not provide this first-bit carry control.

Two nearby external-looking statements are not sufficient.

1. Caro--Krasikov--Roditty zero-sum partition theorems control the **number of edges** in each
   induced part modulo `q`, not each vertex degree modulo `q`; they do not imply the selector above.
2. Random-graph modulo-`q` partition theorems control almost-every `G(n,1/2)`, not arbitrary graphs
   and not the fixed witness already present inside the proof.
3. Scott's residue-modulo-`k` induced-subgraph programme, sharpened by Hunter, gives a genuine
   bipartite theorem: for every fixed `k`, every bipartite graph without isolated vertices has a
   linear induced subgraph with all degrees `1 mod k`.  Ferber--Krivelevich proves the arbitrary-graph
   `k=2` odd-degree conjecture with constant `1/10000`.  These are real nearby inputs, but they do not
   supply an arbitrary-graph mod-`4` congruent-degree selector with the loss-`64` budget: one is
   bipartite-only, and the other freezes only the parity bit.
4. Prescribed-parity extensions of Ferber--Krivelevich still live over `F_2`.  They can prescribe
   `deg_H(v) [MOD 2]` on the retained vertices, but the second bit of an even degree is
   `binom(deg_H(v),2) [MOD 2]`.  After the selected even graph is known, this is the parity of
   half the selected degree; it is not the parity of an inherited ambient out-degree.  This is a
   quadratic/carry condition, not another linear parity label.
5. Alon--Friedland--Kalai, *Regular subgraphs of almost regular graphs*, proves non-induced regular
   subgraphs under almost-regular or density hypotheses via Chevalley--Olson congruence tools.  It is
   therefore not a principal-submatrix theorem and does not control the degrees in `E[W]` after all
   ambient edges among the retained vertices are restored.

The carry can be made completely explicit.  For a proposed retained set `W` and a vertex `v in W`, put

```text
p_W(v) = deg_W(v) [MOD 2],
c_W(v) = binom(deg_W(v),2) [MOD 2]
       = #{ {x,y} subset W : x != y, vx and vy are edges } [MOD 2].
```

Then the pair `(p_W(v),c_W(v))` determines `deg_W(v) [MOD 4]` by

```text
0 -> (0,0),   1 -> (1,0),   2 -> (0,1),   3 -> (1,1).
```

Thus the first-bit theorem is equivalently a simultaneous parity selector for the ordinary graph
degree and for the centered pair-hypergraph whose `v`-degree counts unordered pairs of selected
neighbors of `v`.  The already available Gallai/Ferber--Krivelevich tools act only on the first
coordinate `p_W`; the missing endpoint is exactly the synchronization of the centered quadratic
coordinate `c_W` on the same support.  Any successful internal proof must therefore solve this
centered graph-plus-pair parity problem, or replace it by a genuine fixed-modulus principal-submatrix
theorem.

The same caution applies to the stronger all-zero loss-`5` placeholder
`HasModFourZeroLossFiveInducedSubgraph`: it is a sufficient assumption in the Lean handoff, not a
proved input.  It must not be justified by divisible-degree theorems unless the cited theorem is
explicitly induced, vertex-degree-wise, arbitrary-graph, and large enough at modulus `4`.

The exact missing statement is therefore not an edge-count zero-sum theorem and not a random-graph
partition theorem.  It is a deterministic principal-submatrix theorem for Eulerian `0/1` matrices:

```text
Every symmetric zero-diagonal matrix A over Z with even row sums has
a principal submatrix on at least n/32 rows whose row sums are congruent modulo 4.
```

This matrix form is equivalent to the even selector: row sums of a principal submatrix are exactly the
degrees in the corresponding induced subgraph.  A fixed-orientation parity selector is not an equivalent
reformulation and is not currently a valid sufficient input; the principal-submatrix statement is the
smallest honest first-bit target.

The active internal replacement target is the following centered-pair selector.

```text
Centered-pair parity selector.
Let E be an even graph.  There is W with |W| >= |E|/32 and a pair (p,c) in F_2^2
such that, for every v in W,

  deg_W(v) == p [MOD 2],
  #{ unordered pairs {x,y} subset W : vx, vy are edges of E } == c [MOD 2].
```

This is not a strengthening or weakening: via the residue table above it is exactly the same as the
loss-32 even mod-`4` selector.  The advantage is that it separates the already-linear coordinate
`p_W` from the genuinely quadratic carry coordinate `c_W`.  A proof may therefore target a simultaneous
graph/parity-pair selection lemma directly; proving only the `p_W` half recovers Gallai and cannot
close the first bit.

The deletion algebra for this coordinate pair is exact.  If `W subset S` and
`B = S \ W`, then for `v in W`, writing

```text
p_X(v) = deg_X(v) [MOD 2],
c_X(v) = binom(deg_X(v),2) [MOD 2],
```

we have over `F_2`

```text
p_W(v) = p_S(v) + p_B(v),
c_W(v) = c_S(v) + c_B(v) + p_W(v) * p_B(v).
```

The second identity is just

```text
binom(a+b,2) = binom(a,2) + binom(b,2) + ab
```

with `a = deg_W(v)` and `b = deg_B(v)`.  Hence the terminal co-cut problem has an
intrinsic two-coordinate form: if a chamber `S` has `(p_S,c_S)` synchronized on a large candidate
set, it is enough to choose a large retained `W` on which the deleted layer `B=S\W` has synchronized
`(p_B,c_B)`.  The finite exposed-layer refinement synchronizes old deleted layers, but at the final
step it gives no control of this fresh pair `(p_B,c_B)`, which is why the argument remains one
self-layer short.

There is an equivalent co-degree way to package the same last step.  In the even graph `E`, choose a
largest total-degree class `S0`, so `|S0| >= |E|/2` and `deg_E(v) == lambda [MOD 4]` on `S0`.  For
`W subset S0` and `v in W`,

```text
deg_W(v) == lambda - deg_{E \ W}(v) [MOD 4].
```

Thus it is enough to prove the following labeled terminal co-degree selector.

```text
Labeled co-degree selector.
For every graph H and every label alpha : V(H) -> Z/4Z, there is W with
|W| >= |H|/16 and a residue r such that, for every v in W,

  alpha(v) + deg_{H \ W}(v) == r [MOD 4].
```

This is sufficient, but it is stronger than what the first-bit proof actually needs.  In the application
`H=E[S0]` and `alpha(v)=deg_{E \ S0}(v) [MOD 4]`, the labels satisfy

```text
alpha(v) + deg_H(v) == lambda [MOD 4].
```

Therefore

```text
alpha(v) + deg_{H \ W}(v) == lambda - deg_W(v) [MOD 4].
```

So the needed terminal lemma is exactly the fixed-modulus-four congruent-degree selector for arbitrary
graphs:

```text
Every graph H contains W with |W| >= |H|/16 such that all degrees in H[W]
are congruent modulo 4.
```

Applied to `H=E[S0]`, this gives the required `1/32` even selector.  This is weaker and cleaner than
the arbitrary-label co-degree theorem; it is the current honest first-bit endpoint.  It is still fixed
modulus `4`, so it does not imply the forbidden growing-modulus selector that would collapse the
regular-induced-subgraph problem.

There is one useful maximal-counterexample reduction which removes a tempting but wrong source of
difficulty.  Let `W` be a maximal retained set whose induced degrees are all `r mod 4`, and put
`U=V\W`.  If there is a nonempty packet `B subset U` and a residue `delta` such that

```text
deg_B(w) == delta [MOD 4]                         for every w in W,
deg_W(b) + deg_B(b) == r + delta [MOD 4]          for every b in B,
```

then `W union B` is a larger mod-`4`-congruent induced subgraph: vertices of `W` are shifted uniformly
by `delta`, and vertices of `B` land on the same shifted residue.  The first, `W`-side, condition is
purely linear.  Fixing one anchor `w0 in W`, apply the Alon--Friedland--Kalai/Olson zero-subsum
lemma to the vectors

```text
(1_{bw}-1_{bw0})_{w in W\{w0}} in (Z/4Z)^(|W|-1),        b in P,
```

for any outside pool `P`.  If `|P| > 3(|W|-1)`, some nonempty `B subset P` has zero sum in every
difference coordinate, hence `deg_B(w)` is independent of `w in W` modulo `4`.  Thus the linear
co-cut balancing against the old witness is not the real obstruction.  A genuine counterexample must
force every such `W`-balanced packet to fail on the second, internal `B`-side, congruence.  This is
exactly the same self-layer/carry obstruction in packet form.

The packet obstruction has a useful sparse-side consequence, but only in the zero-shift chamber without
an additional target-subsum input.  Put

```text
P_0 = { b in U : deg_W(b) == r [MOD 4] }.
```

If `P_0` contains an independent set `I` with `|I| > 3|W|`, then `W` was not maximal.  Indeed,
apply Olson's zero-subsum lemma to the full adjacency vectors

```text
(1_{bw})_{w in W},        b in I.
```

It gives a nonempty `B subset I` for which `deg_B(w)=0` for every `w in W`.  Since `I` is independent,
`deg_B(b)=0` for every `b in B`, while `B subset P_0` gives `deg_W(b)=r`.  Thus both packet equations
hold with `delta=0`, and `W union B` is larger.
Consequently, in any maximal counterexample,

```text
alpha(P_0) <= 3|W|.
```

For the other degree-to-`W` chambers the missing datum is exactly one affine target coordinate, not the
old difference balancing.  If `P_t={b: deg_W(b)=t}` and `I subset P_t` is independent, then an
independent packet `B subset I` extends `W` precisely when

```text
sum_B(1_{bw}) == t-r                               for all w in W [MOD 4].
```

The dense analogue has the same shape.  If a clique `K subset P_t` contains a subset `B` with

```text
sum_B(1_{bw}-1_{bw0}) == 0                         for all w != w0,
sum_B(1-1_{bw0}) == r - t + 1                       [MOD 4],
```

then `deg_B(w)` is constant on `W` and `|B|-1+t == r+deg_B(w0)`, so `B` also enlarges `W`.  Hence the
unclosed dense case is a target-subsum problem in `(Z/4Z)^{|W|}` for the vectors
`((1_{bw}-1_{bw0})_{w != w0}, 1-1_{bw0})` restricted to clique chambers.  This is a more precise form
of the terminal self-layer obstruction: after ordinary old-witness balancing, every nonzero chamber
still has to hit one affine target rather than merely produce a zero-sum.

This gives the exact threshold lemma still missing.  Let `m=|W|` and, for `t in Z/4Z`, let
`P_t={b in U : deg_W(b)=t}`.  Since the four `P_t` partition `U`, if `m<|V(H)|/16` then
`|U|>15m`, so some chamber has size `>15m/4>3m`.  Therefore the mod-`4` selector follows from the
following purely packet-local statement:

```text
Affine chamber packet lemma.
Let W be a maximum-cardinality mod-4-congruent witness of residue r.  If a chamber
P_t={b:deg_W(b)=t} has size >3|W|, then it contains a nonempty B and a residue delta such that

  deg_B(w) == delta                         for every w in W,
  deg_B(b) == r+delta-t                     for every b in B.
```

The constant `3` is not cosmetic: it is exactly the Davenport/Olson threshold for balancing the old
`W`-coordinates over `(Z/4Z)^{|W|}`.  All previous false routes failed because they supplied only the
first line of this lemma.  The remaining mathematical task is to prove the second line at the same
threshold using the additional maximality information that no induced subgraph inside `P_t` is larger
than `W` and already mod-`4`-congruent.  Without that maximality input the statement is false: an
independent chamber with all old-neighborhood vectors equal to a single basis vector can defeat every
nonzero affine target, although such a chamber would itself replace `W` if it had size greater than
`|W|`.

The word "maximum" is essential here.  In a genuine minimum counterexample, `W` is chosen with largest
cardinality among all mod-`4`-congruent induced subgraphs.  Consequently every outside chamber
`P_t` has no mod-`4`-congruent induced subgraph of size greater than `m=|W|`; in particular
`alpha(P_t)<=m`, `omega(P_t)<=m`, and no induced cycle or regular packet in `P_t` may have size
greater than `m`.  Thus a chamber with `|P_t|>3m` is already a dense/no-large-regular-witness object:
it is not enough to exclude large independent chambers, and an inclusion-maximal `W` would not provide
the needed contradiction.  The remaining target is therefore the dense affine-packet theorem under this
global maximum hypothesis.

For the actual loss-`32` first-bit theorem, the sharp `3m` chamber threshold is stronger than is
strictly needed.  If an even witness `H` on `n` vertices had a maximum mod-`4` congruent set
`|W|=m<n/32`, then the outside set has size greater than `31m`, so some degree-to-`W` chamber has
size greater than `31m/4`.  Thus any chamber theorem with threshold below `31/4` would already close
the Lean-facing endpoint.  This slack is useful because Olson can be iterated inside such a chamber:
after greedily removing old-balanced packets, the leftover has size at most `3(m-1)`, and the union of
the removed packets is itself old-balanced and has size greater than `19m/4`.  The missing point is
then no longer old-coordinate balancing at all, but how to repair the self-layer.

Equivalently, this gives a precise external-import threshold.  In a terminal counterexample every
outside chamber `P_t` of size `>31m/4` must itself have no mod-`4` congruent induced subgraph of size
greater than `m`.  Therefore any arbitrary-graph theorem guaranteeing a mod-`4` congruent induced
subgraph of size more than `(4/31)|P_t|` inside every graph would close the first-bit endpoint
immediately by applying it to this chamber.  Constants at or below `4/31` are not enough by this direct
chamber-maximality argument.  The live proof is thus asking for either a universal selector stronger
than `4/31` or, more realistically, a selector that exploits the special degree-to-`W` chamber
structure and the old-coordinate packet equations.

The repair equations show why the append-only packet lemma is the rigid endpoint.  Suppose
`B subset P_t` is old-balanced, so every `w in W` has `deg_B(w)=delta`.  If we delete
`D subset W` and keep `W'=W\D`, then `W' union B` has common residue `R` exactly when

```text
  deg_D(w) == r+delta-R                 for every w in W',
  deg_D(b) == t+deg_B(b)-R              for every b in B.
```

The append-only packet is the special case `D=empty`, `R=r+delta`.  Therefore the live obstruction can
also be phrased as a labelled deletion problem on the old witness: a large old-balanced packet exists
with room to spare, and maximality must force either the append-only self-layer target or a nonempty
old deletion `D` whose two correction lines leave more vertices gained than lost.  This is the
replacement version of the terminal self-layer problem.

There is an important correction to the tempting "delete first, then Olson" shortcut.  Fix
`D subset W`, put `E=W\D`, and choose a basepoint `e_0 in E`.  The old-coordinate replacement
condition is not merely that `B` be old-balanced on `E`; it is the affine target

```text
deg_B(w)-deg_B(e_0) == deg_D(w)-deg_D(e_0)        for every w in E.
```

Ordinary Olson supplies large zero-target packets, not arbitrary prescribed target packets.  Adding a
single artificial `-target` vector does not force a zero-sum to use it, and representing every target
would require group-size rather than linear slack.  Thus the first replacement equation is automatic
after an Olson step only in the special case where `deg_D(w)` is already constant on `E`, equivalently
where `E` is itself a mod-`4` congruent induced subset of `W`.

For such an internally congruent kept set `E`, write `e=|E|`.  Balancing only the coordinates of `E`
does give a packet `B_E subset P_t` with

```text
|B_E| > N - max(0,3(e-1)).
```

Since `N>31m/4`, this is larger than `m-e=|D|` for every `e<=m`.  The corrected loss-`32` endpoint is
therefore not an arbitrary deletion theorem, but a simultaneous kept-old theorem: find a congruent
kept set `E subset W` and an old-balanced packet `B` on `E`, still with `|E|+|B|>m`, whose self-layer
also satisfies

```text
deg_E(b)+deg_B(b) == R                              for every b in B.
```

The fully signed statement below remains necessary and sufficient, but the naive Olson size bound
only proves its zero-target/congruent-`E` subcase.  This is exactly why the final obstruction is a
two-sided absorption problem rather than a one-sided dimension count.

There is, however, a correct signed way to use Olson without an arbitrary-target theorem.  Work in
`(Z/4Z)^(W\{w_0})`.  For each chamber vertex `b in P_t` insert the positive vector

```text
p_b(w)=1_{bw}-1_{bw_0},
```

and for each old vertex `d in W` insert the negative vector

```text
-p_d(w)=-(1_{dw}-1_{dw_0}).
```

Greedily remove zero-sum blocks from this combined sequence.  At most `3(m-1)` elements remain, so
the union of the removed blocks is a zero-sum signed packet `(B,D)` with

```text
|B| >= |P_t|-3(m-1) > 19m/4,        |D| <= m.
```

In particular `|B|>|D|`, and the zero-sum condition gives

```text
deg_B(w)-deg_D(w) == deg_B(w_0)-deg_D(w_0)        for every w in W.
```

This proves the old-side half of the profitable signed packet with surplus.  The whole first-bit
problem is therefore concentrated in the signed self-layer cleanup: pass from such a surplus signed
old-balanced packet to one for which `deg_B(b)-deg_D(b)` is constant on the retained positive side.
Equivalently, since the old witness `W` itself has zero old-coordinate sum, replacing the negative
set `D` by the kept set `E=W\D` gives a set `E union B` of size greater than `m` whose degrees into
the old coordinate frame are already constant.  The only vertices not yet certified are the new
outside vertices `b in B`.

The fully symmetric profitable-replacement statement is:

```text
Find B subset P_t and D subset W with |B|>|D| and some K such that

  deg_B(w) - deg_D(w) == K             for every w in W\D,
  deg_B(b) - deg_D(b) == r+K-t         for every b in B.
```

Then `(W\D) union B` is a larger mod-`4`-congruent induced subgraph.  Conversely every enlargement
of `W` using vertices from one chamber has this form.  Hence a genuine counterexample is precisely
a chamber in which every profitable signed packet is blocked; the remaining theorem is to rule out
that blocking when `N>31m/4`.

There is an even sharper labelled-packet version that does not first pigeonhole to one chamber.  Let
`U=V(H)\W` and put `tau(b)=deg_W(b) [MOD 4]`.  If `m<n/32`, then `|U|>31m`.  It is enough to find
a nonempty `B subset U` and a residue `delta` such that

```text
deg_B(w)=delta                         for every w in W,
deg_B(b)+tau(b)=r+delta                for every b in B.
```

This appends `B` to `W` directly.  Olson on the old-coordinate differences now starts from the whole
outside set, so it gives an old-balanced packet `B_0` with `|B_0|>|U|-3(m-1)>28m`.  The labelled
self-layer is therefore the only obstruction, but the order of operations matters.  If one first
takes a large class of `h_0(b)=deg_{B_0}(b)+tau(b)`, the class has size `>7m`, but it need not remain
old-balanced on `W`.  Rebalancing the old coordinates inside that class leaves `>4m`, and any further
ordinary refinement by a newly exposed layer can again destroy old-balance unless Olson is run after
the refinement.  Running Olson after two such four-way refinements would start from only
`>28m/16=7m/4`, which is below the `3m` old-coordinate threshold.  Thus the whole-outside formulation
gains substantial slack, but not enough for a finite "classify, expose, rebalance" argument.

Allowing deletion before this final rebalance gives the exact numerical obstruction.  If after the
two necessary four-way refinements one has `>7m/4` vertices left and deletes `d` old vertices, the
remaining Olson step can leave more vertices than were deleted only if

```text
7m/4 - 3(m-d-1) > d,
```

which forces `d>5m/8-O(1)`.  So deletion can make the dimensions work only after sacrificing a
large majority of `W`; it does not by itself supply the corrected self-layer.  The surviving endpoint
is therefore a genuine self-layer synchronization lemma that preserves old-balance, rather than another
exposed-layer refinement.

Equivalently, writing `E=W\D` for the old vertices kept, a replacement is just a larger congruent
set `E union B`; the conditions become

```text
deg_E(w)+deg_B(w)=R          for every w in E,
deg_E(b)+deg_B(b)=R          for every b in B,
|E|+|B|>m.
```

This kept-old form shows why the last correction cannot be chosen in two independent stages.  In the
whole-outside route the terminal outside pool has size only `>7m/4` after the two necessary exposed
refinements.  If one first chooses `E`, then at best one quarter of that pool has the required value
of `deg_E(b)` against the final label, giving only `>7m/16` outside vertices; to beat `m` this would
force `|E|>9m/16`.  But the old-coordinate rebalance after choosing the outside set is feasible only
in the opposite range `|E|<3m/8+O(1)`.  Hence the final proof must choose `E` and `B` simultaneously:
`E` must correct the terminal labels on `B` while `B` also regularizes the labelled degrees on `E`.
This is the precise two-sided self-layer absorption problem.

For the original even-graph endpoint there is one extra piece of structure that the arbitrary-graph
selector discards.  If `U=V(H)\W`, every outside vertex has total degree `0` or `2 mod 4`; hence one
total-degree fiber `T subset U` has size greater than `31m/2`.  For `B subset T`, with
`C=T\B` and `F=U\T`, the append condition can be written in co-absorbing form:

```text
deg_T(w)-deg_C(w)=delta                         for every w in W,
deg_C(b)+deg_F(b)=s-r-delta                     for every b in B,
```

where `s` is the common total-degree residue on `T`.  Thus the even case is not merely a chamber
problem: one may try to choose a discarded outside corrector `C` so that its degrees simultaneously
regularize the old vertices and the retained outside vertices.  The naive refinement by the fixed
label `deg_F(b)` still costs a factor `4`, bringing the available pool back to the `>31m/8` chamber
scale, so this does not close the proof alone.  It does, however, identify the strongest remaining
even-specific route: a co-absorption lemma on the large total-degree fiber `T`, rather than another
append-only packet lemma inside a small chamber.

An important strengthening is to avoid taking the `h_0` residue class at all.  Let
`B_0 subset T` be old-balanced on `W`, with `|B_0|>25m/2`, and define

```text
h(b)=deg_W(b)+deg_{B_0}(b)        for b in B_0.
```

For any old-balanced `B subset B_0`, put `X=B_0\B` and let `delta_B` be the old increment of `B`.
Then `W union B` is a larger mod-`4` congruent witness exactly when

```text
theta_X(b):=h(b)-deg_X(b)-delta_B = r       for every b in B.
```

However, the zero-sum-free boundary argument cannot be applied to the whole `B_0`: since `B_0`
itself is old-balanced, a cardinal-maximal old-balanced subset of `B_0` is just `B_0`, and the
complement is empty.  Thus the whole-packet formulation is useful only as a labelled discard equation,
not as a maximal-boundary normal form.  To obtain a nontrivial zero-sum-free discarded boundary one
must either restrict to a piece such as the `h_0`-class `C`, which is not itself known to be
old-balanced, or impose an additional value-correct extremality rather than old-balance maximality.

The signed-Olson correction above improves the first old-frame step inside this even-specific route
but still stops at the same terminal obstruction.  Starting from `|T|>31m/2`, an old-balanced packet
`B_0 subset T` can be chosen with `|B_0|>|T|-3(m-1)>25m/2`.  One self-layer class of
`deg_{B_0}(b)+deg_W(b)` then has size `>25m/8`, just above the `3m` old-coordinate threshold.  Restoring
old-balance inside that class leaves only `>m/8`; using signed old negatives gives the same problem,
because the positive surplus after the `3m` Davenport loss is no longer guaranteed to dominate the
old deletions.  Thus the total-degree fiber buys exactly one more exposed layer, not a proof.  The
needed endpoint is sharper: a co-absorption lemma must preserve the `>3m` self-layer class while
regularizing the old frame, rather than regularizing it after the class has already been selected.

This gives a cleaner terminal formulation.  Let `B_0` be old-balanced on `W`, let

```text
h_0(b)=deg_W(b)+deg_{B_0}(b),
```

and take a large residue class `C subset B_0` of `h_0`; write `R=B_0\C`.  For any
`B subset C`,

```text
deg_W(b)+deg_B(b)
  = h_0(b) - deg_R(b) - deg_{C\B}(b)        for b in B.
```

Therefore, once `h_0` is constant on `C`, the final self-layer condition is equivalent to the
co-cut condition

```text
deg_R(b)+deg_{C\B}(b)=H-r-delta_B           for every b in B,
```

together with old-balance of `B` on `W`, where `H` is the common value of `h_0` on `C` and
`delta_B` is the common value of `deg_B(w)` on `W`.  The value is coupled to the old increment; mere
constancy of the co-cut label is not enough.  This is stronger than the earlier vague "self-layer"
wording: after the first large class is chosen, internal edges of `B` disappear from the target and
only the discarded side `R union (C\B)` remains, but its constant must equal `H-r-delta_B`.  The open
lemma is now a value-coupled old-balanced co-cut lemma for a class `C` of size just above `3m`.

Equivalently, put

```text
q_C(b)=deg_C(b)+deg_R(b).
```

Then the co-cut condition is the labelled induced-degree condition

```text
deg_B(b)=q_C(b)-(H-r-delta_B)                  for every b in B,
```

together with the zero-sum old-coordinate condition on `B` and its increment `delta_B`.  Thus the
terminal theorem is not an unlabelled mod-`4` selector on `C`; it is a prescribed-residue selector
whose prescribed residue depends on the same old-coordinate sum that must be zero.  Any closing lemma
must use this coupling between the labels and the old coordinates, because a black-box prescribed
mod-`4` induced-subgraph theorem with enough linear size is not available at the required `>3m`
threshold.

Allowing deletion of old vertices gives the exact signed version of the same co-cut endpoint.  For
`D subset W`, `E=W\D`, and `B subset C`, the candidate `(E union B)` has the right old-side degrees
precisely when

```text
deg_B(w)-deg_D(w)=K                         for every w in E.
```

On the new vertices this same replacement has degree

```text
deg_E(b)+deg_B(b)
  = h_0 - deg_R(b)-deg_{C\B}(b)-deg_D(b)    for b in B.
```

Thus the fully signed terminal condition is

```text
deg_R(b)+deg_{C\B}(b)+deg_D(b)=H-r-K        for every b in B,
|B|>|D|.
```

This is the exact co-cut analogue of the profitable signed packet.  The difficulty is numerical:
`|C|>25m/8` is enough for an append-only old-balanced subpacket, but signed Olson on `C` alone can
leave only `>m/8` positive vertices after the `3m` old-coordinate loss, so it does not by itself
guarantee `|B|>|D|`.  A proof must either close the append-only co-cut lemma on `C`, or find a signed
co-cut packet while preserving positive surplus.

The append-only co-cut can be written as a discard-corrector problem.  Put `X=C\B`.  Then
`W union B` is a larger congruent witness exactly when there is a residue `K` such that

```text
deg_X(w)=deg_C(w)-K                         for every w in W,
deg_X(b)=H-r-K-deg_R(b)                     for every b in C\X,
X != C.
```

This is the cleanest non-signed endpoint: the discarded set `X` must realize a prescribed
old-coordinate vector on `W` and, simultaneously, a prescribed one-sided degree pattern on the
vertices it does not discard.  Taking `X=empty` is the affine packet lemma; taking `X` after a residue
refinement is the false sequential route.  What remains is a genuine one-sided prescribed co-degree
selection theorem for a proper discard set.

There is one more exact reduction inside this discard form.  Choose `B subset C` maximal subject to
being old-balanced on `W`, and put `X=C\B`.  Then `X` is zero-sum-free in the old-coordinate
difference group: any nonempty old-balanced subset of `X` could be added to `B`.  Consequently

```text
|X| <= 3(m-1),        |B| > |C|-3(m-1) > m/8.
```

The old-coordinate equation for the discard set is now automatic, because `B=C\X` is old-balanced.
The only remaining condition is

```text
eta_X(b):=deg_X(b)+deg_R(b) = H-r-delta_B          on B.
```

Thus a terminal counterexample has a very rigid boundary form: every maximal old-balanced retained
set leaves a zero-sum-free discarded boundary `X` of size at most `3m-3`, and the co-cut label
`eta_X` either is nonconstant on the retained side or has the wrong constant value relative to
`delta_B`.  Proving that such a zero-sum-free boundary can always be exchanged away, with the value
coupling preserved, would close the endpoint.

The required exchange can be stated exactly.  Starting from an old-balanced split `C=B disjoint_union X`,
move `Y subset B` to the discard side and `Z subset X` to the retained side:

```text
B'=(B\Y) union Z,        X'=(X\Z) union Y.
```

The old frame is preserved exactly when

```text
sum_{z in Z} p_z = sum_{y in Y} p_y        in (Z/4Z)^(W\{w_0}),
```

where `p_v(w)=1_{vw}-1_{vw_0}`.  The new co-cut label is

```text
eta_{X'}(u)=eta_X(u)-deg_Z(u)+deg_Y(u)       for u in B\Y,
eta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)   for z in Z.
```

For the value-coupled problem one must also update the old increment.  If `delta_B=deg_B(w_0)`, then

```text
delta_{B'}=delta_B+deg_Z(w_0)-deg_Y(w_0).
```

Thus the invariant label is really

```text
theta_X(v)=eta_X(v)+delta_B,
```

and after the exchange

```text
theta_{X'}(u)=theta_X(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0)
                                                    for u in B\Y,
theta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)+delta_{B'}
                                                    for z in Z.
```

The target value for `theta` is the fixed residue `H-r`.

Thus the boundary-exchange lemma is finite and local: if `theta_X` is not identically `H-r` on a
maximal old-balanced `B`, find an old-vector-balanced exchange `(Y,Z)` with `B'` nonempty for which
the two displayed `theta` formulae equal `H-r` on `B'`.  The case `Z=empty` is a pure further discard
and is just the same co-cut problem inside `B`; the genuinely new possibility must use the
zero-sum-free boundary vertices in `X`.

For the extremal obstruction, choose `B` with maximum cardinality among old-balanced subsets of `C`,
and, subject to that, maximize the target fiber of the corrected label

```text
theta_X(b)=eta_X(b)+delta_B
```

on `B`, namely the vertices with `theta_X(b)=H-r`.  Then the boundary satisfies two additional
no-exchange rules.  First, there is no old-vector-balanced exchange `(Y,Z)` with `|Z|>|Y|`; otherwise
`B'` would be a larger old-balanced retained set.  Second, among exchanges with `|Z|=|Y|`, none can
increase the number of target-correct vertices in the updated boundary.  Therefore a minimal counterexample to
the co-cut lemma is not just a zero-sum-free boundary; it is a cardinality-maximal,
target-stable zero-sum-free boundary.  This is the strongest local form presently available:

```text
X is zero-sum-free,
no balanced exchange imports more vertices from X than it exports from B,
no equal-size balanced exchange improves the target theta-fiber {theta=H-r}.
```

Any proof of the terminal lemma may now target this extremal boundary directly.

For later local use, the target-stability inequality is explicit.  Let
`T={b in B : theta_X(b)=H-r}`.  For any balanced equal-size exchange `(Y,Z)`, target-stability says

```text
|{u in B\Y : theta_{X'}(u)=H-r}| + |{z in Z : theta_{X'}(z)=H-r}| <= |T|.
```

For a singleton swap `Y={y}`, `Z={z}` with `p_y=p_z`, this becomes

```text
|{u in B\{y} : theta_X(u)-1_{uz}+1_{uy}+1_{zw_0}-1_{yw_0}=H-r}|
  + 1_{theta_{X'}(z)=H-r}
  <= |T|.
```

In the exact basis model, `p_y=p_z` normally fixes the old neighbourhood and the anchor term vanishes,
so the obstruction is a concrete no-improving-swap condition comparing the neighbourhoods of `y` and
`z` inside the retained side.

Writing `L=H-r`, the same-old-vector singleton swap has the gain/loss form

```text
gain(y,z)=|{u in B\{y} : theta_X(u) != L,
                      theta_X(u)+1_{uy}-1_{uz}=L}|
          + 1_{theta_{X'}(z)=L},
loss(y,z)=|{u in B\{y} : theta_X(u)=L,
                      theta_X(u)+1_{uy}-1_{uz} != L}|
          + 1_{theta_X(y)=L}.
```

Target-stability is exactly

```text
gain(y,z)<=loss(y,z)
```

for every same-old-vector boundary import `z` and retained export `y`.  Thus any boundary vertex that
would become target-correct after import must either be paid for by exporting a target-correct retained
vertex or by knocking some already target-correct retained vertex off target.  This is the counting form
of the singleton-swap obstruction.

One must not overstate the fiber obstruction.  If `S subset B` is old-balanced and `eta_X` is
constant on `S`, this does not by itself append `S` to `W`: the vertices in `B\S` have moved to the
discard side and contribute the additional term `deg_{B\S}(s)` on `S`, and the old increment changes
from `delta_B` to `delta_S`.  Thus a pure discard is truly recursive.  It closes only when the updated
value-coupled label

```text
theta_{X union (B\S)}(s)=eta_X(s)+deg_{B\S}(s)+delta_S
```

equals `H-r` on `S`.  This correction is important: the terminal obstruction is not a simple
five-piece zero-sum-free decomposition by `eta_X`-fibers.  The exchange lemma has to control the
co-cut term and old-increment shift created by every discarded part.

Equivalently, for a pure discard of `B\S`, where both `S` and `B\S` are old-balanced, write
`delta_{B\S}` for the common old increment of `B\S`.  Since
`delta_B=delta_S+delta_{B\S}`, the updated target on `S` is

```text
theta_{X union (B\S)}(s)
  = theta_X(s)+deg_{B\S}(s)-delta_{B\S}.
```

Thus every old-balanced block `S subset B` is a potential immediate exit if

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S}=H-r       for every s in S.
```

In a terminal counterexample, every old-balanced block fails this block-interaction equation.  This is
the exact recursive obstruction left after the value-coupled correction.

If `B` is decomposed into old-balanced blocks

```text
B=S_1 disjoint_union ... disjoint_union S_l,
```

with old increments `delta_i`, the condition for the pure-discard exit using block `S_i` becomes

```text
theta_X(s)+sum_{j != i} (deg_{S_j}(s)-delta_j)=H-r       for every s in S_i.
```

Thus an exchange-free counterexample is a finite interacting zero-sum-block system: no block sees the
boundary plus the other blocks with the same corrected residue as the old frame.  A proof may now
target either an import from `X` or a block `S_i` satisfying this displayed equation.

For a minimal old-balanced block `S subset B`, define its pure-discard defect

```text
phi_S(s)=theta_X(s)+deg_{B\S}(s)-delta_{B\S}-(H-r).
```

The block exits exactly when `phi_S` is identically zero.  If it is not, an import from the boundary
must choose nonempty `Z subset X` and an export `Y subset B` with the same old-coordinate sum.  In the
special exchange that repairs only the block, take `Y subset S` and retain

```text
S'=(S\Y) union Z.
```

Then the old-balance condition is `sum p_Z=sum p_Y`, and the corrected defect on the surviving old
block vertices is shifted by

```text
phi_{S'}(u)=phi_S(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0)       for u in S\Y.
```

The new imported vertices `z in Z` have the corresponding value

```text
theta_{X'}(z)+deg_{B'\S'}(z)-delta_{B'\S'}-(H-r),
```

with `X'=(X\Z) union Y` and `B'=(B\Y) union Z`.  Thus the smallest unsolved local move is: given a
nonzero defect on a minimal zero-sum block, import a boundary subset with the same old vector so that
the displayed defect vanishes on the exchanged block.  This is a value-coupled zero-sum exchange
problem, not merely a size problem.

The defect has a useful cancellation that removes the auxiliary boundary from the local statement.
Since

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S}
  = deg_X(s)+deg_R(s)+deg_{B\S}(s)+delta_S
  = deg_{B_0\S}(s)+delta_S,
```

and `H=deg_W(s)+deg_{B_0}(s)` on the class `C`, one gets

```text
phi_S(s)=r+delta_S-deg_W(s)-deg_S(s).
```

Thus `phi_S=0` is exactly the assertion that the atom `S` itself appends to `W`.  The same formula
holds after an import: for `S'=(S\Y) union Z`,

```text
phi_{S'}(v)=r+delta_{S'}-deg_W(v)-deg_{S'}(v)       for v in S'.
```

So the boundary-exchange language is not adding a new target; it is a mechanism for manufacturing a
self-correcting old-balanced atom inside the `h_0`-class.  In this atom form the terminal theorem is:
inside a class `C` of size greater than the `C_4^(m-1)` Davenport threshold, find a nonempty
old-balanced `S subset C` whose append defect `r+delta_S-deg_W-deg_S` vanishes on `S`.  The maximal
split `C=B disjoint_union X` only records that no such atom has yet been found and leaves a
zero-sum-free reservoir `X` for exchanges.

Summing the atom defect gives the necessary congruence

```text
sum_{s in S} phi_S(s)
  = |S| r + (|S|-m) delta_S - 2 e(S)       [MOD 4],
```

because old-balance gives `sum_{s in S} deg_W(s)=m delta_S`.  Any final proof by atoms must therefore
use more than this scalar obstruction: it must synchronize the pointwise defect, not merely its sum.

The signed repair of an atom is equally explicit.  If `S subset C` is old-balanced with defect
`phi_S`, then replacing `W` by `E=W\D` and adding `S` succeeds with common residue
`R=r+delta_S-c` exactly when

```text
deg_D(w)=c                         for every w in E,
deg_D(s)=c-phi_S(s)                for every s in S,
|S|>|D|.
```

Indeed the kept old vertices have degree `r+delta_S-deg_D(w)`, while vertices of `S` have degree
`r+delta_S-phi_S(s)-deg_D(s)`.  Thus the append-only atom theorem is the `D=empty`, `c=0` subcase of
a sharper signed-atom repair problem.  A terminal counterexample must block both: no atom has
`phi_S=0`, and no defective atom admits a smaller old correction `D` with the two displayed degree
conditions.

There is still a small amount of unused Davenport slack in the class `C`.  Since

```text
|C|>25m/8,
```

Olson may be applied not only to the `m-1` old difference coordinates but to
`m-1+a` fixed `Z/4Z` coordinates whenever

```text
3(m-1+a)<|C|.
```

Thus at least one auxiliary fixed coordinate is always affordable, and for large `m` one can afford
roughly `m/24` such coordinates.  Examples are the constant coordinate `1`, the anchor-adjacency
coordinate `1_{bw_0}`, or a fixed co-cut label such as `deg_R(b)`.  Consequently one can force, in
addition to old-balance, scalar congruences such as

```text
|S|=0,        delta_S=0,        or        sum_{s in S} deg_R(s)=0        [MOD 4],
```

depending on the chosen auxiliary coordinate.

This margin is useful but not yet a proof.  These augmented Olson atoms only control scalar data of
`S`; the append condition is still the pointwise equation

```text
r+delta_S-deg_W(s)-deg_S(s)=0        for every s in S.
```

So any closing argument that uses the `25m/8` slack must convert a bounded number of auxiliary scalar
constraints into pointwise defect cancellation, or combine many such atoms through the signed repair
criterion above.

The inverse-Davenport branch has a sharper exchange interpretation.  Let

```text
Sigma_l(X)={ sum_{z in Z} p_z : Z subset X, |Z|=l }.
```

Cardinality-maximality of `B` says more than `X` is zero-sum-free: for all `Y subset B` and
`Z subset X`,

```text
sum p_Y=sum p_Z        =>        |Z|<=|Y|.
```

Otherwise replacing `Y` by `Z` gives a larger old-balanced retained set.  In particular,

```text
p(B) cap union_{l>=2} Sigma_l(X)=empty.
```

So every retained old-vector avoids all boundary subset-sums of length at least two.

In the exact extremal zero-sum-free model for `C_4^d`, after choosing a basis one has

```text
X={e_1,e_1,e_1, ..., e_d,e_d,e_d}.
```

Then every nonzero group element except the basis elements `e_i` has a representation by at least two
terms of `X`.  Hence the maximality separation forces

```text
p_b in {0,e_1,...,e_d}        for every b in B
```

in this exact extremal model.  The minimal old-balanced atoms are then only zero-row singletons and
four-copy atoms in one basis direction.  Thus the near-extremal inverse-Davenport proof has a concrete
finite target: deviations from the basis model must create a profitable import, while the basis model
itself reduces to checking self-correcting or signed-repairable singleton/four-copy atoms with identical
old-neighbourhood type.

In the exact basis model these atoms can be written explicitly.  A retained vertex with `p_b=0` is a
singleton atom; it closes append-only exactly when `r=0`, because `deg_S(b)=0` and
`deg_W(b)=delta_S`.  For a nonzero feasible basis vector `g`, all vertices with `p_b=g` have the same
old-neighbourhood residue `omega(g)=deg_W(b)` and the same anchor contribution, so any four of them
form an old-balanced atom with `delta_S=0`.  Its append defect is

```text
phi_S(b)=r-omega(g)-deg_S(b).
```

Thus the four-copy atom closes precisely when the chosen four vertices induce a regular four-vertex
graph of degree `r-omega(g)` modulo `4` (independent set, matching, cycle, or clique according to the
residue).  This explains why the exact extremal model is still not automatic: `|B|>m/8` can be spread
among many basis directions, and even a large single direction need not contain the required regular
four-vertex type unless maximality or signed repair supplies additional information.

There is a useful signed refinement inside the same fiber.  If four vertices in direction `g` induce a
regular graph of degree `d'` but the required residue is `d=r-omega(g)`, then the defect is the constant
`d-d'`.  The signed-repair criterion becomes a purely old-side problem:

```text
find D subset W, |D|<4, and c such that
deg_D(w)=c                       for every w in W\D,
deg_D(b)=c-(d-d')                for the common old-neighbourhood type b in C_g.
```

Thus a wrong-residue regular four-block is not the same obstruction as a nonregular four-block.  It
closes whenever the old witness contains a small co-regular deletion set with the displayed intersection
against the direction's old-neighbourhood type.  In particular, the exact-basis terminal case must block
both the required regular four-block and these wrong-residue regular blocks with small old corrections.

This packages the signed information into a finite repair spectrum.  For a direction `g`, let
`Rep(g)` be the set of residues `d' in Z/4Z` for which a `d'`-regular four-block in the direction is
repairable by some `D subset W`, `|D|<4`, as above; the empty deletion puts the required residue
`d=r-omega(g)` in `Rep(g)`.  Then a terminal exact-basis fiber `C_g` must avoid induced regular
four-sets of every degree in `Rep(g)`.  If `{0,3} subset Rep(g)`, Ramsey's theorem bounds
`|C_g|<R(4,4)`, because `0`-regular and `3`-regular four-sets are independent four-sets and cliques.
Thus any large exact-basis fiber must have a repair spectrum missing at least one of the two Ramsey
extremes.  This isolates the remaining obstruction to directions whose old-side small-deletion spectrum
cannot repair both empty and complete four-blocks.

The four-block spectrum is only the smallest instance.  If `S subset C_g` has `|S|=0 [MOD 4]` and
`G[S]` is regular of degree `d' [MOD 4]`, then `S` is old-balanced and has constant defect `d-d'`.
Signed repair asks for `D subset W`, `|D|<|S|`, such that `deg_D` is constant on `W\D` and has the
corresponding shifted constant value on the common old-neighbourhood type of `g`.  Thus a large
empty or complete direction fiber is not automatically a countermodel: larger regular blocks give more
surplus and can be repaired by larger old co-regular deletion sets.  The genuine terminal obstruction is
absence of all such surplus constant-defect block repairs, not just absence of the four-vertex required
regular type.

The old-side condition has a useful intrinsic meaning.  Writing `E=W\D`, the requirement
`deg_D(w)=c` on `E` is equivalent to

```text
deg_E(w)=r-c        for every w in E.
```

Thus `E` is itself an old congruent induced witness.  A constant-defect same-direction block is repaired
exactly by splicing it onto a smaller old witness `E`, with the additional scalar condition on
`deg_D` against the direction's common old-neighbourhood type and the surplus inequality
`|S|>|W\E|`.  This reformulation may be stronger than viewing `D` as an arbitrary co-regular set,
because it ties every signed repair to the internal witness structure of the maximal set `W`.

In this kept-old notation the repair spectrum has the simple formula

```text
d' is repaired by D  <=>  d' = d + deg_D(b_g) - c,
```

where `d=r-omega(g)`, `b_g` is any vertex of the direction type, and
`deg_D(w)=c` for all `w in E=W\D`.  Thus the spectrum is determined by all proper old subwitnesses
`E` of `W` through the shift

```text
shift_D(g)=deg_D(b_g)-deg_D(E)        [MOD 4],
```

where `deg_D(E)` denotes the common value of `deg_D` on `E`.  For `|D|<4` this is a finite catalogue:
a singleton deletion is usable only when the deleted vertex is isolated from, or complete to, the kept
old set; a pair deletion is usable only when every kept old vertex sees `0`, `1`, or `2` of the pair;
and a triple deletion is usable only when every kept old vertex sees a fixed number of the triple.  In
each case the direction residue shifts by `|N_W(b_g) cap D|-c`.  Therefore a terminal exact-basis
direction is one whose old-neighbourhood type avoids all extremal shifts supplied by these small
internal subwitnesses of `W`.

Consequently, for a direction type `g` define

```text
Delta_<(4)(g)={deg_D(b_g)-c :
               |D|<4 and deg_D(w)=c for every w in W\D}.
```

Then the four-block repair spectrum is `d+Delta_<(4)(g)`.  The correct terminal consequence is
residue-by-residue, not the stronger false conclusion that all extreme residues are absent:

```text
0 in d+Delta_<(4)(g)  =>  C_g has no independent four-set,
3 in d+Delta_<(4)(g)  =>  C_g has no clique four-set,
1 in d+Delta_<(4)(g)  =>  C_g has no induced 2K_2,
2 in d+Delta_<(4)(g)  =>  C_g has no induced C_4.
```

Only the simultaneous presence of both extremes gives a constant Ramsey bound:
if `{0,3} subset d+Delta_<(4)(g)`, then `|C_g|<R(4,4)`.  Thus a large terminal
direction need not have middle-only spectrum; it may carry one extreme residue, in which case the
corresponding independence or clique number is at most three.  The append-only residue `d` is always in
the spectrum, so the required residue itself may be `0` or `3`; that branch must be controlled by
outside-only maximality or by the augmented boundary sieve, not by Ramsey alone.

The middle residues still have concrete first obstructions.  If `1` lies in the repair spectrum, a
terminal direction is induced-`2K_2`-free.  If `2` lies in the repair spectrum, it is induced-`C_4`-free.
Larger constant-defect repairs say more: there is no induced regular block of size `0 mod 4` whose
residue lies in the shifted spectrum and whose old-side correction has surplus.  But the first visible
hereditary obstruction is exactly the list above.

The two middle obstructions are complements on four vertices: the complement of `2K_2` is `C_4`.
Thus if a direction's deletion spectrum ever contains both middle residues `1` and `2`, a terminal
large fiber must avoid both induced `2K_2` and induced `C_4`.  Any remaining large obstruction then
has to live in the narrow split/cycle boundary of the hereditary theory, and outside-only maximality
also forbids collecting many congruent cyclic blocks from such fibers.  This does not close the branch,
but it reduces the large-fiber exact-basis endpoint to hereditary middle-residue structure plus the
old-deletion shift catalogue.

More concretely, the standard pseudo-split characterization of `(2K_2,C_4)`-free graphs gives a
finite structural branch.  Such a fiber has a partition into a clique part `K`, an independent part `I`,
and possibly a five-cycle core `M`, with the usual prescribed adjacencies between the core and the
split parts.  Since `W` is maximum, the fiber has no clique or independent set larger than `m`; hence
the pseudo-split branch has size at most about `2m+5` in a single direction.  Thus any exact-basis
counterexample with a direction fiber substantially larger than `2m` must have a repair spectrum
missing one of the two middle residues.  This turns the large-fiber obstruction into a finite
old-deletion spectrum problem rather than an arbitrary hereditary graph problem.

The earlier tempting singleton-spectrum conclusion was too strong.  What is actually forced above the
pseudo-split cap is only a **spectrum-hole** condition: the repair spectrum cannot contain both middle
residues, and if it contains both extreme residues then the direction is Ramsey-small.  Hence a large
terminal direction has one of the following sparse spectra: one middle residue; one extreme residue; or
one middle together with one extreme.  Each nonzero old-deletion shift is still valuable, because it adds
one of the forbidden hereditary constraints in the displayed list, but singleton rigidity
`Delta_<(4)(g)={0}` requires an additional argument and is not a consequence of Ramsey alone.

In fact signed repair does not change the pointwise obstruction inside a single nonzero basis fiber.
Since all four vertices with `p_b=g` have the same old neighbourhood in `W`, every `D subset W` has
`deg_D(b)` constant on the four vertices.  The signed condition

```text
deg_D(b)=c-\phi_S(b)
```

therefore forces `phi_S` itself to be constant, equivalently forces the four vertices to be regular.
So a nonregular four-copy atom cannot be repaired by deleting old vertices alone.  The exact extremal
case must either find the required regular four-set inside one basis fiber or use a cross-direction
exchange/import that changes the internal degrees non-uniformly.

The boundary triples in the exact model give a sharper test.  For each basis direction `g_i`, the
boundary contains three copies `X_i={x_{i,1},x_{i,2},x_{i,3}}`.  If `b in B` has `p_b=g_i`, then

```text
S=X_i union {b}
```

is old-balanced.  Therefore the proof closes immediately if this four-set induces the regular
four-vertex graph of degree `r-omega(g_i)` modulo `4`.  For a fixed boundary triple, each residue
allows at most one adjacency pattern from `b` to the triple:

```text
d=0:  X_i independent and b misses all of X_i;
d=1:  X_i has one edge and b sees exactly the isolated vertex;
d=2:  X_i is a path of length two and b sees exactly the two endpoints;
d=3:  X_i is a triangle and b sees all of X_i.
```

Thus an exact-extremal terminal counterexample must avoid this one allowed extension pattern for every
retained vertex in every basis direction.  This is a finite local obstruction inside each boundary
triple, and any successful inverse-Davenport closure must show that the simultaneous avoidance of all
these `3+1` regular extensions either creates a profitable import elsewhere or contradicts maximality of
the original witness.

The `3+1` test is only the first member of the augmented-direction sieve.  In the exact basis model the
three boundary copies and all retained copies in the same direction have the same old vector.  Therefore
every four-set

```text
Y union Z,        Y subset X_i, Z subset C_i, |Y|+|Z|=4, |Z|>0,
```

is old-balanced.  It closes append-only whenever it is `d_i`-regular, where
`d_i=r-omega(g_i)`.  Thus a terminal exact-basis configuration must forbid `d_i`-regular four-sets in
the **augmented fiber** `A_i=X_i union C_i`, not just among four retained vertices or among
`X_i union {b}`.

The signed repair spectrum applies to these augmented atoms as well.  If such a four-set in `A_i`
induces a regular graph of residue `d'`, its defect is again constant `d_i-d'`, because all four vertices
have the same old-neighbourhood type.  Hence every residue `d' in Rep(g_i)` is forbidden in the
augmented fiber, provided the four-set uses at least one retained vertex so that it is a genuine
profitable import from the boundary/retained pool.  The append-only sieve is the special case
`d'=d_i`.

Equivalently, for each retained vertex `b in C_i` let

```text
a_b(x)=1_{bx},        x in X_i.
```

Then the mixed atom conditions are explicit.  For `Y subset X_i` and `Z subset C_i` with
`|Y|+|Z|=4`, the atom closes iff

```text
deg_Y(y)+sum_{z in Z} a_z(y)=d_i          for every y in Y,
deg_Z(z)+sum_{y in Y} a_z(y)=d_i          for every z in Z.
```

The cases `|Z|=2` and `|Z|=3` are new finite obstructions: two retained vertices together with two
boundary copies, or three retained vertices together with one boundary copy, can repair a direction even
when neither a single retained vertex nor a four-retained block works.  Hence the exact-basis endpoint
should be treated as an eight-type graph over the boundary triple, with these mixed regularity equations
forbidden in every active direction.

The `2+2` equation collapses to a particularly rigid square rule.  Let `Y={x,y} subset X_i` and
`Z={b,c} subset C_i`.  Write `e=1_{xy}` and `epsilon=1_{bc}`.  The four-set is `d_i`-regular iff

```text
epsilon=e,
the 2 by 2 bipartite graph between {b,c} and {x,y} is (d_i-e)-regular.
```

Thus `d_i-e` must be `0`, `1`, or `2`; the cross pattern is respectively empty, a perfect matching
(one of the two `2`-edge 1-regular squares), or complete.  In particular, retained pairs whose edge
status matches a boundary pair are dangerous exactly when their two adjacency types to that boundary pair
form the corresponding regular square.

The `1+3` equation is the dual of the `3+1` table.  For a boundary vertex `x` and retained triple
`T`, a `d_i`-regular atom occurs precisely as follows:

```text
d_i=0:  T is independent and every vertex of T misses x;
d_i=1:  exactly one vertex of T hits x, and it is isolated in T;
d_i=2:  exactly two vertices of T hit x, and the unique misser is the middle of a path P_3;
d_i=3:  T is a triangle and every vertex of T hits x.
```

These tables are still not a contradiction, but they are stronger than the earlier retained-only
hereditary obstruction: each boundary edge/nonedge cuts the retained type graph by a prescribed
edge-status square rule, and each boundary vertex cuts retained triples by the displayed one-corner
patterns.

It is useful to restate the same tables as hereditary constraints on types.  Fix a boundary pair
`{x,y}` with edge status `e`, and write the two-bit type of a retained vertex as its adjacency to
`(x,y)`.  Put `q=d_i-e`.  Terminality implies:

```text
q=0:  two vertices of type 00 may not have retained edge-status e;
q=1:  a type-10 vertex and a type-01 vertex may not have retained edge-status e;
q=2:  two vertices of type 11 may not have retained edge-status e;
```

with no `2+2` restriction from this pair when `q` is outside `{0,1,2}`.  Thus, depending on the boundary
pair and the required residue, a type class is forced to be independent or clique, or two complementary
one-hit classes are forced to be joined or co-joined.

Similarly, for a boundary vertex `x`, let `M_x` be the retained vertices missing `x` and `H_x` those
hitting `x`.  The `1+3` table says:

```text
d_i=0:  alpha(G[M_x]) <= 2;
d_i=3:  omega(G[H_x]) <= 2;
d_i=1:  for every h in H_x, the non-neighbours of h inside M_x form an independent set;
d_i=2:  for every m in M_x, the neighbours of m inside H_x form a clique.
```

These are purely finite graph constraints.  A terminal exact-basis proof can now target the eight-type
quotient: either one of these constraints forces a large outside-only congruent set, or the quotient has
enough regular cross-type squares/triples to build an appendable atom.

For signed repair the same constraints should be read residue-by-residue.  Fix any
`s in Rep(g_i)`.  The `2+2` rule for a boundary pair of status `e` uses `q=s-e` instead of
`q=d_i-e`:

```text
q=0:  type-00 pairs may not have retained edge-status e;
q=1:  type-10/type-01 pairs may not have retained edge-status e;
q=2:  type-11 pairs may not have retained edge-status e;
q=3:  no 2+2 regular square exists for this boundary pair.
```

The `1+3` rule is likewise obtained by replacing `d_i` with `s`.  Thus `0 in Rep(g_i)` forces every
boundary-miss class to have independence number at most `2`, while `3 in Rep(g_i)` forces every
boundary-hit class to have clique number at most `2`; the middle residues impose the one-corner
isolated-hitter and path-middle constraints.  This spectrum-parametric form is stronger than the earlier
Ramsey-only use of `Rep(g_i)`: repaired extreme residues constrain pairs and triples through the fixed
boundary triple even when the retained fiber is far below `R(4,4)`.

At the opposite end from the sparse spectrum-hole branch, suppose the repair spectrum contains all four
residues.  Then the `2+2` table alone almost compresses the retained fiber by its eight boundary types.
For a fixed type `tau in {0,1}^3`, any boundary pair on which `tau` has equal bits forces the edge status
between two vertices of type `tau` to be the complement of the boundary-pair status.  If two such
boundary pairs have different statuses, the type has size at most one.  Otherwise the whole type class is
a clique or an independent set, and so has size at most `m` by outside-only maximality.  Similarly, for
two complementary one-hit types on a boundary pair, the bipartite graph between the two type classes is
forced to be either complete or empty.  Thus rich repair spectra leave only a bounded eight-type blow-up;
the genuinely flexible large-direction case is exactly the spectrum-hole case isolated above.

The resulting cap depends on the boundary triple, and the signed `3+1` rule removes one more type.  If
the triple has one or two edges, the all-equal types `000` and `111` receive inconsistent prescriptions
from two equal-bit boundary pairs, so they have size at most one; the other six types are homogeneous and
have size at most `m`.  The repaired residue matching the boundary triple's own degree pattern forbids
one of those six types by the `3+1` table.  Hence a full-spectrum direction with a nonconstant boundary
triple has size at most `5m+2`.

If the boundary triple is independent, every type is forced to be a clique by the `2+2` rules.  The
repaired residue `0` forbids type `000` by the `3+1` table, while the repaired residue `3` one-corner
rule bounds every type hitting at least one boundary vertex by `2`.  Thus the cap is `14`.  The triangle
case is complementary: type `111` is forbidden by the repaired residue `3`, and the repaired residue `0`
one-corner rule bounds every remaining type by `2`, again giving cap `14`.

Putting the spectrum-hole and full-spectrum bounds together gives a useful large-fiber normal form.  Let

```text
M_0=max(R(4,4), 5m+2).
```

If `|C_i|>M_0`, then `Rep(g_i)` has at most two residues, and it cannot contain either complementary
pair `{0,3}` or `{1,2}`.  Indeed, three residues contain one of those two pairs; `{0,3}` is Ramsey-small,
while `{1,2}` is pseudo-split and hence has size at most about `2m+5`.  Four residues are covered by the
augmented full-spectrum cap above.  Thus every very large exact-basis direction has one of the four
two-residue types

```text
{0,1}, {0,2}, {3,1}, {3,2}
```

or a singleton spectrum.  This is the corrected replacement for the earlier false singleton-rigidity
claim: large directions are not forced to have `Rep={d}`, but their repair spectrum is forced to be a
sparse transversal of the two complementary pairs.

The four two-residue spectra have a concrete hereditary meaning:

```text
{0,1}:  alpha(C_i)<=3 and C_i is 2K_2-free;
{0,2}:  alpha(C_i)<=3 and C_i is induced-C_4-free;
{3,1}:  omega(C_i)<=3 and C_i is 2K_2-free;
{3,2}:  omega(C_i)<=3 and C_i is induced-C_4-free.
```

The complement operation swaps the first and last cases, and swaps the two middle cases.  Therefore the
large exact-basis endpoint has been reduced to two sparse hereditary branches up to complement:
`alpha<=3` plus `2K_2`-free, and `alpha<=3` plus induced-`C_4`-free, together with the augmented
boundary-type constraints.  Any final closure of the exact-basis branch can target these two classes
rather than an arbitrary direction graph.

Two further reductions separate these branches.  First, the tempting chromatic shortcut for the
`2K_2` branch is false and must not be imported.  The proposed estimate

```text
chi(G) <= omega(G)+1        for 2K_2-free graphs with alpha(G)<=3
```

fails already for the join of two `C_5`'s: it is `2K_2`-free because its complement is the disjoint union
of two `C_5`'s and hence is induced-`C_4`-free; it has `alpha=2`, `omega=4`, and `chi=6`.  More generally,
the join of `k` copies of `C_5` has `alpha=2`, `omega=2k`, and `chi=3k`, so even an additive
`omega+O(1)` bound is impossible.  Thus the `{0,1}` and `{3,2}` branches cannot be closed by colouring
alone.  After complementing, the correct residual is a mod-`4` selector problem for induced-`C_4`-free
graphs with clique number at most `3` and independence number at most `m`; any successful closure must
use congruent-degree structure, not just chromatic structure.

One piece of congruent-degree structure survives in this corrected `2K_2` branch.  Let `H` be the
complement of a terminal `{0,1}` direction.  Then `H` is induced-`C_4`-free, has clique number at most
`3`, has `alpha(H)<=m`, and cannot contain an induced subgraph `F` with `Delta(F)<=2` and
`|F|>11m/5`.  The proof is the same degree-two path/cycle count: independent sets in `H`, induced
matchings in `H`, and unions of cycle components of `H` complement back to outside-only sets whose
degrees are constant modulo `4`.  Thus the failed colouring route is replaced by a terminal
induced-degree-two exclusion in an induced-`C_4`-free, `K_4`-free graph.

This residual is genuine: the augmented boundary tables do not by themselves remove it.  If the boundary
triple is a triangle and all retained vertices have the same boundary type `110`, then the signed mixed
rules for `Rep={0,1}` impose no extra same-type condition beyond the retained-only requirements
`alpha<=3` and `2K_2`-free.  In complement language, an arbitrary induced-`C_4`-free, `K_4`-free graph
with `alpha<=m` and the degree-two terminal exclusion can live in that single type.  Therefore the last
closure cannot be another finite boundary-type compression of the existing tables; it must either prove
a mod-`4` congruent-degree selector for this induced-`C_4`-free, `K_4`-free class, or import genuinely
global target-stability/maximal-witness information from the exact-basis construction.

Inside that remaining complement class there is still a useful triangle-anchor decomposition.  Let
`abc` be a triangle in `H`, and for every outside vertex `v` put

```text
tr(v)=N_H(v) cap {a,b,c}.
```

No outside trace has size three, since that would form a `K_4` with `abc`.  If two vertices have
incomparable nonempty traces `A` and `B`, then they are nonadjacent: an edge between them, together with
any `a in A\B` and `b in B\A`, induces the forbidden four-cycle
`v-a-b-w-v`.  Thus edges between nonzero trace classes can occur only along inclusions in the Boolean
poset on `{a,b,c}`.  In particular:

```text
P_ab, P_ac, P_bc  (the two-neighbour classes) are independent;
S_a, S_b, S_c     (the singleton-neighbour classes) are pairwise anti-complete;
S_a anti-joins P_bc, and cyclically.
```

Each singleton class `S_a` is itself triangle-free, because any triangle inside it would form a `K_4`
with the anchor `a`; it is also induced-`C_4`-free by heredity.  Hence the non-bipartite part of the
remaining residual can be peeled by anchored triangles into independent two-neighbour layers, three
pairwise anti-complete triangle-free/`C_4`-free singleton layers, and the zero-trace remainder.

The decomposition already carries two quantitative budgets.  The three two-neighbour classes are
pairwise anti-complete and each is independent, so

```text
|P_ab|+|P_ac|+|P_bc| <= alpha(H) <= m.
```

Likewise, because `S_a,S_b,S_c` are pairwise anti-complete, independent sets chosen in the three
singleton layers may be united; hence

```text
alpha(S_a)+alpha(S_b)+alpha(S_c) <= m.
```

If the singleton layers are bipartite, they contribute at most `2m` in total.  Thus after anchoring a
triangle, the only unbounded pieces not already controlled by `3m+O(1)` are the zero-trace remainder and
the genuinely non-bipartite triangle-free, `C_4`-free singleton layers.  This is the reduced selector
target inside the `{0,1}`/`{3,2}` complement branch.

There is one more terminal budget on those non-bipartite singleton layers.  In a triangle-free,
induced-`C_4`-free layer, every shortest odd cycle is induced.  Since the three singleton layers are
pairwise anti-complete, the union of one such odd cycle from each non-bipartite singleton layer is an
induced `2`-regular subgraph of `H`.  Therefore terminality gives

```text
sum length(C_a) <= m
```

over the chosen odd-cycle cores of the non-bipartite singleton layers; otherwise the same vertex set
complements back to a mod-`4` congruent outside-only set larger than `m`.  Thus the remaining
triangle-anchored task is now a bounded odd-core attachment problem in triangle-free, `C_4`-free layers,
plus the zero-trace remainder.

The attachment problem has its own normal form.  Let `F` be one of the triangle-free, induced-`C_4`-free
singleton layers, and let `C` be a shortest odd cycle of `F`.  Then `C` is induced, and every vertex
outside `C` has at most one neighbour on `C`.  Indeed, if an outside vertex sees two cycle vertices whose
shorter cyclic distance is `d`, then the two cycles through the outside vertex have lengths `d+2` and
`|C|-d+2`; one is an odd cycle shorter than `C` unless `d=1` or `2`, which are excluded by
triangle-freeness and induced-`C_4`-freeness.  Consequently the nonzero trace classes

```text
N_i={v outside C: N_C(v)={c_i}}
```

are independent, and adjacent trace classes `N_i,N_{i+1}` are anti-complete; otherwise
`v-c_i-c_{i+1}-w-v` is an induced `C_4`.  The zero-trace remainder is again triangle-free and
induced-`C_4`-free.  Thus every non-bipartite singleton layer peels to a shortest odd core of total
length budget at most `m`, independent pendant fibres on the core, and a smaller zero-trace layer.  The
only attachment edges still capable of carrying superlinear mass are between nonadjacent pendant fibres
of such odd cores; adjacent fibres and the core itself are already controlled by degree-two selectors and
independent-set bounds.

In fact most nonadjacent fibre pairs are forbidden as well.  If `v in N_i` and `w in N_j` are adjacent,
and the shorter cyclic distance between `c_i` and `c_j` is `d`, then the edge `vw` and the two arcs of
`C` give cycles of lengths `d+3` and `|C|-d+3`.  Since `C` is a shortest odd cycle, this is possible only
when one of the two cyclic distances is exactly `3` (for `|C|=5`, this is the same as distance `2` in
the opposite direction).  Therefore pendant-fibre edges live on the quotient graph

```text
i ~ j        iff        j=i+3 or i-3  on the cycle C.
```

This quotient has maximum degree two and fractional chromatic number at most `3`.  Because every
independent set of quotient positions gives an independent set in `F`, the total size of the nonzero
pendant fibres around the first odd core of a singleton layer is at most `3 alpha(F)`.  Summed over the
three pairwise anti-complete singleton layers of the triangle-anchor decomposition, these first-core
pendant fibres contribute at most `3m`.  The residual after removing them is again the iterated
zero-trace triangle-free, induced-`C_4`-free problem.

Second, the augmented boundary rules already give a `7m` cap for one C4-branch boundary shape.  If
`Rep(g_i)` contains `{0,2}` and the boundary triple `X_i` is independent, then type `000` is forbidden by
the repaired residue `0` `3+1` atom.  For every other boundary type, either some boundary pair has type
`00` (so residue `0` forces that type class to be a clique) or some boundary pair has type `11` (so
residue `2` forces that type class to be a clique).  Hence the seven remaining type classes are cliques,
each of size at most `m`, and `|C_i|<=7m`.  The complementary statement is: if `Rep(g_i)` contains
`{3,1}` and `X_i` is a triangle, then `|C_i|<=7m`.  Thus a direction of size greater than `7m` in the
`{0,2}` branch must have a non-independent boundary triple, and its complement branch must have a
non-triangle boundary triple.

For the remaining `{0,2}` branch, the boundary shape localizes the exceptional types.  Write the retained
type as a three-bit word on the boundary triple.

* If `X_i` has exactly one edge, say `xy` with isolated vertex `z`, then all type classes except
  `001` and `110` are cliques by the `2+2` rules for residues `0` and `2`; hence they have size at most
  `m`.  The two exceptional types are "hit only the isolated vertex" and "hit exactly the edge
  endpoints".
* If `X_i` is a path `x-y-z`, then the nonedge pair `xz` makes every type with equal `x,z` bits a clique,
  and type `101` is forbidden by the residue-`2` `3+1` atom.  Thus only the four types with unequal
  endpoint bits remain exceptional.
* If `X_i` is a triangle, the pair rules are only cross-type restrictions and no single type class is
  forced homogeneous by this argument; this is the hardest `{0,2}` boundary shape.

The complementary statements hold for the `{3,1}` branch after swapping clique/independent and
triangle/independent boundary shapes.  Therefore the unresolved sparse branch has a small, explicit
exceptional-type surface, not an arbitrary eight-type graph.

In the hardest `{0,2}` triangle-boundary shape the residual constraints are still explicit.  For each
boundary pair, the residue-`2` `2+2` rule says that two retained types whose bits on that pair are `10`
and `01` are anti-complete to one another.  Thus, on the cube of boundary types,

```text
10* anti-joins 01*,      1*0 anti-joins 0*1,      *10 anti-joins *01.
```

In addition, residue `0` gives `alpha(M_x)<=2` for each miss class `M_x={tau:tau_x=0}`, and residue `2`
says that for every `v in M_x`, the neighbourhood of `v` inside the hit class
`H_x={tau:tau_x=1}` is a clique.  Therefore the final triangle-boundary `{0,2}` problem is a finite
eight-type cube problem with prescribed anti-joins and one-corner clique-neighbourhood constraints.  Its
complement is the independent-boundary `{3,1}` cube problem.

The anti-join graph on the eight types is exactly the graph joining two bitstrings at Hamming distance
at least two.  Its two parity classes are four-cliques.  Since an anti-join clique of four nonempty types
would give an independent four-set in `C_i`, a terminal `{0,2}` triangle-boundary direction must omit at
least one even-parity type and at least one odd-parity type.  Hence at most six boundary types can be
nonempty in this residual cube problem.  The remaining obstacle is not support size, but bounding the
individual C4-free type classes that survive these anti-join and one-corner constraints.

The induced-`C_4` condition itself becomes a face condition on this cube support.  In any square face

```text
tau, tau+e_a, tau+e_b, tau+e_a+e_b
```

the two diagonal type pairs have Hamming distance two and are anti-complete.  Therefore any alternating
cycle using one vertex from each corner and edges along the four sides is automatically an induced
`C_4`.  Terminality forbids such a cycle in every cube face.  Equivalently, the four bipartite graphs
on the side pairs of every nonempty face form a `C_4`-free cyclic blow-up.  In particular, if three side
pairs of a face are complete and all four corner types are nonempty, the fourth side pair must be empty;
more generally, every face must miss the compatibility needed to close an alternating four-cycle.  This
face constraint is the next finite target after the support bound.

The support bound has a simple cube dichotomy.  Since the residual support omits one even and one odd
type, if six types remain then the two omitted types are either adjacent or antipodal.  If they are
adjacent, two square faces avoid both omissions and are full; the face constraint above applies.  If they
are antipodal, no square face is full and the six remaining types form the induced `6`-cycle in the
cube.  Thus the triangle-boundary `{0,2}` residual splits into:

```text
support size <=5;
support size =6 with adjacent omissions, hence at least one full constrained face;
support size =6 with antipodal omissions, a cyclic six-type blow-up.
```

The last case is the only cube-support shape not immediately exposing a full square-face `C_4` test.

There is an even simpler parity-count compression.  Distinct types of the same parity are pairwise
anti-complete.  Hence, if three types of one parity are nonempty, each of those three type classes must
be a clique: an independent pair inside one class together with one vertex from each of the other two
same-parity classes would be an independent four-set, contradicting repaired residue `0`.  Since no
clique in the outside chamber can exceed `m`, any parity side with at least three nonempty types
contributes at most `3m`.

Consequences:

```text
support size 6  =>  |C_i|<=6m;
support size 5  =>  three same-parity classes are cliques, leaving two opposite-parity exceptional classes;
support size <=4 =>  at most four type classes remain, with no three-type parity compression forced.
```

Thus the triangle-boundary `{0,2}` residual has been reduced from eight arbitrary type classes to either
a linear `6m` cap or at most two exceptional same/opposite-parity type classes beyond a clique-bounded
part.

In the support-five case the two exceptional classes have the same parity and are therefore anti-complete
to each other.  If both contained independent pairs, those two pairs would form an independent four-set.
Hence at least one exceptional class is itself a clique and contributes at most `m`.  Consequently
support five is reduced to a `4m` clique-bounded part plus a **single** possible non-clique type class.
Every such non-clique type class lies in some boundary miss class, so it has independence number at most
two and is induced-`C_4`-free.  Thus a support-five counterexample larger than `4m` would already contain
a single large type class with

```text
alpha<=2,        induced-C_4-free,        no clique larger than m,
```

and with no mod-`4` congruent induced subgraph larger than `m` by outside-only maximality.  This is a
strict one-type residual, smaller than the original eight-type cube.

Equivalently, complementing this one-type graph gives a graph `H` with no triangles and no induced
`2K_2`, and with independence number at most `m`.  The complement correction is important:
`C_4` is not self-complementary; its complement is `2K_2`.  For any selected set `S`,

```text
deg_G[S](v)=|S|-1-deg_H[S](v).
```

Thus `G[S]` has degrees congruent modulo `4` iff `H[S]` has degrees congruent modulo `4`.  The one-type
residual is therefore not a girth-five problem; it is a triangle-free `2K_2`-free selector.

This class has a simple structure.  If a connected component of `H` is bipartite, it is a chain graph
between its two colour classes, and each colour class is independent, so its order is at most `2m`.
If a component is non-bipartite, it contains an induced `C_5`; the `2K_2`-free and triangle-free
conditions force every outside vertex to be a false twin of one of the five cycle vertices, and force
complete joins between consecutive twin classes and anti-joins between nonconsecutive classes.  Hence
the component is a blow-up of `C_5`, say with class sizes `a_1,...,a_5`.

The blow-up case is internally capped by a three-consecutive-part selector.  For any consecutive triple
with capacities `A=a_i`, `B=a_{i+1}`, `C=a_{i+2}`, choose

```text
x<=A,  y<=B,  z<=C,        y = x+z [MOD 4],
```

with `x+z=A+C` and `y>=B-3`.  The induced subgraph on these three consecutive classes has endpoint
degrees `y` and middle degrees `x+z`, so all selected degrees are congruent modulo `4`, and its size is
at least `A+B+C-3`.  Terminality therefore implies

```text
a_i+a_{i+1}+a_{i+2} <= m+3        for every i [MOD 5].
```

Summing the five inequalities gives `3|H_j|<=5m+15` for each non-bipartite component `H_j`.  Globally
one also has the structural independence bound

```text
|H| <= (5/2) alpha(H) <= (5/2)m,
```

because bipartite chain components have order at most twice their independence contribution, while a
`C_5` blow-up satisfies `2|H_j|<=5 alpha(H_j)` by summing the five nonconsecutive-pair inequalities.
Thus the former one-type residual is replaced by an explicit triangle-free `2K_2`-free
structure theorem, plus the sharper three-consecutive-part selector inside every non-bipartite
component.

For support at most four, either the support contains a square face, in which case the face `C_4`
condition applies, or it is a forest subgraph of the cube.  The forest-support case is again a bounded
tree of type classes with anti-complete nonedges; any parity side of size three is clique-bounded by the
previous paragraph.  Hence the only genuinely nonlinear residue of the triangle-boundary `{0,2}` branch
is a single C4-free, `alpha<=2` type class or a small cube-forest of at most four such classes.

The cube-forest alternative is not four-dimensional.  Distinct same-parity classes are anti-complete, so
two non-clique classes of the same parity would supply two independent pairs and hence an independent
four-set.  Thus at most one same-parity class on each side can be nonlinear.  If the two surviving
nonlinear classes have opposite parity but Hamming distance three, they are also anti-complete and the
same independent-pair argument applies.  Therefore a forest support has at most two nonlinear type
classes, and if there are two then they are adjacent in the cube; all other supported types are cliques
of size at most `m`.

At first this leaves only one adjacent-type residual.  If the adjacent types share a zero
coordinate, their union lies in a single miss class `M_x`, so the whole union has independence number at
most two; since the ambient direction is induced-`C_4`-free, complementing this union gives exactly the
same chain/C5 selector already isolated above.  If the adjacent types share no zero coordinate, then
up to symmetry the pair is `111`--`110`: the lower type lies in one miss class, and every vertex of that
lower type has a clique neighbourhood in the all-hit type by the one-corner rule.  Thus the
support-at-most-four branch reduces to the one-type chain/C5 selector or to this top-edge incidence
problem, plus at most `2m` clique-bounded spill.

The top-edge incidence problem also collapses to one-type selector surfaces.  Write the lower type as
`A=110` and the all-hit type as `B=111`.  If `A` contains an independent pair `a_1,a_2`, then each
`N_B(a_i)` is a clique and hence has size at most `m`.  The common non-neighbour set
`B\(N_B(a_1) union N_B(a_2))` must also be a clique: two nonadjacent vertices there, together with
`a_1,a_2`, would be an independent four-set, forbidden by repaired residue `0`.  Hence `|B|<=3m`.
The only unbounded part is then `A`, which is an `alpha<=2`, induced-`C_4`-free one-type instance and
therefore complements to the chain/C5 selector above.  If `A` has no independent pair, it is a clique
and contributes at most `m`; the only unbounded part is `B`, an `alpha<=3`, induced-`C_4`-free one-type
instance, equivalently after complement a `2K_2`-free, `K_4`-free selector with the same
induced-`Delta<=2` exclusion recorded for the corrected `{0,1}` branch.  Here a genuine chromatic import
is available: Wagon's χ-bound for `2K_2`-free graphs gives

```text
chi <= binom(omega+1,2).
```

Since the complement has `omega<=3` and independence number at most `m`, this all-hit case has size at
most `6m`.  Thus small cube-forest support introduces no new two-type obstruction and is linearly capped
apart from the already isolated chain/C5 one-type selector.

The only way three clique-bounded spill classes can coexist with a nonlinear class is the cube-star
shape with the nonlinear type at the centre and three same-parity leaves.  This star has an additional
Hall-type restriction.  Let `T` be the centre type and let `L_1,L_2,L_3` be the three clique leaves,
which are pairwise anti-complete.  For every independent pair `a,b in T`, at most one leaf can contain a
vertex nonadjacent to both `a` and `b`; otherwise two such leaf vertices, together with `a,b`, would form
an independent four-set.  Equivalently, for at least two leaves `L_j` one has

```text
L_j = N_{L_j}(a) union N_{L_j}(b),
```

and each of the two neighbourhoods is a clique by the one-corner rule whenever the centre is a miss for
the corresponding coordinate.  Thus the last possible `3m` spill is not arbitrary: every independent
pair in the nonlinear centre two-covers at least two leaves by clique neighbourhoods.  This constraint
is extra slack on top of the crude `3m+5m/2` estimate below, not a new obstruction.

Quantitatively, the corrected one-type bound is already enough to cap the whole triangle-boundary
`{0,2}` cube branch linearly below `7m`.  Support six contributes at most `6m`; support five contributes
at most `4m+(5/2)m=13m/2`; and support at most four contributes at most `3m+(5/2)m=11m/2`, with the
top-edge subcase capped by `6m` as above.  Together with the independent/one-edge/path boundary caps,
every `{0,2}` direction, and by complement every `{3,1}` direction, has size at most `7m+O(1)` in the
augmented exact-basis branch.  The finite cube residual is therefore closed; the only large-fiber
hereditary surface still not linearly closed is the corrected `{0,1}`/`{3,2}` complement selector:
induced-`C_4`-free, `K_4`-free, independence at most `m`, and no large induced degree-two regular
selector.

The retained-only subcase is the old four-copy obstruction.  Let `C_i` be all vertices of `C` with
old-vector `g_i` in the exact basis model.  Every four vertices of `C_i` form an old-balanced atom with
the same old-neighbourhood residue `omega(g_i)`.
Hence any induced regular four-set in `C_i` of degree

```text
d_i=r-omega(g_i)        [MOD 4]
```

closes the proof.  The exact-extremal terminal condition is therefore

```text
no C_i contains an induced 4-vertex d_i-regular graph.
```

This is a much smaller finite obstruction, but it is still not contradictory by itself: forbidding one
of the four induced regular graphs on four vertices permits large graphs.  The remaining work in the
exact basis branch is to combine these direction-wise forbidden-pattern constraints with either the
global maximum property of `W` or with a non-basis perturbation/import.

The direction-wise obstruction should not be treated as independent.  If `S_i subset C_i` is a
four-vertex old-balanced block in direction `g_i`, then its internal defect is

```text
a_i(s)=r-omega(g_i)-deg_{S_i}(s).
```

A union of several such blocks `S=union_i S_i` is old-balanced, and it closes exactly when the
cross-block degrees repair these defects:

```text
sum_{j != i} deg_{S_j}(s)=a_i(s)        for every s in S_i.
```

Thus exact-basis closure is an interacting four-block problem.  A single block may avoid the required
regular type, but a collection of blocks can still append if their cross-edges supply the missing
pointwise corrections.  This is the basis-model version of the earlier block-interaction normal form;
the remaining extremal proof must force either one regular four-block or a mutually correcting family
of nonregular four-blocks.

There is a local countermodel to any atom-only exact-basis closure.  Suppose every feasible direction
has required residue `d_i=0`, each direction fiber is a clique, and there are no cross-edges between
direction fibers.  Then every old-balanced subset must take a multiple of four vertices from each
direction, and every selected vertex in such a clique block has internal degree `-1 mod 4`, not `0`.
So no same-direction block and no disjoint union of such blocks closes.  This does not contradict the
global theorem, because the construction ignores how the `h_0`-class was produced and may violate
maximum-witness constraints elsewhere.  But it proves that the exact basis branch cannot be finished by
the finite atom catalogue alone; it must import additional information from the global maximum
hypothesis or from a non-basis exchange.

Compressing the exact-basis branch also shows why this is not yet a smaller theorem.  Choose a
four-block `S_i` in each direction and view it as a supervertex carrying a four-coordinate defect vector
`a_i`.  Between two supervertices the graph supplies a `4 by 4` adjacency matrix; selecting a family of
supervertices asks that the row sums of the selected cross-matrices equal the prescribed vector `a_i`
for every chosen block.  This is again a fixed-modulus induced row-sum selector, now on bounded-size
vector labels rather than scalar vertex labels.  Thus the exact-basis reduction is useful only if one
also uses the special origin of the matrices from boundary triples or the maximum-witness constraint;
as an abstract block problem it simply repackages the original self-layer obstruction.

There is, however, a second maximum-witness constraint that is independent of old-balance.  Since `W`
was chosen with maximum cardinality, no subset of the outside class `C` itself may induce congruent
degrees modulo `4` on more than `m` vertices.  In exact-basis language, if one chooses regular
same-direction blocks `P_i subset C_i` with internal residue `q_i`, then an outside-only contradiction
is obtained whenever a family of such blocks satisfies

```text
q_i + sum_{j != i} deg_{P_j}(v) = Q        for every v in P_i
```

for one common residue `Q`, and has total size greater than `m`.  This is weaker than appendability
because it ignores old coordinates entirely, but it is a genuine extra obstruction.  For example, the
local no-cross model with many clique direction blocks cannot be terminal: four vertices from each of
more than `m/4` clique directions already give an outside-only congruent witness of residue `3`.  Thus
any exact-basis counterexample must simultaneously block appendable defect repair and all large
outside-only block selections.  The latter is the missing global information in atom-only local
countermodels.

The same outside-only constraint applies already to the maximal boundary `X`.  Since
`|X|` can be as large as `3(m-1)`, a terminal boundary is a `1/3`-critical obstruction for the
ordinary mod-`4` congruent-degree selector: no `Y subset X` with `|Y|>m` may have all degrees in
`G[Y]` congruent modulo `4`.  In the exact Davenport model this says that the family of boundary
triples `X_i={x_{i,1},x_{i,2},x_{i,3}}` admits no selection of subpatterns whose total size exceeds
`m` and whose internal-plus-cross degrees are constant.  For a subpattern `P_i subset X_i`, write
`q_i(v)=deg_{P_i}(v)` inside the triple.  A boundary-only forbidden selection is precisely

```text
q_i(v)+sum_{j != i} deg_{P_j}(v)=Q        for every selected v in P_i,
sum_i |P_i|>m.
```

This is weaker than the append atom equations but uses the full `3m` reservoir.  In particular, a
terminal exact-basis boundary cannot contain a large collection of cross-isolated independent triples
or cross-isolated triangle triples of one type: selecting those whole triples would give an outside-only
residue-`0` or residue-`2` witness of size greater than `m`.

The boundary side has one more structural feature: `X` is zero-sum-free in
`C_4^(m-1)` and has length at most the exact Davenport extremal value `3(m-1)`.  Hence the terminal
case splits naturally into two regimes.

1. If `|X|` is substantially below `3(m-1)`, then `B=C\X` is substantially larger than the current
   `m/8` lower bound.  This extra retained mass should be spent on the block-interaction equation above.
2. If `|X|` is near `3(m-1)`, inverse Davenport structure for `C_4^(m-1)` should make `X` close to a
   basis sequence with three copies of each order-`4` generator.  In that basis-like case, balanced
   imports from `X` are extremely constrained but explicit, so the exchange equations become finite
   coordinate moves.

Thus a plausible final route is now precise: prove a stability/inverse-Davenport boundary theorem
adapted to the value-coupled exchange.  The required input is not another zero-sum existence theorem;
existence is already exhausted.  It is an inverse theorem for zero-sum-free boundaries together with
the `theta=H-r` co-cut labels.

There is also a minimal-block version of the same endpoint.  Decompose the old-balanced retained set
`B` into minimal nonempty old-balanced blocks.  For such a block `S`, no proper nonempty subset of
`S` has old-coordinate sum zero.  The pure-discard exit for `S` is exactly

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S}=H-r       for all s in S.
```

If this fails, then any successful repair involving vertices of `S` must import a nonempty
`Z subset X` and export a set `Y subset B` whose old-coordinate sum matches `Z`.  Thus a terminal
counterexample is equivalently an exchange-stable family of minimal zero-sum blocks against a
zero-sum-free boundary.  This is a finite local problem in the group `C_4^(m-1)` plus the graph labels:
minimal zero-sum blocks supply the only discard moves, and zero-sum-free boundary subsets supply the
only imports.

There is a complementary one-large-class coloring view which isolates the same obstruction without
requiring a full coloring theorem.  For a labelled graph `(H,alpha)` and a color
`gamma:V(H)->Z/4Z`, call `v` pre-satisfied if

```text
gamma(v) == alpha(v)+deg_{H \ gamma^{-1}(gamma(v))}(v) [MOD 4].
```

For a uniformly random four-coloring, every vertex is pre-satisfied with probability exactly `1/4`:
after the colors on the closed neighbourhood of `v` are fixed up to a common cyclic shift, exactly one
of the four shifts satisfies the displayed congruence.  Hence some color `c` has a pre-satisfied fiber
`S_c` of size at least `|H|/16`.  If `U_c=gamma^{-1}(c)\S_c` has constant degree modulo `4` into
`S_c`, then `S_c` itself is a valid retained class, because moving `U_c` from "same color" to
"outside" adds the same correction to every vertex of `S_c`.

Thus the last obstruction is not failure to find many locally correct vertices; the random
preselector always finds them.  It is precisely the same self-layer contamination: same-color
unsatisfied vertices may have nonconstant degree into the pre-satisfied fiber.  A final proof can
therefore be phrased either as the packet replacement theorem above or as a contamination-removal
lemma for a large pre-satisfied fiber.

One stronger way to prove it would be a global fixed-point coloring
`gamma : V(H) -> Z/4Z` satisfying

```text
gamma(v) == alpha(v) + deg_{H \ gamma^{-1}(gamma(v))}(v) [MOD 4]
```

for every vertex `v`; the largest color class would then give the selector with loss `4`.  This
stronger coloring statement is false.  On the path `a-b-c` with labels
`alpha(a)=0`, `alpha(b)=0`, `alpha(c)=1`, the leaf equations force
`gamma(b) != 1` from `a` and `gamma(b) != 2` from `c`.  If `gamma(b)=0`, then `c`
has color `2`, and the center sees one or two differently colored leaves, never `0`.  If
`gamma(b)=3`, both leaves are differently colored, so the center sees `2`, again not `3`.
Thus no such fixed-point coloring exists.  Any co-degree route, if used, must either stay in the
constant-`alpha+deg_H` special case above or prove a one-large-class theorem rather than partitioning
all vertices into valid classes.

Even the constant-sum special case should not be upgraded to a full four-class partition.  In the
first-bit application the co-degree equation becomes, after writing `alpha(v)+deg_H(v)=lambda`,

```text
gamma(v) + deg_{H[gamma^{-1}(gamma(v))]}(v) == lambda [MOD 4].
```

Thus a full coloring would partition `V(H)` into four classes whose induced degree residues are
`lambda, lambda-1, lambda-2, lambda-3`.  This would be much stronger than the one-class selector.
Balister--Powierski--Scott--Tan's random-graph partition count rules out treating this as a
deterministic lemma: for `q=4` and one part assigned to each residue, the number of such four-part
partitions of `G(n,1/2)` has a finite Poisson limit, so with positive limiting probability there is
no such partition at all.  Therefore the surviving endpoint is genuinely partial:

```text
find one class W of size at least |H|/16 with deg_{H[W]} constant modulo 4,
```

or equivalently find a partial anti-degree coloring covering at least `|H|/4`, from which the largest
of the four residue classes has size at least `|H|/16`.  The full-cover version is not an admissible
replacement for the terminal self-layer lemma.

The Eulerian-orientation formulation is also exact but not linear enough to close the gap.  If an
induced subgraph `J` is even and is given an Eulerian orientation, then for any `S subset V(J)` with
`J[S]` even,

```text
deg_{J[S]}(v)/2 == out_S(v) == in_S(v)        [MOD 2].
```

Therefore `J[S]` has all degrees congruent modulo `4` iff the inherited orientation has both
`out_S(v)` and `in_S(v)` constant modulo `2` on `S`.  In the directed bipartite double-cover this asks
for a large **diagonal** subset `S` whose left-degrees into the right copy of `S` and right-degrees from
the left copy of `S` have the same constant parity.  Ordinary bipartite parity theorems choose two
unrelated sides; they do not enforce this diagonal equality.  Thus Eulerian orientation converts the
mod-`4` selector into a diagonal in/out parity selector, not into a one-sided linear theorem.

Equivalently, fix an Eulerian orientation and let `M` be its zero-diagonal adjacency matrix over
`F_2`.  A sufficient first-bit target is:

```text
find S with |S|>=n/32 and a bit c such that
sum_{u in S} M_{v,u}=c and sum_{u in S} M_{u,v}=c       for every v in S.
```

Then every `v in S` has `deg_{G[S]}(v)=2c [MOD 4]`.  This principal-submatrix row/column parity
selector is the exact diagonal matrix form of the orientation route.  A bipartite theorem that finds
large unrelated row and column sets with constant parities is insufficient unless it also identifies the
two sets.

There is also a tempting internal refinement scheme that explains exactly where the missing constant
is lost.  Start from an even graph `E`, choose a largest class `S1` of the total degree modulo `4`
(loss `2`), then refine by the degree into the first discarded layer `L0=V(E)\S1` (loss `4`), then by
the degree into the next discarded layer.  Each previously exposed layer has constant contribution on
all later retained sets, so if the process could be stopped after two exposed layers it would give the
desired `1/32` selector.  The obstruction is the last self-layer: after retaining `S3`, the complement
contains the new layer `S2\S3`, whose contribution to vertices of `S3` has not been synchronized.  Thus
the layer-refinement argument proves only a conditional route: close a terminal self-layer lemma, or
accept an additional factor.  It is not, by itself, the loss-32 theorem.

Adding more exposed layers does not remove this defect.  At stage `i`, the refinement can make
`deg_{S_i}(v)` constant only on a later set `S_{i+1}`; the desired output would be `S_{i+1}`, whose
own degree still subtracts the fresh layer `S_i\S_{i+1}`.  Thus every finite iteration is one
self-layer behind.  The missing lemma is not a bookkeeping issue but the exact co-cut problem:
turn a set whose degrees into the previous chamber are synchronized into a set whose internal degrees
are synchronized, without paying another factor.

The Scott--Hunter bipartite theorem can only repair this terminal layer if the last obstruction has
already been reduced to a genuinely bipartite chamber, i.e. no uncontrolled edges remain inside the
retained side.  In the principal-submatrix problem the terminal layer still has its own internal
adjacency, and those internal edges are exactly what changes the row sums after the final residue class
is selected.  So the current terminal gap is not a hidden application of the bipartite `1 mod k`
theorem; it is the co-cut synchronization problem for the self-layer plus its newly discarded
complement.

The recent prescribed-parity extension of Ferber--Krivelevich has the same limitation.  It gives a
linear induced subgraph with vertex-wise prescribed parity, and Gallai gives even/even or even/odd
two-partitions, but both statements live only over `F_2`.  They can force the first bit of the selected
degrees, not the carry bit `binom(deg,2) [MOD 2]`.  Its directed partition characterization also shows
why the Eulerian-orientation route cannot be reduced to ordinary out-parity: even an Eulerian directed
triangle has no even/even out-degree partition.  Thus the missing input remains genuinely diagonal and
modulo `4`.

Nor does iterating Gallai's even/even partition close the loss.  Starting from an even graph and always
keeping the larger even child gives a nested even induced graph of size at least `n/32` after five
steps.  However the leaf is only even; its degrees can still split between `0` and `2 mod 4`.  The
successive sibling layers have even degree into the current leaf, but their half-degree parities are not
synchronized, so the carry coordinate `binom(deg,2) [MOD 2]` remains free.  Thus recursive Gallai
partitioning proves only first-bit parity regularity at the required scale, not the mod-`4` congruence.

The centered-pair hypergraph formulation also explains why a one-coordinate hypergraph odd-degree
theorem is not enough.  Form the 3-uniform hypergraph `K` whose edges are triples `{v,x,y}` with
`vx` and `vy` edges of the original graph; then the degree of `v` in `K[W]` is exactly the carry
`binom(deg_W(v),2) [MOD 2]`.  A large induced subhypergraph of `K` with all degrees odd would
synchronize the carry coordinate on some support, but it says nothing about the graph-degree parity
`deg_W(v) [MOD 2]` on that same support.  Conversely Gallai synchronizes graph parity but not the
3-uniform carry.  The needed external input would have to be a **vector-valued** induced hypergraph
parity selector for the pair `(graph degree parity, centered-pair degree parity)` with a constant at
least `1/32`; an ordinary all-odd 3-uniform theorem supplies only one linear coordinate.

A bounded modular partition would be a sufficient but currently unavailable shortcut.  If every graph
could be partitioned into at most `K` vertex classes whose induced degrees are constant modulo `4` in
each class, then the largest class would give an arbitrary-graph `1/K` selector, and with `K<=16` would
close the even loss-`32` route after the total-degree-class reduction.  But this is stronger than the
present one-large-class target: even the deterministic Caro--Krasikov--Roditty problem asking for a
bounded number of parts with all induced degrees divisible by a fixed `q` is open, while the
Balister--Powierski--Scott--Tan random-graph count only describes random partitions and shows that
some fixed `q`-part residue patterns fail with positive limiting probability.  Hence a bounded
partition theorem should not be imported as if proved; the target must remain a partial selector.

Combining Lemmas 10.4b and 10.4e--10.4j reduces the large-gap positive fixed-witness dyadic lift in the
saturated proof pipeline to this first-bit modulus-four target:

```text
0 < j,
HasFixedModulusWitnessOfCard G ((2^j)^6*m) (2^j)
  => HasFixedModulusWitnessOfCard G m (2^(j+1)),
```

under the Ramsey-window and large-gap hypotheses of Lemma 10.4.  The proof splits into the open `j=1`
modulus-four fixed-loss target, `j>=2` and `2^j>=m` by terminal regularization, and `j>=2` with
`2^j<m` by the saturated affine-pair/split-marker route above.

### Conditional Theorem 10.5: dyadic threshold

There is a constant `A` such that

```text
T(2^r) <= 2^(A(r+1)^2)
```

for all `r`.

### Proof

Assume the first-bit fixed-loss theorem

```text
HasParityToModFourLoss64FixedWitnessLift.
```

Start from the parity base and use the positive dyadic lift at each positive
dyadic step to obtain a fixed-modulus witness at modulus `2^r` whose size is polynomial in `2^r` on the
terminal scale.  Lemma 10.4 plus the assumed first-bit theorem supplies the remaining large-gap window;
the other windows are closed by the small-target, finite-base, arithmetic-empty, or Ramsey-large
reductions.  Lemma 10.2 then regularizes the terminal witness.
Equivalently, the cumulative dyadic cost has the form

```text
prod_(i=1)^(r-1) (2^i)^C = 2^(C r(r-1)/2).
```

Multiplying by the terminal target size `2^r` and increasing the constant gives

```text
T(2^r) <= 2^(A(r+1)^2).
```

### Conditional Corollary 10.6: global conclusion

```text
F(n) / log n -> infinity.
```

### Proof

Combine Conditional Theorem 10.5 with Lemma 1.1.

## 11. Final status

What is proved here:

1. terminal modular congruence implies regularity;
2. dropped-tail constancy modulo `q` implies terminal regularity;
3. the dyadic obstruction `tau_m` equals the aggregate complement-orbit carry `beta_m`;
4. a nonzero `beta_m` yields a cut and then a q-marker;
5. no-split, frozen, one-splitter, and static split-quotient q-marker exits are closed;
6. the canonical saturated analogue of q-marker provenance/support-decrease holds in `FR^sat`;
7. saturated descent is sufficient for the terminal proof;
8. saturated q-markers are excluded;
9. the large-gap dyadic residual is reduced to a first-bit modulus-four fixed-loss target plus two closed
   higher-bit parts: the high-modulus range `2^j >= m` by terminal regularization and the
   `j>=2`, `2^j<m` slice by the saturated affine-pair/split-marker route;
10. conditional on the first-bit target, the dyadic threshold is `T(2^r) <= 2^(O(r^2))`;
11. conditional on the first-bit target, `F(n)/log n -> infinity`.

What remains open:

```text
the original path-only Theorem G, equivalently path-saturation comparison with FR^sat;
HasParityToModFourLoss64FixedWitnessLift, or an equivalent parity-to-mod-four fixed-loss theorem;
the stronger q >= 4 terminal-cascade bridge, which is not needed for terminal regularization.
```

What is not used:

```text
equivalence with arbitrary nonminimal extrinsic path choices.
```

Such paths can avoid saturated squares by fiat.  The intended path-only first-return construction is
support-minimal and lexicographically first, but Open target 8.3 has not yet supplied a non-circular
comparison proof for that path.  The global argument above does not use that comparison; it runs terminal
descent directly in `FR^sat`.

For that external unsaturated comparison, the historical normal form is adjacent-slice admissibility,
equivalently minimal
transverse-breaker admissibility: an ambient high-error breaker of a protected packet must either pass
the one-coordinate interval tests and become an ordered boundary row, or its first dirty failed row must
coalesce into a fixed frame or give a strictly smaller transverse breaker.  The one-corner / silent-edge
route has been sharpened to candidate-switching gatedness: fixed-candidate quartic blockers are absent
by interval arithmetic, but non-gated witness packets can still cycle without a common point.  Outgoing
anti-Horn/no-split and filled-overlap pair-injectivity are formal after silent-edge exclusion,
repair-fiber cubicality, and square-breaker routing; their failures reduce back to a square-transverse
breaker.  In the original host-frontier names, `host-silentedge128`, `host-opppair123`, and
`host-orient115` are therefore three conditional views of the same support-local square-breaker.  The
gated-Helly route has the same status: its exact square implication is
`00,10,01 in Omega => 11 in Omega`, whose first failure is the positive-AND row.  The
pointwise sign route has been sharpened to no shared-slack rows: a positive `0001`
coordinate is one row of a full shared-slack set `R` with `|R| = 0 mod q`.  The host absorption/Hall
route also collapses to pointwise one-defect fibers and then to compatible-transversal gatedness.  The
selection part now splits into large-marker no-q-jump plus exact-marker two-splitter routing: all
no-split, low-universal no-second, high-null no-second, and singleton-lift exact branches are closed,
but the marker-splitting two-splitter / zero-sum packet atom still needs first-return packaging.  The
same endpoint can be stated as admissible-module primeness or first-return packet-primality: an ambient
splitter of a packet module must be transported into the admissible first-return package, or else create
a smaller admissible module/local exit.  Minimal failure of this principle has a two-splitter crossing
normal form: the ambient split and the first failed ordered row cross both of each other's sides, with no
first-return-complete quadrant.  More sharply, the four quadrants form a primitive `2x2` residue circuit:
all realized row, column, quadrant, and packaged diagonal subunions have nonzero residue, while the total
carrier has residue `0 mod q`; such circuits exist arithmetically even for dyadic `q>=4`, so a realized
diagonal would have to be obtained from provenance, not residue counting.  They can even be made
clique-coherent in the static quotient for dyadic `q>=8`, so same-trace and roof/twin closures do not
see them; the `q=4` static base is already in the small exact-marker catalogue.  A
2-adic pairing descent only produces a genuine smaller carry after the paired quadrants are realized in
one first-return package; equivalently, the row, column, and diagonal pairings form a three-pairing
triality whose irreducible form is package-coordinate monodromy.  A Boolean/XOR diagonal row would close
this triality, but vertex neighborhoods are not closed under symmetric difference; repair-fiber
cubicality is exactly one of the equivalent missing inputs.  In the same language, the missing theorem
is binary circuit elimination for realized admissible boundary-row traces on the primitive carrier; a
minimal failure of that elimination is again the absent diagonal corner of the `0001` square.  This
elimination is not forced by the abstract reduced trace axioms: the two crossing splitters with the
diagonal omitted form a consistent trace system unless graph-specific first-return history is used.
The product-firewall containment argument is fully closed when the dirty shared-slack set lies in one
proper breaker side; the remaining large-marker case is exactly a simultaneous-wall antichain in which
outside packet pieces reassemble the whole marker at the same first wall.  Such an antichain can have
primitive residues `1,1,1,q-3`, so a mere ordering of packet pieces is not enough; the ordered piece must
also be a realized complete carrier.  After removing common-divisor residue shadows, the antichain can
be assumed primitive, `gcd(q,a_i)=1`; for dyadic `q` this forces odd packet pieces, but they still close
only when first-return history realizes a proper subcarrier.  Minimal zero-sum sequence bounds give at
most `q` simultaneous pieces, but do not make a formal zero-sum subfamily first-return-complete; in the
maximal length-`q` atom the residues are all one generator after unit scaling, so residue heterogeneity
has vanished entirely.  At the lowest 2-adic layer, a dyadic survivor has no realized
first-return-complete odd-pair carrier; this is the large-marker analogue of the absent XOR diagonal.
Any realized first-return cut of the odd layer is forced to be odd/odd; two crossing odd/odd cuts are
exactly the primitive parity circuit.
If realized odd cuts do not cross, they form a laminar odd chain whose even intervals close only when
those intervals are realized complete carriers.  Consecutive laminar cuts in one peeled package would
realize such an even interval, so a laminar survivor must change package at every adjacent step; the
first adjacent package change is again the same pair-status `0001` common-package failure.
Equivalently, Theorem G has been reduced to primitive antichain realization: find a proper realized
zero-sum subcarrier, a binary circuit-elimination row, or a local exit.  In dyadic language this means
crossing odd-cut elimination, laminar even-interval realization, or the first adjacent laminar
common-package failure.
Iterating packet primeness normalizes the survivor further to a directed replacement cycle:
packet sides replace one another with total residue `0 mod q`, but no proper first-return-complete arc,
frozen packet, local exit, complete quadrant, or realized diagonal.  The common-package form has also
been reduced coordinatewise: once the visible median data are fixed, only binary pair-status can differ,
and its shortest change is exactly the successor-side `0001` square.  In the replacement-cycle language,
the two-cycle is only the balanced `0101/0011` flip when both arcs live in one package; a surviving
two-cycle has the same first failed common-space `0001` edge.  Ordinary median convexity and unary
monotonicity do not exclude this row; the needed statement is a first-return pair-status
anti-Horn/submodularity law or support decrease for its shared-slack carrier.  In Möbius form, `0001`
is the only positive row and `0111` is the only negative row; a mass cancellation helps only after the
negative row and both of its unary leaks are in the same peeled package; equivalently the identity
`0001+0111=0101+0011` must be realized in one raw space.  Iterating failed compensator routing gives a
Möbius-leak cycle whose scalar mixed mass cancels but whose rows have nontrivial package holonomy; a
trivial holonomy cycle telescopes in one raw space, while a shortest nontrivial holonomy loop is again a
`0001` square.  Since a globally fixed pair-status predicate has zero closed-loop sum, this holonomy is
not scalar; it is package-coordinate monodromy.  Higher-rank monodromy is not a separate endpoint:
after quotienting fixed-trace, unary, and false-clone kernels, the first moved coordinate of a shortest
nontrivial loop is again a rank-one successor-side `0001` row, with the reverse orientation represented
by the `0111` compensator plus its two unary leaks.  A shortest nontrivial monodromy loop is chordless:
any common-package chord splits it into shorter loops, and a positive/negative adjacent pair either
telescopes through `0001+0111=0101+0011` in a proper common package or leaks a smaller one-corner
failure.  Hence the final monodromy survivor is a sign-coherent simple cycle of adjacent package-change
`0001` edges.  Its consecutive packet residues form a cyclic interval atom, so the cycle has at most
`q` package changes; only a provenance theorem can turn such an interval atom into a realized proper
subcarrier.  The moved coordinate orbit is anonymous to every admissible row; otherwise the first
distinguishing edge is a smaller one-corner package failure.  Therefore nontrivial monodromy is the same
as admissible-module primeness failure for this anonymous coordinate orbit: without an ambient breaker it
is a prime-shell module/local exit, and with one the breaker must be routed into first-return
provenance.  Restricting such a breaker to the cyclic order leaves only a consecutive interval face or a
crossing-cut primitive circuit face; choosing a breaker with the fewest cyclic sign changes makes this a
two-transition interval atom or a four-or-more-transition primitive circuit with no realized diagonal.
Both require the same promotion/realization input, and an abstract equal-residue cycle with only constant
admissible rows shows that cyclic arithmetic alone does not supply it.  Thus the final
obstruction is the anchored
first-return `0001` / positive-AND square, or the same exact q-marker / no-q-jump carrier in which first
failed rows can remain fully skew on the same support.  The weighted dyadic two-child carry reduces to
this same package-equality/support-decrease input.  The binary skew-ladder version has the identical
adjacent-turn test: an opposite-side turn in one package is a zero raw packet, and a same-side turn in
one fixed frame is a local same-trace/twin exit; therefore every surviving ladder edge is another
adjacent package-change `0001` edge.  Omni-saturating the carrier collapses any longer active monodromy
cycle to a bipartite module/local exit, so the final saturated carrier is again a single active pair.
Equivalently, the final saturated endpoint is a sign-coherent q-divisible separator bag over one active
pair; proving that an ambient breaker of this bag promotes to a first-return side, a complete smaller
bag, or a local exit is exactly the missing support-decrease step.  A reduced trace model with only
constant admissible rows and one ambient splitter shows that this promotion cannot be inferred from
prime separation and congruence alone.  The breaker may moreover be sign-normalized: constant-on-pair and
opposite-sign breakers fall to local/common-package cases, so the surviving breaker is a same-sign
separator row outside the admissible package.  Its two sides carry modular force only after one side is
known to be a complete transported shared-slack bag; choosing such a breaker with minimum side reduces
the noncrossing branch to a singleton-side promotion gap, while crossing breakers are the primitive
`2x2` circuit.  The singleton-side gap is stable under first-failed-row iteration: all departures close
locally, contradict minimum side, or form the primitive circuit, so the survivor is a high-error
same-sign isolator loop on one row.  Distinct isolators either coalesce by the same-trace/twin catalogue
or regenerate the same square-transverse breaker, so after local quotienting the final normal form is a
single high-error isolator self-loop.  Pure same-defect token loops close by the prime-shell
same-trace/false-clone argument, so this self-loop is exactly the defect-switching fully skew square.  If
that square is seated with the singleton isolator as its first axis, every row outside the isolated
singleton has zero mixed second difference, so the complete slack bag is contained in a sub-`q` side and
the low-set congruence kills it.  Thus the historical path-only proof stops at common-frame ordered
axis-lock: the external comparison task is to prove that first-return transport cannot drift the
defect-switching square to an incomparable first axis without a local exit or primitive `2x2` circuit.
The in-frame version of this axis-lock is closed.  Remembering the first-failed-row map only as an
abstract routing automaton still allows a one-state singleton-isolator loop, so the remaining external
comparison task is single-turn common-frame gluing for consecutive dirty axes, or equivalently proving
that the first package-change edge already carries a complete smaller marker/local exit.  In the
hidden-median form this is the two-fiber
single-flip overlap lemma:
nonempty `Omega_10` and `Omega_01` must have a common `0111` witness; the lone surviving abstract table is
the mixed non-overlap pair `{0101,0011}`.  Equivalently, the remaining theorem is binary pair-status
constancy on the one-corner median fiber; failure of that constancy is again the successor-side `0001`
shared-slack marker.  Scalar wall-order potentials do not help: their edge signs are coboundaries and
have zero square circulation, while the forbidden `0001` row is a same-row two-face curvature that exists
only after the two successor increments have been placed in one peeled package.  Equivalently,
common-frame gluing is commutation of the two successor package identifications on the active binary
coordinate; a nontrivial commutator is exactly the `{0101,0011}` non-overlap table, or after marking the
first package leak, the positive `0001` row.  Finite commutator order gives only an anonymous coordinate
orbit; without a promoted boundary splitter this is admissible-module primeness again.  In flat-connection
language the three possible failures are now: a nonfilled repair face, a curved filled face, or a flat
nontrivial monodromy loop, respectively the square-transverse breaker, the shared-slack q-marker, and
admissible-module primeness.  Shortest flat loops have no higher-polygon residue after saturation:
odd cycles and even cycles of length greater than two are module/local-exit cases, leaving only the
two-point adjacent package-change turn.  Likewise, ternary dirty-row configurations either close pairwise
or reduce to a flat monodromy triangle / curved `0001` face, so there is no independent ternary atom.
The adjacent turn itself has a signed-edge normal form: opposite signs give the balanced flip, same signs
give the singleton-isolator edge, and in both cases the unresolved datum is the dirty chart change rather
than the sign.  Its carrier either has a proper complete subcarrier, crosses another dirty edge as the
primitive `2x2` circuit, or is an admissible module split only by a non-promoted ambient row.  On the
admissible-module side, minimum-side normalization reduces every such failure to the singleton isolator
self-loop.  Out-of-frame axis drift is the same rank-one frame slip: a nonfilled face, curved face, or
flat monodromy loop gives exactly the three flat-connection endpoints, while the only irreducible slip is
the dirty chart-change edge.  The reduced two-chart model shows that the slip itself needs a boundary
certificate theorem: the slipped coordinate must carry a complete shared-slack side, or its absence must
be a smaller square-transverse breaker.  Once the splitter is an ordered boundary row, the certificate is
formal: the internal failure set is a whole splitter side and hence a smaller complete marker.  Therefore
only ambient-to-boundary transport remains, and its minimal failure is a one-state high-error bounce on
the same slipped side.  This bounce is the common shadow of the three named host frontiers: pair-chamber
hidden-choice separation, anchored persistence/no-split on `Q^+`, and anchored one-corner lift on
`Q_j(x)` each kill it, and failure of any one is the same missing-`0111` table.  A prime-shell breaker of
the two bounced rows reduces further to a same-cut high-error clone packet: it is an admissible module
whose ambient breaker is still not promoted.  Recentring on two clone rows is self-similar and does not
decrease carrier size; maximal clone packets form a directed package-change cycle, and saturation reduces
that cycle back to the two-packet `{0101,0011}` non-overlap atom.  If same-cut clone closure were
hereditary under ambient breakers, primeness would close the endpoint by a module argument; the missing
heredity is exactly boundary provenance.  Acyclic clone-package graphs close by the same module argument,
so the final hereditary failure is a two-state package transposition, i.e. the rank-one flat holonomy /
missing-`0111` atom.  Its anchored subcase closes; an irreducible transposition must move the anchor, so
it is exactly the anchored frame-slip endpoint.  Choosing the first package-label change on a shortest
flat anchor path reduces this to a single chamber-flat anchored slip edge; one-corner lift kills it, and
failure of the lift is the `0001` square.  Equivalently, the final one-edge form is a minimal
square-transverse breaker whose first dirty failed row is fully skew on the same support and changes only
the hidden package label; its support-preserving trace table is exactly the two-fiber non-overlap
`Omega_10,Omega_01` with missing `0111`.  Equivalently, the visible chamber data carry an unbranched
nontrivial two-sheeted hidden-package cover, or a nonzero flat `Z/2` holonomy class; branch points are
precisely one-corner lift failures or square-transverse breakers, and odd filled faces are the `0001`
marker.  Coordinate cancellation kills such a holonomy if every repeated-coordinate swap is filled and
flat; hence the remaining cubical input is rank-one coordinate-swap completeness along a shortest
holonomy loop.  Its fixed-candidate half is closed by interval arithmetic, so the live swap failure is a
candidate-switching gate failure; minimal such gate failures localize to the same three-corner anti-Horn
square with absent `11`.  The candidate data of that square is forced to be a three-certificate cycle;
repeated or sink certificates reduce to the fixed-candidate interval calculation, and the first breakers
on the cycle have no independent ternary residue because two same-sign breakers either coalesce in one
residual frame or expose the same two-state package-change edge.  Geometrically the cycle is a distributed
alternating hexagon `K_{3,3}` minus a perfect matching; once any cyclic five-vertex seed is localized on
one Section `40` frame, the in-frame scalar part is automatic because the seed is `P_5`, so the live input
is exactly distributed-hexagon-to-one-frame synchronization.  This is the same as the ambient-to-fixed
fiber-preserving shared-slice lift, equivalently the compatible degree-congruent transversal theorem for
one shared slice; the visible `2 x 2` hyperplane tile is already forced, so the remaining local form is
adjacent-slice admissibility at the unique median-entry point `s_*`.  The visible half of that lift is
closed; the hidden half is single-witness uniformity on the median fiber `M_rho`.  A mixed witness on
`M_rho` reduces by a closest-return clean corridor to the successor-side `0001` square, and after the
one-edge predecessor/persistence inputs are factored off the quotient table is again
`{0101,0011}` with missing `0111`, equivalently fixed pair-chamber cylinder rigidity for the elementary
hidden choice.  Its intrinsic two-square form is elementary two-sided silent-component injectivity, and
the basin localization reduces it to boundary outgoing anchored witness persistence plus realized
componentwise singleton on `Q^+`, i.e. the `host-opppair123` surface.  Failure of that realized singleton
is a chamber-flat silent edge, killed exactly by the anchored one-corner lift of `host-silentedge128`, and
failure of the lift is again the successor-side `0001` square.  Equivalently, the one-square endpoint is
edgelessness of the silent graph `Gamma_(Q,e)`, or incident-square opposite-defect wall detection; its
minimal failure is one chamber-flat silent edge, and vertex potentials on the silent graph cannot exclude
it.  The same atom is prefix-star sign uniqueness for silent edges with fixed lower packet prefix and
first changed coordinate; opposite signs force the anchored one-corner lift or the `0001` failure.  The
support-local fourth-corner route pushes this to transverse-breaker admissibility: fixed-candidate
interval failures close, clean marked support closes, and the live case is the dirty budget-one
`Abs(1)` / reanchor-breaker prime-shell cycle-breaker.  Minimum-side normalization turns this branch into
a one-point isolator self-loop; an aligned defect-switching square is sub-`q` and impossible, so any
survivor is axis drift, equivalently the same rank-one package slip / common-frame gluing endpoint.  On
the exact-marker side, all finite packet-quotient selections reduce to the same packet-firewall
normal form: a protected clique or compensator packet is a module for all admissible rows, but ambient
primeness supplies only a high-error breaker whose promotion is exactly Theorem G.  The latest
normalization identifies the rank-one slip as a two-sheeted hidden-package cover.  Edge-table
purification forces every nonlocal ambient separator of that cover to be the global sheet character:
mixed edge tables are branch points and base-boundary cuts are the ordered-boundary case.  For odd
moduli a promoted sheet side would already be a smaller q-marker.  For dyadic moduli, even sheet
multiplicity also closes; the only primitive survivor has `|R|=q mod 2q` and sheet sizes
`q/2 mod q`.  A tree gauge then collapses all distributed monodromy to one anchored rank-one slip edge.
The tree sheet has boundary only at that slip edge, so the endpoint is local in the anchored star of the
edge.  Thus the surviving endpoint is the single-slip child-realization problem: either the slip edge is
an ordered first-return boundary edge and one sheet is a `q/2`-child carrier, or the first failed star
transport is a branch point (`0001` / square-transverse breaker).  Tree-gauge normalization also kills
any residual ternary packet: a shortest star word commutes across filled flat swaps until the first
nonflat swap, which is already the one-corner branch face.  The last atom is therefore locally star-flat
slip-edge provenance: a primitive anchored slip edge with every anchored star face filled and flat must be
an ordered first-return boundary edge, unless the hidden-sheet renaming is realized by a branch square.
Prime-shell closure only supplies the same global sheet-character separator; if that separator is not
first-return admissible, recentering reproduces the same atom.  Peripheral boundary tests add no new
cases: a shortest failed commutation from the slip edge to any old boundary row has a first nonfilled or
curved face, hence a local exit or branch square.  The irreducible residue is star-to-boundary normality:
a locally star-flat sheet-character separator commuting with the whole boundary history must itself be
admissible in the ordered first-return family.  Equivalently, every filled flat commutation needed to move
that separator backward along the first-return word must be an actual first-return exchange square; the
first static-but-not-first-return square exposes an exchange-gate edge.  A prime breaker of that gate is
fixed-trace/clean local, or is a minimal square-transverse breaker.  Hence boundary exchange closure is
the cubicality face of transverse-breaker admissibility, not a new endpoint.  Its first dirty row either
gives a proper child carrier, a primitive circuit, or the `0001` branch square; the only support-preserving
case is a gate-parallel sheet-character bounce, the same two-chart renaming atom.  The flip has order two,
but in the primitive dyadic case one flip has residue `q/2 mod q` and two flips reconstruct the original
marker, so finite order gives no descent.  The smallest live atom is an idempotent one-edge
boundary-normality failure: a global sheet-character commuting flatly with all boundary history but not
admitted as a first-return boundary edge.  There is no higher-rank deck group left: two distinct
sheet-character separators either give a base-boundary child carrier/gate breaker or are fixed-trace
twins.  Thus the same atom is rank-one boundary-category fullness for a unique central deck involution.
An abstract index-two extension of the boundary category realizes all reduced local tests while keeping
that involution outside the first-return category, so the remaining proof must use graph-specific
first-return construction rather than local category axioms alone.  Lowering to modulus `q/2` closes as
soon as one sheet is a first-return child carrier; otherwise the same atom becomes prefix-insertion
fullness for the central sheet edge.  If all prefix commutations succeed, the history erases completely
and the residue is root-edge fullness: an ambient separator of a primitive `q/2` child carrier at the
anchored prefix must be a first-return child edge or yield a local/branch exit.  Equivalently, the final
missing graph-specific input is root reseating invariance: such an ambient separator can be chosen as the
first boundary of an equivalent terminal descent, unless reseating exposes the branch square.  Since the
ambient separator already realizes the primitive child profile, this is exactly root selector fullness:
realized ambient child-cut rows must be selectable as initial first-return boundaries, barring local or
branch exits.  After all commuting history is erased, this becomes a memory-free selector theorem: at the
anchored prefix, eligibility must depend only on prefix-local tests.  If it does, the separator is
admitted; if it does not, the only remaining obstruction is hidden selector memory, namely dependence on a
vanished first-return word with no local trace.  A global restart-minimal terminal descent kills that
hidden memory: the `h`-started descent is then a competing minimal descent unless its first divergence is
an already-classified local/branch exchange failure.  Consequently the live endpoint is restart
admissibility for the `h`-started terminal step.  Restart admissibility is measured by the finite residue
vector `Delta_h(P)` of the terminal template.  If that vector is nonzero, its first nonzero coordinate is
old-defect, inserted-root, fixed-trace/clean, or square-transverse, all closed.  Thus a survivor needs a
hidden restart residue: every recorded terminal-template residue vanishes, but the restarted descent is
still outside the comparison class.  Saturating the first-return family by residue-zero, prefix-local rows
would remove that obstruction.  The only remaining possible failure is then a residue-zero non-square row:
all four singleton corners and terminal residues exist, but the square is not admitted as first-return
provenance.  This is provenance-saturation at the anchored prefix.  Passing from the path-only
first-return family to the residue-saturated exchange complex `FR^sat` would make this automatic, and all
earlier reductions are monotone under that enlargement.  The final audit is saturation compatibility:
whether "first-return-complete" support is unchanged when terminal descent is run in `FR^sat`.  Intrinsic
exchange-completeness makes the audit pass, because the low-set congruence uses only the four graph
corners and the terminal residue vector.  Thus the remaining unsaturated issue is path-saturation
equivalence: replacing the historical path convention by the intrinsic exchange-complete convention must
not change the terminal-host descent except through a local/branch exit.  In the saturated convention this
is enough to prove a saturated provenance/support-decrease theorem: a splitter either fails a prefix-local
test, has nonzero first terminal residue and hence a local/branch exit, or has zero residue and is an
`FR^sat` boundary; its first packet-internal failure is then an exchange-complete smaller q-marker.  The
remaining comparison is Open target 8.3: a shortest nonhomotopic path-only/saturated pair should give a
shortest saturated loop; missing-corner and first-residue disagreements should be local/branch exits;
independent equal-residue turns are filled `FR^sat` squares.  The missing non-circular step is the
omni-saturation lemma that would collapse longer flat rank-one loops to admissible-module/local exits or
to the two-state residue-zero square.  Until that lemma is proved, the original path-only Theorem G
remains open.  The graph theorem proved above avoids this by using
`FR^sat` as the terminal boundary category from the start.
