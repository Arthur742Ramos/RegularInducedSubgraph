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

There is a dense zero-target companion.  Let

```text
P_+ = { b in U : deg_W(b) == r+1 [MOD 4] }.
```

If `P_+` contains a clique `K` with `|K|>3|W|`, apply Olson in `(Z/4Z)^|W|` to the vectors

```text
((1_{bw}-1_{bw_0})_{w != w_0}, 1-1_{bw_0}),        b in K.
```

For some nonempty `B subset K` the sum is zero, so `deg_B(w)=delta` is constant on `W` and
`|B|-delta=0 [MOD 4]`.  Since `K` is a clique, every `b in B` has `deg_B(b)=|B|-1`; with
`deg_W(b)=r+1` this gives

```text
deg_W(b)+deg_B(b)=r+|B|=r+delta        [MOD 4].
```

Thus `W union B` is larger.  Therefore every maximal counterexample also satisfies

```text
omega(P_+) <= 3|W|.
```

The two zero-target chambers also have an exact mixed packet rule.  Let `I subset P_0` be independent
and `K subset P_+` be a clique.  Suppose

```text
deg_I(w)=0                         for every w in W,
deg_K(w)=kappa                     for every w in W,
|K|-kappa=0                        [MOD 4],
```

and suppose the cross graph between `I` and `K` is uniform with value `epsilon in {0,1}`.  Then
`B=I union K` appends to `W` provided

```text
epsilon=0 => |K|=0                 [MOD 4],
epsilon=1 => |I|=0                 [MOD 4].
```

Indeed the old increment is `delta=kappa=|K|`.  Vertices of `I` have new degree
`r+epsilon|K|`, while vertices of `K` have new degree
`r+1+(|K|-1)+epsilon|I|`; the two displayed size congruences make both equal to `r+delta`.
Thus terminality forbids not only large independent packets in `P_0` and large cliques in `P_+`
separately, but also any cross-empty or cross-complete pair of such old-balanced packets with the
corresponding size congruence.  The extra size congruence can be forced by Olson at the cost of one
additional `Z/4Z` coordinate when the relevant packet reservoir is larger than `3(m+1)`.

The exact mixed rule only requires the cross graph to be biregular modulo `4`.  Keep `I subset P_0`
independent and `K subset P_+` a clique, with `deg_I(W)=0`, `deg_K(W)=kappa`, and let

```text
c_I=deg_K(i)        for i in I,
c_K=deg_I(k)        for k in K.
```

Then `I union K` appends exactly when

```text
c_I=kappa,        |K|+c_K=kappa        [MOD 4],
```

together with the edge-count compatibility `|I|c_I=|K|c_K [MOD 4]`.  The cross-empty/complete rule is
the special case `c_I=epsilon|K|`, `c_K=epsilon|I|`.
The old-frame double counts also force

```text
r|I|=0,        m kappa=(r+1)|K|        [MOD 4],
```

and in the Olson dense cap where `kappa=|K|`, this becomes `(m-r-1)|K|=0`.
Thus:

```text
r odd => |I|=0,        r=2 => |I| even;
m-r-1 odd => |K|=0,    m-r-1=2 => |K| even              [MOD 4].
```

Equivalently, eliminating the cross residues leaves

```text
(|I|-|K|)kappa = -|K|^2        [MOD 4].
```

So if `|I|=|K| [MOD 4]`, the mixed packet is possible only when `|K|` is even; if the size difference is
odd, the old increment `kappa` is uniquely forced.

More generally, the two-packet chamber equation is scalar once the packets are internally regular and
cross-uniform.  Let `B_a subset P_a` and `B_b subset P_b` have old increments `delta_a,delta_b`, internal
degree residues `d_a,d_b`, and cross value `epsilon in {0,1}`.  Then
`B_a union B_b` appends to `W` iff

```text
a+d_a+epsilon|B_b| = r+delta_a+delta_b,
b+d_b+epsilon|B_a| = r+delta_a+delta_b        [MOD 4].
```

The zero-target independent/clique rule is the case
`a=r`, `d_a=0`, `delta_a=0`, `b=r+1`, `d_b=|B_b|-1`, and `delta_b=|B_b|`.
Thus every remaining chamber-packet obstruction can be phrased as failure to realize one of these
two scalar equations after the old-frame Olson balancing has been performed.

For a finite packet family the same equation is:

```text
B_j subset P_{a_j},       internal residue d_j,       old increment delta_j,
cross(B_j,B_k)=epsilon_{jk} in {0,1}.
```

If all cross graphs are uniform, then `B=union_j B_j` appends iff, for every active `j`,

```text
a_j+d_j+sum_{k != j} epsilon_{jk}|B_k|
  = r+sum_k delta_k                         [MOD 4].
```

This gives a finite packet-system form for the cross-uniform subcase: old-coordinate balancing is
linear, and the remaining self-layer data are internal residues and uniform cross packet sizes.

The exact packet quotient only needs cross-regularity modulo `4`, not cross-uniformity.  For packets
`B_j`, write `c_{jk}` for the common value of `deg_{B_k}(v)` on vertices `v in B_j`, whenever this value
is constant modulo `4`.  Edge-count symmetry imposes

```text
|B_j| c_{jk}=|B_k| c_{kj}        [MOD 4].
```

Then `B=union_j B_j` appends iff, for every active `j`,

```text
a_j+d_j+sum_{k != j} c_{jk}
  = r+sum_k delta_k                         [MOD 4].
```

The old increments are themselves constrained.  Since `B_j subset P_{a_j}` and
`deg_{B_j}(w)=delta_j` for every `w in W`, double-counting edges between `W` and `B_j` gives

```text
m delta_j = a_j |B_j|        [MOD 4],        m=|W|.
```

Thus `delta_j` is not a free scalar: if `m` is odd it is determined by `a_j|B_j|`; if `m=2 [MOD 4]`
only its parity is determined; and if `m=0 [MOD 4]` the chamber-size product `a_j|B_j|` must vanish.
This old-frame edge-count congruence is part of the exact packet quotient.

The old witness has its own edge-count constraint:

```text
m r = 2e(W)        [MOD 4].
```

In particular, if `m` is odd then `r` is even.  Thus the odd-`m` intrinsic target below starts from an
even old residue; odd targets can only be produced by the packet chamber-size contribution.

Consequently the final target can often be eliminated.  If `m` is odd, then

```text
sum_j delta_j = m^{-1} sum_j a_j|B_j|        [MOD 4],
```

so the packet target is the fully intrinsic scalar

```text
r+m^{-1} sum_j a_j|B_j|        [MOD 4].
```

If `m=0 [MOD 4]`, every old-balanced packet must satisfy `a_j|B_j|=0`; in particular odd-size packets
can occur only in the zero chamber.  If `m=2 [MOD 4]`, every packet with `a_j|B_j|` odd is impossible,
and otherwise the parity of `delta_j` is fixed.  Thus the parity of the old witness size already removes
many chamber/size combinations before the self-layer quotient is considered.

Equivalently, by packet size `s=|B_j| [MOD 4]`:

```text
m odd:       every (a,s) is feasible and delta=m^{-1}as;
m=2:         as must be even; if s=0 then delta is even, if s=2 then delta=a [MOD 2];
m=0:         as must vanish; hence s odd forces a=0, and s=2 forces a even.
```

This table is often the first pruning step in the finite quotient.

For a single internally regular packet `B subset P_a` of size `s` and internal residue `d`, the quotient
has no cross terms.  It appends exactly when

```text
a+d = r+delta,        m delta = as        [MOD 4],
```

or, eliminating `delta`,

```text
m(a+d-r)=as        [MOD 4].
```

This is the exact one-packet chamber test.  The zero-shift independent cap and the `+1` clique cap are
the two cases where Olson can force the required old increment together with `d=0` or `d=s-1`.
Unpacked by `m [MOD 4]`:

```text
m odd:       if a=0 then d=r; if a is a unit then s=a^{-1}m(a+d-r);
             if a=2 then d=r [MOD 2] and s is fixed modulo 2;
m=2:         2(a+d-r)=as, so a odd forces s even and a=0 forces d=r [MOD 2];
m=0:         as=0, and the packet must realize the specific old increment delta=a+d-r.
```

Thus when `m=0 [MOD 4]`, all the difficulty is finding old-balanced internally regular packets in
admissible chamber/size pairs with the prescribed increment `delta=a+d-r`; the target residue imposes no
further arithmetic condition.

The cross-uniform formula is the special case `c_{jk}=epsilon_{jk}|B_k|`.  Thus the honest finite
residual is a cross-regular packet quotient with edge-count symmetry, and the cross-uniform packet
system is the most rigid visible subcase.

Equivalently, the packet system splits into a row-difference condition and one scalar target.  Put

```text
R_j=a_j+d_j+sum_{k != j} c_{jk}.
```

Then the union appends iff

```text
R_j=R_l                         for all active j,l,
R_j=r+sum_k delta_k             for one (hence every) active j.       [MOD 4]
```

The first line is pure self-layer compatibility and does not mention the old witness residue `r`; the
second line is the single old-increment target.  Thus a terminal cross-regular packet family must fail
either the row-difference equations

```text
(a_j+d_j)-(a_l+d_l)
  +sum_k (c_{jk}-c_{lk})=0        [MOD 4]
```

or the final scalar old-increment equation.  This is the packet analogue of separating quotient-degree
parity from the last Arf/carry bit in the odd-word branch.

There is also a global edge-count check obtained by summing the row equations with weights
`s_j=|B_j|`.  Put `S=sum_j s_j` and `Delta=sum_j delta_j`.  Since
`sum_j s_j a_j=m Delta`, the packet rows imply

```text
S r + (S-m)Delta = 2e(B)        [MOD 4],
```

where

```text
2e(B)=sum_j s_j d_j + sum_{j != k} s_j c_{jk}        [MOD 4].
```

Equivalently, the enlarged witness of size `m+S` and residue `R=r+Delta` satisfies
`(m+S)R=2e(W union B) [MOD 4]`.  Hence if `m+S` is odd, the target residue `R` must be even.  This
global scalar is automatic for a true extension, but in the quotient algebra it is a fast consistency
check on the row/target data.

For two packets this can be eliminated completely.  Let `B_a subset P_a` and `B_b subset P_b` have sizes
`s_a,s_b`, internal residues `d_a,d_b`, old increments `delta_a,delta_b`, and cross residues
`c_{ab},c_{ba}`.  Put

```text
A=(a+d_a)-(b+d_b).
```

The row-difference equation gives `c_{ba}=c_{ab}+A`.  The only remaining cross-regularity condition is

```text
(s_a-s_b)c_{ab}=s_b A        [MOD 4],
```

and the target equation is

```text
c_{ab}=r+delta_a+delta_b-a-d_a        [MOD 4].
```

Thus a two-packet extension is decided by two scalar congruences after old-frame balancing: one
edge-count congruence and one old-increment target.  The mixed `P_0/P_+` rule above is the special case
`A=-|B_b|`.

Substituting the target value leaves a single quotient congruence:

```text
(s_a-s_b)(r+delta_a+delta_b-a-d_a)
  = s_b((a+d_a)-(b+d_b))        [MOD 4].
```

If `m` is odd, this has the intrinsic form

```text
(s_a-s_b)(r+m^{-1}(a s_a+b s_b)-a-d_a)
  = s_b((a+d_a)-(b+d_b))        [MOD 4].
```

So in odd witness size, two-packet feasibility is determined entirely by the chamber residues, packet
sizes, and internal residues; no independent old-increment label remains.

Equivalently, for a prescribed target cross residue `T=r+delta_a+delta_b-a-d_a`, the edge-count equation
`(s_a-s_b)c_{ab}=s_b A` is soluble exactly as follows:

```text
s_a-s_b odd:     c_{ab} is uniquely forced;
s_a-s_b == 2:    s_b A must be even, and c_{ab} is forced modulo 2;
s_a-s_b == 0:    s_b A must vanish, and c_{ab} is free before the target equation.
```

Thus two-packet terminality is already a tiny residue obstruction unless the actual graph fails to
supply the required cross-regular pair with that residue.

The finite quotient also has a clean parity shadow.  Reduce the exact packet equations modulo `2`.
For odd-size packets, edge-count symmetry gives

```text
c_{jk}=c_{kj}        [MOD 2].
```

Hence on any subsystem of odd-size packets the parities of `c_{jk}` form an undirected quotient graph
`Q`, and the row-difference condition modulo `2` is

```text
a_j+d_j+deg_Q(j)=constant        [MOD 2].
```

Thus the first bit of a packet-system witness is again an ordinary parity-degree condition on a quotient
graph, with vertex labels `a_j+d_j`.  The remaining obstruction after this parity shadow is precisely
the mod-`4` carry encoded by the full residues `c_{jk}` and the final old-increment target.

The full edge-count symmetry can be read by size strata.  If `s_j=|B_j| [MOD 4]`, then:

```text
s_j,s_k odd:       c_{kj}=s_k s_j^{-1} c_{jk}          [MOD 4];
s_j=0, s_k odd:    c_{kj}=0;
s_j=2, s_k odd:    c_{kj}=2 c_{jk} s_k^{-1}            [MOD 4];
s_j=s_k=2:         c_{jk}=c_{kj}                       [MOD 2];
s_j=s_k=0:         no edge-count restriction modulo 4.
```

In particular, two odd packets of the same size residue have `c_{jk}=c_{kj} [MOD 4]`, while odd packets
of opposite size residues have `c_{jk}=-c_{kj} [MOD 4]`.  The parity shadow forgets this sign; the sign
is exactly one of the carry bits.

Thus odd packets see all cross residues rigidly, size-`2` packets see only the parity of other size-`2`
packets, and size-`0` packets are invisible to the edge-count congruence except through rows that point
back from odd packets.  This is the exact arithmetic source of the remaining carry freedom.

The row-difference form also gives an exact packet coalescence rule.  Suppose two active packets
`B_1,B_2` have the same chamber value `a`, the same internal residue `d`, and the same external
cross-profile: for every other packet `B_k`, both `c_{1k}=c_{2k}` and `c_{k1}=c_{k2}`.  Let
`c_{12},c_{21}` be the two cross-degree residues between them.  If `c_{12}=c_{21}`, then
`B_1 union B_2` is internally regular with residue

```text
d+c_{12}        [MOD 4],
```

has old increment `delta_1+delta_2`, and has the same external cross profile after replacing
`c_{k1},c_{k2}` by `c_{k1}+c_{k2}` for the degree from `B_k` into the merged packet.  Edge-count
symmetry is preserved by summing the two old symmetry identities.  Replacing `B_1,B_2` by this union
preserves the packet-system equations.

Conversely, if the two packets appear in an appendable packet system, their row values differ by

```text
R_1-R_2=c_{12}-c_{21}        [MOD 4],
```

because all other terms cancel.  Hence row compatibility forces `c_{12}=c_{21}`, and then the packets
coalesce.  Therefore any appendable primitive packet system is profile-simple: it selects at most one
packet from each same-chamber external profile.  Duplicate profiles are terminal clutter, not part of a
possible extension.

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

It is useful to eliminate `R`.  Define the self-error of `B` by

```text
eta_B(b)=t+deg_B(b)-r-delta        [MOD 4].
```

Writing `lambda=r+delta-R`, the replacement equations become

```text
deg_D(w)=lambda                    for every w in W\D,
deg_D(b)=eta_B(b)+lambda           for every b in B.        [MOD 4]
```

Because `B` is old-balanced, every deleted old vertex also has `deg_B(x)=delta`.  Hence any replacement
deletion of size `d=|D|` must satisfy the two scalar checks

```text
sum_{b in B}(eta_B(b)+lambda)=d delta,             [MOD 4]
lambda(m-d)=d r-2e(D).                             [MOD 4]
```

The first is edge-counting between `D` and `B`; the second is edge-counting between `D` and `W\D`.
Thus a profitable nonappend replacement is not just an arbitrary correction set: it must have constant
degree `lambda` into the kept old witness and must realize the shifted self-error vector of the large
packet.

For `|D|=1` this is especially rigid.  The unique deleted vertex must be either nonadjacent to every
kept old vertex (`lambda=0`, forcing `r=0`) or adjacent to every kept old vertex (`lambda=1`, forcing
`m-1=r [MOD 4]`), and for every `b in B` the value `eta_B(b)+lambda` must be an actual bit `0` or `1`.
Thus one-vertex repair only handles two adjacent self-error classes; all other terminal error patterns
require either an append-only subpacket or a genuinely multi-vertex deletion.

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

Writing this common value as `K`, summing over the whole old frame gives the signed old-frame scalar

```text
mK=|B|t-|D|r        [MOD 4].
```

This is the deletion analogue of the packet identity `m delta=a|B|`: if `m` is odd, `K` is intrinsic,
while if `m=0 [MOD 4]` the signed packet must satisfy `|B|t=|D|r`.
Unpacked by `m [MOD 4]`, with `s=|B|` and `d=|D|`, the signed old-frame constraint is

```text
m odd:       K=m^{-1}(s t-d r);
m=2:         s t-d r is even, and K is fixed modulo 2;
m=0:         s t=d r, and K is not fixed by the old frame.        [MOD 4]
```

Thus every signed replacement quotient has the same first pruning layer as the append-only packet
quotient: old-frame double-counting decides which chamber/size pairs can even carry a target.

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

Summing the two signed equations gives the replacement global scalar.  With `s=|B|`, `d=|D|`, and
internal edge counts `e(B),e(D)`,

```text
(m-d-s)K = (s-d)r + 2e(D)-2e(B)        [MOD 4].
```

Equivalently the new set has size `m-d+s` and residue `r+K`, so if `m-d+s` is odd then `r+K` must be
even.  Thus signed old-coordinate balance plus positive surplus is still not enough: the self-layer
cleanup must also land on this scalar edge-count class.

When the signed old balance is the full-frame one produced above, the two scalar checks combine to

```text
(m-d-s)(s t-d r)=m((s-d)r+2e(D)-2e(B))        [MOD 4].
```

For odd `m`, this eliminates `K` completely.  Thus an odd-size old witness leaves no signed target
freedom: the chamber value `t`, the sizes of the positive and negative packets, and the two internal
edge parities already determine whether a self-layer cleanup can satisfy global edge count.
Reducing modulo `2`, `r` is even and `K=st [MOD 2]`; hence if `t` and `s` are both odd, then `d` must
be even.  Thus an odd chamber cannot be repaired by an odd positive packet while deleting an odd number
of old vertices.

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

Equivalently, for each same-old-vector pair `(y,z)` define

```text
A_{y,z}={u in B\{y}: theta_X(u) != L and theta_X(u)+1_{uy}-1_{uz}=L},
D_{y,z}={u in B\{y}: theta_X(u) = L and theta_X(u)+1_{uy}-1_{uz} != L}.
```

Then target-stability gives

```text
|A_{y,z}| + 1_{z becomes target} <= |D_{y,z}| + 1_{y in T}.
```

Thus any import that is itself target-correct, or that corrects many off-target retained vertices, must
flip at least as many current target vertices off target.  In a minimal counterexample the boundary
vertices in each old-vector class are therefore dominated by the signed cut they induce across the
current target fiber `T`; no boundary vertex can have a strictly positive correction surplus against all
exports in its old-vector class.

Summing over all retained exports `y` in the same old-vector class `B_p={y in B:p_y=p_z}` gives a useful
averaged obstruction for each boundary vertex `z`:

```text
sum_{y in B_p} ( |A_{y,z}|-|D_{y,z}| )
    <= |T cap B_p| - |B_p| 1_{z lands on target}.
```

Thus a boundary vertex that would land on target must create total signed damage at least
`|B_p|-|T cap B_p|` across its old-vector class.  If the signed cut from `z` differs from many exports
in a way that corrects more off-target vertices than it damages target vertices, the singleton exchange
already closes the co-cut endpoint.

When the anchor shift vanishes, this inequality can be read by error residues.  Put

```text
T_+= {u:theta_X(u)=L+1},        T_-={u:theta_X(u)=L-1},        T_2={u:theta_X(u)=L+2}.
```

Since a singleton swap changes a retained label only by `-1,0,+1`, vertices of `T_2` are invisible to
singleton correction.  Moreover

```text
A_{y,z}=(N(y)\N(z) cap T_-) union (N(z)\N(y) cap T_+),
D_{y,z}=(N(y) triangle N(z)) cap T.
```

Thus singleton target-stability is the signed cut inequality

```text
|N(y)\N(z) cap T_-| + |N(z)\N(y) cap T_+| + 1_{z target}
  <= |(N(y) triangle N(z)) cap T| + 1_{y in T}.
```

So the singleton-swap route can only exploit the `+1/-1` error layers; any residual made solely of
`2`-errors requires a larger exchange or a pure block discard.

For a balanced two-for-two exchange the missing `2`-layer becomes visible.  Let
`Y={y_1,y_2} subset B`, `Z={z_1,z_2} subset X`, assume

```text
p_{y_1}+p_{y_2}=p_{z_1}+p_{z_2},        deg_Z(w_0)=deg_Y(w_0),
```

so the anchor shift is zero.  For a surviving retained vertex put

```text
s_{Y,Z}(u)=deg_Y(u)-deg_Z(u) in {-2,-1,0,1,2}.
```

Then the retained-side gain layers are

```text
s= 1 corrects T_-,      s=-1 corrects T_+,
s= 2 or -2 corrects T_2,
```

and the target layer `T` is damaged exactly where `s != 0`.  Thus target-stability for such a pair
exchange says

```text
|{u in T_-:s(u)=1}| + |{u in T_+:s(u)=-1}| + |{u in T_2:|s(u)|=2}|
  + imported-target-count
<= |{u in T:s(u)!=0}| + |Y cap T|.
```

This is the first local inequality that can see a pure `2`-error obstruction.  Consequently, if all
singleton swaps are inert and the residual error lies in `T_2`, the next target is a zero-anchor balanced
pair exchange whose two-export/two-import cut has large `|s|=2` support on `T_2` and small support on the
current target fiber.

Equivalently, a terminal pure-`T_2` branch must satisfy the following no-pair-cut rule.  For every
zero-anchor balanced pair exchange `(Y,Z)`,

```text
|{u in T_2 : deg_Y(u)=2, deg_Z(u)=0}|
+ |{u in T_2 : deg_Y(u)=0, deg_Z(u)=2}|
  + imported-target-count
<= |{u in T : deg_Y(u) != deg_Z(u)}| + |Y cap T|.
```

Thus a large subset of `T_2` on which two old-vector-compatible exports are simultaneously complete and
two imports simultaneously absent, or conversely, is impossible unless the same pair cut damages at least
as many target vertices.  This is the pair-exchange analogue of the singleton signed-cut domination.

The same rule has a more useful averaged form.  Fix an old-vector fiber `A subset B` and a boundary
import pair `Z={z_1,z_2}` with

```text
p_{a_1}+p_{a_2}=p_{z_1}+p_{z_2},        deg_Z(w_0)=deg_{\{a_1,a_2\}}(w_0)
```

for every admissible export pair `{a_1,a_2} subset A` in the averaging family.  Summing the no-pair-cut
inequality over all such export pairs gives

```text
sum_{u in T_2, deg_Z(u)=0} binom(deg_A(u),2)
+ sum_{u in T_2, deg_Z(u)=2} binom(|A|-deg_A(u),2)
+ binom(|A|,2) imported-target-count
<= sum_{t in T} #{Y in binom(A,2): deg_Y(t) != deg_Z(t)}
   + (|A|-1)|A cap T|.
```

Here a `T_2` vertex contributes only from the two complete/empty extremes: if it misses both imported
vertices, then every adjacent export pair is a correcting pair, and if it sees both imported vertices,
then every nonadjacent export pair is correcting.  Therefore a terminal pure-`T_2` branch imposes
quadratic common-neighborhood domination.  Unless the target side pays quadratically many damaged export
pairs, every `u in T_2` with `deg_Z(u)=0` has `deg_A(u)<=1`, and every `u in T_2` with `deg_Z(u)=2` has
`deg_A(u)>=|A|-1`.

In an exact basis direction the import reservoir contains three copies `Z_g={z_1,z_2,z_3}`.  Applying the
previous inequality to all three import pairs yields the majority synchronization corollary: for any large
admissible export pool `A_g` in the same direction, an unpaid pure-`T_2` vertex is almost constant on
`A_g`.  If it sees at most one of the three boundary copies, then it sees at most one vertex of `A_g`; if
it sees at least two boundary copies, then it misses at most one vertex of `A_g`.  Thus the exact-basis
pure-`T_2` residual can only survive by making the old fiber copy the boundary triple's majority pattern
on every unpaid `2`-error vertex, up to one exceptional export vertex per fiber.

Equivalently, for each direction `g` define the boundary majority

```text
M_g(u)=1_{deg_{Z_g}(u)>=2}        for u in T_2.
```

The unpaid majority rule says

```text
|{a in A_g : 1_{ua} != M_g(u)}| <= 1.
```

Hence the exceptional shadows

```text
Q_g(a)={u in T_2 : a is the unique vertex of A_g with 1_{ua} != M_g(u)}
```

are pairwise disjoint.  After deleting one marked old vertex for each unpaid `T_2` vertex, the remaining
core of `A_g` is completely silent on the pure `2`-error layer: every vertex in the core has the same
adjacency to every unpaid `u`, namely the boundary majority `M_g(u)`.

This is the exact ternary one-corner lift.  Partition `T_2` by the eight adjacency patterns to the boundary
triple `Z_g`.  On a fixed pattern cell `U_lambda`, choose a boundary pair `P_lambda subset Z_g` with
`deg_{P_lambda}(u)=2M_g(u)` for all `u in U_lambda` (two zeros if `|lambda|<=1`, two ones if
`|lambda|>=2`).  Then any old pair `{a,b} subset A_g` whose two vertices are not exceptional for
`U_lambda` satisfies

```text
deg_{\{a,b\}}(u)=deg_{P_lambda}(u)        for every u in U_lambda.
```

So the pair exchange against `P_lambda` is silent on that entire `T_2` pattern cell.  The residual pure
`T_2` obstruction is therefore no longer arbitrary: it is encoded by a disjoint family of one-corner
exception shadows `Q_g(a)` over the exact-basis directions.

Combining this with the signed repair spectrum gives a quantitative endpoint for an exact-basis fiber.
Let

```text
A_g^0={a in A_g : Q_g(a)=empty}.
```

Then `|A_g^0|>=|A_g|-|T_2|`.  Every four-set in `A_g^0` has no pure-`T_2` exception shadow, so terminality
can only reject it by the internal four-block test: if its induced degree is a repairable residue
`d' in Rep(g)`, the signed atom repair closes the counterexample.  Hence

```text
G[A_g^0] has no induced d'-regular four-set for any d' in Rep(g).
```

In particular, if the old-side repair spectrum contains both Ramsey extremes `{0,3}`, then `A_g^0`
contains neither an independent four-set nor a clique four-set, and so

```text
|A_g| <= |T_2| + R(4,4)-1.
```

Thus any exact-basis direction exceeding this bound must have a repair spectrum missing at least one
extreme residue.  The remaining exact-basis obstruction is consequently localized to directions whose
small old subwitnesses cannot repair either the empty or the complete silent four-block.

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

The signed atom has its own scalar tests.  If `s=|S|` and `d=|D|`, then edge-counting between `D` and
the kept old vertices and between `D` and `S` gives

```text
c(m-d)=d r-2e(D),                         [MOD 4]
s c=d delta_S+sum_{u in S} phi_S(u).       [MOD 4]
```

Using the defect-sum identity, the second equation is equivalently

```text
s c=s r+(s-m+d)delta_S-2e(S).              [MOD 4]
```

Thus a defective atom can be signed-repaired only if a residue `c` simultaneously satisfies these two
linear congruences.  In particular, for odd `m-d` the first equation fixes `c`; for `m=d [MOD 4]` it
requires `d r=2e(D)`.

For a one-vertex correction `D={x}` the constraints are pointwise.  The constant `c` must be the bit
`0` or `1` according as `x` is nonadjacent or adjacent to every kept old vertex.  Hence

```text
c(m-1)=r        [MOD 4],
```

so either `c=0,r=0`, or `c=1,r=m-1`.  Moreover every atom defect must lie in the adjacent pair
`{c,c-1}`, because `1_{xs}=c-phi_S(s)`.  Thus any atom whose defect uses three residues, or whose
two-residue support is not an adjacent pair compatible with the old residue, cannot be repaired by a
single old deletion.

More generally, if `d=|D|<4`, the constant `c` is represented by the actual integer
`0<=c<=d`, and every defect value must lie in the cyclic interval

```text
phi_S(S) subset {c,c-1,...,c-d}        [MOD 4].
```

The scalar condition is then

```text
c(m-d)=d r-2e(D)        [MOD 4],
```

with `0<=e(D)<=binom(d,2)`.  Thus `d=2` permits only three consecutive defect residues, while `d=3`
is the first deletion size with no pointwise residue-support restriction.  Any proof that all defective
atoms have four-residue support automatically rules out repairs by fewer than three old deletions.

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

In particular, once `m>24` two auxiliary coordinates are affordable.  Taking the constant coordinate
and the anchor-adjacency coordinate gives a nonempty old-balanced atom with

```text
|S|=0,        delta_S=0        [MOD 4].
```

For such a normalized atom the aggregate defect collapses to

```text
sum_{s in S} phi_S(s)=-2e(S)        [MOD 4].
```

Thus an even internal edge count is the scalar precondition for append-only zero defect, while an odd
internal edge count forces any repair to be genuinely signed.  This does not solve the pointwise
defect, but it removes two degrees of scalar freedom in the large-`m` atom branch.

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

The first two levels can be tabulated without any hidden quantifier.  For `D={x}`, the usable cases are

```text
c=0: x is isolated from W\{x},        r=0,          shift=1_{b_g x} in {0,1};
c=1: x is complete to W\{x},          r=m-1,        shift=1_{b_g x}-1 in {3,0}.
```

For `D={x,y}` with `e=1_{xy}` and `a=|N_W(b_g) cap {x,y}|`, the usable cases are

```text
c=0: {x,y} is anticomplete to E,      r=e [MOD 2],                 shift=a in {0,1,2};
c=1: every vertex of E sees one of x,y,
     m-2=2(r-e) [MOD 4],                                      shift=a-1 in {3,0,1};
c=2: {x,y} is complete to E,          m-2=r-e [MOD 2],             shift=a-2 in {2,3,0}.
```

Thus every singleton or pair deletion adds an interval of length at most three to the direction repair
spectrum, and the interval is controlled by a concrete co-regular old pattern.  The first small deletion
that can have no pointwise residue-support restriction is a triple.

Consequently the large silent-core residual has an anti-Horn form.  Fix a direction `g`, write
`d=r-omega(g)`, and suppose an extreme residue `rho in {0,3}` is missing from `Rep(g)`.  Then every usable
old deletion `D` with constant `c` must avoid the single repairing count

```text
deg_D(b_g) != rho-d+c        [MOD 4].
```

For `|D|<=2` this is a literal forbidden adjacency count in `{0,1,2}`.  Thus each isolated/complete
singleton and each co-regular pair of old vertices imposes a Horn-type exclusion on the direction type:
the direction may see that deletion in all counts except the one that would create the missing Ramsey
extreme.  If an exact-basis fiber is larger than the one-corner cap, one of the two extreme residues is
missing, and all small co-regular old subwitnesses must satisfy this anti-Horn exclusion simultaneously.

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

There is nevertheless a strong large-fiber corollary.  Since `0 in Delta_<(4)(g)` from the empty
deletion, two distinct nonzero shifts would make `d+Delta_<(4)(g)` contain at least three residues.
Every three-residue subset of `Z/4Z` contains either both extremes `{0,3}` or both middle residues
`{1,2}`.  Therefore, if

```text
|C_g| >= R(4,4)        and        |C_g|>2m+5,
```

then a terminal exact-basis direction satisfies

```text
Delta_<(4)(g) subset {0,sigma_g}        for some sigma_g in Z/4Z.
```

Thus any very large direction has at most one nonzero small-deletion shift.  In particular, the
singleton/pair table above becomes a rigid old-witness constraint: all usable isolated, universal,
anticomplete, split, and complete old pairs must give the same shift against that direction, or else the
fiber falls into the Ramsey or pseudo-split bounded branch.

The shifts also have an addition law.  If `D_1,D_2` are disjoint usable old deletions with constants
`c_1,c_2`, and `|D_1|+|D_2|<4`, then `D_1 union D_2` is usable with constant `c_1+c_2` on the common
kept old set, and

```text
shift_{D_1 union D_2}(g)=shift_{D_1}(g)+shift_{D_2}(g)        [MOD 4].
```

Consequently, in a very large terminal direction with
`Delta_<(4)(g) subset {0,sigma_g}`, two disjoint usable deletions of unit shift `sigma_g in {1,3}`
are impossible, because their union has shift `2`.  More generally, all disjoint sums of singleton/pair
repairs of total size below four must remain in `{0,sigma_g}`.  This converts the spectral hole into a
concrete packing obstruction inside the old witness.

Thus the very-large direction branch splits.  If `sigma_g` is a unit, then all nonzero-shift usable
deletions of total size at most two form an intersecting family whenever their union has size below
four; in particular there is at most one nonzero-shift singleton, and any nonzero-shift pair must contain
that singleton if it exists.  If `sigma_g=2`, unit-shift repairs are absent, while two disjoint
opposite-shift repairs may add back to zero.  The `sigma_g=2` branch is therefore the only large-fiber
case in which disjoint small repairs can survive the addition law.

For unit `sigma_g` the pair part is therefore completely structured.  If a nonzero-shift singleton
exists, every nonzero-shift usable pair contains it.  If no such singleton exists, the nonzero-shift
usable pairs form an intersecting family of two-subsets of `W`; hence they are either all incident to a
single old vertex, or they are exactly contained in the three edges of one old triangle.  Thus the
unit-shift branch reduces to a star/triangle obstruction inside `W`, while the `sigma_g=2` branch is the
only branch with potentially spread-out disjoint pair repairs.
Equivalently, in the unit branch there is a kernel `K_g subset W` with `|K_g|<=3` such that every usable
singleton or pair deletion disjoint from `K_g` has zero shift against the direction.  The star case has
`|K_g|<=1`, and the only non-star possibility is the triangle case.

This is the exact old-witness persistence form of the anti-Horn residual.  Outside `K_g`, every usable
small deletion `D` with constant `c` satisfies

```text
deg_D(b_g)=c.
```

Thus an isolated old singleton is missed by the direction type, a complete old singleton is hit by it, an
anticomplete old pair is missed twice, a split old pair is hit once, and a complete old pair is hit twice.
In other words, away from the kernel the new direction type is invisible to all one- and two-vertex
co-regular witness tests: it has exactly the same count on each such deletion as the surviving old
witness vertices.

Therefore a unit-shift large fiber has only two possible exits.  If the family of co-regular singleton and
pair tests outside `K_g` separates the realized outgoing defects, anchored witness persistence plus
componentwise no-split forces the outgoing realized set to be a singleton.  If it does not separate them,
then two realized defects have identical values on every such test; their elementary difference is a
chamber-flat silent edge, and the one-corner lift route applies.  This is the promised `host-opppair123`
anti-Horn form: after deleting the kernel, failure of the old-side repair spectrum is exactly failure of a
realized no-split test, not a new arithmetic obstruction.

In the `sigma_g=2` branch the pair table simplifies further.  A split pair (`c=1`) has shifts
`a-1 in {3,0,1}`, so it never contributes shift `2`.  The only nonzero repairs are:

```text
c=0: anticomplete old pair with a=2, i.e. both deleted vertices lie in N_W(b_g);
c=2: complete old pair with a=0, i.e. both deleted vertices avoid N_W(b_g).
```

Thus the opposite-shift branch is not arbitrary: every surviving nonzero pair repair is either an
old-anticomplete pair fully inside the direction neighbourhood or an old-complete pair fully outside it.
It also has no nonzero singleton repairs.  Therefore any old vertex isolated from `W\{x}` in the
`r=0` singleton case must be missed by the direction type `b_g`, and any old vertex complete to
`W\{x}` in the `r=m-1` singleton case must be hit by `b_g`.  Equivalently, all usable singleton shifts
are forced to be zero in the `sigma_g=2` branch.

In repaired-residue language, `Rep(g)=d+Delta_<(4)(g)` is therefore contained in `{d,d+sigma_g}`.
For very large terminal directions the excluded pairs `{0,3}` and `{1,2}` remove two adjacent cases.
Thus:

```text
sigma_g unit:  Rep(g) subset {0,1} or {2,3};
sigma_g=2:     Rep(g) subset {0,2} or {1,3}.
```

This identifies the old-deletion branch with the sparse hereditary pairs: unit shifts are the
one-extreme/one-middle branches, while `sigma_g=2` is the opposite-parity branch.
Unpacked:

```text
{0,1}: alpha(C_g)<=3 and C_g is induced-2K_2-free;
{2,3}: omega(C_g)<=3 and C_g is induced-C_4-free;
{0,2}: alpha(C_g)<=3 and C_g is induced-C_4-free;
{1,3}: omega(C_g)<=3 and C_g is induced-2K_2-free.
```

Thus the unit branch leaves only the first line or its complement, and the `sigma_g=2` branch leaves
the two cross-parity lines.
After complementing the direction fiber if needed, the residual hereditary target is therefore only

```text
unit sigma_g:  alpha(C_g)<=3 and C_g is induced-2K_2-free;
sigma_g=2:     alpha(C_g)<=3 and C_g is induced-C_4-free.
```

This is the current exact-basis endpoint after all small old-deletion repairs are accounted for.

The standard cyclic blow-up obstruction is already controlled at this endpoint.  Suppose a residual
direction fiber has a five-cycle blow-up partition `A_0,...,A_4` (indices modulo `5`) in which each
`A_i` is a clique and the only cross edges are between consecutive bags.  A selection of `q_i` vertices
from `A_i` has bag-degree residues

```text
q_i-1+q_{i-1}+q_{i+1}.
```

Hence taking the same number `q` from each bag gives a regular induced subgraph of size `5q`.  If every
bag has size at least `floor(m/5)+1`, this immediately gives a congruent atom larger than `W`.  Otherwise
some bag, say `A_0`, has size at most `floor(m/5)`.  Since adjacent bag unions are cliques and every
clique in the direction has size at most `m`,

```text
|A_i|+|A_{i+1}|<=m        for all i,
```

and the five-cycle linear program with `|A_0|<=m/5` gives

```text
sum_i |A_i| <= 2m+floor(m/5) <= 11m/5.
```

Thus any C5-blow-up piece of size greater than `11m/5` already closes by an equal-bag atom.  The two
hereditary endpoints above therefore cannot be finished by exhibiting only the usual C5 blow-up
examples; a terminal very-large direction must use additional non-cyclic structure or boundary-type
constraints.

There is a stronger cap in the self-complementary orientation of the same blow-up.  View the five bags
as independent sets with complete joins between consecutive bags.  For three consecutive bags with
capacities `A,B,C`, choose

```text
x<=A,        y<=B,        z<=C,        y=x+z        [MOD 4],
```

with `x+z=A+C` and `y>=B-3`.  The selected endpoints have degree `y` and the selected middle vertices
have degree `x+z`, so the induced subgraph is congruent modulo `4` and has size at least `A+B+C-3`.
Terminality therefore forces every three consecutive bags to have total at most `m+3`, and summing the
five triple inequalities gives

```text
sum_i |A_i| <= (5m+15)/3.
```

Thus any cyclic blow-up component above `(5m+15)/3` is already closed by the three-class selector.  The
remaining hereditary endpoints are not the standard C5 blow-up pieces; they must avoid this
three-consecutive selector as well as the small-deletion spectrum constraints.

The two residual hereditary endpoints also have useful anchor decompositions.  In the unit branch,
where `C_g` is induced-`2K_2`-free with `alpha(C_g)<=3`, every edge `uv` is dominating up to three
vertices: the set anticomplete to `{u,v}` is independent, since an edge inside it together with `uv`
would be an induced `2K_2`.  Hence it has size at most `3`.  Thus a large unit-branch fiber is covered,
up to three vertices, by the two neighborhoods of any chosen edge.

In the `sigma_g=2` branch, where `C_g` is induced-`C_4`-free with `alpha(C_g)<=3` and clique number at
most `m`, every nonedge `uv` has both common parts controlled.  The common neighborhood
`N(u) cap N(v)` is a clique, otherwise two nonadjacent common neighbors form an induced `C_4` with
`u,v`; the common non-neighborhood is also a clique, otherwise it contains two vertices which together
with `u,v` form an independent four-set.  Therefore both have size at most `m`, and all remaining mass
lies in the two exclusive neighborhoods.  This converts the `sigma_g=2` endpoint into a two-sided
exclusive-neighborhood synchronization problem after discarding at most `2m` anchored common vertices.

The two anchor reductions have the same exact packet equation.  Let `p,q` be an anchor pair with
`epsilon=1_{pq}`, let `X` be selected vertices adjacent to `p` and not `q`, and let `Y` be selected
vertices adjacent to `q` and not `p`; ignore common-neighborhood vertices.  Then
`{p,q} union X union Y` has synchronized new-side degrees exactly when

```text
|X|=|Y|=h,
deg_{X union Y}(z)=h+epsilon-1        for every z in X union Y.      [MOD 4]
```

The anchor vertices then have degree `epsilon+h`, and each wing vertex has degree
`1+deg_{X union Y}(z)`.  Thus an edge anchor in the `2K_2`-free branch asks for an `h`-regular
equal-wing packet on `2h` vertices, while a nonedge anchor in the `C_4`-free branch asks for an
`(h-1)`-regular equal-wing packet.  In a single nonzero exact-basis direction this packet is
old-balanced only when

```text
2+2h=0        [MOD 4],
```

so `h` must be odd.  Then the packet appends to `W`, and any such packet contradicts maximality of
`W`.

The first case `h=1` is especially rigid.  For an edge anchor, a cross-edge between the two exclusive
wings gives a four-vertex `2`-regular atom; for a nonedge anchor, a cross-nonedge gives a four-vertex
`1`-regular atom.  Therefore terminality forbids these `h=1` patterns inside a nonzero exact-basis
direction.

Consequently the two sparse hereditary endpoints collapse further.  In the unit branch, which was
already induced-`2K_2`-free, any induced `C_4` would contain an edge anchor whose two exclusive opposite
vertices are cross-adjacent, giving the forbidden `h=1` atom.  Hence the unit branch is also
induced-`C_4`-free.  In the `sigma_g=2` branch, which was already induced-`C_4`-free, any induced
`2K_2` contains a nonedge anchor whose two exclusive opposite vertices are cross-nonadjacent, giving the
other forbidden `h=1` atom.  Hence it is also induced-`2K_2`-free.

Thus every terminal exact-basis hereditary endpoint is `(2K_2,C_4)`-free.  By the pseudo-split
structure theorem it is a clique joined to an independent set, possibly with a five-cycle core.  Since
one of the clique/independent sides is bounded by the old maximum clique cap `m` and the other by the
endpoint condition `alpha<=3` after complementing if necessary, every such direction has size at most

```text
m+8.
```

This eliminates the very-large exact-basis direction branch after the small old-deletion repair spectrum
and the `h=1` anchor atom are included.

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

The complement operation swaps the first and last cases, and swaps the two middle cases.  Before the
equal-wing anchor atom is used, this reduces the large exact-basis endpoint to two sparse hereditary
branches up to complement: `alpha<=3` plus `2K_2`-free, and `alpha<=3` plus induced-`C_4`-free.  The
`h=1` anchor atom above then makes each branch also avoid the complementary four-vertex pattern, so the
exact-basis direction is pseudo-split and has size at most `m+8`.  Thus the following chromatic caution is
only a warning against an obsolete route, not a remaining exact-basis obstruction.

The tempting chromatic shortcut for the `2K_2` branch is false and must not be imported.  The proposed
estimate

```text
chi(G) <= omega(G)+1        for 2K_2-free graphs with alpha(G)<=3
```

fails already for the join of two `C_5`'s: it is `2K_2`-free because its complement is the disjoint union
of two `C_5`'s and hence is induced-`C_4`-free; it has `alpha=2`, `omega=4`, and `chi=6`.  More generally,
the join of `k` copies of `C_5` has `alpha=2`, `omega=2k`, and `chi=3k`, so even an additive
`omega+O(1)` bound is impossible.  The exact-basis proof avoids this by using the `h=1` anchor atom
rather than colouring.

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

The latter global information has a concrete four-layer form in the single-boundary-type residual.  Keep
the notation `L=H-r`, and partition the retained direction fiber by the target label

```text
A_j={u in B : theta_X(u)=L+j},        j in Z/4Z.
```

Suppose a boundary copy `z in X_i` has constant adjacency `epsilon in {0,1}` to the retained type under
consideration; this is exactly the situation when all retained vertices have one boundary type.  For the
same-old-vector singleton exchange importing `z` and exporting any `y in B`, target-stability gives

```text
epsilon=0:   |N_G(y) cap A_{-1}| <= |N_G(y) cap A_0|+1,
epsilon=1:   |A_1 \ N_G(y)|      <= |A_0 \ N_G(y)|+1,
```

where `G` is the original direction graph, indices are modulo `4`, and the `+1` absorbs the exported or
imported vertex.  These are not hereditary restrictions; they are no-improving-swap inequalities forced
by the maximal target choice.  Thus in a one-type `{0,1}`/`{3,2}` residual with both a boundary miss and
a boundary hit, the off-target layer `A_{-1}` is neighbourhood-dominated by the target layer `A_0`, while
`A_1` is co-neighbourhood-dominated by `A_0`.  The remaining proof can now target this labelled
induced-`C_4`-free, `K_4`-free graph rather than an unlabelled hereditary graph.

Two-boundary-copy exchanges reach the opposite label layer.  Import boundary copies `z_1,z_2` with
constant retained adjacencies `epsilon_1,epsilon_2` and put `t=epsilon_1+epsilon_2`.  Export a retained
pair `Y={y_1,y_2}` with the same old-vector sum.  For `u in B\Y`,

```text
theta'(u)=theta(u)+deg_Y(u)-t.
```

Therefore target-stability gives the uniform inequality

```text
sum_{k=0}^2 |{u in A_{t-k}: deg_Y(u)=k, t-k != 0}|
   <= sum_{k != t} |{u in A_0: deg_Y(u)=k}| + O(1),
```

where the `O(1)` accounts only for the two exported/imported vertices.  In particular:

```text
t=0: |A_{-1} cap (N(y_1) triangle N(y_2))|
     + |A_{-2} cap N(y_1) cap N(y_2)|
     <= |A_0 cap (N(y_1) union N(y_2))| + O(1);

t=2: |A_1 cap (N(y_1) triangle N(y_2))|
     + |A_2 \ (N(y_1) union N(y_2))|
     <= |A_0 \ (N(y_1) cap N(y_2))| + O(1).
```

Thus a same-type residual with two boundary hits cannot hide most of its mass in `A_2` unless every
retained pair nearly dominates that mass; dually, two boundary misses force `A_{-2}` into common
neighbourhoods paid for by the target layer.  This second-order labelled domination is the first
constraint on the label opposite the target and is the natural target-stability replacement for the
failed unlabelled colouring route.

The same formula holds for the whole boundary triple.  If `Z subset X_i` has size `s<=3`, total constant
adjacency `t=sum_{z in Z} epsilon_z` to the one retained type, and `Y subset B` is an exported same-size
same-direction set, then for `u in B\Y`

```text
theta'(u)=theta(u)+deg_Y(u)-t.
```

Target-stability therefore yields the hierarchy

```text
sum_{k=0}^s |{u in A_{t-k}: deg_Y(u)=k, t-k != 0}|
   <= sum_{k != t} |{u in A_0: deg_Y(u)=k}| + O(s).
```

For the model type `110`, importing the whole boundary triple has `s=3` and `t=2`; it simultaneously
controls `A_2` through vertices missing the exported triple, `A_1` through vertices seeing one exported
vertex, and `A_{-1}` through vertices seeing all three.  Thus the final same-type residual must satisfy
all singleton, pair, and triple label-gradient inequalities induced by the boundary triple.

It already closes the empty-target degeneration.  Suppose `A_0=empty` and the retained boundary type has
both a miss and two hits, as in the model type `110` up to complement.  The singleton miss inequality
forces `A_{-1}` to be anti-complete to `B` in `G`, hence `A_{-1}` is a clique in the complement `H` and
has size at most `3`.  The singleton hit inequality forces `A_1` to be complete to `B` in `G`, hence
`A_1` is independent in `H` and has size at most `m`.  Finally, the two-hit pair inequality has no target
side to pay for missed vertices; exact target-stability therefore forces every retained pair to dominate
`A_2` in `G`.  Equivalently, every vertex of `A_2` has at most one neighbour in the complement `H`, so
`H[A_2]` has maximum degree at most one and is capped by the induced-degree-two terminal exclusion.  Thus

```text
A_0=empty        =>        |B| <= 2m+O(1)
```

Lean formalization note.  The labelled layer-gradient surface is now named in
`RegularInducedSubgraph/Modular/Asymptotic.lean`:
`SingletonMissLayerGradient`, `SingletonHitLayerGradient`,
`TwoHitPairLayerGradient`, and `TwoMissPairLayerGradient`.  The empty-target
bridge
`oneBoundary_emptyTarget_card_le_two_mul_add_three_of_layerGradients`
proves the concrete cap `|B| <= 2m+3` from the no-slack miss gradient, the
one-slack hit gradient, the exact two-hit domination gradient, and the existing
clique/independence caps.

This is the formal version of the empty-target degeneration in the one-type residual.  Any large
surviving `{0,1}`/`{3,2}` branch must therefore have a nonempty
target layer `A_0`; the final obstruction is not an unlabelled hereditary graph but a labelled graph
whose off-target layers are dominated by, or paid for by, the target layer.

On the target layer the pure-discard test becomes especially explicit.  Let

```text
D_q={u in A_0 : deg_B(u)=q [MOD 4]}.
```

For any four-set `S subset D_q` in one exact direction, the complement `B\S` is still old-balanced and
`delta_{B\S}=delta_B`.  Since `theta_X=L` on `S`, the pure-discard equation reduces to

```text
deg_S(s)=q-delta_B        for every s in S.
```

Thus a terminal target layer has the following residue-sliced forbidden-pattern property: each degree
slice `D_q` avoids the single four-vertex regular graph of degree `q-delta_B`.  This is weaker than
Ramsey, because one slice may only forbid independent fours, another only `2K_2`, another only `C_4`, and
another only cliques.  But it is now localized: the remaining nonempty-target obstruction is a
four-coloured target layer with one specified forbidden regular pattern in each colour, together with the
singleton and pair target-stability domination inequalities on the off-target layers.

The same pure-discard calculation applies to mixed colour sets.  Put

```text
c(u)=deg_B(u)-delta_B        in {0,1,2,3},        u in A_0.
```

Then terminality forbids every four-set `S subset A_0` satisfying the self-degree equation

```text
deg_{G[S]}(u)=c(u)        for every u in S.
```

This colour-realization rule immediately caps two of the four target colours.  The colour `3` slice has
no clique four and still has independence number at most three, so it is Ramsey-bounded.  The colour `2`
slice is both induced-`2K_2`-free (from the `{0,1}` branch) and induced-`C_4`-free (from the target
slice rule), so the pseudo-split cap gives

```text
|D_{\delta_B+2}| <= 2m+O(1).
```

Thus the only target colours that can still carry large mass are the two redundant-pattern slices:
colour `0`, where the forbidden pattern is already the global independent-four exclusion, and colour
`1`, where it is already the global `2K_2` exclusion.

There is nevertheless a mixed-colour domination constraint between these two dangerous slices.  If
`a,b` are nonadjacent vertices of colour `0`, then the common non-neighbour set of `{a,b}` inside the
colour `1` slice is independent in `G`; otherwise an edge `uv` in that common non-neighbour set would
make `{a,b,u,v}` self-degree-coloured with degrees `(0,0,1,1)`.  Since `alpha(G)<=3`, every independent
pair in colour `0` dominates all but at most three colour-`1` vertices.  Consequently, either colour `0`
is clique-bounded by `m`, or colour `1` is uniformly two-dominated from colour `0` up to an `O(1)`
exception.  This is now the unique large target-layer configuration not already linearly capped.

Combining the same mixed-colour rule with the complement structure improves the exception and gives a
usable edge-anchor decomposition.  Work in the complement `H`, and let `ab` be the edge corresponding to
a nonedge in the colour `0` slice.  A colour-`1` vertex adjacent to both `a` and `b` in `H` is a common
non-neighbour of the independent pair in `G`.  There is at most one such vertex: two common neighbours
adjacent in `H` form a `K_4` with `a,b`, while two common neighbours nonadjacent in `H` are adjacent in
`G` and are forbidden by the `(0,0,1,1)` pure-discard rule.

All other colour-`1` vertices split, relative to the edge `ab`, into

```text
Y_a=N_H(a)\N_H(b),        Y_b=N_H(b)\N_H(a),        Y_0=V\N_H({a,b}).
```

The exclusive layers `Y_a` and `Y_b` are anti-complete to each other in `H`; an edge between them would
induce the four-cycle `y-a-b-z-y`.  Each of `Y_a,Y_b` is triangle-free, since a triangle in `Y_a` with
the anchor `a` would form a `K_4`, and similarly for `Y_b`; both are induced-`C_4`-free by heredity.
Moreover

```text
alpha_H(Y_a)+alpha_H(Y_b) <= alpha(H) <= m
```

because the layers are anti-complete in `H`.  Hence if the exclusive layers are bipartite they have total
size at most `2m`; if not, their shortest odd cores have total length at most `m` by the same
degree-two terminal exclusion.  Around those odd cores, the same distance-three pendant quotient applies;
because the exclusive layers have alpha-sum at most `m`, their first-core pendant fibres have total size
at most `3m`.  Thus a non-clique colour-`0` slice reduces the large colour-`1` mass to the zero-layer
`Y_0` plus iterated zero-trace remainders inside the exclusive layers.

Consequently the target layer has a clean dichotomy.  If colour `0` is a clique, it contributes at most
`m` and the only large target mass is the colour-`1` induced-`2K_2`-free slice, subject to the global
triangle/odd-core zero-trace analysis below.  If colour `0` is not a clique, any nonedge in it supplies
the edge-anchor decomposition above and again pushes colour `1` into controlled exclusive layers plus a
zero-trace residual.  Thus every surviving large target-layer configuration is an iterated zero-trace
configuration; no further unanchored colour pattern remains.

This also identifies the exact irreducible local core.  All off-target layers may be empty, colour `0`
may be empty or clique-bounded, and the target layer may lie entirely in colour `1`.  In that situation
the singleton/pair/triple target-stability inequalities have no off-target side to constrain, and the
pure-discard rule is exactly the retained-only `2K_2` exclusion.  Equivalently, in the complement one is
left with an induced-`C_4`-free, `K_4`-free graph `H` with

```text
alpha(H)<=m,
no induced Delta<=2 subgraph on more than 11m/5 vertices,
```

and no additional local boundary-table or target-stability inequality visible.  Thus the remaining proof
must supply a genuine selector theorem for this complement class, or use a global feature not present in
the single-fiber local model.  The previous reductions are complete up to this all-target colour-`1`
core; they cannot honestly be pushed to a contradiction by more finite mixed-table case analysis alone.

One last structural consequence survives even in this core.  For any edge `ab` of the complement `H`,
the common neighbourhood `N_H(a) cap N_H(b)` has size at most two, since `H` is `K_4`-free.  The exclusive
layers `N_H(a)\N_H(b)` and `N_H(b)\N_H(a)` are anti-complete to each other, triangle-free, and
induced-`C_4`-free exactly as above.  Therefore every edge anchor decomposes `H` into controlled
exclusive layers plus the zero-neighbour layer

```text
Z_{ab}=V(H)\(N_H(a) union N_H(b) union {a,b}).
```

If `Z_{ab}` is small for some edge, the whole core is linearly bounded by the exclusive-layer and
pendant-fibre estimates.  Hence any superlinear counterexample inside the irreducible core must be
edge-robust:

```text
|Z_{ab}| is large for every edge ab of H.
```

Equivalently, no edge anchor captures a positive fraction of the graph by its two one-sided
neighbourhoods.  This is a much narrower form of the final selector problem: an induced-`C_4`-free,
`K_4`-free, edge-robust graph with bounded independence and no large induced degree-two subgraph.

The core also admits a maximal induced-matching skeleton.  Let `M` be a maximal induced matching in `H`.
If `|M|>m/2`, then the `2|M|` endpoints induce degree one in `H`, hence a congruent outside-only set in
the original direction graph, contradicting maximality of `W`.  Therefore

```text
|M| <= m/2.
```

By maximality of `M`, the vertices anti-complete to all endpoints of `M` form an independent set, hence
have size at most `m`; otherwise an edge inside that residual could be added to `M`.  Consequently the
irreducible core is covered by

```text
at most m/2 induced-matching edges,
their endpoint neighbourhoods,
and one independent residual of size at most m.
```

For each matching edge `ab`, its common neighbourhood has size at most two and its exclusive
neighbourhoods have the edge-anchor structure above.  Thus the final missing charging problem can be
stated without recursion: bound the total mass in the endpoint-exclusive neighbourhoods of a maximal
induced matching in an induced-`C_4`-free, `K_4`-free graph with `alpha<=m`, using the fact that these
neighbourhoods cannot contain a further large induced matching, odd-core, or independent trace family.

The final local theorem can now be stated cleanly.  For each edge `e_i=a_i b_i in M`, assign every vertex
outside the endpoint set and outside the independent residual to one incident matching edge and one side,
and write the assigned exclusive classes as

```text
E_i^a subset N_H(a_i)\N_H(b_i),        E_i^b subset N_H(b_i)\N_H(a_i).
```

The common-neighbour assignments contribute only `O(m)` in total, since each matching edge has at most
two common neighbours and `|M|<=m/2`.  For every `i`, the pair `E_i^a,E_i^b` is anti-complete in `H`,
each side is triangle-free and induced-`C_4`-free, and

```text
alpha(E_i^a)+alpha(E_i^b) <= m.
```

The required **endpoint-exclusive charging lemma** is:

```text
sum_i (|E_i^a|+|E_i^b|) = O(m).
```

Once this lemma is available, the all-target colour-`1` core is linearly bounded: endpoints contribute at
most `m`, common neighbours at most `m`, the independent residual at most `m`, and the exclusive
neighbourhoods by the displayed lemma.  This is the exact remaining mathematical endpoint of the
`{0,1}`/`{3,2}` branch.

The charging lemma is not a purely matching-theoretic statement; it contains the true last selector
problem.  Indeed, one endpoint-exclusive side may be a whole triangle-free, induced-`C_4`-free graph
attached to a single endpoint `a` and missed by the mate `b`.  Adding the edge `ab` and joining `a` to
that layer preserves induced-`C_4`-freeness and `K_4`-freeness exactly when the layer is triangle-free
and induced-`C_4`-free.  The previous degree-two condition is only the visible small-subgraph shadow of
the actual terminal condition.  In the all-target colour-`1` core, for every same-direction subset
`S` with `|S|=0 [MOD 4]`, pure discard closes exactly when

```text
deg_G[S](s)=1        for every s in S,
```

or equivalently in the complement layer `F`,

```text
deg_F[S](s)=2        [MOD 4]        for every s in S.
```

Thus the endpoint-exclusive charging lemma is equivalent, at its core, to the following standalone
mod-`4` layer theorem:

```text
Triangle-free C4-free mod-2-degree layer selector.
If F is triangle-free and induced-C4-free, alpha(F)<=m, and no nonempty induced
S subset F with |S|=0 [MOD 4] has all degrees 2 [MOD 4], then |F|=O(m).
```

The earlier induced-`Delta<=2` bound follows from this theorem by applying Yuster's
`11(k-1)/5` path/cycle lemma to any induced maximum-degree-two subgraph, but it is not by itself the
whole obstruction.  The bipartite case gives `|F|<=2m`; the non-bipartite case reduces to a shortest odd
core, distance-three pendant quotient, and a zero-trace remainder as above.  This mod-`4` layer theorem
is now the exact irreducible mathematical target.

The mod-`4` layer theorem has a direct linear proof.  If the current layer is bipartite, its two parts
are independent, so it has size at most `2m`.  Otherwise choose a shortest odd cycle `C`.  It is induced,
every outside vertex has at most one neighbour on `C`, and nonzero pendant fibres over `C` have quotient
maximum degree two; hence their total size is at most `3 alpha(F)<=3m`.  Remove `C` and these nonzero
fibres and continue inside the zero-trace layer.

The chosen odd cores in this recursion are pairwise anti-complete.  If their lengths contain a nonempty
subsum equal to `0 mod 4`, the corresponding union is an induced subgraph with all degrees exactly `2`
and size `0 mod 4`, forbidden by the mod-`4` terminal condition.  Since the core lengths are odd, any
four cores of the same residue mod `4`, or any pair of opposite residues `1` and `3`, would give such a
subsum.  Therefore at most three odd cores are chosen, and all have the same residue mod `4`.  Their
total size is also at most `11m/5` by the induced-`Delta<=2` shadow.  Consequently

```text
|F| <= (11/5)m + 3*(3m) + 2m = (66/5)m.
```

Thus the endpoint-exclusive layer is linearly bounded.  The constant is crude but sufficient for the
local all-target colour-`1` core; improving it is now a bookkeeping issue rather than a structural gap.

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

The iteration has a bounded skeleton.  Run the zero-trace peeling greedily, each time choosing inside the
current zero layer either an edge anchor, a triangle anchor, or a shortest odd cycle according to the
first non-bipartite/non-clique obstruction present, and then passing to the vertices with zero trace to
that anchor.  By construction every later anchor is anti-complete in `H` to every earlier anchor.  Hence
the union of all chosen anchors is an induced graph of maximum degree at most two.  The terminal
degree-two exclusion therefore gives

```text
sum |anchor_i| <= 11m/5.
```

Thus the zero-trace recursion cannot hide an unbounded number of independent cores.  The only remaining
estimate needed to close the labelled `{0,1}`/`{3,2}` branch is a charging of the pendant/trace layers to
the global independence budget across this bounded anchor skeleton.

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
augmented exact-basis branch.  The finite cube residual is therefore closed.  The corrected
`{0,1}`/`{3,2}` complement branch is no longer a mere degree-two conditional: target-stability reduces
it to the all-target colour-`1` core, and the endpoint-exclusive mod-`4` layer theorem above linearly
caps that core.  The separate
chain/C5 arithmetic cap no longer needs an assumption: `hasThreeConsecutiveClassModFourSelector`
proves the three-class selector, and
`threeConsecutiveClass_card_le_add_three_of_modFour_terminal_exclusion_unconditional` applies it.

The support-six parity-compression residual has also been reduced one layer.  The original
`HasPolynomialCostFixedWitnessLargeNonhomogeneousBoundaryFiberSelectionFiveFromSeven` now follows from
the internal fiber selector
`HasPolynomialCostFixedWitnessLargeNonhomogeneousBoundaryFiberModEqSelectionFiveFromSeven`, and a
regular induced `2^j`-bucket inside the same fiber is enough via
`HasPolynomialCostFixedWitnessLargeNonhomogeneousBoundaryFiberRegularSelectionFiveFromSeven`.  These
bridges connect directly to
`HasPolynomialCostFixedWitnessTerminalBoundaryAtomOrParityCompressionSelectionFiveFromSeven`, so the
only graph-theoretic content left in that branch is the internal modular/regular subbucket in a large
nonhomogeneous boundary fiber.

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

The outside-only maximum constraint already rules out the large version of this toy model.  In the
disjoint-clique example, taking four vertices from each of `t` clique directions gives an outside-only
induced subgraph in which every selected vertex has degree `3 mod 4`; hence `4t<=m` in a genuine
terminal counterexample.  More generally, any family of pairwise cross-regular four-blocks with the same
total row-sum residue gives an outside-only congruent witness; if its total size exceeds `m`, it
contradicts maximality of `W` even when the residue is not the append residue required to join `W`.
Thus the retained-only branch has two exits:

```text
append exit:       block defects are repaired to residue r relative to W;
outside-only exit: selected blocks have equal total degree residue internally.
```

The exact-basis obstruction must avoid both exits simultaneously.

Every large retained direction supplies wrong-residue regular blocks.  If `C_i` avoids its required
append residue `d_i`, then Ramsey still gives a regular four-block of another residue once `|C_i|>=R(4,4)`:
if `d_i=0`, a clique four-block gives residue `3`; if `d_i=3`, an independent four-block gives residue
`0`; and if `d_i in {1,2}`, Ramsey gives either an independent or a clique four-block, of residue `0`
or `3`.  Thus a terminal exact-basis configuration contains a reservoir of regular four-blocks whose
internal residues are known not to be append residues.  The retained-only obstruction is therefore not
absence of regular blocks; it is the simultaneous failure of:

```text
wrong-residue blocks + cross-edges repair to append residue;
wrong-residue blocks + cross-edges synchronize to an outside-only residue.
```

This is the precise dual-exit bounded-block selector left by the exact-basis reduction.

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

This gives a useful amplification diagnostic.  Fix `L == 0 [MOD 4]`.  In any direction whose retained
fiber has at least `R(L,L)` vertices and avoids the required append residue `d_i`, Ramsey supplies an
`L`-vertex regular block of residue `q_i in {0,3}` with `q_i != d_i` when `d_i` is extreme, and with
`q_i` one of the two extreme wrong residues when `d_i` is middle.  Replacing four-blocks by these
`L`-blocks changes none of the equations except the surplus threshold:

```text
append:       q_i + sum_{j != i} deg_{P_j}(v) = d_i       for v in P_i,
outside-only: q_i + sum_{j != i} deg_{P_j}(v) = Q         for v in P_i,
              sum_i |P_i| > m.
```

Thus large homogeneous reservoirs amplify any block-level selector.  In particular, a no-cross family
of same-residue `L`-blocks has size at most `m/L` in a terminal counterexample.  This kills the
disjoint-clique toy model at every scale, not only for four-blocks.

The same observation also identifies the sparse-import barrier.  The retained lower bound alone can be
spread over only linearly many one-vertex imports; then the available old-balanced augmented blocks
`X_i union {b}` still have size four, and an outside-only contradiction cannot be forced from them
without using a block-level selector of density greater than `1/4`.  Therefore the exact-basis endpoint
has a genuine dichotomy:

```text
heavy retained reservoirs  -> amplified wrong-residue blocks must synchronize or append;
sparse retained imports    -> the missing mass must come from boundary triples X_i.
```

Consequently the remaining theorem is not a finite same-direction Ramsey statement.  It is a
boundary-decorated one-large-class selector: the boundary triples provide almost `3m` outside vertices
but are zero-sum-free, so they can only help through outside-only maximality or through explicit
coordinate exchanges with the sparse retained imports.

This selector can be stated exactly as a finite-alphabet problem.  For each basis direction put
`A_i=X_i union C_i` and let a **word** be a subset `P_i subset A_i`; for `v in P_i` write
`q_i(P_i,v)=deg_{P_i}(v)`.  A family of words `(P_i)` gives an outside-only exit precisely when

```text
q_i(P_i,v)+sum_{j != i} deg_{P_j}(v)=Q       for every v in P_i,
sum_i |P_i|>m.
```

It gives an append/import exit when, in addition, the old coordinate count in every direction is
`0 [MOD 4]` and the displayed common residue is the direction's append residue relative to `W` after
the chosen old-side correction.  Thus the sparse exact-basis obstruction is now a finite-alphabet
row-sum theorem on decorated boundary triples.  The alphabet is small in the diffuse-retained regime,
but the required density is high: whole boundary triples have size three, so an outside-only proof must
select more than one third of the available directions on average.  This is the precise form of the
boundary-decorated one-large-class target left after the amplified retained reservoirs are removed.

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

The cross-isolated statement is actually stronger and does not depend on the internal triple type.
Let `I` be a set of boundary directions such that there are no edges between distinct triples
`X_i, X_j` for `i,j in I`.  If `t=|I|` and `a` of these triples are triangles, then either
`3a>m`, in which case the union of the triangle triples is an outside-only residue-`2` witness, or
`a<=m/3`.  In the second case choose, from every non-triangle triple, a nonedge pair, and from every
triangle triple, one vertex.  All chosen vertices then have internal degree `0` and no cross-degree, and
the selected size is

```text
2(t-a)+a = 2t-a >= 2t-m/3.
```

Thus any cross-isolated family with `t>2m/3` gives an outside-only residue-`0` witness of size
greater than `m`.  A terminal exact-basis boundary therefore has no cross-isolated subfamily of more
than `2m/3` coordinate triples.  This is the first finite-alphabet closure beyond the homogeneous
independent/triangle toy cases: even one-edge and path triples supply residue-`0` nonedge pairs.

By complementing the boundary graph on the chosen triples, the same bound excludes cross-complete
families.  If all edges between distinct triples in `I` are present, then in the complement those triples
are cross-isolated.  The selector above gives a set `S` with all degrees congruent in the complemented
induced graph.  Since

```text
deg_G[S](v)=|S|-1-deg_{\bar G[S]}(v),
```

the original degrees are congruent as well.  Hence a terminal boundary has neither a cross-empty nor a
cross-complete subfamily of more than `2m/3` coordinate triples.  Any surviving sparse boundary
obstruction must therefore contain a genuinely mixed cross-interaction graph on every supercritical
subfamily of triples.

There is also a useful parity-tight form when the cross-interaction is homogeneous but not constant.
Suppose a family `I` of non-triangle boundary triples has the property that every pair of triples is
cross-empty or cross-complete; let `Q` be the quotient graph recording cross-complete pairs.  Each
triple in `I` has a nonedge pair of internal residue `0`.  Hence, for any `U subset I` with `Q[U]`
even, selecting such a pair from every triple of `U` gives an outside-only residue-`0` set of size
`2|U|`, because every selected vertex sees `2 deg_{Q[U]}(i)=0 [MOD 4]` outside its own triple.
Consequently terminality forces every even induced subgraph of `Q` to have size at most `m/2`.
Gallai's theorem is therefore tight on any homogeneous non-triangle quotient that remains near the
critical density.

The tight case has little room for outside vertices.  Let `U` be an even quotient set with
`2|U|>=m-1`.  If a non-triangle triple `X_j` outside `U` is cross-empty to all triples of `U`, then
adding a nonedge pair from `X_j` preserves residue `0` and gives size `2|U|+2>m`.  If `X_j` is
cross-complete to all triples of `U` and `|U|` is odd, the same addition gives residue `2` on every
selected vertex.  Thus a terminal homogeneous quotient must not only be Gallai-half-tight; every
outside non-triangle coordinate must have a genuinely mixed neighbourhood into each near-half even
quotient class (except for the complete case when `|U|` is even).  This is the homogeneous-quotient
version of the finite-alphabet mixed-interaction barrier.

The pair-word quotient is slightly stronger: it only needs constant quotient degree parity, not evenness.
If every selected triple contributes a two-vertex regular word of internal residue `q_pair`, then every
selected vertex has residue

```text
q_pair + 2 deg_{Q[U]}(i)       [MOD 4].
```

Thus any induced quotient set `U` on which all degrees have one parity gives a pair-word outside-only
selector of size `2|U|`.  For non-triangle triples take a nonedge pair and `q_pair=0`; for triangle
triples take an edge pair and `q_pair=1`.  Hence terminality forces Gallai-half tightness separately on
both pair-residue classes:

```text
non-triangle triples: pair residue 0,
triangle triples:     pair residue 1.
```

A mixed homogeneous quotient can survive only by balancing these two pair-residue classes so that
neither class contains a near-half constant-parity quotient selector with an augmenting same-class
outside triple.  The earlier even-quotient statements are the residue-preserving subcase; odd quotient
degree simply shifts the common residue by `2`.

Gallai now leaves only a narrow size deficit.  In a same pair-residue class of `n` homogeneous triples,
Gallai's even/even partition supplies a constant-parity quotient set of size at least `ceil(n/2)`, hence
a pair-word selector of size at least `2 ceil(n/2)`.  Therefore the class closes immediately if
`2 ceil(n/2)>m`.  At the exact Davenport boundary `n<=m-1`, the only possible failures have deficit at
most two:

```text
m even, n=m-1:  pair selector size at least m;
m odd,  n=m-1:  pair selector size at least m-1.
```

Thus a terminal same-residue homogeneous class occupying almost all coordinates must prevent every
one-word or two-word augmentation of this Gallai half.  The residual obstruction is not a large pair
selector; it is a one- or two-vertex augmentation failure at the boundary of the zero-sum-free basis.

For one outside word the obstruction is explicit.  Let `U` be a constant-parity pair-word selector with
common residue `R`, and let `P_j` be a regular word in an outside triple with size `s` and internal
residue `q_j`.  In a homogeneous quotient, appending `P_j` preserves congruence only if its quotient
neighbourhood into `U` is uniform; write `a=0` for cross-empty to all of `U` and `a=1` for
cross-complete to all of `U`.  The appended set is congruent exactly when

```text
q_j + 2a|U| = R + as        [MOD 4].
```

Thus terminality forbids every outside regular word satisfying this one-line congruence.  In the
`m`-even boundary case, where the Gallai pair selector already has size `m`, this one-word test is
enough: any successful outside word gives size `>m`.  In the `m`-odd boundary case the pair selector may
have size only `m-1`; then either one word of size at least two satisfies the displayed test, or the
only remaining augmentation is a two-singleton/two-word equation in which the two outside quotient
neighbourhood columns have constant weighted sum on `U`.  Hence the final homogeneous boundary check is
finite and local around at most two outside triples.

The exact one-word equation is slightly more general than the regular-word shorthand.  Let
`S=union_{i in U} P_i` be the base pair selector.  A word `P` disjoint from `S` augments it iff there is
`K` such that

```text
deg_P(x)=K                         for every x in S,
deg_P(u)+deg_S(u)=R+K              for every u in P.       [MOD 4]
```

Thus internal nonregularity of `P` is allowed, but only if its degree into the selected boundary pairs
compensates it pointwise.  The previous regular/uniform formula is the scalar subcase
`deg_P(u)=q_j` and `deg_S(u)=2a|U|`.

Explicitly, for two outside regular words `P_j,P_k` of sizes `s_j,s_k`, internal residues `q_j,q_k`,
and quotient columns `a_j,a_k:U->{0,1}`, put `b=1` if the two outside triples are cross-complete and
`b=0` if they are cross-empty.  They augment the base selector iff there is a residue `K` such that

```text
s_j a_j(i)+s_k a_k(i)=K                         for every i in U,
q_j+2 sum_U a_j + b s_k = R+K,
q_k+2 sum_U a_k + b s_j = R+K                  [MOD 4].
```

For the genuine deficit-two case `s_j=s_k=1`, this says that the two quotient columns are either
complementary on `U`, both constantly zero, or both constantly one; a nonconstant equal pair would give
row sums `0` and `2` and is not allowed.  Their column sums must also have the parity forced by the last
two displayed equations.  Thus the odd-`m` homogeneous residual is a two-column parity obstruction, not
an unstructured boundary selector.

The exact two-word equation has the same form: for outside words `P,Q` one needs

```text
deg_P(x)+deg_Q(x)=K                         for every x in S,
deg_P(u)+deg_Q(u)+deg_S(u)=R+K              for every u in P union Q.       [MOD 4]
```

Again the weighted-column formulas above are the scalar case in which `P` and `Q` have constant internal
degree and homogeneous cross-adjacency.  Therefore the finite residual is best viewed as a bounded-word
compensation table over at most two outside triples, not merely as a regular-word table.

For one outside exact-basis direction, this bounded-word table is finite.  Write
`A_j=X_j union C_j`, and for `z in C_j` record its three-bit boundary trace to `X_j`.  A one-word
augmentation contained in `A_j` is determined by a subset of the boundary triple and at most one retained
vertex in the sparse-import regime.  The exact equation above says:

```text
for P subset X_j:              internal degrees of P plus its base-column are constant;
for P=Y union {z}:             deg_Y(y)+1_{zy}+base_y is constant on y in Y,
                               deg_Y(z)+base_z has the same value;
for P using two retained z,z': the two retained columns into Y must compensate both
                               their mutual edge and the boundary degrees of Y.
```

Thus the equality residual can be checked direction-by-direction by the same `3+1`, `2+2`, and `1+3`
tables used for append atoms, with the append residue `d_i` replaced by the current base residue
`R+K` and with an additional base-column term.  No new large object is hidden here: after the pair-word
selector is fixed, every one- or two-word augmentation is a bounded augmented-fiber pattern.

The same equations apply to retained imports, and this is essential in the equality case.  A retained
singleton `z in C_j` is an outside word of size `1` and internal residue `0`.  It augments a pair-word
selector `U` only if it is pair-uniform on the chosen boundary pairs: for every selected pair
`P_i subset X_i`, the two adjacencies from `z` to `P_i` are equal, and this common bit is independent of
`i`.  If the common bit is `a`, the one-word congruence becomes

```text
2a|U| = R+a        [MOD 4].
```

Thus every terminal equality-size boundary selector imposes a concrete forbidden trace on all retained
singletons.  In the deficit-two case, two retained singletons `z,z'` augment exactly when their
pair-uniformity defects cancel: the two columns on the selected boundary pairs are complementary, both
constantly zero, or both constantly one, and their column sums satisfy the two displayed two-word
congruences with `q_j=q_k=0` and `s_j=s_k=1`.
Hence the exact-boundary residual is coupled to the retained side by a two-column trace condition; it is
not a purely boundary-internal obstruction.

For retained singletons the congruence table is tiny.  A single retained vertex closes iff either

```text
it misses every selected boundary-pair vertex and R=0,
or it hits every selected boundary-pair vertex and R=2|U|-1 [MOD 4].
```

For two retained vertices, let `b` be their mutual edge and let `alpha` be the number of selected
boundary pairs hit by the first retained vertex in the complementary-column case.  Then:

```text
both columns 0:        b=R                         [MOD 4],
both columns 1:        2|U|+b=R+2                  [MOD 4],
complementary columns: |U| even and 2alpha+b=R+1   [MOD 4].
```

Since `b in {0,1}`, the first two lines are often empty by residue alone.  The only genuinely flexible
two-retained augmentation is the complementary-column line, and even that requires `|U|` even and fixes
the parity of `alpha`.  This converts the retained equality residual into a finite trace-avoidance table.

Equivalently, partition the retained singletons by their pair-uniform column
`c:U->{0,1}`.  Terminality imposes the following hereditary constraints on these trace classes:

```text
c=0:        if R=0 the class is empty; if R=1 it is independent;
            residues R=2,3 impose no two-vertex condition;
c=1:        the singleton line forbids the class when R=2|U|-1;
            the pair line uses the residue R+2-2|U| in place of R;
c and 1-c:  when |U| is even, edges between the two classes of a column c with
            alpha=|c^{-1}(1)| must avoid b=R+1-2alpha whenever this residue is 0 or 1.
```

Thus the equality residual has exactly the same shape as the earlier four-block repair spectrum: large
retained trace classes are possible only in the residue holes of this table, and complementary trace
classes must have a forced edge status unless the required status is outside `{0,1}`.  Any final closure
can now target these finitely many column-hole cases.

The pair-uniform table is only the scalar subcase of the full two-retained equation.  For arbitrary
retained singletons `z,z'`, write the two adjacencies from `z` to the selected boundary pair
`P_i={x_i,y_i}` as a bit pair `h_i(z)=(zx_i,zy_i)`.  Then `z,z'` augment the base pair selector iff
there is `K in {0,1,2}` such that, for every `i in U`,

```text
zx_i+z'x_i = K,
zy_i+z'y_i = K,
deg_U(z)+b = R+K,
deg_U(z')+b = R+K       [MOD 4],
```

where `b=1_{zz'}` and `deg_U(z)=sum_i(zx_i+zy_i)`.  Thus either both retained vertices miss every
selected boundary vertex (`K=0`), both hit every selected boundary vertex (`K=2`), or their bit-columns
are complementary on every selected boundary vertex (`K=1`).  The last case allows non-pair-uniform
vertices, but only in complementary pairs with the displayed total-degree congruences.  Hence the
true retained equality residual is a bit-column complement obstruction; pair-uniform columns are just
its quotient by the two coordinates inside each selected pair.

Moreover, this split is forced by parity: if all selected words have size two, every cross-word
contribution is even (`0` or `2` modulo `4` in the homogeneous quotient), so the parity of the final
degree residue is the parity of the internal pair residue.  Pair-only selectors therefore cannot mix
non-triangle pairs with triangle pairs.  Any terminal mixed-class construction must use singleton or
whole-triple words somewhere; those are exactly the words whose sizes are odd and can change the parity
of cross-contributions.

The odd-word subproblem has an exact linear form.  Work in a homogeneous quotient `Q` on a set `U` of
boundary triples and choose only singleton words, except that on a subset `T` of whole-word-eligible
triples one may choose the whole triple instead.  Whole-word-eligible means independent or triangle;
write `tau_i=0` for an independent triple and `tau_i=1` for a triangle, since replacing a singleton by
the whole triple adds internal residue `0` or `2`.  First restrict to a parity class of `Q[U]`, so
`deg_{Q[U]}(i)=p [MOD 2]` is constant on `U`.  Then the selected degrees are congruent modulo `4` iff
there is a bit `c` such that, for every `i in U`,

```text
floor(deg_{Q[U]}(i)/2) + deg_T(i) + tau_i 1_{i in T} = c       [MOD 2].
```

The resulting outside-only set has size `|U|+2|T|`.  Hence terminality says that every solution of this
linear carry equation has `|U|+2|T|<=m`.  Equivalently, once the pair-residue classes are Gallai-tight,
the remaining homogeneous mixed-class obstruction is a low-weight affine solution space for this
carry equation.  This is strictly sharper than the previous odd-word formulation: failure is now a
linear dual-certificate problem over `F_2`, with variables only on the independent/triangle triples.

Write the matrix of the carry equation as

```text
M_U = A(Q[U]) + diag(tau)          over F_2.
```

If one solution `T_0` exists, then every kernel vector `H in ker M_U` produces the second solution
`T_0 triangle H`.  Since terminality bounds both solution weights by `(m-|U|)/2`, it also forces

```text
|H| <= m-|U|             for every H in ker M_U.
```

Thus a large kernel vector immediately closes the odd-word branch.  If no choice of the constant bit
`c` makes the system solvable, the obstruction is dual: by symmetry of `M_U`, there is a kernel vector
whose dot product with the carry right-hand side is incompatible with both constants (equivalently the
ratios against `1_U` and `floor(deg/2)` are inconsistent).  Hence the irreducible homogeneous
mixed-class case is not an arbitrary labelled quotient; it is a quotient in which the twisted Eulerian
kernel of `A+diag(tau)` is small and simultaneously supplies the affine inconsistency certificate.
That is a much narrower algebraic endpoint.

The small-kernel condition has a useful support consequence.  Let
`L=m-|U|` and let

```text
J = union_{H in ker M_U} supp(H).
```

A uniformly random kernel vector has probability `1/2` of being nonzero on each coordinate of `J`, so
the average weight in the kernel is `|J|/2`.  Since every kernel vector has weight at most `L`,

```text
|J| <= 2L = 2(m-|U|).
```

Therefore, in a soluble terminal branch, outside the small core `J` all solutions of the odd-word
affine system have fixed bits.
If a soluble branch has fixed-one set `F_1 subset U\J`, terminality further forces
`|F_1| <= L/2`, because every solution has weight at most `L/2`.  Thus for `|U|>m/2` the mixed-class
odd-word residual compresses to a core of size at most `2(m-|U|)` plus at most `(m-|U|)/2` forced whole
triples outside the core.  This support compression is a property of the soluble branch; the insoluble
branch is instead the even-kernel certificate described next.

The dual obstruction itself is simpler than it first appears.  Put

```text
r_i = floor(deg_{Q[U]}(i)/2)       [MOD 2].
```

The carry equation is `M_U 1_T = r + c 1_U`.  A choice of `c` is soluble iff
`r+c1_U` is orthogonal to `ker M_U`.  Since changing `c` only changes the pairing with odd-weight kernel
vectors, some `c` works unless there is an even-weight kernel vector `H` with

```text
sum_{i in H} r_i = 1       [MOD 2].
```

Conversely, such an even `H` blocks both constants.  Hence the affine-inconsistent branch is exactly an
even twisted-Eulerian kernel set with odd half-degree sum.  This certificate is the remaining
insoluble obstruction; it is not automatically bounded by the solution-weight argument above.

Unpacking `M_U 1_H=0`, an Arf certificate `H` has the concrete parity-closed form

```text
deg_H(i)=0              for i in U\H,                  [MOD 2]
deg_H(i)=tau_i          for i in H,                    [MOD 2]
|H|=0,  sum_{i in H} floor(deg_U(i)/2)=1               [MOD 2].
```

Thus no outside quotient vertex sees `H` oddly, while vertices of `H` have exactly the parity prescribed
by their boundary type.  If `H` is proper, the mixed-class obstruction has localized to the smaller
parity-closed subquotient `H`; if `H=U`, then the whole class is parity-matched and only the single
global Arf bit remains.  This is the odd-word analogue of the retained trace-hole reduction: terminal
failure is forced onto a proper closed support or a one-bit whole-class obstruction.

The whole-class case has a small-kernel normal form.  Choose an affine-inconsistent
class `U` minimal under passing to a bad closed support.  Then every bad even
kernel vector is `1_U` itself.  Indeed, if `K in ker M_U` is even and
`sum_{i in K} r_i=0`, then `U Delta K` is a proper bad even kernel vector unless
`K` is empty; while if `sum_{i in K} r_i=1`, then `K` is already a proper bad
support unless `K=U`.  Hence the even part of the kernel is exactly

```text
ker(M_U) cap {even vectors} = {0,1_U}.
```

Consequently a minimal Arf obstruction has `|U|` even, `1_U in ker M_U`,
`sum_U r_i=1`, and `dim ker M_U<=2`: if two distinct odd kernel vectors exist,
their sum is a nonzero even kernel vector and therefore equals `1_U`.  Unpacking
`1_U in ker M_U`, every vertex of `U` has

```text
deg_U(i)=tau_i        [MOD 2],
```

and the bad Arf bit is equivalently

```text
e(Q[U]) - (1/2)|{i in U: tau_i=1}| = 1        [MOD 2].
```

Thus the insoluble odd-word branch is no longer an arbitrary quotient-matrix
failure: after localization it has rank at most two, whole-class parity matching,
and a single quadratic half-edge bit.  Any terminal quotient with a larger kernel,
or with an even kernel vector different from `0,1_U`, descends to a proper closed
support and is not irreducible.

This also removes twisted twins from the minimal Arf core.  If two columns of
`M_U=A(Q[U])+diag(tau)` were equal, then the two-point vector `e_i+e_j` would lie
in `ker M_U`.  It has even weight, so in a minimal whole-class obstruction it
would have to be either `0` or `1_U`.  Therefore, for `|U|>2`, all columns of
`M_U` are distinct.  Equivalently, any pair of boundary triples with identical
twisted adjacency profile already yields a proper closed even kernel support and
is not part of an irreducible whole-class obstruction.

One important special case is already explicit.  Suppose `tau` is constant on `U` and
`deg_{Q[U]}(i)=tau [MOD 2]` for every `i in U`.  Then `1_U in ker M_U`.  If `|U|>m/2` and the carry
equation is soluble for some `c`, the two complementary solutions `T` and `U\T` have weights summing
to `|U|`, so one has weight greater than `(m-|U|)/2`, giving an outside-only selector of size
greater than `m`.  Hence a terminal parity-matched constant-type class of size greater than `m/2` must
be affine-inconsistent.  The inconsistency is one-dimensional: because `1_U` is the kernel certificate,
solvability requires

```text
sum_{i in U} ( floor(deg_{Q[U]}(i)/2) + c ) = 0       [MOD 2].
```

If `|U|` is odd, one can choose `c` to satisfy this equation, so the odd-word equation itself is soluble.
In the full selector, however, the pair-word shortcut already closes any constant-type quotient set with
constant degree parity and `|U|>m/2`.  Therefore this Arf-type bit is only a residual diagnostic below
the pair-word threshold or after the class has been forced to split; it is not an independent large
boundary obstruction.

The boundary side has one more structural feature: `X` is zero-sum-free in
`C_4^(m-1)` and has length at most the exact Davenport extremal value `3(m-1)`.  Hence the terminal
case splits naturally into two regimes.

1. If `|X|` is substantially below `3(m-1)`, then `B=C\X` is substantially larger than the current
   `m/8` lower bound.  This extra retained mass should be spent on the block-interaction equation above.
2. If `|X|` is near `3(m-1)`, inverse Davenport structure for `C_4^(m-1)` should make `X` close to a
   basis sequence with three copies of each order-`4` generator.  In that basis-like case, balanced
   imports from `X` are extremely constrained but explicit, so the exchange equations become finite
   coordinate moves.

The exact top layer is already rigid.  By the Olson extremal theorem for finite abelian `p`-groups, a
zero-sum-free sequence of length `D(C_4^r)-1=3r` in `C_4^r` is, after a change of basis,

```text
e_1,e_1,e_1, e_2,e_2,e_2, ..., e_r,e_r,e_r.
```

Thus when `|X|=3(m-1)`, every boundary import has a coordinate count vector
`a=(a_1,...,a_r)` with `0<=a_i<=3`, and its old-coordinate sum is exactly
`sum_i a_i e_i`.  Conversely every vector of `C_4^r` has such a boundary representative, with the only
choices being which of the three parallel copies of each `e_i` are used.  Therefore the value-coupled
exchange is not a general Davenport problem at the exact endpoint: exporting a retained set of old-sum
`sum_i a_i e_i` forces precisely `a_i` imports from the `i`-th boundary triple.  All remaining freedom is
inside the three parallel graph traces of each coordinate.

This gives a numerical exchange budget.  For `g=sum_i a_i e_i` with `0<=a_i<=3`, write

```text
h_X(g)=sum_i a_i.
```

In the exact boundary endpoint, any exchange that deletes `Y subset B` and imports from `X` while
preserving the old-coordinate sum must import exactly `h_X(sigma(Y))` boundary vertices.  Thus the
candidate selected set has size

```text
|B|-|Y|+h_X(sigma(Y)).
```

Consequently terminality implies the following weighted surplus obstruction: every graph-label-compatible
export `Y` must satisfy

```text
|Y|-h_X(sigma(Y)) >= |B|-m.
```

Otherwise the forced coordinate import is already large enough to leave more than `m` selected vertices.
The exact-top boundary problem is therefore a finite trace search with a linear weight
`|Y|-h_X(sigma(Y))`; no hidden zero-sum choice remains.
Equivalently, when the retained old-balanced side has deficit `d=m-|B|>=0`, every compatible exchange
must have

```text
h_X(sigma(Y))-|Y| <= d.
```

Thus the exact-top endpoint can only survive if all graph-compatible exports have boundary-height gain at
most the retained deficit.  Large-height coordinate imports are harmless only when their corresponding
retained export is graph-label incompatible.

The height gain has an exact carry formula.  Write the old-coordinate value of a retained vertex `y` as

```text
sigma(y)=sum_i a_i(y)e_i,        0<=a_i(y)<=3,
```

and for `Y subset B` put `n_i(Y)=sum_{y in Y}a_i(y)`.  Then

```text
h_X(sigma(Y))-|Y|
  = sum_{y in Y}(h_X(sigma(y))-1) - 4 sum_i floor(n_i(Y)/4).
```

Thus terminality is equivalent to the finite carry inequality

```text
sum_{y in Y}(h_X(sigma(y))-1) <= d + 4 kappa(Y),
kappa(Y):=sum_i floor(n_i(Y)/4),
```

for every graph-compatible export `Y`.  In particular every carry-free compatible export
(`n_i(Y)<=3` for all `i`) has total singleton height surplus at most `d`.  The residual exact-top
problem has therefore split into two visible mechanisms: either graph labels block all high-surplus
carry-free exports, or every high-surplus export is forced to spend a coordinate carry, losing four units
of boundary height.

The first consequences are small but useful.  A compatible singleton `y` must satisfy

```text
h_X(sigma(y)) <= d+1.
```

A compatible pair `y,z` with `a_i(y)+a_i(z)<=3` for every coordinate must satisfy

```text
(h_X(sigma(y))-1)+(h_X(sigma(z))-1) <= d.
```

Hence at deficit zero, two positive-height-surplus retained vertices cannot form a graph-compatible
carry-free pair.  Positive surplus is forced into either incompatible traces or coordinate-overlap
patterns that create a mod-`4` carry.  This is the exact finite replacement for the previous vague
"value-coupled inverse Davenport" endpoint.

There is also a useful complementary-cut test inside any old-balanced retained block.  If
`S subset B` has `sigma(S)=0` and `Y` is a proper nonempty cut of `S`, put `g=sigma(Y)`.  Then

```text
h_X(g)+h_X(-g)=4 supp(g),
```

where `supp(g)` is the number of nonzero coordinates of `g`.  If both exports `Y` and `S\Y` are
graph-compatible, terminality gives

```text
h_X(g)-|Y| <= d,
h_X(-g)-(|S|-|Y|) <= d.
```

Adding them yields the block-cut bound

```text
4 supp(sigma(Y)) <= |S|+2d.
```

Thus a cut whose old-coordinate value has support larger than `(|S|+2d)/4` cannot be compatible on both
sides in a terminal exact-top endpoint.  At deficit zero, every two-sided-compatible cut in a block of
size less than four is impossible, and a two-sided-compatible cut in a four-block must be supported on a
single boundary coordinate.  This turns the old `3+1`/`2+2` append tables into a support-restricted
coordinate test rather than an unrestricted finite search.

In particular, a deficit-zero minimal four-block whose singleton and pair cuts are all two-sided
compatible is forced into one boundary coordinate with the positive boundary orientation.  The singleton
height inequality gives `h_X(sigma(y))<=1`; since minimality rules out `sigma(y)=0`, every singleton has
value exactly `e_i` for some coordinate.  Pair cuts then forbid two vertices from using different
coordinates, since their pair value would have support two.  Hence the block is the single cyclic atom

```text
e_i,e_i,e_i,e_i.
```

The negative atom `(-e_i)^4` is excluded by the singleton height test, since exporting one vertex would
import three boundary copies and gain two vertices.  Thus the exact-top four-block residual is either
label-incompatible on some cut, or it is the positive one-coordinate cyclic atom with no hidden
multi-coordinate import.  That atom has zero height gain on every cut, so it can obstruct enlargement
only by self-layer residue, not by boundary-coordinate arithmetic.

For such a positive atom the remaining self-layer table is completely local.  Let `X_i` be the three
boundary copies of `e_i`, let `S_i` be the retained atom `e_i^4`, and put

```text
R_i=S_i union X_i,        |R_i|=7.
```

Every size-preserving old-coordinate reroot of `S_i` is exactly a four-set `T subset R_i`; all four-set
sums are `0` in the old coordinate group.  Let `A` be the fixed selected remainder.  The reroot has two
ordinary self-layer lines: the remainder vertices must see the new four-set by one common correction, and
the four chosen coordinate vertices must hit the same residue.  Equivalently, for some residue `R`,

```text
M_A(a)+deg_T(a)=R             for every a in A,
L_A(v)+deg_T(v)=R             for every v in T,             [MOD 4]
```

where `M_A` and `L_A` collect all contributions not coming from `T`.  In omitted-triple form
`O=R_i\T`, this is

```text
M_A(a)+deg_{R_i}(a)-deg_O(a)=R        for every a in A,
L_A(v)+deg_{R_i}(v)-deg_O(v)=R        for every v in R_i\O. [MOD 4]
```

The second line alone is the internal coordinate-atom table:

```text
L_A(v)+deg_{R_i}(v)-deg_O(v) = constant        for every v in R_i\O.        [MOD 4]
```

Thus the last exact-top positive-atom residue is a labelled seven-vertex omission table coupled to one
constant-column condition on the fixed remainder.  One must rule out, or exploit, the possibility that
every omitted triple fails one of these displayed congruences.  This is a rerooting problem rather than a
Davenport problem; the group arithmetic has disappeared.

The column condition has a finite trace quotient.  For `a in A`, record the trace

```text
p(a)=N(a) cap R_i in {0,1}^{R_i},        mu(a)=M_A(a)+|p(a)|       [MOD 4].
```

For an omitted triple `O`, the remainder line becomes

```text
mu(a)-|p(a) cap O| = R        for every a in A.        [MOD 4]
```

Thus only the occupied labelled trace classes `(p,mu)` matter.  The positive-atom endpoint is finite in
the following literal sense: choose one of the `35` omitted triples `O` in a seven-point labelled graph
and test whether the affine functional `mu-|p cap O|` is constant on the occupied trace alphabet and
whether the internal line on `R_i\O` is constant.  If no `O` passes, terminality is witnessed by a finite
set of labelled trace classes in `{0,1}^7 x Z/4Z`.  This is the exact ternary/omission form of the
self-layer residue.

Equivalently, the external column condition is a `35`-template test.  Let `P` be the occupied trace set
and assume first that each trace `p` has a single label `mu(p)`; if the same trace carries two labels,
then no omitted triple can equalize the remainder.  For an omitted triple `O`, define

```text
phi_O(p)=|p cap O|        [MOD 4].
```

Then the external line holds exactly when

```text
mu(p)=R+phi_O(p)          for every occupied p in P        [MOD 4]
```

for some constant `R`.  Thus the external candidates are

```text
C_ext={O in binom(R_i,3):  mu-phi_O is constant on P}.
```

The positive-atom reroot exists precisely when `C_ext` intersects the internal candidate set cut out by
the signed `E_3` equations.  Terminality of this atom is therefore the disjointness of two explicit
subsets of the `35` omitted triples, one trace-template subset and one internal four-set subset.

The template set is usually tiny.  If the empty trace is occupied, then its label fixes the constant
`R=mu(empty)`.  If a singleton trace `{r}` is occupied, every external candidate must satisfy

```text
1_{r in O}=mu({r})-mu(empty)        [MOD 4].
```

Thus a singleton trace whose label difference is not `0` or `1` kills all external candidates, and each
valid singleton trace decides whether its point lies in `O`.  If the empty trace and all seven singleton
traces are occupied, then `C_ext` has at most one element: it exists exactly when the seven differences
are `0/1` with exactly three `1`s and every other occupied trace `p` satisfies

```text
mu(p)-mu(empty)=|p cap O|        [MOD 4].
```

Consequently a trace-rich positive atom is not a large anti-Horn problem: the external side either fails
immediately or decodes a unique omitted triple, leaving only the internal `E_3` checks.  The genuinely
ambiguous external obstruction must have sparse low-trace support.

There is a dual high-trace decoder.  If the full trace `R_i` is occupied, then
`R=mu(R_i)-3`.  If the co-singleton trace `R_i\{r}` is occupied, every external candidate satisfies

```text
1_{r in O}=mu(R_i)-mu(R_i\{r})        [MOD 4].
```

Thus full trace plus all seven co-singletons also leaves at most one omitted triple, with the same
`0/1` and "exactly three ones" tests.  Hence any genuinely ambiguous external positive-atom obstruction
must be sparse at both ends of the trace lattice: it cannot contain a complete singleton layer or a
complete co-singleton layer with the corresponding anchor trace.

More generally, two surviving external templates force a balance law.  If distinct triples `O,O'` both
belong to `C_ext`, then for every occupied trace `p`

```text
|p cap O|-|p cap O'| = c        [MOD 4]
```

for one constant `c`.  Equivalently, with `U=O\O'` and `V=O'\O`,

```text
|p cap U|-|p cap V| = c        [MOD 4].
```

If the empty trace or the full trace is occupied then `c=0`, so every occupied trace must meet the two
opposite sides `U,V` equally modulo `4`.  Since `|U|=|V|<=3`, this is ordinary equality of the two
intersection sizes.  Thus ambiguity of `C_ext` is possible only when all occupied traces are balanced
across every symmetric difference between surviving omitted triples; any trace that separates one side
from the other collapses `C_ext` to a smaller template set.

In anchored form this is exact.  If the empty trace or full trace is occupied, define two omitted triples
`O,O'` to be trace-equivalent when

```text
|p cap O|=|p cap O'|        for every occupied trace p.
```

Then `C_ext` is contained in one trace-equivalence class of triples; if the occupied trace family
separates all distinct triples, `|C_ext|<=1`.  The singleton and co-singleton decoders are just the
strongest separating families.  Therefore a genuinely ambiguous anchored external endpoint must carry a
nontrivial equivalence class of triples under the intersection-count map
`O -> (|p cap O|)_{p in P}`.

The adjacent case is especially restrictive.  If `O=A union {x}` and `O'=A union {y}` share two points,
then anchored ambiguity forces

```text
1_{x in p}=1_{y in p}        for every occupied trace p.
```

Thus `x` and `y` are trace twins relative to the occupied trace family.  Hence any anchored external
candidate set containing adjacent triples produces a twin pair in the seven-point reservoir; conversely,
without trace-twin points, an anchored `C_ext` is an independent set in the Johnson graph `J(7,3)`.

Consequently, after quotienting trace twins, anchored external ambiguity is a packing of triples.  If
there are no trace twins, any two triples in `C_ext` meet in at most one point; hence their three
two-subsets are disjoint.  Therefore

```text
|C_ext| <= binom(7,2)/binom(3,2)=7.
```

Equality forces the seven triples to form the Fano `2-(7,3,1)` system.  Thus a large ambiguous external
candidate set has a rigid Steiner shape; otherwise it has at most six templates before the internal
cover-family intersection is imposed.

For two occupied trace classes `(p,mu)` and `(q,nu)`, the remainder line can equalize them by an omitted
triple only if

```text
|p cap O|-|q cap O| = mu-nu        [MOD 4].
```

Writing `A=p\q`, `B=q\p`, `C=R_i\(A union B)`, this is the existence of integers

```text
0<=x<=|A|, 0<=y<=|B|, 0<=3-x-y<=|C|,
x-y = mu-nu        [MOD 4].
```

Thus each pair of trace classes supplies an explicit signed three-subset constraint.  A positive-atom
terminal obstruction is precisely a finite family of such pair constraints, together with the internal
four-set equation, with no common omitted triple among the `35` possibilities.  This is the anti-Horn
version of the seven-point table.

It is useful to name the two-class residue set

```text
D_3(a,b)={x-y [MOD 4] :
          0<=x<=a, 0<=y<=b, 0<=3-x-y<=7-a-b}.
```

Here `a=|p\q|` and `b=|q\p|`.  The pair `(p,mu),(q,nu)` is a genuine pairwise blocker exactly when
`mu-nu notin D_3(a,b)`.  Thus the pairwise obstruction forgets the actual positions of the seven points
and remembers only the two private trace sizes, until several pair constraints are intersected.
Some boundary entries are immediate:

```text
D_3(0,0)={0};
D_3(a,0)={0,1,...,min(3,a)}        for 0<=a<=4;
D_3(5,0)={1,2,3},  D_3(6,0)={2,3},  D_3(7,0)={3};
D_3(0,b)=-D_3(b,0);
if a+b=7, then D_3(a,b) contains only odd residues.
```

In fact the whole non-full table is tiny.  Up to swapping `a,b` and negating residues, the only proper
subsets of `Z/4Z` are

```text
(0,0): {0}
(0,1): {0,3}        (0,2): {0,2,3}
(0,5): {1,2,3}      (0,6): {1,2}      (0,7): {1}
(1,1): {0,1,3}
(1,6): {1,3}        (2,5): {1,3}      (3,4): {1,3}.
```

Every other admissible pair `a+b<=7` has `D_3(a,b)=Z/4Z`.  Thus most trace pairs are never pairwise
blockers; blocking is concentrated on identical traces, nearly nested traces, and complementary
large-private traces.

Consequently identical traces with different `mu` block immediately, and complementary traces with even
`mu-nu` block immediately.  All other failures are small private-size defects recorded by the same
`D_3` table.  This is the first genuinely finite anti-Horn compression of the positive atom.

The internal four-set line has the same form.  Put

```text
lambda(v)=L_A(v)+deg_{R_i}(v)        [MOD 4].
```

For kept vertices `u,v notin O`, internal equality requires

```text
deg_O(u)-deg_O(v)=lambda(u)-lambda(v)        [MOD 4].
```

Since `O` is disjoint from `{u,v}`, this is the same signed three-subset equation on the remaining five
points, with private sizes

```text
a_{uv}=|N_{R_i}(u)\N_{R_i}(v) \ {u,v}|,
b_{uv}=|N_{R_i}(v)\N_{R_i}(u) \ {u,v}|.
```

Define

```text
E_3(a,b)={x-y [MOD 4] :
          0<=x<=a, 0<=y<=b, 0<=3-x-y<=5-a-b}.
```

Again the non-full table is small.  Up to swapping and negating residues, the only proper entries are

```text
(0,0): {0}
(0,1): {0,3}        (0,2): {0,2,3}
(0,3): {1,2,3}      (0,4): {1,2}      (0,5): {1}
(1,1): {0,1,3}
(1,4): {1,3}        (2,3): {1,3}.
```

All other admissible `a+b<=5` entries are full.

Then a kept pair `u,v` is internally compatible with some omitted triple only if
`lambda(u)-lambda(v) in E_3(a_{uv},b_{uv})`, and a particular omitted triple must satisfy the
corresponding signed equation for every kept pair.  Therefore both parts of the positive-atom rerooting
problem are now anti-Horn constraints on omitted triples: external trace pairs use `D_3`, internal kept
pairs use `E_3`.

The internal constraints also have a graph shadow.  Put an edge `uv` in `J_int` whenever

```text
lambda(u)-lambda(v) notin E_3(a_{uv},b_{uv}).
```

No omitted triple avoiding both endpoints of such an edge can work, so every successful omitted triple
must be a vertex cover of `J_int`.  Hence `tau(J_int)<=3` is necessary for a positive-atom reroot.
Equivalently, if the internal blocker graph on the seven-point reservoir has vertex-cover number at
least four, the positive atom has no self-layer reroot regardless of the external trace classes.  When
`tau(J_int)<=3`, the remaining internal equations are only the signed `E_3` constraints for pairs not
covered by the chosen omitted triple, to be intersected with the external `D_3` constraints.

Since `|R_i|=7`, this is more naturally stated in the complement.  The kept four-set
`T=R_i\O` must be an independent four-set of `J_int`.  Hence the positive-atom search starts with

```text
T independent in J_int,       |T|=4,
```

then imposes the exact signed `E_3` equations on the six pairs of `T` and the external `D_3` equations
on the omitted triple `O=R_i\T`.  A terminal positive atom is therefore certified by one of two finite
failures: either `alpha(J_int)<=3`, or every independent four-set of `J_int` is killed by an internal
signed equation or by an external trace-pair equation.

Equivalently, the internal candidate set is contained in the cover family

```text
K_3(J_int)={O subset R_i: |O|=3 and O is a vertex cover of J_int}.
```

The signed `E_3` equations only shrink this cover family.  Hence if `K_3(J_int)` is empty, the positive
atom is internally dead; if `K_3(J_int)` is a singleton `{O_0}`, then the whole reroot question is the
single external template check `O_0 in C_ext` plus the six internal equalities on `R_i\O_0`.  If every
3-cover contains a common core `K`, then all internal candidates omit that core, and the external trace
template is tested only on triples containing `K`.  This is the internal analogue of the singleton-trace
decoder: large blocker structure decodes the omitted triple from the inside.

Combining the two sides, a terminal positive atom has a reduced certificate of one of the following
types.

```text
External empty:   C_ext=empty
                  (duplicate trace labels, failed singleton/full decoder, or a D_3 pair blocker);
Internal empty:   C_int=empty
                  (alpha(J_int)<=3, empty K_3(J_int), or an E_3 signed blocker);
Decoded mismatch: one side decodes a unique omitted triple O_0 and the other side excludes O_0;
Ambiguous core:   C_ext and C_int both have size at least two.
```

The ambiguous core is now very narrow: externally it requires a nontrivial trace-equivalence class of
triples, hence poor separation or trace twins; internally it requires at least two 3-covers of `J_int`
surviving all signed `E_3` equations.  Thus the exact-top positive atom has no remaining arithmetic
freedom.  Its terminality is witnessed by explicit finite obstruction data on the seven-point reservoir.

After quotienting trace twins and discarding decoded cases, the ambiguous core has the canonical form

```text
C_ext = a triple packing P on R_i,
C_int subset K_3(J_int) with |C_int|>=2,
P cap C_int = empty.
```

Equivalently, every external packing triple fails internally and every internal 3-cover is excluded by
the external trace templates.  In the Fano-extremal case `P=F`, terminality is the statement that no
Fano line is an internally valid 3-cover.  Since every pair of points lies on one Fano line, this forces
the internal blocker graph or the signed `E_3` equations to hit every line of the Fano plane.  Thus the
last ambiguous positive-atom core is a finite line-hitting problem: an internal obstruction transversal
against a packing (or Fano) of externally indistinguishable omitted triples.

There is one more counting squeeze on this transversal.  For a kept pair `e={u,v}`, let

```text
P(e)={O in P:e cap O=empty}.
```

Because `P` is a triple packing, `P(e)` is a triple packing on the five-point set `R_i\e`; hence
`|P(e)|<=2` (three triples on five points would violate inclusion-exclusion while sharing no pair).
Therefore any terminal ambiguous core with external packing `P` needs at least

```text
ceil(|P|/2)
```

distinct internal kept-pair witnesses, where a witness is either a blocker edge of `J_int` or a signed
`E_3` equality failure on that kept pair.  In particular, a Fano external ambiguity requires at least
four distinct internal pair witnesses.  If the internal side has at most three such witnesses, one
externally surviving omitted triple in `P` survives all internal checks, and the positive atom reroots.

The exact incidence object is the intersection graph `Gamma(P)` of the packing: vertices are triples in
`P`, and two vertices are adjacent when the corresponding triples meet in one point.  A kept pair can be
disjoint from two triples of `P` exactly when those two triples are adjacent in `Gamma(P)`; then the pair
is uniquely `R_i\(O union O')`.  Otherwise it kills only one packing triple.  Thus internal terminality
against `P` is an edge-cover problem on `Gamma(P)` with optional singleton covers.  Even if every
possible pair witness were internally available, killing all triples of `P` would require at least

```text
|P|-nu(Gamma(P))
```

witnesses, where `nu` is matching number.  The crude `ceil(|P|/2)` bound is the special case
`nu<=floor(|P|/2)`.

Minimum witness covers have no further mystery.  Choose a maximum matching `M` of `Gamma(P)`.  For each
matched pair of triples `O,O'`, the two-at-once witness is forced to be the unique kept pair
`R_i\(O union O')`.  Each unmatched triple `O` then needs a one-at-a-time witness, namely some internally
bad kept pair inside the four-point complement `R_i\O`.  Hence a minimum terminal core is exactly a
maximum matching in `Gamma(P)`, together with one bad complement-four pair for every unmatched external
triple.

The size-six packing case is already near-Fano.  If `|P|=6`, the three uncovered pairs of `R_i` have even
degree at every point because each point is incident with `6-2d_P(x)` uncovered pairs.  Hence the leave
is a triangle `L`, and `P union {L}` is the Fano plane.  Thus `Gamma(P)=K_6`, the lower bound is `3`, and
a minimum terminal core is a perfect matching on the six present Fano lines, i.e. three forced
complement-pair witnesses.  The full Fano case is the unique size-seven extension and needs one more
witness because `K_7` has one unmatched line.

This leave calculus also controls the next non-Fano case.  For any packing `P`, the leave graph
`Lambda(P)` on `R_i` has

```text
|E Lambda(P)| = 21-3|P|,        deg_Lambda(x)=6-2d_P(x),
```

so every leave degree is even.  Thus if `|P|=5`, the leave is a six-edge Eulerian graph: it is a
six-cycle, or the union of two edge-disjoint triangles (possibly sharing one vertex).  Hence all
five-template ambiguous cores sit inside one of these two leave types before the internal witness
matching is imposed.

Large packings also rigidify the occupied trace alphabet.  Assume the external ambiguity is anchored by
the empty or full trace, so every occupied trace `p` has `|p cap O|` independent of `O in P`.
If `P=F` is the full Fano plane, double-counting incidences gives

```text
3|p| = 7t,
```

where `t=|p cap O|` is the common line intersection.  Hence `|p|` is `0` or `7`, and the only occupied
traces compatible with full Fano ambiguity are `empty` and `R_i`.

If `P=F\{L_0}` is a six-packing, the same rigidity leaves exactly four trace types.  Write
`A=L_0` and `B=R_i\L_0`.  The six present Fano lines are, for each `a in A`, the two lines
`a` plus a complementary pair of `B`.  Equal intersections on the two lines through the same `a` force
the three pair-sum equalities on `B`, hence the trace is constant on `B`.  Equal intersections across
different `a` then force the trace to be constant on `A`.  Thus

```text
p in {empty, L_0, R_i\L_0, R_i}.
```

So anchored Fano and near-Fano ambiguity can survive only with a two-level trace alphabet.
Consequently they cannot survive in a trace-twin-free anchored quotient.  In the full Fano case all
points have the same occupied-trace profile; in the near-Fano case all points of `L_0` are twins and all
points of `R_i\L_0` are twins.  Thus, after quotienting trace twins, every irreducible anchored external
packing has size at most five.  The Fano and near-Fano witness-cover catalogues are therefore pre-quotient
diagnostics: their occurrence forces a twin split/merge rather than a genuinely seven-point anchored
core.

The remaining trace-twin-free anchored packing core is therefore bounded by the following witness-count
table:

```text
|P|=5: at least 5-nu(Gamma(P)) >= 3 witnesses;
|P|=4: at least 4-nu(Gamma(P)) >= 2 witnesses;
|P|=3: at least 3-nu(Gamma(P)) >= 2 witnesses;
|P|=2: one witness iff the two triples meet, otherwise two.
```

Equality means exactly the maximum-matching normal form above.  Thus the only post-quotient anchored
terminal core with three external templates or more has at least two internally bad kept pairs, and the
five-template endpoint has at least three.

The six-cycle leave subcase of `|P|=5` also forces trace twins.  If the leave is
`C_6` on `0,1,2,3,4,5` with isolated point `infty`, the five triples are forced to be

```text
{0,2,4}, {1,3,5},
{infty,0,3}, {infty,1,4}, {infty,2,5}.
```

For an anchored occupied trace with common intersection `t`, the three `infty`-lines give
`x_0+x_3=x_1+x_4=x_2+x_5=t-x_infty`, while the two alternating lines give
`x_0+x_2+x_4=x_1+x_3+x_5=t`.  Summing the three pair equations and the two alternating equations forces
`3(t-x_infty)=2t`.  If `x_infty=0`, then `t=0`; if `x_infty=1`, then `t=3`.  Thus the trace is empty or
full.  Hence a trace-twin-free anchored five-packing cannot have six-cycle leave; its leave must be the
two-triangle Eulerian type.

The two-triangle type also forces twins.  Disjoint leave triangles are impossible: every block would need
the isolated seventh point, but that point has packing degree three, not five.  Hence the two leave
triangles share one point.  Label the leave triangles `012` and `034`, with isolated points `5,6`.
The block through `0` is forced to be `056`; the other four blocks are obtained by assigning the four
edges of the cycle `13,14,24,23` to `5` and `6`, two edges each.  Up to symmetry the assignment is either
adjacent or opposite.  In the adjacent case, say

```text
513, 514, 623, 624,
```

the equal-intersection equations force `x_3=x_4`.  In the opposite case, say

```text
513, 524, 614, 623,
```

they force `x_1=x_2`, `x_3=x_4`, and `x_5=x_6`.  Thus every anchored five-packing has trace twins.
Consequently, after trace-twin quotienting, an irreducible anchored positive-atom external packing has
size at most four.

The size-four case has only one trace-twin-free shape.  If the point degrees in the four triples are
`n_j=#{x:d_P(x)=j}`, then pair-packing gives

```text
n_0+n_1+n_2+n_3=7,        n_1+2n_2+3n_3=12,
sum_x binom(d_P(x),2)<=binom(4,2).
```

The only possible degree patterns are

```text
(n_3,n_2,n_1,n_0)=(1,3,3,0), (0,6,0,1), (0,5,2,0).
```

The middle pattern is the tetrahedral `2`-regular packing on six points plus one unused point; its
balanced traces identify the three opposite point-pairs of the tetrahedron, so it has trace twins.  The
last pattern has one disjoint pair of triples.  In normal form

```text
A={a_1,a_2,a_3},  B={b_1,b_2,b_3},
C={a_1,b_1,z},    D={a_2,b_2,z},
```

the equal-intersection equations force `a_2=b_1`, `a_1=b_2`, and `a_3=b_3=z` at the level of every
anchored balanced trace, so it also has twins.  Therefore the only trace-twin-free size-four packing is
the first pattern, with one point in three triples.  It has normal form

```text
U={u_1,u_2,u_3},
L_i={a,u_i,v_i}  for i=1,2,3.
```

This is the unique anchored size-four positive-atom quotient left after all twin reductions.
Its anchored balanced traces are also explicit:

```text
empty, R_i,
{u_i,v_j,v_k},                 {a,u_j,u_k,v_i}        for {i,j,k}={1,2,3}.
```

Here the intersection graph `Gamma(P)` is `K_4`.  Hence the witness lower bound is exactly two.  A
minimum terminal internal core is one of the three perfect matchings of `K_4`; in primal kept-pair form
these are

```text
{u_i v_i, v_j v_k}        for {i,j,k}={1,2,3}.
```

Therefore the trace-twin-free anchored size-four positive atom is reduced to three explicit two-witness
patterns, plus non-minimal cores with at least three bad kept pairs.

The smaller anchored packing cases are completely described by the same matching rule.  For `|P|=3`,
the union bound forces `Gamma(P)` to have two or three edges, so it is either a path `P_3` or a triangle
`K_3`.  A minimum terminal core has two witnesses: choose one edge `OO'` of `Gamma(P)`, take the forced
pair `R_i\(O union O')`, and add one internally bad pair in the four-point complement of the unmatched
triple.  For `|P|=2`, adjacent triples have a single forced witness `R_i\(O union O')`; disjoint triples
need one bad pair in each four-point complement.  Thus, after anchored trace-twin quotienting, the
positive-atom ambiguous core is a finite list of two-template, three-template, and the single size-four
base-triple/star pattern above.

Explicitly, the three-template shapes are only

```text
Path:          {a,x_1,x_2}, {a,b,c}, {b,y_1,y_2};
centered K_3:  {a,x_1,x_2}, {a,y_1,y_2}, {a,z_1,z_2};
triangular K_3:{a,b,x}, {a,c,y}, {b,c,z}.
```

The first has two possible matched edges in `Gamma(P)`, while each `K_3` shape has three.  These are the
only remaining anchored external template geometries before internal `E_3` signs are applied.

The unanchored case has the same packing spine after a relative normalization.  Fix an occupied trace
`p_0`.  If `O,O'` are both external candidates, then every occupied trace `p` satisfies

```text
(1_p-1_{p_0}) dot (1_O-1_{O'}) = 0        [MOD 4].
```

For adjacent templates this says the two swapped points have the same **relative trace column**
`(1_p(x)-1_{p_0}(x))_p`.  Thus, after quotienting relative trace twins, the unanchored candidate set is
again a triple packing.  The large-packing collapse is even stronger: if this relative equation holds for
all seven Fano lines, the Fano incidence matrix is nonsingular over the rationals, so
`1_p=1_{p_0}` for every occupied `p`.  If it holds for the six lines of `F\{L_0}`, the nullspace is
spanned by the vector `-2 1_{L_0}+1_{R_i\L_0}`, which has no nonzero `{ -1,0,1 }` multiple; again
`1_p=1_{p_0}`.  Hence full and near-Fano unanchored ambiguity either makes all occupied traces identical
(so the external side is all triples unless labels conflict) or collapses by relative twins.  No genuine
large unanchored external packing survives the relative quotient.

For `P=F` this lower bound has an exact Fano-plane form.  A kept-pair witness `e` kills precisely the
Fano lines disjoint from `e`; therefore a witness graph `H` kills all Fano omitted triples iff no Fano
line meets every edge of `H`.  Equivalently, `H` is not vertex-covered by any Fano line.  Every graph
with at most three witness edges is Fano-line-covered, so the first possible terminal Fano witness graph
has four edges and must be a genuine Fano-line-uncoverable configuration, not a star, triangle, or any
three-edge local defect.

Dualizing the Fano lines makes the condition exact.  Let `D(H)` be the graph whose vertices are the
seven Fano lines and where a kept-pair witness `e` contributes the edge joining the two Fano lines
disjoint from `e`.  Then

```text
H kills every Fano omitted triple  <=>  D(H) has no isolated vertex.
```

Thus the Fano ambiguous core is an edge-cover problem on the dual line set.  A four-witness terminal
core is necessarily a minimum edge cover of seven dual vertices, hence its dual cover has degree pattern
`2,1,1,1,1,1,1`, i.e. `P_3 disjoint union 2K_2`.  Larger witness cores are terminal only through the
same dual no-isolated-line condition.

If the Fano core is inclusion-minimal, this dual graph is even more rigid: every dual edge must touch a
degree-one dual vertex, otherwise that edge could be deleted without creating an isolated vertex.  Hence
every inclusion-minimal dual cover is a star forest.  On seven dual vertices the only possibilities are

```text
4 witnesses: K_{1,2} disjoint union K_2 disjoint union K_2;
5 witnesses: K_{1,4} disjoint union K_2, or K_{1,3} disjoint union K_{1,2};
6 witnesses: K_{1,6}.
```

The extreme `K_{1,6}` case has a concrete primal meaning: all witness pairs lie in the four-point
complement of one Fano line, and in fact form the whole `K_4` on that complement.  Thus even the
maximally degenerate Fano ambiguity has a fixed four-point support.

More generally, a dual star centered at a Fano line `L` is exactly a set of primal witness pairs contained
in the four-point complement `R_i\L`: the leaf line `M` selects the unique pair
`R_i\(L union M)`.  Hence a minimal Fano terminal core is a union of such complement-four clusters.  This
is the bridge back to the internal table: the Fano branch can only survive if the internally bad kept
pairs supplied by `J_int` or by signed `E_3` failures contain one of the listed complement-four
star-forest patterns.

The same height language also covers the non-exact boundary.  For an arbitrary zero-sum-free boundary
`X`, define the available import height

```text
H_X(g)=max{|Z|: Z subset X, sigma(Z)=g},
```

with `H_X(g)=-infty` if no representative exists.  Any compatible export `Y` closes whenever

```text
|B|-|Y|+H_X(sigma(Y))>m.
```

Therefore terminality forces

```text
H_X(sigma(Y))-|Y| <= d=m-|B|
```

for every graph-compatible export.  The exact Davenport-top case is the special case where
`H_X=h_X` is the coordinate sum on the basis box `0<=a_i<=3`.  Near-top boundary stability is thus needed
only to lower-bound `H_X` on many export values; the exchange inequality itself is already exact.

In the basis-with-holes regime the correct statement is capacity-restricted, not an effective-deficit
loss.  Suppose `X` contains `c_i<=3` copies of `e_i`, and write the exact-box representative of
`g` as `g=sum_i a_i e_i` with `0<=a_i<=3`.  Then

```text
H_X(g)=sum_i a_i        if a_i<=c_i for every i,
H_X(g)=-infty           otherwise.
```

A missing copy can make a residue unavailable; it does not merely lower the height of the same residue.
Thus holes are compatibility restrictions.  For every available export value, terminality gives the
same exact-top inequality

```text
h_box(sigma(Y))-|Y| <= d,
```

while an unavailable value is already boundary-incompatible.  Consequently the carry inequality and the
complementary-cut bound survive verbatim on two-sided available cuts, with no `rho` error term.
Coordinatewise, a nonzero coefficient `a` is two-sided available with its complement `-a` only as follows:

```text
c_i=3:  a in {1,2,3};
c_i=2:  a=2 only;
c_i<=1: no nonzero two-sided coefficient.
```

So a one-hole coordinate can support only the self-opposite coefficient `2` in a two-sided cut, and a
two-hole coordinate cannot support any nonzero two-sided cut.

In particular the four-block collapse survives on the available part.  If `d<=1` and a minimal
old-balanced four-block has all singleton and pair cuts two-sided-compatible and available in the
capacity box, the complementary-cut bound gives support at most one for every singleton and pair cut.
Hence all four old-coordinate values lie on one coordinate.  The singleton height inequality gives
coefficients only in `{1,2}`; since four coefficients in `{1,2}` sum to `0 mod 4` without a proper
zero-sum subblock only when all four are `1`, the block is again the positive atom `e_i^4`.  Since
coefficient `1` is two-sided available only when `c_i=3`, any surviving positive atom sits on a full
coordinate.  Holed coordinates therefore create immediate label incompatibilities rather than new
four-block atoms.

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

In the unconstrained one-large-class selector, the co-cut inequalities are stronger than in the
old-vector exchange problem because every equal-size exchange is allowed.  Let `B` be a cardinal-maximal
label-correct selected set, `X=V(H)\B`, and let `T` be the current target layer inside `B`.  In a pure
`T_2` terminal branch, summing the pair-exchange inequality over all export pairs
`Y in binom(B,2)` and all import pairs `Z in binom(X,2)` gives

```text
sum_{u in T_2} [
  binom(deg_B(u),2) binom(|X|-deg_X(u),2)
  + binom(|B|-deg_B(u),2) binom(deg_X(u),2)
]
<= total pair-damage on T plus exported/imported target terms.
```

Thus an unpaid `2`-error vertex is forced to be globally almost constant across the cut: it cannot see
many vertices of `B` while missing many of `X`, and it cannot miss many vertices of `B` while seeing many
of `X`.  Equivalently, outside the target-damage budget, every pure `T_2` vertex is either sparse on both
sides or dense on both sides, up to one-corner exceptions.  This biquadratic domination is the
unrestricted analogue of the exact-basis majority rule, and it is the current sharp local form of the
terminal co-cut/self-layer selector.

The target-damage side is also explicit.  For any vertex `v`, put `b=|B|`, `x=|X|`,
`beta=deg_B(v)`, and `xi=deg_X(v)`, and define

```text
N_B^0(v)=binom(b-beta,2),      N_B^1(v)=beta(b-beta),      N_B^2(v)=binom(beta,2),
N_X^0(v)=binom(x-xi,2),        N_X^1(v)=xi(x-xi),          N_X^2(v)=binom(xi,2).
```

Then the number of export/import pair exchanges that damage a target vertex `t` is

```text
Damage_{B,X}(t)=sum_{i != j} N_B^i(t) N_X^j(t).
```

Consequently the all-pairs terminal inequality can be written without hidden language as

```text
sum_{u in T_2} Polar_{B,X}(u) + ImportedTargetPairs
 <= sum_{t in T} Damage_{B,X}(t) + binom(x,2)(b-1)|T|,
```

where

```text
Polar_{B,X}(u)
 = binom(deg_B(u),2) binom(x-deg_X(u),2)
   + binom(b-deg_B(u),2) binom(deg_X(u),2).
```

The exact zero cases are important.  If `b,x>=3`, then `Polar_{B,X}(u)=0` iff either

```text
deg_B(u)<=1 and deg_X(u)<=1,
```

or

```text
b-deg_B(u)<=1 and x-deg_X(u)<=1.
```

Thus an unpaid zero-polarity `T_2` vertex is genuinely one-corner sparse or one-corner dense across the
whole cut.  Similarly, `Damage_{B,X}(t)=0` for a target vertex with `b,x>=3` iff `t` is constant on both
sides of the cut with the same value: it misses `B union X`, or it sees `B union X`.  Hence terminality
has a clean accounting form: mixed `T_2` polarity must be paid by mixed target cut profiles; cut-constant
target vertices cannot pay for it.

This gives a useful charging corollary.  For `U subset T_2`, let

```text
P_U=min_{u in U} Polar_{B,X}(u),        D_T=max_{t in T} Damage_{B,X}(t).
```

Dropping the nonnegative imported-target term from the exact inequality gives

```text
|U| P_U <= |T| D_T + binom(x,2)(b-1)|T|.
```

Thus every family of `T_2` vertices with uniformly large cut-polarity has size controlled by the target
layer.  In particular, if `U` is linearly mixed on both sides of the cut, in the sense that

```text
epsilon b <= deg_B(u) <= (1-epsilon)b,
epsilon x <= deg_X(u) <= (1-epsilon)x        for every u in U,
```

then `P_U` is a positive `epsilon`-multiple of `b^2 x^2`, while `D_T<=binom(b,2)binom(x,2)`.  Hence
`|U|=O_epsilon(|T|)` (with only the displayed lower-order exported-target term).  After charging this
mixed part to the target layer, the residual pure `T_2` branch is one-corner polarized: every unpaid
vertex is close to sparse on both sides or close to dense on both sides of the cut.

The exact zero-polarized endpoint closes.  Let

```text
U^-={u in T_2:deg_B(u)<=1 and deg_X(u)<=1},
U^+={u in T_2:b-deg_B(u)<=1 and x-deg_X(u)<=1}.
```

Since `U^- subset B`, the induced graph on `U^-` has maximum degree at most one.  It is a disjoint union
of isolated vertices and matching edges.  If more than `m` vertices lie in isolated components, they form
an outside-only congruent set of degree `0`; if more than `m` vertices lie in matching components, the
union of those edges is an outside-only congruent set of degree `1`.  Therefore terminality forces

```text
|U^-|<=2m.
```

The dense part is the complement of the same argument.  In the complement graph on `U^+`, maximum degree
is at most one.  Complement-isolated vertices form a clique in the original graph, and complement-matching
edges form a clique with one missing mate at each vertex; in either case the original induced degrees are
constant.  Hence

```text
|U^+|<=2m.
```

Thus zero-polarity pure `T_2` vertices contribute at most `4m` in a terminal one-large-class
counterexample.  After the mixed-polarity charging above, the only remaining self-layer mass is the
intermediate low-polarity band where at least one of the four factors
`deg_B`, `b-deg_B`, `deg_X`, `x-deg_X` is small but not one-corner exact.  This isolates the final
multi-scale accounting problem.

The intermediate band has an exact scale form.  Fix an integer `L>=2` with `b,x>=2L`.  If

```text
Polar_{B,X}(u) < binom(L,2)^2,
```

then the two products in `Polar` cannot both contain factors at least `L`; hence either

```text
deg_B(u)<L and deg_X(u)<L,
```

or

```text
b-deg_B(u)<L and x-deg_X(u)<L.
```

The other two logical combinations would force `b<2L` or `x<2L`.  Thus low-polarity vertices are
`L`-sparse or `L`-dense.  The `L`-sparse vertices induce maximum degree less than `L`, and therefore
contain an independent set of size at least their cardinality divided by `L`; terminality gives at most
`Lm` such vertices.  Dually, the `L`-dense vertices have complement maximum degree less than `L`, so they
also have size at most `Lm`.  Combining this with the charging inequality gives the scale bound

```text
|T_2|
 <= 2Lm
    + ( |T| D_T + binom(x,2)(b-1)|T| ) / binom(L,2)^2.
```

This is the first quantitative form of the final selector.  The residual is no longer structural but
optimization/accounting: choose a scale `L` and use target-layer information to make the second term
linear in `m`.

The same sparse/dense bound applies to every retained layer, including the target layer.  For any
`U subset B`, if every vertex of `U` is `L`-sparse across the cut, then `G[U]` has maximum degree less than
`L`, so `|U|<=Lm` in a terminal graph.  If every vertex of `U` is `L`-dense across the cut, then the
complement graph on `U` has maximum degree less than `L`, and again `|U|<=Lm`.  Therefore, after deleting
`O(Lm)` target vertices, every remaining target vertex has a genuinely mixed cut profile at scale `L`.

Thus the final accounting core has a symmetric description: the linearly or scale-mixed part of `T_2` is
charged to the scale-mixed part of `T`, while all sparse/dense pieces on either side are already linearly
bounded by degeneracy or complement degeneracy.  In this form, a terminal counterexample must contain a
large target layer whose vertices are themselves mixed across the selected/discarded cut and whose
`Damage_{B,X}` budget pays for the mixed `T_2` polarity.  No cut-constant or one-corner target mass can
participate in the payment.

One can make this last sentence quantitative without using a maximum-damage vertex.  Let `T_mix(L)` be
the target vertices for which neither the sparse nor dense alternative at scale `L` holds.  For a
target vertex that is `L`-sparse, the profile formula gives

```text
Damage_{B,X}(t) <= C L b x(b+x)
```

for an absolute constant `C`; the same estimate holds for `L`-dense vertices by complementing.  Since the
sparse and dense target parts have size at most `Lm` each,

```text
sum_{t in T} Damage_{B,X}(t)
 <= |T_mix(L)| binom(b,2)binom(x,2) + C L^2 m b x(b+x).
```

Substituting this in the exact all-pairs inequality yields the scale-decomposed form

```text
|T_2|
 <= 2Lm
    + |T_mix(L)| binom(b,2)binom(x,2) / binom(L,2)^2
    + C L^2 m b x(b+x) / binom(L,2)^2
    + binom(x,2)(b-1)|T| / binom(L,2)^2.
```

Thus a terminal obstruction at scale `L` has to put a large amount of mass into `T_mix(L)`, the target
vertices which are themselves mixed across the selected/discarded cut.  Sparse/dense target vertices and
zero-polarized `T_2` vertices are already linear; the only remaining nonlinear term is the mixed-target
core.

The mixed-target core can be dyadically localized.  For a mixed vertex `v`, record the four cut factors

```text
deg_B(v),        b-deg_B(v),        deg_X(v),        x-deg_X(v).
```

Bucket each factor by powers of two between `L` and the corresponding side size.  On a fixed bucket
`(A,A',C,C')`, every target vertex has

```text
Damage_{B,X}(t) = Theta(AA'CC')
```

up to an absolute constant, and every `T_2` vertex in the matching polarity bucket has

```text
Polar_{B,X}(u) = Theta(AA'CC').
```

Therefore, after losing only an absolute logarithmic factor in the four cut parameters, terminality gives
a single bucket in which the number of mixed `T_2` vertices is controlled by the number of mixed target
vertices in the corresponding bucket, plus the already linear sparse/dense error.  Equivalently, the
final obstruction can be assumed cut-profile homogeneous: all live vertices have the same four dyadic cut
scales, and the pair-exchange inequality compares their cardinalities rather than heterogeneous weights.

This homogeneous mixed-core form is equivalent to a finite weighted principal-submatrix selector: after
normalizing by the common weight `AA'CC'`, either the bucket has more mixed `T_2` vertices than target
vertices and a pair exchange improves the target layer, or the target bucket itself carries the remaining
self-layer obstruction.  Thus no diffuse cut-profile phenomenon remains; the final gap is concentrated in
one dyadic mixed target bucket.

Refine that bucket once more by the two residues

```text
deg_B(v) [MOD 4],        deg_X(v) [MOD 4].
```

One residue subbucket loses only a factor `16`.  On it, all external cut contributions are fixed modulo
`4`.  Therefore a pure-discard exit from the target bucket is exactly the following internal selector:
find `S` in the subbucket with

```text
deg_{G[S]}(s)=constant        [MOD 4]        for every s in S,
```

and `|S|>m` after adding the already selected compatible part.  Equivalently, the final homogeneous
mixed-bucket obstruction is a principal-submatrix mod-`4` row-sum selector in a graph whose vertices have
comparable degrees and codegrees to both sides of the ambient cut.  All boundary arithmetic, old-vector
data, positive atoms, and one-corner polarized pieces have been removed from this last statement.

There is an exact co-cut form of the same problem.  Put `H` for the principal bucket and write
`D=V(H)\S`.  For `v in S`,

```text
deg_{H[S]}(v)=deg_H(v)-deg_D(v).
```

Therefore `S` is a selector with common residue `c` if and only if

```text
deg_D(v) == deg_H(v)-c        [MOD 4]        for every v in V(H)\D.
```

Thus a terminal bucket is deletion-rigid: for every `c in Z/4Z` and every deletion set `D` whose
complement has size greater than `m`, at least one retained vertex violates this affine co-cut equation.
This is the internal version of the previous chamber/co-cut obstruction; the old boundary has simply
become the deletion layer `D`.

Splitting the same equation into bits gives the exact first-bit/carry obstruction.  For
`r_c(v)=deg_H(v)-c [MOD 4]`, the deletion layer must satisfy, on every retained vertex,

```text
deg_D(v) == r_c(v)                                      [MOD 2],
#{ {x,y} subset D : vx and vy are edges of H } == floor(r_c(v)/2)   [MOD 2].
```

The first line is the ordinary Gallai/F2 cut equation.  The second line is the centered pair-neighbour
equation for the same deletion layer.  Thus the terminal principal bucket is exactly a simultaneous
co-cut selector for the graph-neighbour parity and the cut-pair parity.  Any proof that selects `D` by
only the first line merely produces a parity-regular retained set; it has not synchronized the carry bit.

The deletion equation also has a canonical pruning dynamics.  Fix `c in Z/4Z` and an initial deletion set
`D_0`.  Define

```text
D_{t+1}=D_t union {v notin D_t : deg_{D_t}(v) != deg_H(v)-c [MOD 4]}.
```

The retained sets `S_t=V(H)\D_t` are nested.  If the process stabilizes at `D_infty` with
`|S_infty|>m`, then `S_infty` is a principal selector of residue `c`.  Hence a terminal bucket has the
following avalanche property:

```text
for every c and every D_0, the pruning closure leaves |V(H)\D_infty| <= m.
```

This is stronger than the finite layer-refinement obstruction.  The usual Gallai start is the first
parity line of this pruning process; terminality says that every attempt to repair the carry by deleting
violators must avalanche through all but `m` vertices.

In complement form the same dynamics is the residue-core peeling

```text
S_{t+1}={v in S_t : deg_{H[S_t]}(v)==c [MOD 4]}.
```

Indeed `deg_{D_t}(v)=deg_H(v)-deg_{H[S_t]}(v)`.  Thus the final principal selector is equivalent to the
existence, for some induced starting chamber `S_0` and residue `c`, of a mod-`4` degree-`c` core larger
than `m`.  A terminal bucket is therefore mod-`4` core-degenerate in every residue: every induced chamber
has all four residue-cores of size at most `m`.

Equivalently, for every induced chamber `U` and residue `c`, there is an ordering of all but at most `m`
vertices of `U`,

```text
u_1,u_2,...,u_{|U|-m'},
```

where `m'<=m`, such that `u_i` has degree not congruent to `c` in the current induced graph on
`U\{u_1,...,u_{i-1}\}`.  This is the mod-`4` analogue of a degeneracy ordering, but with the forbidden
degree class depending on `c`.  Therefore any minimal terminal bucket carries four hereditary elimination
orders, one avoiding each residue class.

The residue-core formulation is self-dual.  For any retained set `S`,

```text
deg_{\overline H[S]}(v)=|S|-1-deg_{H[S]}(v).
```

Thus `H[S]` has constant residue `c` modulo `4` if and only if the complement bucket has constant residue
`|S|-1-c` modulo `4` on the same set.  All terminal assertions above are therefore complement-invariant:
row-twin and co-twin exits, dense and codense exits, and residue-core degeneracy must hold on both sides
with the same threshold `m`.

For the loss-`32` theorem one may also pass to the critical minimal counterexample.  Suppose the theorem
fails, and choose a counterexample `H` with minimum order.  Let `m` be the largest selector size in `H`.
Then `|H|>32m`; if `|H|-1>32m`, every vertex deletion would contain, by minimality, a selector of size
greater than `m`, still present in `H`, a contradiction.  Hence

```text
|H|=32m+1.
```

Moreover, for every vertex `z`, the graph `H-z` has order `32m` and therefore contains a selector of
size at least `m`.  Since `H` has no selector of size `m+1`, each vertex is omitted by some maximum
selector of size exactly `m`.  In residue-core language: for every `z` there is a residue `c(z)` and an
induced starting chamber inside `H-z` whose stable residue-`c(z)` core has size exactly `m`.

Thus the terminal residue-core obstruction is not diffuse in size.  It is a critical object of order
`32m+1`, every one-vertex deletion has a maximum residue-core, but adding the deleted vertex to any such
core is blocked by the one- and two-point anti-merge conditions below.

Pairs of maximum cores have an exact exchange normal form.  Let `S` and `T` be maximum selectors of size
`m`, with residues `a` and `b`, and write

```text
P=S cap T,        A=S\T,        B=T\S.
```

Then for every `v in P`,

```text
deg_A(v)-deg_B(v) == a-b        [MOD 4].
```

For every `x in A`,

```text
deg_P(x)+deg_A(x) == a        [MOD 4],
```

and for every `y in B`,

```text
deg_P(y)+deg_B(y) == b        [MOD 4].
```

Thus changing one maximum core into another is a balanced exchange between two equal-size petals `A` and
`B`; the common intersection sees the two petals with a fixed residue difference, while each petal is
internally synchronized after adding its degree to the overlap.  In the critical counterexample the
family `{S_z}` supplied by vertex deletions must satisfy this exchange system for every pair of omitted
vertices.

In the one-exchange case `S=P union {x}` and `T=P union {y}` the exchange system is completely rigid.
Since each vertex of `P` sees the difference of the two new traces in `{-1,0,1}`, the residue difference
`a-b` cannot be `2`.  If `a=b`, then `x` and `y` have identical trace on `P` and
`deg_P(x)==deg_P(y)==a`.  If `a-b==1`, then `x` is complete to `P`, `y` is anticomplete to `P`,
`a==|P|`, and `b==0`.  The case `a-b==-1` is the reverse.

Consequently terminality forbids the immediate one-exchange extensions: in the identical-trace case, if
the common trace is constant `tau` on `P` and `xy` has edge bit `tau`, then `P union {x,y}` is an
`m+1` selector; in the extreme complete/anticomplete cases, if `|P|==0 [MOD 4]` and `xy` is absent, then
`P union {x,y}` is a residue-`0` selector.  These exclusions are the smallest concrete constraints on
the critical family of maximum cores.

A second exact reformulation is by merging smaller selectors.  Let `A` and `B` be disjoint induced
selectors with internal residues `a` and `b`.  Suppose the cross-degrees are constant modulo `4` on both
sides:

```text
deg_B(x)==p [MOD 4] for x in A,
deg_A(y)==q [MOD 4] for y in B.
```

Then `A union B` is a selector exactly when

```text
a+p == b+q        [MOD 4].
```

More generally, a family of pairwise cross-regular selector blocks is governed by the quotient equations

```text
r_i + sum_j p_{ij} x_j == constant        [MOD 4]
```

for the chosen block indicators `x_j`.  Thus a terminal bucket is anti-merge: every cross-regular
quotient solution has total lifted size at most `m`.  This is the finite quotient shadow of the same
principal-submatrix problem, but now the vertices are selector blocks rather than original vertices.

The one-vertex shadow is especially useful.  If `S` is a residue-`a` selector and `x` is outside `S`,
then `S union {x}` is a selector only in the following two uniform cases:

```text
x anticomplete to S and a==0,
```

or

```text
x complete to S and |S|==a+1        [MOD 4].
```

Therefore a maximum selector `S` of residue `0` is dominating, and whenever `|S|==a+1 [MOD 4]`, every
outside vertex fails to be complete to `S`.  Applying the same statement in the complement gives the dual
domination restrictions.  These are weak by themselves, but they are mandatory boundary conditions for
any terminal bucket with a largest selector near the threshold.

The two-vertex shadow is the first genuinely cut-shaped one.  Let `S` have residue `a`, let
`X={x,y}` be outside, and put `delta=1` if `xy` is an edge and `0` otherwise.  Then `S union X` is a
selector only if every vertex of `S` sees the same number `p in {0,1,2}` of vertices of `X`; the residue
condition is

```text
a+p == delta+deg_S(x) == delta+deg_S(y)        [MOD 4].
```

Thus terminality forbids three explicit pair-extension patterns above the threshold: both outside
vertices missed by `S` with `delta==a`, both complete to `S` with `|S|+delta==a+2`, or complementary
traces on `S` with equal corrected degrees `delta+deg_S(x)==delta+deg_S(y)==a+1`.  These are exactly the
size-two instances of the quotient anti-merge equation.

There is also a large-packet version forced by Davenport.  Fix a maximum selector `S` of size `m` and
residue `a`, and partition the outside vertices by

```text
U_t={x notin S : deg_S(x)==t [MOD 4]}.
```

For `x in U_t`, let `phi(x) in (Z/4Z)^S` be its trace vector to `S`.  Since
`D((Z/4Z)^m)=3m+1`, every chamber `U_t` of size at least `3m+1` contains a nonempty packet `X` with

```text
sum_{x in X} phi(x)=0 in (Z/4Z)^S.
```

Equivalently, every vertex of `S` has `0 mod 4` neighbours in `X`.  If in addition `H[X]` has all
degrees congruent to `a-t mod 4`, then `S union X` is an `(m+|X|)`-vertex selector, impossible in a
terminal bucket.  Hence every zero-trace packet in `U_t` is internally forbidden from having residue
`a-t`.

In the critical case `|V(H)\S|=31m+1`, one of the four chambers `U_t` has size greater than `7m`.
For `m>=2`, Davenport can be applied twice disjointly in that chamber.  Thus every maximum core carries
at least two disjoint zero-trace packets in a single outside degree chamber, and every nonempty union of
such packets is forbidden from being an internal residue-`a-t` selector.  This is the packet quotient
form of the terminal anti-merge obstruction.

The exact merge condition only needs constant trace to `S`, not zero trace.  Quotient the trace group by
the constant vector:

```text
(Z/4Z)^S / <(1,1,...,1)> ~= (Z/4Z)^(m-1).
```

Its Davenport constant is `3m-2`.  Therefore every chamber `U_t` of size at least `3m-2` contains a
nonempty packet `X` for which all vertices of `S` see the same residue `p` of neighbours in `X`.
If `H[X]` has all degrees congruent to `a+p-t mod 4`, then `S union X` is a larger selector.  Thus
terminality forbids every constant-trace packet from being an internal selector of its matching residue.
In the critical case the largest outside degree chamber contains two disjoint constant-trace packets, and
all nonempty unions of a disjoint constant-trace packet family are forbidden at their matching residues.

Every constant-trace packet also satisfies the cross-edge congruence

```text
|X| t == m p        [MOD 4],
```

because both sides count `e(S,X)` modulo `4`: by summing over `X` one gets `|X|t`, while by summing over
`S` one gets `mp`.  Thus the packet trace residue is not free.  If `t` or `m` is a unit modulo `4`, then
the packet size determines the constant trace, or conversely; in the even cases only the corresponding
parity survives.  The terminal packet obstruction is therefore an arithmetic anti-selector problem on
constant-trace packets satisfying this cross-count congruence.

There is also the handshaking filter.  A packet `X` can be an internal selector of the matching residue
`r=a+p-t` only if

```text
|X| r == 0        [MOD 2].
```

When this fails, `X` is automatically harmless because the sum of its internal degrees would be odd.
When it holds, the parity of the internal edge count is fixed by

```text
e(X) == |X|r/2        [MOD 2].
```

Thus the dangerous packets are exactly the constant-trace packets satisfying both the cross-count
congruence and this handshaking parity condition.

To remove the handshaking nuisance, add the packet size as one more `Z/4Z` coordinate.  In the group

```text
((Z/4Z)^S / <(1,1,...,1)>) x Z/4Z ~= (Z/4Z)^m,
```

the Davenport constant is `3m+1`.  Hence every chamber `U_t` of size at least `3m+1` contains a
nonempty packet `X` with constant trace to `S` and

```text
|X| == 0        [MOD 4].
```

For such a packet the size divisibility side of handshaking is automatic.  The cross-count congruence
reduces to

```text
m p == 0        [MOD 4],
```

and the handshaking edge-count target becomes

```text
e(X) == 0        [MOD 2].
```

Thus an odd-edge packet is automatically harmless.  Terminality says that every even-edge admissible
packet `X` is not an internal selector of residue `a+p-t`.  In the critical largest degree chamber, for
`m>=2`, there are two disjoint size-`0 mod 4` constant-trace packets, and every nonempty union of a
disjoint family of them has the same even-edge handshaking target.  This is the cleanest packet endpoint:
the only remaining obstruction is internal residue synchronization inside arithmetically admissible
constant-trace packets with even internal edge parity.

The cross-count `mp==0 [MOD 4]` splits the endpoint into three arithmetic branches:

```text
m odd:        p==0,
m==2 mod 4:  p in {0,2},
m==0 mod 4:  p arbitrary.
```

Thus in the odd critical case every size-`0 mod 4` packet is actually zero-trace to the maximum core,
while in the `2 mod 4` case only the parity of the constant trace can vary.  The `m==0 mod 4` branch is
the only one in which all four constant traces survive.

Choose such a packet minimal in the size-refined trace group.  Then it is a packet atom: no proper
nonempty subpacket has both constant trace to `S` and size `0 mod 4`.  Equivalently, the associated
sequence in `(Z/4Z)^m` is a minimal zero-sum sequence, so the atom has size at most `3m+1`.  Terminality
therefore reduces the packet endpoint to the following finite atom obstruction:

```text
X is a size-0 mod 4 constant-trace atom in one U_t,
mp==0 mod 4,
H[X] is not residue-(a+p-t) regular modulo 4.
```

The largest outside degree chamber in a critical bucket contains two disjoint such atoms.  Hence a
terminal bucket must support two disjoint trace atoms in one chamber, while every atom and every union of
disjoint atoms fails the matching internal residue test.  No further trace-subpacket reduction is hidden
inside these atoms.

Greedy extraction gives a stronger cover form.  In the size-refined trace group `(Z/4Z)^m`, repeatedly
remove a minimal zero-sum atom from the largest outside degree chamber until the remainder is
zero-sum-free.  The remainder has size at most `3m`.  Since a critical largest chamber has size greater
than `31m/4`, it contains a disjoint atom family

```text
X_1,...,X_N
```

whose union has size greater than `19m/4`.  Terminality forbids every nonempty subunion of this atom
family from passing its matching internal residue test.  Thus the packet endpoint is a large atom-family
anti-selector problem, not merely a two-atom obstruction.

For an atom `X_i` with constant trace `p_i` in the same chamber `U_t`, define its internal defect

```text
epsilon_i(v)=deg_{X_i}(v)-(a+p_i-t)        [MOD 4]        (v in X_i).
```

The atom is dangerous exactly when `epsilon_i` vanishes identically.  For a disjoint family of atoms
`X_i`, put `p_I=sum_{i in I}p_i`.  The union `X_I` would merge with `S` exactly when, for every
`v in X_i`,

```text
epsilon_i(v)+sum_{j in I, j != i}(deg_{X_j}(v)-p_j) == 0        [MOD 4].
```

Thus the terminal packet endpoint is an anti-cancellation statement: every atom has a nonzero defect
vector, and no collection of cross-degree correction vectors from the other atoms can cancel all defects
simultaneously.  In the critical largest chamber this anti-cancellation already has to hold for two
disjoint atoms.

For two size-`0 mod 4` atoms `X,Y`, cancellation has a global parity filter.  Summing the two defect
equations over `X` and over `Y` gives

```text
2e(X)+e(X,Y)==0        [MOD 4],
2e(Y)+e(X,Y)==0        [MOD 4].
```

Therefore a two-atom union can be dangerous only when `e(X)` and `e(Y)` have the same parity and
`e(X,Y)` has the corresponding residue `0` or `2` modulo `4`.  If this global filter fails, the union is
automatically harmless before any pointwise defect analysis.

If the two atoms are themselves internally regular, say with residues `d_X,d_Y`, and the cross-degrees
are constant modulo `4`,

```text
deg_Y(x)==c_{XY} for x in X,        deg_X(y)==c_{YX} for y in Y,
```

then the two-atom union is dangerous exactly when

```text
d_X+c_{XY} == d_Y+c_{YX} == a+p_X+p_Y-t        [MOD 4].
```

Because both atom sizes are `0 mod 4`, the usual edge-count symmetry imposes no extra congruence on
`c_{XY},c_{YX}`.  In the same-profile subcase `p_X=p_Y` and `d_X=d_Y`, this reduces to the coalescence
rule `c_{XY}=c_{YX}` at the target residue.  Thus terminality forbids every such size-zero two-atom
quotient solution.

For a larger atom family, there is a clean quotient/uniformity split.  Suppose a subfamily `I` has the
property that, for every ordered pair `i != j` in `I`, the cross-correction

```text
kappa_{ij}(v)=deg_{X_j}(v)-p_j        [MOD 4]        (v in X_i)
```

is constant on `X_i`, say `c_{ij}`.  If each atom has constant internal defect `e_i`, then the union of
the subfamily is dangerous exactly when the weighted atom quotient satisfies

```text
e_i + sum_{j in I, j != i} c_{ij} == 0        [MOD 4]        for every i in I.
```

Thus a cross-uniform atom subfamily is governed by an ordinary finite quotient system over `Z/4Z`.
Terminality has two ways to block an atom family covering more than `19m/4` vertices: either every large
subfamily has a genuinely nonconstant cross-correction vector or the associated atom quotient has no
nonempty zero-row solution.  This is the atom-level form of the self-layer obstruction.

Equivalently, on the atoms with constant internal defect, form the irregularity graph `R_atom` by joining
`i` and `j` when at least one of the two cross-corrections `kappa_{ij},kappa_{ji}` is nonconstant.  Every
independent set of `R_atom` is a genuine quotient system over `Z/4Z`.  Terminality implies:

```text
every quotient-solvable independent set in R_atom has lifted size at most m.
```

Thus a terminal atom family of lifted size greater than `19m/4` must either contain many internally
nonconstant-defect atoms, have large irregularity graph, or be a quotient-free weighted `Z/4` system.

There is also a useful size dichotomy.  If some atom `X_i` has `|X_i|>m`, then `H[X_i]` is itself a
terminal induced chamber: by maximality of `m`, every mod-`4` residue-core inside `X_i` has size at most
`m`.  It is compact, with

```text
m < |X_i| <= 3m+1,
```

and it has no proper nonempty size-`0 mod 4` constant-trace subpacket relative to `S`.  This is the
large-atom branch.

Otherwise all atoms have size at most `m`.  Since the extracted atom family covers more than `19m/4`
vertices, the family contains at least five atoms.  This is the finite-quotient branch: one has at least
five disjoint size-`0 mod 4` trace atoms in a single outside degree chamber, every nonempty subunion is
anti-selector, and the obstruction must be witnessed by the atom irregularity graph or by quotient
unsolvability over `Z/4Z`.

The critical endpoint also has the Ramsey base `m>=4`: if `m<=3`, then
`|H|=32m+1>=18` in every nontrivial case, and `R(4,4)=18` gives a clique or independent set of size `4`,
itself a selector.  Thus every size-refined atom has size in

```text
4,8,12,...,m
```

in the small-atom branch.  The finite quotient obstruction is therefore a positive weighted atom system,
with all weights divisible by `4`, total weight greater than `19m/4`, and no quotient-solvable subfamily
of weight greater than `m`.

This weighted system contains disjoint threshold bundles.  Order the atoms arbitrarily and take a minimal
initial block whose total weight exceeds `m`; since every atom has weight at most `m`, this block has
weight at most `2m`.  Removing it leaves total weight greater than `11m/4`, so the same argument gives a
second disjoint block, again with weight in `(m,2m]`.  Therefore the small-atom branch supplies two
disjoint atom bundles of lifted size greater than `m`.  Each bundle must be blocked independently: either
its cross-corrections are not quotient-uniform, its internal defects are not constant on atoms, or its
weighted `Z/4` atom quotient has no zero-row solution.

Choose the two bundles minimal above the threshold.  If `B` is one such bundle with lifted weight
`w(B)`, then

```text
m < w(B) <= 2m,        w(B)-w_i <= m for every atom i in B.
```

Equivalently every atom in `B` has weight at least the excess `w(B)-m`.  Thus minimal threshold bundles
are tight.  Since the two bundles are disjoint, their union has weight greater than `2m` and is also a
forbidden threshold object.  Hence terminality must block not only each bundle separately but also the
combined bundle: if all defects are atom-constant and all cross-corrections inside and between the two
bundles are quotient-uniform, the combined weighted `Z/4` quotient has no zero-row solution.

The small-atom endpoint is therefore a finite two-bundle obstruction: two tight threshold bundles of
size-`0 mod 4` trace atoms, each quotient-blocked, whose union is also quotient-blocked unless some
cross-correction is genuinely nonconstant.

Equivalently, each of the three threshold objects

```text
B_1,        B_2,        B_1 union B_2
```

carries one of three certificates:

```text
D: an atom has nonconstant internal defect,
C: a directed atom-pair has nonconstant cross-correction,
Q: all defects/cross-corrections are constant but the weighted Z/4 quotient has no zero-row solution.
```

If all three certificates are `Q`, the obstruction is purely finite and lives entirely in a weighted
`Z/4` quotient on at least five atoms.  Otherwise the terminal graph contains a concrete local
irregularity certificate inside one atom or between two atoms of the same outside degree chamber.  This
three-certificate split is the current terminal normal form of the small-atom branch.

In the pure `Q` case there is a precise residual-vector form.  For a quotient-uniform bundle `B`, define

```text
R_i(B)=e_i+sum_{j in B, j != i}c_{ij}        [MOD 4]        (i in B).
```

The bundle is blocked by a `Q` certificate exactly when `R(B)` is not the zero vector.  For two disjoint
quotient-uniform bundles `B_1,B_2`, put

```text
C_i(B_2)=sum_{j in B_2}c_{ij}        (i in B_1),
C_j(B_1)=sum_{i in B_1}c_{ji}        (j in B_2).
```

Then the combined bundle `B_1 union B_2` is dangerous exactly when

```text
C_i(B_2) == -R_i(B_1)        for every i in B_1,
C_j(B_1) == -R_j(B_2)        for every j in B_2.
```

Thus the pure two-bundle obstruction is affine avoidance: both individual bundles have nonzero residual
vectors, and the cross-bundle correction vectors avoid the unique affine target that would cancel them.

The same residual language gives a one-atom repair test.  Let `B` be a pure `Q` bundle and let `y` be an
atom outside it, with internal defect `e_y`.  The enlarged bundle `B union {y}` is dangerous exactly when

```text
c_{iy} == -R_i(B)        for every i in B,
e_y + sum_{i in B}c_{yi} == 0        [MOD 4].
```

Thus every outside atom avoids a unique affine repair profile for `B`: either at least one incoming
correction to an atom of `B` misses `-R_i(B)`, or the outgoing row sum from `y` misses `-e_y`.  In a
terminal pure-quotient branch, this pointwise repair avoidance must hold for every tight threshold
bundle and every atom outside it.

For a packet `Y` of outside atoms the repair equations are the atom-level co-cut system

```text
sum_{y in Y}c_{iy} == -R_i(B)        for every i in B,
e_y + sum_{i in B}c_{yi} + sum_{z in Y, z != y}c_{yz} == 0        for every y in Y.
```

The first line is linear in the old bundle `B`; the second line is the fresh self-layer on the atom packet
`Y`.  Thus the pure quotient branch has reproduced the original obstruction at a smaller quotient scale:
old residuals can be repaired by an outside atom packet only if that packet both hits the affine
incoming target and is internally regular after the shifted row labels.  Terminality says every outside
atom packet fails one of these two lines.

Separate these two failures.  For a fixed pure `Q` bundle `B`, define the incoming profile of an outside
atom packet by

```text
P_B(Y)_i=sum_{y in Y}c_{iy}        [MOD 4]        (i in B).
```

Then every outside packet `Y` is blocked in exactly one of the following ways:

```text
incoming failure:      P_B(Y) != -R(B),
self-layer failure:    P_B(Y)=-R(B), but the shifted atom degrees on Y are not all 0 mod 4.
```

Thus the pure quotient branch splits into affine target avoidance in the profile group `(Z/4Z)^B` and a
smaller shifted principal-submatrix problem on packets that hit the target.  This is the exact
atom-quotient analogue of the earlier deletion-layer split.

There is a corresponding profile-Davenport branch, but it is only a zero-target tool and must not be
mistaken for an arbitrary-target theorem.  If `B` contains `b` atoms, then the incoming profile group is
`(Z/4Z)^b` and has Davenport constant `3b+1`.  Any collection of at least `3b+1` outside atoms contains a
nonempty packet with zero incoming profile to `B`.  This preserves whatever incoming defect was already
present; it does not by itself hit the affine target `-R(B)`.  Therefore the atom-quotient endpoint
splits again:

```text
target-hit branch:      some outside packet has P_B(Y)=-R(B), leaving only the shifted self-layer;
target-avoid branch:    outside profiles avoid -R(B), while zero-profile packets exist once the atom count is large.
```

In the target-avoid branch, any zero-profile packet that is shifted-self-regular can be merged with a
target-hitting seed, if such a seed exists.  Without a seed, it only certifies another internally
forbidden atom packet.  This is why the residual is affine target avoidance rather than ordinary
Davenport balancing.

Equivalently, write

```text
Sigma_B(A)={P_B(Y):Y subset A}
```

for the profile subset-sums of an outside atom pool `A`.  The target-hit branch is
`-R(B) in Sigma_B(A)`.  Once a seed `Y_0` with `P_B(Y_0)=-R(B)` is fixed, every disjoint zero-profile
packet `Z` in `A\Y_0` keeps the incoming target:

```text
P_B(Y_0 union Z)=-R(B).
```

Therefore terminality forces every such zero-profile `Z` to fail the shifted self-layer relative to the
already shifted labels created by `Y_0`.  The target-hit branch thus becomes a seeded zero-profile
self-layer problem.

The target-avoid branch is the exact complement:

```text
-R(B) notin Sigma_B(A).
```

It is a pure affine subset-sum avoidance condition in `(Z/4Z)^B`; zero-profile Davenport packets exist in
large pools, but they live in the stabilizer of the already-avoiding subset-sum set and cannot create the
missing affine target without a seed.

The target-avoid branch has a standard inverse form.  Let

```text
G_B=(Z/4Z)^B,        Sigma=Sigma_B(A),        H=Stab(Sigma).
```

Since `0 in Sigma`, the set `Sigma` is a union of `H`-cosets.  If `-R(B) notin Sigma`, its `H`-coset is
missing, so

```text
|Sigma| <= |G_B|-|H|.
```

On the other hand, the sequence form of Kneser's theorem applied to
`Sigma=sum_{y in A}{0,P_B(y)}` gives

```text
|Sigma| >= |H|(1+N_out),
```

where `N_out` is the number of outside atoms whose profile is not in `H`.  Hence

```text
N_out <= |G_B/H|-2.
```

Thus affine target avoidance is possible only with a proper period subgroup `H` such that all but at most
`|G_B/H|-2` outside atom profiles lie in `H`, while the target coset `-R(B)+H` is absent from the profile
sumset.  This is the inverse-Kneser normal form of the target-avoid branch.

Because `G_B` is a `2`-group, this inverse form can be sharpened into a binary flag.  Choose a maximal
subgroup chain

```text
G_B=H_0 > H_1 > ... > H_s=H
```

whose successive quotients have order `2` and whose last quotient still sees the missing coset.  At a
level `H_i > H_{i+1}`, write `tau_i` for the current residual target in `H_i`.  If no available zero-prefix
profile packet has odd image in `H_i/H_{i+1}` while `tau_i` has odd image, then the target is separated by
the parity character `H_i -> H_i/H_{i+1}`.  If such a packet exists, fix a minimal odd seed `Y_i`; then

```text
tau_{i+1}=tau_i-P_B(Y_i) in H_{i+1},
```

and every further repair must be a zero-prefix packet for the quotient `H_i/H_{i+1}`.  Iterating, a target
avoidance counterexample is therefore a finite binary descent in which each level either supplies a seed
and passes to the next index-two subgroup, or stops at a parity character that is invisible to all
remaining zero-prefix packets but nonzero on the residual target.  In particular, the affine-avoidance
branch is a first-bit obstruction in a quotient flag, not an unstructured subset-sum failure.

At the stopping level this can be stated without the preceding flag.  Let `K` be the subgroup already
forced by the earlier zero-prefix conditions and let `chi:K -> Z/2Z` be the next quotient character.  The
stopped branch is exactly

```text
chi(P_B(Y))=0        for every available K-valued repair packet Y,
chi(tau)=1           for the residual target tau.
```

Equivalently, the next bit of every realizable repair packet is a consequence of the previous quotient
bits, but the target has the opposite next bit.  The terminal selector theorem is therefore reduced, in
this branch, to excluding a single first-bit separation character on atom-profile repair packets.  This is
the profile-sum analogue of the hidden `0001`/missing-`0111` square: the visible lower bits are all
compatible, and the only missing datum is one successor bit that refuses to be realized by a packet.

The same stopped form can be read as relation-rigidity.  Let `pi` denote the lower quotient profile before
the stopped character.  For every admissible packet relation

```text
sum_{Y in F} pi(P_B(Y)) = 0
```

among pairwise disjoint available repair packets, one must also have

```text
sum_{Y in F} chi(P_B(Y)) = 0.
```

Otherwise the union of that relation is lower-zero and odd in the stopped bit, giving the next seed and
contradicting stoppedness.  Thus the successor bit factors through the lower packet-relation monoid; the
residual target is precisely a lower-zero element on which this factorization would take value `1`.  Any
proof of a lower-profile odd relation is therefore enough to close the target-avoid branch.

The stopped character is concrete.  Every homomorphism `(Z/4Z)^B -> Z/2Z` is reduction mod `2` followed by
summation over a subset `W subseteq B`; hence, after replacing `chi` by its support,

```text
chi(z)=sum_{i in W} z_i        [MOD 2].
```

The stopped condition becomes the cut-parity certificate

```text
sum_{i in W} sum_{y in Y} c_{iy} = 0        [MOD 2]
```

for every lower-zero available repair packet `Y`, while the residual target satisfies

```text
sum_{i in W} R_i(B) = 1        [MOD 2].
```

Choose such a support `W` inclusion-minimal.  Then every proper nonempty `W' subset W` with
`sum_{i in W'}R_i(B)=1 mod 2` must have a lower-zero packet with odd `W'`-cut parity; otherwise `W'` would
be a smaller stopped support.  Thus the terminal target-avoid obstruction is not merely a character but a
minimal binary cut circuit inside the pure `Q` bundle:

```text
proper odd subcuts are seed-realized,        the full W-cut is not.
```

The singleton case is a one-atom row-parity obstruction, the two-atom case is a pair-chamber parity
obstruction, and supports of size at least three are higher binary circuits whose every odd proper face is
already repairable.  This is the atom-quotient analogue of the host-frontier trichotomy: singleton row
memory, opposite-pair anti-Horn, and ternary one-corner lift are three support sizes of the same stopped
successor-bit certificate.

There is a useful dual normalization of the minimal support.  Work in a fixed outside reservoir and let
`P_W` be the `F_2`-span of the cut-parity vectors

```text
p(Y)=(sum_{y in Y}c_{iy} mod 2)_{i in W}
```

of lower-zero repair packets available in that reservoir.  Stoppedness gives

```text
P_W subseteq {u in F_2^W : sum_{i in W}u_i=0}.
```

Let `r=(R_i(B) mod 2)_{i in W}`.  Minimality of `W` says that every proper subcut `A subset W` with
`r(A)=1` is detected by some packet vector, i.e. `1_A` is not orthogonal to `P_W`.  Since `r(W)=1` and the
all-ones vector `1_W` is orthogonal to `P_W`, the orthogonal complement of `P_W` meets the affine hyperplane
`r(A)=1` only at `1_W`.  A subspace with this property is exactly `span(1_W)`.  Hence

```text
P_W = {u in F_2^W : sum_{i in W}u_i=0}.
```

Thus the minimal stopped circuit is formally full: every even cut-parity pattern on `W` is generated by
lower-zero repair packets.  The missing object is precisely an actual disjoint lower-zero packet with odd
total `W`-cut.  Any remaining obstruction is therefore not a binary linear obstruction; it is a
odd-coset packet-realization obstruction, i.e. the same provenance/disjointization issue that appeared in the
host `0001` square.

Equivalently, form the lower-profile packet graph whose vertices are reachable lower profiles and whose
edges are available repair moves; decorate each edge by its `W`-cut parity.  The absence of an odd
lower-zero packet says that every realized closed walk has even decoration.  Hence the decoration defines
a flat two-sheeted cover of the realized lower-profile graph.  An odd repair packet is precisely a closed
walk with nontrivial sheet holonomy.  Thus the stopped target-avoid branch is a rank-one cover obstruction:
either the lower-profile cycles are generated by local packet squares/relations whose holonomy is already
even, in which case the cover is trivial on the component, or there is a first local cycle with odd
holonomy.  That first odd cycle is the profile version of the missing `0111` corner: a local packet square
whose three visible lower faces are realized and whose fourth face is the absent odd-coset packet.

This gives the exact three-exit split for odd-coset realization.

```text
branch:       two realized packets have the same lower profile and opposite W-parity;
local cycle:  a minimal packet square has odd holonomy;
sheet:        the cover is unbranched and every local packet square is flat.
```

The branch case should be read with its collision term exposed.  Choose two opposite-parity realizations
`Y^0,Y^1` of one lower profile with `|Y^0 cap Y^1|` minimal and write

```text
C=Y^0 cap Y^1,        A=Y^0\C,        A'=Y^1\C.
```

The common part cancels from the stopped bit, so the oddness lives on the signed disjoint relation
`A-A'`.  If that signed relation can be promoted to an unsigned lower-zero packet, the branch closes.
If it cannot, minimality gives the signed branch normal form

```text
pi(P_B(A))=pi(P_B(A')),        chi(P_B(A))+chi(P_B(A'))=1,
```

with no proper signed subrelation and no neutral packet that reduces either side.  Thus the only surviving
branch obstruction is signed-to-unsigned packet provenance: a formal opposite-sheet relation exists, but no
admissible packet realizes its odd coset.  In the local-cycle case, the first odd square is a
support-local missing-corner obstruction, hence one of the `0001`/missing-`0111` host atoms.  In the sheet
case, the parity is a global sheet character constant on all local packet exchanges.  Then any ambient
separator that sees the two sheets is a sheet-character module breaker: if it is admitted by the packet
boundary, it supplies the odd-coset packet; if it is not admitted, the obstruction is exactly boundary
provenance for the sheet character.  Thus the atom-profile target-avoid branch has no fourth endpoint
beyond signed branch provenance, local missing-corner square, and sheet-character provenance.

The signed branch itself has a useful collapse.  Fix the common lower profile and form the exchange graph
on all realizations of that profile, joining two realizations when their symmetric difference is one
neutral lower-zero packet exchange.  If the opposite-parity pair lies in one exchange component, a shortest
path between them is an odd closed walk in the lower-profile packet graph; its first odd elementary square
is the local-cycle exit above.  If the pair lies in different exchange components, parity is constant on
each component and the component partition is an unbranched sheet character for that lower profile.  An
ambient separator between the components is therefore again a sheet-character provenance problem.  Hence,
after exchange connectivity is admitted, signed branch provenance is not a new case: it folds into either
an odd local packet square or the same sheet-character boundary provenance.

The sheet case has the corresponding module squeeze.  In an unbranched flat cover, the two sheet classes
over a fixed lower-profile component are preserved by every neutral packet exchange.  If one sheet class
has lifted weight greater than `m` and all its internal defects and cross-corrections are quotient-uniform,
then the atom quotient restricted to that sheet is a smaller principal selector problem.  A quotient
solution gives a forbidden selector of weight greater than `m`; quotient nonsolvability gives a smaller
pure `Q` bundle and restarts the target-avoid analysis inside the sheet.  Therefore a terminal unbranched
sheet survivor can be normalized so that every large sheet component has an explicit local irregularity
certificate, or else every quotient-uniform sheet component has weight at most `m`.

Consequently the only unbranched sheet case not already reduced is a boundary-provenance failure: the
global sheet character is visible to some ambient separator, but no admitted first-return/packet-boundary
row realizes that separator.  This is exactly the rank-one sheet-character fullness problem isolated on
the host side.  If fullness holds, the separator becomes an odd-coset packet and the target-avoid branch
closes; if fullness fails, the first failed boundary exchange is again a local missing-corner square.

The fullness problem has a restart form.  Let `h` be a sheet-character separator that is prefix-local for
the current atom reservoir and whose terminal residue vector is zero in every recorded lower quotient.  Run
the terminal descent with `h` forced as the first boundary row.  If the restarted descent is comparable
with the original descent, then zero residue and prefix-locality make `h` an admitted boundary row, hence
an odd-coset packet.  If the two descents are not comparable, choose the first exchange where their
boundary histories diverge.  A nonzero residue at that exchange is an already classified local exit; a
zero-residue disagreement is precisely a missing exchange square.  Thus sheet-character provenance is
equivalent to restart admissibility:

```text
zero-residue prefix-local sheet separators are first-boundary admissible,
unless the comparison exposes a local missing-corner square.
```

In the intrinsic exchange-saturated boundary category this criterion is tautological: zero-residue
prefix-local rows are admitted by definition, and the first packet-internal failure is a smaller
exchange-complete marker.  The remaining unsaturated content is only the comparison between the historical
path boundary and that saturated boundary, i.e. the path-saturation equivalence/omni-saturation lemma.

The comparison has a shortest-loop normal form.  Suppose a path-only boundary and an exchange-saturated
boundary first differ on a zero-residue sheet separator, and choose such a comparison with the shortest
closed exchange loop.  Then the loop has:

```text
no nonfilled or curved square,          otherwise there is a local missing-corner exit;
no filled flat chord,                   otherwise the loop splits into shorter comparisons;
no proper exchange-complete interval,   otherwise that interval is a smaller marker;
no repeated lower profile,              otherwise the intervening subloop is shorter.
```

Thus a genuine path-saturation failure is a chordless rank-one flat loop whose every proper interval is
not exchange-complete and whose only sheet change is the central sheet-character separator.  If all
rank-one flat loops of this kind are generated by filled packet squares and exchange-complete intervals,
then path-saturation equivalence holds and the sheet case closes.  If not, the first nongenerated loop is
the exact omni-saturation atom: a two-state residue-zero square or an admissible-module/local-exit failure
for the sheet-character module.  This is the current smallest unsaturated endpoint.

Equivalently, the loop endpoint is a two-state package transposition after the following active-edge
normalization.  If a shortest flat loop contains two independent active sheet separators, their commutator
is either a nonfilled/curved local square or a filled flat square.  The first is a local exit; the second is
a chord or an exchange-complete interval, both forbidden by the shortest-loop normalization.  Hence all
active sheet changes in a genuine survivor are the same rank-one separator.  A loop using one separator
more than twice repeats a lower profile, and a loop using it exactly twice is the two-state transposition.
Thus the unsaturated sheet endpoint is precisely:

```text
a residue-zero two-state sheet transposition not generated by an admitted boundary exchange.
```

This is the same endpoint reached from the host frontiers: `host-orient115` sees it as missing
two-fiber overlap, `host-opppair123` as outgoing no-split failure, and `host-silentedge128` as the anchored
one-corner missing square.

The two-state transposition has a row-action normal form.  Write the two states as disjoint realizations
`A` and `A'` of the same lower profile after cancelling their common part.  The transposition carrier is

```text
K=A union A'.
```

For any ambient row `r`, put

```text
delta_r(K)=deg_A(r)-deg_{A'}(r)        [MOD 4].
```

All recorded lower rows have `delta_r(K)=0`; otherwise the two states would not have the same lower
profile.  If every ambient row has `delta_r(K)=0`, then `A` and `A'` are indistinguishable to the whole
boundary calculus, so `K` is a sheet-clone module; selector-primality gives a module/local exit.  Hence a
genuine survivor has a distinguishing row.  Choose the first such row in the boundary history, and choose
the transposition with minimal carrier among those distinguished by it.

Minimality forces this first distinguishing row to be fully skew on the carrier.  If the support on which
`r` distinguishes `A` from `A'` were a proper signed subcarrier, that subcarrier would be either a smaller
zero-residue transposition, a neutral packet reducing one side, or a local missing square at the first
place where the row action changes.  Therefore the survivor satisfies:

```text
delta_r(K) != 0,
delta_s(K)=0 for every earlier recorded row s,
and r has no proper distinguished subcarrier of K.
```

This is the concrete boundary-provenance form of the endpoint: a single fully-skew separator row sees the
two sheets, all earlier prefix-local tests are blind, and admitting that separator as a boundary row would
generate the missing transposition.  Thus the remaining two-state atom is exactly fully-skew row promotion,
unless its first row-action change exposes the local `0001` square.

In the exchange-saturated convention this row-promotion endpoint is already closed by Proposition 9.2.
Indeed, once the first fully-skew row is admitted as an ordered boundary row, Lemma 9.1 makes its first
packet-internal failed set a whole side of a protected packet of size `<q`; the low-set congruence then
requires that side to have size `0 mod q`, impossible.  Therefore a two-state transposition cannot survive
in `FR^sat`.  The unsaturated residue is exactly the transport statement:

```text
the first fully-skew row distinguished by path-only provenance is also an FR^sat boundary row,
unless transport to FR^sat exposes a local missing-corner square.
```

Thus all algebraic and saturated-category obstructions have been removed from the transposition endpoint;
only path-to-saturated provenance transport remains.

That transport can be normalized as a prefix-insertion ladder.  Let

```text
b_1,b_2,...,b_t
```

be the historical path-boundary word before the fully-skew separator `h` becomes visible in `FR^sat`.
Attempt to commute `h` leftward across the word.  At the step crossing `b_i`, exactly one of the following
occurs:

```text
the exchange square (h,b_i) is nonfilled or curved, giving a local missing-corner exit;
the square is filled and flat, so h commutes past b_i and remains zero-residue prefix-local;
h is already an admitted boundary row.
```

Choose a minimal transport failure.  Then every crossing is filled and flat, `h` never becomes admitted,
and each transported row `h_i` is fully skew on the same carrier `K`; otherwise the first change of carrier
or row-action gives the local `0001` square or a smaller transposition.  Thus the whole failure is a
same-carrier skew ladder

```text
h_t=h, h_{t-1}, ..., h_0
```

with identical visible residue/profile data and only the hidden path position changing.  If two ladder
states repeat, the intervening segment is a shorter flat loop; if the ladder reaches the beginning, `h_0`
is a first boundary row and Proposition 9.2 kills it.  Therefore the unsaturated endpoint is hidden
selector memory: a same-carrier fully-skew row whose every visible commutation is flat, but whose
path-only category refuses to identify the transported copies.

This is an exact equivalence.  Define the memory-free prefix axiom:

```text
two zero-residue prefix-local fully-skew rows with the same carrier K and the same row-action
are the same boundary row for terminal descent purposes.
```

Under this axiom the skew ladder collapses immediately to a first-boundary row, so Proposition 9.2 excludes
the two-state transposition.  Conversely, any path-only transposition survivor produces a skew ladder in
which all visible data are identical but two transported copies are not identified by the boundary
category.  Thus the remaining unsaturated theorem is neither additive, Kneser-theoretic, nor modular: it
is precisely memory-free prefix fullness for same-carrier fully-skew rows.

There is one last visible/invisible split.  If two transported copies in the skew ladder have different
graph-visible trace outside the carrier `K`, let `z` be the first row or vertex detecting the difference.
If `z` is already boundary-admitted, the pair of transported copies and `z` form the same-trace
distinguished-pair configuration handled by the local same-trace/twin closures; if `z` is not admitted, it
is a smaller boundary-provenance failure than the original sheet separator.  Hence a minimal hidden-memory
survivor can be assumed graph-invisible:

```text
all transported fully-skew copies have the same trace to every graph row outside K
and the same row-action on K.
```

Such a survivor is not a new graph-theoretic obstruction.  It is an artefact of remembering the historical
path label after all graph-visible traces and residues have become equal.  Quotienting the boundary
category by this graph-intrinsic equality is exactly the memory-free prefix fullness axiom above; in that
quotient the final two-state transposition is killed by Proposition 9.2.

The quotient is conservative for the degree problem.  Every terminal equation used by the selector proof
depends only on the lower profiles, terminal residues, and row-actions on the active carrier.  Identifying
two boundary rows with the same data changes neither the deletion equation nor any shifted self-layer
equation; it merely chooses a different representative of the same graph-intrinsic move.  Thus the
graph-intrinsic saturated proof has no remaining two-state sheet obstruction.  What remains, if one insists
on the historical path-only boundary category rather than the graph-intrinsic quotient, is the bookkeeping
comparison theorem that the historical category already performs this quotient unless a local
missing-corner square appears.

For the theorem proved in this document that comparison is disposable.  The terminal descent is defined
from the graph-intrinsic saturated category, not from a remembered path word.  Enlarging from the path-only
category to this quotient does not add a formal move: every saturated boundary row is represented by actual
four-corner graph exchange data with zero terminal residue, and every quotient identification preserves the
degree equations above.  Therefore a path-only hidden-memory survivor is not a counterexample to the
graph theorem; it is only a counterexample to the stronger statement that one particular historical
first-return bookkeeping convention already chose the graph-intrinsic representative.  The three named
host atoms are consequently discharged for the saturated proof:

```text
host-orient115:   the two-fiber non-overlap is the two-state sheet transposition;
host-opppair123:  outgoing no-split failure is the same transposition seen on Q^+;
host-silentedge128: the silent edge is the first nonflat commutation of that transposition.
```

In `FR^sat` the first two are killed by row promotion plus Proposition 9.2, and the third is exactly the
local missing-corner exit.  No extra host-frontier input is needed by the saturated terminal proof.

This last principal bucket has immediate rank and module exits.  If two vertices have identical internal
neighbourhood rows over `F_2`, then they are false twins inside the bucket; a trace class of size greater
than `m` is an independent congruent selector.  More generally, if the internal adjacency matrix over
`F_2` has row-rank `r`, some row class has size at least `n/2^r`, so a terminal bucket of size `n` must
satisfy

```text
2^r > n/m.
```

The same statement in the complement controls true-twin classes: a complement-row class of size greater
than `m` is a clique congruent selector.  Therefore a terminal principal bucket is high-rank on both the
graph and its complement at the selector scale.

Modules give the corresponding nonlinear exit.  If `M` is a module of the principal bucket, then every
vertex of `M` has the same external contribution from the bucket complement.  Hence any mod-`4` selector
inside `G[M]` of size greater than `m` is also a selector in the whole bucket.  A terminal bucket is
therefore selector-prime: every module of size exceeding the current threshold is itself a smaller
terminal principal bucket.  In particular, modular decomposition cannot be the source of the final
obstruction; one may pass to a prime node whose size is still superlinear in `m`.

Combining these two exits, the final mixed bucket can be assumed to have no large twin class, no large
co-twin class, no large reducible module, and F2 row-rank at least `log_2(n/m)` in both graph and
complement.  This is the first intrinsic constraint on the internal principal-submatrix selector.

It is also hereditarily dense and hereditarily codense at the selector scale.  Indeed, if some induced
subbucket `U` has an independent set or a clique of size greater than `m`, that set is already a
principal selector.  Hence every `U` with `|U|>m` satisfies

```text
alpha(H[U]) <= m,        omega(H[U]) <= m.
```

By Caro--Wei, or just the average-degree form of Turan's bound, this forces

```text
avgdeg(H[U]) >= |U|/m - 1,
avgdeg(complement(H[U])) >= |U|/m - 1.
```

Consequently no sparse or dense induced chamber can survive inside the terminal bucket.  The final
obstruction is simultaneously deletion-rigid, selector-prime, high-rank over `F_2`, and hereditarily
dense/codense; any proof of the principal selector may now assume all four properties.

There are also small-extension equations around every maximum core.  Fix a maximum selector `S` of size
`m` and residue `a`, and put `O=V(H)\S`.  For a nonempty outside set `X subset O`, the extension
`S union X` would be a selector of size greater than `m` exactly when there is a residue `c` such that

```text
deg_X(v) == c-a                         [MOD 4]        for every v in S,
deg_S(x)+deg_X(x) == c                  [MOD 4]        for every x in X.
```

Thus terminality forbids every outside packet whose trace-sum on `S` is constant and whose shifted
self-layer has the matching constant.  The first cases are explicit:

```text
|X|=1:  x is complete or anticomplete to S, with the corresponding scalar degree congruence;
|X|=2:  the two traces have constant sum on S, and the two shifted degrees agree with that sum;
|X|=3:  a ternary constant-sum trace with one shifted self-layer equation on the induced triangle/path.
```

These are the principal-submatrix analogues of the three host atoms.  The singleton test is row
promotion, the pair test is the opposite-pair/no-split test, and the ternary test is the one-corner
missing-square test.  The atom-quotient reductions above are precisely the large-packet version of these
same equations: if a large outside family contains a constant-sum trace packet whose shifted self-layer is
regular, the maximum core extends and terminality is contradicted.

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

In a critical counterexample the same observation gives a useful four-step normal form.  Let `m` be the
maximum size of a mod-`4` principal selector and assume `n>=32m+1`.  After four Gallai even-child steps
there is an even induced core `J` with

```text
|J| >= n/16 > 2m.
```

Split `J` into its two internal degree-residue classes

```text
J_0={v in J : deg_J(v)=0 mod 4},        J_2={v in J : deg_J(v)=2 mod 4}.
```

One of these, call it `R`, has size greater than `m`; let `C=J\R`.  Since `deg_J` is constant modulo `4`
on `R`, the induced degrees in `R` satisfy

```text
deg_R(v) == deg_J(v)-deg_C(v)        [MOD 4]        (v in R).
```

Therefore `R` itself would be a forbidden selector unless the co-cut degree `deg_C(v) mod 4` is nonconstant
on `R`.  Thus every critical first-bit counterexample contains a **large two-residue co-cut obstruction**:
an even core `J=R disjoint_union C`, with `|R|>m`, constant `deg_J mod 4` on `R`, and nonconstant
`deg_C mod 4` on `R`.  This is the exact terminal self-layer defect left by recursive Gallai: the first
bit is synchronized inside `J`, and the only unsynchronized datum is the co-cut carry from the opposite
residue class.

The co-cut obstruction is a labeled deletion-core problem on `R`.  Use the signed co-cut label

```text
b(v)=-deg_C(v)        [MOD 4]        (v in R).
```

For `T subset R` and `D=R\T`, since `deg_J` is constant modulo `4` on `R`,

```text
deg_T(v) == const + b(v) - deg_D(v)        [MOD 4]        (v in T).
```

Hence `T` is a mod-`4` selector iff there is a residue `lambda` such that

```text
deg_D(v) == b(v)-lambda        [MOD 4]        for every v in T.
```

Equivalently, start with `R` and iteratively delete vertices not satisfying
`deg_D(v)=b(v)-lambda` for the current deleted layer `D`; the surviving `lambda`-core is exactly a selector
inside `R`.  Therefore the first-bit residual can be stated without the opposite class except through the
fixed label `b`: a large labeled graph `(R,b)` whose four labeled deletion-cores all have size at most
`m`.  This is the labeled version of the principal bucket pruning process.

Equivalently, `(R,b)` has a hereditary labeled elimination order.  For each `lambda in Z/4Z` and every
`U subset R` with `|U|>m`, not all vertices of `U` can satisfy

```text
deg_{R\U}(v) == b(v)-lambda        [MOD 4].
```

Hence some `v in U` fails this congruence.  Deleting such a failing vertex and repeating gives, for every
`lambda`, an order deleting all but at most `m` vertices in which each deleted vertex was currently bad for
the same labeled deletion equation.  Conversely, such an order precludes a `lambda`-core larger than `m`.
Thus the first-bit residual is equivalently a labeled graph in which every residue admits a complete
bad-vertex elimination down to the threshold.

The same row/module exits survive after labels are included.  If a set `M subset R` is a module, then every
vertex of `M` has a constant outside contribution `delta_M=deg_{R\M}(v)`.  Any labeled selector inside
`(M,b|_M)` lifts to `(R,b)` after shifting `lambda` by `delta_M`; therefore a terminal labeled residual is
label-selector-prime.  In particular, a false-twin row class with constant label and size greater than `m`
is an independent labeled selector, and a true-twin row class with constant label and size greater than
`m` is a clique labeled selector.  Thus the row-rank bounds strengthen to label-refined form:

```text
4*2^r > |R|/m
```

for the `F_2` row-rank `r` of the graph, and likewise for the complement.  The label `b` cannot hide in a
large low-rank row class.

The labeled obstruction is hereditary, but the label changes.  For `U subset R`, a selector
`T=U\D` inside `U` lifts to a selector in `R` exactly with the relabeled function

```text
b_U(v)=b(v)-deg_{R\U}(v)        [MOD 4]        (v in U),
```

because

```text
deg_{R\T}(v)=deg_{R\U}(v)+deg_{U\T}(v).
```

Thus every induced subbucket `(U,b_U)` is again terminal at the same threshold.  In particular, for every
`U` with `|U|=m+1`, the full-set test `D=emptyset` says `b_U` is nonconstant.  This explains why the
labeled residual cannot be closed by merely shrinking to one-over-threshold size: any graph on `m+1`
vertices with a nonconstant label survives the full-set test.  The remaining information is in the parent
coupling, namely that the label is not arbitrary but the signed co-cut degree `-deg_C mod 4` from the
opposite Gallai residue class, and that every subbucket inherits the correction `-deg_{R\U}`.

For a retained set `T subset R` of size `m+1`, write its current labeled residue as

```text
psi_T(v)=b(v)-deg_{R\T}(v)        [MOD 4]        (v in T).
```

Then `T` is a selector iff `psi_T` is constant.  Terminality is therefore the assertion that every
`(m+1)`-set has at least two `psi_T`-colors.  The one-swap calculus is exact.  If
`x in T`, `y in R\T`, and `T'=(T\{x}) union {y}`, then for `v in T\{x}`,

```text
psi_T'(v)=psi_T(v)+1_{vy}-1_{vx}        [MOD 4],
```

while the incoming vertex has

```text
psi_T'(y)=b(y)-deg_{R\T}(y)-1_{xy}      [MOD 4].
```

Thus any proof of the first-bit selector may equivalently show that a nonconstant `psi_T` coloring on an
`(m+1)`-set can be flattened by one or more such swaps.  A terminal counterexample is a local optimum for
this swap system: every swap keeps at least two colors.  This is the labeled co-cut version of the
small-extension equations around a maximum core.

More generally, for a balanced swap `X subset T`, `Y subset R\T` with `|X|=|Y|`, put
`T'=(T\X) union Y`.  Then

```text
psi_T'(v)=psi_T(v)+deg_Y(v)-deg_X(v)                         (v in T\X),
psi_T'(y)=b(y)-deg_{R\T}(y)+deg_Y(y)-deg_X(y)                 (y in Y).
```

Thus a balanced swap closes the first-bit residual exactly when these two displayed expressions are
constant on `(T\X) union Y`.  The one-swap row-promotion, two-swap no-split, and larger packet-repair
equations are all instances of this single formula.  A terminal labeled residual is therefore a
balanced-swap local optimum at every `(m+1)` retained set.

Separating the two lines gives the exact incoming-target/self-layer split.  Fix `T`, a deleted part
`X subset T`, and a desired final residue `kappa`.  An incoming packet `Y subset R\T`, `|Y|=|X|`, must
first hit the old-vertex target

```text
deg_Y(v)=kappa-psi_T(v)+deg_X(v)        [MOD 4]        (v in T\X).
```

If this target is hit, the remaining condition is the shifted self-layer on the new packet:

```text
b(y)-deg_{R\T}(y)+deg_Y(y)-deg_X(y)=kappa        [MOD 4]        (y in Y).
```

Thus every failed balanced swap is blocked either by incoming affine target avoidance or by shifted
self-layer failure after the target is hit.  This is exactly the same dichotomy as in the atom-quotient
repair equations, now written at the raw first-bit labeled co-cut level.

For one-swaps this becomes a missing-template statement.  Fix `x in T` and `kappa in Z/4Z`, and define on
`T\{x}` the adjusted color

```text
phi_x(v)=psi_T(v)-1_{vx}        [MOD 4].
```

An incoming vertex `y` can flatten `T\{x}` to residue `kappa` only if

```text
1_{vy}=kappa-phi_x(v)        [MOD 4]        (v in T\{x}),
```

so the right-hand side must lie in `{0,1}` for every `v`.  Equivalently, `phi_x` uses only the two adjacent
values `{kappa,kappa-1}`.  When this binary condition holds, the required trace is forced:

```text
N(y) cap (T\{x}) = {v : phi_x(v)=kappa-1},
```

and the new-vertex scalar condition is

```text
b(y)-deg_{R\T}(y)-1_{xy}=kappa        [MOD 4].
```

Thus a terminal labeled residual has the following one-swap normal form: for every `T`, `x`, and `kappa`,
either the adjusted coloring `phi_x` is not contained in an adjacent residue pair, or the unique binary
trace template above has no outside vertex satisfying the scalar condition.  This is the raw
principal-submatrix version of row-promotion failure.

For two-swaps the corresponding target is a pair-template.  Fix `X={x_1,x_2} subset T` and `kappa`.  On
`T\X`, put

```text
theta_X(v)=kappa-psi_T(v)+1_{vx_1}+1_{vx_2}        [MOD 4].
```

An incoming pair `Y={y_1,y_2}` can hit the old-vertex target only if `theta_X(v)` lies in `{0,1,2}` for
every `v`, because it must equal `1_{vy_1}+1_{vy_2}`.  When this holds, the pair must realize a prescribed
three-way partition of `T\X`: no hit, exactly one hit, or two hits.  After that incoming target is met, the
new-vertex equations are

```text
b(y_i)-deg_{R\T}(y_i)+1_{y_i y_{3-i}}-1_{y_i x_1}-1_{y_i x_2}=kappa
        [MOD 4]        (i=1,2).
```

Thus the first non-row-promotion repair is an opposite-pair/no-split template: either the required
three-way trace partition has no outside pair, or every pair realizing it fails one of the two shifted
self-layer scalar equations.

For `r`-swaps the same template is finite.  If `X subset T` has size `r`, define

```text
Theta_X(v)=kappa-psi_T(v)+deg_X(v)        [MOD 4]        (v in T\X).
```

An incoming `r`-packet can hit the old-vertex target only if every `Theta_X(v)` has a representative in
`{0,1,...,r}` congruent modulo `4`; this prescribed representative is the number of incoming vertices
adjacent to `v`.  Thus `Theta_X` prescribes a bounded multiplicity partition of the old vertices.  After
that partition is realized, the shifted self-layer equations on the incoming packet are

```text
b(y)-deg_{R\T}(y)+deg_Y(y)-deg_X(y)=kappa        [MOD 4]        (y in Y).
```

So, for each fixed outgoing packet `X`, the first-bit residual is a finite bounded-target packet problem:
either the old-vertex multiplicity template is unrealizable by an outside packet of size `|X|`, or every
realization fails the shifted self-layer.  This is the raw labeled analogue of the finite atom-quotient
packet repair branch.

The first universally viable outgoing size is `3`.  For `|X|=3`, every residue modulo `4` has a
representative in `{0,1,2,3}`, so the old-vertex multiplicity template is always arithmetically legal:
each old vertex asks to see exactly `0`, `1`, `2`, or `3` of the incoming vertices.  Hence, whenever
`|R\T|>=3`, a terminal residual must block every ternary repair by one of two concrete mechanisms:

```text
ternary target failure: no outside triple realizes the prescribed 0/1/2/3 trace-counts on T\X;
ternary self-layer failure: every realizing triple fails one of the three shifted scalar equations.
```

Thus the large-outside branch of the first-bit residual is a ternary packet-realization problem.  If this
branch is unavailable for a larger residue class `R`, then every `(m+1)`-set `T subset R` has
`|R\T|<=2`, so

```text
|R| <= m+3.
```

Since the Gallai core has `|J|>2m` and `R` is the larger of the two `0/2` classes, the complementary
near-threshold branch has both residue classes squeezed into a bounded window around `m`:

```text
m-2 <= |C| <= |R| <= m+3.
```

Consequently the first-bit selector splits into a large-outside ternary target/self-layer branch and a
near-threshold two-residue branch with only bounded surplus over the critical size.

The large-outside ternary branch has a finite obstruction certificate.  Fix `T`, `X={x_1,x_2,x_3}`,
`S=T\X`, and `kappa`, and let

```text
h(v)=kappa-psi_T(v)+deg_X(v)        [MOD 4],
```

represented in `{0,1,2,3}`.  On the outside set `O=R\T`, form the realization 3-graph `H_h` whose edges
are triples `Y` satisfying

```text
deg_Y(v)=h(v)        for every v in S.
```

The scalar-good subgraph consists of those `Y in H_h` for which the three shifted self-layer equations
hold.  Terminality says this scalar-good subgraph is empty for every `T,X,kappa`.  If already `H_h` is
empty, choose a coordinate-minimal `P subset S` on which no outside triple realizes `h|_P`; then every
`p in P` is essential, meaning some outside triple realizes `h` on `P\{p}` and fails only at `p` inside
`P`.  If `H_h` is nonempty, terminality is purely a scalar obstruction: every target-realizing triple is
covered by at least one of the three failed shifted self-layer equations.  Thus the ternary branch reduces
to either an essential-coordinate 3-trace avoidance certificate or a scalar-killed target-realization
hypergraph.

For small minimal `P` this certificate is completely explicit.  If `|P|=1`, target failure says that the
outside neighborhood or outside non-neighborhood of that single old vertex is too small to supply the
requested count `0`, `1`, `2`, or `3`.  If `|P|=2`, it is a four-chamber transportation failure: the
outside vertices are split by their two-bit traces, and no choice of three vertices has the prescribed two
coordinate margins.  If `|P|=3`, it is the first genuine cube obstruction: the eight trace corners admit no
three-point multiset with the prescribed ternary margins.  Thus the old host-frontier names reappear here
as the size `1`, `2`, and `3` minimal target certificates: row extremity, pair-chamber separation, and
one-corner ternary lift.

In the saturated graph proof these three local certificates are the already-closed row-promotion,
opposite-pair/no-split, and silent-edge/one-corner alternatives.  Therefore an irreducible large-outside
target-avoidance obstruction cannot stop at `|P|<=3`: after importing the saturated local closures, it must
either have an essential coordinate certificate of size at least `4`, or have nonempty target realization
with the scalar-good 3-graph empty.

The scalar-good condition is itself a three-vertex graphicality test.  For an outside vertex `y`, after the
old target is fixed its shifted scalar equation is equivalent to prescribing

```text
deg_Y(y)=kappa-b(y)+deg_{R\T}(y)+deg_X(y)        [MOD 4].
```

Since `deg_Y(y)` is the internal degree of `y` inside the incoming triple, it must have a representative in
`{0,1,2}`; residue `3` kills every target-realizing triple containing `y`.  When the three incoming vertices
all have representatives in `{0,1,2}`, the requested internal degree sequence must be one of the four
graphical patterns on three vertices:

```text
000,        110,        211,        222.
```

These correspond to the empty graph, one edge, a two-edge path, and a triangle.  Thus scalar-good
hypergraph emptiness splits into a residue-`3` endpoint obstruction or a missing internal graph-pattern
obstruction over the target-realizing triples.

Equivalently, for a target-realizing triple `Y={y_1,y_2,y_3}`, let `d_i` be the requested representative in
`{0,1,2}` for `deg_Y(y_i)`.  The scalar test is the following finite table:

```text
000: no internal edges among Y;
110: the unique edge is between the two vertices requesting 1;
211: the vertex requesting 2 is adjacent to both vertices requesting 1, and those two are nonadjacent;
222: all three internal edges are present.
```

Any other requested triple, including any endpoint residue `3`, is non-graphical.  Hence scalar-good
emptiness is a finite pattern-mismatch assertion over the target-realizing triples.

The target-avoidance half can be written as a capacitated 3-sum cube.  For a coordinate-minimal
certificate `P`, let `M_P` be the multiset of outside trace columns

```text
a(y)=(1_{vy})_{v in P} in {0,1}^P        (y in O).
```

The target is the vector `h|_P in {0,1,2,3}^P`.  An outside triple realizes the old target on `P` exactly
when `h|_P` is a capacity-respecting sum of three distinct columns of `M_P`.  Thus target failure is

```text
h|_P notin M_P + M_P + M_P        (with vertex capacities),
```

while coordinate minimality says that every coordinate projection of `h|_P` is such a capacitated
3-sum.  Since `P` is inclusion-minimal, in fact every proper coordinate shadow `Q proper_subset P` is
feasible: some outside triple realizes `h|_Q`.  Equivalently, for each `p in P` there is a single-defect
outside triple realizing all coordinates of `P\{p}` and missing only the `p`-coordinate.  After the
saturated size-`<=3` closures, the irreducible large-outside target branch is precisely a critical
capacitated 3-sum cube of dimension at least `4`, all of whose proper shadows are feasible.

This cube has a coordinate-switching normal form.  In a fixed coordinate `p`, replacing every trace bit
`a_p` by `1-a_p` changes the target entry from `h_p` to `3-h_p` and preserves triple realizability.
Switch all coordinates with target `2` or `3`.  Then

```text
h_p in {0,1}        for every p in P.
```

In this switched form a target-realizing triple is exactly three outside columns which all vanish on the
zero-target coordinates, and whose supports on the one-target coordinates are pairwise disjoint and cover
those coordinates.  Thus the irreducible target-avoidance branch is a critical capacitated three-column
disjoint-cover problem, with all proper coordinate shadows coverable.

Equivalently, write

```text
Z={p:h_p=0},        A={p:h_p=1}.
```

Only outside columns vanishing on `Z` are admissible.  Restrict each admissible column to its support in
`A`; then target realization is exactly a choice of three distinct admissible columns whose supports form a
disjoint cover of `A`.  Full target failure says no such three-column partition of `A` exists.  Minimality
has two parts: deleting any active coordinate makes such a partition possible, while deleting any zero
coordinate relaxes the admissible-column filter enough to make a partition possible.  Thus the target
branch is a critical filtered three-cover instance.

The critical filtered cover has explicit defect witnesses.  For each active coordinate `a in A`, choose a
triple witnessing feasibility after deleting `a`.  It partitions `A\{a}` and avoids `Z`; because a full
partition of `A` is forbidden, its multiplicity at `a` is not `1`.  Hence every active coordinate has one
of three near-cover witnesses:

```text
hole:              multiplicity at a is 0;
double collision:  multiplicity at a is 2;
triple collision:  multiplicity at a is 3.
```

For each zero coordinate `z in Z`, choose a triple witnessing feasibility after deleting `z`.  It partitions
`A` and avoids `Z\{z}`; since no admissible partition exists, at least one of its three columns hits `z`.
Thus every zero coordinate has a filter-breach witness of multiplicity `1`, `2`, or `3` at `z`.  This is
the exact remaining target-avoidance normal form after all size-`<=3` saturated local closures.

It is useful to separate active dimension from filter dimension.  If `|A|<=3`, the disjoint-cover side has
only the finite partition types of a set of size at most three; any obstruction is then purely that the
zero-filtered admissible family lacks enough columns of the required small supports.  Thus the genuinely
new target-avoidance branch has either `|A|>=4`, or is a zero-filter capacity obstruction: every relaxed
filter `Z\{z}` supplies the required small-support partition, but the full filter `Z` does not.  In
particular, the all-zero target `A=emptyset` is exactly the statement that fewer than three outside columns
vanish on all of `Z`, while every one-coordinate relaxation has three such columns.

For fixed `A,Z`, the small-active capacity condition is finite.  Let

```text
c_Z(B)=#{y in O : a(y) cap A = B and a(y) cap Z = emptyset}        (B subset A).
```

A filtered three-cover exists iff there are three pairwise disjoint subsets `B_1,B_2,B_3` with union `A`
such that, for each support value `B`, the number of indices `i` with `B_i=B` is at most `c_Z(B)`.  Hence
failure is witnessed by a deficient support in every ordered three-block partition of `A`.  When a zero
coordinate `z` is deleted, the same test uses `c_{Z\{z}}`; minimality says at least one formerly deficient
partition becomes capacity-feasible for each such `z`.

For `|A|<=3` this criterion is the following table:

```text
A=empty:
    c(empty) >= 3.

A={a}:
    c({a}) >= 1 and c(empty) >= 2.

A={a,b}:
    either c({a,b}) >= 1 and c(empty) >= 2,
    or     c({a}) >= 1, c({b}) >= 1, and c(empty) >= 1.

A={a,b,c}:
    either c({a,b,c}) >= 1 and c(empty) >= 2,
    or     c(P) >= 1, c(A\P) >= 1, and c(empty) >= 1 for some pair P subset A,
    or     c({a}) >= 1, c({b}) >= 1, and c({c}) >= 1.
```

Thus every small-active zero-filter obstruction is a failure of one of these displayed alternatives for
`c_Z`, while criticality says the corresponding table succeeds for each relaxed filter `c_{Z\{z}}`.

The effect of relaxing one zero coordinate is also explicit.  Let

```text
p_z(B)=#{y in O : a(y) cap A = B and a(y) cap Z = {z}}.
```

Then

```text
c_{Z\{z}}(B)=c_Z(B)+p_z(B).
```

So every zero-coordinate criticality witness is supported by columns private to that zero coordinate.  In
the all-zero case this says: if `q=c_Z(empty)<=2`, then each `z in Z` has at least `3-q` outside columns
whose trace on `Z` is exactly `{z}`.  More generally, for `|A|<=3`, each relaxed cover must repair one of
the deficient displayed support alternatives using private `p_z(B)` capacity.

The near-threshold branch is finite on the large residue class.  Write `|R|=m+s`, where
`1<=s<=3`.  Any selector contained in `R` and larger than `m` has the form `R\D` with
`|D|<=s-1<=2`.  The labeled deletion equation says that such a selector exists iff

```text
b(v)-deg_D(v)        [MOD 4]
```

is constant on `R\D`.  Therefore terminality in the near-threshold branch is exactly the finite list:

```text
s=1:  b is nonconstant on R;
s=2:  for every x in R, b(v)-1_{vx} is nonconstant on R\{x};
s=3:  for every {x1,x2} subset R, b(v)-1_{vx1}-1_{vx2} is nonconstant on R\{x1,x2}.
```

These are the deletion-side versions of the one- and two-swap templates.  Thus the first-bit residual now
has only two forms: a large-outside ternary packet problem, or a bounded near-threshold deletion-template
problem on a residue class of size `m+1`, `m+2`, or `m+3`.

The whole Gallai core has an equally useful symmetric deletion form, which keeps mixed selectors visible.
Let `rho` be the residue of `deg_J` on `R` and put

```text
epsilon(v)=0  for v in R,
epsilon(v)=2  for v in C.
```

Thus `deg_J(v)=rho+epsilon(v) mod 4` for every `v in J`.  For any `W=J\D` and `v in W`,

```text
deg_W(v)=rho+epsilon(v)-deg_D(v)        [MOD 4].
```

Consequently `W` is a selector iff `epsilon(v)-deg_D(v)` is constant on `W`.  The signed one-class label
above is exactly the restriction of this full equation to `W subset R`: then `D=C union D_R`, and
`epsilon(v)-deg_D(v)=-deg_C(v)-deg_{D_R}(v)=b(v)-deg_{D_R}(v)`.  Hence the near-threshold branch is not an
arbitrary labeled graph on `R`; it is the one-class shadow of a two-level deletion equation on
`J=R disjoint_union C`.

The same restriction applies on the smaller residue class whenever it is also above threshold.  If
`|C|=m+t` with `t>0`, define

```text
b_C(v)=2-deg_R(v)        [MOD 4]        (v in C).
```

Then a selector contained in `C` and larger than `m` is `C\E` with `|E|<=t-1`, and it exists iff
`b_C(v)-deg_E(v)` is constant on `C\E`.  Thus in the near-threshold branch terminality is two-sided:
both residue classes that exceed `m` obey the same finite deletion-template list, with surplus at most
three on each side.

For a genuinely mixed selector, write

```text
W=(R\D_R) union (C\D_C),        D=D_R union D_C.
```

The full equation says that, for some residue `alpha`,

```text
deg_D(v)=alpha      [MOD 4]        (v in R\D_R),
deg_D(v)=alpha+2    [MOD 4]        (v in C\D_C).
```

Thus mixed repair is a two-level deletion target: the retained vertices must see the deleted set in two
constant residues separated by exactly `2`, according to their Gallai residue class.  The pure `R` and
pure `C` deletion templates are just the boundary cases `D_C=C` and `D_R=R`.

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
HasParityToModFourLoss64FixedWitnessLift, or an equivalent parity-to-mod-four fixed-loss theorem;
the stronger q >= 4 terminal-cascade bridge, which is not needed for terminal regularization.
```

What is not used:

```text
equivalence with arbitrary nonminimal extrinsic path choices.
the original path-only Theorem G / path-saturation comparison, which is a stronger bookkeeping statement
than the graph-intrinsic saturated terminal proof.
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
