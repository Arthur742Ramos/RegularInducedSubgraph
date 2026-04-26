# Current roadmap

This note now serves as an archival record of the shortest path from the modular-control
formalization to the last open work.

## Q-marker localization re-audit correction

The q-marker localization proof below overclaimed.  The low-set update and low-set congruence prove
that any surviving marked two-class quartet has a shared-slack marker `R` with `|R|` a positive
multiple of `q`.  If no outside vertex splits `R`, then `R` is a proper module in the prime shell and
the obstruction is impossible.

At this earlier audit stage, the splitter case was incomplete.  Feeding a splitter into the omni-saturated dirty-split theorem gives
a preserved-side branch, a closed Section-`40` / marked-add exit, or a fully skew positive AND square.
The preserved-side branch would give a proper submarker, contradicting marker minimality.  But in the
fully skew branch the dirty-split theorem only collapses the **active carrier** to a binary crossing
component.  It does not prove that the shared-slack marker `R` is supported on only those two active
vertices.  Thus the asserted bound `|R'|<=2` is unjustified: a fully skew q-marker may still have `q`
or more slack rows all spending the same two repair directions.

The theorem to prove is **q-marker carrier/marker coupling**: in the fully skew splitter branch,
prove that the shared-slack marker restricts to a proper first-return submarker, or else that the
marker is constant to all outside vertices and hence a prime-shell module, or else extract a closed
Section-`40` / marked-add / completer exit.  The final split-quotient and transport argument below
closes this theorem for the tracked endpoint.

The current sharpening is that all other visible roots feed back into this theorem.  The add/add
`q-2` cross-split quotient has no remaining static selection except the `U+k(H)` clique and the
proper-divisor equal-clique bypass; after those are removed, packaged `A`/component splits are sub-`q`
and packaged opposite `U` defects are killed by `40.16`.  The fixed peeled-package/common-shadow root
has only one unfixed coordinate family, binary pair-status on the forced median fiber; a positive
`0001` pair-status coordinate is not a literal singleton but promotes to a shared-slack marker
`R` with `|R|=0 [MOD q]`.  Thus cross-split packet-primality, common-shadow, and successor-side
positive AND all reduce to the same q-marker carrier/marker coupling problem.

The latest sharpening removes two false blockers from this endpoint.  First, a frozen q-divisible
same-trace marker is closed by the modular-cluster lemma: a marker-internal `P_3` is the Section-`40`
roof false-clone template, while a `P_3`-free marker is a union of congruent-size cliques and contains
a regular induced `q`-set.  Second, an exact high-null splitter with no second splitter is closed: the
one-excess graph either has an isolated-neighbor deletion to a regular `q`-set, or forces the same
roof false-clone `P_3`; the singleton-lift half of exact two-splitter routing is the already closed
`U_1`/`Sigma_rf` roof gate.  At that stage the endpoint was therefore narrower still: the
marker-splitting zero-sum atom, appearing either as a non-frozen simultaneous wall or as exact-size
two independent marker cuts.

The split-quotient arithmetic inside that atom is now fully exhausted.  In the extremal add/add
`q-2` form, any selection using the residual pair `U` must use a single compensator component large
enough to contain the required `k(H)` clique; spreading the selection across several smaller
components is impossible by the residual-row degree equation.  Selections avoiding `U` are exactly the
proper-divisor equal-clique bypasses.  After these finite selections, same-trace component splits, and
sub-`q` raw relations are removed, the survivor has a product firewall: provenance data cut only the
residual-pair/compensator coordinate, while ambient primeness cuts the large marker packet only through
high-error breakers.  The ordered routing is forced by the sub-`q` transport trap: any failure to
promote a high-error ambient packet breaker to the boundary family creates a dirty shared-slack marker
inside one side of a proper packet, contradicting the low-set congruence.  Thus the product firewall
has no survivor.

There is a concrete reason this coupling is not formal.  At the incidence-table level, take
`q=4` and a marker

- `R={a_1,b_1,a_2,b_2}`

with active binary components `{a_1,b_1}` and `{a_2,b_2}`.  Let the quartet vertices satisfy the
marked two-class pattern:

- `d,e` miss all of `R`;
- `x,y` see all of `R`.

Now add two outside splitter rows:

- `z_1` sees `a_1,a_2` and misses `b_1,b_2`;
- `z_2` sees `a_1,b_2` and misses `b_1,a_2`.

Each splitter separates every active binary component, so this is fully skew on the active carrier.
But the shared-slack marker still has size `|R|=q`, not `<q`; the low-set congruence does not
contradict it.  This is not asserted to be a global counterexample, but it shows the attempted
implication

- "fully skew binary carrier" `=>` "sub-`q` marker"

is false without an additional carrier/marker coupling theorem.

The same barrier scales.  For any even `q`, take

- `R={a_i,b_i : 1<=i<=q/2}`;
- active binary components `{a_i,b_i}`;
- `d,e` missing all of `R` and `x,y` seeing all of `R`;
- for each sign vector `s in {0,1}^{q/2}`, an outside row `z_s` with
  `z_s~a_i` iff `s_i=1` and `z_s~b_i` iff `s_i=0`.

Every `z_s` is fully skew on every active binary component, while the family `{z_s}` separates every
pair of vertices of `R`.  Thus primeness/module pressure alone can distinguish all marker rows without
ever producing a preserved-side marker.  The low-set congruence sees only `|R|=q`, so this table
satisfies exactly the constraints currently written.  A real proof must therefore use structure not
encoded in the carrier split table itself.

This gives a no-go audit for the present proof package.  Any argument that uses only

- the exact low-set congruence `|R|=0 [MOD q]`;
- marker minimality under preserved-side first returns;
- prime-shell module pressure against unsplit marker rows;
- binary collapse of the active crossing carrier;

cannot eliminate the q-marker endpoint.  The table above satisfies all four bullets and still
contains a nonmodule marker of size exactly `q`.

Nor can the degree-coupling route use only the anchored near-regular residue equations.  For even
`q>=4`, realize the miss/miss table inside `T` as follows.  Put

- `L=R union {d,e}` with `|R|=q`;
- make `R` a perfect matching and add the edge `de`;
- put no edges from `R` to `{d,e}`.

Then every vertex of `L` has internal degree `1`.  Taking `delta=2`, this is exactly
`delta-1 [MOD q]`, and `|L|=q+2 congruent 2=delta [MOD q]`.  Add a disjoint cycle on
`q^2-q-3` vertices as the high part `B`; each new vertex has degree `2=delta [MOD q]`, so
`|T|=q^2-1` and the anchored near-regular residue conditions hold.  The outside vertices `x,y` are
the usual one-defect repairs with `N_T(x)=L\{d}` and `N_T(y)=L\{e}`, while the fully skew splitters
`z_s` may be attached to `R` by the sign-vector table above and kept anticomplete to the filler.

Thus even the exact `q^2-1` near-regular residue bookkeeping does not by itself forbid a size-`q`
fully skew marker.  The missing input must use either admissibility of the splitter as a repair
boundary, or the first-return history that should force a side marker; static degree residues are not
enough.

This construction is only a residue-level no-go model.  It is not claimed to survive the full
Section-`40` catalogue or the first-return admissibility requirements; it only proves that those
additional structures, not the low/high degree congruences alone, must do the remaining work.

It also shows that "fully skew" alone is much weaker than admissibility.  In the same model, a
sign-vector splitter `z_s` sees exactly one endpoint of each active pair `{a_i,b_i}` but, relative to
`L=R union {d,e}` and `B=T\L`, it misses `q/2+2` low vertices and sees no high vertices.  Thus its
one-error distance is `epsilon(z_s)=q/2+2`, not `0` or `1`; it is not a completer and not a
singleton repair/reanchor vertex.  Therefore the admissible-splitter route cannot be a theorem about
arbitrary fully skew outside rows.  It must use the splitter's provenance as a first failed row,
transverse breaker, or repair-boundary row.

The weighted-house/seed-packaging bypass has the same obstruction.  In the miss/miss case, each
single `r in R` makes the five vertices `{d,e,x,y,r}` a house seed, and in the add/add case the
analogous seeds are `P_5/C_5`.  But packaging the whole marker as one roof/seed bag gives a bag of
size `q`, which is outside the prime weighted-quotient reduction where every bag has size `<q` and is
also invisible modulo `q`.  Splitting the marker into smaller seed bags returns to the submarker
problem, and the low-set congruence forbids any genuine first-return marker of size `<q`.  Thus
Section `40.11`--`40.12` cannot be invoked merely from the existence of the q-marker seed family.

Consequently the only sound remaining closure routes are:

1. prove a **provenance-admissible fully skew splitter** theorem, showing that a fully skew row that
   arises as the first failed row / transverse breaker in the first-return process is a valid
   repair/reanchor boundary and therefore falls to the crossing-separator collapse / Section-`40`
   catalogue;
2. prove a **first-return side-marker** theorem, showing that one of `R cap N(z)` or
   `R \ N(z)` carries a new marked two-class first-return square even when no original active pair is
   preserved on that side.

A history-sensitive degree argument would still have to produce one of these two outcomes: either the
fully skew splitter passes the repair interval tests, or the first-return history turns one side of the
split into a genuine smaller marker.  No such input is present in the notes below.

There is an extra selection issue in the first route.  The no-split case uses primeness to obtain
some outside vertex that distinguishes two rows of `R`; primeness alone does not say that this vertex
is a first failed row, transverse breaker, or repair-boundary candidate.  The sign-vector model shows
why this matters: arbitrary prime splitters can be fully skew and still have large `epsilon`.  Thus an
admissibility proof must first show **provenance selection**: if `R` is not a module, then some
splitter of `R` can be chosen from the first-return failed-row / transverse-breaker family.  Only after
that selection can one try to prove interval admissibility.

In particular, the needed side-marker statement is not the weak assertion that `R cap N(z)` and
`R\N(z)` are nonempty.  In the fully skew sign-vector model they are nonempty but contain no preserved
active binary component.  The required theorem must say that the **low-set update itself** localizes:
after transporting to the first-return boundary determined by `z`, one side is again the complete
shared-slack set for a marked two-class quartet.  Only then does the congruence apply to give
`0<|R_i|<|R|` and contradict minimality.

This is the q-marker form of the transverse-breaker support-decrease theorem below.  A provenance
splitter that fails the repair interval tests produces a first failed row `u`; to close the proof one
must show that `u` is not merely another fully skew row, but a breaker whose unfrozen support is
strictly smaller.  In the q-marker language, that strict support decrease is exactly the assertion
that one side of `R cap N(u)` / `R\N(u)` is the complete shared-slack marker of a new first-return
quartet.  Thus the two visible routes are one final atom:

> **q-marker provenance/support-decrease theorem.** In the fully skew first-return q-marker endpoint,
> either a provenance splitter is interval-admissible, or its first failed row carries a genuine
> smaller first-return shared-slack marker.

The phrase "carries" hides two separate requirements.  First, the failed degree row must transport to
a valid outside breaker/candidate in the same first-return frame; a row of `T` that merely witnesses
interval failure is not automatically a new repair-boundary vertex.  Second, after that transport, its
support must be strictly smaller in the low-set-update sense above.  The current notes prove neither
row-to-breaker transport nor strict q-marker support decrease in the fully skew case.

There is also no canonical "first" failed row from the static data.  In the sign-vector model, trying
to use a nonadmissible splitter as a repair can fail simultaneously on many low rows.  Selecting one
of them requires the ordered first-return / wall-crossing structure of the repair path; an unordered
set of failed interval rows gives no descent.  Thus the final atom is really an ordered
first-return statement, not a static interval-counting statement.

Even ordered first failure is not by itself enough.  The first failed wall may define only an initial
prefix or a singleton failed row; the low-set congruence applies only when the whole selected support
is the shared-slack marker of a valid marked two-class quartet.  Therefore support decrease must be
**marker-complete**: the transported failed row must determine a side whose every row, and no outside
row, is exactly the slack set spent by the new two-defect square.  A mere smaller failed support does
not contradict q-marker minimality.

It must also be **marker-internal**.  If the first interval failure for a provenance splitter occurs
at one of the old deleted defects `d,e`, at an inserted-root degree test, or at a filler row of the
peeled set, then the failure may still be a legitimate obstruction but it is not a smaller q-marker.
Those cases must be routed to Section `40`, marked-add, or completer exits before the q-marker
minimality argument is available.  Thus the support-decrease theorem has three ordered clauses:

1. **provenance selection:** the splitter of a nonmodule q-marker can be chosen from the ordered
   first-return failed-row / transverse-breaker family;
2. **local non-marker exit:** if the ordered first failure is at an old defect, inserted-root test, or
   filler row, it localizes to Section `40`, marked-add, or a completer;
3. **marker-complete descent:** if the ordered first failure is marker-internal, it transports to a
   valid breaker whose support is exactly a smaller shared-slack marker for a new first-return marked
   two-class quartet.

The first subclaim is not a consequence of primeness plus the q-marker table.  Abstractly, take the
size-`q` sign-vector marker table above, declare the first-return/provenance family to consist only of
rows constant on `R`, and add one extra outside row `z` that separates two marker rows.  The marker is
not a module in the ambient prime-shell sense, but no provenance row splits it.  This is not a claimed
graph counterexample; it is a dependency witness showing that provenance selection must use a routing
theorem from arbitrary prime distinguishers to repair-boundary rows.  Primeness alone cannot supply
it.

This also blocks a tempting misuse of omni-saturation.  The minimal-carrier saturation below ranges
over outside rows whose traces are already valid dirty-row / repair-boundary tests for the same
obstruction category.  It does not range over an arbitrary prime-shell distinguisher of `R`.  Thus one
may add an ambient splitter `z` with a nonconstant sign vector on `R` while every valid provenance row
is constant on `R`; the carrier remains saturated relative to the valid row family, but `R` is still
not an ambient module.  A successful proof needs an **ambient-to-provenance routing theorem**:

> every ambient splitter of a first-return q-marker either gives a Section-`40`, marked-add, or
> completer exit, or produces a valid first-return/provenance row that is nonconstant on the marker.

Without this routing theorem, the no-split module argument and the omni-saturated carrier argument do
not meet.

The second clause, by contrast, is local bookkeeping once an ordered provenance splitter has already
been selected.  A first failure at an inserted-root degree test is exactly the mixed miss/add or wrong
`xy` case in the five-vertex table below, hence one of the local marked/root-edge failures already
removed by the marked-add catalogue.  A first failure at an old deleted defect is either the same-defect
turn closed by the same-trace / false-clone argument, or one of the marked add/miss root-edge tests in
the same catalogue.  A first failure on a filler row outside the proposed marker contradicts the
assumption that the double corner fails only along the shared-slack set; after marking that row it is
one of the explicit marked miss / low-old / `B_1(D)` / congruence failures, unless it is already a
completer.  Thus **local non-marker exit is closed conditional on having the ordered provenance
splitter**.  It does not supply provenance selection and it does not prove marker-complete descent.

The third clause is formal only for a stronger notion of provenance.  Call a splitter
**square-provenance** if it is not merely a row in the failed-row family, but the boundary row of an
ordered first-return singleton square with its whole wall-failure set recorded.  For such a splitter
`z`, after the non-marker exits above are removed, the full failure set

- `F(z) subseteq R`

is marker-internal.  The same singleton low-set update used below applies in the transported
first-return square: rows of `F(z)` are exactly the retained rows whose one-unit slack is spent in both
singleton corners, and rows of `R\F(z)` are not spent in that transported square.  Hence `F(z)` is not
just a prefix or a chosen failed row; it is the complete shared-slack marker of the new marked
two-class quartet.  If `z` is nonconstant on the old marker, then

- `0 < |F(z)| < |R|`.

The low-set congruence applies to this new first-return marker and gives `|F(z)| congruent 0 [MOD q]`,
contradicting the minimal choice of `R`.  Therefore a nonadmissible square-provenance splitter cannot
survive.  The open selection theorem must consequently produce this square-provenance data; weak
row-provenance alone is not enough.

There is one genuine improvement to the selection problem **after** an exact size-`q` marker has been
isolated.  Ambient primeness is not the only way to obtain a splitter.  If `|R|=q` and every vertex of
the peeled state `T\R` is constant on `R`, then each `r in R` has

- `deg_T(r) = deg_R(r) + c`

with the same outside contribution `c`.  Since every `r in R` is a low row,
`deg_T(r) congruent delta-1 [MOD q]`; hence all `deg_R(r)` are congruent modulo `q`.  But
`0 <= deg_R(r) <= q-1`, so the internal degrees in `G[R]` are equal.  Thus `R` itself is a regular
induced `q`-vertex subgraph, impossible in a counterexample.  Therefore an irreducible exact
q-marker has a **state-internal splitter** in `T\R`.

This narrows the last blocker.  The abstract ambient splitter firewall still shows that arbitrary
prime distinguishers need not be provenance rows, but at the exact q-marker endpoint a counterexample
must already contain a splitter inside the peeled near-regular state.  The remaining theorem is now
state-internal-to-square-provenance routing: a filler/high/low row of `T\R` that splits `R` must either
be a local Section-`40` / marked-add / completer exit, or transport to a valid first-return square
boundary whose full wall-failure set is a proper marker.

This internal-splitter reduction is still not a proof.  Static degree balancing can create such a row
without giving it square provenance.  For instance at `q=4`, let `R={a,b,c,d}` with only the edge
`ab` inside `R`, and add a filler row `v` adjacent to `c,d` and not to `a,b`.  Then the contribution of
`v` makes all four rows have the same degree in `R union {v}`, while `v` splits the marker.  This
local table only illustrates the dependency: the final theorem must use first-return geometry to turn
a state-internal degree-balancing splitter into a repair-boundary square, or else localize it.  Degree
balancing alone does not do so.

There is also a hidden exactness requirement here.  The low-set update has proved only
`|R| congruent 0 [MOD q]`, not `|R|=q`.  If `|R|=m q` with `m>1` and `T\R` is constant on `R`, then the
same calculation gives only that the internal degrees in `G[R]` are congruent modulo `q`; they may
differ by multiples of `q`.  Since the induced degrees in `R` are no longer confined to an interval of
width `<q`, the modular-collapse lemma does not immediately produce a regular `q`-set.  Thus the true
last blocker has two layers:

1. **large-marker reduction:** either extract an exact size-`q` first-return marker from a larger
   positive multiple of `q`, or prove a regular `q`-set directly from the congruent-degree marker block;
2. **exact-marker routing:** once `|R|=q`, route a state-internal splitter to a local exit or to
   square-provenance.

The natural large-marker route is an ordered-prefix theorem.  Along a genuine first-return repair
path, let `F_t` be the rows of the final marker whose slack has become double-spent by the first `t`
wall crossings.  If every marker-internal prefix `F_t` were itself the complete shared-slack set of a
transported first-return square, then the low-set congruence would force every nonempty `F_t` to have
size `0 [MOD q]`; the first nonempty such prefix would have size exactly `q` unless a single wall
jumps over `q`.  Thus the missing large-marker theorem is a **no-q-jump / prefix-completeness**
statement:

> a first-return wall cannot introduce `q` or more new marker rows at once without either producing a
> regular induced `q`-set inside that simultaneous wall block, or localizing to Section `40` /
> marked-add / completer, or exposing a smaller complete first-return marker.

Without this no-jump theorem, a marker of size `m q` can remain a single complete wall-failure set,
and the exact-marker routing argument cannot be applied.

The no-jump theorem itself has a sharper normal form.  Suppose `P` is the last complete prefix with
`|P|<q`, and a simultaneous wall block `B` makes `|P union B|>=q`.  Choose `B_0 subseteq B` with
`|P union B_0|=q`.  If any leftover row of `B\B_0` has a different residual trace from the chosen
rows after the square frame and `P union B_0` are marked, then it is a marker-internal splitter and the
square-provenance descent applies.  If all leftover rows have the same residual trace, then they are in
the same Section-`40` same-trace / false-clone situation as the chosen slack rows unless their internal
adjacency inside `B` supplies such a splitter.  Therefore the only remaining large-marker jump is a
simultaneous wall block that is internally mixed enough to avoid Section `40`, but not mixed in a way
that yields a smaller complete marker.  This is now the precise large-marker obstruction.

There is now one noncircular large-marker reduction in the frozen same-trace case.  Let `F` be a
same-trace marker block with `|F|=m q` and suppose every vertex outside `F` is constant on `F`.  Then
the internal degrees in `G[F]` are all congruent modulo `q`.  If `G[F]` contains an induced `P_3`, that
`P_3` is the same roof false-clone Section-`40` template: in the miss/miss orientation the marked
quartet is `d-e-x-y-d` and marker rows have trace `{x,y}`, while the add/add orientation is its
complement.
If `G[F]` contains no induced `P_3`, then `G[F]` is a disjoint union of cliques.  The congruent-degree
condition says all clique sizes are congruent modulo `q`.  A clique of size at least `q` contains a
regular induced `K_q`; otherwise all clique sizes are a common size `s<q`.  Since the total size is
`m q`, if `g=gcd(s,q)`, the number of cliques is divisible by `q/g`; choosing `g` vertices from each of
`q/g` cliques gives a regular induced `q`-set.  Thus a frozen large marker is closed.

This avoids importing the positive-cost external-block bridge for the frozen fiber.  The remaining
large-marker obstruction is therefore narrower than the abstract fixed-modulus extraction problem:
the simultaneous first-return wall block must be non-frozen in the provenance sense.  After an exact
`q`-prefix is selected, the leftover rows must both avoid same-trace `P_3` localization and prevent the
outside contribution to that prefix from becoming frozen.  The large-marker reduction must still use
first-return wall order / marker provenance for this non-frozen simultaneous block; the downstream
positive-cost external-block bridge cannot be imported here.

Equivalently, refine a surviving large marker `R` by the complete outside trace on the current peeled
state and marked frame.  On each fiber the outside contribution is frozen.  Therefore any fiber whose
size is `0 [MOD q]` is closed by the frozen-fiber argument above.  Also, any proper union of fibers
whose total size is `0 [MOD q]` would close if it were the complete shared-slack set of a transported
first-return square, by the same marker-minimality congruence already used for preserved sides.  Hence
an irreducible non-frozen large marker has the following zero-sum-atom form:

- every outside-trace fiber has nonzero size modulo `q`;
- no proper first-return-complete union of fibers has total size `0 [MOD q]`;
- the full set of fibers has total size `0 [MOD q]`.

The no-q-jump theorem is precisely the assertion that a simultaneous wall cannot create such a
zero-sum atom without either revealing a real intermediate first-return-complete zero-sum union,
producing an exact two-splitter branch, or falling to the local Section-`40` / marked-add /
completer catalogue.

Nor can one remove the simultaneous wall block by a formal tie-break.  The low-set congruence applies
only to a complete shared-slack set of an actual transported first-return square.  If a wall introduces
a block `B` of rows at the same discrete repair step, an arbitrary lexicographic prefix of `B` is not
known to be the failure set of any square; applying congruence to that prefix would be exactly the
marker-completeness gap in another form.  Therefore the no-q-jump theorem must either construct real
intermediate first-return squares for prefixes, or prove a regular/local exit directly from the whole
simultaneous block.

For the exact-marker routing layer, the state-internal splitter has only two possible traces on the
marked quartet.  In both same-type cases, a row of `L\R` sees all four vertices `{d,e,x,y}`: it sees
`x,y` by the one-defect trace, and the low-set update gives that `d,e` see precisely the low vertices
outside `R`.  A row of `B\{d,e}` misses all four: it is outside the low traces of `x,y`, and the update
gives that `d,e` have no high neighbors outside the forced add/miss sites.  Thus the exact-routing
problem has two normalized splitter types:

1. **low universal splitter:** `v in L\R`, `v` sees `d,e,x,y`, and `v` is nonconstant on `R`;
2. **high null splitter:** `v in B\{d,e}`, `v` misses `d,e,x,y`, and `v` is nonconstant on `R`.

Each single marker row still gives the same five-vertex house/`P_5`/`C_5` seed as before, so the
splitter normalization does not by itself solve the seed-packaging problem.  What remains is to show
that a low universal or high null splitter either packages the seed into a Section-`40` quotient/fiber
or supplies the square-provenance wall whose failure set is a proper side of `R`.

There is a useful trap in the low universal case.  Let `v in L\R` be a low universal splitter and set
`S=R union {v}`.  If every vertex outside `S` is constant on `S`, then all vertices of `S` receive the
same outside contribution.  Since all vertices of `S` are low, their degrees in `G[S]` are congruent
modulo `q`.  But `|S|=q+1`, so the induced degrees lie in `[0,q]`.  Congruence modulo `q` forces
either equality, or a mix of degrees `0` and `q`; the latter mix is impossible because a degree-`q`
vertex is adjacent to every vertex of `S` while a degree-`0` vertex is adjacent to none.  Hence `G[S]`
is regular, giving an induced regular subgraph of size `q+1`.

This trap is proved directly for the low universal splitter.  A high null splitter lies in the
opposite near-regular residue class from the marker rows, so the same `R union {v}` congruence does not
follow merely by complementing the local picture.  Thus exact-marker routing first splits as follows:

1. **low universal:** either `R union {v}` is already regular of size `q+1`, or there is a second
   splitter of that enlarged set; a second splitter constant on `R` but distinguishing only `v` is a
   fixed-trace/false-clone candidate for Section `40`, while one that also splits `R` is a new marker
   splitter;
2. **high null:** either the one-excess argument below closes the no-second-splitter case, or there is
   a second splitter of `R union {v}`.

The high-null case has a weaker exact normal form.  Let `v in B\{d,e}` be high null and
`S=R union {v}`.  If no vertex outside `S` splits `S`, then all rows of `R` have the same induced
degree `a` in `G[S]`, while `v` has degree `a+1` modulo `q`; since all degrees lie in `[0,q]`, this is
an actual one-excess pattern:

- every `r in R` has `deg_S(r)=a`;
- `deg_S(v)=a+1`.

Removing a neighbor `u in R cap N(v)` gives a regular `q`-set immediately if `u` has no neighbors in
`R\{u}`; then `v` and every remaining marker row have degree `a`.  Hence the irreducible high-null
case is a one-excess `(q+1)`-vertex graph in which every neighbor of `v` has an internal neighbor in
`R`.  That residual finite pattern is the high-null analogue of the two-splitter blocker.

This residual high-null pattern is not vacuous as a finite one-excess graph.  For `q=8`, take

- `A={a_1,a_2,a_3,a_4}` and `C={c_1,c_2,c_3,c_4}` inside `R`;
- a cycle on `C`;
- matching edges `c_i a_i`;
- two edges `a_1 a_2` and `a_3 a_4`;
- a high-null splitter `v` adjacent exactly to the four vertices of `A`.

Inside `R`, the vertices of `A` have degree `2` and the vertices of `C` have degree `3`.  In
`S=R union {v}`, every marker row has degree `3`, while `v` has degree `4`, so this is exactly the
one-excess high-null normal form.  Deleting `v` leaves nonregular `R`; deleting a vertex of `C` leaves
`v` of degree `4` while the marker rows have degree at most `3`; deleting a vertex of `A` makes
`v` degree `3` but lowers one of its internal neighbors to degree `2`.  Thus no `8`-subset of `S` is
regular.  However, the table also exposes the next reduction rather than a terminal obstruction:
the marker graph contains a same-trace induced `P_3`.

In fact this is forced in every irreducible high-null one-excess case.  Let `A=N_S(v) cap R`, so
`|A|=a+1`, vertices of `A` have degree `a-1` in `G[R]`, and vertices of `R\A` have degree `a` in
`G[R]`.  If `G[R]` had no induced `P_3`, it would be a disjoint union of cliques.  Vertices in the same
clique have the same internal degree, so no clique can mix `A` with `R\A`; every clique meeting `A`
would have size `a`.  Since `|A|=a+1`, this is impossible unless `a=1`.  But when `a=1`, every
neighbor of `v` is isolated inside `R`, and deleting such a neighbor already gives a regular
`q`-set.  Therefore the residual high-null blocker always contains a same-trace induced `P_3` inside
`R`.

This `P_3` is already one of the Section-`40` labelled templates.  In the miss/miss orientation the
marked quartet is the `C_4`

- `d-e-x-y-d`,

and every marker row has trace `{x,y}`, the roof false-clone trace over the adjacent edge `xy`.
Thus a `P_3` inside `R` is exactly the `Sigma_rf` template of Section `40.1`; Section `40.3` routes it
back to the false-clone closure and Consequence `40.10` eliminates it.  In the add/add orientation,
complementing the marked `2K_2` gives the same roof false-clone template.  Hence the high-null branch
with no second splitter on `R union {v}` is closed by Section `40`; the exact high-null work that
remains is the case where a second splitter of `R union {v}` exists.

Consequently the exact-marker endpoint has a clean two-splitter normal form.  There is a
state-internal normalized splitter `v` of `R`, with `v` either low universal or high null, and there is
some second vertex `w` outside `S=R union {v}` that splits `S`.  The second splitter has only two
roles:

1. **marker-splitting:** `w` is nonconstant on `R`; this is again a marker splitter and must be routed
   to square-provenance or a Section-`40` / marked-add / completer exit;
2. **singleton-splitting:** `w` is constant on `R` but distinguishes `v` from the marker; this is the
   exact analogue of a one-corner lift over the normalized splitter and must be localized as a
   false-clone/roof gate or converted into a provenance wall.

The singleton-splitting branch is local.  Since `w` is constant on the entire marker, the marker is a
single roof false-clone bag over the marked quartet, and `v,w` are the opposite-side breaker pair for
that roof gate.  In the miss/miss orientation this is the `U_1` roof template of Proposition `39.10`;
in the add/add orientation it is the complement.  Proposition `39.10` either reseeds immediately to a
`C_5`/house or returns to the old house-reseating automaton, and Proposition `40.3` records exactly
this as the harmless `Sigma_rf` roof false-clone branch.  Thus singleton-splitting second rows are
closed by the already recorded Section `39`--`40` machinery.

The no-second branches and singleton-splitting branch were closed here.  The remaining exact-size case
at that stage was the **marker-splitting two-splitter theorem**: if the second splitter `w` is also nonconstant on
`R`, route the two independent cuts of the exact marker to square-provenance or to a local
Section-`40` / marked-add / completer exit.  A static degree count cannot decide this because `w` may
be an ambient row rather than a state-internal low/high row.

This is not a cosmetic leftover: it is the old sign-vector barrier after the already-closed regular
cases are removed.  The perfect-matching sign-vector table is only an incidence-level warning, because
there `G[R]` itself is regular.  An irreducible exact atom must additionally make `G[R]` nonregular;
for example the `P_3`-free part can be a union of unequal cliques, with outside trace fibers and
state-internal splitters compensating the low degree residues.  Refining by complete outside trace
then gives nonzero fiber residues whose total is `0 [MOD q]` and with no proper first-return-complete
zero-sum union.  Thus all frozen-fiber, no-second-splitter, singleton-lift, and same-trace closures
miss precisely this **nonregular sign-vector/zero-sum atom**.  The final theorem must use
first-return/provenance data to exclude it; no static trace-fiber or degree argument recorded so far
can do it.

Inside that atom one further local reduction is sound.  If `G[R]` contains a same-trace induced `P_3`,
Section `40.10` closes it, so the residual marker graph is a disjoint union of cliques.  A provenance
splitter that cuts through one of those cliques distinguishes two adjacent same-trace marker rows.
Together with the marked quartet this is the same roof/twin-breaker gate handled by the `U_1` and
`Sigma_rf` reductions in Sections `39`--`40`; hence such a cut is local, not a new q-marker
obstruction.  Therefore the irreducible zero-sum atom is **clique-coherent**: every surviving
provenance splitter is constant on each internal clique of the marker, and the atom lives on the
quotient whose vertex weights are the clique sizes.

The clique quotient has one more forced normalization.  Inside one complete outside-trace fiber the
outside contribution is identical for every marker row.  Since all marker rows have the same low
degree residue, the internal clique sizes in that fiber are congruent modulo `q`; as every surviving
clique has size `<q` (otherwise it contains `K_q`), those clique sizes are actually equal.  Thus each
trace fiber is a packet of equal-size cliques, with packet weight `n_i s_i`, where `s_i<q` is the
common clique size and `n_i` is the number of cliques in the packet.  A packet weight `0 [MOD q]` is
closed by the frozen modular-cluster selection, and a proper first-return-complete zero-sum union
contradicts marker minimality.  The final atom is therefore a minimal zero-sum sequence of nonzero
packet weights `n_i s_i` over `Z/qZ`, with no packet internally split by a provenance row.

It is also sparse at every regular-selection scale.  For any divisor `h` of `q`, if the marker
contains at least `q/h` internal cliques of size at least `h`, then choosing exactly `h` vertices from
each of `q/h` such cliques gives an induced `q`-vertex `h-1` regular graph.  Hence an irreducible
clique-coherent atom must satisfy:

- for every `h | q`, fewer than `q/h` marker cliques have size at least `h`.

This eliminates all dense clique quotients; the residual atom has only a small number of large
internal cliques, with the missing degree mass supplied by provenance splitters.

The sparse packet conditions are not enough by themselves.  At `q=8`, a marker graph

- `G[R]=K_5 disjoint_union K_3`

has exact size `q`, is nonregular and `P_3`-free, satisfies the divisor-sparsity condition, and has
packet weights `5` and `3`, a minimal zero-sum sequence in `Z/8Z`.  Suitable outside/state-internal
trace packets can compensate the internal degree difference modulo `8`.  Thus the final exclusion
cannot be a theorem about clique sizes and zero-sum residues alone; it must use first-return
provenance or weighted-quotient packaging.

In the exact-size case the zero-sum language is especially weak.  The packet weights are positive
integers with ordinary sum exactly `q`, so every proper packet union has ordinary size between `1` and
`q-1` and hence cannot be `0 [MOD q]`.  Thus "minimal zero-sum" is automatic at exact size.  The
remaining exact atom is simply a nonregular clique-coherent packet partition of `q` whose low degree
defects are compensated by state-internal/outside traces.  No zero-sum subsequence theorem can remove
it.

There is a conditional weighted-quotient re-entry at this point.  In the exact-size atom every packet
weight is a positive integer `<q`.  If the marked quartet together with these complete outside-trace
packets and the relevant splitter packets forms a prime weighted quotient satisfying the modular
weighted-degree equations, then Consequence `40.12` applies and the atom is closed.  Therefore the
surviving obstruction is not merely "the marker can be split into sub-`q` packets"; it is the failure
to package that packet quotient as one of the Section-`40` weighted-house / false-clone quotients.
Equivalently, the final first-return theorem may be stated as a quotient-packaging theorem for the
minimal zero-sum packet atom.

However, this re-entry is only conditional.  Consequence `40.12` is a total-weight `q^2` theorem,
whereas the exact marker atom asks for a regular induced selection of size `q` from the packet quotient
and a few compensating splitter packets.  The truly local finite target is therefore smaller:

> **packet-quotient regular-selection theorem.** In the clique-coherent first-return atom, the weighted
> quotient whose bags are the marker clique packets and the normalized splitter/provenance packets has
> an induced regular selection of total weight `q`, unless the quotient is exactly one of the
> Section-`40` weighted-house / false-clone packages or yields a proper first-return-complete
> zero-sum marker.

This is the non-circular replacement for importing the full prime weighted quotient branch.  The
remaining proof must either establish this packet-quotient selection theorem from first-return order,
or show that first-return order automatically promotes the packet quotient to the existing
Section-`40.12` setting.

In concrete terms, the packet-quotient theorem asks for an integral regular-selection solution.  For
each marker clique packet `(n_i,s_i)`, choose some number of its cliques and a common number of
vertices from each chosen clique; for each normalized splitter/provenance packet, choose a compatible
number of vertices.  The total chosen weight must be `q`, and for every chosen quotient type the
induced degree

- internal chosen clique contribution,
- plus chosen adjacent quotient weights,

must equal one common integer.  If such a solution uses only marker cliques it is exactly the
divisor-selection lemma above; if it uses splitter packets, it is the finite compensator selection
that should replace the missing completer.  Therefore the final atom is now a fully explicit finite
integer feasibility problem on the first-return packet quotient.

One useful positive subcase is already closed.  Suppose the marker quotient has two clique packets of
sizes `a>b` with `a+b=q`, and there is a provenance/splitter packet containing a clique of size
`t=(a-b)/2` that is complete to the smaller marker clique and anticomplete to the larger one.  Then
select:

- `a-t=b+t` vertices from the larger clique;
- all `b` vertices of the smaller clique;
- the `t` compensator vertices.

The selected larger-clique vertices have degree `b+t-1`; the smaller clique together with the
compensator clique is a clique of size `b+t`, so those vertices also have degree `b+t-1`.  The total
selected size is `(a-t)+b+t=a+b=q`.  Thus this gives a regular induced `q`-set.  For `q=8`, this is
exactly the `K_5 disjoint_union K_3` atom closed by one compensator vertex complete to `K_3` and
anticomplete to `K_5`.

Conversely, in this one-sided two-clique quotient the half-excess clique is forced.  Let a regular
`q`-selection choose `alpha` vertices from `K_a`, `beta` vertices from `K_b`, and a set `W` of
`gamma` compensators, with the compensators complete to `K_b` and anticomplete to `K_a`.  If the
selection meets both marker cliques and the compensator side, then equality of the selected degrees on
`K_a` and `K_b` gives

- `alpha - 1 = beta - 1 + gamma`, hence `alpha=beta+gamma`.

The total-size condition gives

- `alpha + beta + gamma = q = a+b = 2b+2t`,

so `beta+gamma=b+t` and `alpha=b+t`.  Each selected compensator must then have internal degree

- `(alpha-1)-beta = gamma-1`

inside `W`.  Thus `W` is a clique.  Since `beta<=b`, one also has `gamma>=t`.  Therefore every such
regular selection contains a compensator clique of size at least `t`, and the positive lemma above is
sharp for the intended compensation scheme: absence of a `t`-clique blocks every regular selection
that uses both marker cliques and the one-sided compensator side.

Therefore a surviving two-packet atom with even size gap must lack the corresponding clique
compensator; if first-return degree compensation supplies such a packet, the atom is closed.

The residue equation explains exactly what first-return must supply.  For two marker cliques
`K_a,K_b` with `a=b+2t`, marker rows in `K_a` have internal degree `a-1`, while marker rows in `K_b`
have internal degree `b-1`.  Equal low residues require the outside contribution to `K_b` to exceed
the outside contribution to `K_a` by `2t` modulo `q`.  If the ordered first-return orientation rules
out the reverse compensator direction and keeps the signed excess below `q`, this is an actual excess
of `2t` vertices complete to `K_b` and anticomplete to `K_a`.  The selection lemma above needs a
`t`-clique inside that compensator fiber.  Thus the two-packet atom reduces to a precise
half-excess-clique theorem for the first-return compensator fiber; if that fiber has no such clique,
the absence itself must be routed to Section `40` or to a further packet split.

This half-excess clique is not forced by static same-trace information.  For `q=8`, `a=6`, `b=2`, and
`t=2`, one can make the four one-sided compensator vertices independent while keeping them complete
to `K_2` and anticomplete to `K_6`.  The required `K_2` inside the compensator fiber is then absent,
and the compensator fiber itself has no same-trace `P_3`.  This is only a local incidence model, but it
shows that Section `40` plus residue count still do not prove the half-excess theorem.  The missing
ingredient must be first-return provenance for the compensator fiber, not a static Ramsey argument.

The obstruction persists for every even `q>=8` only after the orientation is respected.  Take marker
cliques

- `A=K_{q-2}`,
- `B=K_2`,

and an independent compensator set `C` of size `q-4`, complete to `B` and anticomplete to `A`.  The
marker rows in `A` and `B` have the same degree `q-3` after the compensators are added, so the residue
compensation is exact inside this packet subquotient.  But no induced `q`-set inside
`A union B union C` is regular.  Indeed, if a
candidate chooses `x` vertices from `A`, `y` from `B`, and `z` from `C`, then for `x,y,z>0` regularity
forces `z=1`, `x=y+1`, and hence total size `2y+2`, which equals `q` only when `y=q/2-1>2`; the
remaining cases have total size `<q` or incompatible degrees.  Thus the packet-quotient
regular-selection theorem is false without a first-return restriction on the compensator fiber.

This model is irrelevant in the miss/miss orientation once the marked quartet is allowed: there
`x,y` are adjacent and complete to the marker, so `A union {x,y}` is an induced `K_q`.  Hence the
static split obstruction is an add/add-orientation packet obstruction (or a packet-quotient obstruction
before the marked quartet is packaged), not a universal full-graph obstruction to regular selection.
This is useful:
the miss/miss two-packet atom with a `q-2` clique is already closed by the inserted pair.

More generally, in the miss/miss orientation any marker clique of size at least `q-2` closes: a
`q-1` clique plus either `x` or `y` gives `K_q`, and a `q-2` clique plus the adjacent pair `{x,y}`
gives `K_q`.  Thus a miss/miss residual packet atom has every marker clique of size at most `q-3`.
The extremal split packet obstruction above is therefore purely add/add-oriented unless the quotient
has no `q-2` marker clique.

The inserted-root pair gives one orientation-independent bound as well.  In both same-type
orientations every slack-marker row is adjacent to both inserted roots `x,y`.  Hence any marker clique
of size `q-1` closes immediately by adjoining either inserted root.  The only clique-size endpoint not
removed by the roots themselves is therefore an add/add marker clique of size exactly `q-2`: in
miss/miss the adjacent pair `{x,y}` completes it to `K_q`, while in add/add the pair is nonadjacent and
the induced graph `K_{q-2} * \overline{K_2}` is not regular.

Consequently an exact residual atom with a `q-2` clique has a very rigid orientation: it is add/add,
the remaining marker weight is `2`, and the roots cannot be the missing half-excess compensator.  The
needed compensator must be a genuine first-return/provenance packet, or else the `q-2` clique is a
proper split-module packet whose ambient breakers have to be routed to a packet refinement or to one of
the local exits.

The admissible-splitter subcase of this extremal clique is already harmless.  Since the clique lies in
the slack low set, an interval-admissible one-defect/provenance row is either constant on it or differs
on at most one clique vertex.  A nonconstant admissible split therefore has sides of size `1` and
`q-3`; if either side is the complete first-return shared-slack marker for the transported square, the
low-set congruence forbids it because it is nonempty and sub-`q`.  If the isolated failure is not
marker-complete, it belongs to the local non-marker exit already separated above.  Thus the live
`q-2` clique endpoint is not an admissible-split calculation; it is exactly the
ambient-to-provenance/marker-completeness routing problem.

Nor can one close the endpoint by applying the same-trace theorem to an arbitrary ambient splitter of
the clique.  The vertices of the `q-2` clique are same-trace over the marked quartet, but Consequence
`40.10` applies only after the distinguisher has been reseated into the same residual fixed fiber.
An ambient prime-shell breaker that splits the clique but is not a first-return/provenance row is
therefore still outside the Section-`40` hypotheses.  Routing that breaker into a fixed fiber, or into
a marker-complete first-return split, is precisely the remaining ambient-to-provenance step.

Combining this with the exact-marker internal-splitter reduction above gives the smallest current
form of the add/add `q-2` endpoint.  In an exact marker, some row of `T\R` splits `R`.  If any
state-internal/provenance row cuts the `q-2` clique, the cut is either a fixed-fiber same-trace
breaker and Section `40.10` applies, or it is a square-provenance split and the sub-`q` congruence
applies as just recorded.  Therefore a surviving `q-2` clique must be constant to every
state-internal/provenance row; the required state-internal splitter can only distinguish the residual
two marker rows.  The large clique is then a module for the entire first-return closure, but not
necessarily for the ambient prime shell.  Thus the endpoint is now:

> **ambient-only clique-module routing.** A `q-2` slack clique that is a module for all
> state-internal/provenance rows is either a genuine prime-shell module, or every ambient breaker of it
> routes to a fixed-fiber same-trace breaker, a marker-complete sub-`q` split, or a local exit.

There is a pointwise filter on such ambient breakers.  If an ambient breaker `z` of the clique is a
completer for the peeled package, the host exits immediately.  If `z` is a one-defect outside witness
(`epsilon(z)=1` in the notation of Section `40.16`), then because the clique lies in the low set, `z`
can split it only by isolating one missed low row; that is exactly the admissible one-defect split
closed above by sub-`q` congruence or by the local non-marker exit.  Thus every genuinely live
ambient-only clique breaker has

- `epsilon(z) >= 2`

relative to the current peeled package.  This explains why raw short-packet rigidity and Hall
one-defect capacity do not see the endpoint: the breaker that proves ambient primeness is necessarily
outside the completer/one-defect families unless it has already closed the atom.

The internal marker graph in this endpoint is also forced.  Let

- `A` be the `q-2` marker clique;
- `U=R\A`, so `|U|=2`.

Every row of `R` has the same marked trace over `{d,e,x,y}`.  If some `u in U` has mixed adjacency to
`A`, then two adjacent vertices of `A` together with `u` form a same-trace induced `P_3`, closed by
Consequence `40.10` after the already available roof/fixed-fiber localization.  If `u` is complete to
`A`, then `A union {u,x}` is an induced `K_q`, because the inserted root `x` is complete to the slack
marker.  Therefore, in a residual atom,

- `U` is anticomplete to `A`.

The marker graph is consequently exactly

- `K_{q-2} disjoint_union H`,

where `H` is either `K_2` or `2K_1` on the residual two marker rows.  All degree compensation for
`U` versus `A` must come from outside/provenance packets: `q-4` extra neighbors per residual row in the
`H=K_2` case, or `q-3` in the `H=2K_1` case, modulo the common contribution from rows constant on
`R`.  Thus the ambient-only endpoint is not a hidden internal-marker problem; it is a pure outside
compensation/routing problem over this split marker graph.

The independent residual-pair case has its own compensator-clique criterion.  Suppose a regular
selection uses

- `alpha` from `A`,
- `beta` from `U`,
- `gamma` from a one-sided compensator set `C` complete to `U` and anticomplete to `A`.

If the selection meets `A`, `U`, and `C`, then equality of the selected degrees gives

- `alpha-1 = gamma`,
- every selected compensator has internal degree `gamma-beta` inside the selected part of `C`.

The total size is `alpha+beta+gamma=q`, so `2 gamma+beta+1=q`.  Since `q` is even and
`beta in {1,2}`, necessarily `beta=1`, `gamma=q/2-1`, and `alpha=q/2`.  The selected compensators
must then have internal degree `gamma-1`, i.e. form a clique of size `q/2-1`.  Thus the
`H=2K_1` branch closes if the one-sided compensator fiber contains a clique of size `q/2-1`; the
independent-compensator model is the sharp static obstruction because it supplies no such clique.

Thus the tiny exact endpoint is gone.  For `q=4`, if `H=K_2` then the marker itself is
`K_2 disjoint_union K_2`, a regular `4`-set.  If `H=2K_1`, the single required compensator complete to
`U` and anticomplete to `A` lets one choose all of `A`, one row of `U`, and that compensator, again
giving `2K_2`.  Therefore every live add/add `q-2` cross-split endpoint has `q>=6`.

The `H=K_2` branch has one more small closure.  At `q=6`, `A=K_4`, `U=K_2`, and the required
compensator excess has size `q-4=2`; the half-excess is `1`, so any one compensator complete to `U`
and anticomplete to `A` closes the selection:

- choose `3` vertices from `A`;
- choose both vertices of `U`;
- choose that one compensator.

All selected vertices have degree `2`.  Hence the clique-pair branch is genuinely live only for
`q>=8`; the independent-pair branch is the only cross-split branch that can start at `q=6`.

So the final cross-split theorem has exactly two live arithmetic branches:

1. `H=K_2`, `q>=8`: the residual pair is adjacent, the required outside excess over `A` is `q-4`, and
   the finite obstruction is absence of a clique of size `(q-4)/2` in the one-sided compensator fiber.
2. `H=2K_1`, `q>=6`: the residual pair is independent, the required outside excess is `q-3`, and the
   finite obstruction is absence of a clique of size `q/2-1` in the one-sided compensator fiber.

Both branches have the same structural blocker: the compensator/provenance packets are constant on
`A`, while ambient primeness supplies only high-error breakers of `A`.  Thus the remaining theorem is
uniformly a common-package routing statement, not two unrelated finite selection problems.

Equivalently, set

- `k(H)= (q-4)/2` when `H=K_2`;
- `k(H)= q/2-1` when `H=2K_1`.

The finite part of the endpoint is now exactly:

> find a clique of size `k(H)` in the one-sided compensator/provenance fiber complete to `U` and
> anticomplete to `A`, or route the absence of such a clique to a fixed-fiber Section-`40` closure,
> a proper marker-complete split, or a packet refinement.

This statement is for selections that use the residual pair `U`.  There is a separate divisor bypass
that avoids `U`: if some proper divisor `h|q` has at least `q/h-1` compensator clique components of
size at least `h`, then choosing `h` vertices from `A` and `h` vertices from each of those components
gives a disjoint union of `q/h` copies of `K_h`, hence a regular `q`-set.  Therefore a residual
compensator packet must also satisfy the mixed divisor-sparsity condition

- for every proper divisor `h|q`, fewer than `q/h-1` compensator components have size at least `h`.

After this divisor bypass is removed, the `U`-using selection target is the `k(H)`-clique above.

This finite list is exhaustive for the static split quotient.  In a regular selection using `U` and a
compensator component of selected size `gamma`, every selected compensator vertex has degree
`beta+gamma-1`, where `beta=|S∩U|`; the selected `U`-vertices have degree `gamma` in the independent
case and `gamma+beta-1` in the adjacent case.  Thus `H=2K_1` forces `beta=1` and
`gamma=q/2-1=k(H)`, while `H=K_2` forces either `beta=2,gamma=(q-4)/2=k(H)` or the larger
`beta=1,gamma=q/2-1`, which contains a `k(H)`-clique anyway.  If the selection avoids `U`, equality of
the degrees of the selected `A`-vertices and compensator vertices forces every nonempty selected clique
piece to have the same size `h=|S∩A|`; hence the selection is exactly the proper-divisor bypass above.
Selections avoiding both `A` and `U`, or using `U` but not `A`, require a compensator clique of size at
least `k(H)` unless they have size `<q`.  Therefore "no `k(H)`-clique plus mixed proper-divisor
sparsity" is precisely the no-static-selection condition for this split quotient.

Here is the missing multi-component check explicitly.  Suppose a regular selection meets `A`, meets
`U`, and meets `m` compensator clique components in positive sizes `gamma_1,...,gamma_m`.  The selected
degree on `A` is `alpha-1`, while a vertex in the `i`-th compensator component has degree
`beta+gamma_i-1`; hence all `gamma_i` are equal to a common `gamma=alpha-beta`.  The degree on a
selected residual row of `U` is

- `sum_i gamma_i + beta-1` when `H=K_2`;
- `sum_i gamma_i` when `H=2K_1`.

For `H=K_2`, equality with `beta+gamma-1` gives `(m-1)gamma=0`, so `m=1`.  For `H=2K_1`, equality gives
`(m-1)gamma=beta-1`.  If `beta=1`, again `m=1`; if `beta=2`, then `m=2` and `gamma=1`, giving total
selected size `alpha+2+2=7`, impossible in the even-`q` endpoint.  Thus every live `U`-using regular
selection uses a single compensator component, exactly as the `k(H)` criterion says.  The only way to
use several compensator components is therefore to avoid `U`, and then the equal-size divisor bypass is
forced.

No hidden selection using the marked quartet remains in the live range.  In the add/add quartet, the
deleted high defects `d,e` are anticomplete to the marker and each sees only one inserted root among
`x,y`.  Thus any selected set containing `d` or `e` has minimum selected degree at most `1` on that
vertex.  For `q>=6`, a regular `q`-selection with degree at most `1` can use at most two vertices from
the clique `A` (indeed `deg_A=\alpha-1+p` with `p<=2` selected inserted roots), and then the total
available selected vertices from `A`, `U`, and the quartet is `<q` unless one uses outside
compensators.  Hence the quartet vertices cannot replace the compensator clique in any live
cross-split branch.

If the compensator fiber contains a same-trace induced `P_3`, Section `40.10` closes after fixed-fiber
packaging.  If it is `P_3`-free, it is a disjoint union of cliques, and the only finite obstruction is
that every clique has size `<k(H)` and the mixed divisor-sparsity inequalities above hold.  Thus the
remaining finite arithmetic is explicit; the remaining non-arithmetic work is first-return
routing/packaging of the compensator fiber and the ambient breaker of `A`.

In the `P_3`-free/no-`k(H)` case, the compensator fiber has at least three clique components.  Indeed,
for `H=K_2` its required total excess is `q-4=2k(H)`, while two cliques of size `<k(H)` have total at
most `2k(H)-2`.  For `H=2K_1` the total excess is `q-3=2k(H)-1`, while two cliques of size `<k(H)` have
total at most `2k(H)-2`.  Thus the last static compensator obstruction is not a two-block quotient:
it is a three-or-more-clique compensator packet, all complete to `U`, anticomplete to `A`, and not yet
packaged into a fixed-fiber Section-`40` quotient.

This multi-component compensator packet carries the same module pressure as the large clique.  Each
component has the same trace to the marker and to the other compensator components, except for its own
internal clique edges.  If a component has a fixed-fiber breaker, Section `40.10` or the packet
refinement route applies; if a component has a marker-complete provenance breaker, the resulting
subpacket has size `<k(H)<q` and is closed by the same congruence/selection logic.  Therefore a
surviving compensator component is also a module for the first-return/provenance closure.  Ambient
primeness may still break it, but such a breaker is again high-error and outside the fixed package.
Thus the no-`k(H)` compensator obstruction is another face of the same ambient-only routing theorem,
not a new finite arithmetic branch.

This gives a small dependency witness for the final routing theorem.  Start with either split marker
model above and declare the first-return/provenance rows to be exactly the rows constant on `A` that
provide the required compensation to `U`.  Now add an ambient row `z` that splits `A` in at least two
places and is kept outside the one-defect/completer traces.  Then `A` is not an ambient module, but it
is still a module for the whole first-return/provenance closure; the breaker `z` has `epsilon(z)>=2`
and supplies no marker-complete submarker.  This is not asserted to be a global counterexample, but it
shows that ambient-only clique-module routing is a genuine first-return theorem: module pressure plus
the finite quotient equations do not by themselves promote `z` to a fixed-fiber or provenance
breaker.

Thus the irreducible exact endpoint has a product-like cross-split form.  The exact-marker argument
forces at least one state-internal splitter, but in the residual `q-2` clique atom every such
state-internal/provenance splitter is constant on `A` and can only split the two-row block `U`.
Ambient primeness, on the other hand, supplies a high-error breaker `z` of `A`, but `z` is not in the
first-return/provenance closure.  The two available cuts therefore live on disjoint marker factors:

- a provenance cut on `U`;
- an ambient high-error cut on `A`.

If these two cuts can be realized in one ordered first-return square, the full wall-failure set is
proper and marker-complete, so the sub-`q` congruence or Section `40` closes.  If they cannot be put in
one square/fixed frame, the obstruction is exactly the ambient-only routing problem above.  This is the
packet form of pair-chamber hidden-choice separation: the proof must force the ambient clique breaker
and the provenance residual-pair splitter to share a first-return frame, rather than living in two
independent packet coordinates.

Thus a surviving endpoint has a genuine **product firewall** normal form.  On one factor, the
first-return/provenance closure sees the residual pair `U` and the one-sided compensator packets but is
constant on the large clique `A` and on every unrefined compensator component.  On the other factor,
ambient primeness supplies only high-error breakers of `A` or of such a component; completer and
one-defect breakers have already exited, and fixed-fiber/provenance breakers would refine a proper
sub-`q` packet.  Consequently no finite quotient selection, no same-trace component split, and no raw
short-packet relation remains unused.  The only missing input is order-sensitive: a first-return atom
cannot keep the ambient packet breaker and the provenance `U`-cut in disjoint coordinates indefinitely.

Equivalently, the product firewall reduces the whole problem to **first-boundary completeness**.  Take
a minimal ambient breaker `z` of a packet module, and try to use `z` as the next repair-boundary row in
the ordered first-return frame.  If all interval tests pass, then `z` has become a valid provenance row
and the packet split is in the fixed frame.  If the first failed test is at an old defect, inserted-root
test, or filler row, the already separated local exits apply.  If the first failed test is inside the
packet being split, the required conclusion is that the whole side of the packet cut by `z` is exactly
the wall-failure set of the transported singleton square.  Then that side is marker-complete and has
size `<q`, so low-set congruence or Section `40` closes it.  Thus the only still-unproved sentence is:

> a minimal high-error ambient packet breaker cannot have an ordered first failure inside the packet
> without making the entire first side of the packet a square-provenance wall.

This is the packet version of the q-marker provenance/support-decrease theorem.  It is stronger than
choosing a failed row and weaker than a global common-shadow theorem: it asks only that the first
boundary produced by the ambient breaker be complete enough for the low-set update to apply.

The closed parts of this first-boundary theorem are worth separating.  If the breaker coalesces with a
successor or fixed-trace row after the first failed wall is marked, Section `40.7`--`40.10` supplies the
same-trace / false-clone exit.  If the marked first-failure support is clean (`alpha_S=beta_S=0` in the
marked-add notation), the marked-add catalogue closes the noncoalesced branch.  Therefore the residual
first-boundary problem is purely **dirty packet-internal completeness**: the first failure lies in the
split packet, the support is dirty budget-one, and the wall side has not yet been proved to be the full
shared-slack set of a transported marked two-class quartet.  This is precisely the old dirty
`Abs(1)`/q-marker loop in packet language, with all finite and clean alternatives stripped away.

Once the ambient breaker is already an ordered boundary row, this dirty packet-internal completeness is
actually formal for the clique-coherent packets.  Let `P` be the packet being split.  All vertices of
`P` have the same trace to the marked quartet, to every provenance packet, and to every other packet;
inside `P` they are a clique packet (or one equal-size clique component after the `P_3` closure).  In a
singleton boundary test using `z`, the only coordinate on which two vertices of `P` can differ is
`1_{p~z}`.  Hence the boundary value is constant on `P cap N(z)` and constant on `P\N(z)`.  The first
packet-internal failed wall is therefore one of these two whole sides, or all of `P`; it cannot be an
arbitrary proper subset of one side.  Since `z` splits `P`, any one-side failure is a nonempty proper
marker-complete wall, and an all-`P` failure is still a proper wall unless `P` was the whole marker.
The low-set congruence/minimality argument then closes it, while the whole-marker case is the original
q-marker and not a product-firewall packet split.

Thus the packet-internal completeness part is no longer the live issue.  The live issue is the
preceding **row-to-boundary transport**: an ambient high-error breaker of a packet module must be
promoted to an ordered first-return boundary row, or else routed directly to a Section `40` /
marked-add / completer exit.  This is exactly provenance selection in its packet form.  Once such a
boundary row exists, the homogeneity argument above supplies square-provenance automatically.

The product firewall closes this transport gap by the same sub-`q` trap.  Suppose a minimal ambient
breaker `z` of a product-firewall packet cannot be transported to an ordered boundary row and does not
exit locally.  By the square-breaker routing reduction below, the first nonlocal obstruction is a
square-transverse breaker at the first witness-wall cut; after fixed-trace and clean marked-support
cases are removed, its only possible endpoint is the dirty budget-one shared-slack square.  But the
first nonconstant coordinate of that square is the packet coordinate split by `z`, so the shared-slack
set is contained in one breaker side of that packet.  In the product firewall every packet to which an
ambient high-error breaker is applied is a proper packet: the large clique has size `q-2`, and every
unrefined compensator component has size `<k(H)<q`.  Hence the resulting shared-slack set is nonempty
and has size `<q`.  The exact low-set update then gives `|R'|=0 [MOD q]`, impossible.

Thus row-to-boundary transport holds in the product-firewall endpoint: a high-error ambient packet
breaker either reseats into the ordered first-return boundary family, or one of the already closed
fixed-trace, clean, non-marker, Section-`40`, marked-add, or completer exits occurs.  Combining this
with packet-internal completeness closes the ambient-to-provenance routing theorem for the split
quotient.

The provenance cut on `U` is itself constrained.  Write `U={u_0,u_1}`.  The two residual rows have the
same internal marker degree (`0` in the `2K_1` case and `1` in the `K_2` case) and the same marked
trace.  Therefore the contribution from rows outside `R` must satisfy

- `#{p : p~u_0, p\nsim u_1} - #{p : p~u_1, p\nsim u_0} = 0 [MOD q]`

when counted over any complete state-internal/provenance packet family after rows constant on `U` are
discarded.  Hence a single one-sided provenance splitter of `U` cannot be the whole residual-pair
data: it must be balanced by opposite splitter mass, or by a full `q`-multiple packet, or it is a
local no-split/anti-Horn failure.  This is exactly the `host-opppair123` side of the same cross-split
atom.  The clique breaker on `A` supplies the other coordinate; pair-chamber separation is the
assertion that these two balanced one-coordinate data cannot remain independent.

In the sub-`q` balanced case, the residual-pair side is formally closed once it is packaged.  Two
opposite provenance splitters of `U` in one peeled anchored package have raw discrepancies

- `e_{u_0}-e_{u_1}`,
- `e_{u_1}-e_{u_0}`,

so their sum is a raw zero relation of total mass `2<q`; Proposition `40.16` forces both to be
completers, contradicting the assumption that they are only residual-pair splitters.  Thus the
residual-pair balance leaves only a package-identification problem: either opposite `U`-splitters
enter one fixed raw space and close, or their failure to share that space is the same common-discrepancy
/ pair-chamber blocker already isolated above.

This static obstruction is highly nonprime at the packet-quotient level: the quotient has three
vertices `A,B,C` with only the edge `BC`.  Thus it is split/disconnected, and it would be harmless if
it were promoted to a full total-weight `q^2` split weighted quotient by Proposition `33.1`.  The local
failure therefore identifies the last missing packaging step more sharply:

> **first-return packet-primality/packaging theorem.** The packet quotient produced by a genuine
> first-return q-marker atom is either prime/non-split and hence falls into the Section `40.12`
> weighted-quotient closure, or its split/disconnected decomposition supplies a proper
> first-return-complete marker, a half-excess compensator clique, or a local Section-`40` /
> marked-add / completer exit.

Without this first-return packet-primality input, the split local quotient above remains a static
countermodel to packet selection.

Equivalently, nonprime packet quotients require an **ambient-to-packet-prime routing** step.  If a
proper packet module `M` of the quotient has an ambient breaker, that breaker must be routed to a valid
first-return/provenance row that refines the packet partition, or to one of the local exits.  If no
such breaker exists, `M` is a genuine module of the prime shell.  This is the packet-level version of
the earlier ambient-to-provenance selection problem; it is not supplied by primeness alone because the
breaker may be an arbitrary ambient row outside the first-return family.

The cross-split endpoint is now downstream of the same fixed-package theorem as the host atoms below.
Assume the first-return fixed peeled-package/common-shadow theorem for the pair-chamber generated by an
ambient breaker of `A` and a provenance splitter of `U`.  Then an ambient breaker that splits `A` (or
one compensator component) is no longer harmlessly external: once transported into the common peeled
package, its wall-failure set is a nonempty proper marker-complete subset of `A` (or of a component),
hence has size `<q`.  The low-set congruence / raw short-packet argument then gives a Section-`40`,
marked-add, completer, or sub-`q` marker exit.  The same applies to opposite `U`-splitters: in the
common package their raw discrepancies are `e_{u_0}-e_{u_1}` and `e_{u_1}-e_{u_0}`, so `40.16` kills
the balanced sub-`q` pair.  Therefore a residual cross-split survivor can only be a failure to put the
ambient `A`-breaker, the `U`-splitter, and the compensator component in one peeled package.

That failure is exactly the successor-side `0001` / first-return common-shadow obstruction isolated
later.  One shadow empty is the one-corner ambient-to-fixed lift failure; two nonempty separated shadows
give the fully skew positive AND square.  Thus the add/add `q-2` endpoint adds no fourth mathematical
root after the finite selections above are removed:

`cross-split packet-primality`
`= ambient-to-provenance fixed-package routing`
`= first-return common-shadow / positive AND exclusion`.

This is only a dependency collapse, not a closure claim: the fixed-package/common-shadow theorem is
still the live input.

The original local trace-refinement proof had two gaps: dirty split side-preservation and terminal
module formation.  The omni-saturated carrier repair removes those broad objections by minimizing
against every outside row that preserves an active pair.  What remains is not the old preservation
gap, but the binary crossing endpoint where every surviving dirty row separates the unique active
pair.  This endpoint is the same fully skew `0001` / dirty shared-slack / budget-one reanchor
cycle-breaker isolated below.

The weighted primitive-carry proof has the analogous endpoint: the identity
`[1_B]=[1_{B_0}]+[1_{B_1}]` in `M_2(U)` preserves the formal aggregate class, but it does not by
itself prove that the split preserves the carry cut after the same dirty budget-one unary residual is
marked.

The exact singleton low-set update forces any first-return defect-switching shared-slack square into a
marked two-class quartet.  The closing theorem is:

> **marked two-class localization.** The low-set update produces two same-trace pairs `{d,e}` and
> `{x,y}` whose traces differ exactly on the shared-slack marker `R`; the four vertices induce `C_4`
> in the miss/miss case and `2K_2` in the add/add case.  This marked quartet must be reseated into a
> residual fixed fiber / Section-`40` or Section-`40.16` frame, or else give a completer or a weighted
> quotient seed already closed by Section `40`.

At this stage the proof below closed only the sub-`q`, no-split, and preserved-side branches; the
fully skew q-marker branch still needed q-marker provenance/support-decrease.  The product-firewall
transport closure recorded above supplies that missing support-decrease input, so the later weighted
carry audit no longer has an independent host-local blocker.

## Second attack on the audit gaps

The natural repair is to replace the informal "choose the side containing the next active edge" by a
trace-saturated carrier.  For a frozen host frame, let `A(C)` be the graph of active pairs inside the
current trace class `C`: an edge of `A(C)` is a pair that still realizes the same reanchor,
square-transverse, or filled-overlap obstruction after all fixed-trace and clean marked rows have
been removed.  Choose a counterexample with `C` minimal among all restrictions obtained by adding
valid dirty-row traces.

For a dirty failed row `r`, the partition `C=C_0 ⊔ C_1` gives a genuine descent only if some
`A(C_i)` is nonempty.  The minimal-carrier argument therefore leaves exactly one new case:

> **crossing-carrier case:** every active edge of `A(C)` crosses `C_0|C_1`.

In this case the row `r` separates every still-active pair, so the old potential argument cannot be
finished by induction; it must prove a new collapse statement:

> **crossing-separator collapse.** If a dirty row separates all active pairs in a minimal carrier,
> then either `r` is already an admissible repair/reanchor vertex, or the marked triple localizes to a
> Section `40` same-trace / false-clone kernel.

This was strictly smaller than the original host atoms, but was not then proved by the
same-trace catalogue: the row `r` is mixed-trace by construction, and the crossing condition alone
does not put the two sides into one residual fixed fiber.  Thus that audit sharpened the host gap
before the later q-marker closure.

There is one more honest reduction inside the crossing-carrier case.  Work with a connected component
of `A(C)` and choose `C` minimal under all valid dirty-row traces.  Then every valid dirty row either
is constant on `C` or separates every edge of `A(C)`; otherwise one of its fibers would contain an
active edge and give the forbidden smaller carrier.  Hence every dirty row induces the same
bipartition of the connected active graph, up to complement.  If one side of this bipartition
contained two vertices `x,x'`, then every outside dirty row would be constant on `{x,x'}`; and any
same-trace vertex of `C` distinguishing `x,x'` internally would be a Section `40` same-trace
internal-distinguisher.  Therefore that side would be a nontrivial module of the prime shell.  In a
prime minimal crossing carrier both sides are singletons.

So the host-local failed-row theorem is now equivalent to the following binary endpoint:

> **binary crossing endpoint.** Let `{x,y}` be the unique active same-trace pair in a minimal
> host-local carrier, and let every surviving dirty failed row separate `x` from `y`.  Then some
> separating row is an admissible repair/reanchor vertex, or the alternating failed-row ladder
> localizes to the Section `40` shifted-twin / stable-house descent.

At that stage the existing notes had not established this endpoint.  It is smaller than the earlier
crossing-carrier-collapse statement, but it is still a real orientation/no-holonomy theorem for the
two-row failed-ladder, not a formal consequence of primeness or the raw short-packet identities.

The direct attempt to invoke Proposition `40.8` stops at one precise place.  Normalize the unique
active pair as `{x,y}` and a separating dirty row `r` by `r~x`, `r\nsim y`.  If the first failed row
`s=φ(r)` has the same residual trace as `r` after marking the relevant endpoint/frozen square side,
then the quadruple falls into the normalized corner false-clone fiber: the alternatives in
Proposition `40.8` give an induced `P_4`, house, or gem unless the surviving `(1,0)` shifted
twin-breaker occurs, and that surviving case collapses to `O_10`, impossible by Proposition `40.7`.

Thus the only part of the binary endpoint not covered by Section `40` is a **skew binary ladder**:
successive dirty failed rows `r,s` both separate `x` from `y`, but no allowed marking makes them a
same-residual-trace pair.  The missing lemma is therefore:

> **binary trace-coalescence.** In the binary crossing endpoint, the first failed row of a separating
> dirty row coalesces with it in one residual fixed fiber after marking an endpoint or adjacent square
> side; equivalently, the skew binary ladder cannot occur.

The clean marked-add catalogue proves this coalescence when the marked support has
`alpha_S=beta_S=0`.  The dirty one-defect support does not yet have the same theorem: singleton
reanchors are reversible, and the miss/add sign is an undirected edge label rather than an
orientation.  Consequently the binary endpoint is now exactly this dirty binary trace-coalescence /
skew-ladder exclusion problem.

This is the same obstruction that appears later as two-off-root common-shadow synchronization.  In the
distributed-hexagon language, the two successive dirty rows are the two off-root vertices that must be
placed on one Section `40` frame over the common visible corner.  Binary trace-coalescence supplies
that common frame; conversely, a two-off-root common shadow makes the two rows same-residual-trace
after the allowed marking, and Proposition `40.8` finishes the shifted ladder.  Thus the following
three formulations are now equivalent at the audited frontier:

1. binary trace-coalescence / skew-ladder exclusion;
2. two-off-root common-shadow synchronization;
3. adjacent shared-slice admissibility for the one-corner median fiber;
4. two-fiber single-flip overlap, equivalently pair-chamber separation of the hidden choice after the
   already-isolated predecessor/persistence inputs are factored off.

None of these is presently a theorem in the notes.  All current Section `40` propagation begins after
one such frame/shadow has already been chosen.

The pair-chamber formulation exposes why the quotient-side route also stops here.  If a
pair-chamber cylinder `C` contained a nontrivial oriented hidden step `η -> η'`, any proof by
endpoint data would have to assign an orientation sign to that step while assigning the opposite sign
to `η' -> η`.  But `σ^-` and `σ^+` are constant on `C`, and the dyadic `F_2` cocycle is unoriented, so
neither can distinguish the two orientations.  A proof of pair-chamber separation therefore requires
new ordered common-edge step data: a sign `ω(C)` forced by the packet geometry, or a localization of
the chamber-flat step back to the binary trace-coalescence endpoint.  This ordered-sign problem is the
current quotient-side form of the same root blocker.

The dyadic weighted gap has the parallel minimal-carrier form.  Splitting a weighted block
`B=B_0⊔B_1` is safe only when one child still carries the primitive bad determinant/carry cut.  The
remaining case is:

> **two-child primitive carry:** neither child is a bad homogeneous obstruction, but the sum of their
> primitive boundary contributions is bad after the `2`-adic normalization.

This is exactly the phenomenon that the formal identity `[1_B]=[1_{B_0}]+[1_{B_1}]` misses.  A proof
would need a new localization theorem showing that every two-child primitive carry contains either a
homogeneous `H_min/H_big` suborbit obstruction or the same crossing-separator host configuration
above.  No such localization theorem is presently established.

With the binary reduction, the dyadic target sharpens as well: a two-child primitive carry either
exposes a homogeneous child, or its first nonhomogeneous boundary must localize to the first-return
defect-switching square.  The unweighted host audit reduces that square to five-vertex
seed-packaging; the dyadic endpoint needs the corresponding weighted seed-packaging for the two-child
boundary.

Algebraically, the two-child endpoint is the carry case
`c_0≡c_1≡0` in all homogeneous child tests but `c_0+c_1≡1` in the coarse block test after primitive
normalization.  The bad bit is the carry of the sum, not a bad child coefficient.  Hence a proof must
use host order/trace data across the boundary between the two children; determinant valuation alone
cannot decide it.

## Third attack: signed two-row holonomy

The binary endpoint can be sharpened one more step without closing it.  Normalize the active pair as
`r~x`, `r\nsim y` for one separating dirty row `r`, and write

- `eps(r)=+1` if `r` sees `x` and misses `y`;
- `eps(r)=-1` if `r` sees `y` and misses `x`.

For a skew adjacent pair `r -> s=phi(r)`, all data used by the existing catalogues are either
endpoint-unordered or chamberwise:

1. the fact that both rows separate `{x,y}`;
2. the two endpoint chamber labels after marking an endpoint or adjacent square side;
3. the mod-`2` cut/cocycle class carried by the pair.

These data are unchanged by reversing the elementary skew step, or else only record the unordered
separator side.  Thus they cannot supply the antisymmetric ordered sign needed to orient
`r -> s`.  The only way the current proof package can finish a skew pair is still coalescence into a
single residual fixed fiber, after which Proposition `40.8` and Consequence `40.10` apply.

Consequently the exact residual host blocker is the following smaller no-holonomy statement:

> **oriented two-row holonomy localization.** In the binary crossing endpoint, every noncoalesced
> skew adjacent pair `r -> phi(r)` either admits a cylinder-constant ordered sign on its residual
> pair-chamber, or a finite skew cycle localizes one of its turns to a Section `40` same-trace /
> false-clone kernel.

This is equivalent to binary trace-coalescence for the present proof package.  If the ordered sign is
constant on a pair-chamber cylinder, reversal gives the Lemma `14.1` contradiction and there is no
chamber-flat hidden step.  If instead a turn localizes to one residual fixed fiber, Section `40`
closes it.  What remains unproved is precisely the localization of an oriented skew cycle: singleton
reanchors are reversible, the miss/add label is an undirected edge label, and the dyadic `F_2`
cocycle forgets the direction of the turn.  Thus a proof still needs a genuinely ordered host
invariant, not another endpoint parity invariant.

## Fourth attack: turn-parity normal form

There is a useful split inside a skew turn.  For a noncoalesced adjacent pair `r -> s`, compare the
separator orientations `eps(r), eps(s)`.

### Opposite-side turns

If `eps(s)=-eps(r)`, normalize

- `r~x`, `r\nsim y`,
- `s\nsim x`, `s~y`.

Then the local induced-`P_4` test forces the internal edge of the turn to match the active pair:

- if `xy=0` and `rs=1`, then `x-r-s-y` is an induced `P_4`;
- if `xy=1` and `rs=0`, then `r-x-y-s` is an induced `P_4`.

Therefore every irreducible opposite-side skew turn satisfies

- `rs = xy`.

So the surviving opposite-side turn is exactly a balanced flip quartet: either `2K_2` on
`{x,y,r,s}` when `xy=0`, or a `C_4` when `xy=1`.  In the quotient table this is the already isolated
mixed non-overlap atom `{0101,0011}` with no `0111` row.  Thus the opposite-side part of oriented
holonomy is not a diffuse ladder any more; it is the single balanced flip quartet / two-fiber
single-flip overlap obstruction.

### Same-side turns

If `eps(s)=eps(r)`, then `r` and `s` are twins over the active pair `{x,y}`.  A skew same-side turn
can only remain noncoalesced because of dirty support away from `{x,y}`.  Along a finite holonomy
cycle made only of same-side turns, all cycle rows have the same separator side over `{x,y}` and are
indistinguishable by the endpoint data used above.  If every outside row is constant on the cycle,
the cycle rows form a nontrivial module in the prime shell.  Hence primeness gives an outside
distinguisher of the cycle.

The boundary of such a distinguisher is the exact remaining same-side problem.  At a first cyclic
boundary where the distinguisher changes value between consecutive rows, either that boundary
reseats the two rows into one Section `40` residual fixed fiber, or it creates an opposite-side
balanced flip quartet after the distinguisher is promoted to the next active separator.  What is not
yet proved is the routing step that promotes this boundary without losing the active packet.  This is
the same preservation problem that invalidated the first trace-refinement proof, but now it is
localized to a single boundary of a same-side skew cycle.

Thus oriented two-row holonomy has the following smaller normal form:

> **balanced-flip / same-side-boundary dichotomy.** Every noncoalesced skew holonomy either contains
> an irreducible opposite-side balanced flip quartet (`rs=xy`, row table `{0101,0011}`), or contains a
> same-side skew cycle with an external boundary distinguisher whose first boundary must be routed to
> Section `40` or to such a balanced flip quartet.

The first branch is exactly pair-chamber hidden-choice separation / two-fiber single-flip overlap.
The second branch is the minimal remaining active-packet-preservation problem for dirty
trace-refinement.

## Fifth attack: balanced flip as a raw two-packet

The balanced flip quartet would be killed immediately if its two flipped rows lived in one fixed
anchored raw-discrepancy space.  Indeed, in the opposite-side normalization the two rows have
opposite defects on the active pair.  After choosing the local low/high convention, their raw
discrepancies are

- `Delta_r = e_x - e_y`,
- `Delta_s = e_y - e_x`

up to simultaneous sign/complement.  Hence

- `Delta_r + Delta_s = 0`

with total mass `2 < q`.  By weighted raw short-packet rigidity (`40.16`), both contributing rows
would already be completers in that anchored near-regular package.  In the two-fiber table this is
exactly the missing `0111` row, so the non-overlap table `{0101,0011}` could not be irreducible.

Thus the balanced flip quartet is not a new arithmetic obstruction.  Its only possible escape is a
packaging failure: the two opposite flipped rows have not yet been proved to be raw discrepancies for
the same peeled set `T` with the same low set `L(T)`.  This is precisely the earlier
fiber-constant pair-status / defect-fiber identification problem in the one-corner model.  Once a
common local shell package `T_r=T_s` is available, Section `40.16` supplies the contradiction
formally.

So the balanced-flip branch reduces to:

> **common discrepancy packaging.** In a fixed-trace pair-chamber cylinder, the two opposite
> elementary flipped rows can be represented in one anchored near-regular discrepancy space with
> opposite raw defects on the same active pair.

This is weaker than full packet reconstruction.  It only asks for the common low/high coordinate
identification needed to add the two raw discrepancies.  It is also exactly the point at which the
direct visible geometry stopped: ambient binary-cylinder membership identifies the intended defect
set, but did not by itself prove that the fixed-frame lift has the same fiberwise pair status.

### Packaging audit

The one-square silent-component characterization almost proves common discrepancy packaging, but not
quite.  Equality of the pair-chamber coordinates says that on each incident filled square the two
repaired opposite defects lie in the same silent component.  Therefore every **unary** witness
incidence used by that square is constant across the two choices.  In particular, the intended
low/high active coordinates `x,y` are identified correctly, and the ambient transport point still cuts
out the same missing-corner set `I_rho`.

However `40.16` applies to full raw discrepancy vectors in one peeled set `T`.  Besides the unary
coordinates, those vectors also depend on the pair-status / local-fiber coordinates that say how the
chosen representative interacts with the other fibers of the fixed-frame transversal.  Pair-chamber
data alone do not currently prove that this binary pair-status is constant on the median fiber.  Thus
the exact missing part of common packaging is smaller:

> **binary pair-status constancy.** On the median fiber of the one-corner model, once the unary
> chamber coordinates and the ambient missing-corner set `I_rho` are fixed, the remaining local
> pair-status coordinates of the peeled raw discrepancy vector are constant.

With this constancy, common discrepancy packaging follows: the two opposite flipped rows become
`e_x-e_y` and `e_y-e_x` in the same raw vector space, `40.16` gives the missing `0111` overlap, and
the balanced flip quartet is excluded.  Without it, the two rows may agree on every one-square
chamber while still live in different binary pair-status fibers, so the raw two-packet cannot yet be
formed.

The old median-fiber reduction applies exactly to this pair-status coordinate.  If pair-status is
not constant, pick one local fiber/witness `a` and write

- `E_a := {m in M_rho : m~a}`.

The unary chamber data are fixed on `M_rho`, so a change in `E_a` is a purely hidden pair-status
change.  Assuming the median fiber is connected by hidden-coordinate flips, choose a bad hidden edge
and then a closest return of `E_a` on the far side.  The clean-corridor reduction from the direct
one-corner analysis leaves a single square

- `R={u_0,u_1,v_0,v_1}`

with pattern

- `u_0,u_1,v_0 notin E_a`,
- `v_1 in E_a`.

Thus binary pair-status constancy is now equivalent, for the current proof package, to excluding the
successor-side first-switch `0001` square on the median fiber.  All predecessor-side returns already
shorten the bad edge or fall to the strip-transfer theorem; only the successor-side `0001` square has
no current orientation.

This is the same residual atom as the candidatewise localized square anti-Horn theorem after unary
terms are subtracted.  One-coordinate predecessor/persistence cannot exclude it: the abstract table
`{00,10,01}` has all one-coordinate shadows but lacks the `11` corner.  Therefore the exact
pair-status blocker is:

> **successor-side `0001` exclusion.** On the one-corner median fiber with unary chambers fixed, a
> pair-status witness cannot first switch on the successor side in a hidden square with pattern
> `0001`.

The same-side holonomy branch folds into this atom as well.  In a same-side skew cycle, the cycle
rows are twins over the active pair and over the endpoint/chamber data.  An external boundary
distinguisher `a` of the cycle is therefore exactly a local pair-status witness: its incidence set
`E_a` is constant on one side of the cyclic boundary and changes at the boundary.  If the boundary
turn coalesces after marking, Section `40` applies.  If it does not coalesce, run the same
hidden-edge / closest-return minimization on `E_a`; predecessor-side returns shorten the boundary or
enter the strip-transfer case, and the irreducible noncoalesced boundary is again a successor-side
first-switch `0001` square.  Thus the two roots produced by the turn-parity dichotomy are not
independent:

> oriented two-row holonomy reduces to successor-side `0001` exclusion.

Once `0001` is excluded, binary pair-status is constant, common discrepancy packaging forms the raw
two-packet, the balanced flip quartet is killed by `40.16`, and same-side skew cycles route to
Section `40` or to that killed balanced branch.

## Sixth attack: `0001` is the positive AND square

Write the successor-side square as

- `u_0,u_1,v_0 notin E_a`,
- `v_1 in E_a`.

After identifying the two hidden directions with bits `H,J`, this is the Boolean function

- `p_a(00)=p_a(10)=p_a(01)=0`,
- `p_a(11)=1`.

Thus the obstruction is exactly the positive mixed second difference

- `Delta_H Delta_J p_a = 1`.

All one-coordinate data vanish at the lower corner:

- `p_a(10)-p_a(00)=0`,
- `p_a(01)-p_a(00)=0`.

So no theorem that sees only unary chamber walls, one-coordinate predecessor data, or separate
incident-square silent components can rule it out.  The needed statement is precisely the
single-witness hidden-square submodularity law

- `Delta_H Delta_J p_a <= 0`

in the oriented successor-side normalization.

Not every `0001` row is forbidden by the existing table calculus: earlier reductions explicitly
allow rows of type `0001` because they contribute to neither `Omega_10` nor `Omega_01`.  The live
atom is narrower.  It is a **first-return** `0001` square obtained after minimizing a bad hidden edge:
the predecessor rail and all earlier far-side vertices are outside `E_a`, every predecessor-side
return has already been shortened or discharged by strip transfer, and this square is the first
successor-side return.

There is, however, one more Section-`40` reduction.  The witness `a` is a common successor-only
distinguisher for both successor edges `u_1v_1` and `v_0v_1`.  If, after marking either predecessor
side of the square, `a` and that successor edge lie in one residual fixed fiber, the same-trace /
false-clone catalogue applies: the three-corner pattern gives the internal `P_3` or shifted
twin-breaker, and Proposition `40.8` closes the surviving shifted case.  Hence the only `0001`
square not already killed by Section `40` is:

> **anchored first-return fully skew positive AND square.** The pair-status function on the
> first-return hidden median square is the AND pattern `0001`, all clean-corridor minimality
> conditions above hold, and both successor edges carrying the first positive value remain
> noncoalesced under every allowed endpoint or predecessor-side marking.

Equivalently, successor-side `0001` exclusion is the union of:

1. same-trace / false-clone localization of one successor edge, already closed by Section `40`;
2. exclusion of the anchored first-return fully skew positive AND square.

The second item is now the single live mathematical atom.  It is stronger than pair-chamber
separation only in notation: a fully skew AND square is exactly a chamber-flat hidden step whose
ordered mixed sign cannot be read from either incident chamber separately.

In the distributed-hexagon language, the anchored first-return AND square is the smallest
two-off-root common-shadow failure.  The two successor directions are the two off-root transports
that should enter one common Section `40` frame over the visible median corner.  The clean-corridor
minimality says that all predecessor-side attempts already shorten to an earlier return or discharge
by strip transfer; the only remaining failure is that the two successor entries meet only in the
ambient binary cylinder, not in one fixed frame/shadow.  Thus the current root may be stated
geometrically as:

> **anchored first-return common-shadow theorem.** In the first-return square, the two successor
> off-root transports admit a common Section `40` shadow over the forced visible median point, unless
> one successor edge has already coalesced to the same-trace / false-clone catalogue.

This is the same theorem as anchored first-return AND exclusion.  Once the common shadow exists, the
rooted `P_5` seed lies in one frame, the marked support is clean, the marked-add catalogue kills the
noncoalesced branch, and the scalar part is automatic as recorded in the distributed-hexagon
analysis.

## Tenth attack: two-shadow intersection form

The anchored first-return common-shadow theorem has a sharper internal split.  Work over the forced
visible median point `s_*` and the median fiber

- `M_* := F_(b_1) cap S_c(s_*) cap pi^{-1}(s_*)`.

For the two successor off-root transports in the first-return square, define their fixed-frame shadow
sets

- `Sh_H subseteq M_*`,
- `Sh_J subseteq M_*`,

where membership means that the corresponding successor transport is realized in the Section `40`
frame with the prescribed shared-slice cylinder and the same ambient missing-corner set.

Then common-shadow is exactly:

- `Sh_H cap Sh_J != emptyset`.

The failure splits into two cases.

1. **Single-shadow failure:** one of `Sh_H,Sh_J` is empty.  This is precisely the one-corner
   ambient-to-fixed fiber-preserving shared-slice lift problem: ambient binary-cylinder membership is
   known, but no fixed-frame point above `s_*` has been produced.
2. **Two-shadow separation:** both `Sh_H` and `Sh_J` are nonempty but disjoint.  Choose a shortest
   hidden-coordinate path in `M_*` from `Sh_H` to `Sh_J`.  The first edge leaving the first shadow set
   is a packet-changing boundary.  If that boundary lies on a predecessor-side suffix, the existing
   strip-transfer/closest-return argument shortens the counterexample.  If a successor edge
   coalesces after marking, Section `40` closes it.  Hence the irreducible separated case is exactly
   the anchored first-return fully skew AND square: a successor-side first return whose two shadow
   sets are separated by a positive mixed second difference.

Thus the root can be stated as a fixed-frame shadow theorem:

> **first-return two-shadow theorem.** In the first-return one-corner model, ambient
> binary-cylinder membership produces the two successor fixed shadows, and two nonempty successor
> shadows in `M_*` cannot be separated by a fully skew successor-side first-return boundary.

This was the open non-circular version of the earlier gated/convex packet intuition before the
q-marker/product-firewall closure:
if these shadow sets were known to be gated convex sets in the median fiber, the closest-point
boundary would be a gate edge and the first-return square would collapse.  But importing gatedness
from silent-edge exclusion would be circular; the required input is direct fixed-frame shadow
gatedness or an equivalent two-shadow intersection theorem.

## Eleventh attack: why Section 40 alone does not intersect the shadows

Section `40.15`--`40.16` is a one-package theorem.  For a fixed peeled anchored near-regular set `T`,
the raw discrepancy

- `Delta_x^T = 1_{N(x) cap T} - 1_{L(T)}`

lives in `(Z/qZ)^T`, and every raw relation of total mass `< q` forces all contributing vertices to
be completers of that same `T`.

The two-shadow separated case is not automatically in that situation.  The two successor transports
come with a priori peeled packages

- `T_H, L_H, Delta^{T_H}`,
- `T_J, L_J, Delta^{T_J}`.

Even if each package has a completer, the two raw discrepancy spaces are different unless the
first-return model identifies the hidden representatives and the low/high partition.  Therefore the
formal sum

- `Delta_x^{T_H} + Delta_y^{T_J}`

has no intrinsic meaning in the Section `40` short-packet space, and one cannot use `40.16` to force
a common completer without an additional **common peeled-package** theorem.

This gives the currently smallest non-algebraic target:

> **first-return fixed peeled-package theorem.** In the anchored one-corner first-return model, the
> two successor transports over the visible median point induce the same peeled anchored
> near-regular package `(T,L(T))`, unless one successor edge coalesces into a Section-`40` kernel.

If this package theorem holds, the rest is formal.  The one-corner ambient-to-fixed lift gives a
nonempty shadow for either successor; common package makes the two shadow predicates the same raw
completer predicate, so `Sh_H = Sh_J` and hence `Sh_H cap Sh_J != emptyset`.  Then the common-shadow
theorem closes, followed by the balanced flip, holonomy, dyadic carry, and bridge implications.
This is exactly the earlier binary pair-status constancy statement, but now stated in Section-`40`
coordinates: all coordinates of the raw discrepancy vector, not only unary chamber walls, must be
constant across the first-return median fiber.

There is no further hidden package datum after the visible median point is fixed.  The two successor
transports already have the same ambient missing-corner set `I_rho`, the same unary chamber
incidences, and the same low/high cardinality residue.  Therefore equality of peeled packages
decomposes coordinatewise as:

1. unary coordinates, already fixed by the pair-chamber labels;
2. the low-set base vector, fixed once `I_rho` is fixed;
3. binary local pair-status coordinates against the other fixed-frame fibers.

Thus the first-return fixed peeled-package theorem is equivalent to **binary pair-status constancy on
the forced median fiber**.  If a pair-status coordinate is not constant, choosing one witness `a` and a
shortest hidden edge on which `E_a={m:m~a}` changes gives exactly the successor-side first-return
`0001` square after the closest-return/strip-transfer reductions.  Conversely such a `0001` square is
precisely a pair-status coordinate that prevents the two raw discrepancy vectors from living in one
peeled space.  So the active root is not "construct a whole package" but the single-witness
pair-status monotonicity / positive-AND exclusion.

## Twelfth attack: endpoint-mass does not by itself give the package

There is one tempting way to finish the first-return fixed-package theorem: sum the four-corner
pair-status table over all local fibers and try to use endpoint degree balance.  This gives a useful
audit, but not yet a proof.

After the one-edge predecessor and persistence inputs are factored off, every local-fiber coordinate
row over a terminal square, normalized by `d_00(K)=0`, has one of the five forms

- `0000, 0001, 0101, 0011, 0111`.

Its mixed second difference

- `mu(K) := d_11(K)-d_10(K)-d_01(K)+d_00(K)`

is:

- `+1` for `0001`;
- `-1` for `0111`;
- `0` for `0000,0101,0011`.

Thus any endpoint-mass identity in a common coordinate space can at best prove the compensation

- `# {K : r(K)=0001} = # {K : r(K)=0111}`

(or the corresponding signed equality with multiplicities).  But this is weaker than fixed-package
equality.  A local table with one `0001` coordinate and one compensating `0111` coordinate has
balanced endpoint mass, all one-coordinate persistence data, and a nonempty `Omega_10 cap Omega_01`;
nevertheless the `0001` coordinate still witnesses a different peeled raw-discrepancy coordinate
unless the compensating `0111` row is routed into the same Section-`40` package/shadow.

So endpoint mass breaks the problem into two exact alternatives:

1. **pointwise sign law:** prove `mu(K) <= 0` for every local fiber coordinate in the first-return
   successor-side normalization, thereby excluding `0001` outright;
2. **paired-compensator routing:** allow `0001`, but show that every first-return `0001` coordinate
   has a compensating `0111` coordinate whose common singleton-overlap localizes the offending
   successor transports to one peeled package, unless a successor edge coalesces into Section `40`.

The first alternative is the earlier single-witness median-square submodularity theorem.  The second
is strictly weaker than full fixed-package equality but still strong enough for common-shadow: the
`0111` row is exactly a common `H/J` successor overlap, and once each compensating overlap is routed
into the same peeled package as the positive coordinate it compensates, the endpoint-mass cancellation
becomes a genuine zero **mixed** discrepancy relation in one coordinate space.  This is still not
enough by itself for Proposition `40.16`: `40.16` needs a full raw relation, not merely cancellation of
the mixed second derivative.  Thus package routing must also align the unary residuals already fixed
by the chamber data.  Only after this **full residual alignment** does the compensated packet become a
raw zero-relation to which `40.16` applies, forcing the common completer/shadow.

The audit point is important: an endpoint-mass equality alone is circular if the two successor
coordinates have not first been put in a common raw vector space.  The new smallest target is therefore
not "sum the four corners", but:

> **first-return paired-compensator routing.** In the anchored first-return terminal square, every
> positive `0001` pair-status coordinate either has a coalesced successor edge, or has a compensating
> `0111` coordinate whose common successor overlap lies in the same Section-`40` peeled package as the
> `0001` coordinate and whose unary residuals align with the fixed chamber cancellation.

This theorem was a proposed way to close the fixed-package/two-shadow root without requiring full
median-fiber pair-status constancy.  At that stage it was unresolved, but it was a smaller
two-witness routing problem: one
offending positive mixed coordinate and one compensating negative mixed coordinate with full residual
alignment, rather than all coordinates of the peeled package at once.

## Thirteenth attack: mixed compensation versus raw compensation

The previous endpoint-mass target has a useful audit split.  Write any terminal row as

- `r = r(00) + h H + j J + m HJ`,

where `h,j` are the two unary increments and `m` is the mixed coefficient.  In this notation:

- `0001` has `(h,j,m)=(0,0,+1)`;
- `0111` has `(h,j,m)=(1,1,-1)`.

So a `0111` row compensates a `0001` row only after the two unary increments `H,J` are also absorbed
by the fixed chamber/endpoint cancellation.  This explains why a bare `0001`--`0111` pair is not a
raw short packet: their mixed parts cancel, but their unary parts add.

Consequently the actual routing theorem has two layers.

1. **mixed compensator routing:** route a negative `0111` overlap into the same peeled package as the
   positive `0001` coordinate;
2. **unary-residual cancellation:** prove that the two unary increments of the routed `0111` overlap
   are already cancelled inside the same fixed chamber package (or else one of them gives a
   predecessor-side return / Section-`40` coalescence).

Only the conjunction gives a raw relation of total mass `<q`.  If mixed routing holds but unary
residual cancellation fails, the failure is not the old AND square; it is a **unary-leak boundary**:
one successor side of the compensating overlap has been routed into the offending package, but the
other carries a leftover one-coordinate defect.  By first-return minimality, a predecessor-side unary
leak shortens the clean corridor, and a coalesced successor leak is Section `40`; hence the irreducible
new subtarget is:

> **successor unary-leak routing.** In the first-return terminal square, a routed `0111` compensator
> for a `0001` coordinate cannot leave exactly one successor unary residual outside the common peeled
> package unless that residual successor edge coalesces into Section `40`.

Thus the live root is now the conjunction of mixed compensator routing and successor unary-leak
routing.  This is smaller and more accurate than "paired compensator routing" alone, and avoids the
false inference from mixed endpoint mass to a `40.16` raw short-packet relation.

## Fourteenth attack: unary leaks are single-shadow failures

The successor unary-leak target is not a new independent obstruction.  Suppose a `0111` compensator
has been mixed-routed to the same package as the offending `0001` coordinate at the common `11`
successor overlap, but one unary increment, say the `H`-increment at the `10` corner, is not aligned in
that package.  Freeze the other successor direction `J=0`.  The data on the edge `00 -> 10` are then:

- the ambient binary-cylinder membership for the `H` successor transport is present;
- the endpoint `10` has the required unary incidence for the compensator;
- but there is no fixed-frame point in the current peeled package realizing that unary incidence.

That is precisely the **single-shadow failure** from the two-shadow split: `Sh_H` is empty for the
one-corner transport after the visible median point has been forced.  If the one-corner
ambient-to-fixed lift is available, the unary increment aligns in the package.  If the lift attempt
coalesces, Section `40` closes it; if it runs through a predecessor-side return, the closest-return /
strip-transfer argument shortens the first-return square.

Consequently:

> **successor unary-leak routing = one-corner ambient-to-fixed lift**, modulo the already closed
> predecessor and Section-`40` coalesced exits.

The full-residual compensator theorem therefore has the exact dependency

`full residual compensation`
`= mixed compensator routing + one-corner ambient-to-fixed lift`.

This also explains why the previous "paired compensator" route did not break the equivalence loop:
the unary part of an `0111` compensator returns to the single-shadow half of the original
common-shadow theorem, while the mixed part is the two-shadow/package half.

## Fifteenth attack: the one-corner lift bottoms out at one square

The one-corner ambient-to-fixed lift is not a formal consequence of the data currently frozen on the
median fiber.  The minimal abstract countermodel is the four-point hidden square

- `m_00,m_10,m_01,m_11 in M_ρ`

with one witness/local fiber `a` satisfying

- `m_00,m_10,m_01 notin E_a`,
- `m_11 in E_a`.

All one-coordinate predecessor/persistence data seen from the lower corner are satisfied:

- the `H` edge has no increase at `J=0`;
- the `J` edge has no increase at `H=0`;
- all unary chamber walls can be held fixed on the lower three corners.

Yet the fixed lift fails exactly at the forced median point because incidence to the local fiber `a`
is not constant on `M_ρ`.  Thus no argument that uses only ambient binary-cylinder membership,
one-coordinate predecessor data, endpoint mass, or unary chamber components can prove the one-corner
lift.  The missing input is exactly the square-level sign law:

> **single-witness median-square sign law.** For every hidden `2`-face in the forced median fiber and
> every localized witness `a`, the mixed second difference
> `p_a(11)-p_a(10)-p_a(01)+p_a(00)` is nonpositive in the first-return successor orientation.

Equivalently, in the minimized clean-corridor form, the successor-side first-switch `0001` square
cannot occur.  This is the same atom as before, but now the audit is sharper: one-corner lift,
successor unary-leak routing, and full-residual compensator routing all require this sign law unless
the mixed compensator route supplies a separate same-package `0111` overlap with full unary
cancellation.

So the exact active fork is:

1. prove the single-witness median-square sign law directly; or
2. prove mixed compensator routing plus full unary-residual cancellation strongly enough to bypass the
   positive `0001` square.

No currently recorded Section-`40`, endpoint-mass, or chamber-component theorem supplies either fork
without adding this missing two-coordinate input.

## Sixteenth attack: fixed-witness Horn reduces the sign law to shared slack

The fixed-witness Horn/additive interval calculus does not prove the single-witness sign law; it
pinpoints the exact obstruction.

On a localized `2×2` repair square, fix one candidate/witness and inspect one affected degree row.
The two elementary repair directions contribute coefficients

- `a,b in {-1,0,1}`,

and the admissible interval for that row is one of

- `{0}`, `{0,1}`, `{-1,0}`.

The singleton corners are admissible precisely when `a` and `b` are individually allowed.  The fourth
corner fails only in the two same-sign saturation cases:

- `I={0,1}` and `a=b=1`, so the double corner has value `2`;
- `I={-1,0}` and `a=b=-1`, so the double corner has value `-2`.

Thus the `0001` sign-law failure is exactly **double same-sign slack-row saturation**: two independent
successor repairs spend the same one-unit slack of a retained row.  Equivalently, the sign law is the
local no-shared-slack theorem.

The no-shared-slack theorem has the already isolated split.

1. If the two saturated successor representatives coalesce after marking the slack row, Section
   `40.7`--`40.10` closes the same-trace / false-clone kernel.
2. If the marked support is clean (`alpha_S=beta_S=0`), the marked-add catalogue forces the rooted
   `K_3` branch and eliminates the noncoalesced `P_3/C_6` alternative.
3. If the marked support is dirty, the obstruction is exactly budget-one absorption `Abs(1)`: an
   anchor-supported unique-defect reanchor must create a completer or route an external breaker into
   Section `40`.

So the live sign-law theorem is now:

> **slack-row trace-coalescence / dirty-Abs(1) theorem.** In the first-return successor square, any
> double same-sign slack-row saturation either coalesces after marking the slack row, or lies in the
> dirty budget-one reanchor boundary and exits by the prime-shell cycle-breaker.

This does not close the proof; it identifies the only nonclean place where the sign law can fail.
The omni-saturated carrier repair removes the broad side-selection flaw inside dirty splits, but it
does not orient the singleton reanchor graph.  A pure one-defect reanchor edge is reversible; any
successful proof must still supply a prime-shell cycle-breaker or an equivalent orientation for this
budget-one reanchor graph.

The phrase "single-witness sign law" is slightly misleading at the irreducible endpoint.  A positive
`0001` coordinate picks one slack row `a`, but the double corner fails along the whole set

- `R := {r : r \text{ spends the same one-unit slack in both successor repairs}}`.

The exact low-set update applied to the two singleton corners gives `|R| ≡ 0 [MOD q]`.  Hence the
literal singleton failure `R={a}` is impossible; a surviving positive coordinate must be accompanied by
an entire q-marker of parallel shared-slack rows.  Thus a pointwise proof of the sign law can succeed
only if it proves that first-return minimality makes `R` sub-`q` (or routes a proper submarker to
Section `40`).  This is the same carrier/marker coupling issue in its most local form: the chosen
witness coordinate identifies one member of `R`, while the congruence sees only the whole marker.

In dependency form:

`single-witness median-square sign`
`<=> no shared slack row`
`<=> slack-row trace-coalescence + dirty Abs(1)`
`<=> prime-shell budget-one reanchor cycle-breaker`.

The current active blocker is therefore the **prime-shell budget-one cycle-breaker**, not fixed-witness
degree calculus.

## Seventeenth attack: compensators do not bypass dirty Abs(1)

The mixed-compensator route is not an independent escape from the sign-law blocker unless it also
solves the same unary residual routing problem.

For one endpoint coordinate write the row type as

- `0001`: `(H,J,M)=(0,0,+1)`;
- `0111`: `(H,J,M)=(1,1,-1)`.

Endpoint mass can pair the mixed coefficients `+1` and `-1`, but after the mixed terms cancel the
`0111` row leaves two successor unary increments.  To become a raw Section-`40.16` relation in one
peeled package, those unary increments must be absorbed in the same fixed residual frame.  If one
unary increment is outside the package, the compensator has only been routed on one side; the other
side is exactly a one-corner fixed-frame shadow failure.

That failure is the same double-spend geometry as the sign law.  After marking the routed successor
overlap, the leaked unary increment is a one-unit slack row used by the compensator side but not by
the `0001` side.  If the marked representatives coalesce, Section `40` closes.  If the support is
clean, the marked-add catalogue closes.  If neither happens, the leaked unary row is a dirty
budget-one reanchor edge: a singleton swap is compatible and reversible, but it does not create a
completer or a raw same-package relation.

Therefore:

`full-residual compensator routing`
`= mixed 0001/0111 pairing + unary residual absorption`
`= mixed pairing + dirty Abs(1) / prime-shell cycle-breaker`.

So the only genuine bypass would be a compensator theorem that routes both unary increments into the
same package without using one-corner shadow lifting.  In the present proof surface that is exactly
the prime-shell budget-one cycle-breaker again.  The pending `mixed-compensator-routing` branch is
therefore blocked by the same theorem, not a separate open lane.

## Eighteenth attack: same-defect reanchor turns close

The prime-shell cycle-breaker has one closed subcase.  Consider a non-backtracking singleton reanchor
walk and focus on a middle state

- `T = F union {u}`.

Let `p` be the vertex removed in the previous step and now outside `T`; it is the immediate reverse
one-defect at the current inserted vertex `u`.  Let `x` be the next forward one-defect.

If the next move also has defect `u`, then `p` and `x` have the same trace on all of `T`.

- In the miss case, both are complete to `L(T) \ {u}`, anticomplete to `T \ L(T)`, and miss `u`.
- In the add case, both are complete to `L(T)`, anticomplete to `(T \ L(T)) \ {u}`, and see `u`.

Thus a same-defect non-backtracking turn gives two distinct outside vertices with identical trace over
one peeled near-regular package.  If no outside vertex distinguishes them, they form a nontrivial
module in the prime shell.  If some outside vertex distinguishes them, this is exactly the same-trace
false-clone / shifted twin-breaker configuration closed by Consequence `40.10`, unless the
distinguisher is already a completer for `T`.  Hence same-defect turns cannot occur in an irreducible
prime-shell `Abs(1)` counterexample.

This closes the pure isolated-token cycle model: every step in that model uses the current token as
the next defect, so any non-backtracking cycle contains a same-defect turn and is killed by the
same-trace Section-`40` closure.  The earlier raw countermodel fails exactly because it is non-prime;
after primeness supplies a distinguisher, the middle-state same-trace pair is already in one fixed
peeled package.

The remaining cycle-breaker is therefore sharper:

> **defect-switching shared-slack theorem.** In a shortest irreducible budget-one reanchor cycle,
> every surviving turn must switch to a different defect site.  Such a turn is not a token-cycle
> phenomenon; it is a two-defect singleton square.  If the square fills, the cycle shortens by
> commuting the two singleton reanchors.  If it does not fill, its missing corner is precisely the
> fully skew `0001` / double same-sign shared-slack square.

Consequently the prime-shell no-holonomy problem is no longer an arbitrary reanchor-cycle problem:

`prime-shell budget-one cycle-breaker`
`= defect-switching shared-slack square exclusion`.

The same-defect branch is closed; all remaining work is concentrated on the defect-switching square,
where two different repair fibers spend the same retained row's one-unit slack.

## Nineteenth attack: shortest cycles are first-return squares

The previous closure also removes all genuinely long cycle phenomena from `Abs(1)`.

Take a shortest non-backtracking reanchor cycle with no completer and no Section-`40` localization.
Write the directed edges as singleton swaps

- delete `d_i`,
- insert `x_i`.

Because same-defect turns are closed, every step after `i` avoids deleting the just-inserted vertex
`x_i`.  Since the cycle eventually returns to its starting peeled set, every inserted vertex is
deleted later.  Let `x_j` be the first inserted vertex that is ever deleted again, and let `k>j+1` be
the step deleting it.

Between steps `j+1` and `k-1`, the vertex `x_j` remains in the peeled set and no earlier inserted
vertex has returned.  Thus the corridor from the insertion of `x_j` to its deletion is clean in the
same sense as the one-corner closest-return reduction: all predecessor-side returns would contradict
the choice of `j,k`.

At the state immediately before step `k`, compare:

- the reverse singleton reanchor for the previous step, and
- the forward singleton reanchor deleting `x_j`.

Their defect sites are distinct, by the same-defect closure.  Hence they form a two-defect singleton
square.  If the fourth corner of this square is compatible, one can commute the forward deletion of
`x_j` across the previous step, obtaining an earlier return of `x_j` and contradicting the minimal
choice of `k`.  Therefore the fourth corner is not compatible.

By the fixed-witness Horn/additive interval calculation, a missing fourth corner for two individually
compatible singleton repairs is exactly double same-sign spending of one retained row's one-unit
slack.  In the hidden-square notation this is precisely the successor-side first-return `0001`
pattern.

So the cycle-breaker root has the exact normal form:

> In a shortest irreducible budget-one reanchor cycle, the first returning inserted vertex produces a
> clean-corridor defect-switching square; the cycle is irreducible if and only if that square is the
> fully skew shared-slack `0001` square.

This proves that there is no separate long-cycle obstruction left.  The remaining theorem is exactly
the first-return defect-switching square exclusion / single-witness median-square sign law.

## Twentieth attack: defect-switching square reduces to five-vertex seed packaging

The final defect-switching square has a very small local case table after the local marked/root-edge
failures have been removed.

Work in the `+` orientation; the `-` orientation is the complement.  Let

- `r` be the retained row whose one-unit slack is spent twice;
- `d,e` be the two deleted defect sites;
- `x,y` be the two inserted one-defect representatives.

Thus

- `r` is adjacent to `x,y`;
- `r` is nonadjacent to `d,e`.

Let `tau_d,tau_e in {0,1}` record the defect type:

- `tau=0` for a miss-type low defect;
- `tau=1` for an add-type high defect.

Then the one-defect trace rules give

- `x d = tau_d`, `x e = 1 - tau_e`;
- `y d = 1 - tau_d`, `y e = tau_e`.

The already-removed local marked/root-edge failures force the inserted-vertex degree tests in the
double corner to pass.  Comparing the degree of `x` in the `x`-singleton corner with the double corner
forces

- `x y = x e = 1 - tau_e`,

while comparing the degree of `y` in the `y`-singleton corner with the double corner forces

- `x y = y d = 1 - tau_d`.

Hence `tau_d=tau_e`.  A mixed miss/add defect-switching square cannot be the live fully skew square;
it would fail at an inserted-root degree test and is one of the local marked failures already removed.

So the two repairs have the same type.

### Same miss-type

Here `d,e in L(T)`, `x d = y e = 0`, and `x e = y d = 1`.  The inserted-root test gives `x y = 1`.
There are two possibilities for the internal edge `d e`.

1. If `d e = 0`, then
   - `d - y - x - e`
   is an induced `P_4`.
2. If `d e = 1`, then `d,y,x,e` form an induced `C_4`, and the slack row `r`, adjacent exactly to the
   adjacent pair `x,y` on that `C_4`, forms the standard house template.

Both alternatives are Section-`40` seed shapes once they are packaged into the appropriate fixed-fiber
or weighted-quotient attachment.

### Same add-type

Here `d,e in B(T)`, `x d = y e = 1`, and `x e = y d = 0`.  The inserted-root test gives `x y = 0`.
Again split on `d e`.

1. If `d e = 0`, then
   - `d - x - r - y - e`
   is an induced `P_5`.
2. If `d e = 1`, then
   - `d - x - r - y - e - d`
   is an induced `C_5`.

The `P_5` branch is the complement of the weighted-house branch, and the `C_5` seed is eliminated in
the prime weighted quotient split before Consequence `40.12`, again once the seed is packaged as a
quotient attachment.

Therefore every defect-switching shared-slack square either:

1. has a coalesced successor edge and is closed by Section `40.7`--`40.10`;
2. has a clean/local marked-root failure and is closed by the marked-add catalogue; or
3. has same-type inserted roots and yields one of the five-vertex seed templates above.

At this stage this did not prove the defect-switching shared-slack square exclusion.  The missing
bridge was:

> **five-vertex seed-packaging theorem.** The `P_4`, `P_5`, `C_5`, or house seed produced by a
> first-return defect-switching shared-slack square is not merely an induced local pattern; it lies in
> one fixed-fiber / prime weighted-quotient attachment satisfying the modular weighted-degree
> hypotheses of Section `40`.

Once that packaging theorem is supplied, Section `40.11`--`40.12` closes the defect-switching square,
and then the prime-shell budget-one cycle-breaker closes.  Without it, the five-vertex case table is
only a reduction, not a proof.

## Twenty-first attack: seed packaging reduces to residue homogenization

Auditing the five-vertex packaging step shows that the combinatorial frame is already present, but
the modular residue frame is not automatic.

In the defect-switching square, all five relevant vertices are in one peeled package in the following
limited sense:

- `d,e,r in T`;
- `x,y in O_1(T)`;
- all adjacencies from `x,y` to `T \ {d,e,r}` are fixed by the one-defect trace rules;
- all adjacencies among `d,e,r,x,y` are fixed by the five-vertex table above, after local
  marked/root-edge failures are removed.

Thus there is no remaining **combinatorial** ambiguity about the seed.  The obstruction is that
Section `40.11`--`40.12` is a theorem about prime weighted quotients whose bags satisfy one modular
weighted-degree equation

- `rho_i + sum_{j~i} n_j ≡ lambda [MOD q]`,

whereas the current peeled package is only near-regular:

- vertices of `B(T)` have residue `delta`;
- vertices of `L(T)` have residue `delta - 1`.

The missing unit is exactly the low-set correction `1_{L(T)}`.  A genuine completer would provide it,
because a vertex `h` with `N(h) cap T = L(T)` raises precisely the low rows and turns `T union {h}`
into a modular `q^2`-vertex host.  But using such an `h` is circular: completer existence is the host
theorem being proved.

Therefore five-vertex seed packaging is equivalent to a smaller residue statement:

> **local residue-homogenizer theorem.** For the first-return defect-switching seed
> `S={d,e,r,x,y}`, the low-set correction restricted to the seed and to every seed-preserving outside
> attachment is realized inside the same fixed-fiber / weighted-quotient closure without assuming a
> global completer.

In practical terms, the five-vertex table must be upgraded from:

- "the induced seed is `P_4`, `P_5`, `C_5`, or house"

to:

- "the seed together with its first-return outside attachment classes satisfies the Section-`40`
  modular weighted-degree equations after the low/high residue shift is internalized."

At this stage this was strictly smaller than the previous packaging theorem.  The next section
sharpens it: the low-set update forces a marked two-class quartet before a separate residue
homogenizer is needed.

## Twenty-second attack: low-set update reduces the defect-switching square

The residue-homogenizer obstruction above sharpens.  The exact singleton reanchor low-set update
forces a marked two-class quartet, but a separate localization step is still required before any
Section-`40` closure can be invoked.

Work at the middle peeled state `T`, with low set `L=L(T)` and high part `B=T\L`.  Let the two
singleton repairs be

- delete `d`, insert `x`;
- delete `e`, insert `y`;

and let `R subseteq L` be the nonempty set of retained slack rows spent by both singleton repairs in
the positive orientation.  Thus for every `r in R`,

- `r` misses `d,e`;
- `r` sees `x,y`;

and the double corner fails exactly along the marked shared-slack set `R`.  The earlier "one row"
form is the special case `|R|=1`; marking all of `R` avoids assuming uniqueness of the failed row.

The mixed miss/add case was already removed by the inserted-root tests.  So the two defects have the
same type.

### Miss/miss

Here `d,e in L`, `x` is miss-type at `d`, and `y` is miss-type at `e` in the original state:

- `N_T(x)=L\{d}`;
- `N_T(y)=L\{e}`.

After swapping `d` for `x`, the exact low-set update is

- `L_x={x} union (N_T(d)\setminus {d})`.

Since the final double corner is allowed to fail only along the shared-slack set `R`, the next
insertion `y` must have the miss-type trace at `e` relative to `L_x`, with the extra forbidden
neighbors `R`.  Since every row of `R` misses `d`, none lies in `L_x`.
Thus

- `N_{T-d+x}(y) = (L_x\{e}) union R`.

But directly from the original miss trace and `xy=1`,

- `N_{T-d+x}(y) = {x} union (L\{d,e})`.

Comparing the two displays gives:

- `e in N_T(d)`;
- `N_T(d)\setminus {d,e} = L\( {d,e} union R )`.

So `d` sees exactly the old low vertices outside `{d} union R`, sees `e`, and sees no high vertex.
By symmetry, the same statement holds for `e`.  Hence `d` and `e` have the same trace on

- `T\{d,e}` together with the marked slack set `R`

(both miss every row of `R` and both see precisely `L\( {d,e} union R )` outside the pair).

The inserted vertices distinguish this same-trace pair:

- `x` misses `d` and sees `e`;
- `y` sees `d` and misses `e`.

Moreover, `x` and `y` have the same trace on `T\{d,e}` and differ from the trace of `{d,e}` exactly
on the marker `R`; the induced graph on `{d,e,x,y}` is the balanced `C_4` with cycle
`d-e-x-y-d`.  This is not yet the Section-`40.10` same-trace `P_3`: the distinguishers have not been
shown to lie in the same residual trace class as `d,e`, and the marked frame has not been frozen as a
Section-`40` residual fixed fiber.

### Add/add

Here `d,e in B`, `x` is add-type at `d`, and `y` is add-type at `e`:

- `N_T(x)=L union {d}`;
- `N_T(y)=L union {e}`.

After swapping `d` for `x`, the exact low-set update is

- `L_x=N_T(d)\setminus {d}`.

Again the double corner may fail only along `R`, so relative to `L_x`, the vertex `y` has the
add-type trace at `e` plus the extra forbidden neighbors `R`.  Since every row of `R` misses `d`,
none lies in `L_x`:

- `N_{T-d+x}(y)=L_x union {e} union R`.

But directly,

- `N_{T-d+x}(y)=L union {e}`.

Therefore

- `N_T(d)\setminus {d}=L\R`.

In particular `d` misses `e`, misses every slack row in `R`, sees every other low vertex, and sees no
high vertex.  Symmetrically,

- `N_T(e)\setminus {e}=L\R`.

Thus `d` and `e` again have the same marked trace after `R` is included in the frame, while `x,y`
form the complementary same-trace pair; the induced graph on `{d,e,x,y}` is the balanced `2K_2`.
As in the miss/miss case, this is a marked two-class quartet, not yet a Section-`40` residual fixed
fiber or a same-trace `P_3`.

Hence the defect-switching shared-slack square is reduced to a marked two-class localization theorem,
not eliminated outright.  The remaining target is to route the marked quartet into one residual fixed
fiber / Section-`40` or Section-`40.16` frame, or to extract a completer or closed weighted quotient
seed directly.

There is one additional exact constraint.  Each singleton reanchor is again an anchored near-regular
state with the same residue `delta`, so its low set must still have size congruent to `delta` modulo
`q`.  In both the miss/miss and add/add calculations above,

- `|L_x| = |L| - |R|`;
- symmetrically, `|L_y| = |L| - |R|`.

Since also `|L| congruent delta [MOD q]`, any surviving shared-slack marker satisfies

- `|R| congruent 0 [MOD q]`.

Thus every marked two-class obstruction with `0 < |R| < q` is impossible.  The only possible survivor
would be a **q-marker** obstruction: the marker has size at least `q`, and the low-set congruence
alone cannot trigger `40.16`, whose short-packet rigidity is strictly sub-`q`.

The attempted q-marker closure is as follows.  Choose an irreducible q-marker obstruction with `|R|`
minimal.  If some outside vertex `z` is nonconstant on `R`, split

- `R_1=N(z) cap R`,
- `R_0=R\R_1`.

Apply the omni-saturated dirty-split theorem to the trace-refinement carrier whose
dirty coordinate is `z|_R` and whose active data are the two trace classes `{d,e}` and `{x,y}`.  The
coalesced and clean exits are already Section-`40` / marked-add closures.  If the preserved-side
alternative holds, one side `R_i` carries the same active two-class first-return marker; running the
same low-set update on that first-return boundary gives a new shared-slack marker `R_i`.

But `0<|R_i|<|R|`, and the low-set congruence just proved applies to every such first-return marker,
so `|R_i|` is again a positive multiple of `q`.  This contradicts the minimal choice of `R`.

At this point in the reduction, the fully skew alternative was still unresolved.  In the proof of the omni-saturated dirty-split theorem, a
no-preserved-side split has a connected active component whose bipartition sides are modules unless
they are singletons.  In a prime minimal carrier both sides are therefore singletons.  This proves only
that the **active crossing component** is binary.  It does not bound the number of slack rows in the
marker: those rows are retained low vertices that all miss the deleted defects and see the inserted
vertices, and many such rows can remain parallel to the same binary crossing component.

Therefore the low-set congruence does not contradict the fully skew branch.  What is still needed is
to couple the active binary crossing component to the slack marker itself: either a provenance
splitter must produce a proper first-return marker inside one side of `R`, or every relevant
first-return/provenance row must be shown constant on `R` in a way that forces a genuine prime-shell
module or a closed local exit.

Combining:

1. same-defect reanchor turns are closed;
2. shortest reanchor cycles reduce to first-return defect-switching squares;
3. defect-switching squares reduce by the low-set update to q-marker carrier/marker coupling;

the prime-shell budget-one cycle-breaker depended on q-marker carrier/marker coupling.
The final product-firewall transport closure above supplies this coupling.

## Twenty-third attack: weighted carry audit

The dyadic weighted endpoint adds orbit multiplicities, but no new local geometry.

The reduction above is pointwise on the support:

- choose a representative dirty primitive boundary;
- mark the entire shared-slack set `R`;
- the singleton low-set update forces `{d,e}` and `{x,y}` to be two same-trace pairs separated only by
  the marked slack set `R`;
- q-marker carrier/marker coupling is still needed to close the remaining marked two-class kernel.

No step uses that the boundary has coefficient `1`; weights only repeat the same marked trace class.
If a weighted two-child primitive carry survived, some support representative of its first
nonhomogeneous dirty boundary would be exactly the host-local defect-switching shared-slack square.
The pointwise reduction sends that representative to the same q-marker carrier/marker coupling problem
before the orbit weights are summed.

Thus weighted mixed-trace splitting and the aggregate dyadic class `beta_m=0` remain conditional.

## Final proof audit correction

The earlier audit below identified the only missing local input as q-marker carrier/marker coupling.
The split-quotient exhaustion and sub-`q` transport trap above now supply that input for the tracked
endpoint.

The low-set-update argument proves a strong reduction:

1. same-defect reanchor turns are closed;
2. shortest reanchor cycles reduce to first-return defect-switching squares;
3. every such square yields a marked two-class quartet: two same-trace pairs separated exactly by a
   shared-slack marker `R` with `|R|` a positive multiple of `q`.

The low-set update proves a strong reduction, and the q-marker congruence removes all sub-`q` markers.
It also shows that the no-split q-marker case is impossible by primeness and that any preserved-side
split contradicts marker minimality.  The fully skew splitter branch is now removed as follows: finite
packet arithmetic reduces it to the product firewall; if a high-error ambient packet breaker failed to
transport into the first-return boundary family, the square-breaker reduction would produce a dirty
shared-slack marker inside one side of a proper packet of size `<q`, contradicting the same low-set
congruence.  Therefore the prime-shell budget-one cycle-breaker, single-witness sign law, one-corner
lift, compensator routing, dyadic carry handoff, and global bridge implications are no longer blocked
by q-marker carrier/marker coupling in this note framework.

## Seventh attack: AND square equals dirty shared-slack

The positive AND square is the same object as the double same-sign slack-row saturation after unary
terms are subtracted.  In the `+` orientation, the witness row `a` is the retained row with one unit
of slack.  The two hidden successor moves are individually allowed because each spends that slack
once, while the `11` corner spends it twice.  The function

- `p_a(ij)=1_{m_{ij}~a}`

records exactly that saturation: the mixed increment is zero on both singleton moves and positive
only on the double move.  The `-` orientation is the complement.

Therefore all earlier no-shared-slack reductions apply verbatim:

1. if the two saturated successor representatives coalesce after marking the slack row, Section `40`
   gives the same-trace / false-clone contradiction;
2. in the clean support case `alpha_S=beta_S=0`, the marked-add catalogue forces the coalesced
   rooted `K_3` branch and eliminates the noncoalesced `P_3/C_6` alternative;
3. every surviving fully skew AND square is necessarily the dirty budget-one boundary of the
   anchor-supported unique-defect problem.

Thus the successor-side `0001` atom, the fully skew positive AND square, the nonclean shared-slack
anti-Horn obstruction, and budget-one absorption `Abs(1)` are equivalent at this frontier.  At this
stage the proof package did not close the atom because singleton reanchors are involutive: the deleted
defect is the immediate reverse move, so the miss/add sign is an undirected edge label and gives no
descent.  The q-marker localization audit above does not yet supply the missing no-holonomy step: it
removes sub-`q`, no-split, and preserved-side marker branches, but leaves the fully skew
carrier/marker coupling theorem open.

The exact remaining theorem can be stated in the most economical form:

> **dirty shared-slack absorption / prime no-holonomy.** A prime shell-local, anchor-supported
> unique-defect reanchor graph has no non-backtracking cycle all of whose boundary slack rows remain
> fully skew; equivalently some boundary either gives a completer or localizes to Section `40`.

This is not a Hall-capacity statement and not a raw short-packet statement.  The raw statement is
false in the isolated-token model; primeness must supply the external distinguisher and then one must
route that distinguisher into a fixed-fiber Section `40` kernel or into a completer-producing
reanchor.

## Eighth attack: the equivalence loop closes to one theorem

The prime no-holonomy route does not create a second independent endpoint.  It returns to the
original trace-refinement gap, but now with all inessential branches removed.

Starting from a dirty shared-slack cycle, primeness gives an external boundary distinguisher for two
consecutive reanchor tokens.  If the distinguisher has completer trace, the walk exits.  If it
coalesces with the token pair after marking, Section `40` closes it.  If the marked support is clean,
the marked-add catalogue closes it.  The only survivor is therefore a dirty mixed-trace boundary row
that separates the active token pair and remains transverse after reanchoring.

At that point the old failed-row descent would split the active trace class by the dirty row.  The
only missing assertion is:

> **dirty split active-pair preservation.** In the minimal dirty mixed-trace boundary, one side of the
> dirty split still contains a valid active repair/reanchor pair in the same obstruction category; if
> neither side does, the boundary itself localizes to Section `40` or to the fully skew positive AND
> square.

But the fully skew positive AND square has just been identified with the same dirty shared-slack
boundary.  Thus the current frontier is a closed equivalence loop:

`dirty split active-pair preservation`
`<=>` `mixed-trace breaker admissibility`
`<=>` `dirty shared-slack absorption / Abs(1)`
`<=>` `successor-side 0001 exclusion`
`<=>` `binary pair-status constancy`
`<=>` `common discrepancy packaging`
`<=>` `balanced flip quartet exclusion`
`<=>` `oriented two-row holonomy`
`<=>` `binary trace-coalescence / pair-chamber hidden-choice`.

This is useful but not a proof.  Later reductions below sharpen the genuinely new theorem from
active-pair preservation/no fully skew square to the five-vertex seed-packaging theorem for the
first-return defect-switching square.  Endpoint parity, unary chamber data, Hall capacity, raw
short-packets, and Section `40` same-trace closure each handle one face of the loop, but none by
itself supplies that final packaging step.

## Ninth attack: omni-saturated carriers close the split disjunction

One part of the last paragraph can be improved.  The terminal-module objection to the old
trace-refinement proof disappears if the carrier is saturated against all outside rows that preserve
an active edge, not only against rows already encountered along one failed-row orbit.

Choose a counterexample with `(C,A(C))` minimal as follows.  The vertices of `C` have the same frozen
trace, and `A(C)` is the graph of active repair/reanchor pairs in the same obstruction category.
Minimize first `|C|`, then the multiset of trace-class sizes, among all restrictions obtained by
adding any outside incidence row for which one fiber still contains an active edge.  Fixed-trace
rows, clean marked rows, and admissible/completer rows are already removed by Section `40`, the
marked-add catalogue, and the completer exit respectively.

Then every outside row `z` in a minimal unresolved carrier has only two possibilities:

1. `z` is constant on `C`;
2. `z` separates every edge of `A(C)`.

Indeed, if `z` were nonconstant and some fiber of `z|_C` contained an active edge, that fiber would
be a smaller carrier in the same obstruction category, contrary to omni-minimality.  This is exactly
the preservation assertion needed for the descent; it is built into the choice of carrier rather than
chosen after the dirty row is seen.

Now suppose a dirty split `C=C_0\sqcup C_1` contains no active edge on either side.  Work in one
connected component `H` of `A(C)`.  Every nonconstant outside row is a proper `2`-coloring of `H`,
and hence is constant on the two bipartition classes of `H` up to complement.  Therefore two vertices
on the same side of the bipartition are indistinguishable by every outside row.  If an internal
same-trace row distinguished them, it would be exactly the Section `40` same-trace /
false-clone internal-distinguisher kernel.  Hence each bipartition side is a module of the ambient
prime shell.  In a prime minimal carrier both sides are singletons.

Thus the no-preserved-side alternative in dirty split active-pair preservation is no longer a broad
case: it is forced to the binary crossing endpoint with one active pair `{x,y}`.  For the boundary
row and its first failed successor:

- if the successor coalesces with the boundary after the allowed marking, Section `40` closes it;
- if the marked support is clean, the marked-add catalogue closes it;
- otherwise the turn is the fully skew positive AND square / dirty shared-slack atom isolated above.

So the disjunctive dirty split theorem is proved:

> in an omni-saturated minimal carrier, a dirty split either preserves an active pair on one side, or
> localizes to Section `40`, or reduces to the fully skew positive AND square.

This does **not** prove the conjecture by itself.  Later reductions close same-defect turns and long
cycle holonomy and reduce the fully skew square to five-vertex seed packaging.  The omni-saturated
carrier argument only removes the separate terminal-module and active-pair-preservation objections
from the failed-row descent.

The resulting closure chain is:

1. the weighted-house analysis is now locally closed: Proposition `40.7` is repaired, and the
   false-clone shifted twin-breaker reduces back to that same `O_10` endpoint;
2. the named self-bridge target is **existential**: it asks only for some bounded exact
   single-control witness of size `q`, not for exactness on the distinguished terminal bucket `w`;
3. however, Section `10` of `remaining-gap-obstruction-module.md` needs a **genuine compatible
   size-`q^2` completion** `S` to produce such an existential witness, while the formal
   refinement-data input is only the package `∃ w s t ...`; in fact compatible completion from bare
   refinement data is false. The exact missing finite theorem is an anchored exact-`e` shell host
   theorem:
   - find `S` with `w ⊆ S ⊆ E_e(t)`, `|S| = q^2`, and all degrees in `G[S]` constant modulo `q`;
   - equivalently, in the shell graph `H := G[E_e(t)]`, find a mod-`q` regular `q^2`-vertex induced
     subgraph containing the anchor `w`;
   - peeling one non-anchor vertex gives an exact anchored mod-`q` near-regular completion theorem on
     `q^2 - 1` vertices inside `H`;
   - more sharply, for a fixed peeled set `T`, raw short packets of size `< q` are exact: a nonempty
     raw zero-packet exists if and only if every vertex in it is already a completer;
   - and the exact host-side frontier below that is simply **completer positivity** `c(T) > 0`,
     equivalently the existence of a weighted raw relation of total mass `< q`;
   - equivalently again, `c(T) > 0` is exactly the existence of some `U ⊆ O` with
     `e(L(T), U) - e(B(T), U) > (|L(T)| - 1) |U|` (a singleton `U = {x}` already suffices);
   - more sharply, if `Phi(U) := e(L(T), U) - e(B(T), U) - (|L(T)| - 1) |U|`, then
     `c(T) = max_{U ⊆ O} Phi(U)`;
   - because `U` is arbitrary, the putative one-error-strip theorem collapses to the **pointwise
     one-error witness** `∃ x in O, epsilon(x) <= 1`;
   - more sharply, one-defect witnesses carry a defect map `d : O_1 -> T`, and any witness with
     `d(x) notin w` swaps into `T` while preserving anchored near-regularity;
   - Hall already collapses pointwise: in the anchor-supported regime `h_T(Y) <= 0` for all
     `Y subseteq w` is equivalent to `mu(u) <= q - 1` on each anchor fiber;
   - on the one-defect strip `O_1`, raw discrepancies are diagonal: miss defects contribute `-e_z`
     and add defects `+e_y`, so there is no cross-fiber cancellation;
   - consequently any nontrivial weighted raw relation supported on `O_1` has total mass at least
     `q`, and in the anchor-supported regime `d(O_1) subseteq w`, `mu(u) <= q - 1` there is no
     nonempty raw zero-packet inside `O_1`;
   - exact injective-swap compatibility is now explicit in terms of the deleted defect set `D` and
     the internal degree pattern of the swap set `X`;
   - in that same anchor-supported regime no nonempty injective swap preserves the same anchor, so
     the residual theorem must re-anchor after the swap or produce a completer / full shell
     directly;
   - more sharply, singleton one-defect swaps are always compatible and simply re-anchor, but they
     are reversible and do not themselves create completers;
   - the exact residual host theorem is therefore **compatible-transversal positivity**: find a
     compatible re-anchor `X` with `c(T_X) > 0`;
   - for fixed deleted anchor set `D`, the old-shell trace is frozen and the only nonlinear datum
     left is the induced graph on a transversal `X subseteq d^(-1)(D)`;
   - more sharply, for fixed `D` positivity factors through the candidate set `C(D)`, and the pair
     case collapses completely to one edge bit on `X` plus one candidate bit;
   - equivalently, fixed-`D` positivity is a rooted semiregular transversal problem on `X ∪ {v}`;
     when `|D| < q`, the root degree is exact and parity-constrained;
   - more sharply, `|D| = 4` also collapses exactly: deleted candidates are ruled out by parity, and
     positivity is one of `11` explicit rooted `5`-vertex templates with an outside candidate; the
     `|D| = 5` case also collapses to `16` rooted `6`-vertex templates (`8` up to rooted
     complement), deleted candidates are rigid, and the only genuinely multi-template family is the
     balanced outside-candidate case `(m, r) = (2, 2)` up to complement, namely `C_6 / 2 K_3`
     dually prism / `K_(3,3)`;
   - more sharply, that balanced `|D| = 5` frontier is now a marked candidate-pair theorem:
     positivity is equivalent to an outside candidate hitting exactly the degree-`1` pair of a
     compatible `1^2 2^3` transversal, and the only remaining bit is whether that marked pair is an
     edge (`2 K_3`) or a nonedge (`C_6`);
   - more sharply still, the old-shell difference between the outside candidate and either marked
     vertex is frozen by sets `A(D), B_1(D)` with `|A(D)| ≡ |B_1(D)| [MOD q]`; equivalently the last
     balanced host bit is whether the three unmarked defect fibers admit a compatible
     `P_3`-transversal or `K_3`-transversal;
   - more sharply again, deleted-error values `1,2,3,4` recover exactly which deleted defects are
     marked/unmarked and add/miss, while the old-shell data are branch-blind; the whole remaining
     `|D| = 5` host gap is now a localization theorem, and once the unmarked triple localizes as a
     genuine `|D_R| = 3` candidate instance, Corollary `40.32` kills the `P_3` branch and leaves
     only the isolated-root `K_3 ⊔ K_1` case;
    - more sharply yet, failure of localization is now an explicit obstruction list: a marked miss
      defect, a low old vertex missing a marked defect, a `B_1(D)` vertex seeing a marked defect, a
      marked add defect with wrong `D_R`-degree / `v`-edge, or the single `|Lambda(D_R)|+|M_R|`
      congruence; only deleted one-error marked adds can mimic isolated roots;
    - more sharply still, the low-old half is automatic; after excluding marked misses, the entire
      host gap lives only on the two marked add-defects through the marked support of `A(D)` and
      `B_1(D)`, together with one reduced congruence `alpha_S - beta_S + sigma_1 + |M_R| ≢ 2`;
    - more sharply now, in the clean-support regime `alpha_S = beta_S = 0` the congruence is exact,
      and if both marked add-defects pass the local `deg_(D_R)` / `v`-edge test then the `P_3`
      branch collapses and `R ≅ K_3`; so any surviving `P_3` obstruction is already an explicit
      marked-fiber catalogue: marked miss, failed congruence, one of three local marked failures, or
      a nontrivial residue `alpha_S - beta_S + t ≡ 0` with `alpha_S + beta_S > 0`;
    - more sharply now, that residue family itself splits by the exact fold equation
      `alpha_S - beta_S + t = k q`; in the small-support window `alpha_S + beta_S < q - t` one must
      have `beta_S = alpha_S + t`, so `t = 0` forces the two-sided branch `alpha_S = beta_S > 0`,
      while one-sided obstructions occur only at the first residue layer from `40.42X`;
    - more sharply now, in the whole sub-`q` window the `B_1(D)`-heavy branch disappears entirely;
      the only one-sided atoms are `(0,1)`, `(0,2)`, `(q-1,0)`, `(q-2,0)`, and every other
      sub-`q` survivor lies on the exact two-sided ladder `beta_S = alpha_S + t`;
    - more sharply now, for fixed `t` the one-sided sub-`q` residues occur only at the two endpoint
      supports `t` and `q - t`, so each fixed-`t` branch is a finite support ladder; moreover the
      `A(D)`-side atoms force concentration on one marked defect, and the atom `(0,1)` is
      fiber-unique;
    - more sharply now, the atom `(0,2)` has only the two `B`-fiber profiles `(2,0)` or `(1,1)`,
      the first interior exact rung `s = t + 2` is already `A(D)`-fiber-unique, and `(q-2,0)` is
      either perfectly balanced across the two marked fibers or else has a unique dominant
      `A(D)`-fiber;
    - more sharply now, every exact rung with height `m = alpha_S` is a two-fiber partition with
      totals `m` on `A(D)` and `m + t` on `B_1(D)`; odd `m` or odd `m + t` already forces a unique
      dominant marked fiber, and the second exact rung `s = t + 4` is an explicit finite
      marked-fiber catalogue;
    - more sharply now, the third exact rung `s = t + 6` is also explicit, and parity reduces the
      whole sub-`q` exact ladder to the **even-even window**: only `t in {0, 2}` with even
      `alpha_S` still allows both marked-fiber sides to remain balanced;
    - more sharply now, the endpoint side is support-symmetric only in the two balanced profiles
      `(0,2)` with `B`-split `(1,1)` and `(q-2,0)` with `A`-split `(q/2-1,q/2-1)`, while each
      even-even exact rung leaves at most one fully balanced profile and the fourth rung `s = t + 8`
      is explicit;
    - more sharply now, those support-symmetric endpoint profiles occur only on the `t = 2` branch,
      and the sixth rung `s = t + 12` is explicit;
    - more sharply now, the eighth rung `s = t + 16` is explicit too; on any balanced exact rung each
      marked defect carries exactly half of the total old-shell residue, with local `B-A` excess
      equal to `t / 2`;
    - more sharply now, the tenth rung `s = t + 20` is explicit too, so the first unclassified
      support-symmetric exact rung is now `m = 12`; any remaining balanced exact case already forces
      `q >= 32`, and for `q = 16` the support-symmetric sub-`q` frontier is endpoint-only;
    - more sharply now, the twelfth rung `s = t + 24` is explicit too; on every balanced exact rung
      the two marked defects are numerically identical for all current local Section `40` data, so
      the first unclassified balanced exact rung is now `m = 14`;
    - more sharply now, the fourteenth rung `s = t + 28` is explicit too, so the first unclassified
      balanced exact rung is now `m = 16`; any still-unclassified balanced exact case already forces
      `q >= 64`, and for `q = 32` the support-symmetric sub-`q` frontier is the four-profile kernel
      consisting of the two balanced endpoint atoms together with the two height-`14` balanced exact
      profiles;
    - more sharply now, that `q = 32` four-profile list is itself a pure boundary kernel on the
      `t = 2` branch: every support-symmetric sub-`q` survivor has total marked support either `2`
      or `30 = q - t`, so there are no surviving `q = 32` cases in the strict interior window
      `alpha_S + beta_S < q - t`;
    - more sharply now, the boundary layer `alpha_S + beta_S = q - 2` is in exact normal form:
      a survivor there is either the balanced endpoint atom `(q-2,0)` or the unique top exact rung
      `(alpha_S,beta_S) = (q/2 - 2, q/2)`; in particular, every `q = 32` support-`30` non-endpoint
      survivor is the pair-rigid height-`14` balanced exact type with `A : (7,7)` and `B : (8,8)`,
      so no current local Section `40` invariant can distinguish the two marked defects;
    - more sharply now, once that boundary layer is normalized away, every still-unclassified balanced
      exact case already lies one rung deeper in the interior: on the `t = 2` exact ladder one has
      `alpha_S + beta_S = 2m + 2 ≡ 2 [MOD 4]`, so the next level `q - 4` cannot occur and every
      surviving unresolved case satisfies `alpha_S + beta_S <= q - 6`, equivalently
      `16 <= m <= q/2 - 4`; in particular, for `q = 64` only the heights
      `m ∈ {16,18,20,22,24,26,28}` remain;
    - more sharply now, on the unresolved balanced exact `t = 2` ladder one has
      `a := alpha_S + beta_S = 2m + 2 ≡ 2 [MOD 4]`; since any mixed `X/Y` realization forces
      `a <= q/2 - 1`, dyadic parity improves this to `a <= q/2 - 2`, equivalently
      `m <= q/4 - 2`, so every rung with `m >= q/4` is automatically pure-side;
    - consequently, for every dyadic `q >= 64`, the residual host frontier splits sharply into:
      boundary codimension `2` (endpoint atom or the unique pair-rigid top rung), possible mixed
      interior codimensions `>= q/2 + 2`, and pure-side interior codimensions
      `6 <= q - (alpha_S + beta_S) <= q/2 - 2` with `q - (alpha_S + beta_S) ≡ 2 [MOD 4]`; in
      particular, at `q = 64` the mixed window is empty, so the remaining codimensions
      `30,26,22,18,14,10,6` are all pure-side;
    - more sharply now, writing the residual codimension as `s := q - (alpha_S + beta_S)`, every
      pure-side rung (`6 <= s <= q/2 - 2`, `s ≡ 2 [MOD 4]`) has exact degree windows: if
      `A subseteq M` is an internal `alpha`-regular witness with `|A| = q - s`, then `Y`-side
      completion exists exactly for `0 <= alpha <= s - 1`, while `X`-side completion exists exactly
      for `q - 2s <= alpha <= q - s - 1`;
    - consequently, whenever `3s < q + 1` these windows are disjoint, so the side is already forced
      by `alpha` alone; for `q = 64` this makes codimensions `6,10,14,18` side-rigid, leaving
      overlap only at the pure-side codimensions `22,26,30` (besides the codimension-`2` boundary
      normal form);
    - more sharply now, these pure-side degree windows are complement-dual rather than genuinely two
      separate branches: writing `a := q - s`, if `A subseteq M` is induced `alpha`-regular on `a`
      vertices, then `overline{G[A]}` is `(a - 1 - alpha)`-regular, and this involution sends the
      exact `Y`-window `0 <= alpha <= s - 1` onto the exact `X`-window
      `q - 2s <= alpha <= q - s - 1`;
    - therefore every pure-side codimension is already normalized, up to global complement, by the
      sparse interval `0 <= alpha <= s - 1`; the dense `X`-side contributes no new branch once
      complement is allowed;
    - the genuinely two-sided issue is only the same-graph overlap strip
      `q - 2s <= alpha <= s - 1`, equivalently `3s >= q + 1`; modulo complement, these overlap
      classes have the exact normal form
      `q - 2s <= alpha <= floor((q - s - 1) / 2)`;
    - in particular, for `q = 64` the only normalized overlap profiles are `s = 22` with
      `alpha = 20`, `s = 26` with `12 <= alpha <= 18`, and `s = 30` with `4 <= alpha <= 16`,
      while `s = 6,10,14,18` are purely one-sided sparse-witness codimensions after
      complement-normalization;
    - more sharply now, the normalized pure-side overlap strip has a second exact normal form by the
      defect budget `h := 3s - q - 1`: if `A subseteq M` is induced `alpha`-regular on
      `a := q - s` vertices and lies in the normalized overlap strip
      `q - 2s <= alpha <= floor((q - s - 1) / 2)`, set `d_X := alpha - (q - 2s)` and
      `d_Y := s - 1 - alpha`; then `0 <= d_X <= d_Y`, `d_X + d_Y = h`, the pure `X`-side outside
      target is exactly `d_X`-regular on `s` vertices, and the pure `Y`-side outside target has
      complement exactly `d_Y`-regular on `s` vertices;
    - consequently, overlap is no longer best viewed as a dense/sparse side ambiguity: up to
      complement it is a pair of sparse defect graphs with total budget `h = 3s - q - 1`;
    - for dyadic `q`, the overlap codimensions are an arithmetic progression: if `q ≡ 4 [MOD 12]`
      then `s = (q + 2)/3 + 4j` and `h = 1 + 12j`, while if `q ≡ 8 [MOD 12]` then
      `s = (q + 10)/3 + 4j` and `h = 9 + 12j`; so the overlap frontier lives only on every fourth
      codimension rung, and the defect budget jumps by `12` from one surviving rung to the next;
    - in particular, for `q = 64` the first normalized overlap rung is uniquely
      `(s, alpha) = (22, 20)`, which in defect-budget coordinates is `(d_X, d_Y) = (0, 1)`: the
      pure `X`-side outside target is an independent `22`-set, while the pure `Y`-side outside
      target is `K_22` minus a perfect matching;
    - therefore the codimension-`22` profile at `q = 64` is not a genuinely higher-order multi-swap
      case: it already sits on the anchor-supported unique-defect / one-defect boundary; after
      removing that rung, the genuinely higher-budget `q = 64` overlap kernel is only `s = 26`
      with `h = 13` and `s = 30` with `h = 25`, besides the codimension-`2` boundary normal form;
    - more sharply now, the defect budget already truncates the overlap ladder exactly: for dyadic
      `q`, if `q ≡ 4 [MOD 12]` then every overlap codimension has the form `s = (q + 2)/3 + 4r`
      with budget `h = 1 + 12r`, while if `q ≡ 8 [MOD 12]` then every overlap codimension has the
      form `s = (q + 10)/3 + 4r` with budget `h = 9 + 12r`; thus `h` is strictly increasing in `s`
      and rises by `12` from one surviving overlap rung to the next;
    - consequently, on the `q ≡ 4 [MOD 12]` branch the one-defect edge is isolated: every
      higher-order overlap already satisfies `s >= (q + 14)/3`, equivalently `a = q - s <= (2q - 14)/3`;
    - equivalently, the next exact host theorem should be phrased as a budget-absorption theorem:
      any anchor-supported unique-defect / compatible multi-swap result that absorbs all normalized
      defect packages up to budget `H` removes every pure-side overlap rung with `h <= H`;
    - in particular, for `q = 64` a budget-`13` absorption theorem removes the entire `s = 26`
      rung, and budget `25` removes the whole pure-side interior, leaving only the codimension-`2`
      boundary normal form;
    - more sharply now, this budget view is already exact on the whole pure-side frontier: if
      `Abs(H)` denotes the anchor-supported statement that every complement-normalized pure-side
      defect package with total budget `d_X + d_Y <= H` admits a compatible re-anchor `X` with
      `c(T_X) > 0`, then every pure-side overlap rung with `h(s) := 3s - q - 1 <= H` disappears;
    - since `h(s)` is strictly increasing in `s`, the maximal pure-side budget is
      `h_max = 3(q/2 - 2) - q - 1 = q/2 - 7`, attained at the top interior codimension
      `s = q/2 - 2`; therefore `Abs(q/2 - 7)` removes the whole pure-side interior for every dyadic
      `q`;
    - for `q = 64`, the only higher-order overlap kernels after the isolated one-defect rung
      `s = 22` are exactly `s = 26` with budget `13` and `s = 30` with budget `25`; hence
      `Abs(13)` kills the whole `s = 26` rung, while `Abs(25)` leaves only the codimension-`2`
      boundary normal form;
    - equivalently, below codimension `2` the `q = 64` host problem is the exact finite absorption
      problem on the `20` normalized defect pairs `(26,d,13-d)` for `0 <= d <= 6` and
      `(30,d,25-d)` for `0 <= d <= 12`, with the isolated pair `(22,0,1)` already belonging to the
      unique-defect boundary theory;
    - more sharply now, the budget-`13` rung already collapses to a single exact balanced packet:
      `s = 26` means `a = q - s = 38 = 2m + 2`, hence `m = 18`, so this is the height-`18` rung on
      the unresolved balanced exact `t = 2` ladder;
    - the normalized `h = 13` family is exactly the `7` defect pairs `(26,d,13-d)` for
      `0 <= d <= 6`, and because every even-even exact rung carries at most one fully balanced
      profile, the unique central pair `(26,6,7)` is the only genuinely new balanced packet; the
      other `6` pairs are imbalanced dominant-fiber cases;
    - equivalently, `Abs(13)` is no longer a `7`-profile problem: it is exactly the pair-rigid
      two-defect compatible-re-anchor theorem for the balanced packet `(26,6,7)`;
    - more sharply now, at `q = 64` the top pure-side rung `s = 30` is exactly the height-`m = 16`
      rung on the unresolved `t = 2` exact ladder, and the earlier marked-fiber analysis says that
      every even-even exact rung carries at most one fully balanced profile; therefore among the
      `13` normalized defect pairs `(30,d,25-d)` only the central pair `(30,12,13)` is genuinely
      new balanced multi-swap content, while the other `12` are imbalanced dominant-fiber cases;
    - more sharply now, on the balanced exact `t = 2` ladder with height `m` one has
      `a = 2m + 2`, `s = q - a = 62 - 2m`, and balanced coordinate `alpha = m`; therefore
      `d_X = alpha - (64 - 2s) = 60 - 3m` and `d_Y = s - 1 - alpha = 61 - 3m`, so the two
      surviving `q = 64` balanced packets are exactly the height instances
      `m = 16 -> (30,12,13)` and `m = 18 -> (26,6,7)`;
    - more sharply now, every balanced rung is pair-rigid on the marked defects: the marked support
      splits as `A : (m/2,m/2)` and `B : (m/2+1,m/2+1)`, so `(30,12,13)` has
      `A : (8,8), B : (9,9)` while `(26,6,7)` has `A : (9,9), B : (10,10)`;
    - equivalently, `(30,12,13)` is exactly one balanced four-vertex ladder step below `(26,6,7)`;
      the only genuinely new top-rung move is a compatible balanced `+4` reroot carrying
      `A : (8,8), B : (9,9)` to `A : (9,9), B : (10,10)`;
    - more sharply now, that balanced `+4` reroot is exactly a compatible injective four-swap in the
      one-defect layer: there must exist `X subseteq O_1` with `|X| = 4`, `d|_X` injective,
      `d(X)` equal to the four marked coordinates, and `(T \ d(X)) ⊔ X` still anchored near-regular;
    - more sharply now, the tracked host machinery already isolates the exact theorem shape:
      Propositions `40.14`–`40.16` reduce everything to `c(T) > 0`, anchored one-defect escape
      forces irreducible cases into the anchor-supported regime `d(O_1) subseteq w`, and Hall then
      collapses to the pointwise bounds `mu(u) <= q - 1`; so `Abs(H)` is exactly a
      compatible-transversal positivity theorem on anchor-supported injective layers;
    - consequently, after the isolated one-defect edge `(22,0,1)` the height-`16` packet
      `(30,12,13)` is no longer an independent direct positivity problem: it is exactly the local
      balanced `+4` reroot theorem from `A : (8,8), B : (9,9)` to `A : (9,9), B : (10,10)`;
    - once that local `+4` move is proved, every height-`16` support-symmetric instance funnels into
      the single budget-`13` packet `(26,6,7)`, so the only irreducible direct positivity packet
      left at `q = 64` is `(26,6,7)`;
    - more sharply now, the localized balanced marked candidate-pair / isolated-root `K_3 ⊔ K_1`
      obstruction is already a rooted `2 K_3` normal form: adjoining the compatible outside root to
      the degree-`1` pair of a `1^2 2^3` transversal gives a `2`-regular graph on `6` vertices, so
      only `C_6` or `2 K_3` can occur; once the unmarked triple is a genuine `|D_R| = 3` candidate
      instance, Corollary `40.32` removes the `P_3`/`C_6` branch, leaving only rooted `2 K_3`;
    - consequently, the exact `q = 64` host frontier is already a two-state rooted `2 K_3` ladder:
      the pair-rigid states `m = 16` with `A : (8,8), B : (9,9)` and `m = 18` with
      `A : (9,9), B : (10,10)`, related by the single local balanced `+4` reroot / injective
      four-swap step;
    - more sharply now, rooted `2 K_3` alone did not by itself prove the `m = 16 -> 18` step: rooted
      `2 K_3` is a local `|D| = 5` certificate on one marked pair plus one localized unmarked
      triple, whereas the balanced `+4` reroot needs one compatible one-defect vertex for **each**
      of the four marked coordinates simultaneously;
    - writing `w = {a_1,a_2,b_1,b_2}` for the four marked coordinates of the height-`16` state and
      `F_u := d^(-1)(u) subseteq O_1`, the promotion step is exactly the existence of a top face in
      the four-part promotion complex `K_prom(T)` on `⨆_{u in w} F_u`, whose faces are the compatible
      injective defect selections preserving anchored near-regularity;
    - therefore, after anchored one-defect escape and Hall collapse, failure of promotion is
      **exactly** the absence of a compatible four-part transversal in `K_prom(T)`; there is no
      remaining Hall/capacity obstruction beyond this compatibility complex;
    - more sharply now, because singleton one-defect swaps are always compatible, the exact local
      `m = 16` obstruction is the blocker clutter `B_prom(T)` of minimal incompatible partial
      transversals in `K_prom(T)`; every blocker has size `2`, `3`, or `4`, and promotion fails iff
      `B_prom(T)` meets every full transversal of the four fibers;
    - more sharply now, the exact `q = 64` host frontier is smaller than the
      certified-quartet/terminal split: it is one single two-state rooted `2 K_3`
      **one-step terminal certification** theorem;
    - after the current reductions, the only irreducible rooted `2 K_3` states are the pair-rigid
      balanced rungs `m = 16` with `A : (8,8), B : (9,9)` and `m = 18` with
      `A : (9,9), B : (10,10)`, and promotion from `m = 18` would create the next balanced rung
      `m = 20`, already excluded by the two-state ladder classification;
    - direct terminal audit shows that the height-`18` packet has no remaining global host
      obstruction, and pair-rigid symmetry plus rooted `2 K_3` localization remove all independent
      marked-local input: in the rooted `2 K_3` state `A : (9,9), B : (10,10)`, each marked
      coordinate is automatically a deleted one-error add defect satisfying the local
      `deg_(D_R)` / root-edge test, so `Cert'_18(T)` is equivalent to the scalar congruence alone
      `sigma_1 + |M_R| = 2`;
    - writing `eps_A(T_18), eps_B(T_18) in {0,1}` for whether the marked `A(D)`-side and
      `B_1(D)`-side deleted one-error add defects on the unique terminal rooted `2 K_3` rung
      `T_18` contribute to `M_R(T_18)`, one has
      `|M_R(T_18)| = eps_A(T_18) + eps_B(T_18)`, so the exact terminal content is the scalar
      evaluation theorem
      `sigma_1(T_18) + eps_A(T_18) + eps_B(T_18) = 2` on this single rooted local isomorphism type;
    - more sharply now, the precursor localized obstruction on `T_18` is already the isolated-root
      type `K_3 ⊔ K_1`, so the reduced `|Lambda(D_R)|` term contributes exactly one singleton:
      `sigma_1(T_18) = 1`;
    - consequently the terminal scalar theorem is equivalent to
      `eps_A(T_18) + eps_B(T_18) = 1`, i.e. exactly one of the two marked deleted one-error add
      defects contributes to `M_R(T_18)`;
    - however the present Section `40` / rooted `2 K_3` localization package is symmetric under
      swapping the pair-rigid marked defects, so it determines only the sum and not the side label;
      the exact irreducible terminal datum is the sign
      `δ_term(T_18) := eps_A(T_18) - eps_B(T_18) in {± 1}`;
    - on the nonterminal `m = 16` side, write `w = {a_1,a_2,b_1,b_2}` and
      `F_u := d^(-1)(u) subseteq O_1`; for a quartet
      `x = (x_(a_1),x_(a_2),x_(b_1),x_(b_2)) in Π_(u in w) F_u`, let
      `X := {x_(a_1),x_(a_2),x_(b_1),x_(b_2)}` and `T_X := (T \ w) ⊔ X`;
    - define the certified quartic predicate `Q_cert(T;x)` to mean that `X` is a compatible
      injective four-swap and the promoted state `T_X` satisfies `Cert'_18(T_X)`; equivalently the
      nonterminal obstruction is the emptiness of the certifying quartet set
      `Xi_16(T) := {x in Π_(u in w) F_u : Q_cert(T;x)}`;
    - the lower-arity part of the height-`16` obstruction is exact and finite:
      `B_prom(T)` has `6` binary two-fiber families and `4` ternary rooted-`2 K_3` families, so any
      genuinely new nonterminal obstruction is quartic; these lower-arity blockers only witness why
      `Xi_16(T)` is empty, not independent frontier pieces;
    - to isolate that quartic front exactly, write `P(T) := Π_(u in w) F_u`, let `Low(T)` be the
      union of the cylinders of the `6 + 4` lower-arity blocker families, and define the
      lower-arity-clean quartic region `Gamma_4(T) := P(T) \ Low(T)`;
    - split the full-support quartic failure set into
      `Omega_4^inc(T) := {x in Gamma_4(T) : x is not a face of K_prom(T)}` and
      `Omega_4^term(T) := {x in Gamma_4(T) : x is a face of K_prom(T) but T_X fails Cert'_18(T_X)}`,
      with `Omega_4(T) := Omega_4^inc(T) uu Omega_4^term(T)`;
    - to isolate the genuine quartic incompatibility stratum, let
      `B_4(T) := {x in Gamma_4(T) : x is a size-4 minimal blocker in B_prom(T)}`; then
      `Omega_4^inc(T) = B_4(T)`, so after removing all size-`2` and size-`3` blockers the only
      remaining incompatibility on the `m = 16` side is a quartic blocker;
    - fixing any coordinate `u in w`, every clean quartet is written uniquely as `(tau,y)` with
      `tau in Π_(v in w \ {u}) F_v`; defining the clean completion fiber
      `C_u(T;tau) := {y in F_u : (tau,y) in Gamma_4(T)}` and the good completion set
      `E_u(T;tau) := {y in C_u(T;tau) : (tau,y) notin B_4(T)}`, one has the exact sectionwise
      decomposition
      `Gamma_4(T) \ B_4(T) = ⨆_tau ({tau} × E_u(T;tau))`;
    - defining
      `Tri_u(T) := π_(w \ {u})(Gamma_4(T)) = {tau in Π_(v in w \ {u}) F_v : C_u(T;tau) != emptyset}`
      and the universally blocked triple set
      `Bad_u(T) := {tau in Tri_u(T) : E_u(T;tau) = emptyset}`,
      one has
      `π_(w \ {u})(Gamma_4(T) \ B_4(T)) = Tri_u(T) \ Bad_u(T)`;
    - consequently, the quartic-blocker noncover theorem is equivalent to the **triple noncover
      theorem** `Bad_u(T) != Tri_u(T)`; equivalently, for any fixed coordinate `u`, not every
      lower-arity-clean triple is universally blocked by quartic blockers along the missing fiber;
    - on the compatible quartic side, split terminal failure further into
      `Omega_4^sc(T) := {x in Gamma_4(T) : X is a face of K_prom(T), but sigma_1(T_X) + |M_R(T_X)| != 2}`
      and
      `Omega_4^mark(T) := {x in Gamma_4(T) : X is a face of K_prom(T), sigma_1(T_X) + |M_R(T_X)| = 2,
      but one/every marked coordinate of T_X fails the deleted one-error add-defect test}`;
    - because the promoted state `T_X` lies on the unique terminal rooted `2 K_3` rung and the
      marked local certificate is automatic there, `Omega_4^mark(T) = emptyset`; hence
      `Omega_4^term(T) = Omega_4^sc(T)` and
      `Xi_16(T) = Gamma_4(T) \ (B_4(T) uu Omega_4^sc(T))`;
    - moreover every lower-arity-clean quartet `x in Gamma_4(T) \ B_4(T)` promotes to the unique
      pair-rigid rooted `2 K_3` rung with `m = 18`, and the terminal scalar theorem is already
      settled there: `sigma_1(T_18) = 1` and `eps_A(T_18) + eps_B(T_18) = 1`; hence
      `Omega_4^sc(T) = emptyset` and
      `Xi_16(T) = Gamma_4(T) \ B_4(T)`;
    - in particular, the exact final host theorem is already the single **one-step terminal
      certification theorem**
      `host front empty <-> Xi_16(T_16) != emptyset`;
    - because the terminal scalar theorem is already settled on the unique `m = 18` rung, this is
      now a purely nonterminal statement:
      `Xi_16(T_16) != emptyset <-> Gamma_4(T_16) \ B_4(T_16) != emptyset
      <-> Tri_(b_1)(T_16) \ Bad_(b_1)(T_16) != emptyset
      <-> Bad_(b_1)(T_16) != Tri_(b_1)(T_16)` (equivalently for `b_2`);
    - thus the terminal side sign `δ_term(T_18) in {± 1}` is residual terminal information only; it
      no longer enters the host-closure theorem;
    - since `Bad_u(T) != Tri_u(T)` is equivalent for every coordinate, one may fix `u = b_1`
      (or symmetrically `u = b_2`), which minimizes the ambient triple universe to
      `F_(a_1) × F_(a_2) × F_(b_2)` of size `8 · 8 · 9 = 576`;
    - for `u in {b_1,b_2}` and `tau in Tri_u(T)`, defining the quartic blocker multiplicity
      `m_u(T;tau) := |{y in F_u : (tau,y) in B_4(T)}|`, one has
      `tau in Bad_u(T) <-> m_u(T;tau) = |C_u(T;tau)|`; so the exact last nonterminal obstruction is
      a fully saturated clean triple on the `B`-side;
    - more sharply, if `Bad_(b_1)(T) = Tri_(b_1)(T)`, finite descent in the `576`-point triple
      universe produces a **projection-minimal saturated clean triple system**
      `Sigma subseteq Tri_(b_1)(T)`: every `tau in Sigma` is fully saturated along `F_(b_1)`,
      each visible projection `π_(a_1)(Sigma)`, `π_(a_2)(Sigma)`, `π_(b_2)(Sigma)` has size at
      least `2`, and no proper subsystem with the same three projections remains saturated;
    - more sharply still, any such residual obstruction admits a corner normal form: one may choose
      `Sigma` so that
      `|π_(a_1)(Sigma)| = |π_(a_2)(Sigma)| = |π_(b_2)(Sigma)| = 2`, and after relabelling
      `π_(a_1)(Sigma) = {x_0,x_1}`, `π_(a_2)(Sigma) = {y_0,y_1}`, `π_(b_2)(Sigma) = {z_0,z_1}`,
      one has
      `Sigma = {(x_0,y_0,z_0), (x_1,y_0,z_1), (x_1,y_1,z_0)}`;
    - equivalently, if the host theorem fails then it already fails on a `2 × 2 × 2` visible box as
      a saturated three-edge `L`-corner, every one of whose triples is fully saturated along
      `F_(b_1)`;
    - writing `tau_0 := (x_0,y_0,z_0)`, `tau_1 := (x_1,y_0,z_1)`, `tau_2 := (x_1,y_1,z_0)` and
      `C(tau) := C_(b_1)(T;tau) subseteq F_(b_1)`, each trace `C(tau_i)` is nonempty and is
      completely blocked:
      `C(tau_i) = {u in F_(b_1) : (tau_i,u) in B_4(T)}`;
    - equivalently, the residual obstruction is the three-section blocker-cover incidence system
      `I_Sigma := {(tau,u) in Sigma × F_(b_1) : u in C(tau)}`, i.e. three left vertices on the
      single missing fiber `F_(b_1)`, each carrying only genuine size-`4` blockers;
    - Hall/capacity contributes no further contradiction here: anchored one-defect escape and the
      pointwise bounds `mu(u) <= q - 1` are already exhausted, so the remaining theorem is not a new
      Hall overload but a structural blocker-cover statement on the traces `C(tau_i)`;
    - moreover the common-root case is already excluded:
      `C(tau_0) nn C(tau_1) nn C(tau_2) = emptyset`; otherwise freezing a common `b_1`-root would
      produce a rooted ternary obstruction slice already removed in `Low(T)`;
    - in fact pairwise overlap is impossible as well: since `tau_0,tau_1` share `y_0`, any
      `u in C(tau_0) nn C(tau_1)` would freeze the binary slice
      `F_(a_1) × F_(b_2)` at `(a_2,b_1) = (y_0,u)`; similarly
      `u in C(tau_0) nn C(tau_2)` freezes `F_(a_1) × F_(a_2)` at `(b_2,b_1) = (z_0,u)`, and
      `u in C(tau_1) nn C(tau_2)` freezes `F_(a_2) × F_(b_2)` at `(a_1,b_1) = (x_1,u)`. All three
      are forbidden because `B_4(T) subseteq Gamma_4(T) = P(T) \ Low(T)` and `Low(T)` already
      contains the six binary blocker cylinders;
    - therefore
      `C(tau_0) nn C(tau_1) = C(tau_0) nn C(tau_2) = C(tau_1) nn C(tau_2) = emptyset`;
      equivalently, in the incidence system `I_Sigma` every right vertex of `F_(b_1)` has degree at
      most `1`;
    - hence every binary two-fiber cylinder and every rooted-ternary cylinder is completely silent on
      `B_Sigma := ⋃_(i=0)^2 ({tau_i} × C(tau_i))`: any such lower-arity family meets `B_Sigma` in at
      most one point, so all already-closed size-`2` and size-`3` obstruction mechanisms are absent
      on this residual packet;
    - equivalently, for any choice of roots `u_i in C(tau_i)`, the three quartets
      `x_i := (tau_i,u_i) in B_4(T)` form a **distributed quartic corner-packet**: their visible
      projection is exactly the `L`-corner `Sigma`, their `b_1`-roots are distinct, and no
      pair/triple among them lies in any already-removed lower-arity blocker family;
    - in particular, no two-root core exists: any root meeting two traces would recreate one of the
      forbidden shared-slice binary cylinders, so every minimal root support hitting all three traces
      has exactly size `3`;
    - therefore one may choose distinct roots `u_i in C(tau_i)` (`i = 0,1,2`) so that
      `q_i := (tau_i,u_i) in B_4(T)`, and every cross-transport already lands in `Low(T)`:
      for `i != j`, `(tau_j,u_i) notin Gamma_4(T)`;
    - more precisely, the six cross-transports are forced into the three shared binary cylinders:
      `(tau_1,u_0),(tau_0,u_1)` lie in the `F_(a_1) × F_(b_2)` low cylinder on the shared `y_0`
      slice; `(tau_2,u_0),(tau_0,u_2)` lie in the `F_(a_1) × F_(a_2)` low cylinder on the shared
      `z_0` slice; and `(tau_2,u_1),(tau_1,u_2)` lie in the `F_(a_2) × F_(b_2)` low cylinder on the
      shared `x_1` slice;
    - accordingly define the three binary compatibility relations
      `R_y subseteq C(tau_0) × C(tau_1)`, `R_z subseteq C(tau_0) × C(tau_2)`,
      `R_x subseteq C(tau_1) × C(tau_2)` by requiring membership in the corresponding shared binary
      low cylinders; then an exact three-root packet exists iff there are roots `u_i in C(tau_i)`
      with `(u_0,u_1) in R_y`, `(u_0,u_2) in R_z`, and `(u_1,u_2) in R_x`;
    - eliminating `u_0`, define the single composition obstruction
      `K := R_x nn (R_y^(-1) ∘ R_z) subseteq C(tau_1) × C(tau_2)`; then host failure is exactly
      `K != emptyset`, equivalently
      `R_y^(-1) ∘ R_z subseteq (C(tau_1) × C(tau_2)) \ R_x`
      is the exact host-closure statement (and cyclic permutations give the same theorem);
    - more finely, for each edge `e = (u_1,u_2) in R_x`, define the edge-completion fiber
      `K_0(e) := {u_0 in C(tau_0) : (u_0,u_1) in R_y and (u_0,u_2) in R_z}`; cyclically define
      `K_1` on `R_z` and `K_2` on `R_y`;
    - then host failure is equivalent to the existence of an edge with a nonempty completion fiber:
      some `e in R_x` satisfies `K_0(e) != emptyset` (equivalently cyclically for `K_1` and `K_2`);
    - thus the exact residual nonterminal obstruction is a **binary-slice triangle** on the saturated
      `L`-corner, i.e. a simultaneous realization of the three shared-binary transport constraints by
      three distinct roots;
    - the pairwise lower-arity data alone still do not forbid this triangle: in the abstract incidence
      model take three singleton traces `C(tau_i)={u_i}` and put
      `R_y={(u_0,u_1)}`, `R_z={(u_0,u_2)}`, `R_x={(u_1,u_2)}`. Then the traces are pairwise
      disjoint, every right vertex has degree `1` in `I_Sigma`, no binary or rooted-ternary
      lower-arity cylinder meets the packet in more than one point, yet
      `K=R_x nn (R_y^(-1)∘R_z)` is nonempty. Therefore anti-composition is not a formal consequence
      of lower-arity silence or pairwise trace disjointness; it is exactly the missing
      graph-specific gluing / cross-root transport theorem;
    - importantly, the existing packet-exchange / reseating machinery does not cross this endpoint:
      all previously proved exchange theorems are one-shadow / one-fiber arguments, whereas the
      residual host obstruction is intrinsically a three-trace cross-root triangle, with no single
      fixed fiber, no same-shadow packet pair, and no twin/module pair over a frozen frame;
    - the only surviving synchronizations are weak and pairwise: all three traces lie in the same
      ambient missing fiber `F_(b_1)`, and each pair of corner edges shares exactly one visible
      coordinate (`y_0`, `z_0`, or `x_1`), but these data do not globalize to one common frame or one
      common shadow; pairwise disjointness of the traces means no two roots can even be reseated into
      a single trace class;
    - likewise, the old localized `P_3/C_6` branch killed by Corollary `40.32` still sits one step
      away: a labelled `R_y/R_z/R_x` triangle reconstructs only a **distributed** three-root corner
      packet, not a single rooted `|D_R| = 3` candidate instance with one localized six-vertex graph;
      the current data record only shared-slice binary compatibilities between distinct roots;
    - more precisely, a labelled `R_y/R_z/R_x` triangle canonically produces a **distributed
      alternating hexagon** `H_hex(u_0,u_1,u_2)` on vertex classes
      `{tau_0,tau_1,tau_2}` and `{u_0,u_1,u_2}` whose six edges are exactly the forced
      cross-transports
      `tau_0u_1, tau_1u_0, tau_0u_2, tau_2u_0, tau_1u_2, tau_2u_1}`; equivalently
      `H_hex ≅ K_(3,3) \ {tau_0u_0, tau_1u_1, tau_2u_2} ≅ C_6`;
    - this distributed hexagon is in fact the **maximal synchronization presently available** from
      the existing notes: beyond the common ambient fiber `F_(b_1)` and the three pairwise shared
      visible coordinates, no current theorem upgrades the data to one common frame/shadow or to one
      rooted `|D_R| = 3` candidate instance;
    - so the residual host obstruction is **anchor-supported unique defects** together with one
      finite rooted `2 K_3` theorem `Xi_16(T_16) != emptyset`; equivalently, the exact unresolved
      local datum for host closure is the vanishing of all edge-completion fibers `K_i`, equivalently
      the composition obstruction `K`, i.e. an anti-composition / triangle-free theorem for the three
      shared-binary compatibility relations, or still more conceptually, that no exact three-root
      packet remains closed under all three pairwise slice exchanges simultaneously. The missing
      ingredient is therefore a genuinely new **gluing lemma**: a cross-root transport/exchange
      principle that converts this distributed labelled `C_6` / alternating transport hexagon into
      one rooted localization to which the old `P_3/C_6` exclusion applies, while `δ_term(T_18)`
      survives only as ancillary terminal side-labeled data;
    - more sharply, **common-frame gluing is already equivalent to localizing one cyclic rooted normal
      form**: if for some cyclic index `i` the packet `q_i = (tau_i,u_i)` is realized on one Section
      `40` frame as a balanced `|D_R| = 3` candidate instance with visible corner
      `{tau_0,tau_1,tau_2}`, then pair-rigidity fixes the marked pair and rooted support-edge
      propagation reseats the other two roots in the same frame; conversely any common-frame gluing
      obviously localizes each cyclic rooted normal form;
    - thus the sharp sufficient theorem is the **single-root localization theorem**: for every
      edge-completion witness `u_0 in K_0(e)` for `e = (u_1,u_2) in R_x`, at least one cyclic packet
      `q_i = (tau_i,u_i)` localizes as a balanced `|D_R| = 3` candidate instance on the corner
      `{tau_0,tau_1,tau_2}`;
    - equivalently, the exact minimal existence input is a **distributed-hexagon-to-one-frame gluing
      theorem**: for some cyclic index `i`, the five vertices of
      `H_i := H_hex(u_0,u_1,u_2) \ {u_i}` are simultaneously realized on one Section `40`
      frame/shadow; the current Section `40` tools are only **in-frame propagation tools**, so they
      do not start from the distributed packet alone;
    - this one-frame hexagon formulation is not stronger than single-root localization: on one fixed
      frame, `H_i` is already exactly the rooted `1^2 2^3` seed attached to `q_i`, so realizing
      `H_i` on one frame is the same existence input in geometric form;
    - conversely, there is no direct derivation of that one-frame realization from current
      Section `40` machinery alone: the distributed packet supplies only pairwise synchronizations
      (common ambient fiber and one shared visible coordinate per edge-pair), whereas every
      surviving Section `40` theorem starts after one seed frame/fiber is already frozen;
    - more sharply, the **first genuinely new bridge theorem** is already smaller than one-frame
      gluing: for some cyclic `i`, if the two off-root vertices `u_{i+1},u_{i+2}` can be synchronized
      onto one Section `40` frame/shadow over the corner with the incidences forced by `H_hex`, then
      the five-vertex seed `H_i := H_hex \ {u_i}` is on one frame and the current in-frame
      machinery localizes `q_i`; thus the exact minimal existence input is a
      **two-off-root common-shadow synchronization theorem**;
    - at this endpoint the unmarked side is already fully rigid: an edge-completion witness
      canonically determines the entire localized unmarked `C_6` on the corner, and in each cyclic
      orientation `H_i := H_hex \ {u_i}` is already a rooted `1^2 2^3` normal form whose degree-`1`
      pair is exactly the marked pair seen by `u_i`;
    - consequently the canonical hexagon already carries the **clean marked-support pattern**:
      low-old marked failures, miss-type marked failures, and `B_1(D)`-marked failures are silent,
      the marked add local test is automatic on the rooted `C_6` pattern, and the packet lies in the
      clean-support regime `alpha_S = beta_S = 0`;
    - in fact **common marked support is equivalent to common rooted localization** on this packet:
      the two marked deleted one-error adds can be realized simultaneously iff one cyclic rooted
      `C_6` normal form is realized on one common localization frame/shadow;
    - therefore the remaining gluing problem is no longer to verify marked support after
      localization, but exactly to realize **one common localization frame/shadow** in which one cyclic
      rooted `C_6` normal form is an actual localized balanced `|D_R| = 3` candidate instance;
    - once such a common localization exists, the marked-support requirements and both local marked-add
      checks are already automatic, and the entire residual marked content shrinks to the clean scalar
      datum
      `S(T_hex) := sigma_1(T_hex) + |M_R(T_hex)|`;
    - more sharply, common localization forces the two marked deleted one-error adds simultaneously,
      so `|M_R(T_hex)| = 2`; moreover every surviving singleton of `Lambda(D_R)` is supported only on
      those two marked sides, since low-old marked failures, marked miss, and `B_1(D)`-marked
      failures are already silent on the common-localized packet;
    - writing `iota_A(T_hex), iota_B(T_hex) in {0,1}` for whether the two marked deleted one-error
      adds remain isolating, one has
      `sigma_1(T_hex) = iota_A(T_hex) + iota_B(T_hex)`; hence the direct scalar theorem
      `S(T_hex) = 2` is equivalent to the sidewise **hexagon non-isolation theorem**
      `iota_A(T_hex) = iota_B(T_hex) = 0`, equivalently the local singleton-vanishing theorem
      `sigma_1(T_hex) = 0`;
    - in fact the rooted `C_6` / rooted `1^2 2^3` normal form has a side-swap symmetry exchanging
      the two marked degree-`1` sides while fixing the rooted unmarked triple, so
      `iota_A(T_hex) = iota_B(T_hex)`; therefore `sigma_1(T_hex) in {0,2}` and the full scalar gap
      reduces to a **one-sided hexagon precursor exclusion** on either marked side;
    - equivalently, after common localization the entire scalar frontier is a **single bit**
      `iota_A(T_hex)` on one chosen marked side: either `(iota_A,iota_B)=(0,0)`, giving
      `sigma_1(T_hex)=0` and `S(T_hex)=2`, or `(iota_A,iota_B)=(1,1)`, giving
      `sigma_1(T_hex)=2` and `S(T_hex)=4`;
    - equivalently, the exact missing scalar input is now a local precursor-type theorem excluding
      `K_3 ⊔ K_1` on both marked sides of the common-localized rooted `C_6` packet;
    - the branch closes exactly when `S(T_hex) = 2`; after common localization, the exact minimal
      remaining scalar theorem is therefore the **localized alternating-hexagon scalar theorem**:
      every common-localized cyclic rooted `C_6` normal form `T_hex` satisfies `S(T_hex) = 2`;
    - even the backup comparison `S(T_hex) = S(T_18)` to the unique terminal rooted `2 K_3` rung
      `T_18` is **not a distinct scalar problem**: because common localization gives
      `|M_R(T_hex)| = 2` while the terminal theorem gives `sigma_1(T_18) = 1` and
      `|M_R(T_18)| = 1`, that transport identity is equivalent to the same local theorem
      `sigma_1(T_hex) = 0`;
    - hence the one-sided precursor exclusion on a chosen marked side, the full sidewise
      non-isolation theorem, `sigma_1(T_hex)=0`, `S(T_hex)=2`, and the backup comparison
      `S(T_hex)=S(T_18)` are all equivalent formulations of the same one-bit scalar theorem;
    - therefore any genuine transport theorem would have to prove the exact one-unit singleton/marked
      exchange
      `sigma_1(T_18) - sigma_1(T_hex) = |M_R(T_hex)| - |M_R(T_18)| = 1`;
    - a stronger sufficient packaging is the **localized alternating-hexagon certification
      theorem**: every edge-completion witness localizes one cyclic rooted normal form on the
      corner, and every resulting common-localized packet satisfies the direct scalar theorem
      `S(T_hex) = 2`; after that, Corollary `40.32` kills the branch immediately;
    - however, this is still not the final endpoint. The synchronized-seed scalar half is now
      automatic: if `eps_seed(H_i) in {0,1}` records whether one chosen marked deleted one-error
      add on the synchronized rooted seed `H_i` is isolating, then for any rooted `1^2 2^3` seed
      isolation on one marked side forces the split seed `K_2 ⊔ K_3`; but for the hexagon seed
      `H_i := H_hex \ {u_i}` one has `H_i ≅ P_5`, since deleting any vertex from
      `H_hex ≅ C_6` leaves a `5`-vertex path. Therefore `eps_seed(H_i)=0`;
    - equivalently, if `eps_seed(H_i) in {0,1}` records whether one chosen marked deleted one-error
      add on the synchronized rooted seed `H_i` is isolating, then after the current in-frame
      localization machinery produces `T_hex` one has
      `eps_seed(H_i) = iota_A(T_hex)`, `iota_A(T_hex) = iota_B(T_hex)`,
      `sigma_1(T_hex) = 2 eps_seed(H_i)`, `|M_R(T_hex)| = 2`, and therefore
      `S(T_hex) = sigma_1(T_hex) + |M_R(T_hex)| = 2 + 2 eps_seed(H_i)`;
    - hence once the off-root pair has been synchronized onto one frame, localization produces
      `T_hex`, the split-vs-path lemma gives `eps_seed(H_i)=0`, so
      `sigma_1(T_hex) = 0` and `sigma_1(T_hex) + |M_R(T_hex)| = 2`; Corollary `40.32` then closes
      the host branch automatically;
    - the strongest sound synchronization reduction is now the **off-root co-hyperplane pre-frame**:
      for each cyclic `i`, the four incidences
      `(\tau_{i+1},u_{i+1}), (\tau_{i+2},u_{i+2}), (\tau_{i+1},u_{i+2}), (\tau_{i+2},u_{i+1})`
      form a canonical balanced `2 × 2` tile inside one common visible `c_i`-hyperplane `\Pi_i`,
      where `c_i` is the visible coordinate shared by `\tau_{i+1},\tau_{i+2}`; equivalently the
      off-root pair `{u_{i+1},u_{i+2}}` is already synchronized to the same visible hyperplane as
      the marked pair `{\tau_{i+1},\tau_{i+2}}`;
    - more sharply, the one-sided median-entry step itself reduces to the
      **adjacent-slice admissibility lemma**: for some cyclic `i` and some
      `j \in \{i+1,i+2\}`, the missing-corner transport `\rho = (\tau_i,u_j)` admits Section `40`
      lifts in the two adjacent shared-coordinate slices determined by the two corners of the
      canonical tile `Q_i` carrying the same root `u_j`;
    - equivalently, the only plausible source of adjacent-slice admissibility is a new
      **one-corner adjacent-slice extension** principle: if `(σ,u)` is already realized on the fixed
      Section `40` frame of `Q_i` and `σ'` shares one visible coordinate with `σ`, then the
      root-side transport `(σ',u)` admits a lift in the common shared-coordinate slice of `σ,σ'`;
      applied to the two realized corners of `Q_i` carrying the same root `u_j`, this would produce
      the two adjacent slice lifts for `\rho = (\tau_i,u_j)`;
    - more sharply still, on the normalized rooted-`C_6` tile this one-corner theorem collapses to
      a **median insertion uniqueness/existence split**: the shared slice from an adjacent realized
      corner to the missing corner `\tau_0` meets the fixed hyperplane `\Pi_0` in the unique
      nontrivial visible point `s_*=(x_1,y_0,z_0)`, so any fixed-frame lift is automatically forced
      to land at `s_*`; the only missing content is therefore the smaller **one-corner
      ambient-to-fixed fiber-preserving shared-slice lift** in that slice. Once such a lift exists
      it immediately upgrades to the median insertion statement `(s_*,u_j)\in Sh_F(\tau_0,u_j)`;
      conditional on the shell-host package, this smaller one-corner existence theorem is precisely
      the local **compatible degree-congruent transversal** theorem for the one-corner model
      `H_F(σ,\tau_i;u_j)`, i.e. a one-corner median-fiber defect-repair problem;
    - more atomically, current corner geometry yields only **ambient binary-cylinder membership** for
      `(σ',u)` on the common fiber `F_(b_1)` in the correct shared-coordinate slice, not an actual
      shadow point of the fixed frame in that slice; the exact still-smaller direct missing theorem
      is therefore the **ambient-to-fixed fiber-preserving shared-slice lift**: whenever the visible
      corner geometry already places `(σ',u)` in the admissible ambient binary cylinder on
      `F_(b_1) \cap S_c(σ,σ')`, one has
      `Sh_F(σ',u) \cap F_(b_1) \cap S_c(σ,σ') \neq \varnothing`;
    - more sharply, even this ambient-to-fixed lift already follows from the local
      **compatible degree-congruent transversal** theorem in the incidence model `H_F(σ,σ';u)`:
      such a transversal packages a peeled anchored near-regular set `T_ρ` with low set exactly the
      missing-corner incidence set `I_ρ`, and the ambient transport `x_ρ=(σ',u)` already lies in the
      admissible binary cylinder on `F_(b_1) \cap S_c(σ,σ')`, so `N(x_ρ)\cap T_ρ = I_ρ = L(T_ρ)` and
      Proposition `40.14` makes `x_ρ` a completer; thus the direct and shell-host routes meet at
      this same local transversal theorem;
    - a fresh audit shows that the purely visible direct proof stops exactly at a hidden
      fiber-uniformity step: current normalized-tile geometry proves uniqueness of the lift location
      `s_*`, and ambient membership in the admissible binary cylinder on
      `F_(b_1) \cap S_c(σ,σ')`, but not constancy of shadow-membership along that fiber/slice;
    - correspondingly, the strongest still-sound sufficient theorem below the one-corner lift is not
      full one-corner fiber-pair cylinder determinacy but the smaller **one-corner median-fiber
      cylinder determinacy**: on the single median fiber
      `M_ρ := F_(b_1) \cap S_c(σ,σ') \cap \pi^{-1}(s_*)`, incidence to each local fiber of
      `H_F(σ,σ';u)` is constant. Equivalently, on that distinguished median fiber the admissible
      shared-slice cylinder is all-or-nothing against each local fiber. This already transfers the
      ambient defect set `I_ρ` to the fixed-frame point above `s_*`, after which the same local
      prescribed-degree / equitable-seed transversal theorem packages the one-corner lift by
      Proposition `40.14`; full fiber-pair cylinder determinacy remains a stronger sufficient
      formulation but is no longer the smallest visible theorem below the one-corner lift;
    - more sharply still, even median-fiber cylinder determinacy splits into **median-fiber witness
      localization** and the genuinely geometric **single-witness median-fiber monotonicity**
      theorem: if some local fiber is mixed on `M_ρ`, one should first localize that failure to one
      witness `a`, and then prove that for each single witness the section
      `E_a := \{m \in M_ρ : m \sim a\}` is either empty or all of `M_ρ`. This single-witness hidden
      fiber monotonicity is now the smallest visible one-corner theorem below the ambient-to-fixed
      lift;
    - more sharply yet, even single-witness median-fiber monotonicity reduces to the smallest
      possible comparison above `s_*`: assuming `M_ρ` is connected under single hidden-coordinate
      flips, it is enough to prove **hidden-edge invariance** — whenever `m,m' \in M_ρ` differ in
      exactly one hidden coordinate, one has `m \sim a \iff m' \sim a` for every single witness
      `a`. Thus the genuinely new direct geometric content is no longer fiberwise monotonicity on
      all of `M_ρ`, but invariance of one witness across a single hidden edge over the fixed visible
      median point;
    - more sharply still, even hidden-edge invariance collapses to a one-square theorem: thicken a
      hidden edge above `s_*` to the smallest normalized hidden `2`-face
      `Q = \{m_{00},m_{10},m_{01},m_{11}\} \subset M_ρ`, and for a fixed witness `a` write
      `p_a(i,j) = 1_{m_{ij}\sim a}`. The exact square-level obstruction is then the mixed second
      difference `\Delta_Q p_a = p_a(11)-p_a(10)-p_a(01)+p_a(00)`, so the direct target is the
      **single-witness median-square interaction sign law** `\Delta_Q p_a \le 0`. Current normalized
      one-corner geometry freezes only unary visible data on `Q`, not that mixed sign. More sharply
      again, even this sign law is stronger than needed for the hidden-edge reduction: it already
      suffices to prove **edge-anchored directional sign coherence** on the thickened bad edge,
      namely that if the lower edge has pattern `10` then the opposite edge cannot reverse to `01`
      (equivalently `m_{00}\sim a`, `m_{10}\not\sim a`, `m_{11}\sim a` imply `m_{01}\sim a`, and
      symmetrically after swapping directions). More sharply yet, even full directional coherence is
      stronger than needed: after crossing a bad hidden edge, let `m_{11}` be a closest return of
      `E_a := \{m \in M_ρ : m \sim a\}` on the far side, and let `m_{01}` be the fourth vertex of
      the terminal square on a shortest return path. It is enough to prove the **first-return
      predecessor lemma** `m_{01}\in E_a` in that special square. More sharply still, even this
      designated-strip statement is stronger than needed: among all closest far-side returns and all
      shortest far-side strips, it already suffices that one optimal strip has terminal near-side
      vertex back in `E_a`. More sharply still, after globally minimizing the initial bad hidden
      edge one gets a **clean-corridor lemma**: along any closest-return strip, all far-side interior
      vertices and all near-side interior vertices lie outside `E_a`, so every counterexample
      collapses to a hidden clean diagonal rectangle. More sharply still, even the two-ended
      predecessor alternative is stronger than needed: the endpoint-mass statement does not force it.
      More sharply still, even the first-crossing isolated-corner exclusion is stronger than
      needed. In the parallel ladder between the first crossing `f` of `J(e')` and the terminal
      edge `e'`, write the predecessor rail `u_0,\dots,u_\ell=m_{10}` and the opposite rail
      `v_0,\dots,v_{\ell-1}=m_{01},v_\ell=m_{11}`. The case where some opposite-side ladder vertex
      lies in `E_a` already gives a strictly smaller bad hidden edge by shortening the
      closest-return suffix. So the genuinely minimal direct obstruction now has the exact normal
      form of a **successor-side first-switch `0001` square**: let
      `R=\{u_0,u_1,v_0,v_1\}` be the first square on the opposite rail with
      `u_0,u_1,v_0\notin E_a` and `v_1\in E_a`. Any earlier opposite-rail hit in `E_a` already
      shortens to a strictly smaller bad hidden edge, and if the suffix from `R` to `e'` is
      anchored on the predecessor side of `R` (equivalently, if the original startpoint corner
      `x_0` lies on the predecessor side of `R`), then the existing strip-transfer theorem applies
      on that suffix and again produces a strictly smaller bad hidden edge. Hence the
      predecessor-side case is already discharged. Thus the direct lane no longer stops at
      orienting the successor-side `0001` square itself. The exact remaining direct atom is the
      residual two-part local common core on
      `M_ρ = F_(b_1) \cap S_c(σ,σ') \cap π^{-1}(s_*)`: any fixed-frame lift is forced to the
      unique visible point `s_*`, and the ambient transport `(σ',u)` already lies in the
      admissible binary cylinder on `F_(b_1) \cap S_c(σ,σ')`. The first missing ingredient is the
      explicit **fiber-constant pair-status / defect-fiber identification** on `M_ρ` (the old
      same-fiber-twin item is redundant, and `x_ρ` already cuts out exactly `I_ρ`); once that
      structure is explicit, packet packaging is formal. Conditional on that first half, the
      quotient side shrinks further still. Fix `q_00:=p↓A`, `q_10:=p↓(A∪{H})`,
      `q_01:=p↓(A∪{J})`, `q_11:=p↓(A∪{H,J})`. Conditional on the per-fiber persistence implications
      `d_{10}(K)≤d_{11}(K)` and `d_{01}(K)≤d_{11}(K)`, each fiber row
      `r(K):=(d_{00}(K),d_{10}(K),d_{01}(K),d_{11}(K))` with `d_{00}(K)=0` is one of
      `0000, 0001, 0101, 0011, 0111`. Hence `\Omega_{10}={K:r(K)=0101}` and
      `\Omega_{01}={K:r(K)=0011}`. On a two-fiber edge table, write
      `\Omega_{10}:={K:d_{10}(K)=1}` and `\Omega_{01}:={K:d_{01}(K)=1}`. The rows
      `0000,0001,0101,0011,0111` contribute respectively to neither set, neither set,
      `\Omega_{10}\setminus\Omega_{01}`, `\Omega_{01}\setminus\Omega_{10}`, and
      `\Omega_{10}\cap\Omega_{01}`. Hence the mixed pattern `(0101,0011)` is equivalent to
      `\Omega_{10}\ne\varnothing`, `\Omega_{01}\ne\varnothing`, and
      `\Omega_{10}\cap\Omega_{01}=\varnothing`. So the quotient-side frontier needed for
      tree-path telescoping shrinks further to the **two-fiber single-flip overlap lemma**: if
      `\Omega_{10}\ne\varnothing` and `\Omega_{01}\ne\varnothing`, then
      `\Omega_{10}\cap\Omega_{01}\ne\varnothing`. After reducing each row to one of
      `0000,0001,0101,0011,0111`, there is no further coarse slack: under
      `\Omega_{10}\ne\varnothing` and `\Omega_{01}\ne\varnothing`, the only admissible non-overlap
      table is the mixed pair `{0101,0011}`, while every other admissible two-row configuration
      contains an `0111`-fiber. Factoring off the already-isolated one-edge
      predecessor/persistence inputs on the two incident squares, the residual quotient-side
      problem shrinks further: on each fixed-trace common-edge packet `P_e^\tau`, it is enough to
      prove that the pair-chamber map `Σ_e=σ^- × σ^+` determines the elementary common-edge hidden
      choice `h_e`. Equivalently, no nontrivial elementary common-edge hidden step may stay inside
      a single pair-chamber cylinder. This is strictly smaller than recovering the full
      packet-state; the only missing two-square bridge is **pair-chamber separation of the hidden
      choice over the shared edge `e`**. Tree-path telescoping then upgrades
      an equitable compatible seed with low set exactly `I_ρ` to the target degree-congruent
      transversal; in the Gray / ideal / Horn picture, this is downward flippability at the
      reference ideal. The current notes still do not justify either half of `(1)`, the per-fiber
      predecessor/persistence inputs, or this pair-chamber separation of the hidden choice.
      Without that split `(1) + (2′)` local common core, neither same-frame realization,
      ambient-to-fixed shared-slice lift, fixed-frame shared-slice entry, nor prescribed
      shared-slice entry is yet available;
    - in particular, the one-corner extension factors through that ambient-to-fixed lift and then
      the older **one-step shared-slice entry** / **fixed-frame shared-slice entry** statement
      `Sh_F(σ',u) \cap S_c(σ,σ') \neq \varnothing`; if same-frame realization of `(σ',u)` is
      granted, the residual conditional gap sharpens further to **prescribed shared-slice entry**,
      i.e. the stronger intersection
      `Sh_F(σ',u) \cap C_c(σ',u) \neq \varnothing` with the admissible shared-slice binary cylinder;
    - there is also a fresh **conditional host-side reformulation** of this exact frontier: if the
      local shared-slice model `H_F(σ,σ';u)` can be packaged as a peeled anchored near-regular set
      `T` exactly in the sense of `40.14`–`40.16`, with low set equal to the missing-corner
      incidence condition, then fixed-frame shared-slice entry is equivalent to local completer
      positivity `c(T) > 0`; equivalently, by `40.15`–`40.16`, to a nontrivial local raw short
      packet / weighted relation of total mass `< q`; in the irreducible `c(T)=0` regime the local
      obstruction collapses to the anchor-supported one-defect condition `d(O_1) \subseteq w`;
      more sharply, once such a package exists all packet algebra is formal: the genuinely new
      content is the existence of a completed local shell host `S_ρ = T_ρ ⊔ \{x_ρ\}` (equivalently
      a peeled set `T_ρ` with low set exactly the missing-corner incidence set `I_ρ`); and, in the
      irreducible packaged regime `c(T)=0`, the one-defect strip is diagonal, contributes no
      nonzero weighted raw relation of total mass `< q`, and Hall is exhausted by the pointwise
      overload bounds `μ(a) \le q-1` on the anchor; thus the exact remaining packaged theorem is a
      compatible injective transversal / local multi-swap producing `T_X` anchored near-regular
      with `c(T_X)>0`; equivalently, once the package exists and the overload-free anchor-supported
      regime is reached, the residual packaged problem is a **finite rooted-template transversal**
      problem on the anchor fibers `F_a := d^{-1}(a)`: for a nonempty deleted-anchor set `D ⊆ w`
      and a transversal `x ∈ ∏_(a∈D) F_a`, positivity of `T_x := (T \ D) ⊔ X(x)` factors through a
      finite rooted graph type on `X(x) ∪ \{v\}` for a candidate completer `v`; the exact remaining
      packaged theorem is the existence of some such `D`, compatible injective `x`, and rooted
      positive template, and singleton swaps are reversible so the first genuinely new content is
      typically `|D| ≥ 2`; more sharply, this finite rooted-template problem reduces further to a
      **rooted pair-template average** theorem: it is enough to find distinct anchors `a,b ∈ w` with
      positive pair average `A_{a,b}(T) = \sum_{x \in \mathcal P(\{a,b\})} c(T_x) > 0`, which then
      yields a compatible positive `2`-swap; and, more sharply still, this pair-average theorem
      itself reduces to a **pair-density / two-switch extraction law**: for every compatible
      multi-swap `y ∈ \mathcal P(D)`, writing
      `\kappa_T(E;y) := \sum_{F \subseteq E} (-1)^{|E|-|F|} c(T_F)` on the Boolean lattice of `D`,
      one has the exact expansion
      `c(T_y) = \sum_{\{a,b\}\subseteq D} c(T_{ab}) + \sum_{|E|\ge 3}\kappa_T(E;y)`
      because `c(T)=0` and singleton swaps are reversible; thus it is enough to prove the
      higher-order interaction nonpositivity `\sum_{|E|\ge 3}\kappa_T(E;y)\le 0`, equivalently the
      pair-density inequality `\sum_{\{a,b\}\subseteq D} c(T_{ab}) \ge c(T_y)`, i.e. every positive
      compatible packaged multi-swap contains a positive compatible `2`-subswap. More sharply again,
      it is enough to prove the **candidate-wise rooted two-switch extraction theorem** on the finite
      candidate set `C(D)`: for every candidate completer `v`, if `v` completes `T_y`, then `v`
      already completes `T_{ab}` for some pair `{a,b}\subseteq D`; equivalently, for
      `\kappa_v(E;y) := \sum_{F \subseteq E} (-1)^{|E|-|F|} f_v(F)` with
      `f_v(F)=1_{v\text{ completes }T_F}`, it is enough to prove the candidate-wise Möbius sign
      theorem `\kappa_v(E;y)\le 0` for all `|E|\ge 3`. More sharply yet, if `F` is inclusion-minimal
      with `v` completing `T_F`, singleton reversibility forces `|F|\ge 2`, and it would be enough to
      prove the **balanced minimal rooted obstruction theorem**: every such minimal rooted positive
      template is either a pair or one of the balanced outside-candidate `1^2 2^3` templates
      (equivalently rooted `C_6` / rooted `2K_3`, up to rooted complement / relabelling). Hence a
      still-smaller exact target is the **balanced rooted five-switch exclusion theorem**: no
      compatible packaged multi-swap realizes that balanced `1^2 2^3` rooted template for any
      candidate `v`. More sharply again, this balanced obstruction already collapses back to the
      cyclic/localization lane: after rooted complement it is exactly a rooted `C_6`, and its
      exclusion would follow once one can localize one cyclic `P_5` seed on a common frame; the
      sharpest still-smaller theorem is therefore the old **adjacent-slice admissibility lemma**
      (equivalently the two-off-root common-shadow synchronization theorem) for the packaged rooted
      `C_6` packet. More sharply still, even that localization bridge reduces to the **one-corner
      local shared-slice lift theorem**: for one realized corner `(σ,u_j)` of `Q_i` and the adjacent
      missing corner `σ'=\tau_i` sharing one visible coordinate, the transport `\rho=(σ',u_j)` has a
      lift in the fixed frame inside `S_c(σ,σ')`; applying this at the two realized corners carrying
      the same root `u_j` recovers the full adjacent-slice admissibility lemma. Conditional on the
      shell-host package, this one-corner lift is exactly the local **compatible degree-congruent
      transversal** theorem for the one-corner incidence model `H_F(σ,σ';u_j)`. Moreover, conditional on the shell host, the compatible
      degree-congruent transversal problem itself reduces to a **unit-transfer theorem**: it is
      enough to have one compatible seed transversal with the correct total degree and a local
      binary/shared-slice switching lemma that transfers one unit of degree from an overfull fiber to
      an underfull fiber while preserving compatibility; by convex minimization this forces an exact
      target degree vector. Under the extra hypotheses `|\mathcal F_\rho|=q`,
      `\sum_F d_X(F)=q\delta_\rho-|I_\rho|`, and `|I_\rho|=\delta_\rho`, an equitable compatible
      transversal with low-degree fibers exactly `I_\rho` already yields a degree-congruent
      transversal. More structurally, one does not need a full complete/empty blow-up quotient:
      it already suffices to prove the **pairwise two-fiber exchange** property that whenever
      `d_X(A)\ge t_A+1` and `d_X(B)\le t_B-1`, one can rechoose representatives only in the two
      fibers `A,B` so that `d_X(A)` drops by `1`, `d_X(B)` rises by `1`, and all other fiber degrees
      stay fixed; this sits strictly between bare equitability and full blow-up. Sharpening once
      more, even this pairwise exchange theorem is stronger than necessary: it is enough to prove a
      **spanning-tree shared-slice edge-switch theorem** on the fiber graph `\Gamma_\rho`, namely a
      spanning tree of fibers such that each oriented tree edge `F→G` admits a local switch
      supported on that one shared slice with net degree change `-e_F+e_G`; telescoping such moves
      along the tree path from any overfull fiber to any underfull fiber then realizes full
      degree-congruence. More sharply again, even this reduces to a **load-preserving shared-slice
      pair-exchange theorem** on one tree edge `F-G`: for the current compatible pair
      `p=(x_F,x_G)` and a replacement pair `p'=(f',g')` inside the same defining shared slice, write
      `\lambda_X(p')(H)=1_{x_H\sim f'}+1_{x_H\sim g'}` for `H\neq F,G`; it is enough to find `p'`
      with `\lambda_X(p')=\lambda_X(p)` and endpoint change `\Delta d(F)=-1`, `\Delta d(G)=+1`,
      because equality of outside-load profiles is exactly what keeps every outside fiber degree
      fixed. More sharply yet, this load-preserving pair-exchange theorem itself has a **binary
      normal form**: writing `\tau_H(p') := 1_{x_H\sim f'} - 1_{x_H\sim x_F}` and
      `T(p') := \sum_{H\neq F,G}\tau_H(p')`, and letting `\varepsilon(p)` denote the internal
      adjacency status of the pair on `F-G`, one has
      `\Delta d(F)=T(p')+(\varepsilon(p')-\varepsilon(p))` and
      `\Delta d(G)=-T(p')+(\varepsilon(p')-\varepsilon(p))`; hence it is enough to find a
      same-slice compatible replacement `p'` with unchanged internal edge-status
      `\varepsilon(p')=\varepsilon(p)` and signed transfer sum `T(p')=-1`. More sharply yet, fixing
      the internal status `\varepsilon`, this signed-transfer theorem reduces to the one-coordinate
      outside-load spectrum on the `F`-side:
      `\Lambda_\varepsilon := \{L_F(f') : \exists g' \text{ with } (f',g')\in S_\varepsilon\}`.
      It is enough to prove a **fixed-status interval theorem** asserting that `\Lambda_\varepsilon`
      is an integer interval together with the extremal **fixed-status predecessor/nonminimality
      theorem** `\min \Lambda_\varepsilon < L_F(x_F)`; then `L_F(x_F)-1\in\Lambda_\varepsilon`, so
      some same-status pair has signed transfer sum `T=-1`. More sharply yet, the interval theorem
      itself would follow from a **fixed-status Gray / ideal theorem**: after orienting the
      switchable outside fibers, the feasible same-status set is the ideal lattice of a finite
      poset, equivalently single-coordinate flips connect all feasible same-status pairs and change
      `L_F` by `\pm 1`. The predecessor theorem then reduces further to a **downward-flippability
      theorem** asserting that the reference pair is not the minimum ideal, equivalently some
      allowed single-coordinate flip preserves status and decreases `L_F` by `1`. More sharply yet,
      this Gray / ideal theorem itself would follow from a **pair-table Horn theorem**: the feasible
      same-status bitcube is cut out by its two-coordinate tables, and after orienting by the load
      bit every pair table is Horn/monotone. More sharply again, the Horn/cutout problem splits into
      a **two-fiber missing-corner theorem** — whenever an oriented pair table contains
      `00,10,01`, it also contains `11` — and a **binary-cylinder `2`-Helly theorem** excluding
      genuine ternary infeasible patterns. The missing-corner theorem itself now sharpens one level
      further: the exact fixed-witness content compresses below the residual sign law to the
      **candidatewise localized square anti-Horn theorem**. For every localized witness `ω` and
      candidate completer `v`, on the resulting `2×2` square of pair-choices one should have
      `00,10,01` feasible for `v` imply `11` feasible for `v`; equivalently, after subtracting unary
      terms the candidatewise residual binary atom has nonpositive mixed second difference. But even
      this candidatewise square theorem is stronger than needed for the direct shell-host attack: the
      persistence part is already exactly the **candidatewise one-edge fixed-status predecessor
      theorem** on each of the two incident reference edges. More sharply, the exact unresolved
      mixed content is real: the abstract Boolean table with feasible set
      `{00,10,01}` has both one-coordinate predecessors, interval one-dimensional shadows, and all
      single-coordinate persistence data visible from `00`, but it fails the missing corner `11`.
      Hence the two-fiber missing-corner theorem cannot be obtained from one-edge predecessor /
      persistence data alone; it requires a genuinely two-coordinate anti-Horn or mixed
      second-difference theorem for the localized witness/candidate square. The exact unresolved
      two-square content can therefore still be normalized to the
      **common-edge pair-chamber cylinder rigidity theorem**: for a shared doubly visible interior
      overlap edge `e` with incident filled overlap squares `Q^-`,`Q^+`, fix the trace datum and
      let `χ^- , χ^+` denote the incident unary-chamber maps (equivalently the repaired
      opposite-defect maps, by one-square wall detection). Along any elementary orthogonal hidden
      step in the fixed-trace repair fiber over `e`, if both chamber coordinates `χ^- , χ^+` are
      unchanged, then the repaired packet-state on `e` is unchanged. Equivalently, every fixed
      pair-chamber cylinder `(χ^- , χ^+)^{-1}(C^- , C^+)` on the common-edge packet contains no
      nontrivial elementary hidden edge. Using the already-established one-square wall theorems on
      `Q^-` and `Q^+`, the unresolved two-square content can therefore be read entirely in terms of
      the two incident repaired opposite-defect maps. Thus the exact frontier is the
      **common-edge fixed-opposite-pair packet-rigidity theorem**, equivalently **elementary
      two-sided silent-component injectivity**: after fixing the shared edge `e` and the trace
      datum `ρ_e`, the only currently recorded invariants on an elementary common-edge hidden step
      are the sidewise silent-component labels `σ^- , σ^+` (equivalently the two incident repaired
      opposite-defect components), and no further packet-level consequence is presently proved from
      them. More sharply, the hybrid reduction can be made canonical via an **initial-packet
      basin**. Fix a `C^+`-anchored span-`1` active side `x_i,x_{i+1}` and a passive basepoint
      `u∈C^+`; for each `y∈C^+` let `P(y)` be the repaired packet attached to the hybrid state
      with passive defect `y`, and define
      `B_u := { y∈C^+ : there exists a shortest passive silent path u=z_0,\dots,z_m=y with
      P(z_t)=P(u) for all t }`. Then `B_u` is geodesically star-convex from `u`. If
      `P(v)\ne P(u)` for some `v∈C^+`, then `B_u` is proper, every shortest passive path from `u`
      to `v` has a unique first edge `ab` leaving `B_u`, and any forward geodesic boundary edge
      `ab` with `a∈B_u`, `b∉B_u`, `d(u,b)=d(u,a)+1` is automatically packet-changing, since
      otherwise the constant-packet geodesic to `a` extended by `ab` would place `b` back in
      `B_u`. More sharply, the constant-packet predecessor chain inside `B_u` carries no residual
      ambiguity once one reaches the last basin vertex `a`: it only selects the canonical pre-edge
      hybrid state `η_a` with active side `x_i,x_{i+1}` and packet `P(u)`. Hence the unresolved
      hybrid step is purely one-edge local. More sharply, the boundary one-step same-fiber
      endpoint-uniqueness lemma itself reduces to a smaller one-square identification problem on
      the outgoing incident square. Fix a forward boundary edge `ab` and the canonical pre-edge
      state `η_a`, and write `Q^-` for the side on which we keep `σ^-(η_b)=σ^-(η_a)` and `Q^+`
      for the other incident square. Since `ab` is the first edge leaving the basin `B_u`, every
      admissible continuation over `b` is already packet-changing. More sharply, the smallest exact
      missing object is now **boundary outgoing anchored witness persistence / no-split on `Q^+`**.
      Let `R^+` be the set of outgoing repaired opposite defects on `Q^+` realized by admissible
      packet-changing continuations over `b` for the fixed boundary data
      `(ab,η_a,σ^-(η_a))`. More sharply, the pairwise no-split target may be replaced by the
      one-anchored lemma that if one admissible continuation realizes an outgoing defect `ρ_0^+`
      and a unary witness `λ` on `Q^+` satisfies `λ∼ρ_0^+`, then every admissible
      packet-changing continuation realizes an outgoing defect `ρ^+` with `λ∼ρ^+`. By one-square
      silent-component characterization, this is equivalent to pairwise unary witness-incidence
      constancy: for each unary witness, either every realized outgoing defect sees it or none do.
      Hence all realized outgoing defects lie in a single component `C⊂Γ_{Q^+,ab}`, and the only
      remaining completion input is the **realized componentwise singleton** statement
      `|R^+ \cap C| \le 1`. Thus no global singleton/edgelessness statement on the whole outgoing
      chamber graph, and not even on all square-admissible outgoing defects, is required. The
      present missing bridge is therefore the anchored two-continuation / one-witness no-holonomy
      statement above. Once this anchored witness persistence / no-split is
      available, the downstream chain to
      **candidatewise reference-corner elementary fixed-trace packet-visible wall detection**,
      **candidatewise reference-corner one-step fixed-trace packet reconstruction**,
      **candidatewise reference-corner shared-edge boundary well-definedness**, the intrinsic edge
      potential `φ_ρ^v(e)`, and the
      **candidatewise reference-corner overlap-string witness-switch coboundary** theorem becomes
      formal: along every maximal doubly visible overlap string, the orthogonal drift is the
      difference of the two endpoint edge-potentials. Telescoping then gives the
      **candidatewise reference-corner overlap-string zero-drift** theorem and hence the
      **candidatewise reference-corner overlap-packet neutrality** law. From there one recovers
      candidatewise single-witness overlap neutrality, orthogonal single-witness cylinder
      monotonicity, incident opposite-repair invariance, and then together with the already-available
      one-edge predecessor theorems and finiteness/decreasing defect statistics the candidatewise
      incident two-repair diamond and the candidatewise reference-corner common-gate theorem by
      confluence. A slightly stronger step-level theorem is
      **candidatewise reference-corner elementary fixed-trace packet-visible wall detection**;
      stronger still is
      **candidatewise reference-corner one-step fixed-trace packet reconstruction**; a stronger
      fixed-trace theorem is
      **candidatewise reference-corner fixed-trace witnesswise packet reconstruction**. A stronger
      local sufficient form is the
      **candidatewise reference-corner overlap-square anti-reversal** law, and a still stronger
      sufficient shell-host input is
      candidatewise reference-corner fiber-pair cylinder determinacy. If the expected shell-host decomposition of `p_ω` into
      candidate contributions is valid, summing candidatewise anti-Horn yields the full residual
      interaction sign law `\Delta_{12} p_ω \le 0`; and once that sign law is available, the
      witness-level frontier drops to the weaker **single-coordinate reference persistence +
      reference overlap** package. Likewise the
      `2`-Helly theorem has collapsed past open-top `3`-cube exclusion to the smaller
      **upper-face no-holonomy, fixed-point form**: if `Ω_i` denotes the localized failed-top
      witness packet on the upper face `F_i`, it is enough that
      `Ω_1 \cap Ω_2 \cap Ω_3 \neq \varnothing`, equivalently that cyclic witness transport around the
      upper hexagon has a fixed point. Literal equality of chosen face-witnesses is stronger than
      needed. A smaller sufficient reduction is **adjacent-face gluing + convex Helly**: for each
      adjacent pair `F_i,F_j`, one has `Ω_i \cap Ω_j \neq \varnothing`, and the packets `Ω_i` are
      convex/gated in the shell-host witness space; then Helly yields a common witness. Once such a
      common witness exists, the top corner is reduced to a single-witness missing-corner problem,
      which the one-square submodularity theorem closes. More sharply still, even adjacent-face
      gluing splits into **edge persistence** inside each face and **edge-trace overlap** on the
      common upper edge `E_{ij}`: project `Ω_i` and `Ω_j` to `E_{ij}`, and show each packet reaches
      the edge along a geodesic staying inside the same packet, after which one only needs the two
      edge traces to meet. The sharpest currently visible one-face theorem here is the
      **one-edge predecessor theorem**: every witness in `Ω_i` admits a geodesic to `E_{ij}`
      entirely inside `Ω_i`, equivalently every nearest-point gate of `Ω_i` to `E_{ij}` stays in
      `Ω_i`. More sharply still, even one-edge predecessor splits into **component anchor** on each
      nonempty layer parallel to `E_{ij}` and the local **transverse-square predecessor lemma**:
      on a transverse square `Q = \{x,y,x^{-},y^{-}\}` in one face, one should have
      `x,y,y^{-} \in Ω_i \Rightarrow x^{-} \in Ω_i`. Under the shell-host package, the
      witness-frozen form is essentially already the fixed-witness square Horn axiom:
      **single-witness transverse-square monotonicity** inside `Ω_i(a)`. What remains unfrozen is
      no longer which unary wall is crossed, but the one-step separation of opposite defects inside
      a unary chamber. The shell-host witness-packet geometry already yields
      **elementary fixed-trace incident-square unary-chamber trapping**: if an elementary hidden
      step preserves every single witness incidence on `e`, then the two opposite defects lie in
      the same unary chamber of the opposite packet of `Q`. More sharply, the cubical shell-host
      model also gives **incident-square silent-component characterization**: two repaired opposite
      defects lie in the same unary chamber iff they are connected by a path of elementary hidden
      steps each preserving every single witness incidence on `e`. Equivalently, fix one incident
      filled overlap square `Q` and define the one-square silent graph `Γ_{Q,e}` whose vertices are
      the repaired opposite defects on the fixed opposite packet and whose edges are the elementary
      hidden steps preserving every single witness incidence on `e`. By incident-square
      silent-component characterization, the unary chambers are exactly the connected components of
      `Γ_{Q,e}`; hence `Γ_{Q,e}` is edgeless iff every unary chamber is a singleton, equivalently
      iff **incident-square silent-step opposite-defect rigidity** holds, hence iff
      **incident-square silent-path defect rigidity / incident-square unary-chamber rigidity /
      silent hidden singleton property** holds. Moreover, using the already-available
      **elementary fixed-trace incident-square unary-chamber trapping**, this is also equivalent to
      **elementary fixed-trace incident-square opposite-defect wall detection**: if `Γ_{Q,e}` is
      edgeless then same-chamber implies equality, so any elementary hidden step changing the
      opposite defect must cross a unary wall; conversely, a silent step between distinct repaired
      opposite defects would be trapped in one unary chamber, contradicting wall detection. Thus
      the exact missing one-square input may be stated either as silent-edge exclusion or as
      one-step wall detection. The full hypothesis that an elementary hidden step preserve every
      single witness incidence on `e` buys only this path-level connected-component reformulation:
      it does not presently yield any stronger one-edge injectivity beyond unary-chamber trapping.
      The minimal obstruction remains a single chamber-flat silent edge
      between distinct repaired opposite defects; no longer silent-path phenomenon remains. None of
      the previously recorded confluence / common-gate / fan-merge structure presently shrinks this
      obstruction: every recorded route to incident two-repair diamond / common gate first passes
      through one-square opposite-defect wall detection, then packet-visible wall detection /
      one-step packet reconstruction / shared-edge boundary well-definedness, so confluence is
      downstream of the missing injectivity theorem, not a source of it. Once this one-step wall
      detection / edgelessness holds, together with any pointwise identification
      of packet change through
      opposite-defect change (for example the already-envisioned filled-square rigidity lane), this
      upgrades to **elementary fixed-trace incident-square packet silence**, and then together with
      the already-recorded edge-model packet determinacy and connectivity of the fixed-trace repair
      fiber yields **fixed-trace boundary reconstruction from unary profile**, hence
      **shared-edge boundary well-definedness** on the common overlap packet. That local gluing
      immediately yields the **stringwise witness-switch coboundary theorem** by telescoping, hence
      the **overlap-string zero-drift theorem** and **shared-overlap neutrality**. The already
      available smaller theorems are **unary-chamber trapping** and **silent-component
      characterization**; equivalent one-step normal form:
      **elementary fixed-trace incident-square opposite-defect wall detection**; slightly stronger
      still is **elementary fixed-trace incident-square packet silence**; a slightly stronger fixed-trace
      theorem is **fixed-trace boundary reconstruction from unary profile**; a slightly stronger
      geometric sufficient form is **fixed-trace incident-square unary halfspace presentation**; a
      stronger local sufficient form is **elementary fixed-trace packet invariance** across one
      orthogonal hidden step with the same trace datum `ρ_e`. A stronger pointwise sufficient form
      is
      **filled-square packet rigidity**: on every filled overlap square the opposite defect depends
      only on the packet label and the repaired edge, not on the orthogonal position; equivalently,
      interior overlap-edge invariance on filled squares. This is still strictly weaker than the
      **additive incident defect law**, which remains a stronger sufficient bookkeeping input;
      stronger still is the **incident opposite-repair invariance theorem** (equivalently orthogonal
      local support on the common witness packet), which would make the **incident two-repair
      diamond theorem** formal. Together these yield the weighted
      distributive-lattice
      picture. The exact remaining local obstructions are therefore failure of
      candidatewise one-edge predecessor / common-edge fixed-opposite-pair packet-rigidity on the
      common edge packet over a shared doubly visible interior overlap edge (equivalently, along
      any elementary orthogonal hidden step over `e`, if the repaired opposite defect is unchanged
      on both incident filled overlap squares then the packet on `e` is unchanged; this is
      equivalent to common-edge pair-chamber cylinder rigidity, hence to candidatewise
      reference-corner elementary fixed-trace packet-to-opposite-defect visibility / earlier
      two-chamber no-holonomy; equivalently, by one-square silent-component characterization on
      `Q^-` and `Q^+`, the exact missing input is **elementary two-sided silent-component
      injectivity** on the common-edge packet: if `σ^\pm` sends a repaired packet-state to the
      connected component of its repaired opposite defect in the one-square silent graph
      `Γ_{Q^\pm,e}`, then no nontrivial elementary hidden edge may lie in one fiber of
      `σ^- × σ^+`. Equivalently, the pair of sidewise silent-component data determines the packet
      on an elementary common-edge step. Thus any failure already has a minimal obstruction
      consisting of one elementary common-edge hidden step whose endpoints remain in the same
      silent component on both `Q^-` and `Q^+`; this is only a reformulation, not a closure, since
      the missing input is still the genuinely two-square injectivity of `σ^- × σ^+`. This
      anti-Horn frontier is therefore an honest two-square lift of the one-square silent-component
      data, but it does **not** presently subsume the ternary atom: a chamber-flat silent edge in a
      single `Γ_{Q,e}` gives only failure of one-square wall detection on that square, and no
      currently proved bridge promotes it to an elementary common-edge hidden step lying in one
      fiber of `σ^- × σ^+`. Such a promotion would require additional packet/opposite-defect
      identification not yet available (for example filled-square rigidity, packet-visible wall
      detection, or downstream boundary reconstruction). Hence the ternary atom remains genuinely
      one-square and independent at the current theorem level. Moreover, by one-square
      silent-component characterization, any failure of `σ^- × σ^+`-injectivity gives on each
      incident square `Q^\pm` a shortest silent path in `Γ_{Q^\pm,e}` joining the two repaired
      opposite defects of the packet-nontrivial elementary common-edge hidden step; but this
      shortest-path normalization is presently only a reformulation. No recorded theorem
      synchronizes the two sidewise paths, no honest predecessor/bridge law turns a sidewise silent
      edge into a new elementary common-edge packet step, and no current result determines the
      packet from those path data. In particular, one cannot yet reduce the anti-Horn atom to
      one-edge ternary witnesses on either side, let alone on both sides. Even in the hybrid case
      where one side already realizes a shortest silent path of length `1`, the current theorems
      yield only a chamber-flat silent edge on that side and same-component data on the other; no
      honest extra packet-level consequence follows. Once
      available it yields candidatewise reference-corner
      elementary fixed-trace packet-visible wall detection,
      hence candidatewise reference-corner one-step fixed-trace packet reconstruction, hence
      candidatewise reference-corner shared-edge boundary well-definedness, hence candidatewise
      reference-corner overlap-string witness-switch coboundary, hence candidatewise
      reference-corner overlap-string zero drift, hence candidatewise reference-corner
      overlap-packet neutrality, hence candidatewise
      single-witness overlap neutrality, hence candidatewise orthogonal single-witness cylinder
      monotonicity, hence candidatewise incident opposite-repair invariance, hence candidatewise
      incident two-repair diamond, hence candidatewise reference-corner common gate; slightly
      stronger step-level theorem: packet-visible wall detection; stronger still: one-step packet
      reconstruction; stronger
      fixed-trace theorem: witnesswise packet reconstruction; stronger local sufficient form:
      overlap-square anti-reversal; or stronger reference-corner fiber-pair determinacy),
      failure of
      single-coordinate reference persistence / reference overlap, failure of
      one-square silent-graph edgelessness / elementary fixed-trace incident-square
      opposite-defect wall detection on one incident filled overlap square
      (equivalently, if `Γ_{Q,e}` denotes the silent graph whose vertices are repaired opposite
      defects and whose edges are the elementary hidden steps preserving every single witness
      incidence on `e`, then incident-square silent-component characterization identifies unary
      chambers with the connected components of `Γ_{Q,e}`, so edgelessness is equivalent to
      incident-square silent-step opposite-defect rigidity, hence to incident-square silent-path
      defect rigidity and to incident-square unary-chamber rigidity / silent hidden singleton
      property; using elementary fixed-trace incident-square unary-chamber trapping, this is also
      equivalent to elementary fixed-trace incident-square opposite-defect wall detection; any
      failure has a minimal obstruction consisting of a single chamber-flat silent edge. Preserving
      every single witness incidence on `e` determines exactly the unary chamber (equivalently the
      connected component in `Γ_{Q,e}`) of the repaired opposite defect, and no packet-level datum
      beyond that; this is the exact presently justified one-edge endpoint, not merely a residual
      description. Thus even a chamber-flat silent edge, or more generally a `2`-point connected
      component of `Γ_{Q,e}`, carries no honestly proved packet agreement / packet-visible wall /
      one-step packet-reconstruction consequence. Any such upgrade would require additional
      packet/opposite-defect identification input not yet available, so the positive one-square
      frontier remains precisely edgelessness of `Γ_{Q,e}` / opposite-defect wall detection.
      Moreover, because `Γ_{Q,e}` is undirected, any candidate endpoint statistic on repaired
      opposite defects that is monotone under silent steps is automatically constant on each
      connected component, hence on each unary chamber. So wall count / support / parity /
      first-index viewed as vertex data cannot exclude a chamber-flat silent edge. Any viable
      orientation-potential must therefore be genuinely pairwise: it must canonically orient a
      silent edge from the ordered pair of repaired opposite defects. More sharply, the unresolved
      pairwise one-edge atom can be compressed still further. For a chamber-flat silent edge
      `(x,y)` with `D(x)|_{<j}=D(y)|_{<j}`, `P(x)|_{≤j}=P(y)|_{≤j}`, and `D_j(x)\ne D_j(y)`, let
      `Q_j(x)` denote the statewise coordinate-`j` elementary fixed-trace incident square attached
      to `x`. Conditional on fixed-square coordinate-`j` opposite-defect rigidity, the persistence
      problem reduces further: it is enough to prove an **anchored one-corner lift on `Q_j(x)`**.
      Namely, the shared lower
      repaired-defect prefix and shared packet prefix through `j` should admit a realization on
      the fixed square `Q_j(x)` with coordinate-`j` repaired opposite defect `D_j(y)`. Any such
      realization forces `Q_j(x)` to be compatible with `y`, hence `Q_j(y)=Q_j(x)`. Thus the new
      sharp unresolved one-square object is no longer full anchored square compatibility, but the
      existence of the `y`-corner on the already anchored square `Q_j(x)`. Present
      witness-incidence / silent-component data still do not produce this. Conditional on it,
      and on fixed-square opposite-defect rigidity, one-step repaired-defect extension uniqueness
      follows, then edge packet separation /
      same-packet silent-edge rigidity as before, and the remaining ternary atom may still be
      written equivalently as prefix-star sign uniqueness: for fixed `y,i` and lower packet prefix
      `π`, all silent edges `y-w` with
      `P(w)|_{<i}=π` and first label coordinate `i` carry the same sign.
      `λ(x,y)=(i,ε)` and `P(y)|_{<i}=P(z)|_{<i} => λ(y,z) ≠ (i,-ε)`.
      Together
      with pointwise packet-versus-opposite-defect
      identification such as filled-square rigidity, this yields elementary fixed-trace
      incident-square packet silence, hence via edge-model packet determinacy and fixed-trace
      repair-fiber connectivity fixed-trace boundary reconstruction from unary profile, hence
      shared-edge boundary well-definedness on the common overlap packet, hence stringwise
      witness-switch coboundary, hence overlap-string zero drift, hence shared-overlap neutrality on
      the doubly visible fibers; already available smaller theorems: unary-chamber trapping /
      silent-component characterization; slightly stronger one-step theorem: opposite-defect wall
      detection; slightly stronger still: incident-square packet silence; slightly stronger
      fixed-trace theorem: boundary reconstruction from unary profile; slightly stronger geometric
      sufficient form: incident-square unary halfspace presentation; stronger local sufficient form:
      elementary fixed-trace packet invariance; stronger pointwise filled-square packet rigidity /
      interior overlap-edge invariance; or stronger additive incident defect law / incident
      opposite-repair invariance) /
      an incident two-repair diamond / common gate for the incident traces /
      edge-trace overlap / witness fixed points, equality blocks
      `\{00,11\}` on distinct switchable fibers, and the minimum-ideal obstruction for the
      reference pair. Under the same extra hypotheses as above, an equitable compatible seed with
      low-degree fibers exactly `I_\rho` already has the target degree vector and no switching is
      needed. Moreover the shell-host packaging step itself is
      equivalent to a local
      **compatible degree-congruent transversal** problem on the incidence fibers of
      `H_F(σ,σ';u)`: find one representative in each local fiber so that the induced degree profile
      is `δ_ρ-1` on the missing-corner fibers and `δ_ρ` on the others, with `|I_ρ| \equiv δ_ρ
      \pmod q`; more sharply, the same-fiber-twin part of the blow-up checklist is redundant: the
      real blow-up core is **fiber-constant pair status** together with the already-known fact that
      the ambient transport point `x_ρ` cuts out exactly `I_ρ`; a stronger sufficient formulation is
      quotient-side content shrinks further still. Writing `q_00:=p↓A`, `q_10:=p↓(A∪{H})`,
      `q_01:=p↓(A∪{J})`, `q_11:=p↓(A∪{H,J})`, the new exact local target is the
      **pair-chamber separation of the hidden choice**: after factoring off the already-isolated
      one-edge predecessor/persistence inputs on the two incident squares, it is enough to prove
      that on each fixed-trace common-edge packet `P_e^\tau`, the pair-chamber map
      `Σ_e=σ^- × σ^+` determines the elementary common-edge hidden choice `h_e`. Equivalently, no
      nontrivial elementary common-edge hidden step may stay inside a single pair-chamber
      cylinder. So the honest direct frontier is now `(1)` explicit fiber-constant pair-status /
      defect-fiber identification plus `(2′)` pure predecessor / persistence inputs +
      pair-chamber separation of the hidden choice;
    - indeed, once those two slice lifts exist inside the fixed Section `40` frame already
      containing `Q_i`, double-slice compatibility / no fixed-side holonomy forces them to coincide;
      because they lie in the two transverse shared-coordinate slices inside `\Pi_i`, their common
      value can only be the unique visible point `s_* = (x_1,y_0,z_0)`, so `\rho` enters `\Pi_i`;
    - once one such root-side entry into `\Pi_i` exists, opposite-side determinacy / no fixed-side
      holonomy for the canonical balanced `2 × 2` tile forces the other side to enter the same
      hyperplane as well; the current in-frame rigidity then upgrades this to a full fan-merge and
      realizes `H_i := H_hex \ {u_i}` on one common Section `40` frame/shadow;
    - once this adjacent-slice-admissibility / fan-merge holds, the scalar half is automatic: `H_i ≅ P_5`, so by the local
      split-vs-path lemma no marked deleted one-error add on the seed can be isolating; after
      localization this gives `\sigma_1(T_hex) = 0` and
      `\sigma_1(T_hex) + |M_R(T_hex)| = 2`, hence Corollary `40.32` closes the branch;
    - the pairwise slice data still determine a unique **visible median shadow**
      `s_* = (x_1,y_0,z_0)` and three relevant slice-shadows above it, but the stronger hidden
      `\mathbf F_2` / cocycle / strict-three-shadow package is **not** currently justified by the
      notes; it should be treated only as a heuristic route to the adjacent-slice-admissibility /
      one-sided-entry / fan-merge step, not as a
      proved reduction;
    - there is also **no hidden Section `40` bridge** below this point: the actual marked
      candidate-pair / host machinery is fixed-frame / fixed-fiber local propagation and begins only
      after one balanced `|D_R| = 3` seed is already localized; thus the first exact theorem absent
      from Section `40` is precisely this **adjacent-slice admissibility** step, equivalently the
      existence of the two adjacent slice lifts for one missing-corner transport in the fixed frame
      of `Q_i`; more atomically, no present theorem yields even the
      **ambient-to-fixed fiber-preserving shared-slice lift**
      `Sh_F(σ',u) \cap F_(b_1) \cap S_c(σ,σ') \neq \varnothing`
      from the already-proved ambient low-cylinder membership on the common fiber, and hence not even
      the older **fixed-frame shared-slice entry** / **one-step shared-slice entry** statement
      `Sh_F(σ',u) \cap S_c(σ,σ') \neq \varnothing`. Even if same-frame realization of `(σ',u)` were granted,
      there is still no present **prescribed shared-slice entry** theorem forcing the stronger
      intersection `Sh_F(σ',u) \cap C_c(σ',u)` with the admissible shared-slice cylinder. After two
      such shared-slice entries for the same root, double-slice compatibility yields the first
      cross-hyperplane entry into `\Pi_i`; more sharply, the direct and shell-host routes already
      meet at the local **compatible degree-congruent transversal** theorem above, because for the
      actual ambiently admissible transport the ambient point itself is then a completer. More
      historically, that common core was isolated as the sum of two ingredients:
      the explicit **fiber-constant pair-status / defect-fiber identification** of the one-corner
      model — after which packet packaging is formal — and, on the quotient side, the sharper
      reduction to **per-fiber single-flip persistence + pair-chamber separation of the hidden
      choice** on each oriented tree edge of `Γ_ρ`: per-fiber persistence already encodes the
      full additive slack model, and after the coarse reduction the residual obstruction is a
      single elementary common-edge hidden step that is silent on both incident filled squares.
      Excluding that hidden choice inside one pair-chamber cylinder then yields the
      degree-congruent transversal. Beyond
      that split common core, one can still continue down the packaged host-side line and either prove
      local completer positivity `c(T)>0` directly or, in the irreducible
      `c(T)=0` regime, prove the compatible injective transversal / finite rooted-template /
      rooted pair-template / candidate-wise two-switch / balanced rooted five-switch exclusion /
      pair-density / one-corner ambient-to-fixed lift / load-preserving pair-exchange /
      signed-transfer normal form / two-fiber missing-corner / binary-cylinder `2`-Helly /
      pair-table Horn / fixed-status Gray/ideal /
      one-edge fixed-status predecessor /
      spanning-tree edge-switch / two-fiber-exchange / unit-transfer
      multi-swap theorem, all of which are bypassed by the fixed-square trace-refinement closure
      package below;
    - **host-silentedge128 lemma (anchored one-corner lift kills the ternary atom).** Assume the
      anchored one-corner lift on `Q_j(x)`: whenever `(x,y)` is a chamber-flat silent edge and `j`
      is the first repaired-defect coordinate with `D_j(x) != D_j(y)`, the shared lower
      repaired-defect prefix together with the shared packet prefix through `j` has a realization on
      the already anchored square `Q_j(x)` with coordinate-`j` repaired opposite defect `D_j(y)`.
      Then `Γ_{Q,e}` is edgeless. Indeed, let `(x,y)` be a silent edge. By choice of `j`,
      `D(x)|_{<j}=D(y)|_{<j}` and `P(x)|_{≤j}=P(y)|_{≤j}`. The lift places the `y`-corner on the
      fixed square `Q_j(x)`. Assuming fixed-square coordinate-`j` opposite-defect
      rigidity, a fixed `Q_j(x)` has at most one repaired coordinate-`j` opposite defect
      compatible with this prefix; hence `D_j(y)=D_j(x)`, contradiction. Therefore no silent edge
      exists. In the prefix language, for fixed lower packet prefix and first label coordinate all
      silent edges have the same sign; two opposite-sign edges would supply exactly the forbidden
      chamber-flat silent edge above;
    - **host-opppair123 lemma (anchored persistence plus realized no-split gives anti-Horn).** Fix a
      forward boundary edge `ab`, the canonical pre-edge state `η_a`, the fixed `Q^-` chamber data,
      and the realized outgoing set `R^+` of repaired opposite defects on `Q^+`. Suppose:
      (i) anchored witness persistence holds, i.e. for every unary witness `λ`, if
      `λ ~ ρ_0^+` for one `ρ_0^+ in R^+`, then the outgoing defect of every admissible
      packet-changing continuation also sees `λ`; and (ii) realized componentwise no-split holds,
      i.e. `|R^+ ∩ C|≤1` for each silent component `C` of `Γ_{Q^+,ab}`. Then `|R^+|≤1`. Proof:
      (i) makes every unary witness incidence constant on `R^+`. The one-square silent-component
      characterization identifies silent components with unary chambers, so all points of `R^+`
      lie in one component `C`. Now (ii) gives `|R^+|=|R^+∩C|≤1`. Hence two admissible
      packet-changing continuations with the same anchored boundary data cannot split into two
      distinct outgoing `Q^+` defects. This is exactly the outgoing anti-Horn / one-witness
      no-holonomy step needed for candidatewise reference-corner boundary well-definedness;
    - **host-orient115 lemma (pair-chamber separation gives two-fiber overlap).** Work on a
      fixed-trace common-edge packet `P_e^τ`, after the one-edge predecessor/persistence inputs have
      reduced every row with `d_00=0` to one of
      `0000, 0001, 0101, 0011, 0111`. Assume the fixed-trace elementary graph is connected on the
      reduced packet and that the pair-chamber map `Σ_e=σ^-×σ^+` separates the elementary hidden
      choice `h_e`, i.e. no nontrivial elementary hidden step lies in one pair-chamber cylinder.
      Then the two-fiber single-flip overlap lemma holds:
      `Ω_10 != emptyset` and `Ω_01 != emptyset` imply `Ω_10∩Ω_01 != emptyset`. If not, the reduced
      admissible table has no slack: the only possible non-overlap transition is between a
      `0101` row and a `0011` row, with no `0111` row available. Take a shortest fixed-trace
      elementary path from the `0101` side to the `0011` side. At the first step where the hidden
      choice changes, no one-square wall has changed, because those wall changes were precisely the
      predecessor/persistence inputs already factored off. Thus both incident chamber labels
      `σ^-` and `σ^+` are unchanged across this nontrivial hidden step, so the step lies inside one
      fiber of `Σ_e`, contradicting pair-chamber separation. Hence the overlap is nonempty, and
      tree-path telescoping yields the degree-congruent transversal for the local one-corner model;
    - **pre-closure audit of the local proof package for the three named atoms.** The primitive input common to
      `host-silentedge128`, `host-opppair123`, and `host-orient115` is the following support-local
      square theorem. The initial direct proof attempt below needed a support-classification theorem
      for statewise squares; the later square-transverse breaker / trace-refinement proof supplies
      that classification.

      **Support-local fourth-corner lemma.** Work in the lower-arity-clean region
      `Gamma_4(T)=P(T)\setminus Low(T)`. Fix a statewise coordinate-`j` incident square `Q_j(x)`,
      freeze the lower repaired-defect prefix `D|_{<j}` and the packet prefix `P|_{≤j}`, and suppose
      a repaired coordinate-`j` opposite defect `ρ_j` occurs in some state with those two frozen
      prefixes. Then `ρ_j` occurs on the same anchored square `Q_j(x)`.

      **Direct proof attempt before trace-refinement.** Let `z` be a state with the frozen prefixes and `D_j(z)=ρ_j`. Replace only the
      coordinate-`j` opposite defect of the anchored square `Q_j(x)` by `ρ_j`, and suppose the
      resulting fourth corner is not admissible. Choose an inclusion-minimal blocker `B` certifying
      non-admissibility. No point of `B` can be supported wholly below coordinate `j`, since the
      lower prefix is unchanged from the admissible state `x`. No point of `B` can be supported
      wholly in the packet prefix through `j`, since that prefix is unchanged from the admissible
      state `z`. Thus every essential element of `B` uses the new coordinate-`j` defect together
      with at most the two square directions defining `Q_j(x)`. If it uses only one square direction,
      it is one of the six binary two-fiber blocker cylinders; if it uses both square directions, it
      is one of the four rooted ternary blocker cylinders. These are exactly the lower-arity
      cylinders contained in `Low(T)`. A genuine quartic blocker cannot occur here: quartic support
      requires four independently variable anchor fibers, while after the two prefixes and the
      anchored square are fixed only the coordinate-`j` corner is variable; the other three corners
      are already realized and therefore cannot be essential in an inclusion-minimal obstruction.
      Hence any minimal obstruction to the fourth corner should lie in `Low(T)`, contradicting
      lower-arity-cleanliness, and the replacement corner would be admissible. The unsupported step
      is the italicized classification: at that stage the notes defined the lower-arity blockers and the
      quartic blocker stratum, but had not established that every statewise fixed-square
      fourth-corner obstruction is forced into those lower-arity cylinders, nor that a residual
      quartic blocker cannot survive after the prefixes and anchored square are frozen. This
      support-local blocker classification is the first remaining proof obligation.

      There is a sharp abstract no-go for this proof strategy. In the four-part promotion complex,
      take four fibers with selected vertices `a,b,c,d`, declare every proper subset of
      `{a,b,c,d}` compatible, and declare only the full quartet incompatible. Then all binary and
      ternary lower-arity cylinders are absent, the three anchored corners are realized, but the
      fourth corner is blocked by a genuine size-`4` minimal blocker. This model is exactly the
      quartic stratum `B_4(T)`. Therefore lower-arity-cleanliness alone cannot prove the
      support-local fourth-corner lemma; one needs an additional graph-specific quartic-exchange
      theorem excluding this full-support blocker on statewise squares.

      The natural flag-complex shortcut is also not justified by the current swap formulas. In the
      anchor-supported one-defect regime singleton swaps are reversible and lower-arity blockers
      remove the binary and ternary failures, but for a fixed deleted anchor set `D` the remaining
      nonlinear datum is the whole induced graph on the transversal `X subseteq d^{-1}(D)`, together
      with the rooted candidate bit. Thus compatibility is a finite rooted-template condition, not a
      proved flag condition on the one-skeleton of `K_prom(T)`. Abstractly, a four-vertex template
      predicate can accept every proper induced restriction while rejecting the full four-set (for
      example by one four-way parity/template bit). Hence `K_prom(T)` being flag, or `B_4(T)=emptyset`
      after removing size-`2` and size-`3` blockers, is exactly extra graph-specific content; it is
      not a consequence of the existing one-defect swap bookkeeping.

      A sharper audit separates the quartic blocker into two parts.  The **candidate-fixed** quartic
      blocker is actually impossible.  Fix one proposed outside candidate/witness `v` and one
      injective one-defect packet `X={x_i}` over deleted anchors `D={d_i}`.  For any retained vertex
      `y`, the degree change under a partial swap `S⊆X` is

      - `Δ_y(S)=Σ_{x_i∈S}(1_{y∼x_i}-1_{y∼d_i})`.

      For an inserted vertex `x_i`, relative to the singleton swap the extra change is

      - `Δ_i(S)=Σ_{x_j∈S\{x_i}}(1_{x_i∼x_j}-1_{x_i∼d_j})`.

      The candidate vertex has the same form, with `x_i` replacing `d_i` in its adjacency sum.  In
      each case admissibility asks that the relevant integer sum lie in one of the two-point intervals
      `{0,1}` or `{-1,0}` (or the singleton `{0}`), because all residues differ from the target by at
      most the number of swapped coordinates, hence by `<q`.  The elementary interval fact is:

      > If every singleton coefficient lies in `I∈{{0},{0,1},{-1,0}}` and every two-term partial sum
      > lies in `I`, then every finite partial sum lies in `I`.

      For `I={0}` this is immediate.  For `I={0,1}`, singleton admissibility gives all coefficients
      `0` or `1`, while two-term admissibility forbids two `1`s; hence every sum is `0` or `1`.  The
      case `I={-1,0}` is the sign reverse.  Thus once all binary and rooted-ternary faces are
      admissible for the **same** candidate/witness, the four-swap is admissible for that same
      candidate/witness.  No genuinely four-way degree term exists in the one-defect swap equations.

      Therefore any remaining full-support quartic blocker must be a **candidate-switching Helly
      failure**: every proper face is certified, but the certifying candidate/witness may depend on
      the face, and the candidate fibers have no common point on the full quartet.  Equivalently,
      after the additive interval lemma, the support-local fourth-corner theorem is reduced to a
      candidate-set Helly/gating theorem for the fixed-square witness space, not to a new
      degree-calculus obstruction.

      This Helly failure has an exact transport normal form.  Let the three upper faces of the
      failed fourth-corner cube have witness packets `Ω_1, Ω_2, Ω_3`.  Since candidate-fixed quartic
      blockers are impossible, every adjacent overlap `Ω_i ∩ Ω_j` can be represented by changing only
      the shared edge trace; hence a minimal candidate-switching blocker is equivalent to a
      fixed-point-free return map obtained by transporting a witness around the upper hexagon

      - `Ω_1 -> Ω_2 -> Ω_3 -> Ω_1`.

      Conversely, a fixed point of this return map is precisely a common witness in
      `Ω_1 ∩ Ω_2 ∩ Ω_3`, after which the single-candidate interval lemma fills the fourth corner.
      Thus the candidate-switching obstruction is the **upper-face no-holonomy theorem** in fixed
      point form.  A sufficient smaller theorem is monotone gated transport: if all three overlap
      transports are order-preserving gates in one finite chamber order on the witness space, then
      the composite is monotone on a finite lattice and has a fixed point, so the Helly failure is
      impossible.  The remaining missing input is therefore not a four-way degree term, but the
      common-order / gate-compatibility theorem for adjacent upper-face witness transports.

      The abstract Helly step in that last sentence is formal.  In a finite median chamber graph,
      gated convex sets are Helly: for three gated sets `A,B,C` with pairwise nonempty intersections,
      choose `a∈B∩C`, `b∈C∩A`, and `c∈A∩B`; the median `m=med(a,b,c)` lies on geodesics
      `ab`, `bc`, and `ca`, hence lies respectively in `C`, `B`, and `A` by convexity.  Thus
      `m∈A∩B∩C`.  Equivalently, composing the gates around the upper hexagon has a fixed point.
      Therefore the candidate-switching blocker is now reduced precisely to proving that the
      localized face-witness packets `Ω_i` are gated/convex in the actual chamber graph and that the
      adjacent-edge transport maps are the corresponding gates.

      There is an important circularity warning.  The existing route to packet gatedness in the
      roadmap passes through one-square silent-edge exclusion / opposite-defect wall detection.  But
      silent-edge exclusion is one of the named atoms that the support-local fourth-corner lemma was
      meant to prove.  Hence gatedness cannot be imported from the current `host-silentedge128`
      package without circularity.  The non-circular primitive must be the lower step:

      > **direct transverse-square gate theorem.** In each localized upper face, every nearest-point
      > move toward a common edge stays inside the witness packet; equivalently, on every transverse
      > square `x,y,y^- in Ω_i` forces `x^- in Ω_i`,

      proved directly from the fixed-witness Horn/additive interval calculus and the local
      candidate-fiber structure, not from one-square silent-component rigidity.

      The fixed-candidate part of this transverse-square theorem has an exact obstruction.  On a
      `2×2` square, assume the same candidate/witness certifies the three corners `00,10,01`.  For
      every affected degree row the two elementary switch contributions are `a,b∈{-1,0,1}`, and the
      admissible interval is one of `{0}`, `{0,1}`, `{-1,0}`.  Since the singleton corners are
      admissible, the only way the fourth corner can fail is:

      - `I={0,1}` and `a=b=1`, so the fourth corner has sum `2`; or
      - `I={-1,0}` and `a=b=-1`, so the fourth corner has sum `-2`.

      Thus the same-candidate missing-corner problem is exactly the exclusion of a **double
      same-sign row saturation**.  This is the genuine mixed anti-Horn content: one-coordinate
      predecessor/persistence data allow each load separately, and only a graph-specific two-fiber
      theorem can rule out both loads landing on the same affected row.

      In graph language the saturation row is explicit.  In the `+` case there is a retained vertex
      `r` which is nonadjacent to both deleted fiber representatives and adjacent to both inserted
      representatives (or to the corresponding candidate replacements), while the lower corner left
      `r` one unit below the forbidden upper level.  Each singleton repair is therefore accepted
      because `r` uses the unique allowed slack, but the two repairs together overfill `r`.  The `-`
      case is the complement statement.  Hence the mixed anti-Horn theorem is equivalently a
      **no shared slack row** theorem: two independent repair fibers cannot spend the same one-unit
      slack of a retained row in the same direction.

      The closed same-trace `P_3` theorem almost applies to this row-saturation certificate.  If the
      two saturated repair vertices have the same trace on the frozen old shell after the slack row
      is marked, then the slack row is an internal distinguisher for a same-trace two-vertex packet;
      adjoining any third vertex on the adjacent face gives exactly the same-trace `P_3` kernel
      already excluded in Section `40`.  Therefore the remaining anti-Horn content is the
      **slack-row trace-coalescence theorem**:

      > whenever two independent repair directions saturate one retained row in the same direction,
      > the two inserted representatives coalesce to one residual trace class after localizing at the
      > saturated row.

      Without this coalescence the same-trace closure cannot be invoked: a shared slack row by itself
      fixes only one coordinate of the two traces, while the two repair vertices may still lie in
      different defect fibers.  Thus the no-shared-slack theorem has been reduced to trace
      coalescence plus the already closed same-trace internal-distinguisher theorem.

      The existing marked-add catalogue already proves this coalescence in the clean terminal
      support case.  In the notation of the height ladder, clean support means
      `alpha_S = beta_S = 0`.  Then the reduced congruence is exact, and the earlier marked-add
      local test says: if both marked add-defects pass the local `deg_(D_R)` / root-edge test, the
      `P_3` branch collapses and the residual triple is `R ≅ K_3`.  Interpreted in the slack-row
      square, this is exactly trace-coalescence: the noncoalesced alternative would be the
      `P_3/C_6` branch.  Consequently a shared-slack anti-Horn obstruction cannot survive on the
      clean rooted `2 K_3` terminal rung.  Any remaining no-shared-slack failure must lie in the
      explicit dirty-support catalogue already listed earlier: marked miss, failed congruence, one
      of the local marked failures, or a nontrivial residue
      `alpha_S - beta_S + t ≡ 0` with `alpha_S + beta_S > 0`.

      A shared-slack row is the smallest possible dirty residue: after localizing at the saturated
      row, the normalized defect budget is one.  In the pure-side notation below this is the first
      unique-defect boundary `h = d_X + d_Y = 1`, i.e. the isolated one-defect edge rather than a new
      clean quartic gate obstruction.  Thus the non-clean remainder of no-shared-slack is exactly the
      budget-one absorption theorem `Abs(1)`: an anchor-supported unique-defect package must admit a
      compatible re-anchor producing `c(T_X)>0`.  Higher dirty residues belong to the general
      `Abs(H)` ladder and are not specific to the transverse-square gate.

      `Abs(1)` is not the trivial singleton re-anchor.  If `x∈O_1` is miss-type with defect
      `z∈L(T)`, then `x` misses `z`; after swapping `z` out and `x` in, the natural candidate `z`
      has the wrong edge to the inserted vertex.  If `x` is add-type with defect `y∈B(T)`, then
      `x~y`; after swapping `y` out, the natural candidate `y` again has the wrong edge sign.  This
      is the precise sense in which singleton swaps are reversible but do not create completers.
      Therefore budget-one absorption needs a genuinely reciprocal outside candidate, or a second
      shell/reseating step, not merely the formal anchored one-defect escape.

      Moreover the reciprocal candidate cannot simply be an opposite one-defect vertex at the same
      original anchor.  A miss-type and an add-type one-defect at the same defect site have raw
      discrepancies `-e_u` and `+e_u`; their sum is a nonzero raw relation of total mass `2<q`.
      By weighted raw short-packet rigidity (`40.16`), every vertex in such a relation would already
      be a completer, contradicting the irreducible `c(T)=0` regime.  Thus budget-one absorption is
      intrinsically a **reanchor-walk** theorem: after the reversible singleton swap, a new reciprocal
      candidate must appear in the new shell, or an iterated singleton-reanchor process must be shown
      acyclic and forced to exit at a positive-completer state.

      This walk theorem has the same orientation obstruction as the one-square silent-edge problem.
      The singleton reanchor graph is undirected at the level currently justified: every allowed
      one-defect swap can be immediately reversed.  Hence no scalar invariant of the current anchored
      state can by itself prove exit unless it also supplies a canonical orientation of reanchor
      edges or a no-holonomy theorem excluding non-backtracking cycles.  In particular, budget-one
      absorption is not a hidden Hall argument; it requires an oriented reanchor potential, or a
      graph-specific cycle-breaker for the singleton reanchor graph.

      The obvious sign invariant does not orient the graph.  A miss-type swap is reversed by the
      deleted low defect, which still has the same wrong nonedge to the inserted vertex; an add-type
      swap is reversed by the deleted high defect, which still has the same wrong edge to the
      inserted vertex.  Thus the miss/add label is attached to the undirected reanchor edge, not to an
      orientation of it.  Any viable potential must use extra packet/chamber data beyond the
      one-defect sign.

      The exact low-set update confirms this.  Let `B=T\L(T)`.

      - If `x` is miss-type with defect `z∈L(T)`, so `x` is complete to `L(T)\{z}` and anticomplete
        to `B`, then for `T'=(T\{z})∪{x}` one has
        `L(T') = {x} ∪ (N_T(z)\setminus {z})`.
        The old vertex `z` is miss-type for `T'`, with defect `x`.
      - If `x` is add-type with defect `y∈B`, so `x` is complete to `L(T)` and sees only `y` in `B`,
        then for `T'=(T\{y})∪{x}` one has
        `L(T') = N_T(y)\setminus {y}`.
        The old vertex `y` is add-type for `T'`, with defect `x`.

      Thus a singleton reanchor is literally an involutive neighborhood-pivot of the low set.  The
      congruence `|L(T')|≡δ [MOD q]` is automatic from the degree residue of the deleted defect, but
      the actual integer size `|L(T')|` can move in either direction.  Consequently neither low-set
      size nor miss/add type gives a descent.  The first plausible positive theorem was a
      **short-cycle exclusion / pivot no-holonomy theorem**: every non-backtracking cycle in this
      neighborhood-pivot graph should produce a raw short-packet relation of total mass `<q`, hence
      a completer by `40.15`/`40.16`.  The trace-refinement proof below replaces this false raw
      telescope by the prime-shell module breaker.

      In fact this no-holonomy statement is false in the raw near-regular category.  Take
      `δ=1`, let the high part `B` be a disjoint perfect matching (so every high vertex has degree
      `1≡δ [MOD q]`), and let the low set be one isolated vertex `z`.  Add outside isolated vertices
      `x_1,x_2,...`, anticomplete to `B` and to each other.  Each `x_i` is miss-type with defect the
      current isolated low vertex, and swapping it in simply changes the isolated low token from
      `z` to `x_i`; no outside vertex is a completer because no outside vertex sees the current low
      singleton.  Thus the singleton reanchor graph contains arbitrary non-backtracking cycles
      obtained by cycling the isolated low token.  The model is highly non-prime/modular, so it does
      not refute the shell theorem, but it proves that `Abs(1)` cannot follow from the raw
      near-regular equations plus short-packet rigidity alone.  The needed input is a
      **prime shell cycle-breaker**: any reanchor cycle must create a module unless some external
      distinguisher exits the cycle to `c(T)>0`.

      This gives a smaller normal form for the prime version.  Along a pure isolated-token reanchor
      cycle, the moving one-defect vertices have the same trace on the frozen high core and the same
      miss/add type with respect to the current token.  If no pivot state has a completer, these
      moving vertices form a false-twin class over every frozen part of the shell.  Primeness then
      supplies an external distinguisher `r` for two consecutive token vertices.  If `r` has the
      completer trace for one of the pivot states, the walk exits.  Otherwise `r` is a false-twin
      breaker for the reanchor-token class.  Therefore the prime cycle-breaker reduces to a
      **reanchor false-twin breaker theorem**: every such minimal breaker either becomes a completer
      after one neighboring pivot, or localizes to the already closed same-trace / false-clone
      distinguisher templates of Section `40`.  This is the exact current local target for `Abs(1)`.

      One cannot simply cite Section `40` at this point.  The Section `40` false-clone closure applies
      after the moving same-trace vertices and their breaker have been routed into one residual fixed
      fiber (stable-house or normalized clone-bag).  A reanchor-cycle breaker is initially only
      external to the moving token class: it distinguishes two token vertices but need not have the
      same residual trace as either token over the frozen shell.  Thus the missing step is a
      **reanchor breaker routing theorem**:

      > every minimal external distinguisher of two consecutive reanchor tokens either has the
      > completer trace for one neighboring pivot, or can be reseated into a Section `40` residual
      > fixed fiber without changing the token pair.

      If this routing theorem holds, Section `40.7`--`40.10` finishes the prime reanchor cycle by
      the same half-graph / shifted-twin-breaker descent.  If it fails, the failure is a new
      mixed-trace reanchor breaker, strictly smaller than the original `Abs(1)` statement.

      Comparing with the square-breaker analysis below, this mixed-trace reanchor breaker is the same
      final local object.  A reanchor token edge plays the role of the repaired square coordinate, the
      external false-twin distinguisher plays the role of the square-transverse breaker, and the first
      row on which it fails to be a completer is the marked dirty row.  Fixed-trace failures are closed
      by Section `40`; clean marked rows are closed by the marked-add catalogue; the only unresolved
      case is a dirty marked row that remains transverse after reanchoring.  Thus `Abs(1)` is
      equivalent, at the current level of reduction, to the same **mixed-trace breaker admissibility**
      theorem that closes square-breaker routing:

      > every minimal mixed-trace breaker with no Section `40` localization and no clean marked-row
      > collapse is admissible as the next repair/reanchor vertex, or its first dirty failed row gives
      > a strictly smaller mixed-trace breaker.

      **Unweighted mixed-trace admissibility target.** In the host-local, unweighted, sub-`q`
      support regime, the desired theorem is the statement above.

      **Proof attempt.** Work in a minimal prime shell-local counterexample and freeze the lower packet frame
      used by the reanchor or square-transverse problem.  Let `C` be the active class of possible
      repair/reanchor vertices having the same frozen trace and not already producing a local
      completer.  The closed fixed-trace theorem says that an internal distinguisher whose residual
      trace is constant on `C` is impossible; the clean marked-add catalogue says that a failed marked
      row with clean support is also impossible.

      For a nonadmissible mixed-trace breaker `r`, let `φ(r)` be the first failed row after those two
      closed cases are removed.  The row `φ(r)` is a genuine mixed-trace breaker: if its incidence bit
      were constant on `C`, marking it would put `r` and the active pair in a Section `40` same-trace /
      false-clone fiber; if its marked support were clean, the marked-add catalogue would collapse it
      to the rooted `K_3` branch or to one of the already excluded clean failures.  Thus the only
      remaining possibility is that `φ(r)` is dirty and nonconstant on `C`.

      Transport a nondecreasing `φ`-step back to the same frozen frame.  Since `φ(r)` is nonconstant
      on `C`, the two fibers

      - `C_0 := {x in C : x notsim φ(r)}`,
      - `C_1 := {x in C : x sim φ(r)}`

      are both proper whenever the step is nontrivial.  The next active edge lies in exactly one of
      these two fibers; replace `C` by that fiber.  Hence every dirty nondecreasing step strictly
      refines the active trace class.  The finite potential

      - first `|C|`,
      - then the lexicographically ordered multiset of all current trace-class sizes

      strictly decreases.  Therefore no nondecreasing dirty failed-row cycle exists.

      This old proof attempt is not by itself a proof.  The omni-saturated carrier repair fixes the
      side-selection and terminal-module objections by minimizing against all outside rows that
      preserve an active edge.  After that repair, the only surviving case is the no-preserved-side
      binary endpoint: every dirty row separates the unique active pair, and the next failed row is a
      fully skew `0001` / dirty shared-slack turn.  Thus the remaining theorem is the prime-shell
      budget-one cycle-breaker isolated above, not a general failed-row acyclicity statement.

      A similar warning applies to fixed-square opposite-defect rigidity.  The raw short-packet
      theorems `40.15`--`40.16` cannot by themselves prove uniqueness of the repaired opposite defect
      on a fixed square.  They say that any nonzero raw relation of total mass `<q` is supported on
      completers, but they do not prohibit several distinct completers of the same local near-regular
      host.  Thus if two repaired coordinate-`j` opposite defects are both admissible on the same
      anchored square with the same frozen prefixes, the obstruction is not a small raw relation; it
      is a **same-square completer multiplicity** problem.  The needed fixed-square theorem is
      therefore a packet/fiber injectivity statement: within the fixed square and frozen prefix
      chamber, the local completer fiber has size at most one.  The proof uses the square/frozen
      packet structure via the square-breaker routing package, not merely the anchored short-packet
      algebra.

      The multiplicity problem has a sharper prime normal form.  Fix the square `Q`, the frozen
      boundary frame `F_Q`, and two distinct admissible repaired opposite defects `p,p'` for the same
      coordinate-`j` slot.  Because both defects complete the same frozen packet, every vertex of
      `F_Q` has the same adjacency to `p` and to `p'`; the pair is a true- or false-twin pair over the
      whole fixed frame.  Thus, in a prime counterexample, there is a breaker `r` with
      `rp != rp'`.  Normalize `rp=1` and `rp'=0`.

      If `r` has a single residual trace after localizing at one marked square side, then the triple
      `r,p,p'` is already inside one of the Section `40` same-trace / false-clone fibers: adjoining
      the marked boundary vertex gives the same `P_3`, paw, or shifted twin-breaker kernel used in
      `40.4`--`40.10`, and the half-graph descent closes it.  Hence a genuine same-square
      multiplicity obstruction must be **square-transverse**: every minimal breaker of `p,p'` changes
      trace when transported across the two adjacent square sides.  This is smaller than arbitrary
      packet/fiber injectivity; the only surviving breaker is one whose first nonconstant coordinate
      is exactly the square coordinate being repaired.

      Consequently the fixed-square rigidity theorem now reduces to a square-transverse routing
      theorem:

      > every minimal breaker of two same-square repaired opposite defects is either a local
      > completer, or can be reseated into a Section `40` residual fixed fiber, or is the first
      > witness-wall change on an outgoing repair path.

      The first alternative contradicts the irreducible `c(T)=0` state, and the second is closed by
      Section `40`.  The third is precisely the interface with repair-fiber cubicality: if the
      first wall change sits in an induced statewise square, then support-local fourth-corner filling
      compares the two repaired defects inside that square and eliminates the transverse breaker.
      Thus same-square completer injectivity, repair-fiber cubicality, and support-local
      fourth-corner filling are not three independent local facts; they close as the single
      **square-breaker routing package**.  The routing step from an arbitrary prime breaker `r` to
      either a Section `40` fixed fiber or an elementary repair-wall edge is exactly the
      conditional trace-refinement mixed-trace descent isolated above.

      The `Q^+` square-representation hypothesis has a separate graph-geometric content.  The proof
      of `host-opppair123` chooses a shortest path in the outgoing repair fiber and then assumes that
      the first change of a unary witness incidence is witnessed by a statewise square `Q_j` with the
      predecessor and the two signed successors as three corners.  This is automatic in a median
      cube/partial-cube repair graph, but it is not a consequence of fourth-corner filling alone.
      The required **repair-fiber cubicality theorem** says that every elementary change of a unary
      wall along a shortest outgoing repair path is contained in an induced statewise square with the
      same anchored boundary prefix.  Equivalently, the outgoing repair fiber has the relevant
      Θ-class / square-completion property for witness walls.  A non-cubical edge would itself be a
      square-transverse breaker, so trace-refinement routing supplies the square.

      The non-cubical alternative can also be normalized.  Let
      `ρ_0,...,ρ_k` be a shortest outgoing repair path from a `λ`-positive realized defect to a
      `λ`-negative realized defect, and let `ρ_{i-1}ρ_i` be the first edge on which the unary witness
      `λ` changes sign.  If this edge is not contained in a statewise square with the same boundary
      prefix, then the `λ`-cut has an exposed boundary edge in the outgoing repair graph.  There are
      only two ways this can happen:

      1. the two endpoints are indistinguishable by all admissible boundary repairs except `λ`; then
         the exposed edge is a bridge inside the fixed repair chamber and the endpoint class is a
         module unless an external breaker exists;
      2. some external breaker distinguishes the two endpoints while not being a local completer.

      In the first case primeness of the ambient shell forces the second case.  After marking `λ`,
      any breaker whose trace is fixed lies in the same Section `40` same-trace / false-clone
      templates as above.  Therefore a genuine failure of repair-fiber cubicality is again a
      **square-transverse breaker**: a prime external distinguisher of the two sides of the first
      witness-wall cut whose first nonconstant coordinate is the repaired square coordinate.  Thus
      `Q^+` square representation reduces to the same square-breaker routing package: route this
      breaker to Section `40`, or use it as the elementary wall edge required by the cubical square.

      Finally, filled-overlap reconstruction is another injectivity statement, not a formal
      consequence of edgeless one-square silent graphs.  Edgelessness identifies the repaired
      opposite defect separately on `Q^-` and `Q^+`, but `host-orient115` also needs the map

      > hidden common-edge choice `h_e` ↦ (repaired opposite defect on `Q^-`,
      > repaired opposite defect on `Q^+`)

      to be injective on the fixed-trace common-edge packet.  The sketched proof tries to get this by
      applying fourth-corner filling on one incident square while holding the other repair fixed, but
      that again uses same-square completer injectivity.  Thus the exact overlap target is
      **filled-overlap pair-injectivity**: two hidden choices with the same pair of incident repaired
      opposite defects must coincide.  It is downstream of same-square injectivity plus the
      square-cubicality needed to compare the two hidden choices.

      This target also has the same breaker normal form.  Fix the trace on the common edge `e` and
      suppose two elementary hidden choices `h,h'` have the same repaired opposite defects on both
      incident filled squares `Q^-` and `Q^+`.  On the union of the two frozen square frames, the two
      hidden choices have identical trace: the left repair freezes all `Q^-` incidences, the right
      repair freezes all `Q^+` incidences, and the common-edge trace is fixed by hypothesis.  Thus
      `h,h'` are twins over the filled-overlap frame.  In a prime counterexample there is a breaker
      `r` distinguishing them.  If `r` is fixed-trace on either incident square, Section `40` closes
      exactly as in the same-square case.  If `r` is not fixed-trace on either side, then the first
      side on which its trace changes is a square-transverse breaker for `Q^-` or `Q^+`.  Hence
      filled-overlap pair-injectivity is not an additional independent theorem after all: it follows
      from the same square-breaker routing package applied to the first incident square that detects
      the hidden-choice breaker.

      The routing package itself is now equivalent to a still smaller admissibility statement.  Take
      a minimal square-transverse breaker `r` for a square with repaired coordinate `j`, chosen so
      that the lower prefix below `j` is frozen and no Section `40` fixed-trace localization is
      possible.  Try to use `r` as the missing repaired opposite defect.  If all affected degree rows
      pass the one-coordinate interval test, then `r` is an admissible outgoing repair and the desired
      repair-wall edge has been found.  If not, let `u` be the first failed row.  The failure cannot be
      a fixed-trace failure, because marking `u` would put `r` and the original repaired defect in the
      same-trace `P_3` / false-clone catalogue already closed in Section `40`.  Thus `u` must itself
      be transverse at coordinate `j`.  The desired descent is to replace the breaker `r` by this
      marked row `u` and obtain a square-transverse breaker with strictly smaller unfrozen support.
      This strict support decrease is not automatic from the interval test; it is the last real
      content of the routing package.  Therefore the remaining exact theorem is:

      > **transverse-breaker admissibility.** A minimal square-transverse breaker with no Section
      > `40` localization satisfies every one-coordinate degree-row interval test, unless its first
      > failed row gives a strictly smaller square-transverse breaker.

      A full unweighted mixed-trace admissibility theorem would prove exactly this support decrease.
      The omni-saturated repair reduces its only nonclean failure to the binary fully skew endpoint;
      after the q-marker/product-firewall closure above, this no longer leaves an independent
      conditional branch.

      The clean terminal support case of this last theorem is already closed.  After marking the
      first failed row, clean support means `alpha_S=beta_S=0` in the earlier marked-add notation.
      There the marked-add catalogue says that if the local `deg_(D_R)` / root-edge tests pass, the
      noncoalesced `P_3` branch collapses to `R ≅ K_3`; and if one of those tests fails, the failure
      is one of the explicit marked miss / low-old / `B_1(D)` / congruence rows already excluded from
      the clean rooted `2K_3` terminal rung.  Therefore a transverse-breaker admissibility failure
      cannot live on clean support.  The dirty alternative is exactly the budget-one `Abs(1)` /
      reanchor-breaker problem, i.e. the same prime-shell cycle-breaker.  Thus the square-breaker
      route and the no-shared-slack route are not yet closed on unweighted host supports.

      **Conditional support-local fourth-corner theorem (unweighted host).** The support-local
      fourth-corner lemma stated above would hold in the host-local unweighted setting after
      failed-row acyclicity is proved.

      **Proof.** The candidate-fixed obstruction is impossible by the additive interval lemma:
      once the same candidate/witness certifies all binary and rooted-ternary faces, every affected
      row has coefficients in one of `{0}`, `{0,1}`, `{-1,0}`, and the two-term tests force the
      full partial sum into the same interval.  Hence a fourth-corner failure must be candidate
      switching.

      For candidate switching, use the direct transverse-square gate.  On a transverse square, the
      only possible fixed-candidate gate failure is the double same-sign slack-row saturation.  If the
      two saturated repairs coalesce after marking the slack row, Section `40` excludes the resulting
      same-trace `P_3` / false-clone kernel.  If they do not coalesce, the clean marked rows are
      handled by the marked-add catalogue and the dirty row is the budget-one `Abs(1)` breaker,
      still conditional on unweighted mixed-trace admissibility.  Therefore every nearest-point move toward the
      common edge stays inside the localized witness packet.

      This local gate condition is global in the finite chamber graph: order coordinates by distance
      to the common edge and repeatedly apply the transverse square closure to the first coordinate on
      a shortest path.  The process never leaves the packet and strictly decreases distance, so the
      packet is gated; gated packets are convex, and the median argument above gives Helly for the
      three upper-face packets.  Their pairwise intersections are the already-realized adjacent faces,
      so Helly gives one common witness for all three faces.  With one common witness fixed, the
      candidate-fixed interval lemma fills the fourth corner.  Thus this historical support-local
      fourth-corner lemma was conditional on failed-row acyclicity before the later closure chain.

      **Conditional host-silentedge128 theorem.** If support-local fourth-corner and fixed-square
      rigidity are proved, every one-square silent graph `Γ_{Q,e}` is edgeless; equivalently the
      prefix-star opposite-sign ternary atom is impossible.

      **Proof.** Suppose `(x,y)` is a chamber-flat silent edge. Let `j` be the first coordinate with
      `D_j(x)\ne D_j(y)`. Then `D(x)|_{<j}=D(y)|_{<j}` and, by chamber-flatness,
      `P(x)|_{≤j}=P(y)|_{≤j}`. Apply the support-local fourth-corner lemma to the square `Q_j(x)`
      with `ρ_j=D_j(y)`. It realizes the `y`-corner on the already anchored square `Q_j(x)`. But the
      fixed-square coordinate-`j` opposite-defect rigidity on `Q_j(x)` says that a fixed square with
      these prefixes has a unique repaired coordinate-`j` opposite defect. Hence
      `D_j(y)=D_j(x)`, contradicting the choice of `j`. Thus no chamber-flat silent edge exists.
      If two prefix-star silent edges of first label coordinate `j` had opposite signs, their two
      endpoints would agree below `j` and disagree only by the sign of the coordinate-`j` repair,
      giving such a chamber-flat silent edge. Therefore the prefix-star sign is unique.

      **Conditional host-opppair123 theorem.** If repair-fiber cubicality and silent-edge exclusion
      are proved, boundary outgoing anchored witness persistence and realized no-split hold on `Q^+`:
      for fixed boundary data `(ab,η_a,σ^-(η_a))`, the realized outgoing set `R^+` contains at most
      one repaired opposite defect.

      **Proof.** First prove witness persistence. Suppose a unary witness `λ` on `Q^+` sees
      `ρ_0^+ in R^+` but misses another `ρ_1^+ in R^+`; choose such a pair with minimum coordinate
      distance inside the outgoing repair fiber. Along a shortest path between them, let `j` be the
      first coordinate where the `λ`-incidence changes. The predecessor vertex, the `λ`-positive
      successor, and the `λ`-negative successor determine three corners of the statewise square
      `Q_j` with the same anchored boundary prefix. By the support-local fourth-corner lemma the
      fourth corner is admissible on this same square. If this fourth corner remains in the old
      packet basin, then the boundary edge `ab` was not the first packet-changing exit; if it leaves
      the basin, then the two successive outgoing repairs are joined by a chamber-flat silent edge in
      `Γ_{Q^+,ab}`. The first case contradicts the definition of the forward boundary edge, and the
      second would contradict the edgelessness supplied by `host-silentedge128`. Hence no such pair
      exists, so each unary witness is either incident to every element of `R^+` or to none.

      By the one-square silent-component characterization, equality of all unary witness incidences
      is exactly equality of silent component in `Γ_{Q^+,ab}`. Since that graph is edgeless by
      `host-silentedge128`, every component is a singleton. The persistence argument places all
      of `R^+` in one component, so `|R^+|≤1`. This is the anchored two-continuation no-holonomy /
      no-split statement on `Q^+`.

      **Conditional host-orient115 theorem.** If filled-overlap pair-injectivity is proved, on every
      fixed-trace common-edge packet `P_e^τ`, the pair-chamber map `Σ_e=σ^-×σ^+` determines the
      elementary common-edge hidden choice `h_e`. Equivalently, no nontrivial elementary common-edge
      hidden step stays inside one pair-chamber cylinder.

      **Proof.** Let `p,p'` be endpoints of an elementary hidden step in `P_e^τ` with
      `Σ_e(p)=Σ_e(p')`. On the incident square `Q^-`, equality of the first chamber coordinate says
      the two repaired opposite defects lie in the same silent component of `Γ_{Q^-,e}`; on `Q^+`,
      equality of the second chamber coordinate says the same in `Γ_{Q^+,e}`. By
      `host-silentedge128`, both silent graphs are edgeless, so the repaired opposite defects on
      `Q^-` and on `Q^+` are separately equal for `p` and `p'`.

      In a filled overlap edge with trace `τ` fixed, the pair of incident repaired opposite defects
      determines the common-edge hidden choice. To see this, assume two hidden choices remain after
      both opposite repairs are fixed. Holding the `Q^-` repair fixed and changing only the hidden
      edge choice gives a fourth-corner problem on `Q^+`; holding the `Q^+` repair fixed gives the
      symmetric fourth-corner problem on `Q^-`. In either square, the lower repaired-defect prefix and
      packet prefix are unchanged, so the support-local fourth-corner lemma realizes the alternate
      corner on the same anchored square. Fixed-square opposite-defect rigidity then identifies the
      two choices. Thus the hidden choice is unique. Therefore `h_e(p)=h_e(p')`; since the step was
      assumed elementary, it is not a nontrivial hidden step inside one pair-chamber cylinder. This is
      pair-chamber separation.

      Combining this with the previous two-fiber overlap lemma gives
      `Ω_10∩Ω_01\ne\varnothing` whenever `Ω_10` and `Ω_01` are nonempty. Tree-path telescoping on
      `Γ_ρ` then gives the compatible degree-congruent transversal for the one-corner local model.
    - consequently the three named host frontiers `host-silentedge128`, `host-opppair123`, and
      `host-orient115` remain conditional on failed-row acyclicity / square-breaker routing:
      support-local fourth-corner filling would follow from direct transverse gates and failed-row
      acyclicity, while square-breaker routing would supply fixed-square opposite-defect injectivity,
      outgoing repair-fiber square representation, and filled-overlap reconstruction. Direct Section
      `40` bootstrapping, the older shell/congruence route, terminal comparison with `T_18`, and the
      distributed-hexagon gluing route all factor through this adjacent-slice-admissibility /
      one-corner fixed-square exactness package rather than giving an independent closure;
   - the old `S = s ⊔ C` shell-selection/congruence problem is a stronger sufficient route, not the
     exact theorem itself;
4. the prime weighted quotient branch is locally closed, and the genuinely separate small bad-module
   alternative from Theorem `17.5` is closed by the module-front analysis below.  Section `22`'s old
   universal target "every regular `A ⊆ M` lifts" is false,
   already for the family `K_{m,m,m}`. More sharply, branch-`(1)` depends on `A` only through its
   profile `(a, alpha)`; rewriting by codimension `s := q - a`, codimension `4` is already fully
   classified, and the overlap window now sharpens to:
   - `q = 11`: impossible by parity;
   - `q = 9`: only the internal `C_5` profile survives;
   - `q = 10`: up to complement, only the internal profiles `C_6` and `2 C_3` survive (equivalently
     the `alpha = 3` side is triangular prism / `K_(3,3)`);
   - the residual `q = 10`, `2 C_3 / K_(3,3)` branch now reduces to the finite `M / T / B` seed
     theorem, equivalently the `U`-free house exceptional theorem;
   - the split branch dies immediately by the `27`-clique core, and the `P_5`-free non-split
     `C_5`-prime branch is a clique-join blow-up of `C_5`, hence also dies by a `K_10`;
   - so every surviving `q = 10` package has an induced `P_5`; full closure now depends only on a
     prime regular modular refinement of the coarse `B / T / Q` partition into the weighted-house
     framework (`33.5/33.6` and `40.11`);
   - more sharply, the only possible failures of that refinement are seed-clone reseating mergers or
     stable same-trace twin-mergers inside one exceptional `B / T / Q` class; after fixing the skew
     data, the residual arithmetic datum is the single `tau`-even parameter `t = T_b + T_c`;
   - more sharply still, after stable descent every residual twin-merger is one homogeneous fixed
     fiber inside a single exceptional class; no mixed-sign quotient survives, so the module front is
     now a one-fiber multiplicity theorem in sizes `11-18`, subordinate only to `t = T_b + T_c`;
   - more sharply again, every complete-sign fiber already gives `K_10`, and every edgeless-sign
     fiber is an equal-clique packing `k K_s`; the only residual one-fiber obstructions are the
     three explicit packings `4 K_3`, `3 K_4`, `4 K_4`;
    - more sharply yet, any regular `10`-set meeting such a fiber in at least `8` vertices is forced
      into the `5 K_2` rescue shape; so size `16` leaves only `4 K_4`, while size `12` leaves only
      the ambiguity `4 K_3 / 3 K_4`, with `3 K_4` admitting no `1`- or `2`-vertex rescue;
    - more sharply finally, the remaining packing front is now a finite supplement-template theorem:
      exact `6 + 4` and `4 + 6` rescue catalogues, where every anticomplete outside edge in
      `4 K_3 / 4 K_4` already collapses to `5 K_2`; only complete supplements and the anticomplete
      `I_6` over the `4 K_1` truncation remain genuinely new;
    - more sharply now, the size-`12` `4 + 6` catalogue separates by truncation type:
      `4 K_1`-rescues force `4 K_3`, `K_4`-rescues force `3 K_4`, and only the middle `2 K_2`
      catalogue is branch-blind; modulo the known `5 K_2` rescue, the common size-`12` ambiguity is
      now exactly the three complete templates `2 K_3 + I_4`, `2 K_2 + K_(3,3)`, and
      `2 K_2 + prism`;
    - more sharply now, those three complete templates split by degree into one isolated
      `6`-regular template `2 K_3 + I_4` and a `7`-regular two-case family
      `2 K_2 + K_(3,3)` / `2 K_2 + prism`; up to complement this is exactly the old `q = 10`
      overlap front `2 C_3 / K_(3,3)` and `C_6 / prism`;
    - more sharply now, the isolated `6`-regular template is not a new family at all: together with
      `2 K_2 + K_(3,3)` it is just the old `2 C_3 / K_(3,3)` branch, so modulo that previously
      developed machinery the only genuinely separate common size-`12` survivor is
      `2 K_2 + prism`, equivalently `C_6 / prism`; size `16` still leaves only `4 K_4`;
    - more sharply now, even that prism template is exactly the old whole-`C_6` completion from
      Proposition `22.9`, so the present size-`12/16` compression contributes no genuinely new
      size-`12` work at all; all new module mass is now concentrated in the single size-`16`
      residual packing `4 K_4`;
    - more sharply now, after importing the known `5 K_2`, the old `q = 10` overlap families, and the
      trivial `I_10 / K_10` witnesses, the size-`16` packing `4 K_4` reduces to one exact smaller
      supplement theorem, equivalently the lone genuinely new regular `10`-set type `2 K_5`;
    - more sharply now, even `2 K_5` is only a packaging artifact: the exact remaining `4 K_4`
      frontier is a `6`-vertex outside kernel `K_5 ⊔ K_1` with mixed sign on `F` (singleton complete
      to all of `F`, `K_5` anticomplete to all of `F`);
    - more sharply now, that mixed-sign kernel is equivalent to a singleton-parameterized `1 + 5`
      theorem in the outside strata: for `P^+(F)` complete to `F` and `P^-(F)` anticomplete to `F`,
      a genuinely new witness survives iff some `u in P^+(F)` has a `K_5` inside
      `P^-(F) ∩ overline{N}(u)`; any such kernel already also yields the old `5 K_2` rescue;
    - more sharply now, any `K_5` inside `P^-(F)` already gives the old `5 K_2` rescue, so the only
      genuinely new issue is whether some such `K_5` is **exposed**, i.e. misses a positive vertex;
      on the top side this is exactly the `P^+(F)`-transversality theorem for `K_5`'s in
      `P^-(F)`;
    - more sharply now, after fixing the canonical positive witness `x_*`, the top-side frontier
      splits into a one-positive branch and a genuine two-positive split-clique theorem: either
      `P^-(F) ∩ overline{N}(x_*)` already contains a `K_5`, or some second positive vertex yields a
      complete-join pattern `K_(5-r) * K_r` across the split by `x_*`;
    - more sharply now, that two-positive split-clique theorem itself is a local seed-completion
      problem: for `u in P^+(F)` and a clique seed `D subseteq M_u^1`, one completes inside
      `L_u(D) = M_u^0 ∩ ⋂_(v in D) N(v)`, and after the one-positive case is removed the exact local
      score is `Phi(u) = max_D (|D| + omega(L_u(D)))`;
    - more sharply now, after excluding the empty-seed one-positive case, those five nonempty seed
      sizes collapse to the three unordered split types `(0,5)`, `(1,4)`, `(2,3)` across
      `(M_u^0, M_u^1)`, with the corresponding local obstructions `K_5` in `M_u^1`, a vertex/`K_4`
      split, and an edge/`K_3` split;
    - more sharply now, once the pure `(0,5)` branch and the vertex/`K_4` `(1,4)` branch are
      excluded, the exposed-`K_5` problem is exactly the `K_2 * K_3` kernel across
      `(M_u^0, M_u^1)`; equivalently, triangle-free edge-completion on every `M_u^1` edge kills the
      remaining top-side `4 K_4` obstruction;
    - more sharply now, that residual `K_2 * K_3` kernel has an exact dual triangle-trace form: for
      each triangle `T subseteq M_u^0`, letting `S_u(T) := M_u^1 ∩ ⋂_(t∈T) N(t)`, the obstruction
      survives iff some `S_u(T)` is non-independent; equivalently, with
      `σ(u) := max_(T∈Δ(M_u^0)) ω(S_u(T))`, one has `Φ(u) = 5` exactly when `σ(u) >= 2`;
    - more sharply now, even these trace graphs are secondary: the live datum is the exact
      edge/triangle incidence kernel `I_u := { (T,e) ∈ Δ(M_u^0) × E(M_u^1) : T subseteq N(e) }`,
      so `Φ(u) = 5` iff `I_u ≠ ∅`; equivalently, for each edge `e = ab` of `M_u^1`, the defect set
      `M_u^0 \ (N(a) ∩ N(b))` must be a triangle transversal of `M_u^0`, and each support graph
      `G[M_u^0 ∩ N(a) ∩ N(b)]` is automatically `K_4`-free because the `(1,4)` branch is already dead;
    - one more exact compression is available: for `e = ab ∈ E(M_u^1)` and `f = xy ∈ E(M_u^0)`, the
      completion fiber `K_u(e,f) := M_u^0 ∩ N(a) ∩ N(b) ∩ N(x) ∩ N(y)` is nonempty iff `f` extends to
      a triangle inside the `K_4`-free support graph `G[M_u^0 ∩ N(a) ∩ N(b)]`; each such fiber is
      automatically independent, so the live top kernel is now the smaller edge/edge completion
      kernel with independent fibers rather than the full edge/triangle incidence relation;
    - more sharply now, once a support triangle `xyz` occurs inside `H_e := G[M_u^0 ∩ N(a) ∩ N(b)]`,
      its three edge-fibers `K_u(e,xy)`, `K_u(e,yz)`, `K_u(e,zx)` are pairwise disjoint independent
      sets, and every vertex of `H_e` seeing two vertices of `xyz` lies in exactly one of them; hence
      the whole edge-sharing neighborhood of a support triangle is an exact rooted tripartite book
      kernel on three independent fibers rather than an arbitrary completion graph;
    - more sharply now, this rooted tripartite-book kernel is already self-similar: for a vertex in
      one fiber, its cross-neighborhoods in the other two fibers are exactly descendant edge-fibers
      of the support triangle through that vertex; consequently every cross-edge carries a smaller
      independent propagation fiber, and the only remaining danger is an extra witness beyond the
      forced opposite root on that descendant fiber;
    - more sharply now, this self-similarity is exact: if `p ∈ A = K_u(e,xy)`, then
      `N_B(p) = K_u(e,py) \ {x}` and `N_C(p) = K_u(e,px) \ {y}`, and cyclically for vertices of
      `B` and `C`; so a cross-edge exists iff a child edge of a support triangle has an extra
      witness beyond its forced root;
    - equivalently, the residual `(2,3)` obstruction is no longer a free tripartite cross-edge
      problem at all: every cross-edge is generated by replacing the forced root on one edge by an
      extra witness, producing a child support triangle and the same kernel again, so the live issue
      is nested descendant-fiber propagation only;
    - more sharply now, this exact self-similarity identifies a still smaller kernel than the rooted
      tripartite book: for a fixed support edge `e = ab ∈ E(M_u^1)`, a sequence
      `v_0, ..., v_m ∈ V(H_e)` is a supported ladder when every consecutive triple is a triangle of
      `H_e` and every skip-`3` pair is a nonedge, equivalently
      `v_{i+3} ∈ K_u(e, v_{i+1} v_{i+2}) \ {v_i}` at each step, so ladder extension is exactly one
      more extra-witness move on the current child edge;
    - equivalently, the residual `(2,3)` branch has now been reduced from rooted tripartite books to
      the triangle-ladder kernel inside the `K_4`-free support graphs `H_e`: the minimal live
      obstruction is a `5`-vertex supported ladder, and every further propagation is nothing but
      extension of this ladder by one new extra witness; in finite-state terms, the remaining task
      is exclusion of cyclic supported ladders in the ordered-triangle propagation digraph;
    - more sharply now, the triangle-ladder recursion has an exact state graph: for a fixed support
      edge `e = ab ∈ E(M_u^1)`, let `D_e` be the ordered-triangle propagation digraph whose
      vertices are ordered triangles `(x,y,z)` of `H_e := G[M_u^0 ∩ N(a) ∩ N(b)]`, with
      `(x,y,z) -> (y,z,w)` iff `w ∈ K_u(e,yz) \ {x}`; then supported ladders are exactly directed
      walks in `D_e`, and cyclic supported ladders are exactly directed cycles in `D_e`;
    - therefore no strict ladder-length descent can follow from the present local axioms alone:
      `K_4`-freeness of `H_e` plus the exact child-fiber rule still allows arbitrarily long cyclic
      supported ladders, witnessed by the family `C_m^2` for all `m >= 6`;
    - equivalently, the residual `(2,3)` branch is now reduced to a smaller exact forbidden-family
      problem: for each support edge `e`, rule out embeddings of the cycle-square skeleton
      `Sq_m` (`m >= 6`), beginning with the octahedral seed `Sq_6 = K_{2,2,2}`, by importing one
      additional global constraint from the ambient modular-host setting;
    - more sharply now, one ambient pruning step is already available before any new local
      monovariant is imported: each support graph `H_e` sits inside the surviving `q = 8`
      negative-side module and therefore inherits the established branch-(1) constraints
      `alpha(H_e) <= 3` and induced-`2 K_2`-freeness;
    - this collapses the infinite cycle-square family sharply: for `Sq_m := C_m^2`, one has
      `alpha(Sq_m) = floor(m / 3)`, while for every `m >= 8` the four vertices
      `v_0, v_1, v_4, v_5` induce `2 K_2`; hence no `Sq_m` with `m >= 8` can occur in any support
      graph `H_e`, and `m >= 10` is already impossible just from `alpha(H_e) <= 3`;
    - therefore the residual cycle-square frontier is finite, not infinite: the only possible
      support-embedded skeletons are the two seeds `Sq_6 = K_{2,2,2}` and
      `Sq_7 = C_7^2 = overline{C_7}`;
    - moreover the missing global input is now exact: profile data alone can still see `Sq_6`
      (`(a, alpha) = (6, 4)` lies on the `X`-only boundary at `q = 8`), but `Sq_7` already lies in
      the dead zone of the lifting criterion, so the remaining obstruction is not profile-only; one
      must prove a support-slice theorem excluding `Sq_6` and `Sq_7`, or reroot every supported
      `Sq_7` into an octahedral `Sq_6`;
    - more sharply now, that support-slice frontier is actually already closed by an ambient theorem
      proved elsewhere in the notes, not by a new local monovariant: every support graph
      `H_e := G[M_u^0 ∩ N(a) ∩ N(b)]` sits inside the surviving `q = 8` negative-side branch-(1)
      module, while Section `28` of `remaining-gap-obstruction-module.md` proves that no such
      ambient module exists (Proposition `28.3` reduces every survivor to `K_{3,3,3}`,
      Proposition `28.4` excludes `K_{3,3,3}`, and Consequence `28.5` kills the entire small-window
      branch);
    - therefore the residual `(2,3)` support problem is vacuous: no support slice `H_e` can contain
      a triangle, so there are no supported ladders, no directed cycles in `D_e`, and in particular
      no support-embedded `Sq_6 = K_{2,2,2}` or `Sq_7 = C_7^2 = overline{C_7}`;
    - thus the exact missing global input was already available: it is the ambient impossibility of
      the branch-(1) negative-side module, not another profile-only host-completion theorem; the
      `(2,3)` module front is closed;
    - more explicitly, Proposition `28.3` makes the ambient branch-(1) container complete tripartite
      (`K_{3,3,3}`), so `Sq_7 = overline{C_7}` dies structurally inside every support slice, while
      Proposition `28.4` kills the octahedral seed `Sq_6 = K_{2,2,2}` globally; hence all
      supported-ladder cycles disappear;
5. at this audit stage, the asymptotic wrappers still required
   `HasPolynomialCostEmptyControlDyadicLift`, or at least the weaker one-parameter target family
   isolated by the recent dyadic-lift audit:
   - for `A := D + 1`, it is enough to prove a terminal-exponent lift that upgrades a
     `2^j`-cascade witness of size `(2^j)^C (2^(j+1))^A` to a `2^(j+1)`-cascade witness of size
     `(2^(j+1))^A`;
   - Section `18` reduces the fixed-support core to a residual-packet / `eta`-top-bit theorem, not
     to naive layerwise divisibility;
   - more sharply, the packet-shadow sum is decomposition-independent and equals `bar eta_m(U)` in
     `M_2(U)`, so the exact theorem is `bar eta_m(U) = 0`;
   - equivalently, this is a **pairwise next-bit compensation theorem** on one fixed support `U`;
   - in dual/basis form, the exact smaller theorem is **pair-cut packet parity** for every pair
     `{u, u_0}`;
   - more sharply, every already-separated block with constant external degree mod `q` on `U` is
     silent for those pair-cut functionals, so only the final undecomposed tail can contribute;
   - writing `rho_R(u) := |N(u) ∩ R|` for that last tail, the frozen first `m` bits give
     `rho_R = K_m 1_U + 2^m h_m`;
   - thus the exact dyadic theorem isolated here is vanishing of the terminal-tail class
     `tau_m(R, U) := [h_m mod 2]`, equivalently one more row-divisibility step
     `rho_R = K_(m+1) 1_U + 2^(m+1) h_(m+1)`;
   - equivalently, the normalized difference cocycle
     `kappa_m(u,v) := (rho_R(u)-rho_R(v))/2^m [MOD 2]` is the coboundary of an aggregate
     complement-orbit class `beta_m`;
   - individual complement-orbit coefficients need not vanish: the exact smaller theorem is
     `beta_m = 0`, equivalently constant incidence parity / symmetric-difference-zero for the active
     complement-orbit family;
   - in fact `beta_m = tau_m(R, U)`; if nonzero, there is a unique cut `S_m` up to complement with
     `kappa_m = delta(S_m)` and `rho_R` taking exactly two values modulo `2^(m+1)` across the cut;
   - after choosing a basepoint, the active complement-pairs admit canonical representatives whose
     symmetric difference is exactly `S_m`;
   - any symmetry of the terminal tail profile preserves `{S_m, U \ S_m}`; profile-primitivity kills
     the bad cut, and profile-transitivity forces `|S_m| = |U| / 2`;
   - more sharply, for the profile-symmetry group `Gamma`, the bad class lies in the fixed space
     `M_2(U)^Gamma`, so the residual dyadic obstruction is exactly a fixed-space / invariant-cut
     problem;
   - if `dim M_2(U)^Gamma = 1`, the obstruction reduces to one explicit cut-template;
   - at the actual last bit `m = j - 1`, balanced cuts are impossible, so transitivity of the
     terminal profile already forces `beta_(j - 1) = 0`;
   - for the full terminal tail-profile group, every bad cut is in fact a union of full
     profile-orbits;
   - so the residual last-bit obstruction is a nonbalanced union-of-profile-orbits, and if the full
     profile action has only two orbits on `U` there is only one cut-template left up to complement;
   - more sharply, the first last-bit case unresolved at this stage is three full profile orbits, where
     the bad cuts are already reduced to singleton-orbit templates;
   - orbit data alone are now sharp: any further dyadic closure has to use arithmetic of the actual
     multiplicities `n_A`, not just the orbit partition;
   - more sharply, in that three-orbit case the residual arithmetic is exactly one `q / 2`-outlier
     among the orbit averages `r_i := (1 / |O_i|) sum_A n_A |A ∩ O_i|`, together with total-edge and
     active-pair parity tests for the bad orbit;
   - those parity tests already kill every odd-outlier template, so the only remaining dyadic case is
     the even-outlier determinant template detected by the cross-determinants
     `Delta_ab := |O_b| E_a - |O_a| E_b`;
   - more sharply, after normalizing by `(q / 2) |O_a| |O_b|`, the opposite-determinant condition is
     redundant and the residual three-orbit obstruction is exactly a two-bit `F_2^2` code from two
     explicit linear forms in the multiplicities `n_A`;
   - if exactly one orbit size is odd, that two-bit obstruction collapses to one concrete divisibility
     test on `Delta_12`;
   - in the remaining all-even case, exactly two orbit sizes have minimal `2`-adic valuation, and a
     canonical first bit `B` splits the front into a minimal-pair branch and a large-orbit branch;
   - branchwise, the even branch is already one divisibility test `q |O_1| |O_3| | Delta_13`, while
     on the odd branch only one nonzero pattern survives up to swapping the minimal-valuation pair;
   - more sharply, explicit singleton-neighborhood models realize vanishing, the minimal-pair branch,
     and the large-orbit branch, so the determinant package is now branchwise sharp and any remaining
      dyadic closure at this stage was genuinely host-side template exclusion;
   - equivalently, the dyadic front is now exactly two host-side fixed-`D` positivity theorems:
     `H_min` for the minimal-pair singleton support `D = O_1` (up to swapping `O_1, O_2`) and
     `H_big` for the large-orbit singleton support `D = O_3`;
   - more sharply still, the all-even valuation lemma forces `|O_1|` even and `4 | |O_3|`, so these
      dyadic singleton supports never hit the new `|D| = 5` host frontier; the first cases open at
      that stage were `H_min` at `|O_1| >= 6` and `H_big` at `|O_3| >= 8`;
    - more sharply again, even-size deleted candidates are impossible; the first outside-candidate
      normal forms are `H_min(6)` with `r in {0,2}` and `H_big(8)` with `r in {0,2,4}`. Thus
      `H_min(6)` is one finite rooted `7`-vertex theorem, while at `H_big(8)` only the regular-`8`
      branch and the balanced marked-quad branch are genuinely new;
    - more sharply yet, `H_min(6)` is already a finite rooted `19`-template problem, the regular-`8`
      branch reduces to the explicit low-degree cases plus the cubic `8`-vertex regular list, and the
      `r = 2` / `r = 4` branches of `H_big(8)` are genuinely new only through non-equitable
      localization failure;
    - more sharply now, `H_min(6)` is reduced to five non-equitable rooted templates, the regular-`8`
      branch is exactly the five cubic `8`-vertex graphs after the explicit low-degree cases, and in
      `H_big(8), r = 4` rooted complement normalizes to `m <= 4`, with genuinely new cases starting
      only at non-equitable `4 + 4` cuts for `m in {2, 3, 4}`;
    - more sharply now, the entire `H_min(6), m = 2` slice is just the rooted two-factor catalogue
      `C_7 / (C_4 ⊔ K_3)`, so `H_min(6)` is down to exactly three genuinely new rooted templates; on
      the balanced `H_big(8), r = 4` side, the non-equitable `m = 2` slice is explicit
      (`P_6 ⊔ K_2` or `K_3 ⊔ P_3 ⊔ K_2`);
    - more sharply now, the `H_min(6)` residual splits as two cubic-root `m = 3` templates plus one
      explicit complementary `m = 4` lift of `P_4 ⊔ K_2`, while the balanced `H_big(8), r = 4`
      branch is a finite catalogue: nine cases at `m = 3`, eleven at `m = 4`, or `15` cases up to
      rooted complement;
    - more sharply now, that balanced `H_big(8), r = 4` catalogue is itself a single structural
      kernel: after removing the equitable seeds `(I_4, 2 K_2)`, `(2 K_2, C_4)`, `(C_4, K_4)`, the
      whole branch is exactly the canonical non-equitable `4 + 4` edge-gap-two kernel;
    - more sharply now, this marked-quad edge-gap-two kernel is not irreducible: every such `4 + 4`
      pair descends by equal-cardinality one-vertex localization to a `3 + 3` edge-gap-one pair, so
      the balanced `H_big(8), r = 4` frontier is absorbed into the old `H_big(8), r = 2`
      non-equitable localization-failure branch;
    - more sharply now, this is the minimal-kernel reduction on the balanced large-orbit side:
      there is no irreducible balanced `r = 4` branch at all, and any irreducible balanced carry
      obstruction already occurs at the smaller `3 + 3` edge-gap-one kernel, i.e. exactly in the
      old `H_big(8), r = 2` localization-failure branch;
    - more sharply now, this minimal `3 + 3` branch is itself finite and explicit: up to swapping
      sides the only edge-gap-one ordered pairs are `(I_3, K_2 ⊔ K_1)`, `(K_2 ⊔ K_1, P_3)`,
      `(P_3, K_3)`; rooted complement merges the first and third, and equitability is impossible at
      edge gap `1` on `3` vertices, so the whole balanced `H_big(8)` carry frontier is exactly two
      minimal non-equitable kernels, the extreme kernel `I_3 / (K_2 ⊔ K_1)` and the middle kernel
      `(K_2 ⊔ K_1) / P_3`;
    - more sharply now, this two-kernel frontier is already the `q = 8` boundary packet in disguise:
      on a proper target-`4` near-regular `7`-set `S = A ⊔ B` with `|A| = 4`, `|B| = 3`, every
      surviving packet vertex is an anti-completer with trace `B`, so the residual class is the
      single discrepancy class `g := [1_B - 1_A] ∈ M_8(S)` of exact order `4`; thus the balanced
      large-orbit obstruction is genuinely a carry obstruction, not a parity-pairing phenomenon, and
      the old marked-quad `4 + 4` branch is just four copies of this one order-`4` class before
      localization to the two explicit `3 + 3` kernels;
    - more sharply now, this `q = 8` packet picture actually closes the balanced large-orbit side:
      after one-vertex localization, any nonzero balanced carry would have to live on one of the two
      explicit `3 + 3` kernels `I_3 / (K_2 ⊔ K_1)` or `(K_2 ⊔ K_1) / P_3`, but on those kernels the
      needed support is already explicit, so the pointwise-compensation / cyclic-rigidity /
      off-cyclic-descent package rules both kernels out;
    - therefore no nonzero balanced carry survives on `H_big(8)`: the order-`4` anti-completer
      class `g := [1_B - 1_A]` cannot occur on either minimal kernel, the old balanced `4 + 4`
      marked-quad branch is eliminated as well, and the dyadic frontier drops to the residual
      `H_min(6)` three-template branch (two cubic-root `m = 3` templates plus the complementary
      `m = 4` lift of `P_4 ⊔ K_2`);
    - more sharply now, this residual `H_min(6)` branch already has the same `P_4 -> P_3` descent
      seen in the closed fixed-fiber obstruction mechanism: the complementary `m = 4` lift is not
      localization-irreducible, because deleting an endpoint of the `P_4` side leaves an induced
      `P_3` while the opposite `K_2` side is unchanged;
    - consequently, the honest localization-irreducible dyadic kernel is already the two cubic-root
      `m = 3` templates; the listed `m = 4` branch is only an endpoint extension of that kernel,
      not a third primitive host-side mechanism;
    - more sharply now, even those two cubic-root `m = 3` survivors are not a genuinely new dyadic
      host family: by construction each is a cubic root, so reinstating the peeled minimal-pair
      vertex produces a connected cubic `8`-vertex closure, and the old cubic classification leaves
      only the two connected closures `H_T` (true-twin) and `H_F` (false-twin);
    - equivalently, the two dyadic `m = 3` survivors differ only by the sign of one restored twin
      edge: their primitive localized support is the same-trace `P_3` kernel, and the true-twin /
      false-twin choice is only the one-bit cubic closure datum;
    - therefore the residual dyadic `m = 3` branch is already the old cubic `H_T/H_F` branch in
      localized form, not a third host-side obstruction mechanism; with the `P_4 -> P_3` descent,
      the whole residual `H_min(6)` side is absorbed by the previously closed fixed-fiber /
      prime-weighted-quotient / same-trace package;
    - more sharply now, the only primitive localized support in those cubic roots is the same-trace
      `P_3` kernel itself, and that kernel is already excluded by the closed same-trace
      internal-distinguisher theorem on the residual fixed fiber;
    - therefore neither cubic-root `m = 3` template survives, and the endpoint-extension `m = 4`
      lift cannot survive either; the **finite localized** dyadic host-template frontier is empty;
    - raw parity pairing on `R` is too weak, because it misses the carry contribution hidden inside
      those aggregate complement-orbit coefficients;
    - the standard Section `18` obstruction shows that current `m`-bit data alone do not force this,
      and low-rank shadow space by itself is not enough.
    - more sharply now, any nonzero aggregate class `beta_m = [1_S]` can be compressed
      set-theoretically to a three-block singleton-cut obstruction by merging profile orbits on each
      side of the cut; the bridge is that these merged blocks need not be genuine homogeneous
      terminal profile orbits.  Thus the global dyadic theorem is a coarsening-stability /
      many-orbit projection theorem: localize the arbitrary orbit-union cut to an actual fixed-`D`
      host instance to which the closed `H_min/H_big` analysis applies.
    - more exactly, the immediate projection is only a **weighted fixed-`D`** instance: a merged
      block carries orbit-size weights and nonhomogeneous lower profile data.  The closed
      `H_min/H_big` templates are ordinary homogeneous-orbit closures, so the bridge is the
      weight-splitting theorem extracting one genuine bad suborbit.
    - this weight-splitting is not automatic from the determinant algebra: the all-even /
      minimal-valuation branch may appear only after merging two orbit contributions, and the
      half-`q` determinant valuation can be created by the sum even when neither summand is an
      ordinary bad singleton orbit.  Thus the weighted theorem or an extra host-localization
      principle was the audit target here.
    - more sharply now, the weighted theorem has the same mixed-trace form as the host
      square-breaker / reanchor blocker.  If a merged orbit-union block is bad but no genuine suborbit
      is bad, the first internal profile boundary is invisible to the current `m`-bit tail data but
      visible to lower profile data; fixed-trace boundaries are absorbed by the closed same-trace /
      cubic templates, so the only non-split case is a dirty mixed-trace breaker with orbit-size
      weights.  Thus dyadic coarsening-stability follows from a weighted mixed-trace splitting
      theorem: split off the first internal profile boundary while preserving the bad cut, iterate to
      a homogeneous orbit, and invoke the closed `H_min/H_big` analysis.  This is the weighted dyadic
      avatar of mixed-trace breaker admissibility.
    - more sharply now, the attempted weighted primitive-carry proof divides a minimal weighted
      orbit-union obstruction by the common `2`-adic factor of its internal boundary coefficients and
      retains the odd primitive support.  The formal identity `[1_B]=[1_{B_0}]+[1_{B_1}]` preserves
      the aggregate class in `M_2(U)`, but by itself did not prove that refinement preserves the full
      bad determinant/carry cut or that some primitive boundary is an admissible split.  The q-marker
      audit localizes the primitive boundary to the host low-set-update kernel; the fully skew
      carrier/marker coupling branch is closed above by the product-firewall transport trap, so this
      warning is historical rather than a current blocker.

So the sections below record the candidate route that once depended on q-marker carrier/marker
coupling before the closure above: unweighted host atoms close by the low-set-update cycle-breaker,
dyadic aggregation closes by the weighted pointwise carry audit, and the positive-cost successor bridge follows by
bit-by-bit constancy of the dropped-tail residue.

## Where the formalization stands

The current reduction chain has already moved the main asymptotic bottleneck through the following
equivalent or downstream targets:

1. fixed-witness terminal regularization;
2. one-control host terminal regularization;
3. bounded-host terminal regularization;
4. single-control host terminal regularization;
5. exact-card single-control host terminal regularization.

On the finite side, the key positive bridge is now already in place:

- `hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees`,
- together with its witness-level wrappers in `RegularInducedSubgraph/Modular/Cascade.lean`,

shows that an empty-control fixed-modulus cascade becomes a control-block modular cascade as soon as
one supplies a nonempty separated block family with constant external degree modulo `q` on the top
host.

So the present obstruction is no longer "find a weaker terminal host collapse." It is:

> **produce or propagate the external-block residue data on the top host of a fixed-modulus witness / empty-control cascade.**

However, the zero-cost version is already impossible: the script
`verify_d0_empty_control_external_block_bridge_counterexample.py` checks `K_2`, where the whole graph
is already a fixed-modulus cascade witness of size `q = 2`, but there is no room for any nonempty
separated control block. So the live target is a **positive-cost / one-more-exponent** external-block
bridge, not the literal `D = 0` case.

## Critical path

### 1. Expose the honest asymptotic frontier

`RegularInducedSubgraph/Modular/Asymptotic.lean` now exposes
`HasPolynomialCostEmptyControlExternalBlockBridge` and the positive-dyadic self-target
`HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge`, but these are now known to be
**equivalent repackagings** of the corresponding terminal control-block modular cascade bridges. So
they are still useful bookkeeping layers, but they are not genuinely weaker theorem targets. With
`D = 0` already refuted, the live theorem target is therefore a **positive-cost / successor**
terminal bridge together with the finite data it needs.

### 2. Prove the finite external-block bridge

The next finite theorem should start from a large fixed-modulus witness or empty-control
fixed-modulus cascade and produce:

- a top host `s`,
- an empty-control cascade chain from `s`,
- a nonempty separated control-block family on `s`,
- and `HasConstantModExternalBlockDegrees` for that family.

This is the literal missing input needed by the control-block modular cascade bridge.

### 3. Attack external-block data production

This is the real mathematical step left on the modular-control side.

There is one useful sharpening.  The finite bookkeeping obstruction is only the
**empty-chain** case.  If

- `HasFixedModulusCascadeFrom G q s (u :: chain)`

is already nonempty, then the first dropped layer `s \ u`, and inductively all later dropped layers,
are separated from the terminal bucket and have constant external degree modulo `q` by the defining
drop-residue clauses of the cascade.  Thus a nonempty fixed-modulus cascade automatically carries
the external-block family needed by
`hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees`.

So the bridge is not "how do we turn dropped layers into blocks?" That part is formal.  The honest
positive-cost theorem is:

> from a large fixed-modulus witness whose representing cascade may be empty, force a terminal
> nonempty cascade of size `q` (or equivalently the refinement-data exact self-bridge).

This is exactly where the successor terminal bridge and the `q*q -> q` refinement-data theorem enter.
Before the dyadic tail theorem, no argument forced that nonempty step without reintroducing the same
dropped-tail row-sum problem.

If the dyadic tail theorem (`beta_m=0` at every bit) is supplied by q-marker carrier/marker coupling,
the row-sum input is supplied as follows.  In the refinement-data package, write

> `r(v) := |N(v) ∩ (s \ w)|`

for the dropped-tail degree of `v∈w`.  The host-degree congruence gives `r(v)` constant modulo
`2^0`.  Suppose inductively that `r(v)=K_m+2^m h_m(v)` is constant modulo `2^m`.  The terminal-tail
class `tau_m=[h_m mod 2]` is exactly the aggregate complement-orbit class `beta_m` from the dyadic
lift analysis.  Weighted mixed-trace splitting gives `beta_m=0`, so the parity of `h_m(v)` is
constant on `w`, and `r(v)` is constant modulo `2^(m+1)`.  Iterating for `m=0,...,j-1` yields

> `r(v) ≡ K_j [MOD q]`

for all `v∈w`.

By Proposition `3.1` in `remaining-gap-math-memo.md`, constancy of the dropped-tail residue is
equivalent to regularity of `G[w]`, because `|w|=q`.  The existing exact control block `t` has
`|t|=q-1` and constant exact degree `e` into every vertex of `w`, so regularity of `G[w]` makes
`(w,t)` a bounded exact single-control witness.  The block `t` is nonempty for positive dyadic
`q`, and the already-carried separated blocks retain their constant external residues.  Therefore the
positive-cost successor external-block bridge holds.

This supersedes the earlier proposed subproblems (strengthening host iteration, pair bucketing, or
carrying dropped pieces as explicit proof-blocks): the bit-by-bit dyadic tail theorem gives the
dropped-part residue directly, with exactly one factor `2` spent per binary digit.

## Strategic branches

### Branch A: direct budget-`1` collapse

This branch is now **refuted**. The script
`verify_q8_terminal_host_counterexample.py` exhibits a graph on `11` vertices with:

- an exact-card fixed-modulus single-control modular host witness of size `8` at modulus `8`;
- equivalently, a bounded fixed-modulus control-block modular host witness of size `8` with budget
  `1`;
- no regular induced subgraph on at least `8` vertices.

So neither `HasExactCardFixedSingleControlHostTerminalRegularization` nor
`HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1` can hold in full
generality. The cubic forcing-threshold shortcut remains a valid conditional implication, but it is
no longer a realistic theorem target.

### Branch B: dyadic lift plus external-block bridge

With Branch A ruled out, the dyadic program becomes the main line: prove the empty-control lift and
then bridge into the control-block modular cascade package by supplying the missing external-block
data.

The current Lean surface now makes the surviving targets explicit:

- `HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge`
  asks only for the self-bridge at positive dyadic moduli `q = 2^j` with `j > 0`, avoiding the
  impossible `q = 1` terminal control-block case;
- `HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge`
  is the corresponding data-explicit self-target. The new equivalence theorem shows that it is not
  actually weaker than the terminal self-bridge; it just exposes the missing external-block data on
  the terminal bucket;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge`
  is the new honest finite self-target behind the dropped-part route: from a bounded host witness of
  size `q * q`, recover a bounded exact single-control witness of size `q` with control budget
  `q - 1`;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`
  is the richer self-target that matches the current `Cascade.lean` output exactly: from the full
  refinement-data package (ambient modular degrees, exact control degree, host modular degree, and
  residual external-block data), recover a bounded exact single-control witness of size `q`. This
  immediately implies the stripped step-exact bridge and all of its downstream regularization
  wrappers;
- `hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_self`
  records what the current host-step theorem already delivers: the `q * q -> q` self-step produces a
  structured exact-card fixed single-control modular host witness with control size exactly `q - 1`;
- `HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade`
  isolates the strongest local dropped-part route from that structured output, while
  `HasExactCardFixedSingleControlHostMaximalControlUpgrade`
  keeps only the weaker direct exact-upgrade conclusion needed downstream. These stripped upgrade
  surfaces remain useful diagnostics, but the refinement-data bridge above is now the honest theorem
  interface closest to the actual finite proof output;
- `HasPolynomialCostEmptyControlExternalBlockBridge`
  isolates the actual finite data needed to pass from the empty-control fixed-modulus cascade package
  to the control-block modular cascade package, although the script
  `verify_d0_empty_control_external_block_bridge_counterexample.py` shows that the zero-cost case is
  false already at `q = 2`. The new equivalence theorem shows that this full bridge is just a
  data-explicit presentation of the terminal control-block modular cascade bridge;
- `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge`
  isolates the strongest purely terminal bounded-host statement that would feed this route directly.

The same `q = 8` graph now also shows that the **budget-`1`** instance of this host-to-cascade
shortcut is false: `verify_q8_terminal_host_counterexample.py` finds no fixed-modulus control-block
modular cascade witness of size `8` on that graph. So Branch B can no longer factor only through a
terminal bounded-host witness.

The positive-dyadic host reductions remain useful structural reductions, but the honest live theorem
target is now the **positive-cost / successor terminal bridge together with the refinement-data exact
self-bridge above the current `Cascade` output**. The direct exact-upgrade theorem survives as the
strongest stripped benchmark, not as the primary interface.

`Asymptotic.lean` now packages that successor route explicitly:
- `hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge`
  shows that a one-step exact bridge at budget `D + 1` would yield fixed-witness terminal
  regularization at exponent `D + 2`;
- the corresponding forcing-threshold, eventual-domination, and `TargetStatement` wrappers are now
  wired through this successor route as well.

## Recommended order of attack

1. Record the `q = 8` obstruction so the false budget-`1` target does not stay on the critical path.
2. Keep the strengthened finite host/cascade packaging; it remains the right bookkeeping layer for any
   proof that manufactures external-block data.
3. Keep the new positive-dyadic bridge reductions in `Asymptotic.lean`, but treat
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge` only as a
   reduction identity, not as a realistic budget-`1` target.
4. Focus the live proof effort on proving
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`, i.e. on
   collapsing the full `q * q -> q` refinement-data package to a bounded exact single-control witness.
   Keep `HasExactCardFixedSingleControlHostMaximalControlUpgrade` as the strongest stripped benchmark
   and computational test surface below it. The stronger residue-host route is now only a diagnostic
   layer, not the main target.

The new finite self-theorem sharpens this further: the current proof already gives a structured
exact-card single-control modular host witness with control size `q - 1`, and now the code also
packages the richer refinement data that produced it. So the remaining theorem cannot factor through
the old unrestricted exact-card host regularization route—that route is already dead by the `q = 8`
counterexample. But it also cannot simply be the strongest local residue upgrade:
`verify_q4_structured_residue_upgrade_counterexample.py` shows that this stronger structured
residue-host step is already false at `q = 4`. So the live theorem has to use the special
`q - 1`-control structure and the surrounding refinement data coming from the `q * q -> q` host-step
output **without** insisting on a same-shape residue host witness.

The small dyadic cases are cleaner now as well:

- `q = 2` is trivial;
- `q = 4` is settled externally by Dyson-McKay's `N_4 = 8`, since every `16`-vertex graph already
  contains a regular induced `4`-set;
- so the first genuinely new dyadic case is `q = 8`.

The separate first-bit audit has also sharpened.  The parity-to-mod-`4` lift is equivalent to the
loss-`32` even selector: every even induced graph should contain a `1/32`-large induced subgraph with
degrees congruent modulo `4`.  In maximal-witness packet form, if `W` has residue `r` and `m=|W|`, then an
outside packet `B` appends iff `deg_B` is constant on `W` and `deg_W(b)+deg_B(b)` hits the shifted
residue on `B`.  Olson removes the old-frame balancing obstruction.  Two chamber caps are now exact:
the zero-shift chamber `{b:deg_W(b)=r}` has independence number at most `3m`, and the `+1` chamber
`{b:deg_W(b)=r+1}` has clique number at most `3m`; the dense cap uses Olson on
`((1_{bw}-1_{bw0}),1-1_{bw0})`, forcing `|B|=deg_B(w0) [MOD 4]` inside a clique.  The remaining
first-bit obstruction is therefore the nonzero affine target-subsum/self-layer problem, not old-frame
zero-sum balancing.  There is one mixed zero-target rule between these two chambers: an old-zero
independent packet in `{deg_W=r}` and a clique packet in `{deg_W=r+1}` with old degree `|K|` append
together when their cross graph is empty with `|K|=0`, or complete with `|I|=0`, modulo `4`.
In cross-regular form this mixed rule is `c_I=kappa`, `|K|+c_K=kappa`, and
`|I|c_I=|K|c_K [MOD 4]`.
Old-frame counting adds `r|I|=0` and `m kappa=(r+1)|K|`.
With `kappa=|K|`, odd `r` forces `|I|=0`, and odd `m-r-1` forces `|K|=0`.
Equivalently, `( |I|-|K| )kappa=-|K|^2 [MOD 4]`.
In general, two internally regular cross-uniform chamber packets append exactly when
`a+d_a+epsilon|B_b|=b+d_b+epsilon|B_a|=r+delta_a+delta_b [MOD 4]`; this scalar equation is now the
packet analogue of the bounded-word augmentation table.  For a finite packet system, the normal form is
`a_j+d_j+sum_{k != j}epsilon_{jk}|B_k|=r+sum_k delta_k [MOD 4]` for every active packet.
The exact quotient replaces the uniform term by cross-regular residues `c_{jk}`, with
`|B_j|c_{jk}=|B_k|c_{kj}`; then `R_j=a_j+d_j+sum_{k != j}c_{jk}` must first be independent of `j`, and
only then must hit the single scalar target `r+sum_k delta_k`.
Summing the packet rows gives the global scalar
`S r+(S-m)Delta=2e(B) [MOD 4]`, with `S=sum s_j`, `Delta=sum delta_j`, and
`2e(B)=sum_j s_jd_j+sum_{j != k}s_jc_{jk}`; if `m+S` is odd, the enlarged target residue is even.
Each old increment also satisfies `m delta_j=a_j|B_j| [MOD 4]` by double-counting between `W` and the
packet.
The old witness satisfies `mr=2e(W) [MOD 4]`, so odd `m` forces `r` even.
Thus for odd `m` the target is `r+m^{-1}sum_j a_j|B_j|`; for `m=0 [MOD 4]`, odd-size packets must lie
in chamber `0`; for `m=2 [MOD 4]`, chamber/size products must be even and determine `delta_j` modulo `2`.
Equivalently, for `m=0` the size-`2` packets must lie in even chambers, while for `m=2` every odd-size
packet must lie in an even chamber.
The one-packet test is `m(a+d-r)=a|B| [MOD 4]` for an internally regular packet in chamber `a`.
For `m=0 [MOD 4]`, this reduces to the admissible chamber/size condition `a|B|=0`, while the packet must
still realize the prescribed old increment `delta=a+d-r`.
For two packets this reduces to `(s_a-s_b)c_{ab}=s_b((a+d_a)-(b+d_b))` plus the target
`c_{ab}=r+delta_a+delta_b-a-d_a`.
After substitution this is the single congruence
`(s_a-s_b)(r+delta_a+delta_b-a-d_a)=s_b((a+d_a)-(b+d_b)) [MOD 4]`.
For odd `m`, substitute `delta_a=m^{-1}a s_a` and `delta_b=m^{-1}b s_b` to remove old increments.
On odd-size packet subsystems, cross parities are symmetric and the first-bit condition is the labelled
quotient equation `a_j+d_j+deg_Q(j)=constant [MOD 2]`; the full `c_{jk}` residues are the carry.
The edge-count symmetry stratifies by size modulo `4`: odd sizes determine opposite residues up to units,
size `0` against odd forces the odd packet's incoming residue to vanish, size `2` pairs only synchronize
parity, and size `0` pairs are unconstrained modulo `4`.
For odd packets specifically, equal size residues give symmetric cross residues and opposite size
residues give sign reversal modulo `4`.
Same-chamber same-external-profile packets coalesce in this normal form whenever their two cross-degree
residues agree; row compatibility forces that equality in any appendable system, so an appendable
primitive packet system uses at most one packet from each such profile.
The replacement route has an equally exact self-error form.  For an old-balanced `B subset P_t`, put
`eta_B(b)=t+deg_B(b)-r-delta`; deleting `D subset W` and writing `lambda=r+delta-R` requires
`deg_D=lambda` on `W\D` and `deg_D(b)=eta_B(b)+lambda` on `B`, together with
`sum_B(eta_B+lambda)=|D|delta` and `lambda(m-|D|)=|D|r-2e(D) [MOD 4]`.
In fully signed form `deg_B-deg_D=K` on `W\D` and `deg_B-deg_D=r+K-t` on `B`; summing gives
`(m-|D|-|B|)K=(|B|-|D|)r+2e(D)-2e(B) [MOD 4]`.
If the signed old balance holds on all of `W`, the old-frame scalar is `mK=|B|t-|D|r [MOD 4]`.
Thus odd `m` determines `K`, `m=2` fixes only its parity after an evenness test, and `m=0` requires
`|B|t=|D|r` with `K` free from old-frame counting.
For odd `m`, these combine to the intrinsic test
`(m-|D|-|B|)(|B|t-|D|r)=m((|B|-|D|)r+2e(D)-2e(B)) [MOD 4]`.
In particular, odd `t` and odd `|B|` force even `|D|`.
At the atom level, a defective old-balanced `S` with defect `phi_S` admits a signed repair only if
`c(m-|D|)=|D|r-2e(D)` and `|S|c=|D|delta_S+sum_S phi_S [MOD 4]`.
For `|D|=1`, this forces `c=0,r=0` or `c=1,r=m-1`, and all atom defects lie in `{c,c-1}`.
For `|D|<4`, the defect support must lie in `{c,c-1,...,c-|D|}` with `0<=c<=|D|`; `|D|=3` is the first
small correction size with no pointwise support restriction.
In exact-basis direction spectra, singleton shifts come only from old vertices isolated from or complete
to the kept old witness; pair shifts come from anticomplete, split, or complete old pairs, with shifts
`a`, `a-1`, or `a-2` according to `a=|N_W(b_g) cap D|`.
Since the empty deletion gives shift `0`, any terminal direction with
`|C_g|>=R(4,4)` and `|C_g|>2m+5` has at most one nonzero small-deletion shift; otherwise the repaired
spectrum contains three residues and hence either both Ramsey extremes or both middle pseudo-split
residues.
Disjoint usable deletions add shifts while total size is below four, so two disjoint unit-shift old
repairs are impossible in this very-large-fiber branch.
Hence unit-shift branches force an intersecting family of nonzero singleton/pair repairs, while
`sigma=2` is the only branch where disjoint nonzero repairs can survive by summing to zero.
For unit `sigma`, those nonzero pair repairs are a star or are contained in one old triangle.
Equivalently, a kernel `K_g` of at most three old vertices captures every nonzero singleton/pair shift.
For `sigma=2`, the only nonzero pair repairs are anticomplete old pairs inside `N_W(b_g)` or complete
old pairs outside `N_W(b_g)`.
In that branch all usable singleton shifts are zero: isolated old deletion vertices are missed by
`b_g`, and universal old deletion vertices are hit by `b_g`.
Equivalently, repaired spectra are `{0,1}` or `{2,3}` in the unit-shift branch and `{0,2}` or `{1,3}`
in the `sigma=2` branch.
These mean, respectively, `alpha<=3` with `2K_2`-free, `omega<=3` with `C_4`-free, `alpha<=3` with
`C_4`-free, and `omega<=3` with `2K_2`-free.
Up to complement, the two exact-basis hereditary endpoints are `alpha<=3` plus `2K_2`-free for unit
`sigma`, and `alpha<=3` plus `C_4`-free for `sigma=2`.
A `C_5` clique-blow-up piece larger than `11m/5` already closes: equal bag selection is regular, and if
some bag has size at most `m/5`, adjacent clique caps force total size at most `11m/5`.
In the self-complementary independent-bag orientation, the three-consecutive selector is stronger:
terminal cyclic components have every three consecutive bags of total at most `m+3`, hence total size at
most `(5m+15)/3`.
Endpoint anchor reductions: in the `2K_2`-free/`alpha<=3` branch every edge dominates all but three
vertices; in the `C_4`-free/`alpha<=3` branch every nonedge leaves clique common-neighborhood and
common-nonneighborhood parts, each of size at most `m`.
For an anchor pair `p,q` with `epsilon=1_{pq}`, equal exclusive wings of size `h` close exactly when the
wing union is `(h+epsilon-1)`-regular modulo `4` and, in a nonzero exact-basis direction, `h` is odd.
The `h=1` atom forbids cross-edges for edge anchors and cross-nonedges for nonedge anchors.
Thus both sparse hereditary endpoints are actually `(2K_2,C_4)`-free, so pseudo-split structure bounds a
terminal exact-basis direction by `m+8`.
The `25m/8` class margin also gives, for `m>24`, an augmented atom with `|S|=delta_S=0`, so
`sum_S phi_S=-2e(S)`.
On the boundary finite-alphabet side, the odd-word insoluble branch now has a minimal Arf normal form:
after localizing to a bad closed support, the even kernel is exactly `{0,1_U}`, so `|U|` is even,
`1_U in ker(A(Q[U])+diag(tau))`, `dim ker<=2`, and the only remaining obstruction bit is
`e(Q[U])-(1/2)|{i:tau_i=1}|=1 [MOD 2]`.  Any larger even kernel gives a proper closed support and is not
an irreducible whole-class obstruction.
At the exact Davenport boundary top `X=e_1^3...e_r^3`, the import budget is also fixed: if
`h_X(sum_i a_i e_i)=sum_i a_i` for `0<=a_i<=3`, then exporting `Y` from the retained side and importing
the forced matching boundary value leaves size `|B|-|Y|+h_X(sigma(Y))`.  Hence every graph-compatible
export in a terminal endpoint satisfies `|Y|-h_X(sigma(Y))>=|B|-m`; otherwise the coordinate exchange
already produces a larger congruent selector.  In deficit form (`d=m-|B|>=0`), all compatible exports
must have `h_X(sigma(Y))-|Y|<=d`.
Equivalently,
`h_X(sigma(Y))-|Y|=sum_y(h_X(sigma(y))-1)-4kappa(Y)`.  Carry-free compatible exports have total
singleton surplus at most `d`; at deficit zero, two positive-surplus retained vertices cannot be a
compatible carry-free pair.
For an old-balanced retained block `S`, a proper cut `Y` with both sides graph-compatible must also obey
`4 supp(sigma(Y))<=|S|+2d`, since `h_X(g)+h_X(-g)=4 supp(g)`.  Thus deficit-zero compatible cuts below
size four disappear, and four-block cuts are one-coordinate.

## Supporting work that is useful but not on the critical path

- Keep external computational evidence separate from the formal proof line. The `q = 4` exhaustive
  search note in `notes/q4-terminal-host-search.md` is still useful reconnaissance, but it is no
  longer the reason the `q = 4` slice is known: that slice now follows from `N_4 = 8`.
- The explicit `q = 8` counterexample in `verify_q8_terminal_host_counterexample.py` is strong
  enough to rule out the old budget-`1` target, but it still does **not** identify the missing
  external-block theorem.
- The script `verify_d0_empty_control_external_block_bridge_counterexample.py` shows that the
  zero-cost external-block bridge is false already on `K_2`, so any surviving theorem must lose at
  least one extra factor of `q` before asking for a nonempty separated control-block family.
- The new equivalence theorems in `Asymptotic.lean` show that the external-block bridge formulations
  are not a separate weaker frontier. The false residue route is now exposed explicitly, and the live
  finite frontier is the richer refinement-data exact bridge above the current host-step output, with
  the direct exact upgrade as its stripped shadow.
- An exhaustive Python search found no `q = 2` counterexample to the `q * q -> q` self-step exact
  bridge up to `n = 7`. This is only computational evidence, but it supports continuing on the
  positive-dyadic self-step route rather than abandoning it.
- `verify_q4_structured_residue_upgrade_counterexample.py` is the key new pruning result: it gives a
  graph with the structured `q - 1`-control modular-host witness but no structured residue-host
  witness anywhere, while bounded exact witnesses still exist. So future proof work should target the
  richer refinement-data bridge or, at minimum, the weaker exact-upgrade theorem, not try to revive
  the residue-host route.
- The two proof heuristics worth keeping are now:
  1. completion/discrepancy on target near-regular `(q - 1)`-sets;
  2. fixed-`U` dyadic lifting through the half-obstructions `eta_m(U)`.
  The old naive balanced-halving idea should be treated only as a possible sufficient shortcut, not
  as the main formulation of the gap.
- The completion/discrepancy route has sharpened further:
  1. every near-regular `(q - 1)`-set automatically carries a nonempty zero-sum packet of outside
     discrepancy classes, by Davenport in `M_q(S) ~= C_q^(q - 2)`;
  2. for proper targets `1 <= r <= q - 2`, any zero-sum packet of size strictly less than `q / 2`
     already forces a regular induced `q`-set;
  3. the endpoint cases `r = 0` and `r = q - 1` must be split off as independent/clique alternatives;
  4. so the true missing lemma is a proper missing-pattern / short-packet forcing statement, not mere
     existence of a zero-sum relation.
  5. the strongest direct route is now packet compression: among all proper near-regular `(q - 1)`-sets,
     pick a minimal nonempty zero-packet and prove its size is `< q / 2`.
  6. pushing that route further, the only surviving `p < q` obstruction is a boundary `q / 2`-block
     of anti-completers, but the isolated anti-packet lemma looks too weak: the last move has to use
     global minimality across all proper near-regular sets, not just one local block.
  7. in the boundary case, the leftover layer `W` is another zero-packet and must realize the exact
     residue compensation `deg_W(b)-deg_W(a) \\equiv q/2-1 [MOD q]`, but that modular surplus is not
     enough by itself: `(q/2-1)` anti-completers plus `2` empty-trace vertices already realize it
     without producing any short zero-subpacket.
  8. the live direct target is therefore a **supported seeding approach**: the `2` empty-trace
     vertices alone are too weak, and any successful reseating must recruit a large outside support
     set (from anti-completers and/or other vertices of `W`) to manufacture a different proper
     near-regular `S'` carrying a genuine completer.
  9. more sharply, any successful supported reseating must satisfy a **pointwise compensation law**
     `deg_T(a)-deg_T(b)=x+deg_Y(a)-deg_Y(b)+sigma_{ab}` and therefore force many genuine
     `A`-over-`B` separator vertices in the support whenever the deleted set is not `B`-heavier than
     `A`.
  10. pushing that one step further, the cyclic part is completely rigid, and after subtracting both
      the cyclic contribution and the deleted-set bias, the off-cyclic level functions collapse to
      total oscillation at most `2`;
  11. hence any nonconstant compensation matrix produces a uniform extremal rectangle `A_+ × B_-`, and
      one off-cyclic separator lowers the extremal compensation by exactly `1` on its own separated
      subrectangle;
  12. this resolves `(1,0)`, `(0,1)`, `(2,0)`, and `(0,2)` by descent, leaving only the mixed
      `(1,1)` pattern as irreducible;
  13. but the mixed `(1,1)` case also yields to iterated one-vertex descent until no doubly-mixed
      support remains, and terminal one-sided traces fall into the already-settled `(1,0)` / `(0,1)`
      branches;
  14. so the direct supported-seeding / packet-compression route is now **locally closed**.
- All vertex-transitive cases are positive: any vertex-transitive graph on `q^2` vertices already
  contains a regular induced `q`-set on a `2`-power orbit cut. So any counterexample must be highly
  asymmetric.
- Use `Scratch.lean` only for local theorem-shape experiments and small finite sanity checks.
- Update the README when the frontier moves, but avoid letting the documentation get ahead of the
  actual theorems.

## Things to avoid

- Do not spend time rephrasing already-settled equivalences unless they expose genuinely new finite
  data.
- Do not conflate "degrees are constant in `G[s]` on `u`" with "degrees are constant in `G[u]`".
  The whole point of the current obstruction is the missing contribution from `s \ u`.
- Do not treat the `q = 4` computation as the proof of the `q = 4` slice; it is reconnaissance,
  while the honest proof now comes from `N_4 = 8`.
- Do not treat naive balanced-halving as the core conjecture: deleted layers can reintroduce residue
  on the final `q`-set unless one controls the surviving half-obstructions `eta_m(U)`.
