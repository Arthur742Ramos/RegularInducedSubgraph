# Remaining Gap: Detailed Math Memo

## Q-marker localization re-audit correction

This memo records the final q-marker closure.  Omni-saturated carriers repair the side-selection and terminal-module
objections; same-defect reanchor turns and long reanchor cycles reduce to a first-return
defect-switching square; and the exact singleton low-set update forces a marked two-class quartet.
The deleted defects `{d,e}` have one trace, the inserted vertices `{x,y}` have a second trace, and the
two traces differ exactly on the shared-slack marker `R`; the four vertices induce `C_4` in the
miss/miss case and `2K_2` in the add/add case.

The low-set congruence forces `|R|` to be a positive multiple of `q`; if no outside vertex splits `R`,
then `R` is a proper nontrivial module of the prime shell, impossible.  If an outside vertex splits
`R`, the omni-saturated dirty-split theorem gives either a Section-`40` / marked-add exit, a
preserved-side submarker, or the fully skew positive AND square.  The preserved-side branch contradicts
minimality.

The fully skew branch was the remaining issue.  The previous proof claimed that the dirty-split collapse to a
binary crossing component bounds the new marker by `2`, but that only bounds the active carrier, not
the shared-slack marker.  The marker consists of retained low rows, and many such rows can remain
parallel to the same binary crossing component.  Thus the low-set congruence does not contradict the
fully skew q-marker branch.  The remaining theorem is q-marker carrier/marker coupling: prove that a
fully skew splitter produces a proper first-return submarker, or else forces the whole marker to be a
prime-shell module, or else gives a closed Section-`40` / marked-add / completer exit.  The
product-firewall and transport argument below supplies this theorem for the tracked endpoint.

The current live form is sharper than this older statement.  Frozen q-divisible same-trace markers
close by the modular-cluster lemma; exact high-null no-second-splitter closes by isolated-neighbor
deletion or the roof false-clone `P_3`; and singleton-lift exact two-splitters close by the
`U_1`/`Sigma_rf` roof gate.  The remaining endpoint is the marker-splitting zero-sum atom: complete
outside-trace fibers have nonzero residues whose total is `0 [MOD q]`, but no proper
first-return-complete fiber union has residue zero.

This missing implication is not automatic even in the smallest q-marker case.  For `q=4`, the
incidence pattern

- `R={a_1,b_1,a_2,b_2}`;
- active binary components `{a_1,b_1}` and `{a_2,b_2}`;
- `d,e` miss all of `R`, while `x,y` see all of `R`;
- `z_1` sees `a_1,a_2` and misses `b_1,b_2`;
- `z_2` sees `a_1,b_2` and misses `b_1,a_2`;

is fully skew on every active binary component, but it leaves a marker of size exactly `q`.  Thus
binary active-carrier collapse alone does not produce a sub-`q` marker; any closure must use an
extra first-return, degree, or admissibility invariant not yet written.

The latest finite audit removes the remaining static split-quotient escapes from this atom.  In the
extremal add/add `q-2` packet, every `U`-using regular selection must use a single compensator component
large enough for the required `k(H)` clique; the only multi-component selection is the `U`-free
proper-divisor equal-clique bypass.  Once those selections and same-trace/raw short-packet exits are
removed, the live form is a product firewall: provenance rows cut only the residual-pair/compensator
coordinate, while ambient high-error rows cut the large marker packet.  The missing theorem is the
ordered first-return routing that makes those two cuts share one fixed frame; the sub-`q` transport
trap below closes exactly this routing theorem.

Equivalently, a complete proof must add one of two currently missing inputs: a
**provenance-admissible fully skew splitter** theorem, or a first-return side-marker theorem for one
side of `R cap N(z)` or `R \ N(z)`.  Any history-sensitive degree argument would have to produce one
of these two outcomes.  The product-firewall transport closure supplies this input for the tracked
endpoint.

The side-marker theorem must preserve the full low-set update, not merely split the set `R`.  A fully
skew splitter can make both sides nonempty while preserving no active binary pair.  What is needed is
that, after first-return transport through the splitter boundary, one side becomes the entire
shared-slack set of a new marked two-class quartet; then low-set congruence gives a smaller positive
multiple of `q`, contradicting minimality.

The admissibility route has its own selection gap.  Primeness of the shell gives an arbitrary outside
splitter when `R` is not a module, but it does not give a splitter with first-failed-row or
transverse-breaker provenance.  Since arbitrary fully skew splitters can have large `epsilon`, an
admissibility proof must first prove provenance selection: some splitter of `R` comes from the
first-return failed-row / transverse-breaker family, and only then prove that such a splitter passes
the repair interval tests.

This matches the transverse-breaker support-decrease endpoint.  If a provenance splitter is not
interval-admissible, its first failed row must become a strictly smaller transverse breaker.  In
q-marker terms this is exactly the assertion that one side of the failed row's split of `R` is the
complete shared-slack marker of a new first-return quartet.  Thus the remaining atom is:

> **q-marker provenance/support-decrease theorem:** in the fully skew first-return q-marker endpoint,
> either a provenance splitter is admissible, or its first failed row carries a genuine smaller
> first-return shared-slack marker.

Here "carries" is substantive.  A failed interval row is initially a row of the current peeled set,
not automatically a new outside repair-boundary candidate.  The missing theorem must first transport
that failed row to a valid breaker in the same first-return frame, and then prove that its q-marker
support is strictly smaller.

The word "first" is also ordered data.  A static fully skew splitter can fail interval tests on many
low rows at once; choosing a useful failed row requires the first-return wall order from the repair
path.  No unordered interval-counting argument supplies this order.

Even with such an order, the failed support must be marker-complete.  A first failed wall can give a
proper prefix or a singleton obstruction, but q-marker minimality only applies if that support is
exactly the shared-slack set of a new marked two-class quartet.  Smaller support without the full
low-set-update identity is not enough.

The first failed wall must also be marker-internal.  A failure at one of the old deleted defects,
at an inserted-root degree test, or at a filler row may be a local obstruction, but it is not a
smaller q-marker.  Such non-marker first failures must be routed to Section `40`, marked-add, or
completer exits before the minimality argument can be used.

So the final atom splits into three concrete subclaims: provenance selection for a splitter in the
ordered first-return failed-row / transverse-breaker family; local exit for non-marker first failures;
and marker-complete descent for marker-internal first failures.

The provenance-selection subclaim itself is not implied by primeness.  In the abstract marker table,
one may let every row in the designated first-return/provenance family be constant on `R` and add a
single non-provenance outside row that splits `R`.  Then `R` is not a module, but no provenance row
splits it.  A proof must therefore route arbitrary prime distinguishers into the repair-boundary /
transverse-breaker family; it cannot use primeness alone.

Equivalently, omni-saturation is not enough by itself.  The saturation arguments minimize over valid
dirty-row / repair-boundary traces, whereas a prime-shell distinguisher of `R` may be an ambient row
outside that family.  The missing statement is an ambient-to-provenance routing theorem: every ambient
splitter of a first-return q-marker must either cause a Section-`40`, marked-add, or completer exit, or
force some valid first-return/provenance row to split the marker.  Without that bridge, the
provenance family can be constant on `R` while the ambient shell is still prime.

The local non-marker exit clause is closed, but only after such an ordered provenance row exists.  An
inserted-root failure is the mixed miss/add or wrong-root-edge case already removed by the five-vertex
case table and marked-add catalogue.  A failure at an old defect is the same-defect turn closed by the
same-trace / false-clone argument, or the marked add/miss root-edge test.  A filler-row failure means
the double corner is not failing solely on the proposed marker; after marking the filler it falls into
the explicit marked miss / low-old / `B_1(D)` / congruence catalogue, unless it is already a completer.
Thus non-marker first failures exit locally; the remaining issue is the strength of provenance
selection.

Marker-complete descent is formal once provenance is strengthened to **square-provenance**.  Namely,
the selected splitter must come with the ordered first-return singleton square and the whole
wall-failure set `F(z)`, not merely a distinguished failed row.  After the non-marker exits are
removed, `F(z) subseteq R`; the singleton low-set update identifies `F(z)` exactly as the
shared-slack marker of the transported marked two-class quartet.  If `z` splits `R`, then
`0<|F(z)|<|R|`, and the low-set congruence contradicts minimality.  Thus a nonadmissible
square-provenance splitter cannot survive.  The remaining open point is to route an arbitrary ambient
marker splitter to this square-provenance data.

After an exact size-`q` marker is isolated, the ambient part can be sharpened.  If `|R|=q` and every
row of the peeled state `T\R` is constant on `R`, then all rows of `R` receive the same contribution
from `T\R`.  Since all rows of `R` are low, their degrees in `T` are congruent to the same residue
`delta-1`, so their internal degrees in `G[R]` are congruent modulo `q`.  These internal degrees lie
between `0` and `q-1`; hence they are equal and `R` itself is a regular induced `q`-set.  Thus an
irreducible exact q-marker must have a state-internal splitter in `T\R`.  The blocker then becomes
routing such a state-internal filler/high/low splitter to a local exit or to square-provenance.

This is not yet enough.  A static state-internal splitter can merely balance the degrees of `R`.
For `q=4`, take `R={a,b,c,d}` with only `ab` inside `R`, and add a filler `v` adjacent exactly to
`c,d`.  Then all vertices of `R` have equal degree in `R union {v}`, while `v` splits `R`; no
first-return square provenance follows from this static table.  The remaining theorem must use the
ordered first-return geometry, not just degree balancing.

This exact-marker reduction has its own prerequisite: the notes currently prove only that
`|R|` is a positive multiple of `q`.  For a larger marker `|R|=m q`, constancy of `T\R` on `R` gives
only congruence of the internal degrees in `G[R]` modulo `q`; the degrees can differ by multiples of
`q`, so the interval-collapse argument no longer applies.  Thus the remaining q-marker blocker has
two layers: reduce a larger positive-multiple marker to an exact size-`q` marker (or get a regular
`q`-set directly from it), and then prove state-internal-to-square-provenance routing at exact size
`q`.

The large-marker layer would follow from an ordered-prefix/no-q-jump theorem.  Track, along the
first-return repair path, the prefix `F_t` of marker rows whose slack has become double-spent.  If each
marker-internal prefix is a complete first-return shared-slack marker, congruence forces every
nonempty prefix to have size divisible by `q`, so the first positive prefix has size `q` unless one
wall introduces at least `q` rows simultaneously.  The needed no-jump statement is that such a
simultaneous wall block either contains a regular induced `q`-set, gives a local Section-`40` /
marked-add / completer exit, or exposes a smaller complete marker.  No such theorem is currently in
the notes.

Equivalently, let `P` be the last complete prefix with `|P|<q`, and let the next simultaneous wall
block be `B`.  After choosing `B_0 subseteq B` so `|P union B_0|=q`, every leftover row in `B\B_0`
must either split the marked square frame (giving square-provenance descent), fall into the
same-trace / false-clone catalogue with the chosen rows, or use internal adjacency inside `B` to
separate the block.  Thus the irreducible jump blocker is a simultaneous wall block that avoids both
Section `40` trace coalescence and smaller-marker splitting.

The frozen same-trace part is now separated from the circular external-block bridge.  If a
q-divisible same-trace marker `F` has every outside vertex constant on it, then all internal degrees in
`G[F]` are congruent modulo `q`.  If `G[F]` has an induced `P_3`, this is exactly the roof
false-clone Section-`40` template over the marked quartet (or its complement).  If not, `G[F]` is a
disjoint union of cliques.  The congruent-degree condition
makes all clique sizes congruent modulo `q`; a clique of size at least `q` gives `K_q`, while if all
cliques have common size `s<q`, choosing `g=gcd(s,q)` vertices from each of `q/g` cliques gives a
regular induced `q`-set.  Thus frozen large markers close outright.

The remaining large-marker issue is the non-frozen simultaneous wall block: after an exact `q`-prefix
is chosen, leftover wall rows must avoid both same-trace `P_3` localization and the frozen-fiber
cluster extraction.  That part still requires ordered first-return wall structure; importing the
positive-cost external-block bridge remains circular.

The non-frozen survivor can be stated as a zero-sum atom.  Refine the marker by complete outside trace
on the peeled state and marked frame.  A fiber of size `0 [MOD q]` is frozen and closed by the
cluster/P3 argument.  A proper union of fibers with total size `0 [MOD q]` is fatal if it is
first-return-complete, because it is a smaller shared-slack marker.  Therefore an irreducible
large marker has only nonzero fiber residues, total residue zero, and no proper first-return-complete
zero-sum union.  The no-q-jump theorem must rule out exactly this simultaneous-wall zero-sum atom.

A lexicographic tie-break of a simultaneous wall block is not enough.  The low-set congruence applies
only to complete shared-slack sets of actual transported first-return squares.  An arbitrary prefix of
a simultaneous block need not be such a square's whole failure set, so using it would reintroduce the
marker-completeness gap.

At exact size, the internal splitter has a normalized trace.  A splitter in `L\R` sees all of
`{d,e,x,y}`: the one-defect traces make it adjacent to `x,y`, and the low-set update makes `d,e`
adjacent to all low rows outside `R`.  A splitter in `B\{d,e}` misses all of `{d,e,x,y}`.  Hence exact
routing reduces to two cases, a low universal splitter and a high null splitter, each nonconstant on
`R`.  The five-vertex seed is still only local; the missing step is to use such a splitter either to
package the seed in Section `40` or to produce a square-provenance wall with a proper side of `R`.

The low universal case has a `(q+1)`-set trap.  Put `S=R union {v}`.  If every vertex outside `S` is
constant on `S`, then all vertices of `S` have congruent induced degrees modulo `q`; since
`|S|=q+1`, this already forces exact regularity (a mixed `0/q` degree pair is impossible).  Thus an
irreducible exact marker with a low universal splitter needs a second splitter of `S`.  A second
splitter constant on `R` but not on `v` should be Section-`40` fixed-trace data, while a second
splitter of `R` should feed square-provenance descent.  This argument does not yet cover the high null
case: the high splitter has residue `delta`, while the marker rows have residue `delta-1`, so
`R union {v}` need not have congruent induced degrees modulo `q`.

If a high null splitter has no second splitter on `S=R union {v}`, then `S` has a one-excess normal
form: every marker row has the same induced degree `a`, and `v` has degree `a+1`.  If some neighbor
`u` of `v` has no internal neighbor in `R`, removing `u` leaves a regular `q`-set.  Thus the remaining
high-null finite blocker is the one-excess graph where every neighbor of `v` also has an internal
neighbor in the marker.

This finite one-excess blocker is real as a bare degree pattern.  For `q=8`, let `R=A union C` with
`A={a_1,a_2,a_3,a_4}` and `C={c_1,c_2,c_3,c_4}`.  Put a cycle on `C`, matching edges `c_i a_i`, and
edges `a_1a_2`, `a_3a_4`.  Add `v` adjacent exactly to `A`.  Then all marker rows have degree `3` in
`R union {v}`, while `v` has degree `4`; deleting any one vertex fails to produce an `8`-vertex
regular induced subgraph.  Hence the high-null one-excess case cannot be closed by the finite
`q+1` degree pattern alone.

But the irreducible one-excess case always contains same-trace Section-`40` material.  Put
`A=N(v) cap R`, so `|A|=a+1`; vertices in `A` have degree `a-1` inside `R`, and vertices outside `A`
have degree `a`.  If `G[R]` were induced-`P_3`-free, it would be a disjoint union of cliques, and no
clique could mix `A` with `R\A`.  The `A`-cliques would all have size `a`, impossible for
`|A|=a+1` unless `a=1`; for `a=1`, deleting an isolated neighbor of `v` is already a regular
`q`-set.  Therefore every nontrivial high-null one-excess survivor contains an induced same-trace
`P_3` in `R`.

This is not a new packaging theorem: in miss/miss the marked quartet is the `C_4`
`d-e-x-y-d`, and marker rows have roof false-clone trace `{x,y}` over the edge `xy`; in add/add the
complement of the marked `2K_2` gives the same template.  Thus the forced marker `P_3` is exactly the
`Sigma_rf` case routed by Section `40.3` and closed by Consequence `40.10`.  High-null with no second
splitter on `R union {v}` is therefore closed; only the high-null two-splitter branch remains.

Thus the exact-size endpoint is now a two-splitter routing theorem.  A normalized state-internal
splitter `v` of `R` is fixed, and some second vertex `w` splits `S=R union {v}`.  Either `w` also
splits `R`, in which case it must be routed to square-provenance or to a local exit, or `w` is constant
on `R` and distinguishes only `v`, in which case it is a singleton-lift/false-clone gate over the
normalized splitter.

The singleton-lift gate is closed by the existing roof machinery.  Since `w` is constant on the whole
marker, the marker is one roof false-clone bag over the marked quartet, and `v,w` are the
opposite-side breaker pair.  This is `U_1` in the miss/miss orientation and its complement in add/add;
Proposition `39.10` and Proposition `40.3` reseed it or return it to the closed house-reseating /
same-trace catalogue.  Thus the exact-size work is only the marker-splitting two-splitter theorem:
the second splitter is also nonconstant on `R`.  Static degree counting no longer closes this branch,
because `w` may be an ambient row rather than another state-internal low/high row.

The surviving branch is the nonregular sign-vector zero-sum atom.  The even-`q` perfect-matching
table remains only an incidence-level warning, since that marker is already regular.  In an
irreducible exact atom, `G[R]` must be nonregular, so the `P_3`-free version has unequal clique sizes
whose degree differences are compensated by state-internal/outside trace fibers.  The complete
outside-trace fiber residues are still nonzero and sum to zero only all together.  Therefore the
remaining exact two-splitter branch and the non-frozen simultaneous-wall branch are the same residual
object viewed at exact and large scale: a first-return zero-sum atom that must be killed by
provenance/order, not by static trace-fiber algebra.

There is a final local simplification before the true atom.  If the marker contains a same-trace
`P_3`, Section `40.10` closes it, so the residual marker is a union of cliques.  A provenance splitter
that cuts one clique distinguishes adjacent same-trace twins, which is the roof/twin-breaker gate
handled by `U_1` and `Sigma_rf` in Sections `39`--`40`.  Thus the irreducible zero-sum atom is
clique-coherent: all surviving provenance splitters are constant on each internal marker clique, and
only the weighted clique quotient remains.

Within each complete outside-trace fiber, all clique sizes are equal: outside contribution is the same
throughout the fiber, marker rows have the same low residue, and clique sizes are all `<q`.  Hence the
residual quotient is a minimal zero-sum sequence of packet weights `n_i s_i` in `Z/qZ`, where each
packet consists of `n_i` cliques of common size `s_i`.  Zero-residue packets and proper
first-return-complete zero-sum unions are already closed.

The quotient is also sparse: for every divisor `h` of `q`, there are fewer than `q/h` cliques of size
at least `h`; otherwise taking `h` vertices from each of `q/h` such cliques gives a regular induced
`q`-set.  Thus dense clique quotients are already impossible.

Arithmetic still does not close the atom.  For `q=8`, `K_5 disjoint_union K_3` has exact size `q`, is
nonregular and `P_3`-free, is divisor-sparse, and has minimal zero-sum packet weights `5+3=0` in
`Z/8Z`.  Outside trace packets can compensate the internal degree difference.  Therefore the last
input must be first-return/provenance or weighted-quotient packaging, not a bare zero-sum lemma.

At exact size, minimal zero-sum is automatic: positive packet weights sum to the integer `q`, so no
proper packet union can have residue zero.  The exact atom is therefore just a nonregular
clique-coherent packet partition of `q` with outside/state-internal residue compensation.

If these sub-`q` packets can be packaged as a prime weighted quotient with the marked quartet and the
splitter packets, Consequence `40.12` closes the atom.  Thus the final obstruction is equivalently a
failure of weighted-quotient packaging for the minimal zero-sum packet atom.

More precisely, the needed theorem is smaller than Consequence `40.12`: the exact atom needs a
regular selection of total weight `q` from the marker packets plus the normalized splitter/provenance
packets, not a full total-weight `q^2` quotient.  The final finite target is a packet-quotient
regular-selection theorem: either the packet quotient has an induced regular `q`-selection, or it
packages into Section `40`, or it exposes a proper first-return-complete zero-sum marker.

Equivalently, the last atom is an explicit integer feasibility problem: choose equal-size slices from
some marker cliques and choose compatible weights from splitter/provenance packets so the total weight
is `q` and every chosen quotient type has the same induced degree.  Marker-only solutions are exactly
the divisor-selection lemma; solutions using splitter packets are the finite compensator selection
that replaces a global completer.

In the two-packet case, one compensator pattern closes the atom.  If the marker cliques have sizes
`a>b`, `a+b=q`, and a splitter packet contains a clique of size `t=(a-b)/2` complete to the smaller
clique and anticomplete to the larger, then selecting `a-t=b+t` vertices from the larger clique, all
`b` smaller-clique vertices, and the `t` compensators gives a `b+t-1` regular `q`-set.  The
`q=8`, `K_5 disjoint_union K_3` pattern is closed by a single such compensator vertex.

This condition is also necessary inside the one-sided two-clique quotient.  If a regular `q`-selection
chooses `alpha` vertices from the larger clique, `beta` from the smaller clique, and `gamma`
one-sided compensators, then equality of the larger- and smaller-clique degrees gives
`alpha=beta+gamma`, while total size gives `beta+gamma=b+t`.  Hence the selected compensators must all
have internal degree `gamma-1`, i.e. they form a clique, and `gamma>=t` because `beta<=b`.  Thus no
regular selection of this compensating type exists unless the half-excess fiber contains a `t`-clique.

Residue balance forces the relevant signed excess: if `a=b+2t`, outside contribution to the smaller
clique must exceed that to the larger by `2t` modulo `q`.  Under a one-sided first-return orientation
with excess below `q`, this is an actual `2t`-vertex compensator fiber.  The remaining two-packet
theorem is therefore a half-excess-clique statement: find a `t`-clique in that compensator fiber, or
route its absence to Section `40` / further packet splitting.

Static data do not force that clique: for `q=8`, `K_6 disjoint_union K_2` can have four independent
one-sided compensators complete to `K_2` and anticomplete to `K_6`, with no compensator `K_2` and no
same-trace `P_3` in the compensator fiber.  Thus the half-excess theorem is also first-return
provenance content.

More generally, for every even `q>=8`, `K_{q-2} disjoint_union K_2` plus an independent set of
`q-4` compensators complete to `K_2` and anticomplete to `K_{q-2}` has exact residue compensation and
no regular induced `q`-set inside that packet subquotient.  A selection with `x` vertices from
`K_{q-2}`, `y` from `K_2`, and `z` compensators would need, in the only nontrivial case, `z=1`,
`x=y+1`, and total `2y+2=q`, impossible because `y<=2` for `q>=8`.  So packet-quotient
regular-selection is not a static theorem.

This is an add/add-orientation obstruction, or an obstruction before the marked quartet is packaged.
In miss/miss, the inserted pair `x,y` is adjacent and complete to the marker, so
`K_{q-2} union {x,y}` is an induced `K_q`.  Thus the miss/miss two-packet atom with a `q-2` clique is
already closed.

Indeed, miss/miss closes any marker clique of size at least `q-2`: add one inserted vertex to a
`q-1` clique or both inserted vertices to a `q-2` clique.  Hence the extremal split packet obstruction
is add/add-oriented unless all marker cliques have size at most `q-3`.

Also, in both same-type orientations the inserted roots are complete to the slack marker, so a marker
clique of size `q-1` is impossible in any residual atom.  The only root-unclosed extremal clique is the
add/add `q-2` clique, where `x,y` are nonadjacent and `K_{q-2} * \overline{K_2}` is not regular.
Thus an exact residual atom with such a clique has remaining marker weight `2`; any missing
half-excess compensator must come from a genuine first-return/provenance packet, not from the inserted
roots.
If an interval-admissible one-defect/provenance row splits this `q-2` clique, it can isolate only one
slack row, so the split sides have sizes `1` and `q-3`.  A marker-complete transported side is then
sub-`q` and forbidden by low-set congruence; a non-marker-complete failure is a local exit.  The live
case is therefore routing arbitrary ambient breakers to such provenance/marker-complete data.
An arbitrary ambient splitter of the clique is not enough for Section `40.10`: the same-trace closure
requires the distinguisher to be in the same residual fixed fiber.  Thus ambient clique breakers still
need the ambient-to-provenance/fixed-fiber routing theorem.
With the exact-marker internal-splitter reduction, the surviving form is sharper.  Some row of
`T\R` splits the marker; if any state-internal/provenance row cuts the `q-2` clique, fixed-fiber
same-trace closure or marker-complete sub-`q` congruence closes.  Hence in a residual atom the
`q-2` clique is constant to every state-internal/provenance row, while the required internal splitter
can only distinguish the remaining two marker rows.  The live theorem is ambient-only clique-module
routing: such a first-return-closure module is either an ambient prime-shell module or every ambient
breaker routes into a fixed fiber, marker-complete submarker, or local exit.
Moreover any live ambient breaker has `epsilon>=2` relative to the peeled package.  If `epsilon=0` it
is a completer, and if `epsilon=1` it isolates at most one low clique row, which is the already closed
admissible one-defect split/local-exit case.
The internal marker graph is forced too.  Let `A` be the `q-2` clique and `U=R\A`.  A row
`u in U` cannot be complete to `A`, since then `A union {u,x}` is `K_q`; it cannot be mixed on `A`,
since then `u` and two adjacent vertices of `A` give the same-trace internal `P_3`.  Hence `U` is
anticomplete to `A`, and the marker is `K_{q-2} disjoint_union H` with `H in {K_2,2K_1}`.  All
compensation for the residual two rows is therefore outside/provenance compensation.
For `H=2K_1`, a regular selection using `alpha` clique vertices, `beta` residual rows, and `gamma`
one-sided compensators satisfies `alpha-1=gamma` and requires the selected compensators to be
`(gamma-beta)`-regular.  The total-size equation gives `2 gamma+beta+1=q`; since `q` is even,
`beta=1`, `gamma=q/2-1`, and the selected compensators must be a clique of size `q/2-1`.  Thus the
independent-pair branch closes when such a clique exists; the independent-compensator model is the
static obstruction because it has none.
For `q=4`, the exact endpoint is closed: `H=K_2` gives marker `2K_2`, while `H=2K_1` closes by taking
all of `A`, one row of `U`, and the single compensator complete to `U`.  Hence live cross-split
endpoints have `q>=6`.
In the `H=K_2` branch, `q=6` also closes: choose three vertices from `K_4`, both residual adjacent
rows, and one compensator complete to the residual pair; this is `2`-regular on six vertices.  Thus
`H=K_2` is live only for `q>=8`, while `H=2K_1` may start at `q=6`.
The two live arithmetic branches are therefore `H=K_2,q>=8`, where the missing finite object is a
`(q-4)/2` compensator clique, and `H=2K_1,q>=6`, where the missing finite object is a `q/2-1`
compensator clique.  Both have the same structural blocker: provenance compensators are constant on
`A`, while ambient primeness supplies only high-error breakers of `A`.
Let `k(H)` denote these clique sizes.  If the one-sided compensator fiber complete to `U` contains a
same-trace `P_3`, fixed-fiber Section `40.10` closes after packaging; if it is `P_3`-free, it is a
union of cliques.  The `U`-using finite obstruction is that every clique has size `<k(H)`.
There is also a divisor bypass avoiding `U`: if some proper `h|q` has at least `q/h-1` compensator
components of size at least `h`, then `h` vertices from `A` and from each of those components give a
disjoint union of `q/h` copies of `K_h`.  Hence a residual atom must also have fewer than `q/h-1` such
components for every proper divisor `h`.  After these explicit finite selections are removed, the
only remaining issue is routing/packaging the compensator fiber together with the ambient breaker of
`A`.
This is exhaustive for the split quotient: a regular selection using `U` forces one compensator
component of size `k(H)` (or, in the adjacent-pair one-`U` variant, a larger component containing such a
clique), while a regular selection avoiding `U` forces equal-size clique pieces and is exactly the
proper-divisor bypass.
The possible multi-component `U`-using escape is impossible: if a selection meets `A`, `U`, and
compensator components of sizes `gamma_i`, equality between `A` and the components forces all
`gamma_i=alpha-beta`.  Comparing with the degree on `U` gives `(m-1)gamma=0` for `H=K_2`, and
`(m-1)gamma=beta-1` for `H=2K_1`; the only non-single-component solution is
`H=2K_1`, `beta=2`, `m=2`, `gamma=1`, which has total size `7` and cannot occur in the even-`q`
endpoint.  Thus several compensator components can occur only in the `U`-free equal-size divisor
bypass.
The marked quartet does not supply another live selection: in add/add, `d,e` each have selected degree
at most one unless outside compensators are used, forcing at most two clique vertices from `A`; for
`q>=6` this cannot reach size `q` inside the marker/quartet frame.
In that `P_3`-free/no-`k(H)` case the compensator fiber has at least three clique components: its
total excess is `2k(H)` for `H=K_2` and `2k(H)-1` for `H=2K_1`, while two cliques smaller than `k(H)`
have total at most `2k(H)-2`.
Each such component is itself a first-return/provenance module unless a fixed-fiber breaker or
marker-complete subpacket split closes it.  Ambient primeness can break the component only by another
high-error ambient row, so the no-`k(H)` compensator case is the same ambient-only routing problem.
Before the product-firewall transport argument, the final routing theorem was not formal: one may add
a high-error ambient row `z` splitting `A` while keeping every first-return/provenance compensator
constant on `A`.  Then `A` is not an ambient module but remains a module for the provenance closure.
This dependency witness is not a claimed global counterexample; it marks exactly the ambient-only
routing input supplied by the transport closure below.
Equivalently, the exact endpoint is a cross-split: the required state-internal/provenance splitter can
only split the residual pair `U`, while ambient primeness supplies a high-error splitter of `A`.  If
the two cuts share one first-return square, marker-complete sub-`q` descent or Section `40` closes; if
not, this is precisely pair-chamber hidden-choice separation in packet form.
In a residual atom this is a product firewall: provenance rows are constant on the large clique and
unrefined compensator components, while ambient breakers of those packets have `epsilon>=2` and do not
belong to the one-defect/completer family.  All static selections, same-trace component splits, and
sub-`q` raw relations have already been exhausted, so the remaining assertion is purely
order-sensitive: first-return geometry must force the ambient packet breaker and the provenance
residual-pair cut into one square/fixed frame.
Equivalently, the remaining theorem is first-boundary completeness.  Use a minimal high-error ambient
breaker as a proposed repair-boundary row.  Passing all interval tests makes it a provenance row; a
first failure at an old defect, inserted-root test, or filler row is local.  A first failure inside the
split packet must therefore be the complete wall-failure side of a transported singleton square, not
just a chosen failed row.  If that completeness holds, the side is marker-complete and sub-`q`, so the
low-set congruence or Section `40` closes.  This is the packet-level form of q-marker
provenance/support-decrease.
Coalesced or fixed-trace first failures are already Section `40.7`--`40.10`, and clean marked support
is already in the marked-add catalogue.  Hence the remaining first-boundary case is dirty and
packet-internal: the failed side has to be upgraded from a set of dirty interval failures to the whole
shared-slack marker of a transported two-class quartet.
For clique-coherent packets this upgrade is formal once the ambient breaker is already an ordered
boundary row.  All rows of the split packet have identical trace to the marked frame and to all other
packets; the boundary test can distinguish them only by adjacency to the breaker `z`.  Therefore the
packet-internal failure set is constant on `P cap N(z)` and on `P\N(z)`, hence is a whole side (or all
of `P`), not an arbitrary subset.  A whole side is marker-complete and proper, so congruence/minimality
closes it.  Thus the true remaining issue is row-to-boundary transport: promote the ambient high-error
packet breaker to such an ordered boundary row, or exit locally.
In the product-firewall endpoint this transport gap also closes.  If a minimal ambient packet breaker
fails to transport and is not local, the square-breaker routing reduction leaves a dirty budget-one
shared-slack square whose first nonconstant coordinate is the packet coordinate split by the breaker.
The new shared-slack set is therefore contained in a breaker side of a proper packet: either the
`q-2` clique or a compensator component of size `<k(H)<q`.  This gives a nonempty sub-`q` marker,
contradicting the low-set congruence.  Hence every high-error ambient packet breaker routes to the
ordered boundary family or to an already closed exit.
The `U`-cut is balanced: the two residual rows have equal internal degree and marked trace, so
opposite provenance incidences on `U={u_0,u_1}` have equal mass modulo `q` after constant rows are
discarded.  A one-sided residual-pair splitter therefore requires opposite splitter mass or becomes the
`host-opppair123` anti-Horn/no-split failure.  The ambient clique breaker is the other coordinate of
the same pair-chamber atom.
If opposite `U`-splitters of total mass `<q` are packaged in one peeled raw space, their discrepancies
are `e_{u_0}-e_{u_1}` and `e_{u_1}-e_{u_0}`, so Proposition `40.16` makes them completers.  Thus the
residual-pair side is blocked only by common-package identification.

The quotient of this obstruction is split/disconnected: three packet vertices `A,B,C` with only
`BC`.  Hence the missing first-return input can be phrased as packet-primality/packaging.  A genuine
first-return atom must either promote the packet quotient to the prime/non-split Section `40.12`
setting, or use its split decomposition to produce a proper complete marker, a half-excess
compensator clique, or a local exit.

This is the packet-level ambient-to-provenance problem.  A nonprime packet quotient has a proper
packet module `M`; an ambient breaker of `M` must be routed to a first-return/provenance row refining
the packet partition or to a local exit.  Otherwise `M` is a genuine prime-shell module.  Primeness
alone gives only an arbitrary breaker, not the required first-return one.
Thus the cross-split endpoint is downstream of the same fixed-package/common-shadow theorem as the
host atoms.  If the ambient breaker of `A`, the provenance `U`-splitter, and the compensator component
are transported into one peeled package, every packaged `A`/component split is a nonempty proper
marker-complete sub-`q` wall and closes by congruence or a Section-`40`/marked-add/completer exit;
opposite packaged `U`-splitters close by `40.16`.  A survivor is therefore exactly a common-package
failure, i.e. the one-corner fixed-shadow / successor-side `0001` obstruction isolated below.
For that fixed-package theorem the only unfixed coordinates are binary pair-status coordinates on the
forced median fiber: unary chambers, the missing-corner set `I_rho`, and the low/high cardinality
residue are already fixed.  Thus fixed package is equivalent to binary pair-status constancy; failure
of constancy is exactly the first-return successor-side `0001` square after shortest-edge and
closest-return reductions.
The apparent single-witness `0001` failure immediately promotes to a full shared-slack set
`R`: the positive coordinate chooses one row of `R`, but the double singleton corner fails along all
rows spending the same one-unit slack.  The low-set update forces `|R|≡0 mod q`, so literal singleton
failure is impossible; any survivor is a q-marker carrier/marker coupling problem.

The obstruction is not only a `q=4` accident.  For every even `q`, let
`R={a_i,b_i : 1<=i<=q/2}` with active binary blocks `{a_i,b_i}`, let `d,e` miss all of `R` and
`x,y` see all of `R`, and add outside rows `z_s` indexed by sign vectors
`s in {0,1}^{q/2}` with `z_s~a_i` iff `s_i=1` and `z_s~b_i` iff `s_i=0`.  Each `z_s` is fully skew on
every active block, but the family separates all vertices of `R`; hence module/primeness pressure
does not force a preserved side.  The marker has exactly size `q`, so the low-set congruence is
silent.  This axiomatic table satisfies all currently recorded local constraints.

Therefore the current proof package has a formal no-go boundary: low-set congruence, marker
minimality, prime-shell module pressure, and active-carrier binary collapse do not imply q-marker
localization.  Any successful proof must bring in data from outside that package.

Static near-regular degree residues are also insufficient.  For even `q>=4`, take
`L=R union {d,e}` with `|R|=q`, make `R` a perfect matching, add the edge `de`, and put no edges from
`R` to `{d,e}`.  Every low vertex then has degree `1`.  With `delta=2`,
`1=delta-1 [MOD q]` and `|L|=q+2 congruent delta [MOD q]`.  Adding a disjoint cycle on
`q^2-q-3` high vertices gives a `q^2-1` vertex anchored near-regular state whose high vertices have
degree `2=delta [MOD q]`.  The one-defect repairs `x,y` have neighborhoods `L\{d}` and `L\{e}`, and
the fully skew sign-vector splitters may be attached to `R` and kept away from the high filler.  Hence
the size-`q` marker table is compatible with the exact static low/high residue equations; any
degree-coupling proof must use first-return or admissibility history, not just degrees.

This is only a residue-level audit model, not a claimed survivor of the full Section-`40` catalogue.
Its role is to rule out a purely static low/high congruence proof of q-marker localization.

The same model rules out an unqualified admissible-splitter theorem.  A sign-vector splitter sees
exactly one endpoint of each active pair, but relative to `L=R union {d,e}` it misses `q/2+2` low
vertices and sees no high vertices, so `epsilon(z_s)=q/2+2`.  It is not a completer and not a
one-defect reanchor.  Hence admissibility can only be forced for splitters with first-failed-row /
transverse-breaker provenance, not for arbitrary fully skew outside rows.

The seed-packaging shortcut is blocked for the same reason.  A single `r in R` gives the expected
house / `P_5` / `C_5` seed with `{d,e,x,y}`, but the whole marker is a bag of size `q`, outside the
prime weighted-quotient hypotheses where all bags have size `<q` and zero as a modulo-`q` weight.
Splitting it into smaller seed bags is exactly the forbidden submarker problem.  Hence Section
`40.11`--`40.12` do not close the q-marker family without the missing first-return/admissibility
coupling.

The second attack sharpens the two gaps.  On the host side, minimal trace-saturated carriers reduce
the failed-row problem first to the crossing-carrier case and then to a binary crossing endpoint:
a minimal connected crossing carrier has only two vertices; at that historical stage it was not yet
proved that the
resulting alternating failed-row ladder is admissible or localizes to the Section-`40` shifted-twin /
stable-house descent.  On the dyadic side, minimal primitive support reduces the weighted problem to a
two-child carry case, where neither child is bad alone but their normalized sum is bad; this now needs
a carry-to-host localization onto the same binary endpoint.  These are the current irreducible audit
blockers.

The binary endpoint has also been tested against Section `40`.  Section `40.8` closes the case once
two successive dirty rows coalesce into one residual fixed fiber, because the shifted twin-breaker
then collapses to the impossible `O_10` configuration.  The remaining host blocker is exactly the
dirty **binary trace-coalescence** lemma: exclude a skew binary ladder in which successive separating
failed rows never share a residual fixed fiber after the allowed marking.

This is not a separate problem from the earlier common-shadow endpoint.  Binary trace-coalescence,
two-off-root common-shadow synchronization, and adjacent shared-slice admissibility for the one-corner
median fiber are equivalent formulations of the same missing fixed-frame existence input.  After the
predecessor/persistence inputs are factored off, the quotient form is the two-fiber single-flip
overlap lemma, equivalently pair-chamber separation of the elementary hidden choice.

The two-child dyadic endpoint has the matching algebraic form: each child is harmless in every
homogeneous child test, but the primitive normalized sum has odd carry.  Thus the bad bit is produced
by addition across the child boundary; it cannot be assigned to either child without a new
carry-to-host localization theorem.

The latest direct attack reduces the binary host blocker to **oriented two-row holonomy**.  A
noncoalesced skew adjacent pair `r -> phi(r)` in the binary endpoint carries only endpoint-unordered
or chamberwise data in the current catalogues: both rows separate `{x,y}`, their marked endpoint
chambers agree, and the dyadic endpoint cocycle is mod-`2`.  All of these are blind to reversing the
elementary step.  Thus the missing input is exactly an ordered sign that is constant on the residual
pair-chamber cylinder, or a localization theorem saying that some turn of every finite skew cycle
enters one Section-`40` residual fixed fiber.  This is the same blocker as pair-chamber separation:
a cylinder-constant ordered sign contradicts reversal by the orientation normal form, while
fixed-fiber localization invokes the closed same-trace / false-clone catalogue.

The holonomy blocker now has a smaller two-case normal form.  If a noncoalesced skew turn reverses
the separator side over the active pair `{x,y}`, the local induced-`P_4` test forces the turn edge to
match the active edge: `rs=xy`.  Thus the irreducible opposite-side turn is exactly the balanced flip
quartet (`2K_2` or `C_4`), equivalently the two-fiber non-overlap row table `{0101,0011}` with no
`0111` row.  If all turns in a finite skew cycle keep the same separator side, the cycle rows are
twins over `{x,y}` and over all endpoint/chamber data; primeness gives an external boundary
distinguisher.  The remaining same-side task is to route the first boundary of such a distinguisher
without losing the active packet, either into Section `40` or into the balanced flip quartet.  This is
the active-packet-preservation gap in its smallest current form.

The balanced flip branch itself is now conditional only on packaging, not on new arithmetic.  If the
two opposite flipped rows are represented in one anchored raw-discrepancy space, their discrepancies
are `e_x-e_y` and `e_y-e_x`, so they form a zero relation of total mass `2<q`.  Weighted raw
short-packet rigidity (`40.16`) would force both rows to be completers, giving the missing `0111`
overlap and excluding `{0101,0011}`.  Therefore the exact missing input for the opposite-side branch
is **common discrepancy packaging**: prove that a fixed-trace pair-chamber cylinder identifies the
same low/high active pair and the same peeled set `T` for both flipped rows.  This is the earlier
fiber-constant pair-status / defect-fiber identification problem in its raw-discrepancy form.

Auditing that packaging shows the precise missing coordinate.  Pair-chamber equality plus the
one-square silent-component characterization fixes all unary witness incidences, so the active
low/high coordinates and the ambient missing-corner set `I_rho` are aligned.  What remains is binary
pair-status constancy on the median fiber: the full raw discrepancy vector also records how the
chosen representatives interact with the other local fibers of the fixed-frame transversal.  Until
that pair-status is constant, the two flipped rows cannot be added in one `40.16` discrepancy space.

Binary pair-status constancy has one smaller square normal form.  If a local fiber/witness `a` has
mixed incidence on the median fiber, the hidden-edge / closest-return / clean-corridor reductions
leave a successor-side first-switch square with pattern `0001`: three corners outside
`E_a={m:m~a}` and the far successor corner inside.  Predecessor-side returns already shorten the bad
edge or fall to strip transfer.  Thus the exact pair-status blocker is successor-side `0001`
exclusion, equivalently the residual candidatewise localized square anti-Horn atom after unary terms
are subtracted.

The same-side holonomy branch reduces to the same square atom.  A boundary distinguisher of a
same-side skew cycle is a pair-status witness whose incidence changes at the first cyclic boundary.
If that boundary coalesces, Section `40` closes it; if not, the same closest-return reduction leaves
the successor-side `0001` square.  Consequently the current host, pair-chamber, and dyadic blockers
all pass through this one local atom.

The `0001` atom is exactly a positive AND square, but not every `0001` row is being excluded.  The
live row is the first-return successor-side square obtained after minimizing a bad hidden edge: the
predecessor rail and earlier far-side vertices are outside `E_a`, and predecessor-side returns have
already been shortened or discharged by strip transfer.  For the pair-status function `p_a` on this
hidden median square, the lower one-coordinate differences vanish while `Delta_H Delta_J p_a=1`.
Unary chamber walls and one-edge predecessor/persistence data cannot see this mixed term.  If either
successor edge coalesces with the witness after the allowed marking, Section `40` closes the square
as a same-trace / false-clone kernel.  The only surviving local atom is therefore the **anchored
first-return fully skew positive AND square**: the first-return `0001` pattern with both successor
edges noncoalesced under every allowed marking.

Equivalently, this is the anchored first-return common-shadow theorem.  The two successor directions
are the off-root transports that must enter one Section-`40` shadow over the forced visible median
point.  Predecessor-side attempts are already removed by closest-return minimality and strip
transfer; the survivor is exactly failure of the two successor transports to share a fixed
frame/shadow.  If such a common shadow exists, the rooted `P_5` seed is in one frame and the
marked-add catalogue closes the clean branch.

The latest sharpening splits this common-shadow failure into a fixed-frame shadow-intersection
problem.  Over the forced visible median point `s_*`, let `M_*` be the corresponding median fiber and
let `Sh_H, Sh_J subseteq M_*` be the fixed Section-`40` shadow sets for the two successor transports.
Then common-shadow is exactly `Sh_H cap Sh_J != emptyset`.  If one of these sets is empty, the
remaining task is the one-corner ambient-to-fixed shared-slice lift.  If both are nonempty but
disjoint, a closest hidden-coordinate path between them has an irreducible first boundary; predecessor
boundaries shorten, and coalesced successor boundaries are Section-`40` kernels.  Therefore the only
separated case is the fully skew successor-side first-return AND square.  The open root is now the
first-return two-shadow theorem: ambient binary-cylinder membership must produce the two fixed
successor shadows, and two nonempty successor shadows over `s_*` cannot be separated by a fully skew
first-return boundary.

Section `40` cannot by itself prove this intersection.  Its raw short-packet rigidity is formulated
for one peeled anchored near-regular set `T`; two successor shadows may live in different spaces
`(Z/qZ)^{T_H}` and `(Z/qZ)^{T_J}`.  Thus the formal missing input is the first-return fixed
peeled-package theorem: the two successor transports over `s_*` must induce the same peeled package
`(T,L(T))`, unless a successor edge coalesces into a Section-`40` kernel.  Once that package equality
is known, the two shadow predicates are the same completer predicate, so the single-shadow lift gives
the common shadow.  This is the Section-`40` coordinate form of binary pair-status constancy.

An endpoint-mass attempt does not close this.  In the terminal square, after persistence, each local
coordinate row is one of `0000,0001,0101,0011,0111`, with mixed second difference `+1` only for
`0001` and `-1` only for `0111`.  A degree-mass identity can at best pair positive `0001` rows with
negative `0111` rows in a common coordinate space.  But using that common coordinate space is already
the missing package identification.  The sharper remaining target is therefore paired-compensator
routing: every first-return `0001` coordinate must either coalesce into Section `40`, or have a
compensating `0111` coordinate whose common successor overlap is routed into the same peeled package.
After all such compensators are routed into common packages, the endpoint-mass cancellation becomes a
legitimate zero mixed-discrepancy relation in one coordinate space.  This still does not by itself
trigger `40.16`: `0001` has unary increments `(0,0)` and mixed coefficient `+1`, whereas `0111` has
unary increments `(1,1)` and mixed coefficient `-1`.  The compensator theorem must therefore include
full residual alignment: the unary increments of the routed `0111` overlap must cancel inside the
same fixed chamber package, or else one of them must yield a predecessor return or a Section-`40`
coalescence.  The current root is the conjunction of mixed compensator routing and successor
unary-leak routing.

The unary-leak half is exactly the single-shadow failure already isolated in the common-shadow split.
If a routed `0111` compensator leaves, say, the `H` unary increment outside the common package, then
on the face `J=0` the ambient binary-cylinder transport exists but no fixed-frame point above the
forced median realizes it.  That is the one-corner ambient-to-fixed lift gap.  Thus full residual
compensation is not a wholly new theorem: it is mixed compensator routing plus the one-corner
ambient-to-fixed lift, with predecessor returns and coalesced edges already discharged.

The one-corner lift itself bottoms out at the single-witness median-square sign law.  A four-point
hidden square with one localized witness seeing only the `11` corner satisfies the lower one-edge
predecessor data and all unary chamber information, but fails fixed-frame shadow membership at the
forced median point.  Hence the missing input is exactly exclusion of the first-return successor-side
`0001` square, equivalently nonpositivity of the localized mixed second difference.  Endpoint mass and
unary chamber data do not imply this sign law.

The fixed-witness Horn/additive interval calculus sharpens, but does not close, this sign law.  With
one candidate/witness fixed, the only fourth-corner failure is double same-sign slack-row saturation:
two elementary repairs both spend the same one-unit slack of one retained row.  Coalesced saturated
successor representatives fall to Section `40`, and clean support falls to the marked-add catalogue.
The dirty survivor is exactly budget-one absorption `Abs(1)`, i.e. a prime-shell cycle-breaker for the
reversible one-defect reanchor graph.  Thus the live root can also be stated as slack-row
trace-coalescence plus dirty `Abs(1)`, or equivalently prime-shell budget-one reanchor no-holonomy.

The compensator route folds into this same root.  Pairing a `0001` row with a `0111` row cancels only
the mixed coefficient; `0111` carries two unary successor increments.  If either unary increment is
not absorbed in the same peeled package, the residual is a one-corner shadow failure.  Marking that
leak gives the same split as above: coalesced goes to Section `40`, clean goes to the marked-add
catalogue, and dirty is the budget-one reanchor edge.  Hence full-residual compensator routing is
mixed pairing plus dirty `Abs(1)`, not an independent bypass.

One subcase of `Abs(1)` is now closed.  In a singleton reanchor walk, if the reverse move and the next
forward move use the same current defect, then the old outside vertex and the new outside vertex have
identical trace over the middle peeled set: in the miss case both miss the current low defect and
match all other low/high incidences, and in the add case both see the current high defect and match all
other incidences.  Primeness supplies a distinguisher unless they are a module; the resulting
same-trace false-clone / shifted twin-breaker is exactly Consequence `40.10`, or the distinguisher is
already a completer.  Therefore pure isolated-token reanchor cycles are closed.  The only surviving
budget-one no-holonomy case is defect-switching: consecutive singleton moves use different defect
sites, so the middle turn is a two-defect square whose missing fourth corner is the fully skew
shared-slack `0001` square.

The long-cycle part of `Abs(1)` also collapses to the same square.  In a shortest reanchor cycle with
same-defect turns removed, take the first inserted vertex that is later deleted.  The interval between
insertion and deletion is a clean corridor.  Just before the deletion, the reverse move for the
previous edge and the forward deletion move have distinct defects.  If their two-defect square filled,
the deletion would commute one step earlier, contradicting first return.  Hence the square is missing;
the Horn interval calculation says that the missing corner is exactly double same-sign slack-row
saturation, i.e. the successor-side first-return `0001` atom.  Thus no independent long reanchor
holonomy remains.

The defect-switching square reduces to a five-vertex template audit.  In the positive
orientation, let `r` be the retained slack row, `d,e` the deleted defect sites, and `x,y` the inserted
one-defect representatives.  Then `r` sees `x,y` and misses `d,e`.  If `tau=0` denotes a miss-type
low defect and `tau=1` an add-type high defect, the trace rules give
`xd=tau_d`, `xe=1-tau_e`, `yd=1-tau_d`, `ye=tau_e`.  The local inserted-root tests, after marked
failures are removed, force `xy=xe=yd`, hence `tau_d=tau_e`; mixed miss/add squares are not live.
For two miss defects, `xy=1`, and according as `de=0` or `de=1` the vertices give an induced `P_4` or
a house with roof `r`.  For two add defects, `xy=0`, and according as `de=0` or `de=1` they give an
induced `P_5` or `C_5`.  These are exactly the Section `40` weighted-house / prime weighted quotient
seed shapes, but the audit point is that Section `40` applies only after the seed is packaged as a
fixed-fiber or prime weighted-quotient attachment satisfying the modular weighted-degree hypotheses.
Thus the remaining theorem is five-vertex seed packaging for this first-return square, not the local
case table itself.

The packaging audit sharpens this one step further.  The five vertices are already in one peeled
combinatorial package: `d,e,r in T`, `x,y in O_1(T)`, and all seed adjacencies are fixed by the
one-defect traces plus the inserted-root tests.  What is not automatic is the modular residue package.
Section `40` applies to prime weighted quotients satisfying one residue equation, while the peeled
state has two residues, `delta` on `B(T)` and `delta-1` on `L(T)`.  The missing correction is exactly
`1_{L(T)}`.  A completer would supply this correction, but assuming one is circular.  Hence
five-vertex seed packaging is equivalent to a local residue-homogenizer theorem: the low-set
correction on the first-return seed and its seed-preserving outside attachments must be internalized
inside the same fixed-fiber / weighted-quotient closure without assuming a global completer.

Final local reduction: the residue-homogenizer obstruction is sharpened by the exact low-set update
for a singleton reanchor.  In the positive shared-slack square, let `R subseteq L(T)` be the nonempty set of
slack rows, each missing the deleted defects `d,e` and seeing the inserted vertices `x,y`.  The mixed
miss/add case is already excluded by inserted-root tests.  In the miss/miss case, after swapping `d`
for `x` one has `L_x={x} union (N_T(d)\setminus {d})`.  Since the double corner may fail only along
`R`, the next vertex `y` must satisfy `N_{T-d+x}(y)=(L_x\{e}) union R`; comparing with its original
trace `{x} union (L\{d,e})` gives `e in N_T(d)` and
`N_T(d)\setminus {d,e}=L\( {d,e} union R )`.  Symmetry gives the same formula for `e`, so `d,e`
have the same marked trace after `R` is included, while `x,y` form the complementary same-trace pair;
the induced quartet is `C_4`.  This is not yet a Section-`40.10` same-trace `P_3`.  In the add/add
case, `L_x=N_T(d)\setminus {d}` and comparison of
`N_{T-d+x}(y)=L_x union {e} union R` with `L union {e}` gives
`N_T(d)\setminus {d}=L\R`, symmetrically for `e`; again `d,e` are a same-trace pair distinguished by
`x,y`, while `x,y` form the complementary same-trace pair; the induced quartet is `2K_2`.  Thus the
defect-switching shared-slack square is reduced to marked two-class localization.  The q-marker
minimality/module argument below closes only the sub-`q`, no-split, and preserved-side branches, not
the fully skew carrier/marker branch.

The low-set congruence gives a sharp size restriction on the marker.  Each singleton reanchor is again
an anchored near-regular state with low-set size congruent to the same residue `delta`.  In both
same-type cases the exact update gives `|L_x|=|L|-|R|`, and symmetrically
`|L_y|=|L|-|R|`.  Since `|L| congruent delta [MOD q]`, any surviving marker has
`|R| congruent 0 [MOD q]`.  Therefore every nonempty marker of size `<q` is impossible; the only
remaining case before localization is a q-marker.

The q-marker case reduces by partial minimality.  Choose an irreducible q-marker obstruction
with `|R|` minimal.  If some outside vertex `z` is nonconstant on `R`, then splitting `R` by adjacency
to `z` and applying the omni-saturated dirty-split theorem either reaches a Section-`40` / marked-add
exit, preserves a smaller active two-class first-return marker `R'`, or returns to the fully skew
positive AND square.  In the preserved-side case the low-set congruence applies to `R'`, so `|R'|` is
again a positive multiple of `q`, contradicting minimality.  In the no-split case every outside vertex
is constant on `R`, so `R` is a proper nontrivial module.  At this stage the fully skew splitter case
was incomplete: the binary crossing reduction controlled the active carrier but not the size or support
of the marker.  The product-firewall transport closure above removes this remaining case.

The weighted dyadic audit is formal only after q-marker carrier/marker coupling.  The argument marks the
whole shared-slack set and is pointwise on a support representative; no step uses coefficient `1`.
Orbit weights merely repeat the same marked two-class kernel.  Hence a weighted two-child primitive
carry localizes to the same host square.  With the product-firewall transport closure, the aggregate
class `beta_m=0` has no remaining host-local obstruction in this reduction chain.

Final audit: the single-witness sign law, one-corner lift, unary-leak routing, full-residual
compensator routing, fixed peeled package, two-shadow/common-shadow theorem, binary pair-status
constancy, common discrepancy packaging, balanced-flip exclusion, oriented holonomy, pair-chamber
hidden-choice separation, binary trace-coalescence, crossing-carrier collapse, weighted dyadic
splitting, and aggregate `beta_m=0` remain downstream of q-marker carrier/marker coupling plus the
already recorded Section `40` closures.  Since q-marker carrier/marker coupling is closed above by the
product-firewall transport trap, these downstream local host and dyadic blockers are discharged in the
tracked dependency chain.

This is the same object as the nonclean shared-slack anti-Horn obstruction.  The witness row is the
retained row with one unit of slack; the two singleton hidden moves are allowed separately, while the
double move spends the same slack twice.  Coalesced successor edges fall to Section `40`, and clean
support `alpha_S=beta_S=0` falls to the marked-add catalogue.  Hence every surviving `0001` square is
the dirty budget-one boundary of anchor-supported unique-defect absorption `Abs(1)`.  The remaining
theorem is a prime no-holonomy / dirty shared-slack absorption statement: singleton reanchors are
involutions, so one needs primeness to produce and route an external boundary distinguisher to a
completer or to a Section-`40` fixed fiber.

The no-holonomy route closes an equivalence loop rather than the proof.  Dirty shared-slack
absorption reduces to the same dirty mixed-trace boundary-row descent as the original failed-row
acyclicity proof.  After fixed-trace, clean-support, and completer-trace exits are removed, the only
missing assertion is dirty split active-pair preservation: one side of the dirty split must still
carry a valid active pair, or else the boundary localizes to Section `40` / the fully skew AND square.
Since the fully skew AND square is the same dirty shared-slack atom, all current host and dyadic
frontiers are equivalent to this one prime-shell mixed two-coordinate preservation theorem.

Update: the dirty split preservation objection is closed in its disjunctive form by using an
omni-saturated carrier.  Choose the active-pair carrier minimal not merely along a failed-row orbit,
but under every outside row whose fiber still contains an active pair.  Then every outside row is
constant on the carrier or separates every active edge.  If a dirty split preserves no side, each
connected active component is bipartite and every outside row is constant on each bipartition side;
any internal same-trace distinguisher is a Section-`40` kernel.  Primeness therefore forces both
sides to be singletons, i.e. the binary crossing endpoint.  Coalesced and clean turns are already
closed, so the only remaining no-side case is the fully skew positive AND square.  Later reductions
close same-defect turns and long cycle holonomy, and reduce that square to q-marker carrier/marker
coupling.  Thus the separate terminal-module / side-selection flaw is repaired, but the endpoint is
closed only by the later product-firewall transport trap.

1. the local prime weighted quotient branch is now closed: the weighted-house endpoint is repaired
   and the `C_5` seed is also eliminated internally;
2. the formal self-bridge target is existential, while the host-side reformulation in
   `remaining-gap-obstruction-module.md` needs a **genuine compatible completion** `S` of size
   `q^2`; bare refinement data do not imply such a completion. The exact finite host-side target is
   now an anchored exact-`e` shell host theorem, while the older `S = s ⊔ C` shell-selection problem
   is only a stronger sufficient route. Equivalently, in the shell graph `H := G[E_e(t)]`, one must
   find a mod-`q` regular `q^2`-vertex induced subgraph containing the anchor `w`; peeling one
   non-anchor vertex gives an exact anchored mod-`q` near-regular completion theorem on `q^2 - 1`
   vertices inside `H`, and for a fixed peeled set `T` raw short packets of size `< q` are already
   exact completer tests; below that, the exact host-side frontier is simply proving completer
   positivity `c(T) > 0`, equivalently a weighted raw relation of total mass `< q`, or equivalently
   an exact `L(T)`-vs-`B(T)` edge-bias witness on some outside subset `U`; more sharply,
   `c(T) = max_{U ⊆ O} Phi(U)`, and because `U` is arbitrary the putative one-error-strip theorem is
   just the pointwise witness `∃ x, epsilon(x) <= 1`. More sharply, one-defect witnesses have a
   defect map `d : O_1 -> T`, and any witness with defect off the anchor swaps into `T`; Hall then
   collapses to the pointwise fiber bounds `mu(u) <= q-1`, so the residual host-side obstruction is
   anchor-supported unique defects together with a multi-swap / compatibility theorem for injective
   anchor transversals. The prime weighted
   quotient branch is not the only remaining case because Theorem
   `17.5` also has a small bad-module alternative; that branch is now best viewed as a
   profile/extremal-profile completion problem, not a theorem quantifying over arbitrary regular
   `A subseteq M`; codimension `4` is already classified, so the next exact smaller theorem is
   overlap-profile resolution for `q in {9,10,11}`.

Moreover, at this audit stage the top-level asymptotic wrappers still required
`HasPolynomialCostEmptyControlDyadicLift`, or at least the weaker one-parameter family isolated by
the dyadic-lift audit: for bridge exponent `D`, it was enough to lift to target size
`(2^(j+1))^(D+1)` rather than prove the full all-`m` lift theorem; Section `18` shows the true
fixed-support core is a residual-packet / `eta`-top-bit theorem, not naive layerwise divisibility,
and the standard Section `18` obstruction shows that packetization choice is irrelevant there: the
exact theorem is `bar eta_m(U) = 0`, equivalently a pairwise next-bit compensation law on one fixed
support `U`; in dual form the smallest exact target is pair-cut packet parity for a basis of
pair-functionals. More sharply, all already-separated control / cascade blocks are silent for those
functionals, so the only contribution unresolved at this stage is the final undecomposed tail, where the exact
object is the terminal-tail class `tau_m(R, U) = [h_m mod 2]`, equivalently one more row-divisibility
step for `rho_R(u) := |N(u) ∩ R|`; equivalently one must kill the normalized carry cocycle
`kappa_m(u,v) = (rho_R(u)-rho_R(v))/2^m [MOD 2]`. More structurally, only complement-pairs of tail
neighborhoods matter, and the exact smaller dyadic theorem is triviality of the aggregate
complement-orbit class `beta_m`, not orbitwise coefficient vanishing. Parity-only pairings still
miss the true carry contribution.
The finite dyadic host-template audit in `dyadic-lift-program.md` removes the first `H_big(8)` and
`H_min(6)` template obstructions.  The surviving aggregation statement is `beta_m=0` for an arbitrary
terminal tail profile: the active complement-orbit family has constant vertex-incidence parity
(symmetric difference `emptyset` or `U`) in the actual tail, not merely vanishing of the first small
localized host templates.  A nonzero cut `beta_m = [1_S]` can always be compressed
set-theoretically to a three-block singleton-cut obstruction by merging full profile orbits on the
two sides of `S`; however, those coarse blocks are generally not homogeneous terminal profile orbits.
Thus the exact dyadic bridge isolated here is a coarsening-stability / many-orbit projection theorem: turn that
coarse singleton cut into a genuine fixed-`D` host instance before invoking the closed
`H_min/H_big` analysis.  More precisely, coarsening first gives a weighted fixed-`D` obstruction:
the coarse block is a union of profile orbits with orbit-size weights and nonhomogeneous lower
profile data.  The closed `H_min/H_big` analysis is unweighted and homogeneous-orbit.  The projection
is supplied by weight-splitting, extracting a genuine bad suborbit.  At this point weight-splitting was not formal from the
determinant algebra: an even/minimal-valuation branch can appear only after two odd or lower-valuation
orbits are merged.  Thus any splitting proof needs extra host localization; otherwise the weighted
closure was the honest target.  The primitive trace-refinement proof below is retained as a candidate
route; the later product-firewall/q-marker closure supplies the host-localization needed to discharge
this target in the tracked note framework.

This weighted gap now matches the host mixed-trace blocker.  If a merged orbit-union block is bad
but none of its genuine suborbits is bad, the first internal profile boundary is fixed for the
current `m`-bit tail but distinguished by lower profile data.  Fixed-trace boundaries fall to the
closed same-trace/cubic templates; the remaining case is a dirty mixed-trace breaker with weights.
Weighted mixed-trace splitting would close dyadic coarsening-stability: split off the first internal
boundary while preserving the bad cut until a homogeneous suborbit obstruction is exposed.

The candidate primitive-carry proof is as follows.  In a minimal weighted orbit-union obstruction, divide the
internal boundary coefficients by their common `2`-adic factor and keep the odd primitive support.
Refining along an odd primitive boundary preserves the bad cut because the aggregate class is
unchanged in `M_2(U)`: `[1_B] = [1_{B_0}] + [1_{B_1}]`.  If no primitive boundary split were
admissible, fixed-trace and clean primitive boundaries would be absorbed by the closed local
catalogues, while every dirty primitive boundary would strictly refine the active profile class.  A
minimal nonsplitting primitive cycle would therefore be a nontrivial module of the prime quotient.
Hence the bad cut splits until a homogeneous suborbit obstruction is exposed, and the closed finite
`H_min/H_big` analysis excludes the endpoint.

Audit correction before the product-firewall closure: the first sentence after refinement was the gap.
The aggregate identity alone does not say that one side still carries the bad determinant/carry cut.
The host audit reduces the unweighted dirty endpoint to first-return five-vertex seed packaging; the
weighted `beta_m=0` endpoint requires the analogous weighted packaging of the same seed, not just the
aggregate split identity.  The product-firewall transport trap supplies that packaging by forcing any
failed transport into a forbidden sub-`q` marker.

On the direct completion side, the packet-compression / supported-seeding route is locally closed by
iterated one-vertex descent and terminal one-sided exclusion.

The three host atoms are conditional on the same trace-refinement package.  The common support-local square
package needs a graph-specific quartic-exchange theorem only before the square-transverse breaker is
introduced; after primeness supplies such a breaker, fixed-trace cases fall to Section `40`, clean
cases fall to the marked-add catalogue, and dirty cases strictly refine the active trace class.
Likewise, the distributed `R_y/R_z/R_x` hexagon and the two-fiber anti-Horn table are exactly the
square-transverse / mixed-trace breaker normal form, so the trace-refinement descent supplies the
required gluing / common-frame synchronization.

The quartic-exchange obstruction has one smaller normal form.  For a fixed candidate/witness, the
one-defect swap equations are additive and every affected degree is constrained to a two-point
interval `{0,1}` or `{-1,0}` relative to a compatible lower face.  Hence binary compatibility already
forbids two same-sign elementary changes, and rooted-ternary compatibility forbids the inserted-vertex
analogues.  A full-support quartic blocker therefore cannot be candidate-fixed.  Any surviving
quartic blocker must be a candidate-switching Helly failure: the proper faces have witnesses, but not
one common witness that certifies the full statewise square.  Equivalently, the blocker is a
fixed-point-free witness transport around the upper hexagon of the failed cube.  If adjacent-face
transports are monotone gates in one finite chamber order, finite-lattice fixed-point/Helly gives a
common witness and the single-candidate interval lemma fills the fourth corner.  Thus the new exact
local target is common-order / gate-compatibility for upper-face witness transport.  The abstract
Helly part is already formal: three pairwise-intersecting gated convex subsets of a finite median
chamber graph have a common point, since the median of points in the three pairwise intersections
lies in all three sets.  What remains is to prove that the actual localized witness packets are such
gated convex subsets and that adjacent-face transport is their gate map.  This cannot be imported
from one-square silent-edge exclusion, because that exclusion is downstream of the fourth-corner
lemma in the current host package.  The non-circular local primitive is the direct
transverse-square gate theorem: in a localized upper face, every nearest-point move toward a common
edge preserves the packet, equivalently `x,y,y^- in Ω_i` forces `x^- in Ω_i` on each transverse
square.  For a fixed candidate on such a `2×2` square, the exact failure certificate is a double
same-sign row saturation: the two elementary switch contributions to one affected degree row are
both `+1` in an interval `{0,1}`, or both `-1` in an interval `{-1,0}`.  Excluding that saturation is
precisely the mixed anti-Horn content; one-coordinate predecessor data do not exclude it.  In graph
terms this is the no-shared-slack-row theorem: two independent repair fibers must not be able to
spend the same retained row's unique one-unit slack in the same direction.  The closed same-trace
`P_3` theorem kills this obstruction once the two saturated repair vertices coalesce to one residual
trace class after localizing at the slack row.  Thus the remaining local anti-Horn input can be
phrased as slack-row trace-coalescence plus the already closed same-trace internal-distinguisher
theorem.  This coalescence is already available in the clean terminal support case
`alpha_S = beta_S = 0`: the marked-add catalogue says that when both marked add-defects pass the
local `deg_(D_R)` / root-edge test, the `P_3` branch collapses to `R ≅ K_3`.  Hence no shared-slack
anti-Horn obstruction remains on the clean rooted `2K_3` terminal rung; any survivor is pushed into
the explicit dirty-support/residue catalogue.  Since a shared-slack row contributes one localized
dirty row, that survivor is the budget-one boundary of the pure-side ladder: the remaining theorem is
`Abs(1)`, i.e. anchor-supported unique-defect absorption producing a compatible re-anchor with
positive completer count.  This is not automatic from the singleton swap: in the miss case the
inserted one-defect vertex misses the deleted low defect, and in the add case it sees the deleted
high defect, so the deleted anchor has the wrong edge sign to return immediately as a completer.
Budget-one absorption therefore needs a reciprocal outside candidate or a second shell/reseating
argument.  The reciprocal candidate cannot be just an opposite one-defect at the same original
anchor, since the two raw discrepancies would sum to zero with total mass `2<q`, forcing both
vertices to be completers by weighted raw short-packet rigidity.  Thus the exact smaller target is a
one-defect reanchor-walk theorem: iterated reversible singleton reanchors must be acyclic or must
exit at a state with `c(T)>0`.  Since the singleton reanchor graph is undirected under the present
bookkeeping, this requires a canonical oriented reanchor potential or a graph-specific no-holonomy
cycle breaker; it is not a Hall-capacity consequence.  The miss/add sign of the one-defect edge does
not orient the graph, because it is preserved by immediate reversal and is therefore an undirected
edge label.  More exactly, singleton reanchor is an involutive neighborhood-pivot of the low set:
miss-type `x` at low defect `z` sends `L(T)` to `{x} ∪ (N_T(z)\setminus {z})`, while add-type `x`
at high defect `y` sends `L(T)` to `N_T(y)\setminus {y}`.  The old defect then becomes the same
type of one-defect at the inserted vertex.  Thus neither low-set size nor miss/add type is a
monotone potential.  The remaining possible route is short-cycle exclusion / pivot no-holonomy:
non-backtracking cycles should telescope to raw short-packet relations, or else `Abs(1)` remains
open.  This raw no-holonomy statement is false without primeness: a high part that is a disjoint
matching plus an isolated low token and outside isolated vertices lets the low token move around
arbitrary miss-type reanchor cycles while no outside vertex completes the current state.  Therefore
`Abs(1)` needs a prime shell cycle-breaker, not just raw near-regular arithmetic.  In a prime shell,
such a cycle would make the moving token vertices a false-twin class over the frozen high core, so
primeness supplies an external distinguisher.  The sharpened local target is the reanchor
false-twin breaker theorem: every minimal distinguisher either becomes a completer after one
neighboring pivot or localizes to the already closed same-trace / false-clone templates.  The
localization is not automatic: Section `40` applies after the breaker and token pair lie in one
residual fixed fiber, while a reanchor breaker initially may have mixed trace.  Thus the exact
smaller routing theorem is to reseat any non-completing breaker into a Section `40` fixed fiber, or
else expose a new mixed-trace reanchor-breaker obstruction.

This obstruction is now the same local object as the square-breaker blocker: a mixed-trace breaker
with no Section `40` localization and a dirty marked row.  The common terminal theorem is
mixed-trace breaker admissibility: such a breaker must be admissible as the next reanchor/repair
vertex, or its first dirty failed row must give a strictly smaller mixed-trace breaker.

The unweighted host form would be closed by trace-refinement failed-row acyclicity.  Iterate the first dirty
failed-row map `phi` on a minimal nonadmissible breaker, transporting each nondecreasing step back to
the same frozen frame.  The dirty row is nonconstant on the active same-trace class `C`; otherwise it
would be a fixed-trace Section `40` case or a clean marked-add case.  Replacing `C` by the side of
that incidence bit containing the next active edge strictly decreases the finite trace-refinement
potential.  The missing points are preservation of an active obstruction after passing to the chosen
side and terminal constancy against every outside vertex.  Without those, induction does not yet
prove unweighted mixed-trace admissibility.

Fixed-square opposite-defect rigidity is also not a consequence of the raw short-packet theorem
alone.  That theorem permits multiple completers; it only controls small zero-sum relations.  Two
admissible repaired opposite defects on the same anchored square would be a same-square completer
multiplicity problem, requiring packet/fiber injectivity inside the frozen prefix chamber.

This multiplicity problem has been sharpened to a square-breaker routing package.  Two same-square
repaired defects are twins over the frozen square frame, so primeness supplies a breaker.  If the
breaker localizes to one residual fixed trace, Section `40` closes it by the same same-trace /
false-clone descent.  Therefore the only possible breaker is square-transverse: its first changing
coordinate is the repaired square coordinate itself.  The remaining theorem is to route every such
transverse breaker either to a Section `40` fixed fiber, to a local completer, or to the first wall
change of an outgoing repair path.  In the last case repair-fiber cubicality plus support-local
fourth-corner filling would eliminate the duplicate defect.

The outgoing `Q^+` square-representation assumption is a cubicality theorem.  A shortest path in the
outgoing repair fiber exposes the first witness-incidence change as three corners of a statewise
square after the same square-transverse breaker routing is applied; otherwise the non-cubical edge is
itself a square-transverse breaker.

The non-cubical case has the same normal form.  On a shortest path between a `λ`-positive and
`λ`-negative outgoing defect, the first `λ`-changing edge is an exposed boundary edge of the
`λ`-cut.  If no statewise square contains it, the endpoints are modular in the fixed repair chamber
unless some ambient-shell vertex distinguishes them.  Any such distinguisher with fixed residual
trace is closed by Section `40`; hence the only genuine cubicality blocker is again a
square-transverse breaker at the repaired coordinate.  This folds `Q^+` square representation into
the same square-breaker routing package.

Filled-overlap reconstruction is likewise an injectivity theorem: for fixed trace, the pair of
incident repaired opposite defects on `Q^-` and `Q^+` must determine the common-edge hidden choice.
Edgeless silent graphs only identify the two incident repairs separately; they do not by themselves
make the hidden-choice-to-repair-pair map injective.  This reduces to filled-overlap
pair-injectivity, downstream of same-square completer injectivity and repair-fiber cubicality.

The pair-injectivity blocker also folds into square-breaker routing.  Two hidden choices with the
same incident repairs are twins over the filled-overlap frame.  Primeness gives a breaker; a
fixed-trace breaker is handled by Section `40`, while a non-fixed-trace breaker is square-transverse
on the first incident square where its trace changes.  Thus `host-orient115` needs no fourth
independent local theorem once square-breaker routing is proved.

Square-breaker routing is conditional on unweighted trace-refinement acyclicity.  Fixed-trace failed rows
fall to Section `40`, clean rows fall to the marked-add catalogue, and dirty rows strictly descend by
trace refinement in the prime shell only after failed-row acyclicity is proved.  Hence the three named host atoms remain conditional:
`host-silentedge128`, `host-opppair123`, and `host-orient115`.

After these reductions, the positive-cost successor bridge would follow from the dyadic tail theorem:
bit-by-bit vanishing of `beta_m` makes the dropped-tail residue constant modulo `q`, which forces
regularity of the final `q`-bucket and turns the existing control block into the required exact
witness / external-block datum.

Thus the mathematical proof route is not yet closed at the level tracked in these notes: the host
atoms reduce to trace-refinement failed-row acyclicity, the dyadic lift reduces to weighted
primitive-carry splitting, and the cascade bridge follows only after the resulting dropped-tail residue
constancy is proved.

This note still records the exact finite core that has to be solved.

## External-block bridge audit

The cascade-to-control-block bookkeeping is no longer a separate obstruction in the nonempty-chain
case.  If a fixed-modulus cascade has at least one refinement step

- `s = s_0 ⊇ s_1 ⊇ ... ⊇ s_\ell = u`,

then each dropped layer `D_i := s_i \ s_{i+1}` is disjoint from the terminal bucket and from the
other dropped layers, and the defining cascade residue gives

- `|N(v) ∩ D_i| ≡ e_i [MOD q]`

for every terminal vertex `v ∈ u`.  Thus the list of dropped layers is already a separated
external-block family on the terminal host.

Consequently the missing positive-cost bridge cannot be phrased as "recover the dropped blocks."
They are present whenever the cascade is nonempty.  The genuine missing statement is to force a
nonempty terminal cascade from a large fixed-modulus witness whose representing cascade may be empty.
Equivalently, for a large `q`-modular host one must find a `q`-vertex subhost whose internal degrees
are constant modulo `q`; at terminal size this is exactly a regular `q`-set.  This is the same
successor terminal bridge / refinement-data exact self-bridge, not an independent easier theorem.

Conditional on the dyadic tail theorem, the missing dropped-part residue would be supplied as follows.  In the refinement-data package,
with `R=s\w` and `r(v)=|N(v)∩R|`, the host-degree congruence gives constancy modulo `2^0`.  If
`r(v)=K_m+2^m h_m(v)` is constant modulo `2^m`, then the terminal-tail obstruction
`tau_m=[h_m mod 2]` is the aggregate class `beta_m`; weighted mixed-trace splitting would give
`beta_m=0`, so `r(v)` would be constant modulo `2^(m+1)`.  Iterating through the `j` bits of
`q=2^j` gives `r(v)` constant modulo `q`.  Proposition `3.1` then makes `G[w]` regular, and
Proposition `2.1` turns the existing exact control block `t` into the bounded exact single-control
witness.  Since `t` is nonempty for positive dyadic `q`, this is the required positive-cost
successor external-block bridge once dyadic `beta_m=0` is proved.

The remaining subsections in this audit are retained to show why the bridge is exactly a
dropped-tail residue theorem; any "remaining theorem" language there is superseded only after the
bit-by-bit dyadic tail argument is proved.

The standing live target at that stage was

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

There is also a sharp no-go for any proof that uses only these formal congruence rows. For any
dyadic `q >= 4`, take a cycle on vertices

- `v_1, ..., v_q, x, y`

in that cyclic order, set `w={v_1,...,v_q}`, and set the first dropped tail to be `{x,y}`. Then
`G[w]` is the path `P_q`, so its degrees are `1,2,...,2,1` and are not regular, while every vertex
of the cycle has degree `2`. Thus the host degrees on `s_0=w ∪ {x,y}` are already all congruent
modulo `q`, but the dropped-tail row sums on `w` are `(1,0,...,0,1)`, not constant. If exact size
`q^2` is desired, add any disjoint `2`-regular graph on `q^2-q-2` vertices to the dropped tail; the
same congruence remains true. Finally, a control block `t` of size `q-1` anticomplete to `w` gives
exact control degree `e=0`.

So matrix row-sum constancy is not a formal consequence of host-degree congruence plus exact control
residue. Any successful matrix proof must use additional structure excluding this cycle-tail pattern:
for instance badness/minimality, residue-controlled decomposition of the tail, or the dyadic
bit-by-bit tail coding principle below. This example is not a counterexample to the conjecture; it
only rules out the bare matrix shortcut.

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
So the finite mathematical statement is:

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

The dyadic theorem strengthens the host-step so that the dropped part is itself
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

This was the pre-closure heuristic.  The primitive `beta_m` proof above supplies the graph-theoretic
realization of this bit-by-bit dyadic argument:

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

## 13. Bottom line (updated)

The weighted-attachment route has now supplied the missing finite theorem.

More precisely:

1. split prime weighted quotients are already good for every even `q`;
2. `C_5` is not an independent prime seed;
3. `P_5` reduces to the house / `bar P_5` branch by weighted quotient complementation;
4. the house branch is finished by the attachment analysis in
   `remaining-gap-obstruction-module.md`.

The last local obstruction there was the shifted twin-breaker case in a false-clone fiber, but that
case reproduces the exact stable-house configuration `O_10` after one more forced distinguisher, and
`O_10` is impossible because it forces arbitrarily long half-graph ladders inside one finite fiber.

So the prime weighted quotient branch is locally closed, and the q-marker carrier/marker coupling
issue is supplied above by the product-firewall transport trap.  `O_10` is closed by Section `40`;
dyadic `beta_m=0` follows through the weighted mixed-trace splitting route recorded here, and the
refinement-data bridge uses the dropped-tail residue constancy established in that route.

### First-bit selector audit addendum

The separate parity-to-mod-`4` first-bit audit reduces to the loss-`32` even selector: an even induced
graph should contain a `1/32`-large induced subgraph whose degrees are congruent modulo `4`.  In the
maximal-witness packet form, a congruent witness `W` of residue `r` can be enlarged by an outside packet
`B` exactly when `deg_B` is constant on `W` and `deg_W(b)+deg_B(b)` has the corresponding shifted
constant value on `B`; Olson already supplies the old-frame balancing.

Two zero-target chamber caps are now exact.  If `m=|W|`, then the chamber
`{b:deg_W(b)=r}` has independence number at most `3m`, and the chamber `{b:deg_W(b)=r+1}` has clique
number at most `3m`.  The clique cap uses Olson on
`((1_{bw}-1_{bw0})_{w != w0},1-1_{bw0})`; a zero-sum clique packet has constant old degree `delta` and
`|B|-delta=0 [MOD 4]`, so its internal clique degree `|B|-1` lands at residue `r+delta`.  Thus the
remaining first-bit obstruction is the nonzero affine target-subsum/self-layer problem, not ordinary
old-coordinate zero-sum balancing.

The two zero-target chambers also have a mixed extension rule: an old-zero independent packet in
`{deg_W=r}` and a clique packet in `{deg_W=r+1}` with old degree equal to its size append together if
their cross graph is empty and the clique size is `0 [MOD 4]`, or if their cross graph is complete and
the independent-packet size is `0 [MOD 4]`.
In the exact cross-regular version, writing `c_I` and `c_K` for the two cross-degree residues, the
conditions are `c_I=kappa`, `|K|+c_K=kappa`, and `|I|c_I=|K|c_K [MOD 4]`.
Old-frame counting also gives `r|I|=0` and `m kappa=(r+1)|K|`.
With `kappa=|K|`, odd `r` forces `|I|=0`, and odd `m-r-1` forces `|K|=0`.
Equivalently, `( |I|-|K| )kappa=-|K|^2 [MOD 4]`.

The corresponding general scalar equation is exact: two internally regular cross-uniform packets
`B_a subset P_a`, `B_b subset P_b`, with internal residues `d_a,d_b`, old increments
`delta_a,delta_b`, and cross value `epsilon`, append iff
`a+d_a+epsilon|B_b|=b+d_b+epsilon|B_a|=r+delta_a+delta_b [MOD 4]`.
For a finite cross-uniform packet family this becomes
`a_j+d_j+sum_{k != j}epsilon_{jk}|B_k|=r+sum_k delta_k [MOD 4]` on every packet.
The exact quotient only needs cross-regular residues `c_{jk}` satisfying
`|B_j|c_{jk}=|B_k|c_{kj}`; equivalently, the row values
`R_j=a_j+d_j+sum_{k != j}c_{jk}` must be constant, and that common value must equal the single
old-increment target `r+sum_k delta_k`.
Summing the row equations gives the global scalar
`S r+(S-m)Delta=2e(B) [MOD 4]`, with `S=sum s_j`, `Delta=sum delta_j`, and
`2e(B)=sum_j s_jd_j+sum_{j != k}s_jc_{jk}`; hence if `m+S` is odd, the enlarged target residue is even.
The old increments satisfy `m delta_j=a_j|B_j| [MOD 4]`, so they are also part of the packet quotient
arithmetic rather than free labels.
The old witness itself satisfies `mr=2e(W) [MOD 4]`; hence odd `m` forces `r` even.
For odd `m` the target becomes `r+m^{-1}sum_j a_j|B_j|`; for `m=0 [MOD 4]`, odd-size packets must be in
chamber `0`; and for `m=2 [MOD 4]`, `a_j|B_j|` must be even and fixes `delta_j` modulo `2`.
Thus for `m=0`, size-`2` packets must lie in even chambers, and for `m=2`, odd-size packets must lie in
even chambers.
The one-packet specialization is `m(a+d-r)=a|B| [MOD 4]` for an internally regular packet in chamber
`a`.
For `m=0 [MOD 4]`, this is just `a|B|=0` arithmetically, while the packet still has to realize the
prescribed old increment `delta=a+d-r`.
For two packets this is just `(s_a-s_b)c_{ab}=s_b((a+d_a)-(b+d_b))` together with the target
`c_{ab}=r+delta_a+delta_b-a-d_a`.
Equivalently, after target substitution:
`(s_a-s_b)(r+delta_a+delta_b-a-d_a)=s_b((a+d_a)-(b+d_b)) [MOD 4]`.
For odd `m`, substituting `delta_a=m^{-1}a s_a` and `delta_b=m^{-1}b s_b` makes this a purely intrinsic
two-packet residue test.
On odd-size packet subsystems the cross parities become symmetric, giving the labelled first-bit quotient
condition `a_j+d_j+deg_Q(j)=constant [MOD 2]`; the full mod-`4` quotient is the carry refinement.
The edge-count symmetry has the corresponding size-stratum table: odd sizes determine opposite residues
up to units; size `0` against odd forces incoming residue `0`; two size-`2` packets synchronize only
modulo `2`; and two size-`0` packets are unrestricted modulo `4`.
Equal odd size residues give symmetric cross residues; opposite odd size residues give sign reversal.
Same-chamber same-external-profile packets may be merged whenever their two cross-degree residues agree.
If they appear in an appendable packet system, their row difference is exactly the difference of those
two residues, so row compatibility forces coalescence.  Thus an appendable primitive packet system uses
at most one packet from each such profile.
For the replacement version, an old-balanced `B subset P_t` has self-error
`eta_B(b)=t+deg_B(b)-r-delta`.  Deleting `D subset W` and writing `lambda=r+delta-R` requires
`deg_D=lambda` on `W\D` and `deg_D(b)=eta_B(b)+lambda` on `B`, with scalar checks
`sum_B(eta_B+lambda)=|D|delta` and `lambda(m-|D|)=|D|r-2e(D) [MOD 4]`.
In fully signed form the additional global scalar is
`(m-|D|-|B|)K=(|B|-|D|)r+2e(D)-2e(B) [MOD 4]`.
If the signed old balance holds on all of `W`, also `mK=|B|t-|D|r [MOD 4]`.
Thus odd `m` determines `K`, `m=2` fixes only its parity after an evenness test, and `m=0` requires
`|B|t=|D|r` with `K` free from old-frame counting.
For odd `m`, this gives the intrinsic signed test
`(m-|D|-|B|)(|B|t-|D|r)=m((|B|-|D|)r+2e(D)-2e(B)) [MOD 4]`.
Thus odd `t` and odd `|B|` force even `|D|`.
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
The odd-word boundary residual also compresses: a minimal affine-inconsistent Arf obstruction has even
kernel exactly `{0,1_U}`.  Therefore `|U|` is even, `1_U in ker(A(Q[U])+diag(tau))`, `dim ker<=2`, and
the irreducible obstruction is the single whole-class bit
`e(Q[U])-(1/2)|{i:tau_i=1}|=1 [MOD 2]`; any other even kernel vector descends to a proper closed support.
For `|U|>2`, equal columns of `A+diag(tau)` are impossible in this core, since they create the forbidden
even kernel vector `e_i+e_j`.
At the exact Davenport boundary top `X=e_1^3...e_r^3`, define
`h_X(sum_i a_i e_i)=sum_i a_i` with `0<=a_i<=3`.  A graph-compatible export `Y` from the retained side
closes whenever `|B|-|Y|+h_X(sigma(Y))>m`; thus terminality forces
`|Y|-h_X(sigma(Y))>=|B|-m` for every compatible export.  The exact-boundary endpoint is therefore a
weighted finite trace problem; in deficit form `d=m-|B|>=0`, compatible exports must obey
`h_X(sigma(Y))-|Y|<=d`.
The height gain satisfies
`h_X(sigma(Y))-|Y|=sum_y(h_X(sigma(y))-1)-4kappa(Y)`.  Hence carry-free compatible exports have total
singleton surplus at most `d`; in particular deficit-zero endpoints force every compatible pair of
positive-surplus vertices to create a coordinate carry or fail the graph-label trace condition.
If `S` is old-balanced and a cut `Y` plus its complement are both graph-compatible exports, then
`4 supp(sigma(Y))<=|S|+2d`.  Hence deficit-zero two-sided-compatible cuts in blocks of size less than
four are impossible, and four-block cuts live on a single coordinate.
A deficit-zero minimal four-block with all singleton and pair cuts two-sided-compatible is therefore only
the positive atom `e_i^4`; the negative atom is killed by singleton height gain, and the remaining
obstruction is self-layer residue.
For this atom, `S_i=e_i^4` together with the boundary triple `X_i=e_i^3` forms a seven-point reservoir.
Every same-size old-coordinate reroot is a four-set `T`; with fixed selected remainder `A`, it must
satisfy `M_A+deg_T=R` on `A` and `L_A+deg_T=R` on `T`.  In omitted-triple form this is the
seven-point table obtained from `deg_T=deg_{R_i}-deg_O`, plus a constant-column condition on `A`.
The latter depends only on the labelled trace alphabet `(p,mu) in {0,1}^7 x Z/4Z`, since an omitted
triple `O` requires `mu-|p cap O|` to be constant on all occupied classes.
Equivalently, the external side is a `35`-template test: `mu(p)=R+|p cap O|` on occupied traces for some
omitted triple `O` and constant `R`.
If empty and singleton traces are occupied, the singleton label differences decode the omitted triple;
with all seven singletons present there is at most one external candidate.
The full/co-singleton layer gives the dual decoder
`1_{r in O}=mu(R_i)-mu(R_i\{r})`.
If two external templates survive, occupied traces have constant signed imbalance across their symmetric
difference; with empty or full trace occupied, they must be balanced across it.
With such an anchor, ambiguity is precisely non-separation of triples by occupied trace intersection
counts.
Adjacent surviving templates force a trace-twin pair; without trace twins, anchored candidates are
Johnson-independent.
Then `C_ext` is a triple packing, so it has size at most seven, with equality only Fano.
For two classes this is the signed equation `|p cap O|-|q cap O|=mu-nu [MOD 4]`; the positive-atom
terminal case is a finite anti-Horn obstruction over the `35` omitted triples.
The pairwise blocker set is `mu-nu notin D_3(|p\q|,|q\p|)`, where
`D_3(a,b)={x-y:0<=x<=a,0<=y<=b,0<=3-x-y<=7-a-b} [MOD 4]`.
Up to swapping/negating, the only non-full `D_3` entries are
`(0,0),(0,1),(0,2),(0,5),(0,6),(0,7),(1,1),(1,6),(2,5),(3,4)`.
The internal kept-pair equation uses the analogous
`E_3(a,b)={x-y:0<=x<=a,0<=y<=b,0<=3-x-y<=5-a-b} [MOD 4]`.
Its only non-full entries are `(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3)`.
The internally impossible kept pairs form a graph that the omitted triple must vertex-cover; cover number
above three kills the positive-atom reroot.
Equivalently, candidate reroots are independent four-sets of this blocker graph, followed by the signed
`E_3` and external `D_3` checks.
Equivalently `C_int` is contained in the 3-cover family of the blocker graph; empty or singleton cover
families kill or decode the internal side.
Terminality of the positive atom is now one of four finite certificates: external empty, internal empty,
decoded mismatch, or genuine ambiguous core.
In the ambiguous core, after trace-twin quotienting, `C_ext` is a triple packing disjoint from
`C_int subset K_3(J_int)`; Fano ambiguity means every Fano line is internally killed.
A fixed kept pair is disjoint from at most two packing triples, so an ambiguous packing `P` needs at
least `ceil(|P|/2)` internal kept-pair witnesses; Fano needs four.
For Fano ambiguity this means the witness graph is not covered by any Fano line; all three-edge witness
graphs are line-covered.
Dualizing to Fano lines, pair witnesses form an edge-cover graph; terminality is no isolated dual line,
and the four-witness case is `P_3 disjoint union 2K_2` in the dual.
Inclusion-minimal Fano cores are dual star forests, ending in the six-witness `K_{1,6}` case, which is
primal `K_4` on the complement of one Fano line.
Away from the exact boundary top, the same inequality uses
`H_X(g)=max{|Z|:Z subset X, sigma(Z)=g}`: terminality forces
`H_X(sigma(Y))-|Y|<=m-|B|` for every compatible export.
In a coordinate subbox, holes delete residue availability rather than giving a uniform `h_box-rho` lower
bound.  On available cuts the exact-top carry and cut bounds persist with the original deficit `d`;
unavailable cuts are label-incompatible.
Two-sided availability allows coefficients `{1,2,3}` at capacity `3`, only `2` at capacity `2`, and none
at capacity at most `1`.
If `d<=1`, a minimal four-block whose singleton and pair cuts are two-sided available is still forced to
be the positive atom `e_i^4` on a full-capacity coordinate.

## 14. Pair-chamber orientation normal form

This is the cleanest direct consequence I can justify from the current pair-chamber formulation.

### Setup

Fix a trace class `τ` on a common-edge packet `P_e^τ`. For a repaired packet-state `η`, write

- `Σ_e(η) := (σ^-(η),σ^+(η))`

for its pair-chamber. Let `h_e(η,η') ∈ {±1}` denote the hidden choice attached to an **oriented**
elementary common-edge hidden step `η -> η'`. Assume the orientation convention is antisymmetric:

- `h_e(η',η) = - h_e(η,η')`.

### Lemma 14.1 (pair-chamber orientation normal form)

Assume there is a sign map

- `ω : im(Σ_e) -> {±1}`

with the following property: whenever `η -> η'` is an oriented elementary common-edge hidden step
whose endpoints lie in one pair-chamber cylinder, i.e.

- `Σ_e(η) = Σ_e(η') =: C`,

one has

- `h_e(η,η') = ω(C)`.

Then no nontrivial elementary common-edge hidden step can lie inside a single pair-chamber cylinder.
Equivalently, the pair-chamber map separates the hidden choice.

### Proof

Suppose toward contradiction that `η -> η'` is a nontrivial elementary common-edge hidden step with
`Σ_e(η) = Σ_e(η') = C`. By the hypothesis on `ω`,

- `h_e(η,η') = ω(C)`.

Reversing the same elementary step gives another oriented elementary hidden step `η' -> η` with the
same pair-chamber value `C`, so again

- `h_e(η',η) = ω(C)`.

But antisymmetry gives

- `h_e(η',η) = - h_e(η,η')`,

hence `ω(C) = -ω(C)`, impossible in `{±1}`. Therefore such a nontrivial elementary step cannot
exist. This is exactly pair-chamber separation of the hidden choice. ∎

### Corollary 14.2 (endpoint chamber data can never be enough by themselves)

No orientation rule built only from chamberwise endpoint data can prove pair-chamber separation. In
particular, any rule obtained from a potential of the form

- `F(η) = f^-(σ^-(η)) + f^+(σ^+(η))`

or, more generally, from any statistic constant on each one-square silent component, is constant on
every fixed pair-chamber cylinder. So such a rule cannot orient the hidden choice on a hypothetical
chamber-flat elementary common-edge hidden step.

### Proof

On a fixed pair-chamber cylinder both chamber coordinates `σ^- , σ^+` are constant. Therefore every
function built only from those coordinates is constant on that cylinder. So it cannot distinguish
the two orientations of the same elementary step. By Lemma 14.1, any successful direct proof must
therefore use genuinely pairwise ordered-step data, not chamberwise endpoint data alone. ∎

### Consequence for the direct frontier

The direct pair-chamber route is therefore already in exact orientation normal form:

1. one does **not** need full packet reconstruction on `P_e^τ`;
2. it is enough to construct, on each pair-chamber cylinder, a sign `ω(C)` that is compatible with
   reversal of elementary hidden steps;
3. but such a sign can never be extracted from one-side chamber labels separately, nor from any
   additive chamber potential;
4. so the theorem has to use genuinely pairwise ordered-step data inside the common-edge packet.

The dyadic `F_2` cocycle package does not by itself supply this law. The dyadic class
`kappa_m = partial beta_m` is an unoriented mod-`2` cut/boundary datum on endpoint vertices; it
forgets the difference between the two orientations of the same elementary step. Pair-chamber
separation instead asks for an ordered-edge sign `h_e(η,η') in {±1}` satisfying
`h_e(η',η)=-h_e(η,η')`, and the required contradiction comes only if this ordered sign is forced to
be a function of the fixed cylinder `C=Σ_e(η)=Σ_e(η')`. Thus an `F_2` endpoint cocycle identifies only
a chamberwise cut obstruction; the trace-refinement square-breaker proof supplies the needed
cylinder-constant ordered-edge input.

Audit update: the last sentence should be read as a conditional route, not as a theorem.  The
trace-refinement / square-breaker package has not yet produced a cylinder-constant ordered-edge sign.
Therefore the pair-chamber hidden-choice blocker is exactly:

> construct ordered common-edge step data whose sign is constant on a fixed pair-chamber cylinder, or
> prove that a chamber-flat elementary common-edge hidden step localizes to the binary
> trace-coalescence endpoint.

Endpoint chamber data, dyadic endpoint cocycles, and one-side silent-component labels are all
insufficient by themselves because they are unoriented or constant on the cylinder.
