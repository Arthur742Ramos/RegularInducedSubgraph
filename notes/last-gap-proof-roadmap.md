# Last-Gap Proof Roadmap

This note now records the proof plan and the latest correction to the last-gap endpoint.

## Re-audit correction

The later tracked q-marker proof does not close the endpoint.  The one-defect / dirty shared-slack branch is
reduced by the exact singleton low-set update: after marking the whole shared-slack set, any
first-return defect-switching square becomes a marked two-class quartet.  The deleted defects and
inserted vertices form two same-trace pairs whose traces differ exactly on the marker, inducing `C_4`
or `2K_2`.  The low-set congruence forces the marker to have size `0 [MOD q]`; the no-split case makes
the marker a proper module in the prime shell, and a preserved-side splitter contradicts marker
minimality.  The fully skew splitter branch only collapses the active carrier to a binary crossing
component; it does not bound the number of retained slack rows in the marker.  The remaining theorem
is q-marker carrier/marker coupling.  The latest audit further shows that static anchored
near-regular degree residues cannot be the missing coupling: a size-`q` fully skew marker can satisfy
the `q^2-1` low/high residue equations.  Thus the remaining input must be history-sensitive:
admissibility for a splitter with first-failed-row / transverse-breaker provenance, or first-return
side-marker structure.  In the admissibility branch, primeness must also be strengthened to
**provenance selection**: the splitter of the marker must come from the failed-row / transverse-breaker
family, not merely be an arbitrary outside distinguisher.  Consequently the dyadic `beta_m=0` handoff
and the global conjecture remain conditional.

Equivalently, the endpoint is the **q-marker provenance/support-decrease theorem**: in the fully skew
first-return q-marker case, either a provenance splitter is interval-admissible, or its first failed
row carries a genuine smaller first-return shared-slack marker.
This includes row-to-breaker transport: the failed interval row must become a valid first-return
breaker/candidate before the smaller-marker congruence can be invoked.
It also includes the ordered first-return choice of that failed row; static interval failure can occur
on many rows at once and gives no canonical descent.
The support decrease must moreover be marker-complete: the smaller support has to be the entire
shared-slack marker of a new marked two-class quartet, not just a smaller failed prefix.
It must also be marker-internal; first failures at old defects, inserted-root tests, or filler rows
must exit locally rather than being counted as q-marker descent.
The endpoint therefore splits into provenance selection, local non-marker exit, and marker-complete
descent.
The latest audit sharpens the two size reductions inside this endpoint.  Frozen q-divisible
same-trace markers are closed by the modular-cluster lemma: a same-trace `P_3` is the roof
false-clone Section-`40` template, and a `P_3`-free congruent-degree clique union contains a regular
`q`-set.  Exact high-null splitters with no second splitter are also closed, because their one-excess
normal form either has an isolated-neighbor deletion or forces the same roof false-clone `P_3`.
Consequently only the non-frozen simultaneous-wall zero-sum atom and the exact two-splitter branch
remain.
The provenance-selection piece is a routing theorem, not a primeness corollary: an arbitrary prime
distinguisher of `R` need not lie in the ordered first-return failed-row / transverse-breaker family.
Nor is it supplied by omni-saturation alone, since saturation only minimizes over valid dirty-row /
repair-boundary traces.  The missing bridge is ambient-to-provenance routing from arbitrary marker
splitters to local exits or valid provenance rows.
The local non-marker exit clause is closed conditional on such an ordered row: inserted-root, old
defect, and filler-row first failures are exactly the local marked/root-edge, same-defect
same-trace, or marked-add catalogue exits.
Marker-complete descent is formal for **square-provenance**: once the selected splitter comes with the
ordered first-return square and its whole marker-internal wall-failure set, the low-set update makes
that set the complete smaller shared-slack marker, contradicting minimality.  Thus the remaining open
work is best stated as provenance selection.
At exact marker size `|R|=q` this sharpens further: if `T\R` is constant on `R`, then equal low
degree residues force `G[R]` to be regular, giving a forbidden induced `q`-set.  Hence an irreducible
exact q-marker already has a state-internal splitter in `T\R`; the remaining bridge is routing that
internal splitter to a local exit or to square-provenance.
Static degree balancing does not supply that bridge: a filler row can split `R` only to equalize the
degrees of the marker rows, with no first-return square data.  The final theorem must use the ordered
first-return geometry of that internal splitter.
At this stage exactness itself had not been proved: the low-set update gives only that `|R|` is a positive
multiple of `q`.  For `|R|=m q>q`, constancy of `T\R` on `R` gives internal degree congruence modulo
`q`, not exact regularity.  The remaining endpoint therefore includes a large-marker-to-exact-marker
reduction or a direct regular `q`-set extraction from the larger marker block.
The expected form of that reduction is an ordered-prefix/no-q-jump theorem: as the first-return wall
path accumulates double-spent marker rows, the first complete marker-internal prefix with size
`0 [MOD q]` should have size `q`, unless a single wall introduces a size-at-least-`q` block that
already yields a regular `q`-set or a local exit.
The sharp blocker is a simultaneous wall block: after selecting just enough rows from that block to
make an exact size-`q` prefix, all leftover rows must avoid both Section-`40` same-trace localization
and marker-internal splitting.
The frozen same-trace extraction is now elementary and does not require the downstream
positive-cost external-block bridge.  If a q-divisible marker block has outside contribution constant
on it, its internal degrees are congruent modulo `q`; an induced same-trace `P_3` is Section-`40`
roof false-clone material over the marked quartet, while a `P_3`-free block is a union of cliques with
congruent sizes and contains a regular induced `q`-set by selecting `gcd(s,q)` vertices from each of
`q/gcd(s,q)` cliques.  Thus the remaining
large-marker proof had to use first-return wall order only for the non-frozen simultaneous block; the
later packet/product-firewall reduction and sub-`q` transport trap supply this ordered step for the
tracked endpoint.
In that block, refining the marker by complete outside trace gives a zero-sum atom: each fiber has
nonzero size modulo `q`, the full residue sum is zero, and no proper zero-sum union is known to be a
complete first-return marker.  A zero-residue fiber is frozen and closed; a proper complete zero-sum
union contradicts marker minimality.  The no-q-jump theorem must therefore create such a genuine
complete union, reduce to exact two-splitter routing, or localize.
Formal tie-breaking of a simultaneous wall is also invalid: an arbitrary prefix is not known to be the
complete shared-slack set of any transported first-return square, so low-set congruence cannot be
applied to it.
At exact size, any state-internal splitter is normalized: a low splitter is adjacent to all of
`{d,e,x,y}`, while a high splitter is adjacent to none of them.  Exact routing is therefore the problem
of turning a low universal or high null marker splitter into Section-`40` packaging or a
square-provenance wall.
If a low universal splitter `v` has no second splitter on `S=R union {v}`, then all degrees in
`G[S]` are congruent modulo `q`; with `|S|=q+1` this forces `S` to be regular (the only possible
endpoint mix `0/q` cannot occur).  Hence low-universal exact routing reduces to a two-splitter problem
on `R union {v}`.  The high null case is still separate, because the splitter has the high residue
rather than the marker-row low residue.
With no second splitter, the high null case becomes a one-excess `(q+1)` graph: all marker rows have
degree `a` in `R union {v}`, and `v` has degree `a+1`.  A neighbor of `v` that is isolated inside `R`
can be removed to give a regular `q`-set, so the residual high-null blocker has every neighbor of `v`
supported by an internal marker edge.
The `q=8` table shows this residual blocker is not empty as a bare degree pattern, but the blocker
always contains an induced same-trace `P_3` inside the marker.  Indeed, if the marker graph were
`P_3`-free it would be a union of cliques; the neighbor set `A` of `v` has size `a+1` but its vertices
have internal degree `a-1`, so it would have to be tiled by cliques of size `a`, impossible unless
`a=1`, which is the isolated-neighbor deletion case.  The forced `P_3` is the Section-`40` roof
false-clone template: miss/miss gives the `C_4` `d-e-x-y-d` with marker trace `{x,y}`, and add/add is
the complement.  Thus high-null with no second splitter is closed by Consequence `40.10`; only the
two-splitter exact branch remains.  Equivalently, exact size now means a normalized state-internal
splitter `v` of `R` plus a second vertex `w` splitting `R union {v}`.  The second splitter either
splits `R` again or is constant on `R` and distinguishes only `v`; these two alternatives are the
remaining exact-marker routing problem.
The singleton-lift alternative is local and closed: when `w` is constant on `R`, the marker is a
single roof false-clone bag and `v,w` are the opposite-side `U_1` breaker pair.  Proposition `39.10`
and Proposition `40.3` reseed or return it to the closed house/false-clone catalogue.  Thus exact size
now leaves only the marker-splitting two-splitter branch.
That branch is the nonregular sign-vector zero-sum atom in exact size.  The perfect-matching
sign-vector table is only the incidence-level shadow, since the marker there is already regular; an
irreducible atom must have nonregular internal marker geometry, with outside trace fibers compensating
the residues.  Hence the exact two-splitter branch and the non-frozen simultaneous-wall branch are the
same final first-return/provenance atom at different scales.
After the same-trace closure this atom is clique-coherent: the marker is a union of cliques, and any
provenance splitter cutting one clique is the local roof/twin-breaker gate already handled by
`U_1`/`Sigma_rf`.  The last atom therefore lives on the weighted quotient of internal marker cliques.
Within a complete outside-trace packet those cliques have equal size, so the quotient is a minimal
zero-sum sequence of nonzero packet weights `n_i s_i` modulo `q`.
For every divisor `h` of `q`, it has fewer than `q/h` cliques of size at least `h`; otherwise those
cliques contain a regular induced `q`-set by taking `h` vertices from each.
This arithmetic package is consistent: `q=8` allows `K_5 disjoint_union K_3`, with minimal zero-sum
packet weights `5` and `3`.  Hence the remaining closure cannot be a bare clique-size lemma.
At exact size, minimal zero-sum is automatic because the positive packet weights sum to `q`, so no
proper packet union can have residue zero.
If the sub-`q` packet quotient satisfies the Section-`40.12` prime weighted quotient hypotheses, it is
closed.  The remaining first-return atom can therefore be phrased as the failure, or forced repair, of
that weighted-quotient packaging.
At exact size the needed statement is even smaller: a packet-quotient regular-selection theorem of
total weight `q`, with Section `40.12` only a sufficient promotion.
Equivalently, solve the finite integer quotient system selecting marker-clique slices and
splitter/provenance packet weights of total `q` with one common induced degree.
The basic two-packet compensation lemma is already available: for marker cliques `a>b`, a compensator
clique of size `(a-b)/2` complete exactly to the smaller clique gives a regular `q`-selection.
For selections using both marker cliques and the one-sided compensator side, the condition is
necessary too: degree equality and total size force a clique of at least `(a-b)/2` one-sided
compensators.
The first-return content is to turn the residue excess `a-b` into a one-sided compensator fiber and
find the half-excess clique inside it, or localize the failure.
This is not static: `q=8`, `K_6 disjoint_union K_2` with four independent one-sided compensators has
the right excess but no compensator `K_2`.
The same packet-subquotient construction works for every even `q>=8` using
`K_{q-2} disjoint_union K_2` and `q-4` independent compensators complete only to the `K_2`, with no
regular induced `q`-set inside that packet subquotient.
This is only a live add/add-orientation obstruction; in miss/miss the `K_{q-2}` packet plus the
inserted adjacent pair `x,y` gives `K_q`.
So miss/miss residual atoms have all marker cliques of size at most `q-3`.
In both same-type orientations, a `q-1` marker clique also closes by adding one inserted root, because
the inserted roots are complete to the slack marker.  Thus the root-unclosed extremal clique is the
add/add `q-2` case.
At exact marker size the remaining marker weight is only `2`, so any half-excess compensation must be
a real first-return/provenance packet, not the inserted-root pair.
An admissible one-defect/provenance splitter of that clique is harmless: it isolates at most one slack
row, and any marker-complete side has size `1` or `q-3`, contradicting the sub-`q` marker congruence.
An arbitrary ambient splitter is not enough, since the same-trace closure requires a same residual
fixed fiber; routing the splitter into such a fiber is exactly the remaining theorem.
Together with the exact-marker internal-splitter reduction, this says a residual add/add `q-2` clique
is constant to every state-internal/provenance row; the internal splitter can only split the remaining
two marker rows.  The exact live theorem is ambient-only clique-module routing.
Any live ambient breaker must have `epsilon>=2`; completers and one-defect splitters already exit.
The internal marker is forced to `K_{q-2} disjoint_union H` on the two residual rows: complete
adjacency to the clique gives `K_q` with an inserted root, and mixed adjacency gives a same-trace
`P_3`.
If `H=2K_1`, the branch closes when the compensator fiber contains a clique of size `q/2-1`; the
independent-compensator model is the static obstruction.
For `q=4`, both residual-pair cases give `2K_2`, so the live cross-split endpoint starts at `q>=6`.
For `H=K_2`, `q=6` also closes by a single half-excess compensator, so that branch starts at `q>=8`.
Thus the two live branches are `H=K_2,q>=8` and `H=2K_1,q>=6`, with different compensator-clique
sizes but the same common-package routing of provenance compensators with ambient high-error clique
breakers.
The `U`-using finite endpoint is absence of the required compensator clique `k(H)`; if the
compensator fiber has a same-trace `P_3`, Section `40` closes after fixed-fiber packaging.  A separate
divisor bypass avoiding `U` also closes whenever `q/h-1` compensator components have size at least
`h` for some proper divisor `h|q`.
These alternatives exhaust the static quotient: every regular selection either uses `U` and therefore
contains a `k(H)` compensator clique, or avoids `U` and is exactly the equal-clique-size divisor
bypass.
The exhaustiveness includes the multi-component case: a `U`-using selection that meets several
compensator cliques has equal selected size in each component, and the residual-row degree equation
forces a single component (except for the odd total-size `7` artefact in the independent-pair algebra).
So the only genuine multi-component selection is the `U`-free divisor bypass.
Consequently the cross-split endpoint is not a separate arithmetic root.  Once the ambient `A`-breaker,
the provenance `U`-splitter, and the compensator component are in one peeled package, packaged
`A`/component splits are proper sub-`q` marker walls and opposite `U` defects are a raw zero pair killed
by `40.16`.  The only survivor is the same fixed-package/common-shadow failure as the positive `0001`
host atom.
The fixed-package theorem itself has only one unfixed coordinate family: binary pair-status on the
forced median fiber.  Unary chamber data, the visible missing-corner set, and the low/high cardinality
residue are already fixed, so pair-status constancy is equivalent to common peeled-package equality;
its failure is exactly a successor-side first-return `0001` square.
That `0001` coordinate cannot remain literally single-row: the two successor singleton repairs fail
along a whole shared-slack set `R`, and the low-set update forces `|R|≡0 mod q`.  Thus any surviving
positive coordinate is accompanied by a q-marker; the missing theorem is to couple that coordinate to
a proper first-return submarker or to a fixed-fiber/local exit.
The marked quartet gives no further base-frame selection for live `q>=6`, since selecting `d` or `e`
forces selected degree at most one.
If it is `P_3`-free and has no `k(H)`-clique, the total-excess count forces at least three compensator
clique components.
Each component is then another first-return/provenance module unless fixed-fiber or marker-complete
subpacket routing closes it; ambient component breakers are the same high-error routing problem.
One can restore ambient primeness by a high-error ambient splitter of the large clique while all
provenance rows stay constant on it, so the ambient-only routing theorem is a genuine missing input.
The exact endpoint is therefore a cross-split: provenance cuts only the residual pair, ambient
primeness cuts the large clique, and the missing theorem must force both cuts into one first-return
square/fixed frame.
The residual-pair cut has balanced opposite provenance mass modulo `q`; an unbalanced one-sided cut is
the anti-Horn/no-split failure.
If the opposite `U`-splitters are in one peeled package with total mass `<q`, `40.16` kills them; only
common-package identification remains.
Its quotient is split/disconnected, so the last first-return input is packet-primality/packaging:
prime/non-split goes to `40.12`, and split quotients must expose a proper marker, half-excess clique,
or local exit.
Equivalently, arbitrary ambient breakers of packet modules must route to first-return/provenance
packet refinements; this is the packet-level ambient-to-provenance step.
At the current endpoint this can be stated as a product firewall: provenance data cut the residual
pair and compensator side while staying constant on the large marker packet, and ambient primeness cuts
that large packet only through high-error breakers outside the one-defect/completer family.  Since the
finite split quotient is exhausted, the missing theorem is exactly the ordered routing that forces
these two packet coordinates into one first-return frame.
Equivalently, prove first-boundary completeness for a minimal ambient packet breaker: passing all
interval tests makes it a provenance row, non-marker first failures are local exits, and a packet-
internal first failure must be the complete square-provenance side of the packet split.  This would
turn the product firewall into a sub-`q` marker-complete wall and close it by the recorded congruence /
Section-`40` exits.
Only its dirty packet-internal branch is still live: coalesced/fixed-trace first failures are Section
`40`, and clean marked support is handled by the marked-add catalogue.
For clique-coherent packets, even that branch closes once the ambient breaker has been promoted to an
ordered boundary row: the packet rows differ only by adjacency to the breaker, so the failed wall is a
whole breaker side and is marker-complete.  The remaining transport theorem for high-error ambient
packet breakers is closed in the product-firewall case by the sub-`q` trap below.
In the product-firewall case, transport failure would itself create a dirty shared-slack marker inside
one side of a proper packet (`q-2` clique or `<k(H)` compensator component), contradicting the low-set
congruence.  Thus the ambient-to-provenance routing step is closed for the final split quotient.

## Audit correction

The previous closure claim was too strong.

What remains justified after audit is:

1. the weighted-house route is now locally closed: Proposition `40.7` is repaired, and the
   false-clone shifted twin-breaker reduces back to the same `O_10` endpoint;
2. the prime weighted quotient branch is now locally closed, because the `C_5` seed is also
   eliminated internally from the current notes;
3. the refinement-data exact self-bridge is existential, not same-`w`; however, Section `10` needs a
   genuine compatible size-`q^2` completion `S`, while the formal refinement-data input does not by
   itself furnish such a completion; indeed bare refinement data do not imply it. The exact missing
   finite theorem is an anchored exact-`e` shell host theorem:
   - find `S` with `w ⊆ S ⊆ E_e(t)`, `|S| = q^2`, and all degrees in `G[S]` constant modulo `q`;
   - equivalently, in the shell graph `H := G[E_e(t)]`, find a mod-`q` regular `q^2`-vertex induced
     subgraph containing the anchor `w`;
   - peeling one non-anchor vertex gives an exact anchored mod-`q` near-regular completion theorem on
     `q^2 - 1` vertices inside `H`;
   - more sharply, for a fixed peeled set `T`, raw short packets of size `< q` are exact: a nonempty
     raw zero-packet exists if and only if every vertex in it is already a completer;
   - below that, the exact host-side frontier is simply completer positivity `c(T) > 0`,
     equivalently the existence of a weighted raw relation of total mass `< q`;
   - equivalently again, `c(T) > 0` is exactly the existence of some `U ⊆ O` with
     `e(L(T), U) - e(B(T), U) > (|L(T)| - 1) |U|`;
   - more sharply, if `Phi(U) := e(L(T), U) - e(B(T), U) - (|L(T)| - 1) |U|`, then
     `c(T) = max_{U ⊆ O} Phi(U)`;
   - because `U` is arbitrary, the putative one-error-strip theorem collapses to the **pointwise
     one-error witness** `∃ x in O, epsilon(x) <= 1`;
   - more sharply, one-defect witnesses carry a defect map `d : O_1 -> T`, and any witness with
     `d(x) notin w` swaps into `T` while preserving anchored near-regularity;
   - Hall already collapses pointwise: in the anchor-supported regime `h_T(Y) <= 0` for all
     `Y subseteq w` is equivalent to `mu(u) <= q - 1` on each anchor fiber;
   - on `O_1`, raw discrepancies are diagonal and admit no cross-fiber cancellation; in particular,
     under the anchor-supported fiber bounds no short raw packet can lie entirely in `O_1`;
   - exact injective-swap compatibility is now explicit in terms of the deleted defect set and the
     internal graph on the swap set, and no nonempty injective swap can preserve the same anchor
     once all defects are anchor-supported;
   - more sharply, singleton swaps are always compatible and simply re-anchor, but they are
     reversible and do not yet force positivity;
   - so the exact residual host theorem is now compatible-transversal positivity: find a compatible
     re-anchor `X` with `c(T_X) > 0`;
   - more sharply, for fixed `D` positivity factors through a finite candidate set `C(D)`, and the
     pair case collapses to one edge bit on the transversal plus one candidate bit;
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
      closest-return suffix. So the genuinely minimal direct input now appears to be the
      **successor-side first-switch `0001` square**: let
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
      two-square content can be normalized to the
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
      admissible continuation over `b` is already packet-changing. Hence it is enough to prove the
      **boundary first-packet-change / outgoing-opposite-defect identification lemma**: among
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
      pairwise one-edge atom can be compressed further from earliest-disagreement form to a pure
      one-step extension statement. For a chamber-flat silent edge `(x,y)` and any coordinate `j`,
      pairwise one-edge atom can be compressed still further. For a chamber-flat silent edge
      `(x,y)` with `D(x)|_{<j}=D(y)|_{<j}`, `P(x)|_{≤j}=P(y)|_{≤j}`, and `D_j(x)\ne D_j(y)`, let
      `Q_j(x)` denote the statewise coordinate-`j` elementary fixed-trace incident square attached
      to `x`. Since the present one-square inputs already rigidify the coordinate-`j` repaired
      opposite defect once the square is fixed, the persistence problem reduces further: it is
      enough to prove an **anchored one-corner lift on `Q_j(x)`**. Namely, the shared lower
      repaired-defect prefix and shared packet prefix through `j` should admit a realization on
      the fixed square `Q_j(x)` with coordinate-`j` repaired opposite defect `D_j(y)`. Any such
      realization forces `Q_j(x)` to be compatible with `y`, hence `Q_j(y)=Q_j(x)`. Thus the new
      sharp unresolved one-square object is no longer full anchored square compatibility, but the
      existence of the `y`-corner on the already anchored square `Q_j(x)`. Present
      witness-incidence / silent-component data still do not produce this. Conditional on it,
      one-step repaired-defect extension uniqueness follows, then edge packet separation /
      same-packet silent-edge rigidity as before, and the remaining ternary atom may still be
      written equivalently as prefix-star sign uniqueness: for fixed `y,i` and lower packet prefix
      `π`, all silent edges `y-w` with `P(w)|_{<i}=π` and first label coordinate `i` carry the
      same sign.
      Together
      with pointwise packet-versus-opposite-defect
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
      **fiber-pair cylinder determinacy**, saying the relevant shared slice and admissible binary
      cylinder depend only on the fiber labels. Once that structure is explicit, packet packaging is
      formal by Proposition `40.14`. So conditional on that blow-up data, the real remaining
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
      honestly, that common core itself is already the sum of two still-unproved ingredients:
      the explicit **fiber-constant pair-status / defect-fiber identification** of the one-corner
      model — after which packet packaging is formal — and, on the quotient side, the sharper
      reduction of the quotient side to the smaller pair **common-defect overlap + one-defect
      anti-healing** on each oriented tree edge of `Γ_ρ`: if nonempty defect sets for the two
      single flips must intersect and every common defect persists to the top, then isolated-top
      two-fiber tables are impossible, hence every nonminimal compatible same-status pair has a
      one-bit predecessor. After that, tree-path telescoping yields the degree-congruent
      transversal. Beyond
      that split common core, one can still continue down the packaged host-side line and either prove
      local completer positivity `c(T)>0` directly or, in the irreducible
      `c(T)=0` regime, prove the compatible injective transversal / finite rooted-template /
      rooted pair-template / candidate-wise two-switch / balanced rooted five-switch exclusion /
      pair-density / one-corner ambient-to-fixed lift / load-preserving pair-exchange /
      signed-transfer normal form / two-fiber missing-corner / binary-cylinder `2`-Helly /
      pair-table Horn / fixed-status Gray/ideal /
      one-edge fixed-status predecessor /
      spanning-tree edge-switch / two-fiber-exchange / unit-transfer
      multi-swap theorem, all of which remain genuinely unproved;
    - there is **no third independent closure route** left in the current notes: direct Section `40`
      bootstrapping still requires one localized rooted `|D_R| = 3` instance, the older shell /
      congruence route is only a stronger sufficient formulation of the same scalar `S(T_hex) = 2`,
      the distributed hexagon alone contradicts no existing theorem, and a comparison with the
      terminal rung `T_18` would itself be extra transport input; thus every remaining host-closure
      path factors through the same missing adjacent-slice-admissibility theorem;
   - the older `S = s ⊔ C` shell-selection/congruence problem is only a stronger sufficient route;
4. prime weighted quotient closure alone would still not finish the host-side theorem, because
   Theorem `17.5` also leaves the small bad-module alternative; Section `22`'s old universal target
   "every regular `A ⊆ M` lifts" is false, already for `K_{m,m,m}`. More sharply, branch-`(1)`
   depends on `A` only through its profile `(a, alpha)`; rewriting by codimension `s := q - a`,
   codimension `4` is already fully classified, and the overlap window now sharpens to:
   - `q = 11`: impossible by parity;
   - `q = 9`: only the internal `C_5` profile;
   - `q = 10`: up to complement, only `C_6` and `2 C_3` (equivalently prism / `K_(3,3)` on the
     `alpha = 3` side);
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
      trivial `I_10 / K_10` witnesses, that `4 K_4` branch reduces to one exact smaller supplement
      theorem, equivalently the lone genuinely new regular `10`-set type `2 K_5`;
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
5. the top-level asymptotic route still also needs `HasPolynomialCostEmptyControlDyadicLift`, or at
   least the weaker target family isolated by the dyadic-lift audit:
   - for the bridge exponent `D`, writing `A := D + 1`, it is enough to prove a terminal-exponent
     lift that upgrades a `2^j`-cascade witness of size `(2^j)^C (2^(j+1))^A` to a
     `2^(j+1)`-cascade witness of size `(2^(j+1))^A`;
   - Section `18` shows the fixed-support core is a residual-packet / `eta`-top-bit theorem, not
     naive layerwise divisibility;
   - more sharply, the packet-shadow sum is decomposition-independent and equals `bar eta_m(U)` in
     `M_2(U)`, so the exact theorem is `bar eta_m(U) = 0`;
   - equivalently, the live dyadic theorem is a **pairwise next-bit compensation theorem** on one
     fixed support `U`;
   - in dual/basis form, the exact smaller target is **pair-cut packet parity** for each
     `{u, u_0}`;
   - more sharply, every already-separated block with constant external degree mod `q` on `U` is
     silent for these functionals, so only the final undecomposed tail can contribute;
   - writing `rho_R(u) := |N(u) ∩ R|` for that last tail, the frozen first `m` bits give
     `rho_R = K_m 1_U + 2^m h_m`;
   - thus the exact remaining dyadic theorem is vanishing of the terminal-tail class
     `tau_m(R, U) := [h_m mod 2]`, equivalently one more row-divisibility step
     `rho_R = K_(m+1) 1_U + 2^(m+1) h_(m+1)`;
   - equivalently, the normalized difference cocycle
     `kappa_m(u,v) := (rho_R(u)-rho_R(v))/2^m [MOD 2]` is the coboundary of an aggregate
     complement-orbit class `beta_m`;
   - individual complement-orbit coefficients need not vanish: the exact smaller theorem is
     `beta_m = 0`, equivalently constant incidence parity / symmetric-difference-zero for the active
     complement-orbit family;
   - in fact `beta_m = tau_m(R,U)`; if nonzero, there is a unique cut `S_m` up to complement with
     `kappa_m = delta(S_m)` and a two-level split of `rho_R` modulo `2^(m+1)`;
   - after choosing a basepoint, the active complement-pairs have canonical representatives whose
     symmetric difference is exactly `S_m`;
   - any symmetry of the terminal tail profile preserves `{S_m, U \ S_m}`; profile-primitivity kills
     the bad cut, and profile-transitivity forces `|S_m| = |U| / 2`;
   - more sharply, for the profile-symmetry group `Gamma`, the bad class lies in the fixed space
     `M_2(U)^Gamma`, so the residual dyadic obstruction is exactly a fixed-space / invariant-cut
     problem;
   - if `dim M_2(U)^Gamma = 1`, the obstruction reduces to one explicit cut-template;
   - at the actual last bit `m = j - 1`, balanced cuts are impossible, so transitivity of the
     terminal profile already forces `beta_(j - 1) = 0`;
   - for the full terminal tail-profile group, every bad cut is a union of full profile-orbits;
   - so the residual last-bit obstruction is a nonbalanced union-of-profile-orbits, and in the
     two-orbit case there is only one cut-template left up to complement;
   - more sharply, the first genuinely unresolved last-bit case is three full profile orbits, where
     the bad cut is already a singleton-orbit template up to complement;
   - orbit data alone are now sharp, so any further dyadic closure has to use arithmetic of the
     actual multiplicities `n_A`;
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
     dyadic closure is genuinely host-side template exclusion;
   - equivalently, the dyadic front is now exactly two host-side fixed-`D` positivity theorems:
     `H_min` for the minimal-pair singleton support `D = O_1` (up to swapping `O_1, O_2`) and
     `H_big` for the large-orbit singleton support `D = O_3`;
   - more sharply still, the all-even valuation lemma forces `|O_1|` even and `4 | |O_3|`, so these
     dyadic singleton supports never hit the new `|D| = 5` host frontier; the first genuinely open
     cases are `H_min` at `|O_1| >= 6` and `H_big` at `|O_3| >= 8`;
    - more sharply again, even-size deleted candidates are impossible; the first open outside-candidate
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
    - more sharply now, the entire `H_min(6), m = 2` slice is the rooted two-factor catalogue
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
       lift cannot survive either; this only empties the **finite localized host-template** frontier,
       while the global aggregate `beta_m` theorem still needs q-marker / weighted mixed-trace
       splitting;
    - on the first-bit exact-boundary side, the Davenport top has an exact import height/carry
      inequality; deficit-zero fully compatible four-blocks collapse to the positive atom `e_i^4`;
      the atom is now a seven-point omitted-triple table with external trace candidates `C_ext` and
      internal candidates `C_int subset K_3(J_int)`;
    - after trace-twin quotienting, ambiguous `C_ext` is a triple packing; terminality is
      `C_ext cap C_int = empty`, and a Fano ambiguity requires an internal witness graph not covered
      by any Fano line; for a general packing `P` the internal witness lower bound is
      `|P| - nu(Gamma(P))` from the packing-intersection graph, minimum covers are matching covers plus
      complement-four witnesses, and a six-packing is already Fano minus one line with a three-witness
      minimum core; the leave graph always has even degrees, so five-packings have only six-cycle or
      two-triangle leaves; anchored full-Fano traces are only empty/full, and anchored
      Fano-minus-one-line traces are only the missing line, its complement, empty, and full, so both
      large anchored packings force trace twins and the irreducible anchored quotient has size at most
      five, where witness counts are at least `3,2,2` for sizes `5,4,3`; the six-cycle leave
      five-packing also forces trace twins, and the two-triangle leave does too via the shared-point
      adjacent/opposite equations, so the trace-twin-free anchored quotient has size at most four; at
      size four the only trace-twin-free shape is the `(1,3,3,0)` base-triple/star normal form, while
      the tetrahedral and one-disjoint-pair shapes force twins; its minimum terminal cores are exactly
      the three two-witness patterns `{u_i v_i, v_j v_k}`; sizes three and two are governed directly by
      `Gamma(P)=P_3/K_3` (path, centered `K_3`, triangular `K_3`) or a single adjacent/disjoint pair;
      unanchored ambiguity is handled by relative traces against a reference occupied trace, and full or
      near-Fano relative equations force all traces equal, so no large unanchored packing survives;
      on the terminal co-cut side, singleton same-old-vector imports obey the target-stability inequality
      `|A_{y,z}|+1_{z target}<=|D_{y,z}|+1_{y in T}` and its averaged old-vector-class form;
      with zero anchor shift, singleton swaps correct only `+1/-1` errors and leave the `2`-error layer
      inert, while zero-anchor pair exchanges see `2`-errors through `|deg_Y-deg_Z|=2` and impose the
      pure-`T_2` no-pair-cut rule; summing this over all export pairs in an old-vector fiber gives a
      quadratic common-neighborhood domination inequality, and in an exact basis direction with three
      boundary copies it forces unpaid `T_2` vertices to be almost constant on the matching old fiber by
      boundary-triple majority; equivalently, each unpaid `T_2` vertex marks at most one exceptional
      old-fiber vertex, so the one-corner shadows `Q_g(a)` are disjoint and nonexceptional old pairs match
      a majority boundary pair on each boundary-pattern cell; the resulting silent core must avoid every
      repairable regular four-block, giving `|A_g|<=|T_2|+R(4,4)-1` whenever `{0,3}` lies in the repair
      spectrum; any larger exact-basis fiber therefore has a missing Ramsey extreme, which is equivalent
      to anti-Horn exclusions `deg_D(b_g) != rho-(r-omega(g))+c` for every usable small old deletion `D`;
      in the unit-shift case all nonzero singleton/pair repairs meet a kernel of size at most three, so
      outside that kernel the direction type is invisible to co-regular tests and the residual is exactly
      anchored persistence/no-split versus a chamber-flat silent edge; the complementary `sigma_g=2`
      spectra are capped by the augmented boundary cube/type analysis, and the unit hereditary spectra by
      target-stability plus the endpoint-exclusive mod-`4` layer theorem, leaving the terminal co-cut
      self-layer selector as the live first-bit obstruction; in the unconstrained selector, averaging over
      all export/import pairs gives a biquadratic domination inequality forcing unpaid pure `T_2` vertices
      to be globally almost constant across the selected/discarded cut unless target damage pays; target
      damage itself is `sum_{i!=j}N_B^iN_X^j`, so zero-polarity vertices are one-corner sparse/dense while
      zero-damage target vertices are cut-constant; the charging bound
      `|U|min_U Polar <= |T|max_T Damage+binom(|X|,2)(|B|-1)|T|` controls all linearly mixed `T_2` mass by
      the target layer and leaves a one-corner polarized residual; the exact zero-polarized sparse/dense
      endpoint contributes at most `4m` by the matching/anti-matching congruent-set argument, leaving only
      the intermediate low-polarity band; at scale `L`, that band is `L`-sparse or `L`-dense and has size
      at most `2Lm`, with the rest charged by `binom(L,2)^(-2)` times the target-damage budget; sparse/dense
      target vertices satisfy the same `Lm` bound, so only scale-mixed target profiles can pay for mixed
      `T_2` polarity; the summed-damage estimate isolates the only nonlinear term as the mixed-target core
      `T_mix(L)`, and dyadic bucketing of the four cut factors reduces it to one homogeneous mixed bucket
      where `Damage` and `Polar` have comparable scale; refining by `deg_B,deg_X mod 4` fixes external
      residues and leaves an internal principal-submatrix mod-`4` selector on that cut-homogeneous bucket;
      equivalently, a deletion layer `D` must satisfy `deg_D(v)==deg_H(v)-c mod 4` on every retained
      vertex, i.e. the Gallai parity co-cut equation plus the centered cut-pair carry equation on the same
      support; in pruning form, repeatedly deleting violators must avalanche below scale `m` for every
      residue and initial deletion set, equivalently every induced chamber has all four mod-`4`
      residue-cores of size at most `m`, equivalently four hereditary elimination orders deleting through
      current degrees avoiding each residue; the whole formulation is complement-self-dual with residue
      shift `c -> |S|-1-c`, so terminal buckets are rigid against all large-complement deletion equations;
      at a minimum loss-`32` counterexample one has the critical size `|H|=32m+1` and every vertex deletion
      already contains a stable residue-core of size `m`; pairs of maximum cores satisfy an equal-petal
      overlap exchange system, with one-exchanges restricted to identical-trace or complete/anticomplete
      patterns and forbidden matching-edge extensions;
      selector blocks merge whenever their internal and cross-degree residues satisfy the quotient
      congruence, so terminal buckets are also anti-merge for all cross-regular quotient solutions above
      scale `m`; one-vertex merge shadows force maximum residue-`0` selectors to dominate and give the
      dual non-completion constraints, while two-vertex shadows forbid the uniform missed/complete/
      complementary trace extensions satisfying the corrected pair residue equation;
      Davenport in `(Z/4)^S` around any maximum core gives zero-trace outside packets in large same-degree
      chambers, and criticality gives two disjoint packets in one chamber whose unions are internally
      anti-selector; quotienting by the all-ones trace sharpens these to constant-trace packets with
      threshold `3m-2`, exactly matching the merge equation, and packet parameters satisfy
      `|X|t==mp mod 4` plus the handshaking danger filter `|X|(a+p-t)==0 mod 2`;
      adding packet size as a `Z/4` coordinate gives size-`0 mod 4` constant-trace packets at threshold
      `3m+1`, for which the size congruence is automatic, the edge parity target is even, and
      the cross-count is `mp==0 mod 4`, splitting into
      odd/even/zero `m mod 4` trace branches; minimal packets are zero-sum atoms of size at most `3m+1`,
      greedy extraction covers more than `19m/4` vertices of the largest critical chamber by disjoint
      atoms, and terminality makes every atom and union of disjoint atoms internally anti-selector,
      equivalently atom defect vectors cannot be cancelled by cross-degree correction vectors, with a
      two-atom global parity filter from `2e(X)+e(X,Y)` and `2e(Y)+e(X,Y)` and a two-atom quotient test
      `d_X+c_XY==d_Y+c_YX==a+p_X+p_Y-t` in the cross-regular case; larger cross-uniform atom subfamilies
      reduce to weighted quotient equations, so terminality forces quotient unsolvability or
      cross-irregularity in every large subfamily; equivalently the atom irregularity graph has no
      quotient-solvable independent set of lifted size above `m`; either a large atom is a compact
      terminal chamber of size between `m+1` and `3m+1`, or the small-atom branch has at least five atoms
      and is a finite atom-quotient obstruction with positive weights divisible by `4` and no
      quotient-solvable subfamily of weight above `m`; the total weight `>19m/4` gives two disjoint
      threshold bundles of weights in `(m,2m]`, each blocked by defect variation, cross-irregularity, or
      quotient unsolvability; choosing them minimal makes them tight, and their union is a further
      forbidden threshold object unless the combined quotient is unsolvable or cross-irregular, yielding
      a three-certificate split: defect variation, cross-irregularity, or pure weighted-quotient
      unsolvability; in the pure quotient case, nonzero residual vectors for the two bundles must avoid
      affine cancellation by the cross-bundle correction sums, and every outside atom must avoid the
      corresponding one-atom affine repair profile; outside atom packets satisfy the same incoming-target
      plus shifted self-layer equations at quotient scale, splitting into profile-target avoidance and
      shifted self-layer failure; profile Davenport yields only zero-profile packets unless a
      target-hitting seed is present, so the residual is true affine target avoidance; with a seed,
      zero-profile packets preserve the target and leave a seeded shifted self-layer problem, while
      without one `-R(B)` is absent from the profile subset-sum set; inverse Kneser then supplies a
      period subgroup whose target coset is missing and which contains all but boundedly many outside
      atom profiles; along a dyadic index-two flag this is a first-bit descent, where each level either
      has an odd seed moving the residual target down one subgroup or a parity character separating the
      target from all remaining zero-prefix packets; the stopped form is a character `chi` with
      `chi(P_B(Y))=0` for every lower-zero repair packet but `chi(tau)=1` on the residual target, the
      atom-profile version of the missing successor-bit square; equivalently every lower-profile relation
      has even successor bit, and an odd relation is the missing seed; supporting `chi` on a minimal
      `W subseteq B` gives a minimal binary cut circuit whose proper odd subcuts are seed-realized but
      whose full cut has odd residual and no odd lower-zero packet; dualizing, the lower-zero packet cut
      vectors span the even-parity hyperplane on `W`, so the remaining gap is odd-coset packet
      realization, not binary linear algebra; equivalently the stopped bit is a flat two-sheeted cover of
      the lower-profile packet graph, with the first nontrivial holonomy appearing as a missing-corner
      packet square; odd-coset realization has only signed branch provenance, local odd-square, and
      unbranched sheet-character provenance exits; the signed branch folds into odd local cycle or sheet
      provenance through the fixed-profile exchange graph; large quotient-uniform sheet components reduce
      internally, so the irreducible unbranched case is rank-one boundary-provenance fullness, equivalently
      restart admissibility for zero-residue prefix-local sheet separators; the exchange-saturated boundary
      category closes this and leaves only path-saturation equivalence, whose shortest-loop normal form is
      a chordless rank-one flat loop with no local square exit, no filled-flat chord, no complete proper
      interval, and no repeated lower profile; active-edge normalization reduces that loop to a
      residue-zero two-state sheet transposition, the common endpoint of the three named host frontiers;
      after cancelling common parts its carrier has a first fully-skew distinguishing row, so the endpoint
      is fully-skew row promotion unless the row-action change exposes the local `0001` square; once
      admitted in `FR^sat`, Proposition `9.2` kills the row by the protected side-size contradiction, so
      the only unsaturated gap is path-to-saturated row transport; in prefix-insertion form this is a
      same-carrier skew ladder whose flat commutations preserve all visible data, leaving only hidden
      path memory unless a local missing-corner square appears; equivalently the last path-only theorem is
      memory-free prefix fullness for same-carrier fully-skew rows, which collapses the ladder to
      Proposition `9.2`; any graph-visible difference between transported copies gives a same-trace/twin
      local exit or smaller provenance failure, so a minimal survivor is pure historical memory; quotienting
      graph-intrinsically equal rows is conservative for all selector equations, leaving only historical
      path bookkeeping outside the saturated proof; this bookkeeping comparison is not used for the graph
      theorem, because terminal descent is defined directly in the graph-intrinsic saturated category, so
      the three named host atoms are discharged there;
      around a maximum core `S`, any outside packet with constant trace-sum on `S` and matching shifted
      self-layer extends `S`, so terminality forbids exactly the singleton/pair/ternary extension equations
      corresponding to row promotion, no-split, and one-corner lift;
      the raw first-bit selector has a four-step Gallai normal form: a critical counterexample contains an
      even core `J` of size `>2m`, and the larger internal `0/2 mod 4` degree class is blocked only by a
      nonconstant co-cut degree into the opposite class;
      labeling that class by co-cut degree `b`, any selector `T=R\D` is exactly a labeled deletion core
      satisfying `deg_D(v)=b(v)-lambda`, so the residual is a labeled principal-bucket pruning problem;
      this has a bad-vertex elimination form for each `lambda`, and label-refined twin/module exits force
      `4*2^r>|R|/m` in graph and complement;
      the residual is hereditary with relabeling `b_U=b-deg_{R\U}`, so the one-over-threshold form only
      forces inherited-label nonconstancy and the parent co-cut coupling must still be used;
      on retained `(m+1)`-sets the coloring `psi_T=b-deg_{R\T}` must remain nonconstant under every
      one-swap, with exact update `psi(v)->psi(v)+1_{vy}-1_{vx}`;
      balanced swaps update by `deg_Y-deg_X`, so row-promotion, no-split, and packet repairs are one
      labeled co-cut flattening formula;
      for fixed outgoing `X`, this again splits into incoming affine target avoidance versus shifted
      self-layer failure on the incoming packet;
      for one-swaps this is a missing-template test: if `psi_T-1_{vx}` lies in an adjacent residue pair,
      the required outside trace is forced and no outside vertex may realize it with the scalar condition;
      for two-swaps the target is a `{0,1,2}`-valued partition for an incoming pair plus two shifted
      self-layer scalar equations;
      for `r`-swaps, `Theta_X=kappa-psi_T+deg_X` prescribes bounded old-vertex multiplicities `0..r`,
      followed by shifted self-layer equations on `Y`;
      at `r=3` the target is always arithmetically legal, giving a large-outside ternary branch, while
      absence of three outside vertices squeezes the two Gallai residue classes into
      `m-2<=|C|<=|R|<=m+3`;
      ternary target failure has a coordinate-minimal essential certificate, while nonempty target
      realization is obstructed exactly by scalar-good hypergraph emptiness;
      certificate sizes `1`, `2`, and `3` are row extremity, pair-chamber transportation failure, and
      eight-corner ternary cube failure;
      saturated local closure eliminates those size-`<=3` target certificates in an irreducible branch;
      scalar-killed target triples reduce to internal degree graphicality on three vertices, allowing only
      `000`, `110`, `211`, and `222` and forbidding endpoint residue `3`;
      those four patterns prescribe empty, one-edge, two-edge-path, and triangle internal graphs;
      scalar mismatch is the corresponding extra-edge, missing/wrong-edge, or missing-triangle-edge failure;
      target-avoidance is a critical capacitated 3-sum cube of trace columns, infeasible only in full
      dimension and feasible on every proper coordinate shadow, with irreducible dimension at least `4`;
      coordinate switching normalizes this cube to a `{0,1}` three-column disjoint-cover problem;
      zero coordinates filter admissible columns, and active coordinates require a disjoint three-cover;
      criticality gives active-coordinate hole/collision witnesses and zero-coordinate filter-breach
      witnesses;
      small active dimension `|A|<=3` is a finite zero-filter capacity obstruction, so the genuinely new
      filtered-cover branch has `|A|>=4`;
      finite zero-filter obstructions are governed by the support-count table `c_Z(B)` and disjoint
      three-block covers of `A`;
      equivalently, by a 3-coloring criterion for admissible active supports plus empty-support capacity;
      empty-support capacity determines the allowed number of nonempty admissible blocks;
      the high-active endpoint is a minor-critical support-family obstruction under active deletions and
      zero-filter relaxations;
      equivalently, a partition-spectrum gap relative to empty-support capacity;
      the gap cases are empty spectrum, only useless one-block partitions, or no exact three-block
      partition, according as empty capacity is at least two, one, or zero;
      equivalently, full-support/bipartition/tripartition alternatives are absent according to that
      capacity;
      missing supports form a minor-critical blocker for the allowed partitions;
      a minimal blocker certificate makes every retained missing support essential;
      active deletions and zero-filter relaxations must fill the corresponding spectrum interval;
      in fact every proper active/filter shadow is feasible by inclusion-minimality;
      singleton shadows force `e_Z>=2` and a complete singleton layer in any genuinely high-active
      full-minor endpoint;
      with all singletons present, the endpoint is a full-minor-critical excess-packing failure for
      disjoint non-singleton supports saving at least `|A|-3`;
      large supports of size at least `|A|-2` are excluded, and active-deletion projected near-packings have
      all one-unit lifts blocked; singleton closure only applies to projected partitions with at most two
      blocks, so one-block shadows are impossible and two-block shadows are double-collision only;
      the support graph has independence number at most three, so pair-only endpoints stop at `|A|=7` and
      rank-three projected supports are forced from `|A|>=8`; the pair-only table is triangle at `|A|=5`,
      matching-number-2 deletion-critical at `|A|=6`, and factor-critical at `|A|=7`;
      zero-filter criticality is a private excess bridge across `Delta=|A|-3-mu_Z`;
      in the mixed two-level core, every `(m+1)`-set has a large outside reservoir in `J\T`, so the ternary
      target/scalar packet obstruction applies for `m>=3` even when a pure residue class is near-threshold;
      the `m<=2` bases are closed by the trivial pair selector and the four-color triangle Ramsey bound
      `R_4(3)=51`;
      scalar-killed target triples must shield every discrepant edge/nonedge from all one-/two-vertex
      partial swaps by omitted-trace or retained-scalar failure;
      for fixed `T,X`, the four `kappa` target covers are coherent under the rotation
      `h_k=k+deg_X-psi_T`, with opposite residues swapping active/filter roles and complementing traces;
      in the four `q`-classes, active adjacent pairs rotate as `12,01,30,23` and switch pairs as
      `23,12,01,30`;
      opposite high-active target endpoints on a shared certificate force an antipodal trace core of
      repeated complementary centers plus singleton flips around both centers, with complementary
      restrictions on intersections of different certificates;
      pure high-active target-avoidance for all four residues requires adjacent-pair lower bounds on the
      four `q=deg_X-psi_T` classes and hence `m>=10`; for `m<=9` some residue is scalar-killed or
      small-active zero-filter capacity;
      if all high-active residues avoid rank-three projected supports, then `sum |A_k|=2(m-2)` and
      `|A_k|<=7` give `m<=16`; for `m>=17` a rank-three support is forced;
      for `|A|<=3`, these tables are the explicit empty/singleton/pair/triple support alternatives;
      small-active capacity is equivalently a finite zero-filter blocker with each zero coordinate
      essential through a uniquely breached repair triple;
      relaxing a zero coordinate adds only private columns with zero-trace exactly that coordinate;
      every zero-relaxed cover must use at least one such private column;
      active-coordinate near-covers forbid every one-coordinate lift that toggles the active coordinate
      into exactly one support block;
      equivalently, every allowed partition of `A\{a}` has all block thickenings by `a` forbidden;
      active witness types are one/two/three-block, two/three-block, or exact three-block according to
      empty-support capacity;
      the high-empty-capacity case splits into pure co-singleton core or multi-block forbidden-boundary
      witness;
      the first high-active dimension `|A|=4` has explicit singleton/pair/triple layer restrictions;
      its one-empty-column layer forbids singleton/triple, pair/pair, and pair+two-singleton partitions;
      the one-empty-column layer splits into singleton-core or pair-witness subcases, and the zero-empty
      layer has all missing pairs essential;
      in the co-singleton `|A|=4` core the pair layer is an intersecting `K_4` edge family;
      size-three pair layers are star/triangle templates with complementary pair blockers;
      after full minor-criticality the genuine four-active endpoint is singleton-only;
      the five-active pair-only minimal obstruction is a triangle;
      in the near-threshold branch `|R|=m+s`, `s<=3`, all internal selectors of `R` larger than `m` are
      obtained by deleting at most two vertices, giving finite templates `b-deg_D` on `R\D`;
      the full two-residue Gallai core has the mixed-selector equation `epsilon(v)-deg_D(v)=const` on
      `J\D`, where `epsilon` is `0` on `R` and `2` on `C`;
      if `C` is also above threshold, the mirrored signed label `2-deg_R` obeys the same bounded deletion
      templates on `C`;
      mixed selectors are exactly deletion sets whose degrees into retained `R` and retained `C` are
      constant residues separated by `2`;
      the mixed equation is hereditary with two-level label `epsilon_U=epsilon-deg_{J\U}`;
      constant-label modules for this two-level label are exits, extending selector-prime/rank constraints
      to mixed subbuckets;
      mixed balanced swaps use `omega_T=epsilon-deg_{J\T}` and the same target/self-layer equations;
      row-twin, co-twin, and module exits force any terminal bucket to be selector-prime and high-rank over
      `F_2` in both graph and complement; independent/clique exits force hereditary density and codensity
      at scale `m`;
      Fano itself needs four kept-pair
      witnesses; dualizing to the seven Fano
      lines, those witnesses must form an edge cover, with inclusion-minimal cores exactly the dual
      star forests (`K_{1,2}+2K_2`, the two five-edge star forests, or `K_{1,6}`), each dual star being
      a cluster of bad kept pairs in the complement of its center line;
    - the odd-word boundary residual also has a minimal Arf normal form: after closed-support
      localization, the even kernel of `A(Q[U])+diag(tau)` is exactly `{0,1_U}`, the obstruction is one
      whole-class half-edge bit, and equal twisted columns are impossible for `|U| > 2`;
     - raw parity pairing on `R` is too weak, because it misses the carry contribution hidden inside
       those aggregate complement-orbit coefficients;
   - the Section `18` obstruction shows that current `m`-bit data alone do not force this, and
     low-rank shadow space by itself is not enough.

So the rest of this note should be read as a roadmap / reduction record, not as a completed proof.

The main point is simple:

- the concrete `q = 4` slice is now genuinely settled;
- the **real global frontier** remains the refinement-data exact self-bridge;
- the wrong target is the stripped residue-host upgrade, because that interface is already known to
  be false.

## 1. What the code already reduces the problem to

The current library already has the following finite pipeline.

1. From a bounded host witness at bucket `q * q`, `Cascade.lean` produces the refinement package
   `HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard`.
2. `Finite.lean` already proves the one-way implication
   `hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard`.
3. `Finite.lean` also already proves that drop-data are enough:
   `hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard`.
4. `Asymptotic.lean` packages these implications into the abstract targets
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge`,
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge`, and
   `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

So the honest finite theorem surface is already visible:

> start from the `q * q -> q` refinement output and collapse it directly to an exact single-control
> witness of size `q`.

This is the right target. We do not need more asymptotic repackaging.

## 2. The supporting algebra that matters

Fix `u ⊆ s`, and let `B` denote the separated control-block union. For a vertex `v ∈ u`, write

- `drop(v) := |N(v) ∩ (s \ u)|`,
- `ext(v) := |N(v) ∩ B|`.

Then the degree decompositions are

- `deg_G[s](v) = deg_G[u](v) + drop(v)`,
- `deg_G[u ∪ B](v) = deg_G[u](v) + ext(v)`,
- `deg_G[s ∪ B](v) = deg_G[s](v) + ext(v)`.

This is exactly why the private lemma
`modEq_dropDegree_and_extendedUnionDegree_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees`
goes through:

- host congruence on `G[s]`,
- small-ambient congruence on `G[u ∪ B]`,
- blockwise external congruence into `B`,

together imply

- congruence of `drop(v)` modulo `q`,
- and congruence in the larger ambient graph `G[s ∪ B]`.

The important negative conclusion is that this argument is **one-way**.  
Trying to invert it from the packaged data is the wrong move: the uncontrolled term is still the
contribution of `s \ u`, and nothing in the current stripped data lets us recover it for free.

This is the conceptual reason not to keep attacking the proof by “reconstructing the missing
residue package” after the fact.

## 3. Why the residue-host route is the wrong theorem target

The current evidence already prunes three tempting but false directions.

1. The budget-`1` terminal route is false at `q = 8`.
2. The zero-cost external-block bridge is false already at `q = 2`.
3. The strongest stripped residue-host upgrade is false already at `q = 4`.

The third point is the decisive one for the present gap. The statement to avoid is any theorem that
demands a same-shape residue-host witness as an intermediate object. The local `q - 1` control
structure can still be sufficient to force an exact witness, but it should not be expected to
upgrade to a full residue-host package first.

So the remaining theorem should be phrased directly at the level of

- the exact-card host bucket,
- the maximal control block of size `q - 1`,
- the surrounding refinement data,
- and the final exact single-control witness.

That is why the right frontier remains
`HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge`.

## 4. The settled `q = 4` slice

Dyson-McKay now record `N_4 = 8`, so every graph on at least `8` vertices contains a regular induced
subgraph on `4` vertices. Since the dyadic host size is `q^2 = 16`, the `q = 4` instance of the pure
selection theorem is automatic.

So the split-graph argument below is no longer needed to justify the frontier, but it is still a
useful self-contained internal proof of the same fact.

The cleanest remaining finite theorem is therefore no longer “finish `q = 4`”, but rather “start at
`q = 8` with the corrected global formulation”.

For reference, the old `q = 4` slice was:

- `four_mem_admissibleBounds_seven`,
- `four_le_F_seven`,
- `four_le_F_of_seven_le`,
- `hasBoundedSingleControlExactWitnessOfCard_four_of_sixteen_le_card`,
- `hasBoundedFixedModulusControlBlockModularHostStepExactSelfBridge_four`.

The supporting mathematics is short and robust.

### Human proof of `4 ∈ admissibleBounds 7`

Take any graph `G` on `7` vertices.

If `G` contains any of the following induced subgraphs, we are done immediately:

- an induced `2K₂`, which is `1`-regular on `4` vertices;
- an induced `C₄`, which is `2`-regular on `4` vertices;
- an induced `C₅`, which is `2`-regular on `5` vertices.

Otherwise `G` is `{2K₂, C₄, C₅}`-free. By the Földes-Hammer characterization, `G` is a split graph.
So `V(G)` decomposes as

- a clique `K`,
- and an independent set `I`,

with `|K| + |I| = 7`. One of these two parts has size at least `4`. Therefore `G` has either

- a clique on at least `4` vertices, or
- an independent set on at least `4` vertices.

Either way, `G` contains a regular induced subgraph on at least `4` vertices.

So `4 ∈ admissibleBounds 7`.

### Why this milestone was worth isolating

This one theorem isolates the first nontrivial dyadic bucket:

- every bounded host witness at `(q, q * q) = (4, 16)` collapses to the exact single-control witness
  needed downstream.

It is a real theorem, it uses the current machinery rather than bypassing it, and it does not depend
on any conjectural global bridge.

In other words: this remains a good sanity-check proof, but it is no longer the live frontier.

## 5. The real global gap, stated correctly

After the `q = 4` slice, the actual remaining theorem should be attacked in the following form:

> From the existing `q * q -> q` refinement-data package, produce a bounded exact single-control
> witness of size `q` directly, without first upgrading to a same-shape residue-host witness.

Concretely, the proof should stay as close as possible to the data already produced by
`hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard`.

That package already gives, on a host bucket `w` of exact size `q`,

- an ambient set `s` with `w ⊆ s`,
- a control block `t` with `|t| = q - 1`,
- exact control degree into `t`,
- modular host-degree constancy on `G[s]`,
- modular degree constancy in the small ambient graph,
- and blockwise external residue data.

The global proof should use this data directly.

## 6. The key mathematical reformulation

For a set `u` of size `q`, every induced degree in `G[u]` lies in `{0, 1, ..., q - 1}`. Hence:

> if the induced degrees in `G[u]` are all congruent modulo `q`, then they are actually equal.

So the exact witness problem reduces to a modular one:

> find a size-`q` set on which the induced degrees are constant modulo `q`.

Inside the current refinement package, this means that the real finite selection problem is to
equalize the missing dropped-part term, not to reconstruct a larger witness class.

At the level of formulas, if `u ⊆ s`, then

- `deg_G[u](v) ≡ deg_G[s](v) - drop(v) [MOD q]`.

Since host degrees are already controlled modulo `q`, exact regularity on `u` will follow as soon as
the dropped-part residues are controlled modulo `q` on `u`.

That is the right local goal.

## 7. Roadmap for the actual last-gap proof

### Phase A. Freeze the target at the refinement-data level

Do not aim first at a new asymptotic statement.  
Do not aim first at a new residue-host upgrade.  
State and prove one finite theorem directly over the exact-card refinement package.

The proof object should consume the same data that `Cascade.lean` already produces. This keeps the
critical path short and avoids new wrapper code.

### Phase B. Prove a local selection lemma on the exact host bucket

The right local statement is not “upgrade to a residue-host witness”. It is something morally of the
form:

> from the maximal-control refinement data on a size-`q` host bucket, extract a size-`q` subset on
> which the dropped-part degree is constant modulo `q`, or directly extract exact regularity.

This is weaker than the false residue-host upgrade and is all the downstream exact theorem needs.

Two mathematically faithful routes now stand out for this local step:

1. a completion/discrepancy argument on near-regular `(q - 1)`-sets;
2. a fixed-`u` dyadic lifting argument via the half-obstructions `eta_m(u)`.

By contrast, naive balanced halving should be treated only as a strong sufficient detour, not as the
core formulation of the open problem.

### Phase C. Use maximal control size `q - 1` aggressively

The fact that the control block has exact size `q - 1` is special and should be treated as a proof
tool, not as bookkeeping noise.

Why it matters:

- exact control degree into `t` removes one whole source of fluctuation;
- on a size-`q` bucket, “constant modulo `q`” immediately upgrades to “constant exactly”;
- the only remaining obstruction is the tail `s \ w`, so the proof should isolate and attack that
  term directly.

This is the place where the current false residue route was too ambitious: it tried to package the
tail information into a stronger witness class instead of using it only to prove exact regularity.

### Phase D. Only then push back into the existing exact bridge

Once the local selection lemma is proved, the rest is already in the library:

- convert the resulting refinement statement to the exact single-control witness using the existing
  finite bridge;
- feed that into the positive-dyadic step-exact self-bridge;
- then let the existing asymptotic wrappers carry the rest.

This is why the real mathematical effort belongs in one finite theorem, not in more asymptotic
plumbing.

## 8. What I would not spend time on next

- No more finite brute-force reflection for the global theorem.
- No attempt to invert the existing small-ambient-to-drop implication.
- No effort to revive the stripped residue-host upgrade.
- No new wrapper theorems unless they expose genuinely new finite data.

## 9. Bottom line

The `q = 4` slice is already settled, so the first genuinely new case is `q = 8`.

If the goal is the real final global gap, attack exactly one theorem:

- the refinement-data exact self-bridge at positive dyadic modulus,

and attack it **directly at the exact-card refinement level**, using the maximal `q - 1` control
block and the dropped-part degree as the central local object.

The two routes worth preserving at that finite level are:

1. completion/discrepancy on near-regular `(q - 1)`-sets;
2. fixed-`u` dyadic lifting through the classes `eta_m(u)`.

One further sharpening is now available inside the first route:

- around every near-regular `(q - 1)`-set, the outside discrepancy sequence automatically contains a
  nonempty zero-sum packet by Davenport;
- for proper near-regular targets `1 <= r <= q - 2`, any zero-sum packet of size strictly less than
  `q / 2` already forces a regular induced `q`-set;
- so after separating off the clique and independent-set endpoints, the real missing lemma is a
  **proper missing-pattern / short-packet forcing theorem**, not just a raw zero-sum identity.
- the strongest direct proof target sharpens this further: choose a minimal nonempty zero-packet and
  prove it must have size `< q / 2` (packet compression).
- within that direct route, the only surviving obstruction with `p < q` is the boundary
  `q / 2`-packet of anti-completers, but the isolated boundary anti-packet lemma is too weak:
  the last move must use global minimality across all proper near-regular sets.
- in that boundary case, the remaining layer `W` is itself a large zero-packet forced to compensate
  the anti-completer block by a fixed residue gap between `A` and `B`, but this does not force a
  short zero-subpacket: `(q/2-1)` anti-completers together with `2` empty-trace vertices already
  realize the same compensation.
- so the new direct target is a **supported seeding route**: the empty-trace vertices alone are too
  weak, and one must use them together with a large outside support set to pass to a different
  proper near-regular set `S'`, not to prove an abstract balancing extraction principle on the
  fixed `S`.
- more sharply, any such support must satisfy a **pointwise compensation law** between every
  surviving `a in A'` and `b in B'`, forcing many genuine `A`-over-`B` separator vertices whenever
  the deleted set is not more `B'`-heavy than `A'`-heavy.
- and now the cyclic part is completely rigid: after subtracting the cyclic contribution and the
  deleted-set bias, the off-cyclic level functions have total oscillation at most `2`, so any
  nonconstant compensation matrix yields a uniform extremal rectangle `A_+ × B_-`.
- one off-cyclic separator lowers the extremal compensation by exactly `1` on its separated
  subrectangle, which resolves `(1,0)`, `(0,1)`, `(2,0)`, and `(0,2)` by descent.
- the mixed `(1,1)` case also collapses by iterating descent to a terminal mixed rectangle and then
  excluding any remaining one-sided traces by the already-settled `(1,0)` / `(0,1)` branches.
- therefore the direct packet-compression / supported-seeding route is now **locally closed**.

Also, all vertex-transitive cases are done: every vertex-transitive graph on `q^2` vertices already
contains a regular induced `q`-set.

That is the shortest proof roadmap I currently trust.

## 10. What the `q = 8` probe actually generalized

The long `q = 8` reduction was not valuable as an end in itself.
Its value is that two of its main structural conclusions generalize cleanly.

### 10.1. Split prime quotients are dead in general

If the weighted prime quotient is split, then it is a spider.
For every even `q`, a spider on total bag weight `q^2` with all bags of size `< q` is already good:

- `q / 2` edge-bearing legs give `(q / 2) K_2`,
- `q / 2` non-clique body bags give `overline{(q / 2) K_2}`,
- avoiding `I_q` and `K_q` bounds the remaining total leg/body weight,
- and the head contributes at most `q - 1`,

so the total weight is forced below `q^2` unless a regular `q`-set already exists.

Thus the split prime quotient branch can be discarded uniformly, not just at `q = 8`.

### 10.2. `C_5` is not a fundamental seed

Assuming the standard theorem that every prime `{P_5, bar P_5}`-free graph is split or `C_5`, the
`C_5` seed also disappears as an independent branch.

The `q = 8` attachment analysis on `C_5` is actually graph-theoretic: every outside vertex is either

- a center,
- an anticenter,
- a true clone,
- a false clone,

or it immediately creates an induced `P_5` or `bar P_5`.

So a larger prime non-split quotient cannot remain genuinely `C_5`-only.

### 10.3. The real general prime-quotient frontier

After these two general reductions, the honest remaining prime-quotient problem is no longer:

- arbitrary prime weighted quotients,
- and not even the three-seed family `C_5`, `P_5`, `bar P_5`.

It is now:

- weighted attachment theorems over `bar P_5`.

Reason:

- `C_5` is eliminated by prime-graph structure;
- `P_5` is equivalent to `bar P_5` by weighted quotient complementation.

That is the main reason not to keep grinding `q = 8` locally.
The right next theorem should be phrased directly at the weighted-house-seed level, and then
connected back to the dropped-part refinement package.

More sharply, the current prime-quotient frontier is now:

1. a **double-reseating local theorem** on the `16` remaining `7`-vertex templates coming from the
   six double-house swap types plus one distinguisher;
2. a **packet-exchange theorem** for a stable house, where the only live symmetric move is the top
   packet `(T_b, T_c)` (equivalently the rim packet `(Q_0, B_b, B_c)`).

That is the exact general local theorem surface left by the `q = 8` probe.

After the overlap-symmetry reduction, the first item improves further:

- the double-reseating theorem is now only a theorem on `12` explicit local `7`-vertex templates.

And after one more direct reseating reduction, this sharpens again to:

- a **3-core self-loop theorem** (corner-2, shoulder-3, roof-edge, all with `epsilon = 1`),
- together with **two off-ramp templates** that already land in the stable exceptional sector.

So the local theorem frontier is now closed.

Reason:

- the old one-fiber same-side theorem and the corner/shoulder twin-bag theorem unify;
- the clone-bag shifted twin-breaker does not create a new infinite descent:
  after one more forced distinguisher it reproduces the exact `O_10` configuration;
- the stable-house side is done: the unique surviving `O_10` continuation forces an arbitrarily
  long half-graph ladder inside one finite fiber, so `O_10` is impossible;
- the old roof oscillation theorem reduces through `T_ε` and `U_1`, but those templates collapse
  back into the old reseating automaton, so they leave no genuinely new branch.

Consequently the weighted-house seed theorem is complete, and with the split / `C_5` / `P_5`
reductions from Section `33`, the general prime-quotient branch is closed.
