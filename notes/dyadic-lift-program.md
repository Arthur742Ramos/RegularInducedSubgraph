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
`1/32`-large induced subgraph whose degrees are congruent modulo `4`.  A fixed Eulerian orientation of
the ambient even graph does not linearize the zero/two-residue case: the selected graph `E[W]` can be
oriented Eulerian after `W` is known, but the inherited orientation on `E[W]` need not be Eulerian and
its out-parity does not determine `deg_{E[W]}(v)/2 [MOD 2]`.  In matrix language, the exact first-bit
obstruction left after the higher-bit q-marker
closure is the deterministic principal-submatrix theorem for symmetric zero-diagonal matrices with even
row sums: find a `1/32`-large principal submatrix whose row sums are constant modulo `4`.  Edge-count
zero-sum partitions and random-graph modulo partitions do not imply this vertex-degree statement.  Nor do
the currently checked Scott/Hunter/Ferber--Krivelevich tools: Scott--Hunter gives a real bipartite
mod-`k` linear bound with all degrees `1 mod k`, while Ferber--Krivelevich proves the arbitrary-graph
`k=2` odd-degree conjecture with constant `1/10000`.  The former is bipartite-only and the latter
freezes only the parity bit, so neither supplies the loss-`64` arbitrary even-graph mod-`4` selector.
The newer prescribed-parity extension of Ferber--Krivelevich is still an `F_2` theorem: it prescribes
degree parity vertex-by-vertex with a small linear constant, but it does not control the carry
`binom(deg,2) [MOD 2]`.  Its directed partition characterization also confirms that fixed Eulerian
orientations do not give a free out-parity partition; a directed triangle is already an Eulerian
obstruction to even/even out-degree partition.
Iterating Gallai even/even partitions is also insufficient.  It gives nested even induced leaves of
size `n/32` after five halvings, and degrees to each discarded sibling layer are even, but the
half-degree parities of those sibling contributions are not synchronized.  The final leaf can still mix
degrees `0` and `2 mod 4`.
Likewise, a one-coordinate odd-degree theorem for 3-uniform hypergraphs is insufficient by itself.
The carry is the degree in the centered-pair 3-uniform hypergraph with edges `{v,x,y}` for pairs of
selected neighbors of `v`; an all-odd induced subhypergraph there synchronizes only
`binom(deg,2) mod 2`, while Gallai synchronizes only `deg mod 2`.  Closing via hypergraphs would require
a vector-valued induced parity selector for these two coordinates on the same support.
Prescribed-parity variants remain linear `F_2` inputs: they can choose the first bit of the retained
degrees, but the next bit is the carry `binom(deg,2) [MOD 2]`, equivalently the synchronized in/out
parity condition only after the selected even graph is oriented on its own.  That carry is exactly what
the first-bit selector must control.  Equivalently, for `v` in a retained set `W`, the residue `deg_W(v) [MOD 4]` is the pair
`(deg_W(v) [MOD 2], binom(deg_W(v),2) [MOD 2])`; the second coordinate counts unordered pairs of
selected neighbors of `v`.  The first-bit target is therefore exactly a simultaneous graph-degree and
centered pair-hypergraph parity selector, not a single linear parity-label theorem: find a `1/32`-large
`W` on which both coordinates are constant.

For the orientation route, a clean sufficient matrix target is available.  Fix an Eulerian orientation
of the ambient even graph and let `M` be its zero-diagonal orientation matrix over `F_2`.  If a set `S`
has all row sums and all column sums of the principal submatrix `M[S,S]` equal to the same bit `c`, then
every vertex in `S` has undirected degree `2c [MOD 4]`.  Thus the route is a diagonal
principal-submatrix row/column parity selector.  Bipartite parity theorems that choose unrelated row and
column sets do not enforce this diagonal constraint.

For nested sets `W subset S` with `B=S\W`, the carry obeys
`c_W = c_S + c_B + p_W p_B` over `F_2`, alongside `p_W=p_S+p_B`.  This identity is the exact terminal
self-layer equation: the last discarded layer must have both its linear degree bit and its centered
pair bit synchronized on the vertices that survive.
Equivalently, after taking a largest total-degree class `S0` in the even graph, the labels in the
co-degree form satisfy `alpha(v)+deg_H(v)=lambda`.  Thus the first-bit selector would already follow
from the fixed-modulus-four arbitrary-graph selector: every graph `H` has a `1/16`-large induced
subgraph whose degrees are congruent modulo `4`.  Applying this to `H=E[S0]` gives the required
`1/32` subset.  The arbitrary-label co-degree theorem would be sufficient but is stronger than needed.
A full four-color fixed-point partition would be stronger but is false: the labeled path with vertex
labels `(0,0,1)` along the path has no coloring `gamma` for which each vertex satisfies
`gamma(v)=alpha(v)+deg` into other color classes modulo `4`.  The remaining target must therefore be a
single-large-class theorem, not a partition theorem.
The primary-source Alon--Friedland--Kalai theorem is also not enough: it produces non-induced regular
subgraphs under almost-regular/density hypotheses, so it does not select a large principal submatrix of
an arbitrary Eulerian witness.
Even in the special anti-degree case `alpha+deg_H=lambda`, the full four-class coloring upgrade is too
strong.  It would require a partition into classes whose induced degree residues are
`lambda,lambda-1,lambda-2,lambda-3`; Balister--Powierski--Scott--Tan's random-graph partition theorem
has a finite Poisson limit for exactly this `q=4` one-class-per-residue count, hence such full
partitions do not exist deterministically.  The viable formulation is a partial anti-degree coloring
covering at least one quarter of the graph, or directly the single class of size `|H|/16`.
A bounded deterministic modular partition into self-regular classes would be a sufficient shortcut but
is stronger than the one-class selector: the Caro--Krasikov--Roditty bounded-partition problem is open
for fixed `q>2`, and the random-graph `q`/`q+1` partition theorems do not provide arbitrary-graph
principal submatrices.  Do not treat bounded modular color refinement as an available theorem.
The packet version of the same obstruction is now clean.  If `W` is a maximal mod-`4`-congruent
retained set of residue `r`, any outside packet `B` with `deg_B(w)` constant (`delta`) on old vertices
`w in W` and with `deg_W(b)+deg_B(b)=r+delta` for all `b in B` would enlarge `W`.  The old-vertex
condition is linear: from any outside pool of size greater than `3(|W|-1)`, AFK/Olson applied to the
mod-`4` difference vectors to a fixed anchor in `W` produces a nonempty packet whose degrees into `W`
are constant modulo `4`.  Thus the hard part is not balancing the old witness; it is forcing the
packet's own internal degrees to match the shifted residue, i.e. the same fresh self-layer carry.
Quantitatively, if `|W|=m<n/32`, then some degree-to-`W` chamber has size `>31m/4`; any universal
mod-`4` congruent induced-subgraph theorem with constant strictly larger than `4/31` would find a
larger witness inside that chamber alone.  Constants at or below `4/31` do not close this chamber
maximality route, so the proof still needs the special old-coordinate structure.
This kills the zero-shift sparse chamber: if `P_0={b: deg_W(b)=r}` contains an independent set larger
than `3|W|`, Olson on the full adjacency vectors supplies a nonempty subset with zero old degree
vector; its internal packet degree is zero, so it extends `W`.  Hence every maximal obstruction has
`alpha(P_0)<=3|W|`.  There is also a zero-target dense companion: in the chamber
`P_+={b:deg_W(b)=r+1}`, a clique larger than `3|W|` closes by Olson on the vectors
`((1_{bw}-1_{bw0})_{w != w0},1-1_{bw0})`, because zero sum gives constant old degree `delta` and
`|B|-delta=0`, while clique internal degree is `|B|-1`.  Thus terminality also gives
`omega(P_+)<=3|W|`.
The two zero-target chambers have an exact mixed rule: if `I subset P_r` is independent with
`deg_I(W)=0`, `K subset P_{r+1}` is a clique with constant old degree `kappa=|K|`, and the cross graph
between `I` and `K` is uniform `epsilon`, then `I union K` appends whenever `epsilon=0` forces
`|K|=0 [MOD 4]` or `epsilon=1` forces `|I|=0 [MOD 4]`.  The needed size congruence is just one extra
Olson coordinate.
In exact cross-regular form, if `c_I` is the degree from `I` into `K` and `c_K` from `K` into `I`, then
the mixed packet appends iff `c_I=kappa` and `|K|+c_K=kappa [MOD 4]`, with
`|I|c_I=|K|c_K`.
Old-frame double counts add `r|I|=0` and `m kappa=(r+1)|K|`; for the dense Olson cap `kappa=|K|`, this
is `(m-r-1)|K|=0`.
So odd `r` forces `|I|=0`, `r=2` forces `|I|` even, odd `m-r-1` forces `|K|=0`, and
`m-r-1=2` forces `|K|` even.
Equivalently, `( |I|-|K| )kappa=-|K|^2 [MOD 4]`; equal size residues require `|K|` even, while odd size
difference forces `kappa` uniquely.
The general two-packet scalar equation is: for internally regular cross-uniform packets
`B_a subset P_a`, `B_b subset P_b` with old increments `delta_a,delta_b`, internal residues `d_a,d_b`,
and cross value `epsilon`, their union appends iff
`a+d_a+epsilon|B_b|=b+d_b+epsilon|B_a|=r+delta_a+delta_b [MOD 4]`.
For finitely many internally regular packets with pairwise uniform cross values `epsilon_{jk}`, this
becomes
`a_j+d_j+sum_{k != j}epsilon_{jk}|B_k|=r+sum_k delta_k [MOD 4]` for every active packet `j`.
This is the cross-uniform chamber packet-system normal form of the first-bit self-layer residual.  The
exact form only needs cross-regularity modulo `4`: if `c_{jk}` is the common degree from vertices of
`B_j` into `B_k`, with edge-count symmetry `|B_j|c_{jk}=|B_k|c_{kj}`, then the equations are
`a_j+d_j+sum_{k != j}c_{jk}=r+sum_k delta_k [MOD 4]`.
The old increments also obey `m delta_j=a_j|B_j| [MOD 4]` by double-counting edges between `W` and
`B_j`; hence they are determined when `m` is odd, parity-determined when `m=2 [MOD 4]`, and impose
`a_j|B_j|=0` when `m=0 [MOD 4]`.
The old witness itself satisfies `mr=2e(W) [MOD 4]`, so odd `m` forces `r` even.
So for odd `m` the final target is intrinsic:
`r+m^{-1}sum_j a_j|B_j| [MOD 4]`.  For `m=0 [MOD 4]`, odd-size packets can occur only in chamber `0`;
for `m=2 [MOD 4]`, packets with `a_j|B_j|` odd are excluded.
By size residue: for odd `m`, all `(a,s)` are feasible; for `m=2`, `as` must be even, with
`delta` even when `s=0` and `delta=a [MOD 2]` when `s=2`; for `m=0`, `as=0`, so odd `s` forces
`a=0` and `s=2` forces `a` even.
The one-packet chamber test is
`a+d=r+delta` and `m delta=a|B|`, equivalently `m(a+d-r)=a|B| [MOD 4]`.  The zero-shift independent
and `+1` clique caps are the cases where Olson supplies the required old increment and internal residue.
In particular, if `m=0 [MOD 4]`, this reduces to `a|B|=0`; once an old-balanced internally regular
packet exists in an admissible chamber/size pair with prescribed increment `delta=a+d-r`, the target
residue adds no further arithmetic condition.  If `m` is odd,
`a=0` requires `d=r`, unit `a` determines `|B|`, and `a=2` fixes only the parity of `|B|`.
Equivalently, with `R_j=a_j+d_j+sum_{k != j}c_{jk}`, the system is the row-difference
condition `R_j=R_l` for all active packets plus the single scalar target
`R_j=r+sum_k delta_k`.  Terminality must therefore block either quotient self-layer compatibility or the
last old-increment target.
Summing the row equations gives the global scalar
`S r+(S-m)Delta=2e(B) [MOD 4]`, where `S=sum s_j`, `Delta=sum delta_j`, and
`2e(B)=sum_j s_j d_j+sum_{j != k}s_j c_{jk}`.  In particular, if the enlarged size `m+S` is odd, its
target residue `r+Delta` must be even.
For two packets this eliminates to scalar congruences.  With sizes `s_a,s_b` and
`A=(a+d_a)-(b+d_b)`, row equality gives `c_{ba}=c_{ab}+A`; edge-count symmetry becomes
`(s_a-s_b)c_{ab}=s_b A [MOD 4]`, and the final target is
`c_{ab}=r+delta_a+delta_b-a-d_a`.
After substituting the target, the single quotient congruence is
`(s_a-s_b)(r+delta_a+delta_b-a-d_a)=s_b((a+d_a)-(b+d_b)) [MOD 4]`.  If `s_a-s_b` is odd the cross
residue is unique; if it is `2`, existence requires an even right side and fixes the residue modulo `2`;
if it is `0`, the right side must vanish.
When `m` is odd, substitute `delta_a=m^{-1}a s_a` and `delta_b=m^{-1}b s_b`; two-packet feasibility then
depends only on chamber residues, packet sizes, and internal residues.
Modulo `2`, every odd-size packet subsystem has symmetric cross parities, so it is an undirected
quotient graph `Q` with labelled row condition `a_j+d_j+deg_Q(j)=constant [MOD 2]`.  The full
mod-`4` residues are the carry beyond this parity shadow.
The size-stratum form of edge-count symmetry is explicit: odd packet sizes determine the opposite cross
residue up to multiplication by a unit; a size-`0` packet forces incoming residue `0` from an odd packet;
two size-`2` packets only force cross residues equal modulo `2`; two size-`0` packets impose no
edge-count restriction modulo `4`.
For odd packets, equal size residues give symmetric cross residues modulo `4`, while opposite size
residues give sign reversal; this sign is the carry forgotten by the parity shadow.
There is an exact coalescence rule: same-chamber same-external-profile packets with cross residues
`c_{12},c_{21}` merge whenever `c_{12}=c_{21}`; the merged packet has old increment sum and internal
residue `d+c_{12}`.  Conversely, in an appendable packet system the two row values differ by
`c_{12}-c_{21}`, so row compatibility forces this equality.  Hence an appendable primitive packet system
uses at most one packet from each same-chamber external profile.
The other sparse chambers and the remaining dense targets are affine target-subsum
problems: an independent subset `B subset P_t` extends once
`sum_B(1_{bw})=t-r` for every old `w`, while a clique subset `B subset P_t` extends once
`sum_B(1-1_{bw0})=r-t+1`.  Thus the residual obstruction is target avoidance in `(Z/4Z)^{|W|}`, not
ordinary old-witness balancing.
Equivalently, the final lemma has the sharp form: any degree-to-`W` chamber of size greater than
`3|W|` in a maximum-cardinality witness must contain an affine packet whose old degrees are constant
and whose internal degrees hit the shifted residue.  The four chambers then force an extension unless
`|W|>=|H|/16`.  The lemma is false without maximality of `W` (large independent chambers can avoid
nonzero targets), so the remaining proof must use the absence of a larger mod-`4`-congruent induced
subgraph inside the chamber, not just Olson balancing.  With `W` chosen maximum, every chamber `P_t`
has `alpha(P_t)<=|W|`, `omega(P_t)<=|W|`, and more generally no mod-`4`-congruent induced subgraph
larger than `W`; hence a large chamber is already a dense/no-large-regular-witness object.  The final
affine-packet theorem must use this global maximum hypothesis, not mere inclusion-maximality.

For the formal loss-`32` endpoint one can spend more room than the sharp chamber lemma suggests.  If
`|W|=m<n/32`, then some chamber has size greater than `31m/4`; iterating Olson in that chamber leaves
at most `3(m-1)` vertices unused and gives an old-balanced union of size greater than `19m/4`.  Thus
the first-bit target can be attacked through a weaker large-packet replacement theorem: given an
old-balanced packet `B subset P_t`, either the append-only target
`deg_B(b)=r+delta-t` occurs on a nonempty subpacket, or one deletes a set `D subset W` and keeps
`W\D` together with many vertices of `B`.  The exact correction equations are

```text
deg_D(w) == r+delta-R       for kept old vertices w,
deg_D(b) == t+deg_B(b)-R    for packet vertices b.
```

The case `D=empty` is precisely the affine packet lemma; nonempty `D` is the replacement slack that
the loss-`32` constant may allow.
Equivalently, with `eta_B(b)=t+deg_B(b)-r-delta` and `lambda=r+delta-R`, the equations are
`deg_D(w)=lambda` on `W\D` and `deg_D(b)=eta_B(b)+lambda` on `B`.  Since `B` is old-balanced, a deletion
of size `d` must also satisfy
`sum_{b in B}(eta_B(b)+lambda)=d delta` and `lambda(m-d)=d r-2e(D) [MOD 4]`.
For `|D|=1`, this forces the deleted vertex to be all-zero or all-one on the kept old witness and forces
`eta_B(b)+lambda` to be an actual bit for every packet vertex.

The sharper way to spend this slack is more constrained than the first deletion-first formulation
suggested.  If `D subset W` and `E=W\D`, then the old-coordinate equation for a replacement packet is

```text
deg_B(w)-deg_B(e_0) == deg_D(w)-deg_D(e_0)       for w in E
```

after choosing a basepoint `e_0 in E`.  Ordinary Olson gives a large zero-target packet on the
coordinates of `E`; it does not by itself realize this arbitrary affine target.  Therefore the old
coordinates are automatic only when `deg_D` is constant on `E`, equivalently when `E` is itself a
mod-`4` congruent induced subset of the old witness `W`.

In that congruent-`E` subcase, Olson on the coordinates of `E` leaves at most `max(0,3(|E|-1))`
vertices unused, so a chamber of size `N>31m/4` gives an old-balanced packet `B_E` with

```text
|B_E| > N - max(0,3(|E|-1)) > m-|E|.
```

The loss-`32` theorem is therefore reduced not to arbitrary deletion, but to a simultaneous kept-old
self-layer correction: find such a congruent `E` and a packet, or a subpacket still larger than
`W\E`, for which

```text
deg_E(b)+deg_B(b) == constant       for every retained b.
```

Equivalently, one must rule out a chamber with no profitable signed packet `(B,D)` satisfying

```text
deg_B(w)-deg_D(w) == K          for w in W\D,
deg_B(b)-deg_D(b) == r+K-t      for b in B,
|B|>|D|.
```

Summing these equations gives the signed global scalar
`(m-d-s)K=(s-d)r+2e(D)-2e(B) [MOD 4]`, where `s=|B|` and `d=|D|`; if the resulting size `m-d+s` is odd,
then the new residue `r+K` is even.
Together with the full-frame old scalar `mK=s t-d r`, this yields
`(m-d-s)(s t-d r)=m((s-d)r+2e(D)-2e(B)) [MOD 4]`, eliminating `K` when `m` is odd.
Modulo `2`, odd `m` gives `r` even and `K=st`; thus odd `t` and odd `s` force even `d`.
This signed packet form is still the cleanest loss-`32` obstruction.  Deletion lowers the zero-sum
dimension only in the zero-target/congruent-`E` subcase, or after an additional theorem representing
the affine old-coordinate target; it is not a standalone Olson dimension count.

A correct signed Olson normalization is nevertheless available.  In the group
`(Z/4Z)^(W\{w_0})`, insert `p_b(w)=1_{bw}-1_{bw_0}` for every chamber vertex `b`, and insert
`-p_d(w)=-(1_{dw}-1_{dw_0})` for every old vertex `d in W`.  Greedy Olson on this combined positive
/ negative sequence leaves at most `3(m-1)` elements unused.  Therefore the union of the zero-sum
blocks gives a signed packet `(B,D)` with

```text
|B| >= |P_t|-3(m-1) > 19m/4,       |D| <= m,
deg_B(w)-deg_D(w) == constant      for every w in W.
```

If the constant is `K`, summing over the old frame gives the signed old-frame scalar
`mK=|B|t-|D|r [MOD 4]`; for odd `m`, `K` is determined by `|B|,|D|,t,r`, while for `m=0` the signed
packet must satisfy `|B|t=|D|r`.
The case table is: `m` odd gives `K=m^{-1}(s t-d r)`, `m=2` requires `s t-d r` even and fixes `K`
modulo `2`, and `m=0` requires `s t=d r` with `K` free from the old frame.
Thus the old side of a profitable replacement can be made honest with large positive surplus.  The
remaining obstruction is exactly the signed self-layer cleanup: refine such a packet, without losing
the surplus, until `deg_B(b)-deg_D(b)` is constant on the positive side.
Because the old witness has zero old-coordinate sum, this is the same as finding `E subset W` and
`B subset P_t` with `|E|+|B|>m` whose old-coordinate degrees are already constant; only the new
vertices in `B` still need their self-layer synchronized.

One should also avoid spending the chamber pigeonhole too early.  With `U=V(H)\W` and
`tau(b)=deg_W(b) [MOD 4]`, the direct labelled outside-packet target is

```text
deg_B(w)=delta              for all w in W,
deg_B(b)+tau(b)=r+delta     for all b in B.
```

If `m<n/32`, then `|U|>31m`; Olson on all of `U` gives an old-balanced `B_0` with
`|B_0|>28m`.  However, a class of `deg_{B_0}+tau` of size `>7m` need not remain old-balanced.
Rebalancing inside that class still leaves `>4m`, but a second ordinary four-way refinement drops the
available pool below the `3m` old-coordinate threshold if Olson is run afterward.  Thus the whole
outside version does not close by a finite classify/expose/rebalance loop.

The deleted-coordinate arithmetic after two unavoidable four-way refinements is:

```text
7m/4 - 3(m-d-1) > d,
```

which forces `d>5m/8-O(1)`.  Deletion can therefore make the final old-balance dimension feasible
only after removing most of `W`; it still does not create the corrected self-layer.  The remaining
lemma must synchronize the terminal self-layer while preserving old-balance.

In kept-old notation `E=W\D`, the desired replacement is simply a larger congruent set `E union B`:

```text
deg_E(w)+deg_B(w)=R          for w in E,
deg_E(b)+deg_B(b)=R          for b in B,
|E|+|B|>m.
```

This exposes the exact two-sided absorption barrier.  After the two exposed refinements the outside
pool has size `>7m/4`.  Choosing `E` first and then taking the best residue class of the final label
`deg_E(b)` leaves only `>7m/16` outside vertices, so one would need `|E|>9m/16`.  But choosing the
outside set first and then rebalancing old coordinates requires `|E|<3m/8+O(1)`.  These ranges are
disjoint.  Therefore the missing lemma must couple the choices of `E` and `B`; neither side can be
chosen first by a pure pigeonhole/Olson step.

The even-degree endpoint has a stronger co-absorbing formulation before reduction to arbitrary
labels.  If `U=V(H)\W`, one total-degree fiber `T subset U` has size `>31m/2`.  Writing `F=U\T` and
`C=T\B`, the append equations for retained `B subset T` become

```text
deg_T(w)-deg_C(w)=delta             for w in W,
deg_C(b)+deg_F(b)=s-r-delta         for b in B,
```

where `s` is the common total-degree residue on `T`.  Thus the even case asks for an outside
discard-set `C` that regularizes both the old side and the retained side.  Refining by the fixed label
`deg_F` costs a factor `4`, reducing the large `>31m/2` fiber to the familiar `>31m/8` chamber scale,
so this is not yet a proof; it is the cleanest even-specific alternative to the arbitrary labelled
self-layer lemma.

The stronger way to keep the even-specific slack is not to pass to an `h_0` residue class.  Let
`B_0 subset T` be old-balanced on `W`, with `|B_0|>25m/2`, and put

```text
h(b)=deg_W(b)+deg_{B_0}(b).
```

For old-balanced `B subset B_0`, with `X=B_0\B` and old increment `delta_B`, the append condition is

```text
theta_X(b):=h(b)-deg_X(b)-delta_B == r       for b in B.
```

But cardinal-maximal old-balance is trivial on the whole packet: `B_0` itself is old-balanced, so the
maximum old-balanced subset is `B_0` and the complement is empty.  Thus this whole-packet equation is
not a zero-sum-free boundary normal form.  A nontrivial boundary requires either restricting to a piece
such as the `h_0`-class `C`, or maximizing a value-correct condition rather than old-balance alone.

With the signed-Olson normalization, the first old-frame step inside `T` can be made stronger:
old-balancing a packet `B_0 subset T` leaves `|B_0|>|T|-3(m-1)>25m/2`.  A class of
`deg_{B_0}(b)+deg_W(b)` therefore has size `>25m/8`, barely above the `3m` threshold.  But an
ordinary rebalance inside that class leaves only `>m/8`, and a signed rebalance with old negatives no
longer guarantees positive surplus over the deleted old vertices.  Hence the even total-degree fiber
buys one extra exposed layer, but it still does not close by "classify, then rebalance."  The missing
co-absorption lemma must regularize the old frame while retaining the large self-layer class, not
after shrinking it by a Davenport loss.

After the large class is chosen, the self-layer can be written as a co-cut condition.  Let
`h_0(b)=deg_W(b)+deg_{B_0}(b)`, let `C` be a residue class of `h_0`, and put `R=B_0\C`.  For
`B subset C`,

```text
deg_W(b)+deg_B(b) = h_0(b)-deg_R(b)-deg_{C\B}(b).
```

Thus on `C` the desired final label is equivalent to

```text
deg_R(b)+deg_{C\B}(b) == H-r-delta_B       for b in B,
```

plus old-balance of `B` on `W`, where `H` is the common `h_0` value on `C` and `delta_B` is the
common old increment of `B`.  Mere constancy of the co-cut label is insufficient; the constant is
coupled to the old increment.  The terminal object is therefore a value-coupled old-balanced co-cut
lemma for a class just larger than `3m`, not a raw internal-degree synchronization problem.

Equivalently, with `q_C(b)=deg_C(b)+deg_R(b)`, one needs an old-balanced `B subset C` and a residue
whose old increment is `delta_B` such that

```text
deg_B(b) == q_C(b)-(H-r-delta_B)       for b in B.
```

The labels are not arbitrary: on the class `C`, `q_C(b)=h_0-deg_W(b)`, and the prescribed shift uses
the same old increment `delta_B` being balanced.  The missing theorem must use this coupling between
prescribed residue and old-neighbourhood vector; a black-box labelled mod-`4` induced-subgraph result
at this density would be stronger than what is currently available.

With old deletion allowed, the same class endpoint becomes a signed co-cut.  For `D subset W`,
`E=W\D`, and `B subset C`, the old side is

```text
deg_B(w)-deg_D(w) == K       for w in E,
```

while the new side is equivalent, on the `h_0`-class, to

```text
deg_R(b)+deg_{C\B}(b)+deg_D(b) == H-r-K        for b in B,
|B|>|D|.
```

This is the precise signed terminal lemma.  The class size `>25m/8` is enough to find an append-only
old-balanced subpacket, but not enough for a blind signed-Olson step on `C` to keep more positive
vertices than old deletions after the `3m` loss.  Hence the proof must either solve the append-only
co-cut on `C`, or preserve positive surplus while solving the signed co-cut.

The append-only version can be expressed through the discarded set `X=C\B`:

```text
deg_X(w) == deg_C(w)-K              for w in W,
deg_X(b) == H-r-K-deg_R(b)          for b in C\X,
X != C.
```

Thus the final non-signed lemma is a one-sided prescribed co-degree theorem for a proper discard
set.  The old equations prescribe the trace of `X` on `W`; the new equations prescribe the trace of
`X` only on vertices retained outside `X`.

Maximizing the retained side sharpens the obstruction further.  Choose `B subset C` maximal
old-balanced on `W` and set `X=C\B`.  Then `X` is zero-sum-free in the old-coordinate difference
group, so

```text
|X| <= 3(m-1),        |B| > |C|-3(m-1) > m/8.
```

The old-coordinate equation is automatic for this `X`; only the co-cut label

```text
eta_X(b)=deg_X(b)+deg_R(b)
```

must equal `H-r-delta_B` on `B`.  Hence the terminal obstruction is a zero-sum-free discarded boundary
whose co-cut label is either nonconstant or has the wrong value on every maximal old-balanced
complement.

The local exchange equations are explicit.  From `C=B disjoint_union X`, move `Y subset B` into the
discard and `Z subset X` into the retained set.  Old-balance is preserved iff

```text
sum_{z in Z} p_z == sum_{y in Y} p_y       in (Z/4Z)^(W\{w_0}),
```

and the new label is

```text
eta_{X'}(u)=eta_X(u)-deg_Z(u)+deg_Y(u)       for u in B\Y,
eta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)   for z in Z.
```

The value-coupled label also changes by the old increment.  With `delta_B=deg_B(w_0)`,

```text
delta_{B'}=delta_B+deg_Z(w_0)-deg_Y(w_0),
theta_X(v)=eta_X(v)+delta_B,
```

and hence

```text
theta_{X'}(u)=theta_X(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0)
                                                    for u in B\Y,
theta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)+delta_{B'}
                                                    for z in Z.
```

The target value is the fixed residue `H-r`.

The final boundary-exchange lemma is to find such an old-vector-balanced exchange making `theta`
equal to `H-r` on `B'=(B\Y) union Z`.  A pure discard (`Z=empty`) only recurses inside `B`; any real
closure has to use vertices of the zero-sum-free boundary `X`.

The extremal boundary should be chosen lexicographically: first maximize `|B|` among old-balanced
subsets of `C`, then maximize the target fiber `{b in B : theta_X(b)=H-r}` of the corrected label
`theta_X=eta_X+delta_B`.  Such a boundary has no
old-vector-balanced exchange with `|Z|>|Y|`, and no equal-size exchange that improves the largest
updated target fiber.  Hence the terminal obstruction can be stated as a target-stable zero-sum-free
boundary:

```text
X zero-sum-free;
no balanced exchange imports more from X than it exports from B;
no equal-size balanced exchange improves the target theta-fiber.
```

This is the strongest finite local target reached so far.

Writing `T={b in B : theta_X(b)=H-r}`, target-stability means every balanced equal-size exchange
`(Y,Z)` satisfies

```text
|{u in B\Y : theta_{X'}(u)=H-r}| + |{z in Z : theta_{X'}(z)=H-r}| <= |T|.
```

For a singleton same-old-vector swap `y -> z`, this compares the neighbourhoods of `y` and `z` inside
the retained side; in the exact basis model the anchor shift vanishes.

With `L=H-r`, define the vertices gained by the swap as non-target vertices moved to `L`, plus the
imported vertex if it lands at `L`; define losses as target vertices moved away from `L`, plus the
exported vertex if it was target.  Target-stability is precisely `gain(y,z)<=loss(y,z)` for every
same-old-vector singleton import.  Hence every target-correct boundary import must be paid for by a
lost target vertex.
Equivalently, if `A_{y,z}` is the set of off-target retained vertices corrected by swapping out `y` and
in `z`, and `D_{y,z}` is the set of target vertices knocked off target, then
`|A_{y,z}|+1_{z lands on target}<=|D_{y,z}|+1_{y in T}`.  Boundary vertices in each old-vector class are
therefore dominated by their signed cut across the current target fiber.
Summing over all exports in the same old-vector class `B_p` gives
`sum_y(|A_{y,z}|-|D_{y,z}|)<=|T cap B_p|-|B_p|1_{z lands on target}`.
When the anchor shift vanishes, decompose off-target vertices into `T_+`, `T_-`, and `T_2`.  Singleton
swaps never correct `T_2`; the exact inequality is
`|N(y)\N(z) cap T_-|+|N(z)\N(y) cap T_+|+1_{z target}
 <= |(N(y) triangle N(z)) cap T|+1_{y in T}`.
For a zero-anchor balanced two-for-two exchange, put
`s_{Y,Z}(u)=deg_Y(u)-deg_Z(u) in {-2,-1,0,1,2}`.  Then `s=1` corrects `T_-`, `s=-1` corrects `T_+`,
and `|s|=2` corrects `T_2`; target vertices are damaged exactly where `s!=0`.  Thus the pair-exchange
inequality is the first local test that can see a pure `2`-error layer.
A terminal pure-`T_2` branch therefore forbids any zero-anchor balanced pair cut with many vertices
complete to the exports and anticomplete to the imports, or conversely, unless the same cut damages at
least as many target vertices.
Summing this inequality over all admissible export pairs in an old-vector fiber `A` gives the quadratic
common-neighborhood form
`sum_{u in T_2,deg_Z(u)=0} binom(deg_A(u),2)+sum_{u in T_2,deg_Z(u)=2} binom(|A|-deg_A(u),2)`
bounded by the target pair-damage plus `( |A|-1)|A cap T|`.
Hence an unpaid pure-`T_2` vertex that misses an import pair sees at most one export vertex in `A`, while
one that sees the import pair misses at most one export vertex.
For an exact basis direction with three boundary copies, applying this to the three import pairs gives a
majority synchronization rule: each unpaid `T_2` vertex is almost constant on the matching old fiber, with
the constant equal to the majority of its adjacency to the boundary triple.
Writing `M_g(u)=1_{deg_{Z_g}(u)>=2}`, the exceptional sets
`Q_g(a)={u in T_2:1_{ua}!=M_g(u)}` are disjoint across `a in A_g`.
Thus deleting at most one old-fiber vertex per unpaid `T_2` vertex leaves a core that is silent on the
pure `2`-error layer.
On each of the eight boundary-pattern cells, a matching majority pair from the boundary triple makes every
nonexceptional old pair silent on that cell; this is the ternary one-corner lift.
For the silent core `A_g^0`, terminality reduces to the signed repair spectrum: `G[A_g^0]` cannot contain
an induced `d'`-regular four-set for any `d' in Rep(g)`.
If `{0,3} subset Rep(g)`, then `|A_g|<=|T_2|+R(4,4)-1`; hence any larger exact-basis fiber must have an
old-side repair spectrum missing one Ramsey extreme.
Writing `d=r-omega(g)`, a missing extreme `rho in {0,3}` is equivalent on every usable small deletion
`D` with constant `c` to the anti-Horn exclusion `deg_D(b_g) != rho-d+c [MOD 4]`.
For singleton and pair deletions this forbids one concrete adjacency count to the direction type.
The shift-addition law sharpens this: in a very large unit-shift branch, all nonzero singleton/pair
repairs meet a kernel `K_g` of size at most three.  Outside `K_g`, every usable small deletion has zero
shift, i.e. `deg_D(b_g)=c`.  Thus the direction type is invisible to all co-regular one- and two-witness
tests off the kernel; if those tests separate realized outgoing defects, anchored persistence plus
componentwise no-split gives the singleton conclusion, and if they do not, the remaining pair is a
chamber-flat silent edge for the one-corner lift.
The opposite-shift branch `sigma_g=2` is handled by the augmented exact-basis cube analysis: it gives
the `{0,2}`/`{1,3}` hereditary pairs, and the boundary-type/one-corner tables cap those directions by
`7m+O(1)`.  The unit hereditary pair `{0,1}`/`{3,2}` is capped by target-stability via the
endpoint-exclusive mod-`4` layer theorem.  Thus large same-direction repair spectra are no longer the
main obstruction; what remains is the terminal co-cut self-layer selector.
In that unconstrained selector every equal-size pair exchange is legal.  Summing over all export pairs
and all import pairs gives, for each unpaid `u in T_2`, the biquadratic contribution
`binom(deg_B(u),2)binom(|X|-deg_X(u),2)+binom(|B|-deg_B(u),2)binom(deg_X(u),2)`, bounded by total target
pair-damage.  Therefore any unpaid pure `2`-error vertex must be almost constant on both sides of the
cut, unless the target layer pays for many pair exchanges.
More precisely, target damage for `t in T` is
`sum_{i!=j}N_B^i(t)N_X^j(t)`, with `N_B^i,N_X^j` the pair-degree counts.  For side sizes at least three,
zero polarity is exactly one-corner sparse or one-corner dense, while zero target damage is exactly a
cut-constant target vertex.  The final accounting problem is therefore mixed `T_2` polarity versus mixed
target cut profiles.
The accounting gives the charging bound
`|U|min_U Polar <= |T|max_T Damage + binom(|X|,2)(|B|-1)|T|` for every `U subset T_2`.
Thus the linearly mixed part of `T_2` is `O(|T|)` and can be charged to the target layer; the residual
selector problem is one-corner polarized.
The exact zero-polarized part is bounded: the sparse side induces maximum degree at most one and the
dense side has complement maximum degree at most one, so each has at most `2m` vertices in a terminal
configuration.  Otherwise isolated/matching components, or their complements, give an outside-only
congruent set larger than `m`.
More generally, at scale `L`, low-polarity vertices with `Polar<binom(L,2)^2` are `L`-sparse or
`L`-dense when both cut sides have size at least `2L`; these two pieces have size at most `Lm` each.
Therefore
`|T_2|<=2Lm+(|T|max_T Damage+binom(|X|,2)(|B|-1)|T|)/binom(L,2)^2`.
The same degeneracy/complement-degeneracy bound applies to sparse/dense target vertices.  Hence the only
target mass that can pay for mixed `T_2` polarity is itself scale-mixed across the cut.
The summed profile is
`sum_T Damage <= |T_mix(L)|binom(|B|,2)binom(|X|,2)+C L^2m|B||X|(|B|+|X|)`.
Thus the nonlinear part of the final inequality is exactly the mixed-target core.
Bucketing the four cut factors dyadically makes the core homogeneous: on one bucket, `Damage` and `Polar`
are comparable, and terminality says the mixed `T_2` bucket is paid by the mixed target bucket, up to the
already linear sparse/dense error and a logarithmic bucket loss.
After also refining by `deg_B,deg_X mod 4`, all external cut residues are fixed.  The final homogeneous
bucket asks only for an internal induced subgraph with constant degree modulo `4`, i.e. a
principal-submatrix selector on one cut-homogeneous bucket.
In deletion form, for `D` the removed layer, this asks for
`deg_D(v)==deg_H(v)-c mod 4` on all retained vertices; terminal buckets are rigid against every such
large-complement deletion equation.
Splitting this congruence gives the Gallai parity co-cut equation plus the centered cut-pair parity
equation on the same deletion layer, so the carry line is the only remaining unsynchronized bit.
The equivalent pruning form fixes `c` and repeatedly deletes every vertex violating
`deg_D(v)==deg_H(v)-c mod 4`; a terminal bucket is exactly one in which every such pruning process
avalanches down to at most `m` retained vertices.
Equivalently, the complement iteration keeps only vertices whose current induced degree is `c mod 4`.
The remaining theorem is that some induced chamber has a mod-`4` residue-core larger than `m`.
Terminal buckets therefore have a hereditary four-residue degeneracy certificate: for each residue `c`,
every induced chamber can delete all but at most `m` vertices through current degrees not equal to `c`.
The formulation is self-dual under complement, with residue shift `c -> |S|-1-c` on a retained set `S`.
A minimum loss-`32` counterexample is critical: with maximum selector size `m`, it has order `32m+1`, and
every vertex deletion contains a selector, equivalently a stable residue-core, of size exactly `m`.
Any two maximum cores then form an equal-petal exchange: on the overlap the two petals have fixed
degree-difference residue, and on each petal the internal degree plus overlap degree is fixed.
For a one-vertex exchange, only identical-trace or complete/anticomplete trace patterns are possible;
the matching-edge subcases that create `m+1` selectors are excluded by terminality.
Selector blocks merge by the quotient rule `a_i+sum_j p_{ij}x_j=constant mod 4`; terminal buckets forbid
every cross-regular quotient solution whose lifted size exceeds `m`.
The one-vertex merge shadow forces maximum residue-`0` selectors to dominate and, when `|S|==a+1 mod 4`,
forces every outside vertex to miss a residue-`a` selector; the complement gives the dual condition.
For outside pairs, terminality forbids the three uniform trace extensions: both missed, both complete, or
complementary traces on the selector, whenever the corrected pair degrees satisfy the same mod-`4`
quotient residue.
For a maximum core `S`, Davenport in `(Z/4)^S` produces zero-trace packets in every outside degree chamber
of size at least `3m+1`; terminality says no such packet, nor any union of disjoint packets in the same
degree chamber, may have the matching internal residue needed to merge with `S`.
Quotienting traces by the constant all-ones vector gives the sharper constant-trace packet form with
threshold `3m-2`; a constant-trace `p` packet in degree chamber `t` may not be an internal
residue-`a+p-t` selector.
The packet parameters obey `|X|t==mp mod 4` by counting the cross edges to the maximum core in the two
directions.
The matching internal residue additionally must pass the handshaking filter `|X|(a+p-t)==0 mod 2`, with
the parity of `e(X)` then fixed.
Refining the Davenport group by a size mod-`4` coordinate gives constant-trace packets with
`|X|==0 mod 4` from any `3m+1` vertices in one outside degree chamber; these automatically pass
handshaking, and their cross-count condition is just `mp==0 mod 4`.
Large row-twin classes, complement-row classes, and modules close immediately: false twins give
independent selectors, true twins give clique selectors, and modules have constant outside contribution.
Thus a terminal principal bucket is selector-prime and high-rank over `F_2` in both graph and complement.
It is also hereditarily dense and codense at scale `m`, since any induced chamber containing an
independent set or clique larger than `m` already closes.

Do not replace the exchange lemma by a zero-sum-free statement for the `eta_X`-fibers.  If
`S subset B` is old-balanced and `eta_X` is constant on `S`, appending `S` still changes the discard
from `X` to `X union (B\S)`, so the relevant label is

```text
eta_{X union (B\S)}(s)=eta_X(s)+deg_{B\S}(s).
```

The pure-discard case therefore recurses; it closes only when the value-coupled updated label

```text
theta_{X union (B\S)}(s)=eta_X(s)+deg_{B\S}(s)+delta_S
```

equals `H-r` on `S`.  The terminal obstruction is not a five-piece zero-sum-free decomposition by
`eta_X`-fibers.

If both `S` and `B\S` are old-balanced, this recursive condition has the cleaner form

```text
theta_{X union (B\S)}(s)
  = theta_X(s)+deg_{B\S}(s)-delta_{B\S}.
```

Hence `S` exits exactly when

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S} == H-r       for every s in S.
```

Every old-balanced block must fail this block-interaction equation in a terminal counterexample.

For an old-balanced block decomposition `B=S_1 disjoint_union ... disjoint_union S_l` with increments
`delta_i`, the block `S_i` exits exactly when

```text
theta_X(s)+sum_{j != i} (deg_{S_j}(s)-delta_j) == H-r       for every s in S_i.
```

So the no-import endpoint can be viewed as an interacting zero-sum-block system in which every block
has a nonzero corrected interaction defect.

For a minimal old-balanced block `S`, write the defect

```text
phi_S(s)=theta_X(s)+deg_{B\S}(s)-delta_{B\S}-(H-r).
```

Pure discard closes exactly when `phi_S=0`.  A local import repair chooses nonempty `Z subset X` and
`Y subset S` with `sum p_Z=sum p_Y`, replacing `S` by `(S\Y) union Z`.  On vertices `u in S\Y`, the
defect changes by

```text
phi_{S'}(u)=phi_S(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0).
```

So the local move is a value-coupled zero-sum exchange that kills `phi_S`, not just a balanced import.

The same defect also has a boundary-free form.  Since

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S}
  = deg_{B_0\S}(s)+delta_S
```

and `H=deg_W(s)+deg_{B_0}(s)` on `C`,

```text
phi_S(s)=r+delta_S-deg_W(s)-deg_S(s).
```

Thus a zero-defect block is exactly a self-correcting atom that appends to the old witness.  Boundary
exchange is a way to replace `S` by another old-balanced atom `S'` for which the same append defect
vanishes.  The maximal split only supplies a zero-sum-free exchange reservoir.

For any old-balanced atom `S`, the scalar sum is

```text
sum_{s in S} phi_S(s)=|S|r+(|S|-m)delta_S-2e(S)       [MOD 4].
```

This scalar identity is necessary but not sufficient; the remaining theorem is pointwise defect
synchronization on an old-balanced atom.

There is a signed atom version.  Replacing `W` by `E=W\D` and adding an old-balanced atom `S` succeeds
with residue `r+delta_S-c` iff

```text
deg_D(w)=c                  for w in E,
deg_D(s)=c-phi_S(s)         for s in S,
|S|>|D|.
```

So append-only closure is the special case `D=empty`; a terminal obstruction must also rule out all
smaller old corrections of defective atoms.
The signed atom scalar tests are
`c(m-d)=d r-2e(D)` and `s c=d delta_S+sum_{u in S}phi_S(u) [MOD 4]`, equivalently
`s c=s r+(s-m+d)delta_S-2e(S) [MOD 4]`.  Thus `c` is fixed when `m-d` is odd, while `m=d` requires
`d r=2e(D)`.
For `|D|=1`, `c` is a bit, so either `c=0,r=0` or `c=1,r=m-1`; the defect values on `S` must lie in
the adjacent pair `{c,c-1}`.
More generally, if `d=|D|<4`, then `c` is an actual integer `0<=c<=d`, the defect support lies in
`{c,c-1,...,c-d}`, and `c(m-d)=d r-2e(D) [MOD 4]`.  Thus `d=2` allows only three consecutive defect
residues; `d=3` is the first size with no pointwise support restriction.

The `h_0`-class has a little unused rank margin.  Since `|C|>25m/8`, Olson can be run on
`m-1+a` fixed `Z/4Z` coordinates whenever `3(m-1+a)<|C|`.  Thus one may add at least one auxiliary
coordinate, and for large `m` about `m/24` of them.  This can force scalar side conditions such as

```text
|S|=0,        delta_S=0,        or        sum_{s in S} deg_R(s)=0        [MOD 4].
```

For `m>24`, two auxiliary coordinates are affordable; using the constant and anchor-adjacency
coordinates gives a nonempty old-balanced atom with `|S|=0` and `delta_S=0`, so
`sum_S phi_S=-2e(S) [MOD 4]`.

This does not close the self-layer by itself: the atom condition remains pointwise,
`r+delta_S-deg_W(s)-deg_S(s)=0` for every `s in S`.  Any successful use of the extra `25m/8` slack must
turn these auxiliary scalar constraints into pointwise defect cancellation or into a signed atom
repair.

The maximal-boundary condition is also a sumset-separation statement.  If
`Sigma_l(X)` denotes sums of `l` boundary old-vectors, then no equality
`sum p_Y=sum p_Z` with `Y subset B`, `Z subset X`, and `|Z|>|Y|` is allowed.  In particular,
`p(B)` avoids every boundary subset-sum of length at least two.  In the exact extremal
zero-sum-free model `X={e_i,e_i,e_i : 1<=i<=d}` in `C_4^d`, every nonzero element except the basis
elements `e_i` is such a length-at-least-two sum.  Hence retained vectors in the extremal model must
be only `0` or basis vectors, and minimal atoms reduce to zero-row singletons or four-copy same-basis
atoms.  The near-extremal inverse-Davenport branch should therefore either find a profitable import
from a deviation from this basis model, or solve these singleton/four-copy atom defects by append or
signed repair.

In that exact basis case, a zero-vector singleton closes iff `r=0`.  A four-copy atom in one feasible
basis direction `g` has a fixed old-neighbourhood residue `omega(g)=deg_W(b)` and defect

```text
phi_S(b)=r-omega(g)-deg_S(b).
```

So it closes exactly when the four selected vertices induce the required regular four-vertex type
modulo `4`.  This catalogue is finite but not yet forcing: the retained mass can be spread over many
basis directions, and a single direction may avoid the one required regular four-vertex type without
contradicting the current maximality bounds.

Signed deletion does not repair a nonregular four-copy atom within one basis direction: all four
vertices have the same old neighbourhood, so `deg_D` is constant on them for every `D subset W`.  The
signed condition then forces the original defect to be constant, i.e. the four vertices were already
regular.  Thus the exact extremal branch needs either the required regular four-set in a basis fiber or
a cross-direction import that changes internal degrees non-uniformly.

A regular four-copy atom with the wrong residue is a separate signed branch.  If the induced degree is
`d'` and the required value is `d=r-omega(g)`, the defect is the constant `d-d'`; signed repair reduces
to finding `D subset W` with `|D|<4`, constant degree on `W\D`, and the shifted prescribed intersection
with the common old-neighbourhood type of the direction.  Thus terminal exact-basis configurations must
also block these small old co-regular deletion repairs.

For each direction this gives a repair spectrum `Rep(g)` of regular four-block residues repaired by
deletions `D subset W` with `|D|<4`; the append-only required residue is included via `D=empty`.  A
terminal direction fiber must avoid induced regular four-sets of every residue in `Rep(g)`.  In
particular, if both `0` and `3` lie in `Rep(g)`, then Ramsey bounds the fiber by `R(4,4)`, since those
are independent four-sets and cliques.

The same constant-defect repair applies to larger same-direction blocks: if `|S|=0 mod 4` and `G[S]`
is regular of degree `d'`, then the defect is constant `d-d'`, and signed repair only asks for an old
co-regular deletion `D` with `|D|<|S|` and the shifted intersection with the direction type.  Large
empty/complete direction fibers therefore remain attackable through larger surplus blocks; a terminal
fiber must block all such constant-defect repairs.

Equivalently, with `E=W\D`, the condition that `deg_D` is constant on `W\D` says exactly that `E` is
itself a congruent induced witness inside the old maximum witness `W`.  Constant-defect signed repair
therefore splices a same-direction regular block onto a smaller old witness, subject to the scalar
intersection condition with that direction and the surplus inequality `|S|>|D|`.

In this language the repair spectrum is explicit: if `d=r-omega(g)` is the append-only required residue
and `deg_D(w)=c` on `E=W\D`, then a regular block of residue

```text
d' = d + deg_D(b_g)-c
```

is repaired, where `b_g` is any vertex of the direction type.  For `|D|<4`, this is just the catalogue
of singleton, pair, or triple deletions whose external degree into the kept old witness is constant;
the residue shift is `|N_W(b_g) cap D|-c`.
For a singleton, either `c=0,r=0` and the deleted old vertex is isolated from the kept old witness,
giving shift `1_{b_gx}`, or `c=1,r=m-1` and it is complete to the kept old witness, giving shift
`1_{b_gx}-1`.  For a pair `{x,y}`, with `e=1_{xy}` and `a=|N_W(b_g) cap {x,y}|`, the three cases are:
anticomplete pair with `r=e [MOD 2]` and shift `a`; split pair with `m-2=2(r-e) [MOD 4]` and shift
`a-1`; complete pair with `m-2=r-e [MOD 2]` and shift `a-2`.

Thus, with `Delta_<(4)(g)` the set of these small shifts, terminality should be read
residue-by-residue:

```text
0 in d+Delta_<(4)(g)  =>  no independent four-set in the direction;
3 in d+Delta_<(4)(g)  =>  no clique four-set in the direction;
1 in d+Delta_<(4)(g)  =>  no induced 2K_2 in the direction;
2 in d+Delta_<(4)(g)  =>  no induced C_4 in the direction.
```

Only if both `0` and `3` lie in the repair spectrum does Ramsey bound the direction by `R(4,4)`.
Therefore the old "middle-only" conclusion was too strong: a large terminal direction may still carry
one extreme residue, and that branch must be controlled by outside-only maximality or by the augmented
boundary sieve.

The middle residues have concrete first obstructions: repaired residue `1` means the direction fiber is
induced-`2K_2`-free, while repaired residue `2` means it is induced-`C_4`-free.  Larger same-direction
regular blocks give stronger exclusions, but these two hereditary classes are the visible terminal branch.
Since `2K_2` and `C_4` are complements, any direction whose repair spectrum contains both middle
residues is forced into the much narrower class avoiding both patterns; remaining large examples must
be controlled by the outside-only maximum constraint on repeated cyclic/split-like blocks.
Using the pseudo-split characterization of `(2K_2,C_4)`-free graphs, such a direction decomposes into
a clique part, an independent part, and at most a five-cycle core.  Because no clique or independent
set inside a chamber can exceed `m=|W|`, a pseudo-split direction has size only about `2m+5`.  Thus
any much larger direction fiber must have a repair spectrum missing one of the middle residues.
The corrected conclusion above the pseudo-split cap is a spectrum-hole condition, not singleton
rigidity: the spectrum cannot contain both middle residues, and it cannot contain both extreme residues
unless the fiber is Ramsey-small.  Singleton/pair/triple co-regular deletions in `W` remain useful
because each nonzero shift adds one of the hereditary constraints in the displayed list, but
`Delta_<(4)(g)={0}` still needs a separate argument.
Since the empty deletion always contributes shift `0`, two distinct nonzero shifts in
`Delta_<(4)(g)` would give three repaired residues.  Every three-residue subset contains either both
extremes `{0,3}` or both middle residues `{1,2}`.  Hence any terminal exact-basis direction with
`|C_g|>=R(4,4)` and `|C_g|>2m+5` has `Delta_<(4)(g) subset {0,sigma_g}` for one nonzero shift at most;
all usable singleton and pair deletion shifts against such a direction must coincide.
Disjoint usable deletions add shifts: if `D_1,D_2` have constants `c_1,c_2` and total size below four,
then `D_1 union D_2` has constant `c_1+c_2` and shift `shift(D_1)+shift(D_2)`.  Thus a very large
terminal direction cannot contain two disjoint usable deletions of unit shift `1` or `3`; their union
would create the new shift `2`.
So the large branch splits: unit `sigma_g` forces the nonzero-shift singleton/pair repairs into an
intersecting family, while `sigma_g=2` is the only branch where disjoint nonzero repairs can add back to
zero.
For unit `sigma_g`, the pair family is therefore a star or a triangle: if a nonzero singleton exists all
nonzero pairs contain it; otherwise pairwise-intersecting two-subsets are either all incident to one old
vertex or lie in the three edges of one old triangle.
Equivalently, there is a kernel `K_g subset W`, `|K_g|<=3`, such that every usable singleton or pair
deletion disjoint from `K_g` has zero shift.
For `sigma_g=2`, split pairs never contribute.  The nonzero pair repairs are exactly anticomplete old
pairs with both vertices in `N_W(b_g)` or complete old pairs with both vertices outside `N_W(b_g)`.
All usable singleton shifts are zero: isolated old deletion vertices in the `r=0` case are missed by
`b_g`, and universal old deletion vertices in the `r=m-1` case are hit by `b_g`.
Since `Rep(g) subset d+{0,sigma_g}`, the large-fiber exclusions leave only `{0,1}` or `{2,3}` in the
unit-shift branch, and only `{0,2}` or `{1,3}` in the `sigma_g=2` branch.
These are respectively: `alpha<=3` plus `2K_2`-free; `omega<=3` plus `C_4`-free; `alpha<=3` plus
`C_4`-free; and `omega<=3` plus `2K_2`-free.
Up to complement, the exact-basis endpoint is therefore: unit `sigma_g` gives `alpha<=3` and
`2K_2`-free, while `sigma_g=2` gives `alpha<=3` and `C_4`-free.
The standard `C_5` blow-up obstruction is capped: in a clique blow-up with bags `A_i`, equal bag
selection is regular, so if all bags have size `>m/5` it gives an atom larger than `W`; otherwise one
bag has size at most `m/5`, and the adjacent clique caps `|A_i|+|A_{i+1}|<=m` force
`sum_i |A_i|<=11m/5`.
In the self-complementary independent-bag orientation, the stronger three-consecutive selector applies:
for capacities `A,B,C`, choose `x,z` with `x+z=A+C` and `y=x+z [MOD 4]`, `y>=B-3`.  This gives a
congruent atom of size at least `A+B+C-3`, so terminality forces every three consecutive bags to have
size at most `m+3`, and the whole cyclic component has size at most `(5m+15)/3`.
The two hereditary endpoints have anchor decompositions.  In the `2K_2`-free branch with `alpha<=3`,
every edge dominates all but at most three vertices.  In the `C_4`-free branch with `alpha<=3`, every
nonedge has clique common-neighborhood and clique common-nonneighborhood, each of size at most `m`; the
large residual is therefore in the two exclusive neighborhoods.
For either anchor pair `p,q`, with `epsilon=1_{pq}`, equal exclusive wings `X,Y` of size `h` give a
new-side-regular packet exactly when `deg_{X union Y}(z)=h+epsilon-1` on every wing vertex.  In one
nonzero exact-basis direction it is old-balanced only for odd `h`.  The `h=1` case forbids cross-edges
for edge anchors and cross-nonedges for nonedge anchors.
Therefore the unit branch, already `2K_2`-free, is also `C_4`-free, and the `sigma_g=2` branch, already
`C_4`-free, is also `2K_2`-free.  The endpoint is pseudo-split; with one side bounded by `m` and the
other by `alpha<=3` up to complement, every terminal exact-basis direction has size at most `m+8`.

The three boundary copies in a basis direction give an immediate `3+1` test.  If
`X_i={x_{i,1},x_{i,2},x_{i,3}}` are the boundary copies of direction `g_i` and `b in B` also has
old-vector `g_i`, then `X_i union {b}` is old-balanced.  It closes if it induces the required regular
four-vertex type of degree `r-omega(g_i)`.  For a fixed triple, the allowed extension pattern is unique:
miss an independent triple for degree `0`, hit the isolated vertex of a one-edge triple for degree `1`,
hit the endpoints of a path triple for degree `2`, and hit all of a triangle for degree `3`.  Terminal
exact-extremal configurations must avoid these allowed `3+1` patterns in every direction.

The augmented direction actually gives more tests.  Since `X_i` and the retained fiber `C_i` have the
same old vector, every four-set `Y union Z` with `Y subset X_i`, `Z subset C_i`, `|Y|+|Z|=4`, and
`Z nonempty` is old-balanced.  It closes exactly when

```text
deg_Y(y)+sum_{z in Z}1_{zy}=d_i        for y in Y,
deg_Z(z)+|N_{X_i}(z) cap Y|=d_i        for z in Z,
```

where `d_i=r-omega(g_i)`.  Thus the exact-basis sieve must include the mixed `2+2` and `1+3` atoms, not
only `3+1` and four-retained atoms.  Each retained vertex has one of eight adjacency types to the
boundary triple; terminality forbids the finite regularity patterns produced by these type equations.
The same mixed atom is signed-repairable whenever its regular residue lies in `Rep(g_i)`, since the
defect is constant on the augmented direction.  Thus replace `d_i` by each residue in the repair spectrum
when applying the augmented sieve.

For `2+2` atoms the equations simplify.  If `Y={x,y} subset X_i`, `Z={b,c} subset C_i`, `e=1_{xy}`,
and `epsilon=1_{bc}`, then `Y union Z` is `d_i`-regular iff `epsilon=e` and the bipartite square between
`{b,c}` and `{x,y}` is `(d_i-e)`-regular.  Thus the cross square is empty, 1-regular, or complete
according as `d_i-e=0,1,2`.  For `1+3` atoms, a boundary vertex `x` and retained triple `T` close iff:
independent/all miss `x` for `d_i=0`; one hitter isolated for `d_i=1`; two hitters with the unique
misser as the middle of a `P_3` for `d_i=2`; triangle/all hit `x` for `d_i=3`.

As type constraints, a boundary pair `{x,y}` of status `e` forbids retained edge-status `e` on type
`00` pairs when `d_i-e=0`, on complementary `10/01` pairs when `d_i-e=1`, and on type `11` pairs when
`d_i-e=2`.  For a boundary vertex `x`, terminality gives: if `d_i=0`, the miss class has no independent
triple; if `d_i=3`, the hit class has no triangle; if `d_i=1`, each hitter's non-neighbours in the miss
class are independent; if `d_i=2`, each misser's neighbours in the hit class are a clique.
In the signed form, replace `d_i` by each residue `s in Rep(g_i)`.  Repaired extreme residues therefore
act before Ramsey: `0 in Rep(g_i)` gives independence number at most `2` in every boundary-miss class,
and `3 in Rep(g_i)` gives clique number at most `2` in every boundary-hit class, while the `2+2`
boundary-pair restrictions use `q=s-e`.
If `Rep(g_i)` contains all four residues, the `2+2` rules force each of the eight retained boundary
types to be a clique, an independent set, or a singleton: equal-bit boundary pairs prescribe the internal
edge status as the complement of the boundary-pair status, and inconsistent prescriptions leave at most
one vertex.  Cross-pairs of complementary one-hit types are likewise forced complete or empty.  Thus rich
spectra reduce to a bounded eight-type blow-up; the flexible terminal case is the sparse spectrum-hole
branch.
More sharply, a one-edge or two-edge boundary triple gives cap `5m+2` for a full-spectrum direction:
types `000` and `111` are singleton, the six remaining types are homogeneous, and the signed `3+1` rule
forbids the one type that completes the boundary triple to its regular residue.  An independent boundary
triple gives cap `14`: type `000` is forbidden by repaired residue `0`, all other types are cliques and
repaired residue `3` bounds them by two vertices.  A triangle gives the complementary cap `14`.

Combining the corrected spectrum-hole logic with the full-spectrum cap gives the current large-fiber
normal form.  For `|C_i|>max(R(4,4),5m+2)`, the repair spectrum has at most two residues and contains
neither complementary pair `{0,3}` nor `{1,2}`.  Hence a very large direction has spectrum contained in
one of `{0,1}`, `{0,2}`, `{3,1}`, `{3,2}`, or is a singleton.  This sparse-transversal statement replaces
the earlier false singleton-rigidity claim.
The four two-residue cases are respectively: `alpha<=3` plus `2K_2`-free; `alpha<=3` plus induced
`C_4`-free; `omega<=3` plus `2K_2`-free; and `omega<=3` plus induced-`C_4`-free.  Up to complement,
only the first two sparse hereditary branches remain, plus the augmented boundary-type constraints.
The tempting `2K_2` chromatic shortcut remains false: the join of two `C_5`'s is `2K_2`-free with
`alpha=2`, `omega=4`, and `chi=6`; the join of `k` copies has `omega=2k` and `chi=3k`.  This is now only
a caution against the obsolete route.  The exact-basis branch is capped instead by the `h=1` anchor atom,
which turns the sparse hereditary endpoints into `(2K_2,C_4)`-free pseudo-split fibers of size at most
`m+8`.  The labelled target-stability inequalities below remain useful only for near-basis or mixed-type
boundary imports where the exact-basis `h=1` atom is not directly available.
In the one-boundary-type case, target-stability becomes explicit.  Partition the retained fiber by
`A_j={theta=L+j}`.  For a same-old-vector boundary copy `z` whose adjacency to the retained type is the
constant `epsilon`, every singleton exchange importing `z` and exporting `y` gives
`epsilon=0 => |N_G(y) cap A_{-1}|<=|N_G(y) cap A_0|+1`, while
`epsilon=1 => |A_1\N_G(y)|<=|A_0\N_G(y)|+1`.  Hence a residual with both a boundary miss and a boundary
hit has labelled domination of the two adjacent off-target layers by the target layer; this is the
global information absent from the local hereditary tables.
Two-boundary-copy exchanges control the opposite layer.  If `z_1,z_2` have constant retained adjacencies
with sum `t` and `Y={y_1,y_2}` is the exported retained pair, then
`theta'(u)=theta(u)+deg_Y(u)-t`, so target-stability gives
`sum_k |{u in A_{t-k}: deg_Y(u)=k, t-k !=0}| <= sum_{k!=t}|{u in A_0:deg_Y(u)=k}|+O(1)`.
For two boundary hits this says
`|A_1 cap (N(y_1) triangle N(y_2))|+|A_2 \ (N(y_1) union N(y_2))|`
is paid for by target vertices outside the common neighbourhood of the pair; hence mass in the opposite
layer `A_2` must be nearly dominated by every retained pair.  The two-miss case is dual and controls
`A_{-2}` through common neighbourhoods.
More generally, any imported boundary subpacket `Z` of size `s<=3`, with total constant retained
adjacency `t`, and exported same-size retained set `Y` gives
`sum_k |{u in A_{t-k}: deg_Y(u)=k, t-k !=0}| <= sum_{k!=t}|{u in A_0:deg_Y(u)=k}|+O(s)`.
For model type `110`, the full boundary triple has `t=2` and controls all three off-target layers at
once.  The same-type residual must satisfy this whole singleton/pair/triple label-gradient hierarchy.
This closes the empty-target same-type degeneration.  If `A_0=empty` and the retained boundary type has
both a miss and two hits, the singleton miss makes `A_{-1}` a clique in the complement and hence size
`<=3`; the singleton hit makes `A_1` independent in the complement and hence size `<=m`; the two-hit
pair inequality forces every retained pair to dominate `A_2` in the original graph, so each vertex of
`A_2` has complement-degree at most one and `|A_2|<=m` by the induced-degree-two exclusion.  Therefore a
large one-type residual must have nonempty target layer `A_0`.
Inside `A_0`, partition further by total retained degree modulo four:
`D_q={u in A_0: deg_B(u)=q}`.  Any four-set `S subset D_q` is a pure-discard closing atom exactly when
it induces the regular four-vertex graph of degree `q-delta_B`; terminality forbids that one pattern in
that slice.  The remaining target-layer obstruction is therefore a four-coloured graph, each colour
forbidding one specified regular four-pattern, coupled to the off-target layers by the singleton and
pair target-stability inequalities.
The mixed-colour form is stronger: with `c(u)=deg_B(u)-delta_B`, no four-set `S subset A_0` may satisfy
`deg_{G[S]}(u)=c(u)` for every `u in S`.  Hence colour `3` is Ramsey-bounded, and colour `2` is
`(2K_2,C_4)`-free and therefore pseudo-split, giving size at most `2m+O(1)`.  The only target colours
that can remain large are colours `0` and `1`.  Between them, every independent pair in colour `0`
dominates all but at most three colour-`1` vertices: otherwise an edge in their common non-neighbour set
would realize degrees `(0,0,1,1)` and close by pure discard.
In complement form this is sharper.  A colour-`0` nonedge is an edge `ab` in `H`.  The colour-`1` common
neighbourhood of `ab` in `H` has size at most one: an adjacent pair gives a `K_4`, while a nonadjacent
pair gives the forbidden `(0,0,1,1)` pure-discard atom.  The remaining colour-`1` vertices split into
exclusive layers `Y_a=N_H(a)\N_H(b)`, `Y_b=N_H(b)\N_H(a)`, and zero layer `Y_0`.  The exclusive layers
are anti-complete to each other in `H`, are triangle-free and induced-`C_4`-free, and satisfy
`alpha_H(Y_a)+alpha_H(Y_b)<=m`.  Hence their bipartite part has total size at most `2m`, and their
non-bipartite odd cores have total length at most `m`; the distance-three quotient bounds their
first-core pendant fibres by `3m`.  The remaining colour-`1` mass is pushed into the zero layer plus
iterated zero-trace remainders inside the exclusive layers.
Thus the target-layer dichotomy is: colour `0` is a clique and hence `m`-bounded, leaving only the
colour-`1` zero-trace analysis; or colour `0` has a nonedge and supplies the edge-anchor decomposition,
again leaving only controlled layers plus zero-trace remainders.
The exact irreducible local core is therefore the all-target colour-`1` case: off-target layers empty,
colour `0` empty or clique-bounded, and target layer contained in colour `1`.  Then all target-stability
inequalities are vacuous and the pure-discard rule is just the retained-only `2K_2` exclusion.  In
complement language, the remaining theorem must address induced-`C_4`-free, `K_4`-free graphs with
`alpha<=m` and no induced `Delta<=2` selector larger than `11m/5`; no further finite boundary-table
case split can close this core.
Even in this core, every complement edge `ab` gives the same edge-anchor decomposition: common
neighbourhood size at most two, exclusive neighbourhoods anti-complete/triangle-free/induced-`C_4`-free,
and zero-neighbour layer `Z_ab`.  If some `Z_ab` is small, the core is linearly bounded by the controlled
exclusive-layer and pendant-fibre estimates.  Thus a superlinear core must be edge-robust: `Z_ab` is
large for every edge `ab`.
Equivalently, choose a maximal induced matching `M` in the core.  Since an induced matching with more than
`m/2` edges already gives an outside-only congruent set, `|M|<=m/2`; the vertices anti-complete to all
endpoints of `M` are independent and have size at most `m`.  Hence the core is covered by the endpoint
neighbourhoods of at most `m/2` matching edges plus an independent residual.  For each matching edge the
common neighbourhood has size at most two and the exclusive neighbourhoods have the edge-anchor
triangle-free/`C_4`-free structure.  The final charging problem is to bound the total mass in these
endpoint-exclusive neighbourhoods.
Equivalently, after assigning every non-residual vertex to one incident matching edge, the needed
endpoint-exclusive charging lemma
`sum_i(|E_i^a|+|E_i^b|)=O(m)`, where
`E_i^a subset N(a_i)\N(b_i)` and `E_i^b subset N(b_i)\N(a_i)`.  The endpoints, common neighbours, and
independent residual already contribute only `O(m)`; the layer theorem below supplies this charging and
linearly bounds the all-target colour-`1` core.
This charging lemma contains the true last selector problem: a single exclusive side can be an arbitrary
triangle-free induced-`C_4`-free layer joined to one endpoint of a matching edge and missed by the other.
The visible induced-`Delta<=2` bound is only a shadow.  In the all-target colour-`1` core, every
same-direction subset `S` with `|S|=0 [MOD 4]` is forbidden when the complement layer has
`deg_{F[S]}(s)=2 [MOD 4]` for all `s`.  Thus the irreducible standalone target is the triangle-free
induced-`C_4`-free mod-`2`-degree layer theorem: with `alpha<=m` and no nonempty size-`0 mod 4`
induced subgraph all of whose degrees are `2 mod 4`, prove linear size.  The bipartite case is `<=2m`;
the non-bipartite case is the shortest-odd-core/distance-three-pendant/zero-trace recursion.
This layer theorem is linearly closed.  In each non-bipartite zero-trace layer choose a shortest odd
cycle.  The nonzero pendant fibres over that cycle have quotient maximum degree two, hence total size at
most `3m`; the residual is the zero-trace layer.  Chosen odd cores are pairwise anti-complete.  A
nonempty subfamily with total length `0 mod 4` would be an induced all-degree-`2` subgraph of size
`0 mod 4`, forbidden by terminality; hence at most three odd cores are chosen, all with the same residue
mod `4`.  Their total length is at most `11m/5`, and the final bipartite zero layer has size at most
`2m`.  Thus `|F|<=66m/5`.
Useful structure remains inside that class.  If `abc` is a triangle in the complement `H`, trace every
outside vertex by `N_H(v) cap {a,b,c}`.  No trace has size three; incomparable nonempty traces are
anti-complete, since an edge between them and an anchor edge induce a `C_4`.  Thus two-neighbour trace
classes are independent, singleton trace classes are pairwise anti-complete, and each singleton trace
class is triangle-free and induced-`C_4`-free.  Quantitatively,
`|P_ab|+|P_ac|+|P_bc|<=m` and `alpha(S_a)+alpha(S_b)+alpha(S_c)<=m`; if the singleton layers are
bipartite they contribute at most `2m`.  After anchoring a triangle, the only unbounded pieces not
already controlled by `3m+O(1)` are the zero-trace remainder and genuinely non-bipartite triangle-free
`C_4`-free singleton layers.  Each non-bipartite singleton layer has an induced shortest odd cycle, and
these cycle cores are pairwise anti-complete across the singleton layers, so terminality caps the total
chosen odd-core length by `m`.  The triangle-anchored residual is therefore a bounded odd-core attachment
problem plus the zero-trace remainder.  In a triangle-free induced-`C_4`-free layer with shortest odd
cycle `C`, every outside vertex has at most one neighbour on `C`; two neighbours would create a shorter
odd cycle, except for distances one and two, which are excluded by triangle-freeness and induced-`C_4`
freeness.  The pendant fibres over consecutive cycle vertices are anti-complete, so the only potentially
large attachments are edges between nonadjacent pendant fibres and the iterated zero-trace remainder.
More sharply, an edge between pendant fibres over `c_i,c_j` is possible only when one cyclic distance
between `i` and `j` is exactly `3`; otherwise the edge and the two cycle arcs create a shorter odd cycle
or a forbidden triangle/`C_4`.  The pendant quotient therefore has maximum degree two and fractional
chromatic number at most `3`, so the first-core pendant fibres in one singleton layer have total size at
most `3 alpha(layer)`, and across the three singleton layers at most `3m`.
The zero-trace recursion has a bounded skeleton: choose successive edge, triangle, or shortest-odd-cycle
anchors only inside the current zero layer.  Later anchors are anti-complete to earlier anchors, so their
union is an induced graph of maximum degree at most two; terminality gives total anchor size at most
`11m/5`.  The mod-`4` layer theorem above supplies the needed pendant/trace charging across this bounded
anchor skeleton.
For the C4 branch, the augmented boundary rules give a direct shape cap: if
`{0,2} subset Rep(g_i)` and `X_i` is independent, then type `000` is forbidden and all other seven
boundary types are cliques, so `|C_i|<=7m`.  Complementarily, `{3,1}` with a triangle boundary also gives
`|C_i|<=7m`.
For the remaining `{0,2}` branch, boundary shape localizes the exceptions: with a one-edge boundary
`xy` plus isolated `z`, all types except `001` and `110` are cliques; with a path boundary `x-y-z`, all
types with equal endpoint bits are cliques and type `101` is forbidden, leaving only the four unequal
endpoint types exceptional; with a triangle boundary, pair rules are cross-type only and this remains the
hardest shape.  Complement gives the analogous `{3,1}` statements.
In that hardest triangle-boundary `{0,2}` case, the cube-type constraints are:
`10*` anti-joins `01*`, `1*0` anti-joins `0*1`, and `*10` anti-joins `*01`; each miss class has
independence number at most two; and every misser's neighbourhood in the corresponding hit class is a
clique.  This finite eight-type cube problem is the residual sparse C4 surface.
The anti-join graph is the distance-at-least-two graph on the 3-cube; its parity classes are four-cliques.
Since four pairwise anti-joined nonempty types would give an independent four-set, at least one even and
one odd type must be empty.  Thus the residual cube has support on at most six types; the remaining issue
is bounding the surviving C4-free type classes.
Moreover, every square face of the cube has anti-complete diagonals, so any alternating cycle around the
face is automatically an induced `C_4`.  Hence each nonempty face is a `C_4`-free cyclic blow-up: the four
side bipartite graphs must avoid a compatible four-edge cycle.  For example, if three side pairs of a face
are complete and all four corner types are nonempty, the fourth side pair must be empty.
The support shapes are finite: support size at most five; or support size six with adjacent omitted
even/odd types, which leaves full square faces; or support size six with antipodal omissions, in which
case the surviving type graph is the induced six-cycle of the cube.  The antipodal-omission six-cycle is
the only support shape with no full face.
Parity-count compression is stronger for size six: distinct same-parity types are pairwise anti-complete,
so if three types of one parity are nonempty then each is a clique, otherwise an independent pair in one
plus one vertex from the other two gives an independent four-set.  Hence support size six gives
`|C_i|<=6m`; support size five leaves three clique-bounded same-parity classes and only two exceptional
classes; support size at most four is the remaining small-support case.
In support size five, the two exceptional same-parity classes are anti-complete; they cannot both contain
independent pairs.  Thus one is clique-bounded, and the only possible nonlinear remnant is a single type
class with `alpha<=2`, induced-`C_4`-free, clique number at most `m`, and no outside-only congruent
subgraph larger than `m`.  Correcting the complement is decisive: the complement `H` is triangle-free
and induced-`2K_2`-free, not C4-free, and congruent degrees modulo `4` are preserved up to the shift
`|S|-1`.
Connected bipartite components of such an `H` are chain graphs, so their order is at most twice their
independence contribution.  Connected non-bipartite components are blow-ups of `C_5`: an outside vertex
of an induced `C_5` must be a false twin of a cycle vertex, and consecutive twin classes are completely
joined.  If the five class sizes are `a_1,...,a_5`, then summing the nonconsecutive-pair independence
inequalities gives `2|H_j|<=5 alpha(H_j)`.  Moreover any three consecutive classes with capacities
`A,B,C` contain a congruent-degree induced subgraph of size at least `A+B+C-3` by choosing
`x<=A,y<=B,z<=C` with `y=x+z [MOD 4]`.  Thus terminality imposes
`a_i+a_{i+1}+a_{i+2}<=m+3` for every cyclic triple.  The former one-type residual is therefore
an explicit chain/C5-blow-up structure, with global size at most `(5/2)m` and stronger local triple
constraints in non-bipartite components.  For support at most four, either a full square face triggers
the face-C4 condition or the support is a cube forest of at most four such type classes.
The support-at-most-four cube forest also compresses: at most one type of each parity can be nonlinear,
because same-parity types are anti-complete and two independent pairs would give an independent four-set.
If the two possible nonlinear types have opposite parity and Hamming distance three, the same argument
applies.  Hence any two nonlinear types must be adjacent in the cube; all other supported types are
cliques of size at most `m`.  An adjacent edge sharing a zero coordinate is already the same one-type
chain/C5 selector after complementing the whole shared-miss union, because that union has
independence at most two and is induced-`C_4`-free.  The only new adjacent-edge case is the top edge
`111`--`110` up to symmetry, where every lower-type vertex has clique neighbourhood in the all-hit type.
Thus before the final top-edge collapse, the small-support branch has only the one-type selector or this
top-edge incidence residual, plus clique-bounded spill.
The top-edge residual is not genuinely two-type: with lower type `A=110` and all-hit type `B=111`, an
independent pair in `A` forces `|B|<=3m` because the two clique neighbourhoods plus the common
non-neighbour clique cover `B`; if `A` is a clique, then `A` is `m`-bounded and only the all-hit one-type
branch remains.  The all-hit branch is linearly capped after complementing by Wagon's bound
`chi<=binom(omega+1,2)` for `2K_2`-free graphs: here `omega<=3` and `alpha<=m`, so it has size at most
`6m`.  Therefore small cube-forest support reduces entirely to the one-type chain/C5 selector plus
clique-bounded spill.
The only support shape with three clique spill classes is a cube star with the nonlinear type as centre
and three same-parity clique leaves.  For every independent pair in the centre, common non-neighbours can
occur in at most one leaf; two leaves with common non-neighbours would give an independent four-set.
Thus every independent centre-pair two-covers at least two leaves by clique neighbourhoods.  This
pair-covering constraint is extra slack, and the crude star bound is already enough for the finite cube
cap.  Support six is at most `6m`; support five is at most `4m+(5/2)m=13m/2`; support at most four is at
most `3m+(5/2)m=11m/2`, with the top-edge subcase capped by `6m`.  Hence every triangle-boundary
`{0,2}` direction, and by complement every `{3,1}` direction, is bounded by `7m+O(1)`.  The remaining
large hereditary surface is the corrected `{0,1}`/`{3,2}` complement selector: induced-`C_4`-free,
`K_4`-free, independence at most `m`, and no induced degree-two regular selector larger than `m`.

The retained-only subcase is the old four-copy obstruction: if `C_i` is a full direction fiber in the
exact basis model, any four vertices of `C_i` are old-balanced.  A four-set closes exactly when it
induces the required `d_i`-regular graph, where
`d_i=r-omega(g_i)`.  Thus the exact basis obstruction is the finite condition that each direction
fiber avoids one specified induced regular graph on four vertices.  This condition alone is not
contradictory; it must be combined with global maximality or with a perturbation/import out of the
exact basis model.

Unions of direction blocks can still close through cross-edges.  For a four-vertex block
`S_i subset C_i`, set `a_i(s)=r-omega(g_i)-deg_{S_i}(s)`.  A union `S=union_i S_i` of such
old-balanced blocks closes iff

```text
sum_{j != i} deg_{S_j}(s)=a_i(s)        for every s in S_i.
```

So the exact basis branch is an interacting four-block correction problem: force one regular block, or
force several nonregular blocks whose cross-degrees supply the missing pointwise defects.

An atom-only exact-basis proof would be false.  If every direction has required residue `d_i=0`, every
direction fiber is a clique, and there are no cross-edges between directions, then any old-balanced
selection takes a multiple of four vertices from each direction and each selected vertex sees
`-1 mod 4`, not `0`, inside its direction block.  Thus the finite atom catalogue needs extra global
information; it cannot close the theorem by itself.
The large version of this toy model is excluded by outside-only maximality: four vertices from each of
`t` clique directions form an outside-only congruent set of residue `3`, so `4t<=m` in a terminal
counterexample.  The retained-only exact-basis branch must therefore avoid both append exits (defects
repaired relative to `W`) and outside-only exits (selected blocks with constant total internal row-sum
residue and total size larger than `m`).
Every large direction still supplies wrong-residue regular four-blocks: if it avoids append residue
`d_i`, Ramsey gives a clique block, independent block, or both, of residue different from `d_i` once the
fiber has size at least `R(4,4)`.  Hence the retained-only obstruction is not a lack of regular blocks;
it is a dual-exit bounded-block selector problem in which wrong-residue blocks must neither repair to
the append residue through cross-edges nor synchronize to a large outside-only residue.

Compressing four-blocks to supervertices recovers the same kind of row-sum selector: each block carries
a four-coordinate defect vector, and each pair of blocks contributes a `4 by 4` cross-adjacency matrix.
Selecting blocks asks for selected cross-matrix row sums to equal the defect vectors.  So the exact
basis reduction only helps if the boundary-triple origin or the maximum-witness hypothesis is used; as
an abstract bounded-block problem it merely repackages the self-layer obstruction.

Use also the outside-only maximum constraint: because `W` is cardinal-maximum, no subset of `C` alone
can have congruent induced degrees modulo `4` on more than `m` vertices.  For regular direction blocks
`P_i` with internal residues `q_i`, this forbids any block family of total size `>m` satisfying
`q_i+sum_{j != i}deg_{P_j}(v)=Q` on every selected block.  This rules out local atom-only models such as
many no-cross clique directions: four vertices from each of more than `m/4` clique directions would
already form an outside-only residue-`3` witness.  Terminal exact-basis configurations must block both
appendable repairs and outside-only block selections.

This block obstruction amplifies with the block size.  For any fixed `L == 0 [MOD 4]`, a direction
fiber of size at least `R(L,L)` that avoids its append residue contains an `L`-vertex regular block of
wrong residue `q_i in {0,3}`.  The same append and outside-only equations hold with four replaced by
`L`; only the outside-only surplus condition changes to `sum |P_i|>m`.  Hence a no-cross same-residue
family of such blocks has size at most `m/L`, and any block-level selector is amplified by `L`.
The obstruction that remains after this amplification is the sparse-import regime: the retained mass may
be distributed as one or a few imports in many directions, where the only old-balanced local block is
`X_i union {b}` of size four.  That regime cannot be closed by a finite same-direction Ramsey catalogue;
it must use the boundary triples themselves through outside-only maximality or through explicit
coordinate exchanges.

Equivalently, the sparse endpoint is a finite-alphabet row-sum problem.  For each direction set
`A_i=X_i union C_i` and allow a word `P_i subset A_i`.  The outside-only exit is exactly a word family
with `q_i(P_i,v)+sum_{j != i}deg_{P_j}(v)=Q` for every selected `v in P_i` and total size `>m`; the
append/import exit adds the old-coordinate condition `|P_i|=0 [MOD 4]` directionwise and asks for the
append residue relative to `W`.  Thus after the heavy retained reservoirs are amplified away, the
remaining theorem is a high-density decorated-boundary selector, not another local four-block catalogue.

The boundary `X` alone carries the same constraint at the critical density: since `|X|<=3(m-1)`, a
terminal `X` has no mod-`4` congruent induced subset of size `>m`.  In the exact basis model this forbids
any selection of subpatterns `P_i subset X_i` from the boundary triples with
`q_i(v)+sum_{j != i}deg_{P_j}(v)=Q` on all selected vertices and total size `>m`.  Thus large
cross-isolated collections of independent triples or triangle triples are impossible, because the whole
triples would already give an outside-only congruent witness.
In fact any cross-isolated family of more than `2m/3` boundary triples is impossible.  If `a` of its
`t` triples are triangles and `3a>m`, take all triangle triples for residue `2`; otherwise choose a
nonedge pair from every non-triangle triple and one vertex from every triangle triple.  This gives
residue `0` and size `2(t-a)+a >= 2t-m/3>m`.  Thus one-edge and path triples are also harmless in the
cross-isolated toy model; they contribute nonedge pairs.
By complementing the induced graph on such a family, the same `2m/3` cap excludes cross-complete
families: congruent degrees in the complement translate back by
`deg_G[S](v)=|S|-1-deg_{\bar G[S]}(v)`.  Therefore any surviving sparse boundary obstruction must have
mixed cross-interactions on every supercritical subfamily of coordinate triples.
For a homogeneous but nonconstant cross-interaction on non-triangle triples, pass to the quotient graph
`Q` whose edges are cross-complete triple pairs.  A nonedge pair from each triple in an even induced
subgraph `Q[U]` gives an outside-only residue-`0` set of size `2|U|`.  Thus terminality forces
`even_selector(Q)<=m/2`, so Gallai is tight near the critical density.  Moreover, if
`2|U|>=m-1`, any outside non-triangle triple that is cross-empty to all of `U` augments the selector,
and any outside non-triangle triple cross-complete to all of `U` augments it when `|U|` is odd.  The
surviving homogeneous quotient must therefore have mixed neighbourhoods into every near-half even class.
The pair-word statement only needs constant quotient degree parity.  A two-vertex regular word of
internal residue `q_pair` gives final residue `q_pair+2 deg_Q(i) [MOD 4]`; odd quotient degree merely
shifts the common residue by `2`.  Thus non-triangle triples use nonedge pairs with `q_pair=0`, triangle
triples use edge pairs with `q_pair=1`, and a mixed homogeneous quotient can survive only by balancing
these two pair-residue classes so that neither has a near-half constant-parity selector.
Gallai gives such a selector of size at least `2 ceil(n/2)` from a same-residue homogeneous class of
`n` triples.  Since exact Davenport has at most `m-1` directions, the only near-boundary deficits are
`m even, n=m-1` (selector size `m`) and `m odd, n=m-1` (selector size `m-1`).  The remaining
same-residue homogeneous obstruction is therefore a one- or two-word augmentation failure, not a large
pair-selector failure.
For a one-word augmentation of a constant-parity pair selector `U` with residue `R`, an outside regular
word `P_j` of size `s` and internal residue `q_j` must have uniform quotient neighbourhood into `U`.
Writing `a=0` for cross-empty and `a=1` for cross-complete, the exact condition is
`q_j+2a|U|=R+as [MOD 4]`.  If `m` is even this one-word test already handles the size-`m` boundary
selector; if `m` is odd and the pair selector has size `m-1`, the only remaining augmentation check uses
two outside words whose weighted neighbourhood columns sum constantly on `U`.
The exact one-word condition is `deg_P(x)=K` on the base selector and
`deg_P(u)+deg_S(u)=R+K` on the new word `P`; internal nonregularity is allowed if the degree into the
base compensates it.  Similarly, two words `P,Q` satisfy
`deg_P(x)+deg_Q(x)=K` on the base and
`deg_P(u)+deg_Q(u)+deg_S(u)=R+K` on the new vertices.  The scalar formulas below are the regular-word
homogeneous-cross subcase.
Inside a single outside exact-basis direction `A_j=X_j union C_j`, the resulting catalogue is bounded:
subsets of the boundary triple and at most one or two retained vertices are governed by the same
`3+1`, `2+2`, and `1+3` equations as append atoms, with the append residue replaced by `R+K` and with
the added base-column term.  Thus the equality residual is a finite augmented-fiber pattern check once
the base pair selector is fixed.
For two words `j,k`, the exact equations are
`s_j a_j(i)+s_k a_k(i)=K` on `U`,
`q_j+2 sum_U a_j+b s_k=R+K`, and
`q_k+2 sum_U a_k+b s_j=R+K [MOD 4]`.  In the deficit-two singleton case this is just a two-column
condition: the columns are complementary, both constantly zero, or both constantly one; nonconstant
equal columns do not have constant row sum.
Retained vertices are also outside words.  A retained singleton augments a pair-word boundary selector
only if it is pair-uniform on all chosen boundary pairs; with common bit `a` the one-word condition is
`2a|U|=R+a [MOD 4]`.  Two retained singletons augment exactly when their pair-uniformity columns are
complementary or both constant and satisfy the same two-word congruences with `q_j=q_k=0`.  Thus the exact
boundary equality case is coupled to retained trace columns rather than being boundary-only.
The retained table is explicit: one retained vertex closes if it misses all selected pair vertices and
`R=0`, or hits all of them and `R=2|U|-1`.  For two retained vertices with mutual edge `b`, both-zero
columns require `b=R`, both-one columns require `2|U|+b=R+2`, and complementary columns require `|U|`
even plus `2alpha+b=R+1`, where `alpha` is the number of pairs hit by the first retained vertex.
Hence the all-zero column class is empty when `R=0` and independent when `R=1`; the all-one class uses
the shifted residue `R+2-2|U|`; complementary columns must avoid the specified edge status whenever it
is `0` or `1`.  The equality residual is now a finite column-hole problem.
For non-pair-uniform retained vertices use the full bit-column equation.  Two retained singletons
`z,z'` augment iff for every selected boundary pair `{x_i,y_i}` there is a common `K in {0,1,2}` with
`zx_i+z'x_i=zy_i+z'y_i=K`, and also
`deg_U(z)+b=deg_U(z')+b=R+K [MOD 4]`.  Thus the only nonuniform possibility is bitwise complementary
columns on every selected boundary vertex, with the total-degree congruences fixed.
Equivalently, with retained traces `t_z(i)=(zx_i,zy_i)`, any augmenting pair satisfies
`t_z(i)+t_z'(i)=(K,K)` for every selected pair.  Non-pair-uniform traces therefore force the affine
complement trace, leaving only the displayed total-degree congruence and the mutual edge `b`.
Pair-only selectors cannot mix these classes: size-two words contribute only even cross-degrees, so the
parity of the final residue is the parity of the internal pair residue.  Any genuine mixed-class
selector must therefore use singleton or whole-triple words, the odd-size words that can change
cross-contribution parity.
The odd-word part has an exact linear carry equation.  On a quotient parity class `U`, choose singletons
everywhere and whole triples on `T` among independent/triangle triples.  With `tau_i=0` for independent
and `tau_i=1` for triangle, congruence modulo `4` is equivalent to
`floor(deg_{Q[U]}(i)/2)+deg_T(i)+tau_i 1_{i in T}=c [MOD 2]` for all `i in U`.  The selector has size
`|U|+2|T|`; terminality forces every solution to have size at most `m`.  Thus the last homogeneous
mixed-class obstruction is a low-weight affine solution space over `F_2`.
Writing `M_U=A(Q[U])+diag(tau)`, any kernel vector toggles one solution to another, so if a solution
exists terminality forces every `H in ker M_U` to have `|H|<=m-|U|`.  A large twisted-Eulerian kernel
vector closes the branch.  If no constant bit makes the affine system soluble, symmetry gives a dual
kernel certificate incompatible with the carry right-hand side.  The irreducible endpoint is therefore
small-kernel plus affine-inconsistency for this twisted quotient matrix.
In a soluble terminal branch this is a genuine compression: if `J=union_{H in ker M_U} supp(H)`,
averaging over the kernel gives `|J|/2<=m-|U|`, hence `|J|<=2(m-|U|)`.  Outside `J`, every soluble
affine branch has fixed bits; the fixed-one set outside `J` has size at most `(m-|U|)/2`.
Moreover the insoluble branch is exactly an even-kernel Arf certificate.  With
`r_i=floor(deg_{Q[U]}(i)/2)`, the system is `M_U 1_T=r+c1_U`; some `c` is soluble unless there is an
even-weight `H in ker M_U` with `sum_{i in H} r_i=1 [MOD 2]`.  Such an `H` blocks both constants; it is
the remaining insoluble certificate rather than a solution-weight consequence.
Unpacked, this certificate is parity-closed:
`deg_H(i)=0` for `i outside H`, `deg_H(i)=tau_i` for `i in H`, `|H|` is even, and
`sum_{i in H} floor(deg_U(i)/2)=1 [MOD 2]`.  A proper `H` localizes the obstruction to a smaller closed
mixed quotient; `H=U` is the one-bit whole-class Arf obstruction.
In a minimal whole-class Arf obstruction, the even kernel is exactly `{0,1_U}`.
Otherwise an even kernel vector `K` with zero Arf pairing makes `U Delta K` a proper bad support, while
an even `K` with odd pairing is already a proper bad support.  Hence `|U|` is even,
`1_U in ker M_U`, `sum_U r_i=1`, and `dim ker M_U<=2`: two distinct odd kernel vectors differ by the
unique nonzero even kernel vector `1_U`.  Equivalently the quotient is parity-matched,
`deg_U(i)=tau_i [MOD 2]`, and the single remaining bit is
`e(Q[U])-(1/2)|{i:tau_i=1}|=1 [MOD 2]`.  Thus the insoluble mixed-word endpoint has rank at most two
after closed-support localization; larger kernels are reducible, not terminal atoms.
It also has no twisted twins: for `|U|>2`, two equal columns of `M_U` would give the forbidden even
kernel vector `e_i+e_j`.
In the parity-matched constant-type case, `tau` is constant and `deg_Q(i)=tau [MOD 2]`, so `1_U` lies
in the kernel.  If `|U|` is odd, the constant bit `c` can always satisfy the single all-ones
compatibility equation.  But the full selector already closes any constant-type constant-parity quotient
set with `|U|>m/2` by pair words, so the Arf-type half-degree bit is only a below-threshold diagnostic,
not an independent large obstruction.

The zero-sum-free boundary `X` has length at most the Davenport extremal value `3(m-1)` in
`C_4^(m-1)`.  This suggests the next split:

1. If `X` is not close to extremal, the retained side `B=C\X` has extra mass for the
   block-interaction route.
2. If `X` is close to extremal, an inverse-Davenport theorem for `C_4^(m-1)` should force a
   basis-like boundary, roughly three copies of independent order-`4` directions, and the allowed
   imports from `X` become explicit coordinate exchanges.

At the exact top layer this is rigid by Olson's extremal theorem for finite abelian `p`-groups:
if `|X|=3r` in `C_4^r`, then after a basis change
`X=e_1^3 e_2^3 ... e_r^3`.  A boundary import is then just a coordinate count vector
`0<=a_i<=3`; exporting old-sum `sum_i a_i e_i` forces exactly `a_i` imported copies from the `i`-th
parallel triple.  The only residual freedom is which parallel graph traces of each coordinate are used.
Equivalently, with `h_X(sum_i a_i e_i)=sum_i a_i`, deleting `Y subset B` and importing from `X` gives
size `|B|-|Y|+h_X(sigma(Y))`.  Terminality therefore forces every graph-label-compatible export to obey
`|Y|-h_X(sigma(Y))>=|B|-m`; otherwise the forced coordinate import already leaves more than `m` selected
vertices.  At the exact top, the boundary exchange is a finite trace search with this linear surplus
weight, not a hidden zero-sum choice.
In deficit form, if `d=m-|B|>=0`, terminality says every compatible export has
`h_X(sigma(Y))-|Y|<=d`; all larger boundary-height gains would close immediately.
The gain has the carry identity
`h_X(sigma(Y))-|Y|=sum_{y in Y}(h_X(sigma(y))-1)-4 sum_i floor(n_i(Y)/4)`, where
`n_i(Y)` is the total exported coefficient in coordinate `i`.  Thus terminality is the finite inequality
`sum_y(h_X(sigma(y))-1)<=d+4kappa(Y)` for every graph-compatible export.  Carry-free exports
(`n_i<=3` in every coordinate) have singleton surplus at most `d`; in particular a compatible singleton
has height at most `d+1`, and at deficit zero two positive-surplus vertices cannot form a compatible
carry-free pair.
Complementary cuts inside old-balanced retained blocks add another restriction.  If `sigma(S)=0`,
`Y` is a proper cut, and both exports `Y` and `S\Y` are graph-compatible, then with `g=sigma(Y)` the
identity `h_X(g)+h_X(-g)=4 supp(g)` and the two terminal inequalities give
`4 supp(g)<=|S|+2d`.  Hence deficit-zero two-sided-compatible cuts in blocks of size below four are
impossible, and four-block cuts must be supported on one boundary coordinate.
If a deficit-zero minimal four-block has all singleton and pair cuts two-sided-compatible, it is forced
into the positive one-coordinate atom `e_i^4`: singleton cuts have height at most one, hence value `e_i`,
and pair cuts forbid two different coordinates.  The negative atom `(-e_i)^4` is excluded because a
compatible singleton export would import three boundary copies and gain two vertices.  The positive atom
has zero boundary-height gain on every cut; any obstruction it leaves is self-layer residue, not
coordinate arithmetic.
For a positive atom, combine the retained four-set `S_i=e_i^4` with the boundary triple `X_i=e_i^3`.
Every size-preserving old-coordinate reroot is a four-set `T subset R_i=S_i union X_i`, `|R_i|=7`.
With `A` the fixed selected remainder, the full reroot test is:
`M_A(a)+deg_T(a)=R` on `A` and `L_A(v)+deg_T(v)=R` on `T`.  Equivalently, for the omitted triple
`O=R_i\T`, replace `deg_T` by `deg_{R_i}-deg_O`.  Hence the final positive-atom residue is a labelled
seven-vertex omission table coupled to one constant-column condition on the fixed remainder, not a
group-theoretic boundary problem.
The column condition depends only on the trace quotient of `A` into `R_i`: for
`p(a)=N(a) cap R_i` and `mu(a)=M_A(a)+|p(a)|`, an omitted triple `O` works on the remainder iff
`mu(a)-|p(a) cap O|` is constant on all occupied labelled trace classes.  Therefore the positive-atom
endpoint is a finite alphabet problem on `{0,1}^7 x Z/4Z` plus the internal four-set equation on
`R_i\O`.
Equivalently, if each occupied trace `p` has a single label `mu(p)`, the external candidates are the
omitted triples `O` for which `mu(p)-|p cap O|` is constant on the occupied trace set.  If a trace carries
two labels, there is no external candidate.  Thus the positive atom is the intersection problem
`C_ext cap C_int` inside the `35` omitted triples: `C_ext` is a trace-template set, and `C_int` is the
internal four-set set.
If the empty trace and singleton traces are occupied, the external candidates decode directly:
`R=mu(empty)` and `1_{r in O}=mu({r})-mu(empty)`.  Any singleton difference outside `{0,1}` kills
`C_ext`; if all seven singletons are present, `C_ext` has at most one triple, existing only when exactly
three differences are `1` and all higher occupied traces obey the same count formula.
The dual decoder uses the full trace and co-singletons:
`1_{r in O}=mu(R_i)-mu(R_i\{r})`.  Thus full trace plus all seven co-singletons also leaves at most one
external candidate.
More generally, if two distinct omitted triples `O,O'` both survive externally, then every occupied trace
has constant imbalance `|p cap (O\O')|-|p cap (O'\O)| [MOD 4]`.  If the empty or full trace is occupied,
the constant is zero, so every occupied trace must be balanced across the symmetric difference.  External
ambiguity is therefore possible only on trace families that do not separate surviving templates.
Anchored by the empty or full trace, this becomes exact: `C_ext` is contained in one equivalence class of
triples under the map `O -> (|p cap O|)_p`.  If occupied traces separate all triples, then
`|C_ext|<=1`.
Adjacent surviving triples force a trace-twin pair: if the triples differ by swapping `x` and `y`, then
every occupied trace contains either both or neither of `x,y`.  Thus with no trace-twin points, anchored
`C_ext` is independent in the Johnson graph `J(7,3)`.
Hence, after quotienting trace twins, anchored external ambiguity is a triple packing: no two surviving
triples share a pair, so `|C_ext|<=7`, with equality only in the Fano `2-(7,3,1)` system.
For two trace classes `(p,mu),(q,nu)`, equalization is the signed three-subset equation
`|p cap O|-|q cap O|=mu-nu [MOD 4]`.  With `A=p\q`, `B=q\p`, this means choosing
`x` omitted points from `A` and `y` from `B`, with a total omitted size three, so that
`x-y=mu-nu [MOD 4]`.  The positive-atom obstruction is a finite anti-Horn family of these pair
constraints with no common omitted triple among the `35` triples.
Equivalently define
`D_3(a,b)={x-y [MOD 4]:0<=x<=a,0<=y<=b,0<=3-x-y<=7-a-b}`.  A trace pair blocks exactly when
`mu-nu notin D_3(|p\q|,|q\p|)`.  Hence identical traces with different `mu` block, complementary traces
with even `mu-nu` block, and the remaining pairwise failures are just the small private-size entries of
this `D_3` table.
The non-full `D_3` entries are only
`(0,0),(0,1),(0,2),(0,5),(0,6),(0,7),(1,1),(1,6),(2,5),(3,4)` up to swapping and negating residues;
all other `a+b<=7` entries are full.
The internal four-set line is identical after conditioning on the kept pair.  With
`lambda(v)=L_A(v)+deg_{R_i}(v)`, kept vertices `u,v notin O` require
`deg_O(u)-deg_O(v)=lambda(u)-lambda(v)`.  Since `O` avoids `u,v`, the allowable residues are
`E_3(a,b)={x-y:0<=x<=a,0<=y<=b,0<=3-x-y<=5-a-b} [MOD 4]`, using private neighbourhood sizes inside
`R_i\{u,v}`.  Thus external trace pairs use `D_3` and internal kept pairs use `E_3`; both are anti-Horn
constraints on the same omitted triple.
The non-full `E_3` entries are only
`(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3)` up to the same symmetry.
There is also an internal blocker graph `J_int` on `R_i`: join `u,v` when
`lambda(u)-lambda(v) notin E_3(a_{uv},b_{uv})`.  Any successful omitted triple must cover every edge of
`J_int`; therefore `tau(J_int)<=3` is necessary.  If the vertex-cover number is at least four, the
positive atom has no self-layer reroot before external traces are considered.
Equivalently, the kept four-set `T=R_i\O` must be an independent four-set of `J_int`; after choosing such
a `T`, the remaining signed `E_3` equations are checked on the six pairs of `T` and the external `D_3`
constraints on `O`.
So `C_int` is contained in the 3-vertex-cover family `K_3(J_int)`.  If this family is empty the atom is
internally dead; if it is a singleton, the whole reroot question reduces to one external template and the
six internal equalities.  A common core in all 3-covers similarly partially decodes the omitted triple.
Thus terminal positive atoms have four finite certificate types: `C_ext=empty`, `C_int=empty`, decoded
singleton mismatch, or a genuine ambiguous core where external traces fail to separate triples and
internal 3-covers are non-unique after all signed checks.
After quotienting trace twins and excluding decoded cases, the ambiguous core is simply
`C_ext=P`, a triple packing, and `C_int subset K_3(J_int)`, with `P cap C_int=empty`.  In the extremal
case `P` is Fano, so terminality says every Fano line is killed internally by the blocker graph or a
signed `E_3` equation.
Moreover a fixed kept pair is disjoint from at most two triples of a packing on seven points.  Hence
killing an external packing `P` internally requires at least `ceil(|P|/2)` distinct kept-pair witnesses;
Fano ambiguity needs at least four.
More exactly, use the intersection graph `Gamma(P)` of the packing.  A kept pair kills two packing
triples precisely when they are adjacent in `Gamma(P)`, and is then uniquely the complement of their
union.  Thus the incidence lower bound is `|P|-nu(Gamma(P))`.
Minimum covers are a maximum matching in `Gamma(P)` plus one bad pair in the complement-four of each
unmatched triple.  If `|P|=6`, the leave has even degrees and three edges, hence is a triangle; adding it
completes `P` to the Fano plane.  So a six-packing has `Gamma(P)=K_6` and minimum terminal core three
forced complement-pair witnesses.
Generally the leave graph has `21-3|P|` edges and even degrees `6-2d_P(x)`.  For `|P|=5`, it is therefore
a six-cycle or two edge-disjoint triangles, so the five-template core has only these leave types.
Anchored large packings rigidify traces: full Fano ambiguity allows only empty/full occupied traces by
`3|p|=7t`, while a six-packing `F\{L_0}` allows only
`empty, L_0, R_i\L_0, R_i`.
Thus full and near-Fano anchored ambiguity force trace twins; after trace-twin quotienting, irreducible
anchored packings have size at most five.
In that post-quotient anchored range the witness lower bounds are explicit:
`|P|=5` needs at least `3`, `|P|=4` at least `2`, `|P|=3` at least `2`, and two disjoint templates need
two.
The six-cycle leave five-packing has only empty/full anchored balanced traces, so it also forces trace
twins.  Thus the irreducible anchored five-template case has the two-triangle leave type.
The two-triangle leave also forces twins: disjoint triangles cannot occur, and the shared-point block
systems have adjacent/opposite assignments whose balanced trace equations force equal coordinates.
Therefore the trace-twin-free anchored external packing has size at most four.
At size four, the degree-pattern count leaves only three shapes.  The tetrahedral `(0,6,0,1)` shape and
the one-disjoint-pair `(0,5,2,0)` shape force trace twins.  The unique trace-twin-free size-four normal
form is `(1,3,3,0)`: one base triple `U={u_1,u_2,u_3}` and three triples `{a,u_i,v_i}`.
Its balanced traces are `empty`, full, `{u_i,v_j,v_k}` and their complements.  Since
`Gamma(P)=K_4`, minimum terminality needs two witnesses, necessarily one of
`{u_i v_i, v_j v_k}`.
For `|P|=3`, `Gamma(P)` is `P_3` or `K_3`, and a minimum core is one forced complement pair for a
matched edge plus one bad pair in the unmatched triple's complement-four.  For `|P|=2`, adjacent
templates have one forced witness and disjoint templates need two.
The three-template geometries are just path, centered `K_3`, and triangular `K_3`:
`{a,x_1,x_2},{a,b,c},{b,y_1,y_2}`; three triples sharing `a`; or
`{a,b,x},{a,c,y},{b,c,z}`.
Unanchored ambiguity is handled by choosing an occupied reference trace `p_0` and using relative columns
`1_p-1_{p_0}`.  Adjacent templates force equal relative columns, so after relative-twin quotienting the
candidate set is again a packing.  Full Fano relative equations force all traces equal by nonsingularity
of the Fano incidence matrix; six-line near-Fano equations have nullspace
`<-2 1_{L_0}+1_{R_i\L_0}>`, which has no nonzero `{ -1,0,1 }` multiple.
For `P` Fano, the exact graph shadow is that the internal witness graph is not covered by any Fano line;
all three-edge witness graphs are line-covered.
Equivalently, dualize to the seven Fano lines: each kept-pair witness joins the two lines disjoint from
it, and terminality is exactly that this dual graph has no isolated vertex.  A four-witness terminal core
has dual cover `P_3 disjoint union 2K_2`.
Inclusion-minimal dual covers are star forests: `K_{1,2}+2K_2` with four witnesses,
`K_{1,4}+K_2` or `K_{1,3}+K_{1,2}` with five, and `K_{1,6}` with six.  The six-star is primal `K_4` on
the complement of one Fano line.
More generally a dual star centered at line `L` is a cluster of primal bad pairs inside `R_i\L`; the leaf
line selects the unique pair outside both lines.
For a non-exact boundary, replace `h_X` by the maximum available import height
`H_X(g)=max{|Z|:Z subset X, sigma(Z)=g}`.  Terminality forces
`H_X(sigma(Y))-|Y|<=m-|B|` for every graph-compatible export.  The exact top is just the case
`H_X=h_X`; near-top inverse Davenport input is needed only to give useful lower bounds on `H_X`.
If stability places `X` in a coordinate subbox with capacities `c_i<=3`, then
`H_X(sum a_i e_i)=sum a_i` exactly when `a_i<=c_i` for all `i`, and is unavailable otherwise.  Holes
therefore delete residues rather than contributing a uniform `rho` height loss.  On available values the
exact-top inequalities hold with the original deficit `d`; unavailable values are already
boundary-incompatible.
Two-sided availability is coordinatewise tiny: capacity `3` allows coefficients `{1,2,3}`, capacity `2`
allows only the self-opposite coefficient `2`, and capacity at most `1` allows no nonzero coefficient.
Therefore the four-block coordinate collapse survives on two-sided available cuts for `d<=1`: singleton
and pair cuts force one-coordinate support, the singleton height bound leaves coefficients in `{1,2}`,
and minimality plus total sum zero forces the positive atom `e_i^4` on a full-capacity coordinate.

So the remaining input is an inverse/stability theorem for value-coupled zero-sum-free boundaries,
not another ordinary zero-sum extraction.

Equivalently, decompose `B` into minimal old-balanced blocks.  A minimal block `S` has no proper
old-balanced subblock, and it exits by pure discard exactly when

```text
theta_X(s)+deg_{B\S}(s)-delta_{B\S} == H-r       for all s in S.
```

If every minimal block fails, then any repair must import a nonempty subset of the zero-sum-free
boundary `X` and export an old-coordinate-equivalent subset of `B`.  This is the exchange-basis form
of the terminal problem.

The same endpoint has a useful one-large-class coloring normal form.  In a labelled graph
`(H,alpha)`, a random four-coloring has the following property: for each vertex, the congruence

```text
gamma(v) == alpha(v)+deg_{H \ gamma^{-1}(gamma(v))}(v) [MOD 4]
```

holds with probability exactly `1/4` by cyclically shifting all colors in the closed neighbourhood of
`v`.  Therefore some color has at least `|H|/16` pre-satisfied vertices.  If the same-color unsatisfied
vertices have constant degree into that pre-satisfied fiber, the fiber is already a valid output.  The
remaining obstruction is exactly the nonconstant same-color contamination term, i.e. the final
self-layer again.  This is weaker than the false full fixed-point coloring theorem but strong enough
to expose the only missing cleanup lemma.

The Eulerian-orientation reformulation is exact but still diagonal.  If `J` is even and Eulerianly
oriented, then for any `S` with `J[S]` even,

```text
deg_{J[S]}(v)/2 == out_S(v) == in_S(v)        [MOD 2].
```

So a mod-`4` congruent induced subgraph is the same as a large diagonal set whose inherited in- and
out-degrees are constant modulo `2`.  In the bipartite double-cover the two sides must be the same
vertex set; ordinary bipartite parity selectors do not enforce that diagonal condition.

The current internal attack is the exposed-layer refinement diagnostic.  Once a discarded layer has been
exposed and the retained set is refined by degree into that layer modulo `4`, its contribution remains
constant forever.  The desired constant would follow if the final self-layer contribution could be
synchronized without another factor; this is exactly the missing terminal self-layer lemma.  A bipartite
residue theorem can repair only a chamber whose retained side has no uncontrolled internal edges, so the
current self-layer must first be converted into such a chamber or handled by a genuinely self-layer
co-cut argument.  Iterating the exposed-layer refinement further does not solve this: each new step
only synchronizes the previous chamber on a smaller future set, and the output still has a fresh
unsynchronized layer just outside it.

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
