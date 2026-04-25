# Formalization handoff: saturated proof route

## Current formalization status

The last checked build was green before the newest handoff sharpening; the current dirty tree should
be rebuilt before merging. The conjecture is not yet proved unconditionally in Lean, but the
saturated proof route is wired to `TargetStatement`.

The public final handoff endpoint is:

```lean
targetStatement_of_proofMdFinalHandoff
```

Apart from the implicit terminal budget `D`, it has exactly three named inputs:

```lean
sevenVertexBooleanCertificate :
  ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true

largeGapDyadicWindow :
  HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7

droppedTailConcreteFRSatTerminalFields :
  Q64ProofMdDroppedTailConcreteFRSatTerminalFields (D + 1)
```

Current Lean now proves that the terminal field above is uninhabited for every terminal budget
`D + 1`.  The obstruction is the formal `q = 8` terminal-host counterexample in
`RegularInducedSubgraph.Modular.Asymptotic`: it lifts to a one-block bounded terminal host, is
monotone in the block budget, and has no regular induced 8-set.  Consequently the present public
handoff certificate is a useful compatibility wrapper, but it cannot be instantiated as stated.
The same obstruction also refutes the all-dyadic bounded-host terminal-regularization package and
the bounded-host positive-dyadic terminal cascade/external-block self-bridge packages at every
nonzero budget, because any of these packages would immediately produce the same impossible regular
8-set.
It also refutes the exact-card single-control terminal-regularization shortcut and its zero-cost
single-control-host polynomial form, so those older shortcuts are diagnostic only, not viable
assumptions.

The Lean-checked replacement handoff is:

```lean
targetStatement_of_proofMdFinalHandoff_of_fixedWitnessTerminalRegularization
```

It keeps the seven-vertex Boolean certificate and large-gap dyadic residual, but replaces the
refuted arbitrary bounded-host terminal field by:

```lean
terminalRegularization :
  HasPolynomialCostFixedWitnessTerminalRegularization D
```

This is the honest Lemma 10.2 landing surface: a large fixed-modulus witness is regularized after
choosing the terminal host with the saturated-minimal provenance required by `proof.md`.

The sharper terminal-facing wrapper is now:

```lean
targetStatement_of_proofMdFinalHandoff_of_fixedWitnessExternalBlockSelfBridge
```

It pushes the terminal task to the fixed-witness external-block frontier:

```lean
fixedWitnessExternalBlockSelfBridge :
  HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D
```

Existing Lean reductions turn that external-block self-bridge into
`HasPolynomialCostFixedWitnessTerminalRegularization D`.  This is the terminal side to work on in
parallel with dyadic: produce the nonempty separated external-block data from the top host of a large
fixed-modulus witness, not a blanket regularization/external-block theorem for arbitrary bounded
terminal hosts.

The current strictest dyadic public endpoint is:

```lean
targetStatement_of_proofMdFinalHandoff_of_twiceLargeGap
```

which replaces `largeGapDyadicWindow` by the smaller residual:

```lean
twiceLargeGapDyadicWindow :
  HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGap 7
```

There is also a named-field certificate:

```lean
ProofMdFinalTwiceLargeGapHandoffCertificate
```

The dyadic frontier is now split one step further by:

```lean
targetStatement_of_proofMdFinalHandoff_of_parityToModFourLoss64_and_twiceLargeGapJAtLeastTwoFromTen
```

This replaces the single strict dyadic input by:

```lean
parityToModFourLoss64Lift :
  HasParityToModFourLoss64FixedWitnessLift

twiceLargeGapJAtLeastTwoFromTen :
  HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo 10
```

The first input removes every `j = 1` case with exactly the loss needed by the `C = 6` input size.
The second input starts the strict higher-bit residual at `m = 10`; the first live higher-bit case is
`m = 10, j = 2`.

The sharper current handoff isolates that first higher-bit case too:

```lean
targetStatement_of_proofMdFinalHandoff_of_parityToModFourLoss64_and_fourToEightTargetTen_and_twiceLargeGapJAtLeastTwoFromEleven
```

Its dyadic inputs are:

```lean
parityToModFourLoss64Lift :
  HasParityToModFourLoss64FixedWitnessLift

fourToEightTargetTen :
  HasFourToEightTargetTenFixedWitnessLift

twiceLargeGapJAtLeastTwoFromEleven :
  HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo 11
```

There is also a Ramsey-certificate wrapper:

```lean
targetStatement_of_proofMdFinalHandoff_of_parityToModFourLoss64_and_ramseyTenRegular_and_twiceLargeGapJAtLeastTwoFromEleven
```

where

```lean
ramseyTenRegular : HasRamseyTenRegularAtDyadicTarget
```

means every graph on at least `40960 = 4^6 * 10` vertices has a regular induced 10-set. This closes
`HasFourToEightTargetTenFixedWitnessLift` because the isolated `m = 10, j = 2` input witness itself
has 40960 vertices.

The strongest checked viable terminal-frontier wrapper currently exposed in Lean is now the affine
cross-selector version:

```lean
targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_fourToEightTargetsToSixteen_and_affineCrossSelectorFromSeventeen
```

Its remaining inputs are:

```lean
sevenVertexBooleanCertificate :
  ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true

HasModFourZeroLossFiveInducedSubgraph

RamseyTenSmallTable

HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5

HasFourToEightTargetElevenFixedWitnessLift

HasFourToEightTargetTwelveFixedWitnessLift

HasExactSmallModulusFixedWitnessDyadicLift 2 13
HasExactSmallModulusFixedWitnessDyadicLift 2 14
HasExactSmallModulusFixedWitnessDyadicLift 3 14
HasExactSmallModulusFixedWitnessDyadicLift 2 15
HasExactSmallModulusFixedWitnessDyadicLift 3 15
HasExactSmallModulusFixedWitnessDyadicLift 2 16
HasExactSmallModulusFixedWitnessDyadicLift 3 16

HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulusAffineCrossSelector 17
```

This is the current best checked Lean statement of "what remains."  The old residual
`HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 17`
is still available, but Lean now exposes the sharper affine cross-selector target: choose a retained
bucket `u` inside the old `2^j` witness support `s` so that the ambient top-bit discrepancy on `s`
cancels pairwise against the dropped tail `s \ u` modulo `2^(j+1)`.  Mathematically, this is the
Lean-facing form of the saturated affine-pair/split-marker route.  The displayed stronger all-zero
loss-5 theorem is one sufficient Lean way to supply the first bit.  `RamseyTenSmallTable` closes the
isolated `m = 10, j = 2` case by
recursing to `R(10,10) <= 40304 < 40960`, and the fixed-witness external-block self-bridge yields
fixed-witness terminal regularization and removes the high-modulus higher-bit slice `m <= 2^j`.
Lean also isolates the first two remaining small-modulus cases, `m = 11, j = 2` and
`m = 12, j = 2`, as the finite targets `HasFourToEightTargetElevenFixedWitnessLift` and
`HasFourToEightTargetTwelveFixedWitnessLift`.  It also isolates the whole next finite block
`13 <= m < 17`, where only `j = 2, 3` survive, using the generic exact target
`HasExactSmallModulusFixedWitnessDyadicLift`; the `(13,3)` case is already discharged by the
generic binomial Ramsey fallback.  The infinite residual in this wrapper now starts at `m >= 17`;
this is the intended cutoff for finite enumeration before switching to a uniform large-`m`
saturated theorem.

There is also a concrete-terminal-field variant:

```lean
targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenRegular_and_terminalFields_and_twiceLargeGapJAtLeastTwoSmallModulusFromEleven
```

but the concrete terminal field package is formally refuted for every nonzero budget by the same
`q = 8` terminal-host obstruction, so the viable route is the fixed-witness-terminal wrapper above.

There is also a historical selector-terminal variant:

```lean
targetStatement_of_proofMdFinalHandoff_of_droppedTailSelector
```

This selector form bypasses the vacuous saturated q-marker wrapper and goes directly through the
finite dropped-tail terminal regularization endpoint.  It is also formally refuted for every nonzero
budget by the `q = 8` obstruction, so it should not be used as a remaining handoff input.

Compatibility wrappers remain available for older assembly surfaces, including:

```lean
targetStatement_of_ramseyIndexWindowAtLeastSeven_and_terminalGraphLocalObligations
targetStatement_of_proofMdConcreteFRSatLargeGapBoolHandoffCertificate
```

The remaining missing formal pieces are the inputs of the strongest viable wrappers plus the
replacement theorem that discharges the older higher-bit residual predicate.  If the seven-vertex Boolean
certificate is accepted from the existing external/Python proof, then the active mathematical gaps are:
the first-bit modulus-four fixed-loss theorem (for Lean, the stronger
`HasModFourZeroLossFiveInducedSubgraph` is sufficient), `RamseyTenSmallTable`,
`HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5` (equivalently enough for
`HasPolynomialCostFixedWitnessTerminalRegularization 5`), and formalization of the saturated
affine-pair/split-marker theorem replacing the finite `m = 11, j = 2` target plus
the finite `m = 12, j = 2` target plus
the exact finite `13 <= m < 17`, `j = 2,3` targets except for the Ramsey-closed `(13,3)` case plus
`HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 17`.
The old monolithic `HasRamseyTenRegularAtDyadicTarget` is still available, but Lean now proves it from
`RamseyTenSmallTable`.

Work order: the dyadic residual should split into the first-bit modulus-four theorem and the already
written higher-bit saturated theorem.  The terminal track should separately push the fixed-witness
terminal side down to the external-block self-bridge and then prove that selected-top-host bridge.

No `sorry`, `admit`, or `axiom` is currently present in the Lean files.

## How `proof.md` proves the theorem conditionally

The notes prove the conjecture conditionally on the first-bit modulus-four fixed-loss theorem, and only in
the canonical residue-saturated exchange convention `FR^sat`. They do not prove the original path-only
Theorem G, and they do not prove the stronger terminal-cascade bridge. The notes explicitly say those are
not needed for the final graph theorem.

The proof chain is:

1. **Threshold reduction.** It suffices to prove a dyadic bound:

   ```text
   T(2^r) <= 2^(O(r^2)).
   ```

   Then `F(n) / log n -> infinity`.

2. **Terminal modular regularity.** If a terminal bucket `U` has size `q` and the induced degrees inside `U` are all congruent modulo `q`, then the degrees are actually equal, because all degrees lie in `[0, q - 1]`. Hence `G[U]` is regular.

3. **Dropped-tail constancy implies terminal regularity.** In the terminal host, if the dropped-tail residue row `rho_R` is constant modulo `q`, then the internal degree residues on `U` are constant modulo `q`, so the terminal bucket is regular.

4. **Nonconstant dropped-tail residue gives a dyadic obstruction.** The notes define an obstruction class `tau_m` and prove the aggregate carry identity:

   ```text
   tau_m = beta_m.
   ```

   If some dropped-tail bit first fails to be constant, then `beta_m != 0`.

5. **Nonzero `beta_m` gives a cut.** A nonzero carry class yields a genuine nonconstant cut in the terminal bucket.

6. **A cut yields a q-marker.** The first boundary seeing the cut cannot be fixed-trace or clean in a minimal obstruction. Therefore it is mixed, and a mixed boundary produces a q-marker.

7. **Local q-marker cases close.** The notes close no-split markers, frozen same-trace markers, one-splitter markers, and static split-quotient cases.

8. **Fully skew markers are handled by saturated provenance.** The hard remaining case is the fully skew q-marker. The notes switch to the canonical saturated exchange complex `FR^sat`.

   Proposition 8.1 says that in `FR^sat`, every ambient high-error splitter has one of three outcomes:

   ```text
   ordered saturated boundary row
   local/branch regularizing exit
   complete smaller q-marker
   ```

9. **Saturated descent is sufficient.** Theorem 8.2 says the terminal proof can be run directly in `FR^sat`, because every added saturated square is still an actual graph exchange with four graph corners and equal terminal residue data. Therefore no comparison with the original path-only first-return path is needed.

10. **Saturated q-markers are excluded.** Lemma 9.1 proves ordered boundary completeness. Proposition 9.2 uses this plus saturated support minimality to rule out fully skew q-marker survivors.

11. **Terminal dyadic theorem.** If `rho_R` were nonconstant, the chain above would produce a q-marker, but all q-markers are excluded. Therefore `rho_R` is constant, hence the terminal bucket is regular.

12. **Terminal regularization.** Every sufficiently large fixed-modulus witness can be reduced to a bounded terminal host. The terminal dyadic theorem regularizes that host.

13. **Dyadic threshold.** Assuming the first-bit modulus-four fixed-loss theorem, start from the parity
    base at modulus `2`, iterate the positive dyadic lift, then apply terminal regularization. The
    cumulative cost is:

   ```text
   product_(i=1)^(r-1) (2^i)^C = 2^(C r(r-1)/2).
   ```

    This conditionally gives:

   ```text
   T(2^r) <= 2^(A(r+1)^2).
   ```

14. **Global conclusion.** The threshold reduction conditionally gives:

   ```text
   F(n) / log n -> infinity.
   ```

## Mapping `proof.md` to current Lean objects

| Notes proof component | Lean object |
|---|---|
| Seven-vertex q=4 finite base | `sevenVertexCodeHasRegularFourOrFiveBool` certificate, bridged to `SevenVertexFourRegularBaseCase` |
| Positive dyadic lift | `HasPolynomialCostPositiveEmptyControlDyadicLift C` |
| Reduced dyadic residual | `HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7` |
| Terminal regularization | `HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalRegularization r` |
| Host-local terminal obligations | `Q64PositiveDyadicTerminalGraphLocalObligations r` |
| Concrete dropped-tail saturated terminal fields | `Q64ProofMdDroppedTailConcreteFRSatTerminalFields r` |
| Saturated q-marker proof route | `Q64ProofMdSaturatedQMarkerTerminalRoute r` |
| Saturated exchange model | `Q64FRSatRawExchangeComplex Row Packet` |
| Completed branch maps | `Q64CompletedFRSatBranchClosureMaps` |
| Saturated q-marker exclusion | `Q64SaturatedQMarkerExclusionData` |
| Final audit components | `Q64FinalAuditComponentChain` |
| Main target | `TargetStatement` |

Current key theorem to use for assembly:

```lean
targetStatement_of_proofMdFinalHandoff
```

## Lean formalization plan

### Phase 1: Formalize or certify the seven-vertex base

Goal:

```lean
theorem sevenVertexFourRegularBaseCase : SevenVertexFourRegularBaseCase := ...
```

Current status:

```lean
def SevenVertexFourRegularBaseCase : Prop :=
  4 ∈ admissibleBounds 7
```

The notes prove this by exhaustive enumeration of all `2^21` labelled graphs on 7 vertices. The Python script reports that every 7-vertex graph has a regular induced subgraph of size at least 4.

Recommended Lean approach:

1. Define a compact edge-code type for graphs on `Fin 7`.
2. Define a boolean checker for "this edge-code has a regular induced subset of size >= 4".
3. Generate a certificate mapping each of the `2^21` graph codes to one valid subset.
4. Prove the checker sound once in Lean.
5. Let Lean verify the certificate, not search from scratch.

This avoids making Lean perform an expensive combinatorial search.

Prototype theorem shape:

```lean
theorem sevenVertexFourRegularBaseCase_of_codeCertificate
    (hcode : ∀ x : SevenEdgeCode, SevenCodeHasRegularInducedSubgraphOfCard x 4) :
    SevenVertexFourRegularBaseCase := ...
```

Then replace `hcode` with a generated certificate verifier.

### Phase 2: Close the residual dyadic lift

Goal, preferably with `C = 6`:

```lean
theorem dyadicWindowAtLeastSeven :
    HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeast 6 7 := ...
```

Definition shape:

```lean
HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeast C 7
```

This says: for `m >= 7`, in the remaining Ramsey-index window,

```lean
j * C < 2 * (m - 1)
n < Nat.choose ((m - 1) + (m - 1)) (m - 1)
```

a fixed-modulus witness of size

```lean
((2 ^ j) ^ C * m)
```

at modulus `2^j` gives a fixed-modulus witness of size `m` at modulus `2^(j+1)`.

Lean already removed several cases:

1. small targets
2. ambient-Ramsey-large cases
3. `m = 3`
4. `m = 4`, using `SevenVertexFourRegularBaseCase`
5. for `C >= 4`, `m = 5`
6. for `C >= 6`, `m = 6`

So with `C = 6`, the dyadic proof only starts at `m >= 7`.

The current formal arithmetic reductions sharpen this further. It is enough to prove the strict
large-gap package:

```lean
HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGap 7
```

In that package, with `d = 2 * (m - 1) - j * 6`, the remaining cases satisfy:

```lean
2 * m < 2 ^ d
```

The complementary slice `2^d <= 2*m` is already contradicted by the central-binomial half-bound.

The newest Lean split then separates off the first dyadic bit. It introduces:

```lean
HasParityToModFourLoss64FixedWitnessLift
```

meaning: every parity-regular fixed witness contains a mod-4 fixed witness on at least a `1/64`
fraction of its vertices. The stronger half-size form is false already on a 9-vertex parity-regular
random example, but the loss-64 form is exactly what the `j = 1`, `C = 6` input size requires. If this
is proved, all `j = 1` strict-residual cases are closed automatically. The remaining higher-bit strict
residual is:

```lean
HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo 10
```

Lean proves that in the strict gap, `j >= 2` forces `m >= 10`.

This has now been pruned in Lean.  The high-modulus slice `2^j >= m` is already terminal: from the
input `2^j`-modular fixed witness, the checked reduction invokes the surviving fixed-witness
terminal regularization surface, obtains a regular induced `2^j`-set, and therefore gets a
mod-`2^(j+1)` fixed witness of card at least `m`.  Thus the path-only strict higher-bit residual is
restricted to:

```lean
2 ^ j < m
```

in addition to `2 <= j`; after the Ramsey-10 split, the public path-only residual starts at `11 <= m`.
In the saturated exchange convention used by the terminal proof, the small-modulus slice is now closed by
the affine-pair/split-marker reduction and Proposition 8.1 below.

This remaining small-modulus package should not be replaced by an unstructured theorem saying that every
large graph has a polynomial-loss induced subgraph with all degrees `0 mod 2^(j+1)`.  Such a theorem
would be false when the modulus grows: below the modulus, divisibility is independence, so a polynomial
loss would force polynomial-size independent sets in arbitrary random graphs.  The viable target must
use the input `2^j`-modular witness and preserve deleted-part residue data, i.e. it is a fixed-modulus
cascade lift rather than a generic divisible-degree selection theorem.

A deletion-facing target is now isolated in `proof.md`.  For a q-modular witness `A`, call
`D subseteq A` q-complete when deleting `D` leaves `A \ D` q-modular; equivalently every survivor has the
same external degree into `D` modulo `q`.  This is only the modulo-`q` shadow of the true dyadic lift.  The
strict small-modulus residual would follow from:

```lean
-- informal mathematical surface
large_non_2q_qWitness_has_size_preserving_qCompleteDeletion
nearTerminal_minimal_qWitness_has_2qWitness
```

The first line is the large-marker no-q-jump/provenance-completeness theorem.  The second is the
exact-marker/near-terminal routing theorem once no deletion can keep the witness above target size.

The actual Lean-facing selector must also carry the top dyadic label.  If `A` is q-modular and

```text
deg_A(v) == d + q b_A(v) [MOD 2q],   b_A(v) in F_2,
```

then a retained set `W subseteq A`, with tail `T = A \ W`, is a `2q` fixed witness exactly when

```text
rho_T(v) := |N(v) cap T| == c + q b_A(v) [MOD 2q]
```

for all `v in W`.  Equivalently, the affine beta class `beta_T + b_A` vanishes in
`M_2(W) / constants`.  A q-complete deletion packet updates the label by
`b_{A\D}=b_A-c_D`, where `rho_D(v)=e+q c_D(v) [MOD 2q]` on the survivor.  Thus the final small-modulus
target should be an affine q-complete selector, not an unlabeled q-complete selector.

The affine selector has a pair-local form.  Once `W` is q-complete relative to `T=A\W`, define

```text
lambda_T(u,v) =
  ((rho_T(u)-rho_T(v)) - (deg_A(u)-deg_A(v))) / q [MOD 2].
```

Then `G[W]` is `2q`-modular iff all `lambda_T(u,v)` vanish.  Hence any remaining obstruction is a single
oriented pair with `lambda_T=1`; the global affine beta cut is obtained by summing these pair labels from
a basepoint.  The current host-frontier bridge to prove is:

```lean
-- informal mathematical surface
qFlat_orientedPair_lambdaOne_promotes_or_hostSquareBreaker
```

where the alternatives are a label-transporting q-complete descent packet, or one of
`host-orient115`, `host-opppair123`, `host-silentedge128`.

Equivalently, after local exits are removed, the pair target is the two-fiber overlap atom:

```text
lambda_T(u,v)=1
  <=> Omega_10 and Omega_01 are nonempty but Omega_10 cap Omega_01 has no 0111 witness.
```

Filling that overlap kills the affine pair obstruction; failing to fill it must produce the complete
shared-slack side used as the label-transporting q-complete deletion packet.

After local exits, the overlap atom has a finite split-marker quotient:

```text
K_(q-2) disjoint_union H,   H in {K_2, 2K_1}.
```

The one-sided compensator/provenance fiber `C` is complete to the two residual rows and anticomplete to
`K_(q-2)`.  The static regular-selection target is a clique in `C` of size `(q-4)/2` when `H=K_2`
(`q>=8`) or `q/2-1` when `H=2K_1` (`q>=6`), unless the proper-divisor bypass already gives a regular
q-set.  Thus the concrete remaining theorem is:

```lean
-- informal mathematical surface
splitMarker_compensatorNoClique_routes_to_section40_or_markerSplit
```

The marker-split/packet-refinement outcome is the label-transporting q-complete deletion packet needed by
the affine dyadic descent.

In the saturated exchange convention `FR^sat`, this routing theorem is discharged by Proposition 8.1:
the compensator components are admissible modules; an ambient splitter either fails a prefix-local test
(Section-40/local closure), is promoted to a saturated boundary row whose first packet-internal failure is
an exchange-complete shared-slack side (the q-complete deletion packet), or directly gives a smaller
q-marker.  Thus the strict higher-bit small-modulus residual is closed for the saturated proof pipeline.
The remaining comparison issue is only the path-only versus `FR^sat` convention, not a new dyadic carry
case.

The first-bit theorem has the same affine shape with `q=2`.  For a parity-regular set `A`, let
`b_A(v)=(deg_A(v)-d)/2 [MOD 2]`, where `d` is the common degree parity.  A subset `W` is mod-4-regular
exactly when, for `T=A\W`,

```text
rho_T(v) == c + 2 b_A(v) [MOD 4]
```

on all `v in W`.  Gallai gives only the modulo-2 shadow.  The full first bit remains the fixed-loss
modulus-four selector: either prove it from the parity-regular witness structure, or import a genuine
fixed-modulus-four congruent-degree theorem.  A uniform `N/(Q+1)` theorem for arbitrary growing `Q` must
not be used here; it would imply unrealistically large regular induced subgraphs by taking
`Q ~ sqrt(N)`.

The formerly isolated first higher-bit case was:

```lean
HasFourToEightTargetTenFixedWitnessLift
```

This is exactly the finite `m = 10`, `j = 2` step:

```lean
HasFixedModulusWitnessOfCard G ((2 ^ 2)^6 * 10) (2 ^ 2)
  -> HasFixedModulusWitnessOfCard G 10 (2 ^ 3)
```

under the same ambient-small hypothesis `n < choose 18 9`.  In the saturated proof pipeline it is covered
by the same affine-pair/split-marker proof as the rest of the `j>=2`, `2^j<m` slice, so a separate
Ramsey-10 certificate is no longer mathematically needed for the saturated handoff.

Lean also proves:

```lean
HasRamseyTenRegularAtDyadicTarget -> HasFourToEightTargetTenFixedWitnessLift
```

So a formal or cited Ramsey certificate with threshold at most `40960` remains a useful path-only/Lean
fallback, but it is not part of the saturated mathematical closure.

Recommended attack:

1. Work only in the exact residual assumptions:

   ```lean
   0 < j
   2 < m
   7 <= m
   j * 6 < 2 * (m - 1)
   2 * m < 2 ^ (2 * (m - 1) - j * 6)
   n < choose (2m - 2) (m - 1)
   ```

2. Isolate the first-bit theorem:

   ```lean
   HasParityToModFourLoss64FixedWitnessLift
   ```

   This is the real remaining dyadic lift input.  The all-zero theorem names
   `HasModFourZeroLoss64InducedSubgraph` and `HasModFourZeroLossFiveInducedSubgraph` are stronger
   sufficient inputs, but they are not known consequences of the current proof notes.

   Do not replace this with a blanket congruent-degree selection theorem for arbitrary moduli.  The
   tempting statement that every `N`-vertex graph has an induced `N/(Q+1)`-vertex subgraph with all
   degrees congruent modulo `Q` would, by taking `Q ~ sqrt(N)`, force `sqrt(N)`-size regular induced
   subgraphs in arbitrary graphs.  The first-bit theorem must use the fixed modulus `4` and the
   parity-regular witness structure, or be imported as a genuine external fixed-modulus result.

   The clean Lean-facing replacement target is the even Eulerian selector.  Gallai reduces the
   odd-parity input to an even induced bucket at loss `2`; therefore the loss-64 theorem follows from:

   ```text
   every induced even-degree graph E contains W with |W| >= |E|/32
   such that all degrees in E[W] are congruent modulo 4.
   ```

   After orienting each even component Eulerian, the zero/two-residue subcase is the stronger bidirected
   selector: find a large induced set `W` and a bit `r` with

   ```text
   out_W(v) == in_W(v) == r [MOD 2]  for every v in W.
   ```

   One-sided directed Gallai partitions are not enough: the modulus-four condition requires the in-
   and out-parity equations to hold on the same retained vertices if the retained graph is forced even.
   The full selector is broader because it may also return all degrees `1` or `3 mod 4`.

   Avoid two false imports here.  The Caro--Krasikov--Roditty zero-sum partition theorem is about the
   number of edges in each induced part modulo `q`, not all vertex degrees modulo `q`; random-graph
   modulo-`q` partition theorems are also irrelevant to arbitrary fixed witnesses.  The exact deterministic
   statement needed is the principal-submatrix form.  Scott's modulo-`k` induced-subgraph results prove
   useful bipartite and chromatic-number lower bounds and explicitly leave the arbitrary-graph linear
   `f_k(n)` direction open; Ferber--Krivelevich and the prescribed-label extension are only parity
   theorems.  Alon--Friedland--Kalai supplies non-induced regular subgraphs under almost-regular/density
   hypotheses, not induced principal submatrices.  Do not cite any of these as a mod-`4` fixed-witness
   selector.

   ```text
   every symmetric zero-diagonal integer matrix with even row sums has a principal submatrix
   on at least n/32 rows whose row sums are congruent modulo 4.
   ```

   This is equivalent to the even selector and would imply `HasParityToModFourLoss64FixedWitnessLift`.
   The bidirected formulation is only a sufficient zero/two-residue strengthening, not an equivalent
   replacement for the principal-submatrix statement.

   A useful failed internal route is bounded layer refinement.  Choosing a largest total-degree class
   costs `2`, and successively synchronizing degrees into exposed discarded layers costs factors of `4`.
   Previously exposed layers stay synchronized under further refinement, but the final retained set has
   one new self-layer in its complement whose contribution is not controlled.  Closing that terminal
   self-layer at no extra loss would prove the desired `1/32` even selector; without it, the argument is
   only a diagnostic and must not be formalized as the theorem.

3. Optional path-only fallback: prove the finite Ramsey table:

   ```lean
   RamseyTenSmallTable
   ```

   Lean proves `RamseyTenSmallTable -> HasRamseyTenRegularAtDyadicTarget`, then uses that to close
   the isolated `m = 10, j = 2` target.  The generic binomial Ramsey bound supplies the
   `R(3,k)` row, and `R(5,5) <= 52` follows by recurrence from `R(4,5) <= 26`.
   The table now consists only of `R(4,5) <= 26`, and the recurrence yields
   `R(10,10) <= 40304 < 40960`.

4. Prove or replace the first remaining finite small-modulus target:

   ```lean
   HasFourToEightTargetElevenFixedWitnessLift
   ```

   Lean proves that in the `m = 11` small-modulus residual, `j = 3` contradicts the strict gap
   inequality, so only `j = 2` remains.

5. Prove or replace the next finite small-modulus target:

   ```lean
   HasFourToEightTargetTwelveFixedWitnessLift
   ```

   The same arithmetic repeats at `m = 12`: `j = 3` contradicts `24 < 16`, so only `j = 2`
   remains.

6. Prove or replace the exact finite block:

   ```lean
   HasExactSmallModulusFixedWitnessDyadicLift j m
   ```

   for `13 <= m < 17` and `j = 2, 3`, except `(13,3)`, which Lean closes by the generic Ramsey
   fallback `R(13,13) <= choose 24 12 <= 8^6 * 13`.  Lean proves that in this range `j = 4` is
   impossible from the small-modulus condition `2^j < m`.  Supplying this block raises the infinite
   residual to `m >= 17`.  This should be the stopping point for finite enumeration unless a
   certificate engine makes these exact cases cheap.

7. For the saturated handoff, prove the remaining higher-bit small-modulus affine selector

   ```lean
   HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulusAffineCrossSelector 17
   ```

   by the affine-pair/split-marker theorem from `proof.md` Lemmas 10.4e--10.4j.  The selector already
   uses the existing residual assumptions:

   ```lean
   2 ^ j < m
   17 <= m
   HasFixedModulusWitnessOfCard G ((2 ^ j)^6 * m) (2 ^ j)
   ```

   and the saturated `FR^sat` provenance/support-decrease proposition.  This is no longer a dyadic
   carry gap; it is a formalization of the saturated q-marker routing already written in the proof notes.

The hardest remaining non-terminal mathematical gap is therefore the first-bit
`HasParityToModFourLoss64FixedWitnessLift`, unless the project chooses to import an external
fixed-modulus-four congruent-degree theorem.

### Phase 3: Deferred terminal replacement

The direct goal below is obsolete as a route to the final theorem:

Goal:

```lean
theorem terminalGraphLocal :
    Nonempty (Q64PositiveDyadicTerminalGraphLocalObligations (D + 1)) := ...
```

This is the Lean package corresponding to `proof.md` Sections 4-9.

Lean now proves:

```lean
isEmpty_q64PositiveDyadicTerminalGraphLocalObligations_of_one_le
isEmpty_q64ProofMdDroppedTailConcreteFRSatTerminalFields_of_one_le
isEmpty_q64ProofMdDroppedTailSelectorTerminalFields_of_one_le
```

Thus the next terminal task is not to fill this structure.  The viable replacement is the
fixed-witness terminal regularization surface:

```lean
HasPolynomialCostFixedWitnessTerminalRegularization D
```

The notes indicate that its proof should first select a terminal host minimal under the saturated
complete-support order, then apply the Section 9 terminal dyadic theorem to that selected host.  The
`q = 8` counterexample only refutes arbitrary bounded hosts; it does not refute this selected-host
fixed-witness statement.

It requires:

```lean
constantResidueRegular
obstructionFullySkew
qMarkerCoupling
properSubmarkerCloses
primeModuleCloses
closedLocalCloses
regularQSetRealizes
```

Map from notes:

| Field | Notes source |
|---|---|
| `constantResidueRegular` | Sections 2-3 |
| `obstructionFullySkew` | Sections 4-6: nonconstant residue -> carry/cut -> q-marker -> local cases removed |
| `qMarkerCoupling` | Sections 8-9 saturated q-marker exclusion |
| `properSubmarkerCloses` | minimality/descent in Section 9 |
| `primeModuleCloses` | local module closure in Section 6 |
| `closedLocalCloses` | local/branch regularizing exits in Sections 6 and 8 |
| `regularQSetRealizes` | terminal bucket regularity in Sections 2-3 |

Recommended implementation:

1. First prove the constant-residue branch concretely:

   ```lean
   constant residue modulo q -> HasRegularInducedSubgraphOfCard G q
   ```

2. Formalize the obstruction chain:

   ```lean
   NonconstantResidue -> DyadicObstructionCut -> QMarker
   ```

3. Reuse or extend existing q-marker structures in `Frontier.lean`.
4. Prove that the local q-marker closures produce one of:

   ```lean
   ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ FullySkewSplitter
   ```

5. For the fully skew case, defer to Phase 4's saturated q-marker exclusion.

### Phase 4: Formalize the concrete saturated `FR^sat` route

Goal:

```lean
theorem terminalRoute :
    Nonempty (Q64ProofMdSaturatedQMarkerTerminalRoute (D + 1)) := ...
```

or construct it via:

```lean
q64ProofMdSaturatedQMarkerTerminalRoute_of_structuralFRSat
```

The notes' Proposition 8.1 says:

```text
in FR^sat, every fully skew high-error splitter gives:
1. local/branch regularizing exit, or
2. complete smaller q-marker, or
3. ordered saturated boundary row
```

Lean already has structural branch-map support:

```lean
q64_completedFRSatBranchClosureMaps_structural
```

so the remaining task is to instantiate the actual saturated exchange complex and prove that the notes' `FR^sat` objects satisfy the abstract interface.

Recommended steps:

1. Define the concrete `Row` and `Packet` types for the terminal q-marker situation.
2. Define:

   ```lean
   Q64FRSatRawExchangeComplex Row Packet
   ```

3. Prove the prefix-local failure branch:

   ```lean
   Q64FRSatPrefixLocalFailure -> local exit
   ```

4. Prove the nonzero first terminal residue branch:

   ```lean
   Q64FRSatNonzeroFirstTerminalResidue -> local exit
   ```

5. Prove the complete smaller marker branch:

   ```lean
   Q64FRSatExchangeCompleteSmallerQMarker -> ProperSubmarker
   ```

6. Use:

   ```lean
   q64_saturatedQMarkerExclusionData_structural
   ```

   or the existing saturated exclusion package to assemble:

   ```lean
   Q64SaturatedQMarkerExclusionData
   ```

This phase is the Lean version of `proof.md` Proposition 8.1 and Proposition 9.2.

### Phase 5: Assemble the final theorem

Once the following are available:

```lean
sevenVertexBooleanCertificate :
  ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true

largeGapDyadicWindow :
  HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7

droppedTailConcreteFRSatTerminalFields :
  Q64ProofMdDroppedTailConcreteFRSatTerminalFields (D + 1)
```

the final assembly should be short:

```lean
theorem targetStatement_final : TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff
      (D := D)
      sevenVertexBooleanCertificate
      largeGapDyadicWindow
      droppedTailConcreteFRSatTerminalFields
```

## Suggested priority order

1. **Do the seven-vertex finite base first.** It is finite, isolated, and removes an explicit hypothesis.
2. **Then attack terminal graph-local obligations.** This directly formalizes the notes' Sections 4-9 and is the mathematical heart of the saturated route.
3. **Then prove the residual dyadic window.** This is technically hard but now sharply isolated. Use `C = 6` and target only `m >= 7`.
4. **Finally assemble `TargetStatement`.** The final Lean theorem should be a thin wrapper around the existing endpoint.

## What not to spend time on

Do not try to prove these unless the goal changes:

1. Original path-only Theorem G.
2. Path-saturation equivalence.
3. Stronger `q >= 4` terminal-cascade bridge.
4. All-`j` empty-control dyadic lift.
5. Unit-exponent positive dyadic lift.

Lean already has counterexamples or notes explaining why some of these are false or stronger than needed. The route to the conjecture is the saturated `FR^sat` route plus terminal regularization, not the old path-only/cascade route.
