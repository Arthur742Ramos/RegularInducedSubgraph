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

The preferred checked terminal-frontier wrapper currently exposed in Lean is the uniform higher-bit
affine-selector version with the first bit reduced through Gallai to an even-degree mod-four selector
and the terminal side left at the real fixed-witness external-block bridge:

```lean
targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
```

Its remaining inputs are:

```lean
sevenVertexBooleanCertificate :
  ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true

C : ℕ
0 < C
C ≤ 32
HasEvenDegreeModFourCongruentDegreeColoringBound C

RamseyTenSmallTable

HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5

HigherBitSmallModulusAffineSelectorsFromEleven
```

The higher-bit input can equivalently be exposed through the slightly stronger
`HigherBitSmallModulusAffineSelectorsFromElevenExtended`, which adds the finite `(m,j)=(13,3)`
affine selector instead of using the built-in Ramsey fallback for that one slice.  Lean provides
`hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus_eleven_of_extended`
and the certified wrapper
`targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromElevenExtended_certifiedSeven`.

There is also a sufficient finite-Ramsey expansion of the D=5 external-block bridge:

```lean
targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
```

Its remaining inputs are:

```lean
sevenVertexBooleanCertificate :
  ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true

HasLargeEvenDegreeModFourLoss32InducedSubgraph

RamseyTenSmallTable

HasCliqueOrIndepSetBound 16 16 8388607

∀ {j : ℕ}, 5 ≤ j →
  ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
    2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j

HigherBitSmallModulusAffineSelectorsFromEleven
```

This finite-Ramsey expansion is useful as a diagnostic sufficient condition for the terminal bridge,
but it should not be treated as the main route to an unconditional proof: the tail is an arbitrary
graph Ramsey bound of polynomial size in `q = 2^j`, so the real terminal goal remains the
fixed-witness external-block bridge above.

For importing the tail as a conventional Ramsey theorem, Lean now has
`cliqueOrIndepSetBoundTail_of_pow_six_bound`, which packages a pointwise family
`HasCliqueOrIndepSetBound q q R` with `2 * R + 1 <= q^6` into the exact terminal-tail shape above.
The corresponding certified-seven endpoint is
`targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_powSixTail_and_higherBitAffineSelectorsFromEleven_certifiedSeven`.

With `RegularInducedSubgraph.CertifiedHandoff` imported, these same fields are packaged as
`CertifiedProofMdCurrentFrontierCertificate`, since the seven-vertex finite certificate is supplied by
`SevenVertexCertificate`.  The stronger arbitrary-set coloring variant is packaged as
`CertifiedProofMdCurrentFrontierModFourColoringCertificate`, and the weaker first-bit import surface
that only asks for an even-degree bounded coloring theorem with at most `32` colors is packaged as
`CertifiedProofMdCurrentFrontierColoringCertificate`.  For the preferred external-block terminal
frontier, use `CertifiedProofMdExternalBlockFrontierCertificate`,
`CertifiedProofMdExternalBlockFrontierColoringCertificate`, or
`CertifiedProofMdExternalBlockFrontierModFourColoringCertificate`.

This is the current best checked Lean statement of "what remains."  The old residual
`HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 17`
is still available, but Lean now packages all higher-bit small-modulus work after Ramsey-10 as affine
selectors: the finite `m = 11,12,13,14,15,16` selectors plus the uniform `m >= 17` selector.  Each
selector chooses a retained bucket `u` inside the old `2^j` witness support `s` so that the ambient
top-bit discrepancy on `s` cancels pairwise against the dropped tail `s \ u` modulo `2^(j+1)`.
Mathematically, this is the Lean-facing form of the saturated affine-pair/split-marker route.  The
first bit is now reduced to the large-support even-degree loss-32 selector; supports of size at most
`32` are Lean-closed by empty/singleton witnesses, and Gallai contributes the extra loss factor `2`,
yielding the existing `HasParityToModFourLoss64FixedWitnessLift`.  The older stronger all-zero loss-5
theorem is still a sufficient compatibility input, but it is no longer the cleanest first-bit frontier.
Lean also exposes the bounded-partition import surface
`HasModFourCongruentDegreeColoringBound 32`: a 32-color partition of every induced vertex set into
mod-4 congruent induced parts implies the even-degree selector by pigeonholing the largest color
class.  The exact weaker first-bit import surface is
`HasEvenDegreeModFourCongruentDegreeColoringBound C` for any `0 < C <= 32`; it only needs to color
the even induced buckets produced by Gallai.
`RamseyTenSmallTable` closes the isolated `m = 10, j = 2` case by
recursing to `R(10,10) <= 40304 < 40960`, and the fixed-witness external-block self-bridge yields
fixed-witness terminal regularization and removes the high-modulus higher-bit slice `m <= 2^j`.
The fixed-witness terminal side also now has a direct finite-Ramsey prefix, independent of the
external-block/cascade package:

```lean
fixedWitnessTerminalRegularizationData_of_ramsey_exponent_bound
hasPolynomialCostFixedWitnessTerminalRegularization_of_exact_ramsey_prefix_and_tail
fixedWitnessTerminalRegularizationData_six_of_le_four
hasPolynomialCostFixedWitnessTerminalRegularization_six_of_tail_from_five
fixedWitnessTerminalRegularizationData_eleven_of_le_five
hasPolynomialCostFixedWitnessTerminalRegularization_eleven_of_tail_from_six
fixedWitnessTerminalRegularizationData_twenty_of_le_six
hasPolynomialCostFixedWitnessTerminalRegularization_twenty_of_tail_from_seven
hasPolynomialCostFixedWitnessTerminalRegularization_of_ramsey_prefix_and_tail
fixedWitnessTerminalRegularizationData_thirtyFive_of_le_seven
hasPolynomialCostFixedWitnessTerminalRegularization_thirtyFive_of_tail_from_eight
fixedWitnessTerminalRegularizationData_thirtySix_of_le_seven
hasPolynomialCostFixedWitnessTerminalRegularization_thirtySix_of_tail_from_eight
hasPolynomialCostFixedWitnessTerminalRegularization_mono
fixedWitnessTerminalRegularizationData_sixtyThree_of_le_eight
hasPolynomialCostFixedWitnessTerminalRegularization_sixtyThree_of_tail_from_nine
fixedWitnessTerminalRegularizationData_oneHundredThirteen_of_le_nine
hasPolynomialCostFixedWitnessTerminalRegularization_oneHundredThirteen_of_tail_from_ten
fixedWitnessTerminalRegularizationData_twoHundredFour_of_le_ten
hasPolynomialCostFixedWitnessTerminalRegularization_twoHundredFour_of_tail_from_eleven
fixedWitnessTerminalRegularizationData_sixHundredEightyTwo_of_le_twelve
hasPolynomialCostFixedWitnessTerminalRegularization_sixHundredEightyTwo_of_tail_from_thirteen
```

The same section also exposes a direct selector ladder that is strictly weaker than producing
external-block/cascade data:

```lean
HasPolynomialCostFixedWitnessRegularSubbucketSelection
HasPolynomialCostFixedWitnessModEqSubbucketSelection
HasPolynomialCostFixedWitnessDroppedTailConstancySelection
hasPolynomialCostFixedWitnessTerminalRegularization_of_regularSubbucketSelection
hasPolynomialCostFixedWitnessTerminalRegularization_of_modEqSubbucketSelection
hasPolynomialCostFixedWitnessTerminalRegularization_of_droppedTailConstancySelection
```

So the terminal-regularization task can now be attacked directly as exact subbucket selection inside
the chosen large fixed-modulus host, or equivalently as dropped-tail residue constancy on that selected
subbucket, without asking for the stronger terminal external-block/cascade witness.  For the viable
D=5 external-block frontier, Lean also has a nonzero-exponent upgrade from these selectors back to
external-block data:

```lean
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_regularSubbucketSelection
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_modEqSubbucketSelection
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_droppedTailConstancySelection
HasPolynomialCostFixedWitnessRegularSubbucketSelectionFiveFromFive
HasPolynomialCostFixedWitnessModEqSubbucketSelectionFiveFromFive
HasPolynomialCostFixedWitnessDroppedTailConstancySelectionFiveFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive_of_regularSubbucketSelectionFiveFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive_of_modEqSubbucketSelectionFiveFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive_of_droppedTailConstancySelectionFiveFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_regularSubbucketSelectionFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_modEqSubbucketSelectionFromFive
hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_droppedTailConstancySelectionFromFive
```

Thus the external-block terminal side is now reduced to the q=16 Ramsey certificate plus a genuine
`j >= 5` exact subbucket/dropped-tail selector, while the already checked `j = 1,2,3` slices stay
outside the remaining tail obligation.

Thus the terminal regularization frontier can be pushed past any checked finite dyadic prefix by
increasing the fixed polynomial exponent.  Concretely, Lean now regularizes all fixed-witness
terminal slices through `q = 16` at exponent `6`, through `q = 64` at exponent `20`, and through
`q = 128` at exponent `35`.  The exact finite-prefix form also reaches `q = 32` at exponent `11`.
The coarser direct Ramsey-prefix arithmetic has additionally been batched through
`q = 256` at exponent `63`, `q = 512` at exponent `113`, `q = 1024` at exponent `204`, and
`q = 4096` at exponent `682`; the exponent-`682` terminal tail starts only at `j >= 13`.
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
the first-bit even-degree bounded coloring theorem
`HasEvenDegreeModFourCongruentDegreeColoringBound C` for some `0 < C ≤ 32` (or equivalently the
loss-32 selector it implies), `RamseyTenSmallTable`,
`HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5` (equivalently enough for
`HasPolynomialCostFixedWitnessTerminalRegularization 5`; alternatively the direct fixed-witness
terminal tail `j >= 13` at exponent `682` would be enough for
`HasPolynomialCostFixedWitnessTerminalRegularization 682`), and formalization of the saturated
affine-pair/split-marker theorem replacing the finite `m = 11, j = 2` target plus
the finite `m = 12, j = 2` target plus
the exact finite `13 <= m < 17`, `j = 2,3` targets except for the Ramsey-closed `(13,3)` case plus
`HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 17`.
The old monolithic `HasRamseyTenRegularAtDyadicTarget` is still available, but Lean now proves it from
`RamseyTenSmallTable`.

Work order: the dyadic residual should split into the first-bit even-degree selector and the already
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
| Terminal regularization | `HasPolynomialCostFixedWitnessTerminalRegularization D` |
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

   The clean Lean-facing replacement target is now formalized as
   `HasLargeEvenDegreeModFourLoss32InducedSubgraph`: the full even-degree selector is equivalent to
   the large-support version because supports of size at most `32` are discharged by empty/singleton
   witnesses.  Gallai reduces the odd-parity input to an even induced bucket at loss `2`, and Lean
   proves

   ```lean
   hasLargeEvenDegreeModFourLoss32InducedSubgraph_iff :
     HasLargeEvenDegreeModFourLoss32InducedSubgraph ↔
       HasEvenDegreeModFourLoss32InducedSubgraph

   hasParityToModFourLoss64FixedWitnessLift_of_evenDegreeModFourLoss32InducedSubgraph :
     HasEvenDegreeModFourLoss32InducedSubgraph →
       HasParityToModFourLoss64FixedWitnessLift

   hasEvenDegreeModFourLoss32InducedSubgraph_of_modFourCongruentDegreeColoringBound :
     HasModFourCongruentDegreeColoringBound 32 →
       HasEvenDegreeModFourLoss32InducedSubgraph

    hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound :
      0 < C → C ≤ 32 →
        HasEvenDegreeModFourCongruentDegreeColoringBound C →
          HasEvenDegreeModFourLoss32InducedSubgraph

    hasModFourCongruentDegreeColoringBound_mono :
      C ≤ D →
        HasModFourCongruentDegreeColoringBound C →
          HasModFourCongruentDegreeColoringBound D

    hasEvenDegreeModFourCongruentDegreeColoringBound_mono :
      C ≤ D →
        HasEvenDegreeModFourCongruentDegreeColoringBound C →
          HasEvenDegreeModFourCongruentDegreeColoringBound D
    ```

   Thus the remaining selector is exactly:

   ```text
   every induced even-degree graph E with |E| >= 33 contains W with |W| >= |E|/32
   such that all degrees in E[W] are congruent modulo 4.
   ```

   Do not use a fixed Eulerian orientation of the ambient even graph as a linear replacement for the
   zero/two-residue subcase.  Once a particular even induced graph `E[W]` is known, it can be oriented
   Eulerian and then out-parity equals `deg_{E[W]}(v)/2 [MOD 2]`; however the restriction of an
   Eulerian orientation of `E` to `E[W]` need not be Eulerian.  Inherited out- and in-parities therefore
   do not determine the second bit of `deg_{E[W]}(v)` on the candidate support.  The full selector is
   broader anyway, because it may also return all degrees `1` or `3 mod 4`.

   The prescribed-parity extension of Ferber--Krivelevich should be recorded only as an `F_2` tool.  It
   gives a small linear induced subgraph with `deg_H(v)=f(v) [MOD 2]`, but does not control the carry
   `binom(deg,2) [MOD 2]`.  Its directed Gallai-type characterization also warns against an
   orientation shortcut: a directed triangle is Eulerian but has no even/even out-degree partition.

   Iterated Gallai even/even partitioning is another false closure: after five halvings one has an even
   induced leaf of size `n/32`, but not a mod-`4` congruent leaf.  The discarded sibling layers have even
   degree into the leaf, yet their half-degree parities can vary by vertex, leaving the carry coordinate
   uncontrolled.

   A one-coordinate odd-degree theorem for 3-uniform hypergraphs is also not enough.  The carry
   coordinate is the degree in the centered-pair 3-uniform hypergraph with edges `{v,x,y}` whenever
   `vx` and `vy` are graph edges.  Such a theorem can synchronize `binom(deg,2) [MOD 2]` on a support,
   but it does not simultaneously synchronize `deg [MOD 2]`.  A usable import would need a
   vector-valued induced parity selector for both coordinates on the same retained set.

   Avoid two false imports here.  The Caro--Krasikov--Roditty zero-sum partition theorem is about the
   number of edges in each induced part modulo `q`, not all vertex degrees modulo `q`; random-graph
   modulo-`q` partition theorems are also irrelevant to arbitrary fixed witnesses.  The exact deterministic
   statement needed is the principal-submatrix form.  Scott's modulo-`k` induced-subgraph results,
   sharpened by Hunter, give useful bipartite/chromatic lower bounds with all degrees `1 mod k`;
   Ferber--Krivelevich proves the arbitrary-graph `k=2` odd-degree conjecture with constant
   `1/10000`.  These are genuine nearby theorems, but they do not provide the needed arbitrary
   even-graph mod-`4` selector within the loss-`64` budget: the Scott--Hunter theorem is bipartite-only,
   and the Ferber--Krivelevich theorem freezes only the first parity bit.  Prescribed-parity extensions
   are still only `F_2` label theorems; the second bit of an even degree is the carry
   `binom(deg,2) [MOD 2]`, not an inherited ambient out-degree parity.  Alon--Friedland--Kalai supplies non-induced regular
   subgraphs under almost-regular/density hypotheses, not induced principal submatrices.  Do not cite
   any of these as a mod-`4` fixed-witness selector.

   The exact carry normal form is useful for formalization triage.  For `W` and `v in W`,

   ```text
   deg_W(v) [MOD 4] is determined by
   p_W(v) = deg_W(v) [MOD 2]
   c_W(v) = binom(deg_W(v),2) [MOD 2]
          = #{ unordered selected neighbor-pairs of v } [MOD 2].
   ```

   The first-bit selector is therefore a simultaneous parity theorem for the graph-degree coordinate
   `p_W` and the centered pair-hypergraph coordinate `c_W`.  Linear prescribed-parity imports address
   only `p_W`; they do not synchronize `c_W` on the same retained support.

   The exact internal target can be stated without mentioning modulo `4`:

   ```text
   for every even graph E, find W with |W| >= |E|/32 and constants p,c in F_2
   such that every v in W has
   deg_W(v) = p [MOD 2]
   and an even/odd constant number c of unordered selected neighbor-pairs.
   ```

   This is equivalent to `HasLargeEvenDegreeModFourLoss32InducedSubgraph`, not merely sufficient:
   the pair `(p,c)` is exactly the binary expansion of `deg_W(v) [MOD 4]`.

   Useful algebraic deletion identity: if `W subset S`, `B = S \ W`, and `v in W`, then over `F_2`

   ```text
   p_W(v) = p_S(v) + p_B(v),
   c_W(v) = c_S(v) + c_B(v) + p_W(v) * p_B(v),
   ```

   where `p_X(v)=deg_X(v) [MOD 2]` and `c_X(v)=binom(deg_X(v),2) [MOD 2]`.  This is the formal
   self-layer equation behind the exposed-layer obstruction: old deleted layers can be synchronized,
   but the last fresh deleted layer must have both `p_B` and `c_B` synchronized on the retained support.

   A co-degree package explains the exact terminal form.  Since the input graph is even, choose a
   largest total-degree class `S0`; it has size at least half.  For `W subset S0`,

   ```text
   deg_W(v) == lambda - deg_{E \ W}(v) [MOD 4].
   ```

   A fully labeled theorem would be sufficient:

   ```text
   for every graph H and label alpha : V(H) -> Z/4Z, there is W with |W| >= |H|/16
   such that alpha(v) + deg_{H \ W}(v) is constant modulo 4 for all v in W.
   ```

   But the application only needs the special case `alpha(v)+deg_H(v)=lambda`, because
   `alpha(v)=deg_{E\S0}(v)`.  In that case the statement is exactly:

   ```text
   every graph H has W with |W| >= |H|/16 whose induced degrees are congruent modulo 4.
   ```

   This fixed-modulus-four arbitrary-graph selector, applied to `H=E[S0]`, is the sharpest current
   standalone endpoint for the first-bit problem.

   A maximal-counterexample packet form is now isolated.  If `W` is maximal with induced degrees all
   `r mod 4`, then any nonempty outside packet `B` satisfying

   ```text
   deg_B(w) == delta [MOD 4]                         for all w in W,
   deg_W(b) + deg_B(b) == r + delta [MOD 4]          for all b in B
   ```

   would enlarge `W`.  The first condition is only linear co-cut balancing: for any outside pool `P`
   with `|P| > 3(|W|-1)`, the AFK/Olson zero-subsum lemma applied to the difference vectors
   `(1_{bw}-1_{bw0})_{w != w0}` gives a nonempty `B subset P` for which `deg_B(w)` is constant on
   `W` modulo `4`.  Hence the old-witness side can be balanced at linear cost; the obstruction is the
   second condition, the internal packet degree/carry equation on `B`.

   The zero-shift sparse side of the packet obstruction is closed.  For
   `P_0={b in V\W : deg_W(b)=r [MOD 4]}`, any independent set `I subset P_0` of size greater than
   `3|W|` contains, by Olson on the full adjacency vectors `(1_{bw})_{w in W}`, a nonempty subset `B`
   with `deg_B(w)=0` for all old vertices.  Since `B` is independent, `deg_B(b)=0`, so
   `W union B` enlarges `W`.  Thus
   a maximal counterexample must satisfy

   ```text
   alpha(P_0) <= 3|W|.
   ```

   The other sparse chambers and the dense chambers reduce to the same target-subsum variant.  For an
   independent chamber `I subset P_t`, the target is
   `sum_B(1_{bw}) == t-r [MOD 4]` for every `w in W`; for a clique chamber `K subset P_t`, the target is
   `sum_B(1-1_{bw0}) == r-t+1 [MOD 4]`.  Together with the old difference sums, either target enlarges
   `W`.  The last obstruction is therefore affine target avoidance in `(Z/4Z)^{|W|}`, not ordinary
   old-witness zero-sum balance.

   The exact remaining packet lemma is now:

   ```text
   If W is maximum-cardinality of residue r, |W|=m, and P_t={b:deg_W(b)=t} has |P_t|>3m,
   then P_t contains nonempty B and delta with
     deg_B(w)=delta       for all w in W,
     deg_B(b)=r+delta-t   for all b in B.
   ```

   This lemma immediately gives the `1/16` arbitrary selector: if `m<n/16`, the four chambers partition
   more than `15m` outside vertices, so one chamber has size `>3m` and extends `W`.  The threshold `3m`
   is the Olson threshold for `(Z/4Z)^m`; the unproved content is exactly the internal-degree target,
   using maximality of `W`.  Do not state the chamber lemma without maximality: independent chambers
   with all old-neighborhood vectors equal can avoid nonzero affine targets, but then they are ruled out
   only when they are themselves larger mod-`4`-congruent witnesses.

   For formalization, this must be cardinal maximum, not inclusion maximal.  In a true counterexample
   setup, every chamber `P_t` has no mod-`4`-congruent induced subgraph larger than `W`; in particular
   `alpha(P_t)<=m` and `omega(P_t)<=m`.  Thus the residual chamber is not a sparse chamber but a
   dense/no-large-regular-witness object, and the affine packet lemma must import that global maximum
   hypothesis explicitly.

   The loss-`32` target does not require the sharp `>3m` lemma.  If `m<n/32`, the largest chamber has
   size `>31m/4`; iterated Olson inside it gives an old-balanced union of size `>19m/4` after discarding
   at most `3(m-1)` vertices.  A possible weaker formal endpoint is therefore a replacement lemma for
   such a large old-balanced packet.  If `B subset P_t` has old increment `delta` and one deletes
   `D subset W`, then `W\D union B` has common residue `R` exactly when

   An external arbitrary-graph mod-`4` selector with constant strictly greater than `4/31` would also
   close this chamber directly, because it would find a mod-`4` congruent induced subgraph inside
   `P_t` larger than `m`.  Constants at or below `4/31` do not suffice for this direct chamber
   maximality argument, so the formal proof should either import a stronger universal constant or use
   the special degree-to-`W` chamber structure.

   ```text
   deg_D(w)=r+delta-R       for kept old vertices w,
   deg_D(b)=t+deg_B(b)-R    for packet vertices b.
   ```

   The affine packet lemma is the `D=empty`, `R=r+delta` special case; the nonempty-`D` version is the
   replacement slack available only because the required constant is `1/32` rather than the sharper
   arbitrary-selector `1/16`.
   Add the equivalent self-error form:
   `eta_B(b)=t+deg_B(b)-r-delta`, `lambda=r+delta-R`,
   `deg_D(w)=lambda` on `W\D`, and `deg_D(b)=eta_B(b)+lambda` on `B`.
   Formalize the two scalar checks
   `sum_{b in B}(eta_B(b)+lambda)=|D|delta [MOD 4]` and
   `lambda(m-|D|)=|D|r-2e(D) [MOD 4]`.  The `|D|=1` repair case is only possible when the deleted vertex
   is all-zero or all-one on the kept old witness and the shifted self-errors are actual bits.

   For a weaker formal endpoint, deletion can lower the number of old coordinates only after one
   accounts for its affine target.  If `D subset W`, `E=W\D`, and `e_0 in E`, the old-side
   replacement condition is

   ```text
   deg_B(w)-deg_B(e_0)=deg_D(w)-deg_D(e_0)       for every w in E.
   ```

   Plain Olson gives large zero-target packets, not arbitrary target packets.  Hence the earlier
   deletion-first shortcut is valid without a new target-representation lemma only when `deg_D` is
   constant on `E`, equivalently when `E` is itself a mod-`4` congruent induced subset of `W`.
   In that zero-target subcase, Olson on the coordinates of `E` gives an old-balanced packet `B_E`
   with

   ```text
   |B_E| > N - max(0,3(|E|-1)) > m-|E|.
   ```

   The remaining statement is then exactly the corrected self-layer condition

   ```text
   deg_E(b)+deg_{B_E}(b)=constant       for b in B_E
   ```

   or the same condition on an old-balanced subpacket still larger than `W\E`.  In its most symmetric
   form, the profitable replacement lemma still asks for `B subset P_t`, `D subset W`, and `K` with

   ```text
   deg_B(w)-deg_D(w)=K          for every w in W\D,
   deg_B(b)-deg_D(b)=r+K-t      for every b in B,
   |B|>|D|.
   ```

   This is necessary and sufficient for `(W\D) union B` to contradict maximality of `W`.
   Add the signed global scalar:
   `(m-|D|-|B|)K=(|B|-|D|)r+2e(D)-2e(B) [MOD 4]`; if `m-|D|+|B|` is odd then `r+K` is even.
   Together with the full-frame old scalar, record the eliminated odd-`m` test
   `(m-|D|-|B|)(|B|t-|D|r)=m((|B|-|D|)r+2e(D)-2e(B)) [MOD 4]`.
   Its mod-`2` corollary is: for odd `m`, odd `t` and odd `|B|` force even `|D|`.

   The safe formal replacement for the invalid arbitrary-target shortcut is a signed Olson packet.
   When the signed old side has common value `K` on all of `W`, include the double-count
   `mK=|B|t-|D|r [MOD 4]`.
   Include the case table: odd `m` determines `K`, `m=2` requires `|B|t-|D|r` even and fixes `K`
   modulo `2`, and `m=0` requires `|B|t=|D|r`.
   Record two target-zero chamber caps first.  In a packet-maximal witness of residue `r`, the independent
   number of `P_0={b:deg_W(b)=r}` is at most `3m`, and the clique number of
   `P_+={b:deg_W(b)=r+1}` is at most `3m`.  The dense cap uses Olson on
   `((1_{bw}-1_{bw0})_{w != w0},1-1_{bw0})`: zero sum gives constant old degree `delta` and
   `|B|-delta=0`, so a clique packet in `P_+` has new degree `r+delta`.
   Also formalize the mixed zero-target rule: an old-zero independent packet in `P_0` and a clique packet
   in `P_+` with old degree `kappa=|K|` append together if their cross graph is empty and `|K|=0`, or
   complete and `|I|=0`, modulo `4`.
   Exact cross-regular version: if `c_I=deg_K(i)` on `I` and `c_K=deg_I(k)` on `K`, then append iff
   `c_I=kappa`, `|K|+c_K=kappa [MOD 4]`, and `|I|c_I=|K|c_K`.
   Add old-frame constraints `r|I|=0` and `m kappa=(r+1)|K|`; with `kappa=|K|`, this is
   `(m-r-1)|K|=0`.
   Record the size table: odd `r` forces `|I|=0`, `r=2` forces `|I|` even; odd `m-r-1` forces `|K|=0`,
   and `m-r-1=2` forces `|K|` even.
   Equivalently, `( |I|-|K| )kappa=-|K|^2 [MOD 4]`.
   Generalize this as the two-packet scalar equation: internally regular cross-uniform packets
   `B_a subset P_a`, `B_b subset P_b` append iff
   `a+d_a+epsilon|B_b|=b+d_b+epsilon|B_a|=r+delta_a+delta_b [MOD 4]`.
   The finite packet-system form is
   `a_j+d_j+sum_{k != j}epsilon_{jk}|B_k|=r+sum_k delta_k [MOD 4]` for every internally regular packet
   `B_j` when all cross graphs between packets are uniform.
   Generalize to the exact cross-regular quotient: if `c_{jk}` is the common degree from `B_j` to `B_k`
   modulo `4`, impose edge-count symmetry `|B_j|c_{jk}=|B_k|c_{kj}` and the equations
   `a_j+d_j+sum_{k != j}c_{jk}=r+sum_k delta_k [MOD 4]`.
   Include the old witness edge-count constraint `mr=2e(W) [MOD 4]`, especially odd `m => r` even.
   Include the old-frame edge-count constraint `m delta_j=a_j|B_j| [MOD 4]` for each old-balanced packet
   `B_j subset P_{a_j}`.
   Record its consequences: if `m` is odd, replace `sum delta_j` by `m^{-1}sum a_j|B_j|`; if
   `m=0 [MOD 4]`, require `a_j|B_j|=0`; if `m=2 [MOD 4]`, require `a_j|B_j|` even and fix
   `delta_j` modulo `2`.
   Include the size feasibility table: odd `m` allows all `(a,s)`; `m=2` requires `as` even; `m=0`
   requires `as=0`, so odd `s` forces `a=0` and `s=2` forces `a` even.
   Formalize the single-packet test: an internally regular `B subset P_a` of size `s` and residue `d`
   appends iff `a+d=r+delta` and `m delta=as`, equivalently `m(a+d-r)=as [MOD 4]`.
   Include the special cases: for `m=0`, the arithmetic test is `as=0` and the packet must realize
   `delta=a+d-r`; for odd `m`, `a=0` requires `d=r`,
   unit `a` determines `s`, and `a=2` determines `s` modulo `2`.
   Also formalize the row-difference split: with
   `R_j=a_j+d_j+sum_{k != j}c_{jk}`, the first condition is `R_j=R_l` for all packets and the
   final condition is the scalar target `R_j=r+sum_k delta_k`.
   Add the global scalar check:
   `S r+(S-m)Delta=2e(B) [MOD 4]`, with
   `2e(B)=sum_j s_j d_j+sum_{j != k}s_j c_{jk}`; if `m+S` is odd, the target residue is even.
   For two packets, record the eliminated form: with `A=(a+d_a)-(b+d_b)`, row equality gives
   `c_{ba}=c_{ab}+A`, edge-count symmetry gives `(s_a-s_b)c_{ab}=s_b A [MOD 4]`, and the target is
   `c_{ab}=r+delta_a+delta_b-a-d_a`.
   Equivalently, after substitution:
   `(s_a-s_b)(r+delta_a+delta_b-a-d_a)=s_b((a+d_a)-(b+d_b)) [MOD 4]`, with the usual gcd cases for
   solving a linear congruence modulo `4`.
   For odd `m`, substitute `delta_a=m^{-1}a s_a` and `delta_b=m^{-1}b s_b` to get the intrinsic
   two-packet feasibility criterion.
   Add the odd-size parity shadow: on odd-size packets, `c_{jk}=c_{kj} [MOD 2]`, so the first-bit row
   condition is `a_j+d_j+deg_Q(j)=constant [MOD 2]` for the quotient graph of odd cross parities.
   Record the size-stratum edge-count table: odd sizes determine opposite residues up to units;
   size-`0` versus odd forces incoming residue `0`; two size-`2` packets force equality only modulo `2`;
   two size-`0` packets impose no modulo-`4` edge-count constraint.
   For two odd packets, equal size residues mean `c_{jk}=c_{kj}` and opposite size residues mean
   `c_{jk}=-c_{kj}` modulo `4`.
   Formalize exact packet coalescence: same-chamber same-external-profile packets with cross residues
   `c_{12},c_{21}` merge if `c_{12}=c_{21}`; the merged internal residue is `d+c_{12}` and the old
   increment is the sum.  Conversely their row difference is `c_{12}-c_{21}`, so any appendable
   primitive packet system uses at most one packet from each same-profile class.
   Choose `w_0 in W`, work in `(Z/4Z)^(W\{w_0})`, and insert positive vectors
   `p_b(w)=1_{bw}-1_{bw_0}` for `b in P_t` together with negative vectors
   `-p_d(w)=-(1_{dw}-1_{dw_0})` for `d in W`.  Greedy Olson on the combined sequence leaves at most
   `3(m-1)` elements unused, so the union of the removed zero-sum blocks gives `B subset P_t` and
   `D subset W` with

   ```text
   |B| >= |P_t|-3(m-1) > 19m/4,       |D| <= m,
   deg_B(w)-deg_D(w)=constant         for every w in W.
   ```

   Hence `|B|>|D|` and the old-side line of the profitable packet is already certified.  The remaining
   formal lemma is the signed self-layer cleanup preserving positive surplus and forcing
   `deg_B(b)-deg_D(b)` to be constant on the retained positive vertices.
   Equivalently, since `W` itself has zero old-coordinate sum, put `E=W\D`; then `E union B` has
   size greater than `m` and is already regular on the old coordinate frame.  The remaining condition
   is only the degree of each new vertex `b in B` into `E union B`.

   There is a stronger labelled outside-packet statement that avoids the chamber pigeonhole.  Put
   `U=V(H)\W` and `tau(b)=deg_W(b) [MOD 4]`.  If `m<n/32`, then `|U|>31m`, and it is enough to find
   nonempty `B subset U` and `delta` with

   ```text
   deg_B(w)=delta              for all w in W,
   deg_B(b)+tau(b)=r+delta     for all b in B.
   ```

   Olson on all of `U` gives an old-balanced packet `B_0` of size `>28m`.  A class of
   `deg_{B_0}+tau` has size `>7m`, but old-balance is not inherited by that class.  If old-balance is
   restored after two ordinary four-way refinements, the available pool is only `>7m/4`, below the
   no-deletion `3m` threshold.  With deletion, the exact final inequality is

   ```text
   7m/4 - 3(m-d-1) > d
   ```

   which requires `d>5m/8-O(1)`.  Thus this is a useful formal endpoint only if paired with a real
   terminal self-layer lemma that preserves old-balance.

   In kept-old notation `E=W\D`, the replacement conditions are simply

   ```text
   deg_E(w)+deg_B(w)=R          for every w in E,
   deg_E(b)+deg_B(b)=R          for every b in B,
   |E|+|B|>m.
   ```

   The final formal lemma should not choose `E` and `B` independently.  After the exposed refinements,
   the outside pool has size only `>7m/4`; choosing `E` first leaves a best label fiber of size
   `>7m/16`, forcing `|E|>9m/16`, while choosing `B` first and rebalancing old coordinates needs
   `|E|<3m/8+O(1)`.  The disjoint ranges identify the true endpoint as a simultaneous two-sided
   absorption lemma.

   The original even-degree theorem also admits a co-absorbing endpoint that should be kept separate
   from the stronger arbitrary-label selector.  If `U=V(H)\W`, one total-degree fiber `T subset U` has
   size `>31m/2`.  For `B subset T`, `C=T\B`, `F=U\T`, and common total-degree residue `s` on `T`,
   the append equations are equivalent to

   ```text
   deg_T(w)-deg_C(w)=delta             for every w in W,
   deg_C(b)+deg_F(b)=s-r-delta         for every b in B.
   ```

   A formal proof could target this co-absorption lemma directly.  The elementary refinement by
   `deg_F` alone only recovers the `>31m/8` chamber scale, so an additional simultaneous argument is
   still required.

   A stronger formal endpoint avoids choosing the `h_0` residue class.  Let `B_0 subset T` be
   old-balanced with `|B_0|>25m/2`, and define `h(b)=deg_W(b)+deg_{B_0}(b)`.  For old-balanced
   `B subset B_0`, with `X=B_0\B` and old increment `delta_B`, the append condition is

   ```text
   theta_X(b):=h(b)-deg_X(b)-delta_B = r       for every b in B.
   ```

   This whole-packet equation should not be combined with cardinal-maximal old-balance: `B_0` itself
   is old-balanced, so the maximum old-balanced subset is `B_0` and the complement is empty.  A
   zero-sum-free boundary only appears after restricting to a piece such as the `h_0`-class `C`, or
   after adding a value-correct extremality condition.

   The signed-Olson normalization sharpens but does not close this route.  Old-balancing a packet
   `B_0 subset T` gives `|B_0|>|T|-3(m-1)>25m/2`; a class of
   `deg_{B_0}(b)+deg_W(b)` has size `>25m/8`, just above `3m`.  Rebalancing after taking that class
   leaves only `>m/8`, and signed rebalancing with old negatives no longer forces the positive side to
   outnumber the old deletions.  Therefore the formal co-absorption target must keep the large
   self-layer class while regularizing old coordinates simultaneously.

   The class form can be stated without mentioning internal self-layer edges.  If `B_0` is
   old-balanced, `h_0(b)=deg_W(b)+deg_{B_0}(b)`, `C` is a residue class of `h_0`, and `R=B_0\C`, then
   for any `B subset C`

   ```text
   deg_W(b)+deg_B(b)=h_0(b)-deg_R(b)-deg_{C\B}(b).
   ```

   Hence the terminal formal lemma is a value-coupled old-balanced co-cut lemma: find nonempty
   old-balanced `B subset C`, with old increment `delta_B`, such that
   `deg_R(b)+deg_{C\B}(b)=H-r-delta_B` on `B`.  In the even-specific route, `|C|>25m/8`, so the
   class is only barely above the old-coordinate Davenport threshold.  Equivalently, with
   `q_C(b)=deg_C(b)+deg_R(b)`, find old-balanced `B subset C` such that

   ```text
   deg_B(b)=q_C(b)-(H-r-delta_B)       for every b in B.
   ```

   On this class the labels satisfy `q_C(b)=h_0-deg_W(b)`, so the formal lemma should include the
   coupling between the prescribed residue, the old-neighbourhood vector, and `delta_B`.

   The signed version should be stated separately.  For `D subset W`, `E=W\D`, and `B subset C`,
   the old side asks for `deg_B(w)-deg_D(w)=K` on `E`, while the new side is

   ```text
   deg_R(b)+deg_{C\B}(b)+deg_D(b)=H-r-K        for every b in B,
   |B|>|D|.
   ```

   The numerical warning is important for formalization: since `|C|` is only `>25m/8`, a blind
   signed-Olson step on `C` can leave too few positive vertices to dominate `D`.  The formal endpoint
   must either be append-only on `C` or explicitly preserve positive surplus in the signed co-cut.

   The append-only formal endpoint can use the discard variable `X=C\B`:

   ```text
   deg_X(w)=deg_C(w)-K                 for every w in W,
   deg_X(b)=H-r-K-deg_R(b)             for every b in C\X,
   X != C.
   ```

   This avoids circular references to `B` and states the remaining problem as a one-sided prescribed
   co-degree selection theorem for a proper discard set.

   A sharper formal endpoint chooses `B subset C` maximal among old-balanced subsets and sets
   `X=C\B`.  Then `X` is zero-sum-free in `(Z/4Z)^(W\{w_0})`, hence `|X|<=3(m-1)` and
   `|B|>|C|-3(m-1)>m/8`.  Since `B` is old-balanced, the old equation for `X` is automatic; the only
   remaining condition is the value-coupled label equation

   ```text
   eta_X(b)=deg_X(b)+deg_R(b)=H-r-delta_B.
   ```

   Thus the last obstruction can be formalized as a zero-sum-free boundary exchange lemma: some
   maximal old-balanced complement must satisfy this value-coupled `eta_X` equation, or else one can
   exchange vertices across the zero-sum-free boundary to get a profitable packet.

   The exchange lemma has the following local equations.  Given `C=B disjoint_union X`, move
   `Y subset B` to the discard side and `Z subset X` to the retained side.  The old-balance condition is

   ```text
   sum_{z in Z} p_z = sum_{y in Y} p_y       in (Z/4Z)^(W\{w_0}),
   ```

   and the new co-cut labels are

   ```text
   eta_{X'}(u)=eta_X(u)-deg_Z(u)+deg_Y(u)       for u in B\Y,
   eta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)   for z in Z.
   ```

   For the value-coupled statement, also track

   ```text
   delta_{B'}=delta_B+deg_Z(w_0)-deg_Y(w_0),
   theta_X(v)=eta_X(v)+delta_B.
   ```

   Then

   ```text
   theta_{X'}(u)=theta_X(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0)
                                                       for u in B\Y,
   theta_{X'}(z)=deg_{X\Z}(z)+deg_Y(z)+deg_R(z)+delta_{B'}
                                                       for z in Z.
   ```

   The desired value is the fixed residue `H-r`, not merely an arbitrary constant.

   The pure-discard case `Z=empty` just recurses inside `B`; a closing proof must use a nonempty
   `Z` from the zero-sum-free boundary.

   For a minimal formal counterexample, choose `B` lexicographically: maximum cardinality among
   old-balanced subsets of `C`, then maximum target fiber
   `{b in B : theta_X(b)=H-r}`.  Then no balanced exchange `(Y,Z)` has `|Z|>|Y|`, and no balanced
   exchange with `|Z|=|Y|` improves the updated target fiber.  This target-stable zero-sum-free
   boundary is the strongest local obstruction to state before proving the exchange lemma.

   If `T={b in B : theta_X(b)=H-r}`, the formal target-stability inequality for every equal-size
   balanced exchange is

   ```text
   |{u in B\Y : theta_{X'}(u)=H-r}| + |{z in Z : theta_{X'}(z)=H-r}| <= |T|.
   ```

   In particular, singleton swaps in one old-vector class become concrete no-improving-swap constraints
   on the two swapped vertices' retained-side neighbourhoods.

   For a same-old-vector singleton swap, this can be formalized as `gain(y,z)<=loss(y,z)`: gains are
   non-target retained vertices shifted to `H-r` plus the imported vertex if it lands at `H-r`; losses
   are target retained vertices shifted away plus the exported vertex if it was target.  This is the
   local counting form of target-stability.

   Do not record a separate zero-sum-free claim for the `eta_X`-fibers.  If
   `S subset B` is old-balanced and `eta_X` is constant on `S`, appending `S` changes the discard set
   from `X` to `X union (B\S)`.  The needed label is

   ```text
   eta_{X union (B\S)}(s)=eta_X(s)+deg_{B\S}(s),
   ```

   and the old increment changes to `delta_S`.  Thus the pure-discard case is recursive and closes
   only when the value-coupled label

   ```text
   theta_{X union (B\S)}(s)=eta_X(s)+deg_{B\S}(s)+delta_S
   ```

   equals `H-r` on `S`.

   If both `S` and `B\S` are old-balanced, this can be recorded as the block-interaction equation

   ```text
   theta_{X union (B\S)}(s)=theta_X(s)+deg_{B\S}(s)-delta_{B\S}.
   ```

   A terminal counterexample must make every old-balanced block `S subset B` fail equality to `H-r`
   on all of `S`.

   If `B=S_1 disjoint_union ... disjoint_union S_l` is a decomposition into old-balanced blocks with
   increments `delta_i`, then block `S_i` exits precisely when

   ```text
   theta_X(s)+sum_{j != i} (deg_{S_j}(s)-delta_j)=H-r       for every s in S_i.
   ```

   This is the block-interaction normal form of the pure-discard recursion.

   The boundary `X` is zero-sum-free in `C_4^(m-1)`, with the sharp Davenport bound
   `|X|<=3(m-1)`.  A possible formal route is therefore an inverse-Davenport split: either `|X|` is
   bounded away from extremal, giving extra retained mass for the block-interaction argument, or `X`
   has the near-extremal basis-like structure of a zero-sum-free sequence in `C_4^(m-1)`, allowing the
   exchange equations to be checked on explicit coordinate imports.

   Another formal normal form decomposes `B` into minimal old-balanced blocks.  Each block `S` exits by
   pure discard precisely when

   ```text
   theta_X(s)+deg_{B\S}(s)-delta_{B\S}=H-r       for every s in S.
   ```

   If all minimal blocks fail, any successful repair must import a nonempty `Z subset X` and export a
   subset of `B` with the same old-coordinate sum.  This is the exchange-basis form of the terminal
   lemma.

   For a minimal block `S`, define

   ```text
   phi_S(s)=theta_X(s)+deg_{B\S}(s)-delta_{B\S}-(H-r).
   ```

   Pure discard closes exactly when `phi_S=0`.  A local import with `Y subset S`, nonempty
   `Z subset X`, and `sum p_Z=sum p_Y` changes the defect on `u in S\Y` by

   ```text
   phi_{S'}(u)=phi_S(u)-deg_Z(u)+deg_Y(u)+deg_Z(w_0)-deg_Y(w_0).
   ```

   This is the value-coupled zero-sum exchange equation for a final local proof.

   The defect can also be simplified before formalization.  Since

   ```text
   theta_X(s)+deg_{B\S}(s)-delta_{B\S}=deg_{B_0\S}(s)+delta_S
   ```

   and `H=deg_W(s)+deg_{B_0}(s)` on the class `C`,

   ```text
   phi_S(s)=r+delta_S-deg_W(s)-deg_S(s).
   ```

   Therefore a zero-defect block is exactly an old-balanced atom that appends to `W`; the boundary
   exchange is only a construction mechanism for such an atom.  The scalar sum identity

   ```text
   sum_{s in S} phi_S(s)=|S|r+(|S|-m)delta_S-2e(S)       [MOD 4]
   ```

   follows from `sum_{s in S} deg_W(s)=m delta_S`, but it is only a necessary condition.  The terminal
   theorem still has to force pointwise vanishing of the defect.

   The signed atom repair criterion is:

   ```text
   deg_D(w)=c                  for every w in W\D,
   deg_D(s)=c-phi_S(s)         for every s in S,
   |S|>|D|.
   ```

   Under these conditions `(W\D) union S` has common residue `r+delta_S-c`.  The append-only atom
   theorem is the `D=empty`, `c=0` case; a signed proof may instead show that every defective atom has
   a smaller old correction `D` satisfying this display.
   Add scalar tests:
   `c(m-|D|)=|D|r-2e(D)` and
   `|S|c=|D|delta_S+sum_{s in S}phi_S(s) [MOD 4]`, equivalently
   `|S|c=|S|r+(|S|-m+|D|)delta_S-2e(S) [MOD 4]`.
   For `|D|=1`, record the pointwise specialization: `c` is `0` or `1`, so either `c=0,r=0` or
   `c=1,r=m-1`, and every `phi_S(s)` lies in `{c,c-1}`.
   For `d=|D|<4`, record the small-deletion spectrum:
   `0<=c<=d`, `phi_S(S) subset {c,c-1,...,c-d}`, and
   `c(m-d)=d r-2e(D) [MOD 4]`.
   For exact-basis direction spectra, add the singleton/pair table.  Singleton: isolated old vertex has
   `c=0,r=0,shift=1_{b_gx}`; complete old vertex has `c=1,r=m-1,shift=1_{b_gx}-1`.  Pair
   `{x,y}` with `e=1_{xy}`, `a=|N_W(b_g) cap {x,y}|`: anticomplete gives `r=e [MOD 2]`, shift `a`;
   split gives `m-2=2(r-e) [MOD 4]`, shift `a-1`; complete gives `m-2=r-e [MOD 2]`, shift `a-2`.

   The class-size margin also allows augmented Olson statements.  Since `|C|>25m/8`, one may add
   `a` fixed `Z/4Z` coordinates to the `m-1` old-difference coordinates whenever
   `3(m-1+a)<|C|`.  In particular, at least one scalar side condition can be imposed on an atom, such
   as `|S|=0`, `delta_S=0`, or `sum_{s in S} deg_R(s)=0` modulo `4`.  This is only scalar control; the
   formal terminal lemma still needs pointwise vanishing of
   `r+delta_S-deg_W(s)-deg_S(s)` on every vertex of the atom.
   For `m>24`, formalize the two-coordinate normalization using constant `1` and anchor adjacency:
   `|S|=0`, `delta_S=0`, hence `sum_S phi_S=-2e(S) [MOD 4]`.

   A formal inverse-Davenport route should include the maximal-boundary sumset separation.  If
   `Sigma_l(X)` is the set of sums of `l` old-vectors from `X`, then cardinal maximality gives no
   exchange `Y subset B`, `Z subset X` with equal old-vector sum and `|Z|>|Y|`; in particular
   `p(B)` is disjoint from all `Sigma_l(X)` for `l>=2`.  In the exact extremal model
   `X={e_i,e_i,e_i}`, this forces every retained old-vector to be `0` or a basis vector `e_i`, since
   every other nonzero element is a boundary sum of length at least two.  The extremal formal case
   therefore reduces to zero-vector singleton atoms and four-copy same-basis atoms, plus their signed
   repair criterion.

   In this exact basis model, the singleton atom with old-vector `0` closes iff `r=0`.  For a feasible
   nonzero basis direction `g`, all retained vertices with `p_b=g` have the same old-neighbourhood
   residue `omega(g)=deg_W(b)`, and any four of them form an old-balanced atom with

   ```text
   phi_S(b)=r-omega(g)-deg_S(b).
   ```

   Hence the four-copy atom closes exactly when those four vertices induce the required regular
   four-vertex graph.  This finite catalogue is a reduction, not a proof: formal closure still needs a
   maximality or signed-repair argument forcing one required regular type.

   A caveat for the signed route: within one nonzero basis direction, all four vertices have the same
   old neighbourhood in `W`, so `deg_D` is constant on them for every `D subset W`.  Therefore signed
   deletion can repair such an atom only if the defect was already constant, equivalently if the four
   vertices were already regular.  Nonregular four-copy atoms require cross-direction exchange/import,
   not old deletion alone.

   If the four vertices are regular with the wrong residue, the defect is constant and the signed branch
   becomes a small old-side deletion problem.  For induced degree `d'` and required value
   `d=r-omega(g)`, formalize the repair as existence of `D subset W`, `|D|<4`, and `c` with
   `deg_D(w)=c` for `w in W\D` and `deg_D(b)=c-(d-d')` for the common old-neighbourhood type in the
   direction.  This branch is distinct from nonregular four-block repair.

   It is useful to define a repair spectrum `Rep(g)` of residues `d'` whose regular four-blocks in
   direction `g` are repaired by some such `D`; include the required residue via `D=empty`.  A terminal
   exact-basis fiber avoids regular four-sets for every residue in `Rep(g)`.  If `{0,3} subset Rep(g)`,
   Ramsey bounds that fiber by `R(4,4)`, because those two residues are independent four-sets and cliques.

   The same statement should be available for larger same-direction blocks: if `|S|=0 [MOD 4]` and
   `G[S]` is regular of degree `d' [MOD 4]`, then `S` has constant defect `d-d'`; signed repair asks for
   `D subset W`, `|D|<|S|`, with constant `deg_D` on `W\D` and the shifted constant value on the
   direction's old-neighbourhood type.  Terminal exact-basis configurations must block these larger
   constant-defect repairs too.

   Record also the equivalent kept-old formulation: with `E=W\D`, the condition `deg_D(w)=c` on
   `W\D` is equivalent to `deg_E(w)=r-c` on `E`, so `E` is a smaller congruent induced witness inside
   `W`.  Constant-defect repair is therefore a splice of the outside regular block onto such an `E`,
   with `|S|>|W\E|` and the scalar direction-intersection condition.

   The repair spectrum can be stated by a single formula.  If `d=r-omega(g)` and `deg_D(w)=c` on
   `E=W\D`, then a regular same-direction block of residue

   ```text
   d' = d + deg_D(b_g)-c
   ```

   is repaired, where `b_g` is any vertex with direction type `g`.  For `|D|<4`, formalize the usable
   deletions as singleton/pair/triple subsets whose degree into every kept old vertex is constant; the
   shift is `|N_W(b_g) cap D|-c [MOD 4]`.

   Define `Delta_<(4)(g)` to be the set of these shifts.  Terminality is residue-by-residue:

   ```text
   0 in d+Delta_<(4)(g)  =>  no independent four-set in the direction;
   3 in d+Delta_<(4)(g)  =>  no clique four-set in the direction;
   1 in d+Delta_<(4)(g)  =>  no induced 2K_2 in the direction;
   2 in d+Delta_<(4)(g)  =>  no induced C_4 in the direction.
   ```

   Only the simultaneous presence of both `0` and `3` gives the constant Ramsey bound `R(4,4)`.
   Therefore do not formalize the earlier overstrong claim that a large terminal direction has
   `(d+Delta_<(4)(g)) cap {0,3}=empty` or that its required residue must be `1` or `2`.

   In a middle-residue branch, formalize the first hereditary obstruction as follows: repaired residue
   `1` forbids induced `2K_2`; repaired residue `2` forbids induced `C_4`.  Larger same-direction regular
   blocks provide additional exclusions but are not yet a closure.

   Note the complement symmetry: `2K_2` and `C_4` are complementary four-vertex regular graphs.  If
   both middle residues lie in `Rep(g)`, a terminal large fiber must avoid both patterns; any remaining
   hereditary case should be combined with the outside-only maximum constraint, especially for repeated
   cyclic blocks.

   The useful structural import is the pseudo-split characterization of `(2K_2,C_4)`-free graphs.  In
   this branch, a direction fiber decomposes into a clique part, an independent part, and possibly a
   five-cycle core.  Since no clique or independent set inside a chamber can be larger than `m=|W|`, a
   pseudo-split direction fiber has size at most about `2m+5`.  Therefore a direction fiber
   substantially larger than `2m` must have `Rep(g)` missing at least one middle residue.

   The corrected conclusion above the pseudo-split cap is only a spectrum-hole statement: `Rep(g)` must
   miss at least one middle residue, and it cannot contain both extreme residues unless the fiber is
   Ramsey-small.  Singleton rigidity `Rep(g)={d}` or `Delta_<(4)(g)={0}` needs a separate argument and
   should not be formalized from Ramsey alone.
   But since shift `0` is always present, two distinct nonzero shifts force three repaired residues and
   hence either the Ramsey-extreme pair or the middle pseudo-split pair.  Therefore a terminal direction
   with `|C_g|>=R(4,4)` and `|C_g|>2m+5` has `Delta_<(4)(g) subset {0,sigma_g}`.
   Add the shift-addition lemma: disjoint usable deletions of total size `<4` add their constants and
   their shifts.  Hence in the large-fiber branch two disjoint unit-shift deletions are impossible.
   Record the branch split: unit `sigma_g` makes nonzero singleton/pair repairs intersect; `sigma_g=2`
   is the only case where disjoint nonzero repairs can add to zero.
   For unit `sigma_g`, formalize the standard pair-family classification: the nonzero pair repairs are
   a star, or (if no nonzero singleton exists) contained in one old triangle.
   Equivalently, formalize the unit-branch kernel `K_g` with `|K_g|<=3` such that all usable singleton
   or pair deletions disjoint from `K_g` have zero shift.
   For `sigma_g=2`, split old pairs contribute no nonzero shift; only anticomplete pairs inside
   `N_W(b_g)` and complete pairs outside `N_W(b_g)` contribute.
   Also record singleton zero-shift constraints in the `sigma_g=2` branch: isolated usable old vertices
   are outside `N_W(b_g)`, and universal usable old vertices are inside `N_W(b_g)`.
   Translate this to repaired residues: unit `sigma_g` leaves only `{0,1}` or `{2,3}` after the large
   exclusions, while `sigma_g=2` leaves only `{0,2}` or `{1,3}`.
   Record the hereditary meanings: `{0,1}` is `alpha<=3` plus `2K_2`-free; `{2,3}` is `omega<=3` plus
   `C_4`-free; `{0,2}` is `alpha<=3` plus `C_4`-free; `{1,3}` is `omega<=3` plus `2K_2`-free.
   Up to complement, only two exact-basis hereditary endpoints remain: unit `sigma_g` gives
   `alpha<=3` and `2K_2`-free, while `sigma_g=2` gives `alpha<=3` and `C_4`-free.
   Add the `C_5` blow-up cap: equal selection from all five clique bags is regular; if one bag has size
   at most `m/5`, adjacent clique caps imply total size at most `11m/5`.  Hence any `C_5` blow-up piece
   larger than `11m/5` already closes.
   Also formalize the stronger self-complementary three-consecutive selector: in the independent-bag
   orientation, any three consecutive bags with total more than `m+3` contain a congruent atom, so a
   terminal cyclic component has total size at most `(5m+15)/3`.
   Add endpoint anchor decompositions: in the `2K_2`-free/`alpha<=3` branch every edge dominates all but
   at most three vertices; in the `C_4`-free/`alpha<=3` branch every nonedge has common-neighborhood and
   common-nonneighborhood cliques, each bounded by `m`.
   Add the equal-wing anchor equation: for anchor pair `p,q`, `epsilon=1_{pq}`, exclusive wings
   `|X|=|Y|=h` have synchronized new-side degrees iff every wing vertex has degree `h+epsilon-1` inside
   `X union Y`; in a nonzero exact-basis direction also require `h` odd for old-balance.  The `h=1`
   local atom forbids cross-edges for edge anchors and cross-nonedges for nonedge anchors.
   Formalize the collapse: unit `sigma_g` endpoints become both `2K_2`-free and `C_4`-free; `sigma_g=2`
   endpoints do too.  Pseudo-split structure then bounds each terminal exact-basis direction by `m+8`.

   In the exact extremal model, each basis direction has three boundary copies `X_i`.  For any retained
   `b` with the same old-vector, `X_i union {b}` is an old-balanced atom.  It closes if the four-set is
   regular of degree `r-omega(g_i)`.  The allowed adjacency pattern from `b` to the fixed triple is
   unique for each required degree: miss an independent triple (`0`), hit only the isolated vertex of a
   one-edge triple (`1`), hit the endpoints of a path triple (`2`), or hit all vertices of a triangle
   (`3`).  A terminal exact-extremal proof obligation is to rule out simultaneous avoidance of these
   allowed `3+1` extensions.

   Formalize the stronger augmented-fiber sieve.  If `C_i` is the retained fiber with old-vector `g_i`,
   then every four-set `Y union Z` with `Y subset X_i`, `Z subset C_i`, `|Y|+|Z|=4`, and `Z nonempty`
   is old-balanced.  It appends whenever

   ```text
   deg_Y(y)+sum_{z in Z}1_{zy}=d_i        for y in Y,
   deg_Z(z)+|N_{X_i}(z) cap Y|=d_i        for z in Z,
   d_i=r-omega(g_i).
   ```

   Thus the exact-basis terminal condition must also exclude mixed `2+2` and `1+3` regular atoms.
   Equivalently, retained vertices are typed by their eight adjacency patterns to the boundary triple,
   and the finite forbidden configurations are the regularity solutions of the displayed equations.
   Moreover, the same augmented four-set is signed-repairable whenever its regular residue lies in
   `Rep(g_i)`, since the defect is constant across a single old-neighbourhood type.  Formal terminality
   should therefore quantify the augmented sieve over all residues in `Rep(g_i)`, not only the
   append-only residue `d_i`.

   The useful finite tables are:

   ```text
   2+2: for Y={x,y}, Z={b,c}, e=1_xy, epsilon=1_bc,
        regularity is equivalent to epsilon=e and the cross square
        ({b,c},{x,y}) being (d_i-e)-regular.

   1+3:
        d_i=0  independent retained triple, all miss x;
        d_i=1  exactly one hitter of x, isolated in the retained triple;
        d_i=2  exactly two hitters of x, and the unique misser is the middle of a P_3;
        d_i=3  retained triangle, all hit x.
   ```

   Equivalent type constraints worth formalizing: for a boundary pair `{x,y}` of status `e`, terminality
   forbids retained edge-status `e` on type-`00` pairs if `d_i-e=0`, on type-`10`/type-`01` pairs if
   `d_i-e=1`, and on type-`11` pairs if `d_i-e=2`.  For a boundary vertex `x`, the miss class has no
   independent triple when `d_i=0`, the hit class has no triangle when `d_i=3`, each hitter's
   non-neighbours in the miss class are independent when `d_i=1`, and each misser's neighbours in the
   hit class form a clique when `d_i=2`.

   In signed form these tables are residue-parametric: replace `d_i` by any repaired residue
   `s in Rep(g_i)`.  For `2+2`, use `q=s-e`; `q=0,1,2` give the type-`00`, type-`10/01`, and type-`11`
   restrictions respectively, while `q=3` has no square solution.  For `1+3`, residue `0` bounds
   independence in every boundary-miss class by `2`, residue `3` bounds clique number in every
   boundary-hit class by `2`, and residues `1,2` give the isolated-hitter/path-middle one-corner
   constraints.

   Useful corollary for rich spectra: if `Rep(g_i)` contains all four residues, then every retained
   boundary type `tau in {0,1}^3` is forced by the `2+2` rules to be a clique, an independent set, or a
   singleton.  For each boundary pair on which `tau` has equal bits, the internal retained edge status
   must be the complement of that boundary-pair status; inconsistent prescriptions bound the type by one
   vertex, while consistent prescriptions make it homogeneous and hence size at most `m` by outside-only
   maximality.  Complementary one-hit type pairs are also forced complete or empty.

   Shape-specific caps: if the boundary triple has one or two edges, then types `000` and `111` have
   inconsistent prescriptions and size at most one, while the other six types are homogeneous; the signed
   `3+1` rule forbids the one homogeneous type that completes the boundary triple to its regular residue,
   giving `|C_i|<=5m+2`.  If the boundary triple is independent, repaired residue `0` forbids type
   `000`, all other types are cliques, and repaired residue `3` bounds them by two vertices, giving
   `|C_i|<=14`.  The triangle case is complementary and also gives `|C_i|<=14`.

   Large-fiber normal form to formalize after the above corrections: if
   `|C_i|>max(R(4,4),5m+2)`, then `Rep(g_i)` has at most two residues and contains neither `{0,3}` nor
   `{1,2}`.  Three residues always contain one of those complementary pairs; four residues are excluded
   by the full-spectrum augmented cap.  Thus a very large direction has spectrum contained in one of
   `{0,1}`, `{0,2}`, `{3,1}`, `{3,2}`, or is a singleton.  This is the correct replacement for the false
   singleton-spectrum rigidity.

   The two-residue spectra translate to hereditary branches:

   ```text
   {0,1}: alpha(C_i)<=3 and 2K_2-free;
   {0,2}: alpha(C_i)<=3 and induced-C_4-free;
   {3,1}: omega(C_i)<=3 and 2K_2-free;
   {3,2}: omega(C_i)<=3 and induced-C_4-free.
   ```

   Complementation swaps the first/last and middle two cases, so only two sparse branches remain up to
   complement before the augmented boundary-type constraints are added.

   Warning: do not formalize the earlier `2K_2` sparse-colouring shortcut.  The statement
   `2K_2`-free and `alpha<=3 => chi<=omega+1` is false: the join of two `C_5`'s is `2K_2`-free with
   `alpha=2`, `omega=4`, and `chi=6`, and joins of `k` copies have `omega=2k`, `chi=3k`.  Thus the
   `{0,1}` and `{3,2}` branches require a congruent-degree selector argument after complementing to
   induced-`C_4`-free graphs with clique number at most `3`; colouring alone is not enough.  The safe
   replacement invariant is: in any terminal complement of this branch, every induced `Delta<=2`
   subgraph has size at most `11m/5`, by the same degree-two path/cycle argument.

   For the C4 branch, the augmented boundary rules give an internal cap: if
   `{0,2} subset Rep(g_i)` and `X_i` is independent, then type `000` is forbidden and the other seven
   boundary types are cliques, so `|C_i|<=7m`.  Complementarily, `{3,1}` plus a triangle boundary gives
   `|C_i|<=7m`.

   Residual `{0,2}` exceptional types by boundary shape: if `X_i` has one edge `xy` and isolated vertex
   `z`, all types except `001` and `110` are cliques.  If `X_i` is a path `x-y-z`, all types with equal
   endpoint bits are cliques and type `101` is forbidden by the residue-`2` `3+1` atom, leaving only the
   four unequal-endpoint types exceptional.  If `X_i` is a triangle, the pair rules are cross-type only;
   this is the hardest remaining shape.  Complement these statements for the `{3,1}` branch.

   In that triangle-boundary `{0,2}` case, formalize the cube anti-join system:

   ```text
   10* anti-joins 01*,
   1*0 anti-joins 0*1,
   *10 anti-joins *01.
   ```

   Also formalize `alpha(M_x)<=2` for every miss class and the one-corner rule that each misser's
   neighbourhood in the corresponding hit class is a clique.  This finite eight-type cube is the residual
   sparse C4 surface; the independent-boundary `{3,1}` case is its complement.

   The anti-join graph on boundary types is the distance-at-least-two graph on the 3-cube.  Its even and
   odd parity classes are four-cliques.  Since four pairwise anti-joined nonempty types would give an
   independent four-set, a terminal direction must omit at least one even type and at least one odd type;
   the residual cube has support on at most six types.

   Also formalize the cube-face C4 condition.  In every square face
   `tau, tau+e_a, tau+e_b, tau+e_a+e_b`, the diagonals are anti-complete, so any alternating four-edge
   cycle around the face is automatically an induced `C_4`.  Therefore the four side bipartite graphs of
   each nonempty face must contain no compatible alternating cycle; if three side pairs are complete and
   all corner types are nonempty, the fourth side pair is empty.

   The finite support dichotomy: with six nonempty types, the omitted even and odd types are either
   adjacent or antipodal.  Adjacent omissions leave full square faces and trigger the face condition.
   Antipodal omissions leave the induced six-cycle of the cube and no full square face.  Otherwise the
   support has size at most five.

   Also formalize parity-count compression: distinct same-parity types are pairwise anti-complete.  If
   three types of one parity are nonempty, each such type class is a clique; otherwise an independent pair
   in one type plus one vertex from each of the other two gives an independent four-set.  Therefore
   support size six gives `|C_i|<=6m`, support size five leaves only two exceptional classes after a
   `3m` clique-bounded part, and support size at most four is the final small-support case.

   In support size five, the two exceptional classes have the same parity and are anti-complete.  They
   cannot both contain independent pairs, so one is also clique-bounded; support five reduces to a `4m`
   clique-bounded part plus one possible nonlinear type class with `alpha<=2`, induced-`C_4`-free, clique
   number at most `m`, and no outside-only congruent induced subgraph larger than `m`.  Complementing
   that type class gives a triangle-free, induced-`2K_2`-free graph `H`; this corrects the earlier false
   "C4 is self-complementary" wording.  Since `deg_G[S](v)=|S|-1-deg_H[S](v)`, mod-4 congruent induced
   sets are preserved by complement up to a constant shift.

   Formalize the structure of triangle-free `2K_2`-free graphs: bipartite connected components are chain
   graphs, while non-bipartite connected components are blow-ups of `C_5`.  For a `C_5` blow-up with
   class sizes `a_1,...,a_5`, summing the nonconsecutive-pair independence inequalities gives
   `2|H_j|<=5 alpha(H_j)`.  Also formalize the three-consecutive-class selector: capacities `A,B,C`
   contain selected sizes `x,y,z` with `y=x+z [MOD 4]` and total at least `A+B+C-3`, so terminality forces
   every cyclic triple to have size at most `m+3`.
   For support at most four, either a full square face triggers the face-C4 condition, or the support is
   a cube forest of at most four type classes.  In the cube-forest case, formalize the parity compression:
   at most one type of each parity is nonlinear, and if two nonlinear opposite-parity types survive they
   must be adjacent in the cube.  If the adjacent edge shares a zero coordinate, its union is already an
   `alpha<=2`, induced-`C_4`-free instance and complements to the one-type chain/C5 selector.  Therefore
   the only possible new small-support residual is the top edge `111`--`110` up to symmetry, where each
   lower-type vertex has clique neighbourhood in the all-hit type; all other classes are clique-bounded.
   This top edge reduces further: if the lower type has an independent pair, the all-hit side is covered
   by two clique neighbourhoods plus a common non-neighbour clique, so has size at most `3m`; if the
   lower type is a clique, it is `m`-bounded and the all-hit one-type branch is the only remaining part.
   The all-hit branch is capped by formalizing/importing Wagon's bound `chi<=binom(omega+1,2)` for
   `2K_2`-free graphs after complementing; with `omega<=3` and `alpha<=m`, it has size at most `6m`.
   For the remaining cube-star spill shape, formalize the pair-covering constraint: if `T` is the
   nonlinear centre and `L_1,L_2,L_3` are the same-parity clique leaves, then every independent pair in
   `T` has common non-neighbours in at most one leaf.  Hence at least two leaves are covered by the two
   clique neighbourhoods of that pair.  The crude resulting constants already close the finite cube
   residual: support six is at most `6m`, support five is at most `13m/2`, support at most four is at
   most `11m/2`, and the top-edge subcase is at most `6m`.  Thus the triangle-boundary `{0,2}` and
   complementary `{3,1}` directions are bounded by `7m+O(1)`.  The remaining large hereditary surface is
   the corrected `{0,1}`/`{3,2}` complement selector: induced-`C_4`-free, `K_4`-free, independence at
   most `m`, and no induced degree-two regular selector larger than `m`.

   Do not try to close the `{0,1}`/`{3,2}` residual by adding more local mixed-table cases alone.  There is
   a one-type local model: with triangle boundary and all retained vertices of type `110`, the signed
   `Rep={0,1}` mixed rules impose no extra same-type restriction beyond the retained-only
   `alpha<=3`, `2K_2`-free branch.  The branch is closed only after importing target-stability and the
   mod-`4` endpoint-exclusive layer theorem below.
   Formalize the singleton-swap label-gradient lemma: with `A_j={theta=L+j}` and a same-old-vector
   boundary copy whose retained-type adjacency is the constant `epsilon`, target-stability gives
   `epsilon=0 => |N(y) cap A_{-1}|<=|N(y) cap A_0|+1` and
   `epsilon=1 => |A_1\N(y)|<=|A_0\N(y)|+1` for every retained export `y`.
   Also formalize the two-boundary-copy label-gradient lemma: if the imported boundary pair has constant
   adjacency sum `t` to the retained type and the exported retained pair is `Y`, then
   `theta'(u)=theta(u)+deg_Y(u)-t` and
   `sum_k |{u in A_{t-k}: deg_Y(u)=k, t-k !=0}| <= sum_{k!=t}|{u in A_0:deg_Y(u)=k}|+O(1)`.
   Generalize this to any imported boundary subpacket of size `s<=3`, with error `O(s)`; for the model
   type `110`, importing the full boundary triple has `t=2` and controls all three off-target layers.
   Deduce the empty-target corollary for a type with a miss and two hits: if `A_0=empty`, then
   `|A_{-1}|<=3`, `|A_1|<=m`, and `H[A_2]` has maximum degree at most one, so the same-type residual is
   at most `2m+O(1)`.
   For the nonempty target layer, formalize the pure-discard slice criterion: in
   `D_q={u in A_0: deg_B(u)=q [MOD 4]}`, any four-set closes by pure discard exactly when it induces the
   regular four-vertex graph of degree `q-delta_B`; terminality forbids that pattern in `D_q`.
   Also formalize the mixed-colour form: with `c(u)=deg_B(u)-delta_B`, no four-set `S subset A_0` has
   `deg_{G[S]}(u)=c(u)` for all `u`.  Consequences: colour `3` is Ramsey-bounded, colour `2` is
   pseudo-split and `2m+O(1)`-bounded, and an independent pair in colour `0` dominates all but at most
   three vertices of colour `1`.
   Strengthen the last item in complement form: for a colour-`0` nonedge `ab` (an edge in `H`), the
   colour-`1` common neighbourhood of `ab` in `H` has size at most one; the exclusive layers
   `N_H(a)\N_H(b)` and `N_H(b)\N_H(a)` inside colour `1` are anti-complete, triangle-free,
   induced-`C_4`-free, and have alpha-sum at most `m`; their first-core pendant fibres have total size at
   most `3m` by the distance-three quotient lemma.  Record the dichotomy: either colour `0` is a clique
   and `m`-bounded, or a colour-`0` nonedge gives this edge-anchor decomposition; in both cases the
   remaining large target mass is zero-trace.
   Also record the irreducible local core: all off-target layers empty and target layer contained in
   colour `1`.  Then target-stability is vacuous and the only visible local condition is the
   induced-`2K_2` exclusion, equivalently an induced-`C_4`-free, `K_4`-free complement with
   `alpha<=m` and no induced `Delta<=2` selector larger than `11m/5`.
   Add the edge-robust sharpening: every complement edge `ab` has common neighbourhood of size at most
   two and decomposes the graph into controlled exclusive layers plus `Z_ab`; any superlinear core must
   have large `Z_ab` for every edge.
   Add the maximal induced-matching skeleton: a maximal induced matching has at most `m/2` edges; the
   vertices anti-complete to all matching endpoints are independent and have size at most `m`; all
   remaining vertices lie in endpoint neighbourhoods whose common/exclusive parts have the edge-anchor
   structure.  Formalize the endpoint-exclusive charging lemma
   `sum_i(|E_i^a|+|E_i^b|)=O(m)` for assigned exclusive classes of the matching edges.
   Record that the true standalone layer theorem is stronger than the visible induced-`Delta<=2` shadow:
   triangle-free induced-`C_4`-free `F` with `alpha(F)<=m` and no nonempty induced
   `S` of size `0 mod 4` whose degrees are all `2 mod 4` must have `|F|=O(m)`.
   Formalize the proof: recursively choose shortest odd cycles in zero-trace layers; pendant fibres over
   each core have total size at most `3m`; the chosen cores are pairwise anti-complete, and no zero-sum
   subfamily of their odd lengths is allowed, so at most three cores occur.  With total core length
   `<=11m/5` and final bipartite layer `<=2m`, get `|F|<=66m/5`.
   Within that complement class, formalize the triangle-anchor trace lemma: for a triangle `abc`, no
   outside vertex is adjacent to all three anchors; vertices with incomparable nonempty traces into
   `{a,b,c}` are anti-complete; the two-neighbour trace classes are independent; singleton trace classes
   are pairwise anti-complete and are themselves triangle-free induced-`C_4`-free graphs.  Also formalize
   the immediate budgets `|P_ab|+|P_ac|+|P_bc|<=m` and
   `alpha(S_a)+alpha(S_b)+alpha(S_c)<=m`.  If a singleton layer is non-bipartite, its shortest odd cycle
   is induced; chosen odd-cycle cores in the pairwise anti-complete singleton layers have total length at
   most `m`, by the induced degree-two terminal exclusion.  For such a shortest odd cycle `C` in a
   triangle-free induced-`C_4`-free layer, formalize that every outside vertex has at most one neighbour
   on `C`, and that pendant fibres over consecutive cycle vertices are anti-complete.  Strengthen this to
   the distance-three quotient lemma: pendant fibres can be adjacent only when their core vertices are at
   cyclic distance `3`; the quotient has fractional chromatic number at most `3`, giving first-core
   pendant-fibre mass at most `3 alpha(layer)`.
   For the iterated zero-trace process, formalize the bounded-skeleton lemma: successive edge, triangle,
   or shortest-odd-cycle anchors chosen inside zero layers are pairwise anti-complete, so their union is an
   induced graph of maximum degree at most two and has total size at most `11m/5`.

   The retained-only subcase is the old four-copy obstruction: every four vertices in one exact direction
   fiber `C_i` are old-balanced, and they close precisely when they induce the specified
   `d_i`-regular four-vertex graph with
   `d_i=r-omega(g_i)`.  The exact basis branch has therefore been reduced to direction fibers avoiding
   one specified regular four-vertex induced pattern; this finite obstruction still needs global
   maximality or a non-basis import to become contradictory.

   Direction fibers are not independent in a multi-block atom.  If `S_i subset C_i` is a four-vertex
   block and `a_i(s)=r-omega(g_i)-deg_{S_i}(s)`, then a union `S=union_i S_i` closes exactly when

   ```text
   sum_{j != i} deg_{S_j}(s)=a_i(s)       for every s in S_i.
   ```

   Thus the exact basis branch can be formalized as an interacting four-block correction problem.

   Do not attempt to prove this branch from the finite atom catalogue alone.  A local model with all
   required residues `d_i=0`, clique direction fibers, and no cross-edges has no closing union of
   same-direction four-blocks: every old-balanced selection uses multiples of four vertices per
   direction, so each selected vertex has internal degree `-1 mod 4`.  Formal closure must use global
   maximum-witness information or a non-basis exchange.
   However, the large version of that toy model is excluded by outside-only maximality: four vertices
   from each of `t` clique directions form an outside-only congruent set of residue `3`, so `4t<=m`.
   More generally, any selected block family with constant total row-sum residue and size `>m`
   contradicts maximality of `W`.
   Formalize the wrong-residue block reservoir: every direction fiber of size at least `R(4,4)` that
   avoids its append residue still contains a regular four-block of another residue.  The terminal
   retained-only branch is therefore a dual-exit bounded-block selector: wrong-residue blocks must not
   repair to the append residue and must not synchronize to a large outside-only residue.

   Also formalize the amplified version.  For every fixed `L == 0 [MOD 4]`, replacing four-blocks by
   `L`-vertex clique or independent blocks gives the same append/outside-only equations with internal
   residue `q_i in {0,3}` and surplus threshold `sum |P_i|>m`.  Thus a terminal configuration has no
   no-cross same-residue family of such blocks of size greater than `m/L`.  This closes only the heavy
   homogeneous reservoir toy models; the sparse-import regime remains and must use boundary triples
   `X_i` via outside-only maximality or explicit coordinate exchange.

   The sparse endpoint should be recorded as a finite-alphabet selector.  For every direction
   `A_i=X_i union C_i`; a word is `P_i subset A_i`.  Outside-only terminality forbids word families with
   `q_i(P_i,v)+sum_{j != i}deg_{P_j}(v)=Q` on every selected `v` and total size `>m`.  Append/import
   terminality is the same row-sum equation together with the old-coordinate condition
   `|P_i|=0 [MOD 4]` in every basis direction and the append residue relative to `W`.  This is the
   formal sparse-import target after the amplified heavy-reservoir branch is removed.

   Compressing four-blocks gives a bounded-block version of the original row-sum selector: each block
   has a four-coordinate defect vector, and each block pair has a `4 by 4` cross-adjacency matrix.  A
   selected block family must make selected cross-matrix row sums equal the defect vectors.  Thus this
   reduction is useful only together with boundary-triple provenance or maximum-witness constraints; as
   an abstract formal target it is circular.

   Add the outside-only maximum constraint as a separate formal obstruction.  Since `W` is
   cardinal-maximum, no subset of `C` alone can induce congruent degrees modulo `4` on more than `m`
   vertices.  For regular direction blocks `P_i` with internal residues `q_i`, this forbids any selected
   block family of total size `>m` satisfying

   ```text
   q_i + sum_{j != i} deg_{P_j}(v)=Q        for every v in P_i.
   ```

   This rules out local no-cross clique countermodels with many directions, because four vertices from
   each of more than `m/4` clique directions already form an outside-only residue-`3` witness.  Formal
   closure may use this outside-only constraint in addition to appendable old-balanced atoms.

   The boundary alone gives a sharper critical version: no `Y subset X` with `|Y|>m` can have all
   induced degrees congruent modulo `4`.  In the exact basis model, for subpatterns
   `P_i subset X_i` of the boundary triples, formalize the forbidden boundary-only selection as

   ```text
   q_i(v)+sum_{j != i} deg_{P_j}(v)=Q        for every selected v in P_i,
   sum_i |P_i|>m.
   ```

   Hence terminal exact-basis boundaries cannot have large cross-isolated collections of independent
   triples or triangle triples, since selecting those whole triples would already beat `W`.
   Strengthen this to all triple types: a cross-isolated family of `t>2m/3` boundary triples is
   impossible.  If `a` of them are triangles and `3a>m`, take those whole triangles for residue `2`;
   otherwise take a nonedge pair from every non-triangle triple and one vertex from every triangle,
   giving a residue-`0` outside-only set of size `2(t-a)+a>m`.
   The same cap holds for cross-complete families by complementing the induced graph on the family:
   congruent degrees in the complement translate to congruent degrees in `G` via
   `deg_G[S](v)=|S|-1-deg_{\bar G[S]}(v)`.
   For homogeneous cross-interaction on non-triangle triples, formalize the quotient lemma: if `Q[U]`
   is even, choosing a nonedge pair from each triple in `U` gives a residue-`0` outside-only selector of
   size `2|U|`.  Hence terminality implies `even_selector(Q)<=m/2`.  If `2|U|>=m-1`, an outside
   non-triangle triple that is cross-empty to all of `U` augments by a nonedge pair; if it is
   cross-complete to all of `U` and `|U|` is odd, the same augmentation gives residue `2`.
   Strengthen the pair-word quotient lemma: it requires constant quotient degree parity, not evenness.
   A two-vertex regular word of internal residue `q_pair` gives final residue
   `q_pair+2 deg_Q(i) [MOD 4]`; use `q_pair=0` for non-triangle nonedge pairs and `q_pair=1` for
   triangle edge pairs.
   Gallai's even/even partition gives a pair-word selector of size at least `2 ceil(n/2)` in a
   same-residue homogeneous class of `n` triples.  Near the exact basis boundary, the only deficits are
   size `m` when `m` is even and size `m-1` when `m` is odd (with `n=m-1`); residual work is an
   augmentation obstruction.
   Formalize the one-word augmentation test: for a pair selector `U` of residue `R`, an outside regular
   word of size `s` and internal residue `q_j` with uniform quotient adjacency `a in {0,1}` appends iff
   `q_j+2a|U|=R+as [MOD 4]`.  The odd-`m` deficit may also need a two-word weighted-column check.
   The exact condition is more general: for base selector `S`, one word `P` appends iff
   `deg_P(x)=K` on `S` and `deg_P(u)+deg_S(u)=R+K` on `P`; for two words `P,Q`, replace the first
   condition by `deg_P(x)+deg_Q(x)=K` and the second by
   `deg_P(u)+deg_Q(u)+deg_S(u)=R+K` on `P union Q`.
   For a single outside direction `A_j=X_j union C_j`, formalize this as a bounded augmented-fiber
   catalogue: the old `3+1`, `2+2`, and `1+3` tables apply with append residue replaced by `R+K` and
   with the extra base-column term.
   For two words `j,k`, record the equations
   `s_j a_j(i)+s_k a_k(i)=K` on `U`, and
   `q_j+2 sum_U a_j+b s_k=q_k+2 sum_U a_k+b s_j=R+K [MOD 4]`.
   Retained singletons are outside words with `s=1,q=0`; one retained singleton requires pair-uniform
   adjacency to all selected boundary pairs and satisfies `2a|U|=R+a [MOD 4]`.  Two retained
   singletons are governed by the same two-column equations: complementary columns, both-zero columns,
   or both-one columns, plus the displayed column-sum congruences.
   Expand this as the table: single all-zero requires `R=0`; single all-one requires
   `R=2|U|-1`; two both-zero requires mutual edge `b=R`; two both-one requires
   `2|U|+b=R+2`; complementary columns require `|U|` even and `2alpha+b=R+1`.
   The all-zero retained trace class is empty for `R=0` and independent for `R=1`; the all-one class
   follows by the shifted residue `R+2-2|U|`; complementary classes avoid the specified edge status when
   it is `0` or `1`.
   Also formalize the full non-pair-uniform two-retained equation: for selected pairs `{x_i,y_i}`,
   retained `z,z'` augment iff a common `K` satisfies
   `zx_i+z'x_i=zy_i+z'y_i=K` for all `i`, and
   `deg_U(z)+b=deg_U(z')+b=R+K [MOD 4]`.  Nonuniform columns can only occur in bitwise complementary
   retained pairs.
   Equivalent trace formulation: with `t_z(i)=(zx_i,zy_i)`, an augmenting retained pair must satisfy
   `t_z(i)+t_z'(i)=(K,K)` on every selected pair; non-pair-uniform traces force the affine complement
   trace, and then only the total-degree congruence remains.
   Record the parity split: pair-only selectors cannot mix non-triangle and triangle pair classes,
   because size-two words contribute only even cross-degrees.  Mixed-class selectors must use odd-size
   singleton or whole-triple words.
   For those odd words, formalize the linear carry equation on a quotient parity class `U`: with
   `tau_i=0` on independent triples and `tau_i=1` on triangle triples, choosing whole triples on
   `T` and singletons elsewhere gives congruent degrees iff
   `floor(deg_{Q[U]}(i)/2)+deg_T(i)+tau_i 1_{i in T}` is constant modulo `2`; the selector size is
   `|U|+2|T|`.
   Let `M_U=A(Q[U])+diag(tau)`.  If one solution exists, every kernel vector toggles solutions, so
   terminality implies `|H|<=m-|U|` for all `H in ker M_U`; a large kernel vector closes.  If no constant
   bit is soluble, record the dual obstruction as a kernel vector witnessing affine inconsistency.
   Formalize the support compression for a soluble terminal branch: for `J=union supp(H)` over
   `ker M_U`, averaging over the kernel gives `|J|<=2(m-|U|)`.  Outside `J`, affine solutions have fixed
   bits, with at most `(m-|U|)/2` forced ones in a terminal soluble branch.
   Formalize the exact dual criterion: with `r_i=floor(deg_{Q[U]}(i)/2)`, some constant bit `c` solves
   `M_U 1_T=r+c1_U` iff no even-weight `H in ker M_U` has `sum_{i in H} r_i=1 [MOD 2]`.
   Unpack this as a parity-closed certificate: `deg_H(i)=0` off `H`, `deg_H(i)=tau_i` on `H`, `|H|`
   even, and the half-degree sum over `H` odd.
   Add the minimal Arf-kernel normal form.  If an affine-inconsistent quotient is minimal under passing
   to a bad closed support, then its even kernel is exactly `{0,1_U}`.  An even kernel vector with zero
   Arf pairing gives the proper bad support `U Delta K`; one with odd Arf pairing is itself a proper bad
    support.  Therefore `|U|` is even, `1_U in ker M_U`, `sum_U r_i=1`, and `dim ker M_U<=2`; if odd
    kernel vectors exist, they are a complementary pair modulo `1_U`.  Formalize the equivalent
    whole-class parity statement `deg_U(i)=tau_i [MOD 2]` and quadratic bit
    `e(Q[U])-(1/2)|{i:tau_i=1}|=1 [MOD 2]`.
   Formalize the no-twisted-twins corollary: for `|U|>2`, equal columns of `M_U` would put
   `e_i+e_j` in the even kernel, contradicting `{0,1_U}`.
   In the constant `tau` parity-matched case (`deg_Q(i)=tau [MOD 2]`), `1_U` is in the kernel; if
   `|U|` is odd, some constant bit is always compatible.  The full selector already closes
   constant-type constant-parity quotient sets above `m/2` by pair words, so keep the Arf bit only as a
   below-threshold diagnostic.
   Formalize the exact Davenport top layer if the boundary route is used: Olson's extremal theorem for
   `C_4^r` identifies every zero-sum-free sequence of length `3r` as three copies of a basis.  In that
   endpoint, boundary imports are coordinate count vectors `0<=a_i<=3`; an export of old-sum
   `sum_i a_i e_i` forces exactly `a_i` imports from the `i`-th parallel triple.
   Add the exact-top exchange budget: define `h_X(sum_i a_i e_i)=sum_i a_i` with `0<=a_i<=3`.  If
   `Y subset B` is exported and the forced boundary import has the same old-coordinate value
   `sigma(Y)`, the resulting size is `|B|-|Y|+h_X(sigma(Y))`.  Therefore any graph-compatible exchange
   with `|Y|-h_X(sigma(Y))<|B|-m` closes, and terminality forces the opposite inequality for all
   graph-compatible exports.  Equivalently, for deficit `d=m-|B|>=0`, every compatible export has
   `h_X(sigma(Y))-|Y|<=d`.  This is the finite weighted trace form of the exact-boundary endpoint.
   Formalize the carry identity.  If `sigma(y)=sum_i a_i(y)e_i`, `0<=a_i(y)<=3`, and
   `n_i(Y)=sum_{y in Y}a_i(y)`, then
   `h_X(sigma(Y))-|Y|=sum_y(h_X(sigma(y))-1)-4 sum_i floor(n_i(Y)/4)`.  Hence terminality is equivalent
   to `sum_y(h_X(sigma(y))-1)<=d+4kappa(Y)` for every graph-compatible export.  Carry-free compatible
   exports have total singleton surplus at most `d`; compatible singletons have height at most `d+1`,
   and at deficit zero no compatible carry-free pair can contain two positive-surplus vertices.
   Formalize the complementary-cut bound for old-balanced retained blocks: if `sigma(S)=0`, `Y` is a
   proper cut of `S`, `g=sigma(Y)`, and both `Y` and `S\Y` are graph-compatible exports, then
   `h_X(g)+h_X(-g)=4 supp(g)` and terminality imply `4 supp(g)<=|S|+2d`.  At deficit zero this forbids
   two-sided-compatible cuts in blocks of size below four and restricts four-block cuts to one coordinate.
   Formalize the four-block corollary: if a deficit-zero minimal four-block has all singleton and pair
   cuts two-sided-compatible, then all four old-coordinate values are the same positive boundary basis
   element, so the block is `e_i^4`.  The singleton height test excludes `(-e_i)^4`, because one exported
   `-e_i` imports three boundary copies and gains two vertices.  The positive atom has no boundary-height
   gain on cuts, so its remaining obstruction is purely self-layer residue.
   Formalize the local reroot table for that atom.  With retained atom `S_i=e_i^4` and boundary triple
   `X_i=e_i^3`, set `R_i=S_i union X_i`.  Every size-preserving old-coordinate reroot is a four-set
   `T subset R_i`.  For fixed selected remainder `A`, the full reroot test is existence of `R` such that
   `M_A(a)+deg_T(a)=R` on `A` and `L_A(v)+deg_T(v)=R` on `T`; equivalently, for the omitted triple
   `O=R_i\T`, use `deg_T=deg_{R_i}-deg_O` in both lines.  The positive atom is therefore a seven-vertex
   omission table plus a constant-column condition on `A`.
   Formalize the trace quotient of the column condition: for `p(a)=N(a) cap R_i` and
   `mu(a)=M_A(a)+|p(a)|`, an omitted triple `O` satisfies the remainder line iff
   `mu(a)-|p(a) cap O|` is constant on all occupied labelled trace classes `(p,mu)`.  Hence the local
   endpoint is finite over `{0,1}^7 x Z/4Z` and the `35` omitted triples.
   Add the template normal form: if one trace has two labels, the external condition fails for every
   omitted triple.  Otherwise write the occupied label function as `mu(p)`.  For
   `phi_O(p)=|p cap O|`, the external candidate set is
   `C_ext={O: mu-phi_O is constant on occupied traces}`.  The positive-atom reroot exists iff
   `C_ext` meets the internal candidate set defined by the `E_3` checks.
   Add singleton-trace decoding: if the empty trace is occupied, it fixes `R=mu(empty)`.  Each occupied
   singleton trace `{r}` forces `1_{r in O}=mu({r})-mu(empty) [MOD 4]`; differences outside `{0,1}`
   kill `C_ext`.  If all seven singleton traces are occupied, then there is at most one external
   candidate, and it must have exactly three forced points and satisfy the count formula on every
   occupied higher trace.
   Add the dual decoder: if the full trace is occupied, then each occupied co-singleton `R_i\{r}` forces
   `1_{r in O}=mu(R_i)-mu(R_i\{r}) [MOD 4]`; full trace plus all seven co-singletons again leaves at
   most one candidate.
   Add the multi-template ambiguity law: if two distinct omitted triples `O,O'` are both in `C_ext`, then
   `|p cap (O\O')|-|p cap (O'\O)|` is constant modulo `4` over all occupied traces.  If the empty or full
   trace is occupied, this constant is zero, so every occupied trace must be balanced across that
   symmetric difference.
   In this anchored case, formalize the separation corollary: `C_ext` lies in one equivalence class of
   triples for the map `O -> (|p cap O|)_p`; if occupied traces separate all triples, then `|C_ext|<=1`.
   Also formalize the adjacent-template corollary: if two surviving triples differ by swapping `x` and
   `y`, then every occupied trace has equal incidence on `x` and `y`; hence `x,y` are trace twins, and
   without trace twins anchored `C_ext` is independent in `J(7,3)`.
   Add the packing bound: without trace twins, anchored `C_ext` is a 3-uniform packing on seven points,
   so `|C_ext|<=7`; equality is the Fano `2-(7,3,1)` system.
   Formalize the pairwise equalization criterion: for occupied trace classes `(p,mu),(q,nu)`, an omitted
   triple can equalize them only if `|p cap O|-|q cap O|=mu-nu [MOD 4]`.  With
   `A=p\q`, `B=q\p`, and `C=R_i\(A union B)`, this is equivalent to integers
   `0<=x<=|A|`, `0<=y<=|B|`, `0<=3-x-y<=|C|`, and `x-y=mu-nu [MOD 4]`.  Multiple classes require one
   omitted triple satisfying all such pair constraints and the internal four-set equation.
   Introduce `D_3(a,b)={x-y [MOD 4]:0<=x<=a,0<=y<=b,0<=3-x-y<=7-a-b}`.  Then a pair of trace classes is
   a pairwise blocker iff `mu-nu notin D_3(|p\q|,|q\p|)`.  Record the boundary entries
   `D_3(0,0)={0}`, `D_3(a,0)={0..min(3,a)}` for `a<=4`,
   `D_3(5,0)={1,2,3}`, `D_3(6,0)={2,3}`, `D_3(7,0)={3}`, symmetry under negating/swapping, and
   complementary traces allowing only odd residues.
   Record the full non-blocking compression: up to swapping and negating, the only non-full `D_3` entries
   are `(0,0),(0,1),(0,2),(0,5),(0,6),(0,7),(1,1),(1,6),(2,5),(3,4)`.
   Formalize the matching internal table: with `lambda(v)=L_A(v)+deg_{R_i}(v)`, kept vertices
   `u,v notin O` require `deg_O(u)-deg_O(v)=lambda(u)-lambda(v)`.  Because `O` avoids `u,v`, the
   admissible residues are
   `E_3(a,b)={x-y [MOD 4]:0<=x<=a,0<=y<=b,0<=3-x-y<=5-a-b}`, where `a,b` are private neighbourhood
   sizes in `R_i\{u,v}`.  Thus the internal line is the same anti-Horn omitted-triple constraint.
   Up to the same symmetry, the only non-full `E_3` entries are
   `(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3)`.
   Formalize the internal blocker graph `J_int` on `R_i`: put `uv in J_int` when
   `lambda(u)-lambda(v) notin E_3(a_{uv},b_{uv})`.  Any omitted triple satisfying the internal line must
   be a vertex cover of `J_int`; hence `tau(J_int)<=3` is necessary.  After choosing such a cover, only
   the signed `E_3` equations for kept pairs remain.
   Equivalently, formalize the complement form: the kept four-set `T=R_i\O` must be an independent
   four-set of `J_int`; each candidate `T` then has six internal signed `E_3` checks plus the external
   trace checks on `O`.
   Record the cover-family normal form: `C_int` is contained in
   `K_3(J_int)={O: |O|=3 and O is a vertex cover of J_int}`.  If `K_3` is empty, no internal reroot
   exists; if `K_3={O_0}`, only that omitted triple needs the external template and six internal equality
   checks.  A common core in all 3-covers partially decodes `O`.
   Record the final certificate split for the positive atom: terminality is `C_ext cap C_int=empty`,
   witnessed by external emptiness, internal emptiness, a decoded singleton mismatch, or a genuine
   ambiguous core where `|C_ext|,|C_int|>=2`.
   In the ambiguous core after quotienting trace twins, record the finite form
   `C_ext=P` a triple packing and `C_int subset K_3(J_int)` with `P cap C_int=empty`.  In the Fano case,
   each Fano line must be killed internally by the blocker graph or a signed `E_3` equality failure.
   Add the packing-transversal bound: for each kept pair `e`, the family `{O in P:e cap O=empty}` has
   size at most two, since it is a triple packing on five points.  Thus terminality of an external
   packing `P` requires at least `ceil(|P|/2)` distinct internal kept-pair witnesses; Fano requires four.
   Formalize the sharper matching form: if `Gamma(P)` is the intersection graph of the packing, a kept
   pair kills two triples exactly along one edge of `Gamma(P)` and otherwise kills one triple.  The
   incidence lower bound is therefore `|P|-nu(Gamma(P))`.
   Formalize minimum covers as maximum matchings plus one complement-four witness for each unmatched
   triple.  Add the six-packing lemma: a six-triple packing on seven points has a three-edge even leave,
   hence the leave is a triangle and the packing completes uniquely to Fano; its minimum terminal core has
   three forced complement-pair witnesses.
   Add the general leave calculus: `|E Lambda(P)|=21-3|P|` and
   `deg_Lambda(x)=6-2d_P(x)`, so leave degrees are even.  For five triples the leave is either a six-cycle
   or two edge-disjoint triangles.
   Formalize anchored large-packing trace rigidity: if all occupied traces have constant intersection
   with all Fano lines, then only `empty` and `R_i` occur (`3|p|=7t`).  If they have constant intersection
   with the six lines of `F\{L_0}`, then only `empty`, `L_0`, `R_i\L_0`, and `R_i` occur.
   Conclude that full and near-Fano anchored packings force trace twins, so a trace-twin-free anchored
   quotient has external packing size at most five.
   Record the post-quotient witness-count table from `|P|-nu(Gamma(P))`: sizes `5,4,3,2` need at least
   `3,2,2,1` witnesses respectively, except two disjoint triples need two.
   Add the six-cycle leave collapse: the forced block system
   `{024},{135},{infty 03},{infty 14},{infty 25}` has anchored balanced traces only `empty` and full,
   by `3(t-x_infty)=2t`.  Therefore irreducible anchored five-packings must have two-triangle leave.
   Add the two-triangle leave collapse: disjoint leave triangles are impossible; shared-point leave
   triangles force block `056` and adjacent/opposite assignments on the four-cycle, and their balanced
   trace equations force twin pairs.  Conclude trace-twin-free anchored packings have size at most four.
   Add the size-four classification.  The degree patterns are only `(1,3,3,0)`, `(0,6,0,1)`, and
   `(0,5,2,0)`.  The tetrahedral and one-disjoint-pair patterns force trace twins; the sole
   trace-twin-free normal form is `U={u_1,u_2,u_3}` and `{a,u_i,v_i}` for `i=1,2,3`.
   Formalize its balanced traces: `empty`, full, `{u_i,v_j,v_k}`, and complements.  Its
   `Gamma(P)=K_4`, so minimum witness covers are perfect matchings, i.e. primal pairs
   `{u_i v_i, v_j v_k}`.
   Add the size-three/two endpoint: for three templates, `Gamma(P)` is `P_3` or `K_3`, and a minimum
   core is one forced complement pair for a matched edge plus one bad complement-four pair for the
   unmatched triple.  For two templates, adjacent pairs have one forced witness and disjoint pairs need
   two one-at-a-time witnesses.
   Record the three size-three geometries: path
   `{a,x_1,x_2},{a,b,c},{b,y_1,y_2}`, centered `K_3` with all triples sharing one point, and triangular
   `K_3` `{a,b,x},{a,c,y},{b,c,z}`.
   Add the unanchored relative-trace normalization.  For a reference occupied trace `p_0`, ambiguity gives
   `(1_p-1_{p_0}) dot (1_O-1_{O'})=0`.  Adjacent templates force equal relative columns.  Full Fano
   equations force `p=p_0` by incidence-matrix nonsingularity; six-line near-Fano equations have
   nullspace generated by `-2 1_{L_0}+1_{R_i\L_0}`, so no nonzero binary trace difference is possible.
   For the co-cut endpoint, formalize the singleton target-stability inequality.  If `T={theta=L}`,
   same-old-vector swap `y -> z` has corrected-set `A_{y,z}` and damaged-set `D_{y,z}`, then
   `|A_{y,z}|+1_{z lands on target}<=|D_{y,z}|+1_{y in T}`.
   Also formalize the averaged old-vector-class inequality obtained by summing over `y in B_p`:
   `sum_y(|A_{y,z}|-|D_{y,z}|)<=|T cap B_p|-|B_p|1_{z target}`.
   In the zero anchor-shift case, split errors into `T_+`, `T_-`, and `T_2`; singleton swaps cannot
   correct `T_2`, and the inequality becomes the signed cut formula using
   `N(y)\N(z) cap T_-`, `N(z)\N(y) cap T_+`, and `(N(y) triangle N(z)) cap T`.
   Add the zero-anchor pair-exchange layer table: for balanced two-for-two exchange
   `s_{Y,Z}=deg_Y-deg_Z`, values `1,-1,±2` correct `T_-`, `T_+`, and `T_2` respectively, while target
   vertices are damaged where `s_{Y,Z}!=0`.
    Record the pure-`T_2` no-pair-cut rule: the number of `T_2` vertices with `(deg_Y,deg_Z)=(2,0)` or
    `(0,2)`, plus imported targets, is at most the number of target vertices with `deg_Y!=deg_Z`, plus
    exported targets.
    Add the averaged pair-cut form over an admissible export pool `A`: for a fixed import pair `Z`,
    the left side is
    `sum_{u in T_2,deg_Z(u)=0} binom(deg_A(u),2)+sum_{u in T_2,deg_Z(u)=2} binom(|A|-deg_A(u),2)`
    plus the imported-target term, and the right side is the summed target pair-damage plus
    `(|A|-1)|A cap T|`.
    Derive the exact-basis three-copy corollary: if a direction has boundary triple `Z_g`, then any
    unpaid pure-`T_2` vertex is almost constant on a large matching old fiber `A_g`; adjacency to at most
    one boundary copy forces `deg_{A_g}(u)<=1`, while adjacency to at least two boundary copies forces
    `deg_{A_g}(u)>=|A_g|-1`.
    Formalize the exception-shadow version.  With `M_g(u)=1_{deg_{Z_g}(u)>=2}`, the sets
    `Q_g(a)={u in T_2: a is the unique vertex of A_g with 1_{ua}!=M_g(u)}` are pairwise disjoint.
    For each boundary pattern cell `U_lambda`, choose two zero boundary corners if `|lambda|<=1` and two
    one boundary corners if `|lambda|>=2`; every old pair avoiding the corresponding exception shadows has
    the same degree as that boundary pair on all of `U_lambda`.
    Combine with the exact-basis repair spectrum: for `A_g^0={a:Q_g(a)=empty}`, terminality implies
    `G[A_g^0]` has no induced `d'`-regular four-set for any `d' in Rep(g)`.  In particular, if
    `{0,3} subset Rep(g)`, then `|A_g|<=|T_2|+R(4,4)-1`.
    Add the anti-Horn residual for a missing extreme.  If `d=r-omega(g)` and `rho in {0,3}` is not in
    `Rep(g)`, then every usable old deletion `D` with constant `c` satisfies
    `deg_D(b_g) != rho-d+c [MOD 4]`; for `|D|<=2` this is a forbidden adjacency count in `{0,1,2}`.
    Formalize the shift-addition corollary for very large fibers.  Since two disjoint small deletions have
    additive shifts, a unit-shift terminal branch has a kernel `K_g` of size at most three meeting every
    nonzero-shift singleton/pair repair.  For every usable deletion `D` disjoint from `K_g`, one has
    `deg_D(b_g)=c`.  This is the formal bridge from missing repair spectra to anchored persistence/no-split:
    co-regular tests outside `K_g` either separate outgoing defects or leave a chamber-flat silent edge.
    Record the already-reduced complementary branch: `sigma_g=2` gives the `{0,2}`/`{1,3}` hereditary
    spectra, which are capped by the augmented boundary cube/type analysis; the unit `{0,1}`/`{3,2}`
    branch is capped by target-stability and the endpoint-exclusive mod-`4` layer theorem.  The remaining
    formal target is therefore the terminal co-cut/self-layer selector, not another same-direction
    exact-basis spectrum case.
    For the unconstrained self-layer selector, formalize the all-pairs averaged inequality: summing over
    every `Y in binom(B,2)` and `Z in binom(X,2)` gives each unpaid `u in T_2` the contribution
    `binom(deg_B(u),2)binom(|X|-deg_X(u),2)+binom(|B|-deg_B(u),2)binom(deg_X(u),2)`, bounded by total
    target pair-damage and exported/imported target terms.  This is the biquadratic domination version of
    the final co-cut endpoint.
    Add the target-damage profile: `Damage(t)=sum_{i!=j}N_B^i(t)N_X^j(t)` with
    `N_B^0=binom(b-beta,2)`, `N_B^1=beta(b-beta)`, `N_B^2=binom(beta,2)` and similarly on `X`.
    Formalize the zero cases for `b,x>=3`: zero `Polar` iff the vertex is one-corner sparse or dense
    across the cut, and zero `Damage` iff the target vertex is cut-constant with the same value on both
    sides.
    Add the charging corollary: for `U subset T_2`,
    `|U|min_U Polar <= |T|max_T Damage + binom(|X|,2)(|B|-1)|T|`.  Deduce that any linearly mixed
    `T_2` subset has size `O(|T|)`, leaving a one-corner sparse/dense polarized residual after charging to
    the target layer.
    Formalize the zero-polar endpoint: if
    `U^-={u:deg_B(u)<=1 and deg_X(u)<=1}`, then `G[U^-]` has maximum degree at most one, so terminality
    gives `|U^-|<=2m`; dually the dense set `U^+` has complement maximum degree at most one and also has
    size at most `2m`.
    Add the scale version: for `L>=2` and `|B|,|X|>=2L`, `Polar(u)<binom(L,2)^2` implies `u` is either
    `L`-sparse or `L`-dense across the cut.  Degeneracy gives at most `Lm` vertices of each type, yielding
    `|T_2|<=2Lm+(|T|max_T Damage+binom(|X|,2)(|B|-1)|T|)/binom(L,2)^2`.
    Formalize that the same `Lm` sparse/dense bound applies to arbitrary retained subsets, especially the
    target layer.  Thus only scale-mixed target vertices can contribute nontrivially to the damage budget
    after `O(Lm)` one-corner target vertices are removed.
    Add the summed-damage estimate:
    `sum_T Damage <= |T_mix(L)|binom(b,2)binom(x,2)+C L^2m b x(b+x)`, obtained from
    `Damage(t)<=C L b x(b+x)` on sparse/dense target vertices and the `Lm` bound on each such target part.
    This identifies `T_mix(L)` as the only nonlinear target core left in the scale inequality.
    Add dyadic cut-profile bucketing for the four factors `deg_B`, `b-deg_B`, `deg_X`, `x-deg_X`.  On each
    homogeneous bucket, prove `Damage` and `Polar` are comparable to the same product of bucket scales, so
    the all-pairs inequality compares mixed `T_2` and mixed target cardinalities up to bucket-count loss.
    Add the residue refinement by `deg_B mod 4` and `deg_X mod 4`, reducing the remaining homogeneous
    mixed target bucket to an internal principal-submatrix selector with constant degree modulo `4`.
    Formalize the equivalent deletion equation: for `D=V(H)\S`, the selector condition is
    `deg_D(v)==deg_H(v)-c mod 4` on all retained vertices.  Terminality says every deletion set with
    complement larger than `m` violates this equation for every residue `c`.
    Add the bit split: the same equation is equivalent to the Gallai parity equation for `deg_D(v)` and
    the centered cut-pair parity equation
    `#{ {x,y} subset D : vx,vy in E(H) } == floor((deg_H(v)-c)/2) mod 2` on the same retained support.
    Formalize the pruning closure: starting from `D_0`, repeatedly add every retained violator of
    `deg_D(v)==deg_H(v)-c mod 4`; if the stable complement has size greater than `m`, it is a selector.
    Terminal principal buckets are therefore precisely buckets where every residue and every initial
    deletion set avalanches to a complement of size at most `m`.
    Add the equivalent complement-side residue-core formulation
    `S_{t+1}={v in S_t : deg_{H[S_t]}(v)==c mod 4}`; terminality means every induced starting chamber has
    all four stable residue-cores of size at most `m`.
    Add the equivalent elimination-order certificate: for each induced chamber `U` and residue `c`, all
    but at most `m` vertices of `U` can be ordered so that each deleted vertex has current degree not
    congruent to `c mod 4`.
    Add complement self-duality:
    `deg_complement[S](v)=|S|-1-deg_H[S](v)`, so a residue-`c` selector in `H` is a
    residue-`|S|-1-c` selector in the complement on the same support.
    Formalize the critical minimal-counterexample normalization for the loss-`32` theorem: if `H` is a
    minimum counterexample and `m` is its maximum selector size, then `|H|=32m+1`; for every vertex `z`,
    `H-z` contains a selector of size exactly `m`, equivalently a stable residue-core of size `m`.
    Formalize maximum-core exchange: for two maximum selectors `S,T` with residues `a,b`, overlap `P`,
    and petals `A=S\T`, `B=T\S`, prove `deg_A(v)-deg_B(v)==a-b mod 4` on `P`,
    `deg_P(x)+deg_A(x)==a mod 4` on `A`, and `deg_P(y)+deg_B(y)==b mod 4` on `B`.
    Add the one-exchange classification: if `S=P union {x}` and `T=P union {y}`, then `a-b!=2`;
    `a=b` gives identical traces to `P`, while `a-b=±1` gives complete/anticomplete traces.  Formalize
    the forbidden extension subcases producing `P union {x,y}` as an `m+1` selector.
    Formalize selector merging: disjoint selector blocks with residues `a,b` and constant cross-degree
    residues `p,q` merge iff `a+p==b+q mod 4`.  For a cross-regular family, the quotient condition is
    `r_i+sum_j p_{ij}x_j` independent of `i` modulo `4`; terminality forbids any quotient solution whose
    lifted block size exceeds `m`.
    Formalize the one-vertex extension corollary: `S union {x}` is a selector iff either `x` is
    anticomplete to a residue-`0` selector `S`, or `x` is complete to a residue-`a` selector with
    `|S|==a+1 mod 4`.  Record the resulting domination/non-completion constraints for maximum selectors.
    Formalize the two-vertex extension corollary: for outside pair `{x,y}` with internal edge bit
    `delta`, `S union {x,y}` is a selector only when every `s in S` sees a constant
    `p in {0,1,2}` vertices of the pair and
    `a+p==delta+deg_S(x)==delta+deg_S(y) mod 4`.  Expand the three trace cases
    `p=0,1,2`.
    Formalize the Davenport packet reduction relative to a maximum selector `S` of size `m`: in each
    chamber `U_t={x:deg_S(x)==t mod 4}`, any `3m+1` vertices contain a nonempty packet whose trace sum to
    `S` is zero in `(Z/4)^S`.  Such a packet cannot be an internal residue-`a-t` selector, and in the
    critical case some chamber has size greater than `7m`, giving two disjoint zero-trace packets whose
    nonempty unions are all internally forbidden.
    Formalize the sharper quotient version: modulo the constant all-ones trace, the trace group is
    `(Z/4)^(m-1)` with Davenport constant `3m-2`; hence a chamber of size at least `3m-2` contains a
    constant-trace packet.  If the constant trace is `p`, that packet is forbidden from being an internal
    residue-`a+p-t` selector.
    Add the packet arithmetic lemma: for a constant-trace `p` packet `X subset U_t`, counting cross edges
    gives `|X|t==mp mod 4`.
    Add the handshaking filter for dangerous packets: an internal residue `r=a+p-t` selector on `X` is
    possible only if `|X|r==0 mod 2`, and then `e(X)==|X|r/2 mod 2`.
    Add the size-refined Davenport endpoint: in
    `((Z/4)^S/<1>) x Z/4 ~= (Z/4)^m`, every `3m+1` vertices yield a nonempty constant-trace packet with
    `|X|==0 mod 4`.  For these packets the size congruence is automatic, the edge parity target
    is `e(X)==0 mod 2`, and cross-count reduces to `mp==0 mod 4`.
    Add the case split for `mp==0 mod 4`: odd `m` forces `p=0`, `m==2 mod 4` forces `p in {0,2}`, and
    `m==0 mod 4` imposes no condition on `p`.
    Add the atom refinement: choose a minimal zero-sum packet in the size-refined trace group.  It has size
    at most `3m+1`, no proper nonempty constant-trace size-`0 mod 4` subpacket, and terminality forbids it
    (and unions of disjoint such atoms) from being internally regular at the matching residue.
    Add greedy atom-family extraction: repeatedly remove minimal zero-sum atoms from the largest critical
    chamber until the remainder is zero-sum-free.  The remainder has size at most `3m`, so the extracted
    atom family covers more than `19m/4` vertices; every nonempty subunion is terminally forbidden.
    Add the atom-defect formulation: for an atom `X_i` with constant trace `p_i` in chamber `U_t`, define
    `epsilon_i(v)=deg_Xi(v)-(a+p_i-t) mod 4`.  For a union of atoms, regularity is equivalent to
    `epsilon_i(v)+sum_{j!=i}(deg_Xj(v)-p_j)==0 mod 4` for every vertex in every chosen atom.  Terminality
    is anti-cancellation of these defects by cross-degree correction vectors.
    Add the two-atom global parity filter obtained by summing the defect equations:
    `2e(X)+e(X,Y)==0 mod 4` and `2e(Y)+e(X,Y)==0 mod 4`.
    Add the two-atom quotient test for internally regular, cross-regular atoms:
    `d_X+c_XY==d_Y+c_YX==a+p_X+p_Y-t mod 4`; for same-profile atoms this reduces to `c_XY=c_YX`.
    Add the atom quotient/uniformity split: if a subfamily has constant cross-corrections
    `kappa_ij(v)=deg_Xj(v)-p_j` on each atom and constant internal defects `e_i`, then its union is
    dangerous iff `e_i+sum_{j!=i}c_ij==0 mod 4` for all atoms.  Terminality requires quotient
    unsolvability or nonconstant cross-corrections in every large subfamily.
    Define the atom irregularity graph on constant-defect atoms, joining two atoms when either directed
    cross-correction is nonconstant.  Formalize that every quotient-solvable independent set has lifted
    size at most `m`.
    Add the atom-size dichotomy: if an atom has size greater than `m`, it is a compact terminal induced
    chamber of size at most `3m+1` and has no proper size-`0 mod 4` constant-trace subpacket.  If all atoms
    have size at most `m`, the extracted cover greater than `19m/4` contains at least five atoms.
    Add the Ramsey base and weights: `m>=4` by `R(4,4)`, and in the small-atom branch all atom weights are
    positive multiples of `4`; no quotient-solvable subfamily can have weight greater than `m`.
    Add the weighted bundle lemma: from total atom weight `>19m/4` and atom weights at most `m`, extract
    two disjoint subfamilies, each of total weight in `(m,2m]`.  Terminality blocks each by defect
    variation, cross-irregularity, or quotient unsolvability.
    Add the minimal tight-bundle refinement: choose each bundle minimal above `m`, so `w(B)-w_i<=m` for
    every atom `i` in the bundle.  Their union has weight greater than `2m`; if all defects and
    cross-corrections across both bundles are quotient-uniform, the combined quotient must be unsolvable.
    Add the three-certificate split for each threshold object `B1`, `B2`, and `B1 union B2`: either an
    atom has nonconstant internal defect, an ordered atom pair has nonconstant cross-correction, or the
    fully constant weighted `Z/4` quotient has no zero-row solution.
    Add the pure-Q residual form: for a quotient-uniform bundle `B`, define
    `R_i(B)=e_i+sum_{j in B,j!=i}c_ij`.  For two bundles, the union is quotient-solvable iff the
    cross-bundle correction sums are `-R(B1)` and `-R(B2)` on the two sides.  Terminality is affine
    avoidance of this cancellation vector.
    Add the one-atom repair profile: for atom `y` outside pure-Q bundle `B`, `B union {y}` is solvable iff
    `c_iy=-R_i(B)` for all `i in B` and `e_y+sum_i c_yi==0 mod 4`.  Terminality forces every outside atom
    to avoid that affine profile.
    Add the atom-packet repair equations:
    `sum_{y in Y}c_iy=-R_i(B)` for all atoms `i in B`, and
    `e_y+sum_{i in B}c_yi+sum_{z in Y,z!=y}c_yz=0` for each `y in Y`.  This is the co-cut/self-layer
    obstruction reproduced at atom-quotient scale.
    Add the incoming/self-layer split: define `P_B(Y)_i=sum_{y in Y}c_iy`.  Packets fail either because
    `P_B(Y)!=-R(B)` or because they hit `-R(B)` but fail the shifted self-layer equation.
    Add the profile-Davenport caveat: in `(Z/4)^{|B|}`, `3|B|+1` outside atoms yield zero-profile packets,
    not arbitrary target packets.  Formalize the target-hit versus target-avoid split and avoid using
    Davenport as an affine target theorem without a seed.
    Add the seeded split: define `Sigma_B(A)={P_B(Y):Y subset A}`.  If `-R(B) in Sigma_B(A)`, fix a seed
    `Y0`; then every disjoint zero-profile packet preserves the incoming target and must fail the shifted
    self-layer.  If `-R(B)` is absent, the branch is pure affine subset-sum avoidance.
    Add the inverse-Kneser form of target avoidance: with `H=Stab(Sigma_B(A))`, the missing target means
    the coset `-R(B)+H` is absent; sequence Kneser gives
    `|Sigma_B(A)|>=|H|(1+N_out)`, hence `N_out<=|(Z/4)^B/H|-2`.
    Add the dyadic flag refinement: choose an index-two subgroup chain to the period subgroup.  At each
    quotient bit, either a minimal odd seed moves the residual target into the next subgroup, or the
    quotient character separates the residual target from all remaining zero-prefix profile packets.
    Formalize the stopped-bit certificate as a residual subgroup `K`, character `chi:K->Z/2Z`, and target
    `tau` with `chi(P_B(Y))=0` for every available lower-zero repair packet but `chi(tau)=1`.
    Add the relation-rigidity equivalent: for disjoint repair-packet relations with zero lower quotient
    sum, the sum of stopped characters is forced even; an odd relation is exactly the next seed.
    Add the support form of characters `(Z/4)^B -> Z/2`: choose minimal `W subseteq B` with odd residual
    `sum_{i in W}R_i(B)`.  Formalize that every proper odd subcut of `W` must have an odd lower-zero seed,
    while the full `W`-cut has none.
    Formalize the dual span lemma: in a fixed reservoir, the `F_2`-span of lower-zero packet cut vectors on
    minimal `W` is the even-parity hyperplane `1_W^\perp`; the remaining task is odd-coset packet
    realization.
    Add the cover normal form: build the lower-profile packet graph with `W`-cut parity on moves.  No odd
    lower-zero packet means every closed walk has even parity, i.e. a flat two-sheeted cover; the first odd
    local cycle is the packet-square missing-corner obstruction.
    Formalize the three exits for odd-coset realization: signed branch provenance, odd local packet square,
    and unbranched sheet-character provenance.  For the branch, choose opposite-parity realizations of one
    lower profile with minimal intersection and reduce to a signed disjoint relation `A-A'`; the required
    closure is promotion to an unsigned lower-zero packet.
    Add the exchange-graph collapse: within one lower profile, connected opposite-parity realizations
    yield an odd local cycle, while disconnected opposite-parity components form a sheet-character
    provenance obstruction.
    Add the sheet module squeeze: in a flat unbranched cover, any large quotient-uniform sheet component
    either supplies a selector or restarts the pure-`Q` target-avoid branch inside the sheet.  The
    irreducible survivor is boundary-provenance fullness for the rank-one sheet character.
    Add restart admissibility: a zero-residue prefix-local sheet separator should be admissible as the
    first boundary row unless comparison with the original descent exposes a local missing-corner square.
    In the exchange-saturated boundary category this is definitional; the path-only gap is saturation
    equivalence.
    Add the shortest-loop normal form for saturation equivalence: no nonfilled/curved square, no filled
    flat chord, no exchange-complete proper interval, and no repeated lower profile.  The remaining
    omni-saturation atom is a chordless rank-one flat loop not generated by filled squares and intervals.
    Add active-edge normalization: two independent active sheet separators create a local square exit or a
    flat chord/complete interval, so the survivor is a residue-zero two-state sheet transposition.
    Add the row-action normal form: after cancelling common parts, write `K=A union A'` and
    `delta_r(K)=deg_A(r)-deg_A'(r) mod 4`.  If all ambient rows have zero action, this is a module/clone
    exit; otherwise the first distinguishing row is fully skew on `K` by minimality.
    Connect this to Proposition 9.2: in `FR^sat`, a fully-skew boundary row forces a protected-packet side
    of size strictly between `0` and `q`, contradicting the low-set congruence.  The remaining path-only
    task is transport of the first fully-skew row into `FR^sat` or a local missing-corner failure.
    Add the prefix-insertion ladder: commute the fully-skew row left through the historical boundary word.
    Filled flat commutations preserve the same carrier; nonfilled/curved commutations are local exits; a
    minimal survivor is hidden path memory among visibly identical transported rows.
    Add the exact memory-free prefix fullness equivalence: same-carrier, same-row-action, zero-residue
    prefix-local fully-skew rows should be identified as terminal boundary rows.  This axiom plus
    Proposition 9.2 closes the two-state transposition, and every path-only survivor violates it.
    Add the visible/invisible split: if transported copies differ on any graph-visible row outside the
    carrier, the first distinguisher gives a same-trace/twin local exit or a smaller provenance failure.
    Therefore a minimal survivor is graph-invisible historical memory.
    Add the conservative quotient lemma: identifying graph-intrinsically equal boundary rows preserves all
    deletion and shifted self-layer equations.  The saturated graph proof closes after this quotient; the
    only remaining comparison is whether the historical path-only category realizes the quotient.
    Record that the historical comparison is not required for the graph theorem: terminal descent is run in
    the graph-intrinsic saturated category.  The old path-only Theorem G is a stronger bookkeeping
    statement, not a dependency of the saturated proof.
    Formalize the rank/module exits for that bucket: row-twin classes larger than `m` give independent
    selectors, complement row-twin classes larger than `m` give clique selectors, and modules preserve
    selector validity because outside contribution is constant.  Conclude terminal buckets are
    selector-prime and have F2 row-rank at least `log_2(n/m)` in both graph and complement.
    Add the hereditary density/codensity consequences: every induced `U` of a terminal bucket with
    `|U|>m` has `alpha,omega<=m`, so Caro--Wei/Turan gives average degree and average complement degree at
    least `|U|/m-1`.
    Add the maximum-core extension equations: for a maximum selector `S` of residue `a`, an outside packet
    `X` extends it iff `deg_X(v)=c-a` on all `v in S` and `deg_S(x)+deg_X(x)=c` on all `x in X`.  Record
    singleton/pair/ternary tests as the core-level forms of row promotion, no-split, and one-corner lift.
    Add the four-step Gallai normal form for the first-bit selector: in a critical counterexample
    `n>=32m+1`, an even core `J` of size `>2m` has a larger internal `0/2 mod 4` degree class `R` of size
    `>m`; since `deg_R(v)=deg_J(v)-deg_C(v) mod 4`, terminality forces `deg_C mod 4` nonconstant on `R`.
    Add the labeled deletion-core equivalence: with signed label `b(v)=-deg_C(v) mod 4`, a subset
    `T=R\D` is a selector
    iff `deg_D(v)=b(v)-lambda mod 4` for all `v in T`.  The residual has all four labeled cores of size
    at most `m`.
    Add the hereditary elimination equivalent: for each `lambda`, every `U` of size `>m` has a bad vertex
    with `deg_{R\U}(v)!=b(v)-lambda`, yielding an elimination order down to `m`.  Add label-refined
    twin/module exits and the rank bound `4*2^r>|R|/m` for graph and complement row ranks.
    Add hereditary relabeling: for `U subset R`, selectors lift with `b_U(v)=b(v)-deg_{R\U}(v)`.  Record
    that the size-`m+1` full-set condition is only nonconstancy of `b_U`, so one must use the parent co-cut
    origin `b=-deg_C mod 4`.
    Add the `(m+1)`-set swap calculus: `psi_T(v)=b(v)-deg_{R\T}(v)`, selector iff `psi_T` is constant; for
    `T'=(T\{x}) union {y}`, old vertices change by `1_{vy}-1_{vx}` and the new vertex has
    `b(y)-deg_{R\T}(y)-1_{xy}`.
    Add the balanced multi-swap formula: for `X subset T`, `Y outside T`, `|X|=|Y|`, old vertices change by
    `deg_Y-deg_X`, while new vertices have `b-deg_{R\T}+deg_Y-deg_X`.  Selector closure is constancy of
    these expressions on the swapped set.
    Add the incoming-target/self-layer split for fixed outgoing `X` and residue `kappa`: old vertices
    require `deg_Y(v)=kappa-psi_T(v)+deg_X(v)`, and then incoming vertices require
    `b(y)-deg_{R\T}(y)+deg_Y(y)-deg_X(y)=kappa`.
    Add the one-swap missing-template normal form: with `phi_x=psi_T-1_{vx}`, a flattening one-swap to
    residue `kappa` is possible only if `phi_x` is contained in `{kappa,kappa-1}`; then the outside trace
    is forced and terminality says no outside vertex also satisfies the scalar condition.
    Add the two-swap template: for `X={x1,x2}`, `theta_X=kappa-psi_T+1_{vx1}+1_{vx2}` must be
    `{0,1,2}`-valued, prescribing a no/one/two-hit partition for an incoming pair, followed by the two
    shifted scalar equations including the `y1y2` edge and the edges to `x1,x2`.
    Add the general `r`-swap template: `Theta_X=kappa-psi_T+deg_X` must have representatives in
    `{0,...,r}` prescribing old-vertex incoming multiplicities; every realizing `Y` must satisfy the
    shifted self-layer equations.
    Add the ternary/near-threshold split: for `r=3` every residue is representable, so the large-outside
    branch is ternary target realization plus shifted self-layer; if `|R\T|<3` for all `|T|=m+1`, then
    `|R|<=m+3` and, since `|J|>2m`, `m-2<=|C|<=|R|<=m+3`.
    Add ternary obstruction certificates: target failure has a coordinate-minimal old-vertex set `P` with
    every coordinate essential; otherwise the target-realization 3-graph is nonempty but its scalar-good
    subgraph is empty.
    For `|P|=1,2,3`, record the explicit finite forms: row extremity, four-chamber pair transportation
    failure, and eight-corner ternary cube failure.
    Record that the saturated local closure excludes these size-`<=3` target certificates in an
    irreducible target-avoidance branch.
    Add the scalar graphicality split: after old-target realization, each incoming vertex prescribes its
    internal degree in the incoming triple; residue `3` is impossible and the only graphical degree patterns
    are `000`, `110`, `211`, and `222`.
    Record the edge-pattern table: `000` empty, `110` the edge between the two `1`s, `211` the two-edge path
    centered at the `2`, and `222` triangle.
    Record the scalar mismatch table: extra edge for `000`; missing correct edge or extra wrong edge for
    `110`; missing path edge or extra `1-1` edge for `211`; missing edge for `222`.
    Add the target-avoidance 3-sum normal form: for a coordinate-minimal certificate `P`, outside trace
    columns in `{0,1}^P` do not capacity-respecting sum to `h|_P` in triples, but every coordinate projection
    and hence every proper coordinate shadow does; after local closures, `|P|>=4`.
    Add coordinate switching for the 3-sum cube: replace `a_p` by `1-a_p` and `h_p` by `3-h_p` to normalize
    `h` into `{0,1}^P`; realization becomes three columns vanishing on zero coordinates and disjointly
    covering one coordinates.
    Add the filtered three-cover form: zero coordinates define the admissible outside columns; active
    coordinates must be disjointly covered by three admissible supports, with every coordinate essential.
    Add the defect-witness split: deleting an active coordinate gives a cover of the rest with multiplicity
    `0`, `2`, or `3` at the deleted coordinate; deleting a zero coordinate gives a cover that hits the
    removed zero coordinate with multiplicity `1`, `2`, or `3`.
    Add the active/filter split: if `|A|<=3`, obstruction is a finite small-support capacity failure inside
    the zero filter; the genuinely new cover case has `|A|>=4`.
    Add the finite capacity-table criterion: `c_Z(B)` counts admissible columns with active support `B`;
    three-cover existence is equivalent to a disjoint three-block cover of `A` respecting these
    multiplicities, and zero-coordinate deletion changes the table to `c_{Z\{z}}`.
    Record the equivalent 3-coloring criterion: each nonempty color class needs positive `c_Z`, and the
    number of empty color classes must be at most `c_Z(empty)`.
    Record the empty-capacity compression: for nonempty `A`, with `e_Z=min(c_Z(empty),3)`, require an
    admissible partition into `k` nonempty blocks for some `max(1,3-e_Z)<=k<=3`.
    Add the support-family endpoint `F_Z={B nonempty subset A:c_Z(B)>0}`: target failure is that `A` has no
    allowed partition by `F_Z`, while every active deletion and zero-filter relaxation does.
    Add partition-spectrum language: `Spec_Z(A)` is the set of partition sizes in `{1,2,3}` available from
    `F_Z`; realization requires intersection with `{max(1,3-e_Z),...,3}`.
    Record the three empty-capacity cases: `e_Z>=2` forces empty spectrum, `e_Z=1` permits only useless
    one-block partitions, and `e_Z=0` permits only useless one-/two-block partitions.
    Record the equivalent forbidden block alternatives: absence of full support/bipartitions/tripartitions
    according to the empty-capacity case.
    Add blocker duality: `M_Z={B nonempty subset A:B notin F_Z}` hits every allowed partition of `A`, but
    every active deletion or zero-filter relaxation has an allowed partition avoiding the corresponding
    blocker.
    Add minimal blocker certificates: an inclusion-minimal hitting subfamily `M_Z^*` has, for each
    `B in M_Z^*`, an allowed partition in which `B` is the unique blocked part.
    Record the criticality equations for `Spec_Z(A\{a})` and `Spec_{Z\{z}}(A)`, with
    `e_{Z\{z}}=min(c_Z(empty)+p_z(empty),3)`.
    Strengthen to full minor-criticality: for every proper shadow `(A',Z')`, with counts
    `c_{Z'}^{A'}(B)`, the filtered-cover criterion succeeds.
    Add the singleton-shadow collapse: for `|A|>=2`, full minor-criticality with `A'={a}`, `Z'=Z` forces
    `c_Z(empty)>=2` and all singleton supports `{a}` present.
    Add the excess-packing form: with all singletons present, realization is equivalent to disjoint
    non-singleton supports with total saving `sum(|B|-1) >= |A|-3`; the endpoint is full-minor-critical
    failure of this packing.
    Record large-support exclusions `|B|<=|A|-3` and active-deletion projected near-packings of saving
    `|A|-4` whose one-unit lifts by the deleted coordinate are blocked; singleton closure is only for
    projected partitions with at most two blocks, giving no one-block shadows and double-collision-only
    two-block shadows.
    Add the support graph consequence: every four-set contains a co-supported pair, so the support graph has
    independence number at most three; pair-only endpoints occur only for `|A|=5,6,7` with the exact
    triangle / matching-critical / factor-critical table.
    Define `mu_Z` as maximum disjoint-support excess and `Delta=|A|-3-mu_Z`; formalize zero relaxation as a
    private excess bridge of size at least `Delta`.
    For the mixed two-level core, formalize that every `(m+1)`-set `T` has `|J\T|>=m`, hence for `m>=3` the
    ternary packet target/scalar dichotomy applies even when the pure `R` outside has size at most two.
    Add the tiny-base closure: pairs handle `m=1`; `R_4(3)=51` gives a monochromatic edge-residue triangle
    and hence a 3-selector for the `m=2` counterexample range.
    Formalize the scalar lower-swap shadow: a target-realizing ternary mismatch is terminal only if every
    one- and two-vertex partial swap is blocked by omitted-trace inequality or retained-scalar failure.
    Formalize four-residue target coherence for fixed `T,X`: `h_k=k+deg_X-psi_T`, active set
    `{h_k in {1,2}}`, zero set `{h_k in {0,3}}`, and `k` versus `k+2` swaps active/zero while complementing
    outside traces.
    Record the explicit `q`-class rotation table: active pairs `12,01,30,23` and switch pairs
    `23,12,01,30`.
    Formalize the antipodal trace core forced when both opposite residues are high-active target endpoints
    on a shared certificate: repeated centers `sigma`, `1-sigma`, and singleton flips around the two centers;
    for different certificates, record complementary restrictions on intersections.
    Formalize the small-core cutoff: if all four residues are high-active target-avoidance then
    `|N_i|+|N_{i+1}|>=4` for the four `q=deg_X-psi_T` classes, so `m>=10`; otherwise some residue is
    scalar-killed or small-active zero-filter capacity.
    Add the large-core rank-three forcing: `sum_k |A_k|=2(m-2)` and no rank-three support implies
    `|A_k|<=7` for all high-active residues, hence `m<=16`.
    Package this as a universal `X`-dichotomy for every retained `T` and outgoing triple `X`: scalar-killed,
    small-active zero-filter, low-rank bounded, or rank-three high-active.
    Add the finite Ramsey window for the low-rank bounded line: a monochromatic clique in the mod-`4`
    edge-coloring is a selector, so `3<=m<=16` and `32m+1<=n<R_4(m+1)`.
    Translate rank-three support to original traces: for each rotation, an outside vertex matches the
    switch pattern on the two zero `q`-classes and has at least three deviations on the active pair.
    Add the column-separation lemma: adjacent residue zero-pinnings conflict on the shared zero `q`-class,
    and opposite zero-pinnings imply forbidden full active supports in high-active terminal endpoints.
    Add the adjacent-transfer lemma: a one-sided rank-three support in the shared active `q`-class is
    admissible for the adjacent residue with complementary support; otherwise the support is bi-active
    oriented.
    Formalize the paired cut endpoint: for a transferable support `C subset M`, both `C` and `M\C` satisfy
    atom-defect inequalities in adjacent four-atom bridge blockers, forbidding pure two-atom unions on either
    side.
    Formalize rank-three support contraction: a support `B` of size `r>=3` plus a complement-shadow packing
    saves `|A|-4`, so terminality is exactly absence/capacity-deficiency of all one-saving bridges,
    thickenings, or larger replacements.
    Define the replacement gain
    `gain_P(C)=|C|-1-sum_{B_i in P, C cap B_i nonempty}(|B_i|-1)` and prove terminality is
    `gain_P(C)<=0` for every deficit-one packing `P` and support `C`.
    Record the four-atom normalization `t+L=4` for deficit-one packings and prove that every pure union of
    two atoms is a forbidden support.
    Add atom-defect form: `gain_P(C)=pi_P(C)-1-delta_P(C)`, so every support has
    `delta_P(C)>=pi_P(C)-1` and zero-gain supports are exactly tight atom-defect replacements.
    Derive the local caps: leftover singletons support-independent; one-block crossings have size at most
    the block; crossings over block set `I` have size at most `1+sum_I(|B_i|-1)`.
    Add zero-gain saturation: gain-zero replacements preserve deficit one, so choose `P` lexicographically
    maximal in block-size profile and covered support; all terminal exclusions must hold on its zero-gain
    orbit.
    Derive zero-gain locality: in a lexicographically saturated packing, a zero-gain support cannot meet two
    packed atoms; if it meets one, it has the same size as that atom.
    Add strict cross-defect corollary: supports meeting `r>=2` atoms satisfy `delta>=r`; in the four-four
    no-leftover subcase, cross-support sizes are bounded by `6/9/12`.
    Add the four-four no-leftover deletion dichotomy: every deletion repair is either
    unit strict absorption (`h=0,t=1,g^-=1`) or lift-collision.
    Formalize the unit strict absorption taxonomy from `g^-=pi-s-delta=1`: the only templates are
    `(s,pi,delta)=(1,2,0),(1,3,1),(2,3,0)` on the three atoms opposite the deleted vertex.
    Record that these are cap-tight maximum-size cross-defect events.
    Formalize deletion-only bridge families: deleting a packed-block vertex makes the projected packing one
    short, forcing a minimal positive-gain repair family in the shadow whose full lifts all have nonpositive
    total gain.
    Add exact one-support deletion lift accounting.  If the projected support hits the shortened block, its
    thickened lift has the same projected gain and is blocked while its unlifted lift has gain one less.  If
    it misses the shortened block, the thickened lift pays the large-block absorption penalty `|B_j|-2`.
    Derive the absorption cutoff: size-two packed blocks cannot absorb positive one-support repairs, and
    size-three blocks absorb only unit projected gain.
    Generalize to repair families: if `h` records contact with `B_j\{a}` and `t` records a lift using `a`,
    the full gain is `g^- + t - (1_{h or t}(|B_j|-1)-h(|B_j|-2))`, i.e. the four cases
    `g^-`, `g^- - 1`, `g^-`, `g^- + 2 - |B_j|`.
    Combine lift accounting with zero-gain locality: nonpositive shortened-block unlifts are unit-gain
    same-size exchanges with leftover singletons, and equality pure absorptions require `|B_j|-1` leftover
    singletons.
    Add lift-collision alternative: a projected repair family has no disjoint full lift only if at least two
    projected supports are forced to lift through the deleted vertex.
    Derive the small-atom corollary: size-two atoms have only zero-gain pivots in the noncollision branch;
    size-three atoms purely absorb only unit projected gain.
    Record the caution that inclusion-minimality gives positive marginal contribution, not positive individual
    gain, so two-atom collision stars remain a real branch.
    Add pair-pivot saturation: a zero-gain pair pivot meeting another packed atom creates a larger block and
    contradicts zero-gain saturation; surviving pair pivots are same-size exchanges with leftover singletons,
    so pair atoms with no leftover singleton are collision endpoints.
    Record the no-leftover small-atom endpoint: pair atoms have no pivot option, and three-atoms have no
    zero-gain/equality-absorption boundary lift or negative pure absorption; both are collision-only.
    Add no-leftover zero-gain rigidity: with `L=0`, zero-gain supports are exactly the packed atoms and the
    zero-gain orbit is trivial.
    Record leftover-budget rules: zero-gain shortened-block exchanges require `L>=1`; equality pure
    absorption at atom `B_j` requires `L>=|B_j|-1`; otherwise repairs are strict absorption or lift-collision.
    Formalize pair-exchange components: for a pair atom `{a,b}`, endpoint deletions force pivot pairs
    `{b,l}` and `{a,l'}` with leftover singletons; common leftovers form support-graph triangles, while the
    triple itself remains forbidden by positive gain.
    Formalize pair-collision templates: after deleting one endpoint, an inclusion-minimal projected collision
    repair has gain `pi-s-delta>0`, at least two supports forced through the deleted endpoint, and only
    `s=2:(3,0),(4,0),(4,1)` or `s=3:(4,0)`.
    Add the shared-rebate identity
    `g(S)=sum_C g(C)+sum_H(c_H(S)-1)_+(|H|-1)` and derive that every pair-collision repair splits a packed
    atom between forced petals.
    Package pair collisions as rebate circuits: with deficits `d_i=-g(C_i)`, every proper subfamily has
    rebate at most the corresponding deficit sum, while the full two- or three-petal family exceeds it.
    Prove the pair-atom strict-deficit strengthening: a forced split-petal has a cross-atom full lift with
    the same gain, so zero-gain saturation forces `d_i>=1`; two-petal pair collisions need rebate at least
    three.
    Extend the same finite rebate-collision template to no-leftover size-three atoms: zero-gain boundary
    lifts require leftovers and strict absorption is unavailable, so every deletion is collision-only.
    Derive the collision-free cutoff: in a no-leftover packing with `|A|<=15`, some atom has size at most
    three and therefore forces a finite small-atom collision circuit; four-four is only the first
    collision-free branch.
    Formalize the four-pair collision core: endpoint deletion forces complementary transversal supports
    `{a} union T` and `{a} union T^c` on the other three pairs; equal labels on the two endpoints of one pair
    give two disjoint support blocks partitioning all four pairs.
    Repackage this core as an antipodal-free orientation of full transversals in `{0,1}^4`, with each
    coordinate-bit facet containing a selected distance-three edge (`v_i=1111+e_i` in the antipodal quotient).
    Prove the Boolean quotient lemma: the three coordinate matchings on the four base complement-pairs each
    need a bichromatic edge, so nonconstant colorings are forced to be `1+3` stars; the four-pair core has a
    unique hidden center for the three base-coordinate matchings.
    Add star rigidity: all selected transversals become actual supports, all antipodes are absent, and every
    two-face through the center is a one-corner `0001/0111` square, identifying the core with the host
    square-breaker.
    Record the discharge consequence: once the support-local one-corner square-breaker is excluded, the
    four-pair no-leftover collision core is gone; remaining no-leftover rank-three cases either split an
    atom of size at least three in a finite rebate circuit or have all atoms size at least four.
    Split pair collisions into partner-free and partner-hit cases.  In the partner-free branch prove
    `s=2,pi=3,delta=0`, yielding complementary bipartition labels `C|M\C` on the opposite three atoms;
    equal labels on the two endpoints close.  Record partner-hit as the finite high-cover template list.
    Add the no-near-complement rule for two endpoint bipartitions: if a cross-choice is disjoint and misses
    at most one vertex, two supports close; equivalently every empty four-cell has opposite diagonal cell
    size at least two.
    Expand the partner-hit list into its four high-cover templates: two-petal `b` plus two opposite atoms,
    two-petal `b` plus all three, two-petal one-omission, and three-petal `b` plus all three.
    Add the partner-hit individual-deficit rule: the high-cover is by the family union, while the full-pair
    petal itself must satisfy `delta>=r+1` if it hits `r` opposite atoms.
    Derive the partner-hit large-atom consequence: some hit atom has at least two omissions and is covered by
    a compensating petal, so partner-hit collisions force a split atom of size at least three and cannot occur
    over all-pair opposite atoms.
    Add the split-rebate lower bound for partner-free labels: the split atoms have
    `sum(|H|-1)>=3`, so the minimal patterns are one size-at-least-four atom, one size-three atom plus
    another split atom, or three pair atoms.
    Conclude the pair-atom endpoint after square-breaker discharge: every remaining pair collision splits an
    opposite atom of size at least three, so pair atoms only detect larger split atoms.
    Add the isolated size-three elimination: for atom sizes `3,2,2,2`, deletion from the size-three atom gives
    four projected pair atoms and therefore the same one-corner square core.
    Derive the first-size cutoff: after square-breaker discharge, no no-leftover small-collision endpoint
    survives with `|A|<=9`; the first sorted profiles are `4,2,2,2` and `3,3,2,2`.
    Normalize the first profiles: `4,2,2,2` is a one-large-atom cut system, while `3,3,2,2` is a coupled
    two-three-atom split system whose three-atom deletions route to the other three-atom or to the square core.
    Add the balanced-cut table for partner-free `4,2,2,2`: a side carrying `k` auxiliary pair atoms contains
    exactly `3-k` vertices of the four-atom.
    Add the partner-free `3,3,2,2` balance table: split both three-atoms gives weighted side sizes `4` and
    `3`; split one three-atom plus the pair gives a forced `1/2` split around the unsplit three-atom.
    Package the general small-collision endpoint as a weighted split-dependency graph: after square-core
    discharge, pair atoms and non-square-routed three-atoms point to split atoms of size at least three.
    Prove the size-monotone branch split for that graph: every path reaches a split atom of size at least
    four or cycles entirely among size-three atoms.
    Enumerate the ternary-cycle profiles: `3,3,2,2`, `3,3,3,2`, and `3,3,3,3`; reuse the coupled
    two-three-atom table for the first.
    Add the ternary-cycle outdegree lemma: `3,3,3,3` deletions split at least two other three-atoms, and
    `3,3,3,2` deletions split both other three-atoms or one three-atom plus the pair.
    Add source-side separation: a shortened-pair-free deletion from a size-three atom gives a complementary
    bipartition of the other three atoms, and the three source vertices must have distinct labels.
    Add the no-rainbow source constraint: one side from each of the three source labels cannot disjointly
    partition the opposite atoms, or the three lifted supports close.
    Repackage no-rainbow as a finite code condition: opposite vertices receive `{0,1}^3` words from the three
    cuts, and no sign vector is at Hamming distance `2` from every word.
    Prove the parity form of no-rainbow: such a code is either parity-mixed or contains all four words of one
    parity class.
    Add the distinct-label sharpening: parity-mixed source codes contain a Hamming edge; otherwise the code
    would be one antipodal pair and all three complementary labels would coincide.  The remaining code atoms
    are unit-edge and parity-tetrahedron.
    Identify the unit-edge atom with the one-corner square-breaker: two opposite vertices agree in two source
    labels and differ in the third.  After square discharge, shortened-pair-free source codes are parity
    tetrahedra.
    Record parity-tetrahedron rigidity: projection to any two source coordinates is a complete balanced
    `2x2` square, the `0101/0011` compensator side of `0001+0111=0101+0011`.
    Add the target-type table inside a parity tetrahedron: support size `1` is split by no source cuts, support
    size `2` is a parity edge split by exactly two source cuts, and support size at least `3` is split by all
    three source cuts.  Rephrase ternary high-outdegree as incidence constraints on these target types.
    For `3,3,3,3`, formalize the incidence enumeration: `FFF`, `FFX`, `F E_i E_j` with `i!=j`, or the
    all-edge permutation triangle `E_1E_2E_3`.
    Extend the same enumeration to pair profiles: `3,3,3,2` gives `FFP_x`, `F E_iP_j` with `i!=j`, or
    `E_iE_jP_k` with all omissions distinct; `3,3,2,2` gives `F P_iP_j` with `i!=j` or `E_iP_jP_k`
    with all omissions distinct.
    Formalize fully split transpose rigidity: a `3x3` trace with three same-parity column labels and
    same-parity row labels cannot have row support size `1` or `2`; row support size `3` forces a permutation
    matrix or its complement, so `F` atom-pairs are mutual and cross-regular of degree `1` or `2`.
    Add the `F`-edge terminality rule: same internal type on an `F` edge makes the two-atom union a selector,
    so every surviving `F` edge crosses the empty/triangle type split.
    Package the `F`-containing branch as a typed bipartite graph with omitted-coordinate labels on non-`F`
    corner edges: local constraints are none for `deg_F>=2`, distinct omissions for `deg_F=1`, and all three
    omissions for `deg_F=0`.
    For the all-edge permutation minimum, formalize the phase split: the three parity edges form either a
    star through one parity word or the triangle avoiding one parity word, and each size-three edge target
    has only a `2+1` label multiplicity choice.
    Add the symmetric transpose test: if two size-three atoms are mutual parity-edge targets, the edge support
    must contain an all-constant column, so the all-ternary edge endpoint is star phase and not triangle
    phase.
    Add the star-multiplicity normalization: multiplicity two of the all-constant word transposes to a
    unit-edge square-breaker, so the residual trace is a corner matrix with one omitted row, one omitted
    column, and a filled complementary `2x2`; globally this is a half-edge Latin `K_{2,2}` design.
    Formalize the cross-residue-flat calculation for the Latin design:
    `deg_cross(g_i)=3s_i+sum_{h!=i}(2-s_h)=4-S+4s_i`, independent of `i` modulo `4`.
    Add the quotient scalar equation for the full all-edge carrier: with internal residue `r_G` and incident
    sign sum `S_G`, atom `G` has total residue `r_G-S_G`; if these four residues are constant the carrier is
    a selector, otherwise the residual is a finite signed-`K_4` scalar obstruction.
    Formalize the signed-`K_4` closure classification: writing `r_G=2t_G`, closure with residue `lambda`
    is exactly `d_G==2t_G-lambda mod 4`; this yields empty/C4/matching/K4 for `k=0,4`, majority K3 or
    minority-centered star for `k=1,3`, and no full-carrier closure for `k=2`.
    Add shortened-pair-hit strict defect: a forced petal using `q=2,3` source vertices and hitting `r` other
    atoms has `delta_other>=r` or `r+1`, respectively; remaining petals compensate those omissions.
    Record the small-profile hit table: `q=2` tight means exactly one omission in every hit atom; `q=3`
    cannot be tight on pair targets alone and forces a singleton hit in a size-three/larger target.
    For `|A|<=3`, record the explicit alternatives: three empty supports; singleton plus two empties; pair
    plus two empties; two singletons plus an empty; triple plus two empties; pair+singleton plus an empty;
    or three singletons, as appropriate to `|A|`.
    Repackage the small-active case as a finite zero-filter blocker: every allowed support triple has
    nonempty zero-hit union, and each zero coordinate is uniquely hit by some repair triple.
    Add the private-column relaxation formula
    `c_{Z\{z}}(B)=c_Z(B)+p_z(B)`, where `p_z(B)` counts active support `B` columns whose zero trace is
    exactly `{z}`.
    Record private repair tuples: every zero-relaxed cover must use at least one support block or empty
    class supplied by `p_z`, because otherwise it would already be an unrelaxed cover.
    Add active lift-exclusion: a near-cover after deleting `a` has projected blocks covering `A\{a}`;
    replacing them by supports that put `a` in exactly one block must be capacity-deficient for every such
    choice.
    Record the support-family thickening form: for every allowed partition of `A\{a}`, all block
    thickenings `B union {a}` are absent from `F_Z`, and singleton `{a}` is absent when a new color class is
    allowed.
    Record the active witness taxonomy by empty capacity: one/two/three-block for `e_Z>=2`, two/three-block
    for `e_Z=1`, and exact three-block for `e_Z=0`.
    Add the `e_Z>=2` split: pure co-singleton core (`A\{a}` present for all `a`, `A` absent) versus a
    multi-block witness whose one-coordinate thickenings are absent.
    Add the first high-active `|A|=4` table: co-singleton core has all triples present, full/singletons
    absent, and no complementary pair-pair; `e_Z=0` has all singletons present and all pairs absent.
    Add the `|A|=4`, `e_Z=1` layer: no singleton/triple, pair/pair, or pair+two-singleton partition of
    `A`, but every three-point active deletion has a pair+singleton or three-singleton witness.
    Split it into singleton-core (all singletons present, all pairs/triples absent) and pair-witness
    subcases; in a pair-witness for `A\{a}`, both thickened pairs and singleton `{a}` are absent.  For
    `e_Z=0`, all pairs are essential missing blockers.
    Record that the `|A|=4` co-singleton pair layer is intersecting in `K_4`, hence contained in a star or
    triangle and has size at most three.
    Add the star/triangle pair templates: size-three pair layers are either a star or triangle, and the
    complementary three missing pairs are the pair-partition blockers; smaller layers add blockers.
    Add the full-minor `|A|=4` collapse: the only surviving four-active endpoint is singleton-only, with all
    pair/triple/full supports absent and essential.
    Add the `|A|=5` excess threshold: a triple or two disjoint pairs closes; the minimal pair-only
    obstruction is a triangle.
    Add the finite near-threshold deletion templates: for `|R|=m+s`, `1<=s<=3`, selectors inside `R` are
    exactly `R\D` with `|D|<=s-1`, so terminality is nonconstancy of `b-deg_D` on `R\D` for all
    `|D|<=s-1` (explicitly `D=empty`, singletons, and pairs).
    Add the full two-residue deletion equation: with `epsilon=0` on `R` and `epsilon=2` on `C`, a mixed
    selector `J\D` is exactly a set on which `epsilon(v)-deg_D(v)` is constant; restricting to `R` recovers
    the signed label `b=-deg_C`.
    Add the mirrored near-threshold templates on `C`: when `|C|=m+t>m`, the signed label
    `b_C(v)=2-deg_R(v)` has no deletion core `C\E` with `|E|<=t-1`.
    Add the mixed deletion target form: for `W=(R\D_R) union (C\D_C)`, selectorhood is equivalent to
    `deg_D=alpha` on retained `R` and `deg_D=alpha+2` on retained `C`.
    Add hereditary two-level relabeling: for `U subset J`, `epsilon_U(v)=epsilon(v)-deg_{J\U}(v)`, and
    `W=U\E` is a selector iff `epsilon_U(v)-deg_E(v)` is constant on `W`.
    Add two-level module exits: constant-`epsilon_U` modules lift selectors after a residue shift, so
    terminal mixed subbuckets have no large constant-label twin/module classes and satisfy the
    label-refined row-rank bound.
    Add mixed balanced-swap calculus: `omega_T=epsilon-deg_{J\T}`; old vertices change by `deg_Y-deg_X`,
    and incoming vertices have `epsilon-deg_{J\T}+deg_Y-deg_X`.
    In the Fano case, formalize the equivalent witness-graph condition: pair witnesses kill all Fano lines
    iff no Fano line vertex-covers the witness graph; every three-edge witness graph is line-covered.
   Also formalize the dual edge-cover version: the vertices are the seven Fano lines, each pair witness
   connects the two lines disjoint from it, and terminality is no isolated dual vertex.  Four witnesses
   then force the dual cover shape `P_3 disjoint union 2K_2`.
   Formalize the inclusion-minimal classification: every edge in a minimal no-isolated dual graph touches
   a degree-one vertex, so the dual graph is a star forest.  On seven vertices this gives the four-,
   five-, and six-witness shapes `K_{1,2}+2K_2`, `K_{1,4}+K_2`, `K_{1,3}+K_{1,2}`, and `K_{1,6}`; the
   last is primal `K_4` on the complement of a Fano line.
   Record the primal dictionary: a dual star centered at line `L` corresponds to bad kept pairs inside
   the four-point complement of `L`, with each leaf selecting the unique pair disjoint from both lines.
   Generalize the height inequality to non-exact boundaries with
   `H_X(g)=max{|Z|:Z subset X, sigma(Z)=g}` (or unavailable).  For every graph-compatible export `Y`,
   terminality gives `H_X(sigma(Y))-|Y|<=m-|B|`; exact Davenport top is the special case `H_X=h_X`.
   Near-top stability lemmas should provide lower bounds on this height function.
   Formalize the corrected basis-with-holes transfer: if `X` is a coordinate subbox with capacities
   `c_i<=3`, then for `g=sum a_i e_i`, `0<=a_i<=3`, one has `H_X(g)=sum a_i` when all `a_i<=c_i`, and
   `H_X(g)` is unavailable otherwise.  There is no uniform `h_box(g)-rho` lower bound for the same
   residue.  Exact-top carry and cut inequalities remain valid with the original deficit `d` on
   two-sided available cuts; unavailable cuts are label-incompatible.
   Record the coordinate two-sided availability table: capacity `3` allows nonzero coefficients
   `{1,2,3}`, capacity `2` allows only coefficient `2`, and capacity `0` or `1` allows none.
   Add the available-cut corollary: if `d<=1` and a minimal four-block has all singleton and pair cuts
   two-sided-compatible and available, then all four values lie on one coordinate, coefficients are in
   `{1,2}`, and minimality forces the positive atom `e_i^4` on a full-capacity coordinate.

A second equivalent attack surface is a one-large-class preselector.  For a labelled graph
`(H,alpha)` and a random `Z/4Z` coloring `gamma`, the event

   ```text
   gamma(v)=alpha(v)+deg_{H\gamma^{-1}(gamma(v))}(v) [MOD 4]
   ```

   has probability exactly `1/4` for each fixed vertex, by cyclic-shift symmetry on the closed
   neighbourhood.  Hence some color has a pre-satisfied fiber of size at least `|H|/16`.  If the
    same-color unsatisfied vertices have constant degree modulo `4` into that fiber, the fiber becomes a
    genuine retained class.  The unproved cleanup lemma is precisely removal of this same-color
    contamination; do not formalize the random preselector alone as the selector theorem.

   The Eulerian-orientation version should also be stated diagonally.  If `J` is even and has an
   Eulerian orientation, then for any `S` with `J[S]` even,

   ```text
   deg_{J[S]}(v)/2 = out_S(v) = in_S(v)       [MOD 2].
   ```

   Hence the mod-`4` selector becomes a large diagonal in/out parity selector in the directed bipartite
   double-cover: the left and right selected sets must be the same `S`.  Ordinary bipartite parity
   selectors are not enough unless they also prove this diagonal constraint.

   In matrix form, if `M` is the zero-diagonal orientation matrix over `F_2`, a sufficient formal target
   is a set `S` and bit `c` such that every row sum and every column sum of the principal submatrix
   `M[S,S]` is `c`.  Then all undirected degrees in `J[S]` are `2c [MOD 4]`.  The principal-submatrix
   diagonal constraint is the essential missing part.

   Do not replace this with the stronger claim that every labeled graph admits a full
   fixed-point coloring `gamma(v)=alpha(v)+deg_{H\gamma^{-1}(gamma(v))}(v) [MOD 4]`.  That partition
   statement is false: the path `a-b-c` with labels `(0,0,1)` has no such coloring.  The leaf equations
   exclude center colors `1` and `2`; center color `0` gives center outside-degree `1` or `2`, and
   center color `3` gives outside-degree `2`.  The valid target is only a single large retained class,
   and in the first-bit application the labels are the anti-degree labels above, not arbitrary labels.

   The constant-sum anti-degree specialization also must remain a one-large-class theorem.  If
   `alpha(v)+deg_H(v)=lambda`, then a full fixed-point coloring would be a partition into four
   classes satisfying

   ```text
   gamma(v) + deg_{H[gamma^{-1}(gamma(v))]}(v) == lambda [MOD 4],
   ```

   i.e. the four classes would have induced degree residues `lambda-i`.  This is stronger than needed
   and is not a deterministic import: Balister--Powierski--Scott--Tan's random-graph partition count
   gives a finite Poisson limit for the number of `q=4` partitions with one class of each residue, so
   such full partitions fail with positive limiting probability in `G(n,1/2)`.  A valid endpoint may
   instead be phrased as a partial anti-degree coloring covering at least a quarter of the vertices; the
   largest of its four classes would give the required `1/16` selector.

   A bounded deterministic partition into self-regular modulo-`4` induced classes would also suffice,
   but do not formalize it as known.  It is stronger than the one-large-class selector and contains the
   open Caro--Krasikov--Roditty bounded-partition problem for fixed `q>2` as a special divisibility
   case.  The Balister--Powierski--Scott--Tan results are random-graph counts, not arbitrary-graph
   partition theorems.

   ```text
   every symmetric zero-diagonal integer matrix with even row sums has a principal submatrix
   on at least n/32 rows whose row sums are congruent modulo 4.
   ```

   This is equivalent to the even selector and would imply `HasParityToModFourLoss64FixedWitnessLift`.
   Fixed-orientation bidirected parity is not a replacement for the principal-submatrix statement.

   A useful failed internal route is bounded layer refinement.  Choosing a largest total-degree class
   costs `2`, and successively synchronizing degrees into exposed discarded layers costs factors of `4`.
   Previously exposed layers stay synchronized under further refinement, but the final retained set has
   one new self-layer in its complement whose contribution is not controlled.  Closing that terminal
   self-layer at no extra loss would prove the desired `1/32` even selector; without it, the argument is
   only a diagnostic and must not be formalized as the theorem.  The Scott--Hunter bipartite theorem
   would become relevant only after reducing this terminal obstruction to a chamber with no uncontrolled
   internal edges on the retained side; the present principal-submatrix terminal layer is not yet
   bipartite in that sense.  Nor does a longer finite refinement close the proof: every extra refinement
   synchronizes degrees into the previous retained chamber only on a later subset, leaving a fresh
   newly discarded self-layer whose contribution to the proposed output is still uncontrolled.

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

6. Prove or replace the finite affine-selector block:

   ```lean
   HasExactSmallModulusAffineCrossSelector j m
   ```

   for `m = 11, 12`, and for `13 <= m < 17` with `j = 2, 3`.  The exact fixed-witness targets remain
   available, and the old package still closes `(13,3)` by the generic Ramsey fallback
   `R(13,13) <= choose 24 12 <= 8^6 * 13`.  The extended package
   `HigherBitSmallModulusAffineSelectorsFromElevenExtended` exposes `(13,3)` as an explicit affine
   selector field via
   `hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus_thirteen_to_seventeen_with_thirteen_three`.
   The preferred dyadic formulation is affine cancellation because it matches the uniform saturated
   route.  Lean proves that in `13 <= m < 17`, `j = 4` is impossible from the small-modulus condition
   `2^j < m`.

7. For the saturated handoff, prove the uniform higher-bit affine-selector package

   ```lean
   HigherBitSmallModulusAffineSelectorsFromEleven
   ```

   by the affine-pair/split-marker theorem from `proof.md` Lemmas 10.4e--10.4j.  The uniform `m >= 17`
   field already uses the existing residual assumptions:

   ```lean
   2 ^ j < m
   17 <= m
   HasFixedModulusWitnessOfCard G ((2 ^ j)^6 * m) (2 ^ j)
   ```

   and the saturated `FR^sat` provenance/support-decrease proposition.  This is no longer a dyadic
   carry gap; it is a formalization of the saturated q-marker routing already written in the proof notes.

The hardest remaining non-terminal mathematical gap is therefore the large-support first-bit
`HasLargeEvenDegreeModFourLoss32InducedSubgraph`, unless the project chooses to import an external
fixed-modulus-four congruent-degree theorem strong enough to imply it.

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
