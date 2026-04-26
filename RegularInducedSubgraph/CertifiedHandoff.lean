import RegularInducedSubgraph.Modular.Asymptotic
import RegularInducedSubgraph.SevenVertexCertificate

namespace RegularInducedSubgraph

/--
Final handoff with the seven-vertex finite certificate already instantiated.  The remaining
assumptions are the large-gap dyadic window and the fixed-witness terminal regularization theorem.
-/
theorem targetStatement_of_proofMdFinalHandoff_of_fixedWitnessTerminalRegularization_certifiedSeven
    {D : ℕ}
    (largeGapDyadicWindow :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7)
    (terminalRegularization : HasPolynomialCostFixedWitnessTerminalRegularization D) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_fixedWitnessTerminalRegularization
      sevenVertexFourOrFiveBoolCertificate largeGapDyadicWindow terminalRegularization

/--
External-block terminal handoff with the seven-vertex finite certificate already instantiated.  This
is the obstruction-safe terminal-facing endpoint: it only needs the positive dyadic fixed-witness
external-block self-bridge and the large-gap dyadic window.
-/
theorem targetStatement_of_proofMdFinalHandoff_of_fixedWitnessExternalBlockSelfBridge_certifiedSeven
    {D : ℕ}
    (largeGapDyadicWindow :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap 7)
    (fixedWitnessExternalBlockSelfBridge :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_fixedWitnessExternalBlockSelfBridge
      sevenVertexFourOrFiveBoolCertificate largeGapDyadicWindow fixedWitnessExternalBlockSelfBridge

/--
Strongest current viable handoff after discharging the seven-vertex certificate internally.  The
remaining inputs are the mod-four loss theorem, the Ramsey-10 table, the D=5 fixed-witness
external-block terminal bridge, the finite `4 -> 8` cases through `m = 16`, and the residual
large-modulus dyadic window from `m = 17`.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_fourToEightTargetsToSixteen_and_twiceLargeGapJAtLeastTwoSmallModulusFromSeventeen_certifiedSeven
    (modFourZeroLossFive : HasModFourZeroLossFiveInducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (fourToEightTargetEleven : HasFourToEightTargetElevenFixedWitnessLift)
    (fourToEightTargetTwelve : HasFourToEightTargetTwelveFixedWitnessLift)
    (h13_2 : HasExactSmallModulusFixedWitnessDyadicLift 2 13)
    (h14_2 : HasExactSmallModulusFixedWitnessDyadicLift 2 14)
    (h14_3 : HasExactSmallModulusFixedWitnessDyadicLift 3 14)
    (h15_2 : HasExactSmallModulusFixedWitnessDyadicLift 2 15)
    (h15_3 : HasExactSmallModulusFixedWitnessDyadicLift 3 15)
    (h16_2 : HasExactSmallModulusFixedWitnessDyadicLift 2 16)
    (h16_3 : HasExactSmallModulusFixedWitnessDyadicLift 3 16)
    (twiceLargeGapJAtLeastTwoSmallModulusFromSeventeen :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 17) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_fourToEightTargetsToSixteen_and_twiceLargeGapJAtLeastTwoSmallModulusFromSeventeen
      sevenVertexFourOrFiveBoolCertificate modFourZeroLossFive ramseyTenSmallTable
      fixedWitnessExternalBlockSelfBridgeFive fourToEightTargetEleven fourToEightTargetTwelve
      h13_2 h14_2 h14_3 h15_2 h15_3 h16_2 h16_3
      twiceLargeGapJAtLeastTwoSmallModulusFromSeventeen

/--
Sharpest current Lean-facing handoff with the seven-vertex finite certificate already instantiated.
The first-bit input is the even-degree loss-`32` selector, and the higher-bit dyadic work is packaged
as affine cross-selectors from `m = 11` onward.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
      sevenVertexFourOrFiveBoolCertificate evenDegreeModFourLoss32 ramseyTenSmallTable
      fixedWitnessExternalBlockSelfBridgeFive higherBitSelectors

/--
Certified-seven handoff using the extended higher-bit selector package that explicitly includes
the finite `(m,j)=(13,3)` affine selector.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromElevenExtended_certifiedSeven
    (modFourZeroLossFive : HasModFourZeroLossFiveInducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromElevenExtended) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_modFourZeroLossFive_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromElevenExtended
    sevenVertexFourOrFiveBoolCertificate modFourZeroLossFive ramseyTenSmallTable
    fixedWitnessExternalBlockSelfBridgeFive higherBitSelectors

/--
Certified-seven version of the sharp handoff with the D=5 terminal input expanded to the finite
Ramsey frontier: the q=16 bound plus the positive-bit tail bounds.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
      sevenVertexFourOrFiveBoolCertificate evenDegreeModFourLoss32 ramseyTenSmallTable
      cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/--
Certified-seven final handoff with both exposed frontiers sharpened: first-bit work only starts at
large even-degree supports, and terminal work is the explicit D=5 finite-Ramsey frontier.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (largeEvenDegreeModFourLoss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
      sevenVertexFourOrFiveBoolCertificate largeEvenDegreeModFourLoss32 ramseyTenSmallTable
      cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/--
Certified-seven large-support handoff with the terminal tail written as a `q^6` polynomial Ramsey
bound for `q = 2^j`.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_powSixTail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (largeEvenDegreeModFourLoss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 6)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_powSixTail_and_higherBitAffineSelectorsFromEleven
    sevenVertexFourOrFiveBoolCertificate largeEvenDegreeModFourLoss32 ramseyTenSmallTable
    cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/--
Certified-seven final handoff with the first-bit frontier stated as an arbitrary-set 32-color
mod-four congruent-degree coloring theorem.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (modFourColoringBound32 : HasModFourCongruentDegreeColoringBound 32)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
    sevenVertexFourOrFiveBoolCertificate modFourColoringBound32 ramseyTenSmallTable
    fixedWitnessExternalBlockSelfBridgeFive higherBitSelectors

/--
Certified-seven final handoff with the first-bit frontier weakened to an even-degree mod-four
congruent-degree coloring theorem using any `C <= 32` colors.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (evenModFourColoringBound : HasEvenDegreeModFourCongruentDegreeColoringBound C)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
    hCpos hC sevenVertexFourOrFiveBoolCertificate evenModFourColoringBound
    ramseyTenSmallTable fixedWitnessExternalBlockSelfBridgeFive higherBitSelectors

/--
Certified-seven external-block frontier certificate.  This keeps the terminal input at the real
fixed-witness external-block bridge instead of expanding it to an arbitrary Ramsey-tail sufficient
condition.
-/
structure CertifiedProofMdExternalBlockFrontierCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  ramseyTenSmallTable : RamseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The certified external-block frontier certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdExternalBlockFrontierCertificate
    (h : CertifiedProofMdExternalBlockFrontierCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    h.evenDegreeModFourLoss32 h.ramseyTenSmallTable h.fixedWitnessExternalBlockSelfBridgeFive
    h.higherBitSelectors

/--
External-block frontier certificate using the weaker even-degree bounded-coloring first-bit surface.
-/
structure CertifiedProofMdExternalBlockFrontierColoringCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  ramseyTenSmallTable : RamseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The coloring-form certified external-block frontier certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdExternalBlockFrontierColoringCertificate
    (h : CertifiedProofMdExternalBlockFrontierColoringCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound
    h.ramseyTenSmallTable h.fixedWitnessExternalBlockSelfBridgeFive h.higherBitSelectors

/--
External-block frontier certificate using the stronger arbitrary-set 32-color mod-four partition
theorem.
-/
structure CertifiedProofMdExternalBlockFrontierModFourColoringCertificate : Type where
  modFourColoringBound32 : HasModFourCongruentDegreeColoringBound 32
  ramseyTenSmallTable : RamseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The arbitrary-set coloring-form certified external-block frontier certificate closes the target. -/
theorem targetStatement_of_certifiedProofMdExternalBlockFrontierModFourColoringCertificate
    (h : CertifiedProofMdExternalBlockFrontierModFourColoringCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    h.modFourColoringBound32 h.ramseyTenSmallTable h.fixedWitnessExternalBlockSelfBridgeFive
    h.higherBitSelectors

/--
Non-Ramsey part of the certified external-block frontier.  This deliberately leaves
`RamseyTenSmallTable` outside the package, so the remaining work can focus on the first-bit selector,
the D=5 positive-dyadic external-block bridge, and the higher-bit affine selectors.
-/
structure CertifiedProofMdExternalBlockNonRamseyRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- Adding the Ramsey-10 table to the non-Ramsey rest package recovers the full frontier certificate. -/
def certifiedProofMdExternalBlockFrontierCertificate_of_nonRamseyRest
    (h : CertifiedProofMdExternalBlockNonRamseyRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    CertifiedProofMdExternalBlockFrontierCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  ramseyTenSmallTable := ramseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitSelectors := h.higherBitSelectors

/-- The non-Ramsey rest package plus the Ramsey-10 table closes the target statement. -/
theorem targetStatement_of_certifiedProofMdExternalBlockNonRamseyRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockFrontierCertificate
    (certifiedProofMdExternalBlockFrontierCertificate_of_nonRamseyRest h ramseyTenSmallTable)

/--
Rest-only certificate using the sharp first-bit coloring surface.  This is the same non-Ramsey rest
package, but it asks for an even-degree mod-four congruent-degree coloring theorem with at most 32
colors instead of asking directly for the loss-32 selector.
-/
structure CertifiedProofMdExternalBlockNonRamseyColoringRestCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The coloring-form rest package implies the loss-32 rest package by taking the largest color class. -/
def certifiedProofMdExternalBlockNonRamseyRestCertificate_of_coloringRest
    (h : CertifiedProofMdExternalBlockNonRamseyColoringRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyRestCertificate where
  evenDegreeModFourLoss32 :=
    hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
      h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitSelectors := h.higherBitSelectors

/-- The coloring-form non-Ramsey rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyColoringRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyColoringRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockNonRamseyRestCertificate_and_ramseyTenSmallTable
    (certifiedProofMdExternalBlockNonRamseyRestCertificate_of_coloringRest h)
    ramseyTenSmallTable

/--
Rest-only certificate using the stronger loss-5 all-zero mod-four first-bit surface.  This is useful
when the first-bit work is proved in the stronger literature-shaped form.
-/
structure CertifiedProofMdExternalBlockNonRamseyModFourZeroRestCertificate : Type where
  modFourZeroLossFive : HasModFourZeroLossFiveInducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The loss-5 zero-mod-four rest package implies the loss-32 rest package. -/
def certifiedProofMdExternalBlockNonRamseyRestCertificate_of_modFourZeroRest
    (h : CertifiedProofMdExternalBlockNonRamseyModFourZeroRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyRestCertificate where
  evenDegreeModFourLoss32 :=
    hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourLoss32InducedSubgraph
      (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_modFourZeroLossFiveInducedSubgraph
        h.modFourZeroLossFive)
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitSelectors := h.higherBitSelectors

/-- The loss-5 zero-mod-four non-Ramsey rest package plus the Ramsey-10 table closes the target. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyModFourZeroRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyModFourZeroRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockNonRamseyRestCertificate_and_ramseyTenSmallTable
    (certifiedProofMdExternalBlockNonRamseyRestCertificate_of_modFourZeroRest h)
    ramseyTenSmallTable

/--
Rest-only certificate with higher-bit work stated as fixed-witness finite targets instead of affine
selectors.  Affine selectors imply this package, but finite certificates can target it directly.
-/
structure CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/-- The fixed-target rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven
    sevenVertexFourOrFiveBoolCertificate h.evenDegreeModFourLoss32 ramseyTenSmallTable
    h.fixedWitnessExternalBlockSelfBridgeFive h.higherBitTargets

/--
Rest-only certificate with the extended fixed-witness higher-bit package, including the explicit
`(m,j)=(13,3)` field.
-/
structure CertifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromElevenExtended

/-- The extended fixed-target rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromElevenExtended
    sevenVertexFourOrFiveBoolCertificate h.evenDegreeModFourLoss32 ramseyTenSmallTable
    h.fixedWitnessExternalBlockSelfBridgeFive h.higherBitTargets

/-- Forget the explicit `(13,3)` field from the extended fixed-target rest package. -/
def certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_of_extendedFixedTargetsRest
    (h : CertifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitTargets := higherBitSmallModulusFixedWitnessTargetsFromEleven_of_extendedTargets h.higherBitTargets

/--
Rest-only certificate with a mixed higher-bit surface: direct fixed-witness targets for
`m = 11, 12`, and reduced fixed-witness targets only from `m = 13` onward.
-/
structure CertifiedProofMdExternalBlockNonRamseyMixedFixedTargetsRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  fourToEightTargetEleven : HasFourToEightTargetElevenFixedWitnessLift
  fourToEightTargetTwelve : HasFourToEightTargetTwelveFixedWitnessLift
  higherBitTargetsFromThirteen : HigherBitSmallModulusFixedWitnessTargetsFromThirteen

/-- Forget the exact `m = 11, 12` field shape from the full fixed-target rest package. -/
def certifiedProofMdExternalBlockNonRamseyMixedFixedTargetsRestCertificate_of_fixedTargetsRest
    (h : CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyMixedFixedTargetsRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  fourToEightTargetEleven := by
    intro n hambient G hinput
    exact h.higherBitTargets.h11_2 hambient G hinput
  fourToEightTargetTwelve := by
    intro n hambient G hinput
    exact h.higherBitTargets.h12_2 hambient G hinput
  higherBitTargetsFromThirteen :=
    higherBitSmallModulusFixedWitnessTargetsFromThirteen_of_targetsFromEleven h.higherBitTargets

/-- The mixed fixed-target rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyMixedFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyMixedFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_fourToEightTargetsElevenTwelve_and_higherBitFixedWitnessTargetsFromThirteen
    sevenVertexFourOrFiveBoolCertificate h.evenDegreeModFourLoss32 ramseyTenSmallTable
    h.fixedWitnessExternalBlockSelfBridgeFive h.fourToEightTargetEleven h.fourToEightTargetTwelve
    h.higherBitTargetsFromThirteen

/--
Rest-only certificate with direct fixed-witness targets for `m = 11, 12` and affine selectors only
for the `m >= 13` higher-bit tail.
-/
structure CertifiedProofMdExternalBlockNonRamseyMixedAffineTailRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  fourToEightTargetEleven : HasFourToEightTargetElevenFixedWitnessLift
  fourToEightTargetTwelve : HasFourToEightTargetTwelveFixedWitnessLift
  higherBitSelectorsFromThirteen : HigherBitSmallModulusAffineSelectorsFromThirteen

/-- Forget the `m = 11, 12` affine selector witnesses from the full affine rest package. -/
def certifiedProofMdExternalBlockNonRamseyMixedAffineTailRestCertificate_of_nonRamseyRest
    (h : CertifiedProofMdExternalBlockNonRamseyRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyMixedAffineTailRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  fourToEightTargetEleven :=
    hasFourToEightTargetElevenFixedWitnessLift_of_affineCrossSelector h.higherBitSelectors.h11_2
  fourToEightTargetTwelve :=
    hasFourToEightTargetTwelveFixedWitnessLift_of_affineCrossSelector h.higherBitSelectors.h12_2
  higherBitSelectorsFromThirteen :=
    higherBitSmallModulusAffineSelectorsFromThirteen_of_selectorsFromEleven h.higherBitSelectors

/-- The mixed affine-tail rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyMixedAffineTailRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyMixedAffineTailRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_fourToEightTargetsElevenTwelve_and_higherBitAffineSelectorsFromThirteen
    sevenVertexFourOrFiveBoolCertificate h.evenDegreeModFourLoss32 ramseyTenSmallTable
    h.fixedWitnessExternalBlockSelfBridgeFive h.fourToEightTargetEleven h.fourToEightTargetTwelve
    h.higherBitSelectorsFromThirteen

/-- The affine-selector rest package implies the fixed-target rest package. -/
def certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_of_nonRamseyRest
    (h : CertifiedProofMdExternalBlockNonRamseyRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitTargets :=
    higherBitSmallModulusFixedWitnessTargetsFromEleven_of_affineSelectors h.higherBitSelectors

/--
Rest-only certificate with both softer first-bit coloring and fixed-witness higher-bit target
surfaces exposed.
-/
structure CertifiedProofMdExternalBlockNonRamseyColoringFixedTargetsRestCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/-- The coloring/fixed-target rest package plus the Ramsey-10 table closes the target statement. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyColoringFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyColoringFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven
    sevenVertexFourOrFiveBoolCertificate
    (hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
      h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound)
    ramseyTenSmallTable h.fixedWitnessExternalBlockSelfBridgeFive h.higherBitTargets

/--
Rest-only certificate using the extended affine-selector package.  The extra `(13,3)` affine selector
is accepted but not needed by the current default route.
-/
structure CertifiedProofMdExternalBlockNonRamseyExtendedRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromElevenExtended

/-- The extended-selector rest package implies the fixed-target rest package. -/
def certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_of_extendedRest
    (h : CertifiedProofMdExternalBlockNonRamseyExtendedRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitTargets := higherBitSmallModulusFixedWitnessTargetsFromEleven_of_extended h.higherBitSelectors

/-- The extended-selector rest package implies the extended fixed-target rest package. -/
def certifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate_of_extendedRest
    (h : CertifiedProofMdExternalBlockNonRamseyExtendedRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyExtendedFixedTargetsRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitTargets := higherBitSmallModulusFixedWitnessTargetsFromElevenExtended_of_extended
    h.higherBitSelectors

/-- The extended-selector non-Ramsey rest package plus the Ramsey-10 table closes the target. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyExtendedRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyExtendedRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (certifiedProofMdExternalBlockNonRamseyFixedTargetsRestCertificate_of_extendedRest h)
    ramseyTenSmallTable

/--
Rest-only certificate with the terminal input reduced to the first unproved dyadic terminal slice
`j >= 4`; the `j = 1,2,3` external-block cases are already proved in Lean.
-/
structure CertifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFiveFromFour :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFour
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The terminal-from-four rest package implies the monolithic non-Ramsey rest package. -/
def certifiedProofMdExternalBlockNonRamseyRestCertificate_of_terminalFromFourRest
    (h : CertifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFive :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_fromFour
      h.fixedWitnessExternalBlockSelfBridgeFiveFromFour
  higherBitSelectors := h.higherBitSelectors

/-- The terminal-from-four non-Ramsey rest package plus the Ramsey-10 table closes the target. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockNonRamseyRestCertificate_and_ramseyTenSmallTable
    (certifiedProofMdExternalBlockNonRamseyRestCertificate_of_terminalFromFourRest h)
    ramseyTenSmallTable

/--
Rest-only certificate with terminal work split into the exact q=16 slice and the large-modulus
`j >= 5` slice.
-/
structure CertifiedProofMdExternalBlockNonRamseyTerminalSplitRestCertificate : Type where
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  fixedWitnessExternalBlockSelfBridgeFiveAtFour :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveAtFour
  fixedWitnessExternalBlockSelfBridgeFiveFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The terminal split rest package implies the terminal-from-four rest package. -/
def certifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate_of_terminalSplitRest
    (h : CertifiedProofMdExternalBlockNonRamseyTerminalSplitRestCertificate) :
    CertifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate where
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  fixedWitnessExternalBlockSelfBridgeFiveFromFour :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFour_of_atFour_and_fromFive
      h.fixedWitnessExternalBlockSelfBridgeFiveAtFour
      h.fixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitSelectors := h.higherBitSelectors

/-- The terminal split non-Ramsey rest package plus the Ramsey-10 table closes the target. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyTerminalSplitRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyTerminalSplitRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate_and_ramseyTenSmallTable
    (certifiedProofMdExternalBlockNonRamseyTerminalFromFourRestCertificate_of_terminalSplitRest h)
    ramseyTenSmallTable

/--
Fully split non-Ramsey rest certificate.  This exposes the first-bit work as an even-degree coloring
theorem, the terminal work as q=16 plus `j >= 5`, and the higher-bit work as fixed-witness targets.
-/
structure CertifiedProofMdExternalBlockNonRamseyFullySplitRestCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  fixedWitnessExternalBlockSelfBridgeFiveAtFour :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveAtFour
  fixedWitnessExternalBlockSelfBridgeFiveFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/-- The fully split non-Ramsey rest package plus the Ramsey-10 table closes the target. -/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyFullySplitRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyFullySplitRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement := by
  have hterminal :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_fromFour
      (hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFour_of_atFour_and_fromFive
        h.fixedWitnessExternalBlockSelfBridgeFiveAtFour
        h.fixedWitnessExternalBlockSelfBridgeFiveFromFive)
  exact
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven
      sevenVertexFourOrFiveBoolCertificate
      (hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
        h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound)
      ramseyTenSmallTable hterminal h.higherBitTargets

/--
Fully split non-Ramsey rest certificate with the exact `j = 4` terminal slice discharged by the
existing q=16 Ramsey reduction.  The only terminal field left here is the genuine `j >= 5` tail.
-/
structure CertifiedProofMdExternalBlockNonRamseyTerminalTailFixedTargetsRestCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  fixedWitnessExternalBlockSelfBridgeFiveFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/--
The terminal-tail/fixed-target non-Ramsey rest package plus the Ramsey-10 table closes the target.
-/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyTerminalTailFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyTerminalTailFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement := by
  have hterminal :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_fromFive
      h.cliqueOrIndepSetBound16 h.fixedWitnessExternalBlockSelfBridgeFiveFromFive
  exact
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven
      sevenVertexFourOrFiveBoolCertificate
      (hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
        h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound)
      ramseyTenSmallTable hterminal h.higherBitTargets

/--
Loss-5 first-bit version of the terminal-tail/fixed-target non-Ramsey rest package.  This is the
smallest current certified-facing list of non-Ramsey assumptions except for replacing loss-5 by the
weaker coloring surface.
-/
structure CertifiedProofMdExternalBlockNonRamseyModFourZeroTerminalTailFixedTargetsRestCertificate :
    Type where
  modFourZeroLossFive : HasModFourZeroLossFiveInducedSubgraph
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  fixedWitnessExternalBlockSelfBridgeFiveFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/--
The loss-5 terminal-tail/fixed-target non-Ramsey rest package plus the Ramsey-10 table closes the
target.
-/
theorem
    targetStatement_of_certifiedProofMdExternalBlockNonRamseyModFourZeroTerminalTailFixedTargetsRestCertificate_and_ramseyTenSmallTable
    (h : CertifiedProofMdExternalBlockNonRamseyModFourZeroTerminalTailFixedTargetsRestCertificate)
    (ramseyTenSmallTable : RamseyTenSmallTable) :
    TargetStatement := by
  have hterminal :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_fromFive
      h.cliqueOrIndepSetBound16 h.fixedWitnessExternalBlockSelfBridgeFiveFromFive
  have hfirst : HasEvenDegreeModFourLoss32InducedSubgraph :=
    hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourLoss32InducedSubgraph
      (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_modFourZeroLossFiveInducedSubgraph
        h.modFourZeroLossFive)
  exact
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven
      sevenVertexFourOrFiveBoolCertificate hfirst ramseyTenSmallTable hterminal
      h.higherBitTargets

/--
Certified-seven final handoff with both exposed frontiers sharpened: the first bit is an arbitrary-set
32-color mod-four coloring theorem, and terminal work is the explicit D=5 finite-Ramsey frontier.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (modFourColoringBound32 : HasModFourCongruentDegreeColoringBound 32)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
    sevenVertexFourOrFiveBoolCertificate modFourColoringBound32 ramseyTenSmallTable
    cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/--
Certified-seven final handoff with both exposed frontiers sharpened: the first bit is the weak
even-degree coloring theorem with `C <= 32`, and terminal work is the explicit D=5 finite-Ramsey
frontier.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (evenModFourColoringBound : HasEvenDegreeModFourCongruentDegreeColoringBound C)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourLoss32InducedSubgraph
      (hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
        hCpos hC evenModFourColoringBound))
    ramseyTenSmallTable cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/--
Current sharp frontier certificate with the seven-vertex finite base already discharged by
`SevenVertexCertificate`.
-/
structure CertifiedProofMdCurrentFrontierCertificate : Type where
  largeEvenDegreeModFourLoss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The certified current frontier certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierCertificate
    (h : CertifiedProofMdCurrentFrontierCertificate) :
    TargetStatement := by
  exact
    targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
      h.largeEvenDegreeModFourLoss32 h.ramseyTenSmallTable h.cliqueOrIndepSetBound16
      h.cliqueOrIndepSetBoundTail h.higherBitSelectors

/--
Current sharp frontier certificate using the weakest first-bit surface currently wired in Lean:
an even-degree mod-four congruent-degree coloring theorem with at most 32 colors.
-/
structure CertifiedProofMdCurrentFrontierColoringCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The coloring-form certified current frontier certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierColoringCertificate
    (h : CertifiedProofMdCurrentFrontierColoringCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound
    h.ramseyTenSmallTable h.cliqueOrIndepSetBound16 h.cliqueOrIndepSetBoundTail
    h.higherBitSelectors

/--
Current frontier certificate using the stronger arbitrary-set 32-color mod-four partition theorem.
-/
structure CertifiedProofMdCurrentFrontierModFourColoringCertificate : Type where
  modFourColoringBound32 : HasModFourCongruentDegreeColoringBound 32
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The arbitrary-set coloring-form current frontier certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierModFourColoringCertificate
    (h : CertifiedProofMdCurrentFrontierModFourColoringCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_modFourColoringBound32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven_certifiedSeven
    h.modFourColoringBound32 h.ramseyTenSmallTable h.cliqueOrIndepSetBound16
    h.cliqueOrIndepSetBoundTail h.higherBitSelectors

/-!
## Integrated final-facing handoff surfaces

The declarations below are packaging-only: they do not strengthen any mathematical assumption.  They
collect the current Ramsey, exact-`42`, terminal, and first-bit/co-cut frontier surfaces behind
projection aliases that downstream orchestration can consume without opening the lower-level files.
-/

/-- The unified Ramsey consequence bundle supplies exactly the isolated dyadic regular-10 target. -/
theorem hasRamseyTenRegularAtDyadicTarget_of_ramseyTenR45GlobalConsequenceBundle
    (h : RamseyTenR45GlobalConsequenceBundle) : HasRamseyTenRegularAtDyadicTarget := by
  intro V _ _ G hcard
  exact h.toHasRegularInducedSubgraphOfCard_ten_40960 G hcard

/--
Normalized exact-`42` Ramsey consumer surface.  It keeps the profiled `R(3,10) <= 42` row paired
with the local degree-`9` endpoint ledgers, and separately carries the global Ramsey-10 consequences
needed by the proof-md handoff.
-/
structure CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate : Prop where
  exact42WithMiddleSplits : RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits
  ramseyConsequences : RamseyTenR45GlobalConsequenceBundle

/-- Build the normalized exact-`42` consumer surface from the combined Ramsey handoff. -/
theorem certifiedProofMdExact42ConsumerNormalizedRamseyCertificate_of_middleDegreeEndpointProfile
    (h : RamseyTenR45MiddleDegreeEndpointCertificateWithExact42Profile) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate where
  exact42WithMiddleSplits := h.toExact42WithMiddleSplits
  ramseyConsequences := h.toGlobalConsequenceBundle

/-- Project the exact-`42` profile with middle-degree ledgers. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toExact42WithMiddleSplits
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits :=
  h.exact42WithMiddleSplits

/-- Project the profiled exact-`42` surface. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toExact42ProfileSurface
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    RamseyThreeTenExact42ThreeRowProfileSurface :=
  h.exact42WithMiddleSplits.toExact42ProfileSurface

/-- Project the local endpoint ledger bundle paired with the exact-`42` profile. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toLocalLedgerBundle
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    RamseyTenR45MiddleDegreeLocalLedgerBundle :=
  h.exact42WithMiddleSplits.toLocalLedgerBundle

/-- Project the low-row `R(3,10) <= 42` consequence. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toThreeTenFortyTwo
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    HasCliqueOrIndepSetBound 3 10 42 :=
  h.exact42WithMiddleSplits.toThreeTenFortyTwo

/-- Project the unified Ramsey global consequence bundle. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toGlobalConsequenceBundle
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.ramseyConsequences

/-- Project the relaxed `R(4,5) <= 27` consequence. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toR45TwentySeven
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    HasCliqueOrIndepSetBound 4 5 27 :=
  h.ramseyConsequences.toHasCliqueOrIndepSetBound_four_five_twenty_seven

/-- Project the propagated `R(10,10)` consequence. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toR10Ten39246
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    HasCliqueOrIndepSetBound 10 10 39246 :=
  h.ramseyConsequences.toHasCliqueOrIndepSetBound_10_10_39246

/-- Project the regular induced `10`-set consequence at the dyadic target. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toRamseyTenRegular
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    HasRamseyTenRegularAtDyadicTarget :=
  hasRamseyTenRegularAtDyadicTarget_of_ramseyTenR45GlobalConsequenceBundle
    h.ramseyConsequences

/-- Project the admissible-bound consequence at `40960`. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toTenMemAdmissibleBounds_40960
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    10 ∈ admissibleBounds 40960 :=
  h.ramseyConsequences.toTenMemAdmissibleBounds_40960

/-- Project the extremal-function lower bound at `40960`. -/
theorem CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate.toTenLeF_40960
    (h : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate) :
    10 ≤ F 40960 :=
  h.ramseyConsequences.toTenLeF_40960

/--
Final-facing terminal mixed-target core imports.  This is just the concrete homogeneous-carry import
triple re-exposed under the proof-md handoff namespace.
-/
structure CertifiedProofMdTerminalMixedTargetCoreImports : Prop where
  terminalTrichotomy : HasHomogeneousMixedCarryTerminalTrichotomyReduction
  supportCompression : HasHomogeneousMixedCarrySupportCompressionReduction
  affineArf : HasHomogeneousMixedCarryAffineArfCertificateReduction

/-- Build the terminal mixed-target core imports from the two genuine residual reductions. -/
theorem certifiedProofMdTerminalMixedTargetCoreImports_of_reductions
    (hsupport : HasHomogeneousMixedCarrySupportCompressionReduction)
    (harf : HasHomogeneousMixedCarryAffineArfCertificateReduction) :
    CertifiedProofMdTerminalMixedTargetCoreImports where
  terminalTrichotomy := homogeneousMixedCarryTerminalTrichotomyReduction
  supportCompression := hsupport
  affineArf := harf

/-- Repackage the handoff imports as the existing homogeneous-carry import bundle. -/
theorem CertifiedProofMdTerminalMixedTargetCoreImports.toHomogeneousCarryImports
    (h : CertifiedProofMdTerminalMixedTargetCoreImports) :
    FirstBitTerminalMixedTypeHomogeneousCarryImports where
  terminalTrichotomy := h.terminalTrichotomy
  supportCompression := h.supportCompression
  affineArf := h.affineArf

/-- Apply the mixed-target trichotomy from the handoff import surface. -/
theorem CertifiedProofMdTerminalMixedTargetCoreImports.trichotomy
    (h : CertifiedProofMdTerminalMixedTargetCoreImports)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : SimpleGraph ι) (U : Finset ι) (tau : ι → ℕ) (m : ℕ) :
    HomogeneousMixedCarryTerminalTrichotomy Q U tau m :=
  h.toHomogeneousCarryImports.trichotomy Q U tau m

/-- Apply support compression from the terminal mixed-target import surface. -/
theorem CertifiedProofMdTerminalMixedTargetCoreImports.smallCoreResidual
    (h : CertifiedProofMdTerminalMixedTargetCoreImports)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : SimpleGraph ι} {U : Finset ι} {tau : ι → ℕ} {m : ℕ}
    (hres : HomogeneousMixedCarrySmallKernelConsistentResidual Q U tau m) :
    ∃ J T : Finset ι, ∃ c : ℕ, HomogeneousMixedCarrySmallCoreResidual Q U tau m J T c :=
  h.toHomogeneousCarryImports.smallCoreResidual hres

/-- Apply the affine-Arf residual extraction from the terminal mixed-target import surface. -/
theorem CertifiedProofMdTerminalMixedTargetCoreImports.arfCertificate
    (h : CertifiedProofMdTerminalMixedTargetCoreImports)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : SimpleGraph ι} {U : Finset ι} {tau : ι → ℕ}
    (hinc : HomogeneousMixedCarryAffineInconsistency Q U tau) :
    HomogeneousMixedCarryArfCertificateResidual Q U tau :=
  h.toHomogeneousCarryImports.arfCertificate hinc

/--
Current first-bit/co-cut obligation surface: final branch wrappers, available-coordinate cut imports,
and post-quotient anchored-packing rows are presented as one reusable handoff object.
-/
structure CertifiedProofMdFirstBitCoCutObligationSurface
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Prop where
  finalAvailableCut :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutAndPostQuotientAnchoredPacking
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Build the first-bit/co-cut obligation surface from the available-cut and packing packages. -/
theorem certifiedProofMdFirstBitCoCutObligationSurface_of_parts
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (hfinal :
      FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
        Basis WithHoles PositiveAtom)
    (hpacking :
      PositiveAtomPostQuotientAnchoredPackingImports
        AnchoredPacking TraceTwinFree packingSize
        WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  finalAvailableCut :=
    firstBitTerminalPacketFinalBranchWrappersWithAvailableCutAndPostQuotientAnchoredPacking_of_parts
      hfinal hpacking

/-- Recover the available-cut final wrapper from the co-cut obligation surface. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toAvailableCutFinalWrapper
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom :=
  h.finalAvailableCut.to_availableCutFinalWrapper

/-- Project the ordinary final branch wrappers from the co-cut obligation surface. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toFinalBranchWrappers
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappers :=
  h.finalAvailableCut.to_finalBranches

/-- Project the available-cut positive-atom import package from the co-cut obligation surface. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toAvailableCutPositiveAtom
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalAvailableCutPositiveAtomBoundaryImports Basis WithHoles PositiveAtom :=
  h.finalAvailableCut.to_availableCutPositiveAtom

/-- Project the raw available-cut collapse surface from the co-cut obligation package. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toAvailableCutCollapse
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom :=
  h.finalAvailableCut.to_availableCutCollapse

/-- Project the full-coordinate collapse surface from the co-cut obligation package. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toFullCoordinateCollapse
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse
      WithHoles PositiveAtom :=
  h.finalAvailableCut.to_fullCoordinateCollapse

/-- Project the post-quotient anchored-packing imports from the co-cut obligation package. -/
theorem CertifiedProofMdFirstBitCoCutObligationSurface.toPostQuotientAnchoredPacking
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.finalAvailableCut.to_postQuotientAnchoredPacking

/--
Certified-seven handoff using the unified Ramsey regular-10 consequence directly and higher-bit work
in fixed-target form.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenRegular_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyTenRegular : HasRamseyTenRegularAtDyadicTarget)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven) :
    TargetStatement := by
  have hsmallEleven :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus 11 :=
    hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwoSmallModulus_eleven_of_fixedWitnessTargets
      higherBitTargets
  have hterminal :
      HasPolynomialCostFixedWitnessTerminalRegularization 5 :=
    hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
      fixedWitnessExternalBlockSelfBridgeFive
  have hrestEleven :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo 11 :=
    hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo_of_fixedWitnessTerminalRegularizationFive_and_smallModulus
      hterminal hsmallEleven
  have hrestTen :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo 10 :=
    hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo_ten
      (hasFourToEightTargetTenFixedWitnessLift_of_ramseyTenRegularAtDyadicTarget
        ramseyTenRegular)
      hrestEleven
  have htwiceSeven :
      HasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGap 7 :=
    hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGap_of_parityToModFourLoss64_and_jAtLeastTwo
      (M := 7)
      (hasParityToModFourLoss64FixedWitnessLift_of_evenDegreeModFourLoss32InducedSubgraph
        evenDegreeModFourLoss32)
      (hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixTwiceLargeGapJAtLeastTwo_seven_of_ten
        hrestTen)
  exact
    targetStatement_of_proofMdFinalHandoff_of_fixedWitnessTerminalRegularization
      sevenVertexFourOrFiveBoolCertificate
      (hasPositiveEmptyControlFixedWitnessDyadicLiftRamseyIndexWindowAtLeastSixLargeGap_of_twiceLargeGap
        htwiceSeven)
      hterminal

/-- Certified-seven fixed-target handoff consuming the unified Ramsey consequence bundle. -/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_unifiedRamseyConsequences_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyConsequences : RamseyTenR45GlobalConsequenceBundle)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenRegular_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    evenDegreeModFourLoss32
    (hasRamseyTenRegularAtDyadicTarget_of_ramseyTenR45GlobalConsequenceBundle
      ramseyConsequences)
    fixedWitnessExternalBlockSelfBridgeFive higherBitTargets

/-- Certified-seven fixed-target handoff consuming the normalized exact-`42` Ramsey surface. -/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_exact42ConsumerNormalizedRamsey_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramsey : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_unifiedRamseyConsequences_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    evenDegreeModFourLoss32 ramsey.toGlobalConsequenceBundle
    fixedWitnessExternalBlockSelfBridgeFive higherBitTargets

/--
Certified-seven fixed-target handoff with terminal work exposed as the q=16 slice plus the genuine
`j >= 5` external-block tail.
-/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_unifiedRamseyConsequences_and_cliqueOrIndepSetBound16_and_terminalTail_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    (evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph)
    (ramseyConsequences : RamseyTenR45GlobalConsequenceBundle)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (terminalTailFromFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive)
    (higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_unifiedRamseyConsequences_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    evenDegreeModFourLoss32 ramseyConsequences
    (hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_fromFive
      cliqueOrIndepSetBound16 terminalTailFromFive)
    higherBitTargets

/-- Same split-terminal handoff with the first-bit input in the current bounded-coloring form. -/
theorem
    targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_unifiedRamseyConsequences_and_cliqueOrIndepSetBound16_and_terminalTail_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (evenModFourColoringBound : HasEvenDegreeModFourCongruentDegreeColoringBound C)
    (ramseyConsequences : RamseyTenR45GlobalConsequenceBundle)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (terminalTailFromFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive)
    (higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_unifiedRamseyConsequences_and_cliqueOrIndepSetBound16_and_terminalTail_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    (hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
      hCpos hC evenModFourColoringBound)
    ramseyConsequences cliqueOrIndepSetBound16 terminalTailFromFive higherBitTargets

/--
Single integrated handoff certificate for the current final frontier.  Some fields are projected for
downstream first-bit/terminal orchestration; the target-statement theorem below uses the mathematical
fields that already feed the proof-md final route.
-/
structure CertifiedProofMdIntegratedFrontierHandoffCertificate
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  ramsey : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Project unified Ramsey consequences from the integrated frontier certificate. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toGlobalConsequenceBundle
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.ramsey.toGlobalConsequenceBundle

/-- Project the Ramsey regular-10 target from the integrated frontier certificate. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toRamseyTenRegular
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasRamseyTenRegularAtDyadicTarget :=
  h.ramsey.toRamseyTenRegular

/-- Project the D=5 external-block bridge assembled from the split terminal fields. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toExternalBlockSelfBridgeFive
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
  hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_fromFive
    h.cliqueOrIndepSetBound16 h.terminalTailFromFive

/-- Project the loss-32 first-bit selector implied by the integrated bounded-coloring field. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toEvenDegreeModFourLoss32
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound

/-- Project the terminal mixed-target core imports from the integrated frontier certificate. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toTerminalMixedCore
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project the first-bit/co-cut obligation surface from the integrated frontier certificate. -/
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitCoCut
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- The integrated final frontier handoff certificate closes the target statement. -/
theorem targetStatement_of_certifiedProofMdIntegratedFrontierHandoffCertificate
    {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
    {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
    {packingSize : AnchoredPacking → ℕ}
    {WitnessCountAtLeast : ℕ → ℕ → Prop}
    {TwoDisjointTemplatesNeedTwo : Prop}
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_unifiedRamseyConsequences_and_cliqueOrIndepSetBound16_and_terminalTail_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound
    h.ramsey.toGlobalConsequenceBundle h.cliqueOrIndepSetBound16 h.terminalTailFromFive
    h.higherBitTargets


/-!
## Final proof-md obligation dashboard

The next declarations are final-facing aliases over the integrated handoff certificate.  They split the
current frontier into a small target consumer and a broader checklist that still exposes the exact-`42`,
terminal mixed-target, and first-bit/co-cut obligations for downstream lanes.
-/

/--
Small target-statement consumer for the current proof-md frontier.  This keeps only the assumptions
used by the final `TargetStatement` route: bounded-coloring first-bit work, unified Ramsey
consequences, the split D=5 terminal tail, and higher-bit fixed targets.
-/
structure CertifiedProofMdFinalTargetConsumerCertificate : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  ramseyConsequences : RamseyTenR45GlobalConsequenceBundle
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven

/-- Project the Ramsey regular-10 target used by the proof-md consumer route. -/
def CertifiedProofMdFinalTargetConsumerCertificate.toRamseyTenRegular
    (h : CertifiedProofMdFinalTargetConsumerCertificate) :
    HasRamseyTenRegularAtDyadicTarget :=
  hasRamseyTenRegularAtDyadicTarget_of_ramseyTenR45GlobalConsequenceBundle
    h.ramseyConsequences

/-- Project the D=5 external-block terminal bridge from the split terminal fields. -/
def CertifiedProofMdFinalTargetConsumerCertificate.toExternalBlockSelfBridgeFive
    (h : CertifiedProofMdFinalTargetConsumerCertificate) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
  hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_fromFive
    h.cliqueOrIndepSetBound16 h.terminalTailFromFive

/-- Project the normalized loss-32 first-bit selector from the bounded-coloring field. -/
def CertifiedProofMdFinalTargetConsumerCertificate.toEvenDegreeModFourLoss32
    (h : CertifiedProofMdFinalTargetConsumerCertificate) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  hasEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourCongruentDegreeColoringBound
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound

/-- Project the unified Ramsey consequence bundle. -/
def CertifiedProofMdFinalTargetConsumerCertificate.toGlobalConsequenceBundle
    (h : CertifiedProofMdFinalTargetConsumerCertificate) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.ramseyConsequences

/-- The small final target consumer closes `TargetStatement`. -/
theorem targetStatement_of_certifiedProofMdFinalTargetConsumerCertificate
    (h : CertifiedProofMdFinalTargetConsumerCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenModFourColoringBound_le32_and_unifiedRamseyConsequences_and_cliqueOrIndepSetBound16_and_terminalTail_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    h.firstBitColorCount_pos h.firstBitColorCount_le32 h.evenModFourColoringBound
    h.ramseyConsequences h.cliqueOrIndepSetBound16 h.terminalTailFromFive
    h.higherBitTargets

section FinalObligationDashboard

variable {Basis WithHoles PositiveAtom : ℕ → ℕ → Prop}
variable {AnchoredPacking : Type*} {TraceTwinFree : AnchoredPacking → Prop}
variable {packingSize : AnchoredPacking → ℕ}
variable {WitnessCountAtLeast : ℕ → ℕ → Prop}
variable {TwoDisjointTemplatesNeedTwo : Prop}

/-- Extract the small target consumer from the integrated handoff certificate. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate where
  firstBitColorCount := h.firstBitColorCount
  firstBitColorCount_pos := h.firstBitColorCount_pos
  firstBitColorCount_le32 := h.firstBitColorCount_le32
  evenModFourColoringBound := h.evenModFourColoringBound
  ramseyConsequences := h.ramsey.toGlobalConsequenceBundle
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  terminalTailFromFive := h.terminalTailFromFive
  higherBitTargets := h.higherBitTargets

/-- Constructor alias with a non-dot name for orchestration scripts. -/
def certifiedProofMdFinalTargetConsumerCertificate_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.toFinalTargetConsumerCertificate

/-- Project the normalized exact-`42` Ramsey surface from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toExact42ConsumerNormalizedRamsey
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate :=
  h.ramsey

/-- Project the exact-`42` profile with middle-degree endpoint ledgers from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toExact42WithMiddleSplits
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits :=
  h.ramsey.toExact42WithMiddleSplits

/-- Project the exact-`42` three-row profile surface from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toExact42ProfileSurface
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ThreeRowProfileSurface :=
  h.ramsey.toExact42ProfileSurface

/-- Project the local Ramsey endpoint ledger bundle from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toLocalLedgerBundle
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45MiddleDegreeLocalLedgerBundle :=
  h.ramsey.toLocalLedgerBundle

/-- Project the `R(3,10) <= 42` row from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toThreeTenFortyTwo
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 3 10 42 :=
  h.ramsey.toThreeTenFortyTwo

/-- Project the relaxed `R(4,5) <= 27` row from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toR45TwentySeven
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 4 5 27 :=
  h.ramsey.toR45TwentySeven

/-- Project the propagated `R(10,10) <= 39246` row from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toR10Ten39246
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 10 10 39246 :=
  h.ramsey.toR10Ten39246

/-- Project the terminal homogeneous-carry import bundle from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toHomogeneousCarryImports
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalMixedTypeHomogeneousCarryImports :=
  h.terminalMixedCore.toHomogeneousCarryImports

/-- Project the available-cut final first-bit wrapper from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitAvailableCutFinalWrapper
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutFinalWrapper

/-- Project the ordinary first-bit final branch wrappers from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitFinalBranchWrappers
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappers :=
  h.firstBitCoCut.toFinalBranchWrappers

/-- Project the available-cut positive-atom imports from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitAvailableCutPositiveAtom
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalAvailableCutPositiveAtomBoundaryImports Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutPositiveAtom

/-- Project the available-cut collapse import from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitAvailableCutCollapse
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutCollapse

/-- Project the full-coordinate available-cut collapse import from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitFullCoordinateCollapse
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse
      WithHoles PositiveAtom :=
  h.firstBitCoCut.toFullCoordinateCollapse

/-- Project the post-quotient anchored-packing imports from the integrated handoff. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toFirstBitPostQuotientAnchoredPacking
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut.toPostQuotientAnchoredPacking

/--
Final proof-obligation dashboard.  It keeps the target consumer fields together with the exact-`42`,
terminal mixed-target, and co-cut surfaces that are useful for handoff checklists.
-/
structure CertifiedProofMdFinalObligationDashboard
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  firstBitColorCount : ℕ
  firstBitColorCount_pos : 0 < firstBitColorCount
  firstBitColorCount_le32 : firstBitColorCount ≤ 32
  evenModFourColoringBound :
    HasEvenDegreeModFourCongruentDegreeColoringBound firstBitColorCount
  exact42Ramsey : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Collapse the full dashboard to the small target consumer. -/
def CertifiedProofMdFinalObligationDashboard.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate where
  firstBitColorCount := h.firstBitColorCount
  firstBitColorCount_pos := h.firstBitColorCount_pos
  firstBitColorCount_le32 := h.firstBitColorCount_le32
  evenModFourColoringBound := h.evenModFourColoringBound
  ramseyConsequences := h.exact42Ramsey.toGlobalConsequenceBundle
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  terminalTailFromFive := h.terminalTailFromFive
  higherBitTargets := h.higherBitTargets

/-- Build the final dashboard from the integrated handoff certificate. -/
def certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  firstBitColorCount := h.firstBitColorCount
  firstBitColorCount_pos := h.firstBitColorCount_pos
  firstBitColorCount_le32 := h.firstBitColorCount_le32
  evenModFourColoringBound := h.evenModFourColoringBound
  exact42Ramsey := h.toExact42ConsumerNormalizedRamsey
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  terminalTailFromFive := h.terminalTailFromFive
  higherBitTargets := h.higherBitTargets
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut

/-- Project exact-`42` Ramsey obligations from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toExact42ConsumerNormalizedRamsey
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate :=
  h.exact42Ramsey

/-- Project unified Ramsey consequences from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toGlobalConsequenceBundle
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.exact42Ramsey.toGlobalConsequenceBundle

/-- Project the Ramsey regular-10 target from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toRamseyTenRegular
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasRamseyTenRegularAtDyadicTarget :=
  h.exact42Ramsey.toRamseyTenRegular

/-- Project the normalized loss-32 first-bit selector from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toEvenDegreeModFourLoss32
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.toFinalTargetConsumerCertificate.toEvenDegreeModFourLoss32

/-- Project the D=5 external-block bridge from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toExternalBlockSelfBridgeFive
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
  h.toFinalTargetConsumerCertificate.toExternalBlockSelfBridgeFive

/-- Project terminal mixed-target imports from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toTerminalMixedCore
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitCoCut
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the exact-`42` profile with middle-degree ledgers from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toExact42WithMiddleSplits
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits :=
  h.exact42Ramsey.toExact42WithMiddleSplits

/-- Project the exact-`42` three-row profile surface from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toExact42ProfileSurface
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ThreeRowProfileSurface :=
  h.exact42Ramsey.toExact42ProfileSurface

/-- Project the local Ramsey endpoint ledger bundle from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toLocalLedgerBundle
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45MiddleDegreeLocalLedgerBundle :=
  h.exact42Ramsey.toLocalLedgerBundle

/-- Project the `R(3,10) <= 42` row from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toThreeTenFortyTwo
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 3 10 42 :=
  h.exact42Ramsey.toThreeTenFortyTwo

/-- Project the relaxed `R(4,5) <= 27` row from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toR45TwentySeven
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 4 5 27 :=
  h.exact42Ramsey.toR45TwentySeven

/-- Project the propagated `R(10,10) <= 39246` row from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toR10Ten39246
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 10 10 39246 :=
  h.exact42Ramsey.toR10Ten39246

/-- Project the admissible-bound consequence at `40960` from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toTenMemAdmissibleBounds_40960
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ∈ admissibleBounds 40960 :=
  h.exact42Ramsey.toTenMemAdmissibleBounds_40960

/-- Project the extremal-function lower bound at `40960` from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toTenLeF_40960
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ≤ F 40960 :=
  h.exact42Ramsey.toTenLeF_40960

/-- Project the terminal homogeneous-carry import bundle from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toHomogeneousCarryImports
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalMixedTypeHomogeneousCarryImports :=
  h.terminalMixedCore.toHomogeneousCarryImports

/-- Project the available-cut final first-bit wrapper from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitAvailableCutFinalWrapper
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutFinalWrapper

/-- Project the ordinary first-bit final branch wrappers from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitFinalBranchWrappers
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappers :=
  h.firstBitCoCut.toFinalBranchWrappers

/-- Project the available-cut positive-atom imports from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitAvailableCutPositiveAtom
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalAvailableCutPositiveAtomBoundaryImports Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutPositiveAtom

/-- Project the available-cut collapse import from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitAvailableCutCollapse
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutCollapse

/-- Project the full-coordinate available-cut collapse import from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitFullCoordinateCollapse
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse
      WithHoles PositiveAtom :=
  h.firstBitCoCut.toFullCoordinateCollapse

/-- Project the post-quotient anchored-packing imports from the dashboard. -/
def CertifiedProofMdFinalObligationDashboard.toFirstBitPostQuotientAnchoredPacking
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut.toPostQuotientAnchoredPacking

/-- The final dashboard closes `TargetStatement` through its small target consumer. -/
theorem targetStatement_of_certifiedProofMdFinalObligationDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdFinalTargetConsumerCertificate
    h.toFinalTargetConsumerCertificate

/-- The final dashboard also closes `TargetStatement` through its exact-`42` Ramsey surface. -/
theorem targetStatement_of_certifiedProofMdFinalObligationDashboard_via_exact42Consumer
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_exact42ConsumerNormalizedRamsey_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitFixedWitnessTargetsFromEleven_certifiedSeven
    h.toEvenDegreeModFourLoss32 h.toExact42ConsumerNormalizedRamsey
    h.toExternalBlockSelfBridgeFive h.higherBitTargets

/-- The integrated handoff also closes `TargetStatement` through the dashboard route. -/
theorem targetStatement_of_certifiedProofMdIntegratedFrontierHandoffCertificate_via_dashboard
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdFinalObligationDashboard
    (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h)

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate_firstBitColorCount
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate.firstBitColorCount = h.firstBitColorCount :=
  rfl

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate_ramseyConsequences
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate.ramseyConsequences = h.ramsey.toGlobalConsequenceBundle :=
  rfl

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate_cliqueOrIndepSetBound16
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate.cliqueOrIndepSetBound16 = h.cliqueOrIndepSetBound16 :=
  rfl

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate_terminalTailFromFive
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate.terminalTailFromFive = h.terminalTailFromFive :=
  rfl

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toFinalTargetConsumerCertificate_higherBitTargets
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate.higherBitTargets = h.higherBitTargets :=
  rfl

@[simp]
theorem certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff_targetConsumer
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h).toFinalTargetConsumerCertificate =
      h.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff_exact42Ramsey
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h).exact42Ramsey =
      h.toExact42ConsumerNormalizedRamsey :=
  rfl

@[simp]
theorem certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff_terminalMixedCore
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h).terminalMixedCore =
      h.toTerminalMixedCore :=
  rfl

@[simp]
theorem certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff_firstBitCoCut
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h).firstBitCoCut =
      h.toFirstBitCoCut :=
  rfl

/-- Compact audit certificate for the current proof-md frontier dashboard. -/
structure CertifiedProofMdCurrentFrontierAuditCertificate
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Alias name for consumers that prefer dashboard terminology over audit terminology. -/
abbrev CertifiedProofMdCurrentFrontierDashboard
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type :=
  CertifiedProofMdCurrentFrontierAuditCertificate
    Basis WithHoles PositiveAtom
    AnchoredPacking TraceTwinFree packingSize
    WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Promote the final obligation dashboard to the compact current-frontier audit surface. -/
def CertifiedProofMdFinalObligationDashboard.toCurrentFrontierAuditCertificate
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  finalDashboard := h

/-- Non-dot constructor alias from the final obligation dashboard. -/
def certifiedProofMdCurrentFrontierAuditCertificate_of_finalObligationDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierAuditCertificate

/-- Constructor from the integrated final-frontier handoff certificate. -/
def certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  (certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h).toCurrentFrontierAuditCertificate

/-- Recover the final obligation dashboard from the current-frontier audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFinalObligationDashboard
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.finalDashboard

/-- Project the small target consumer from the current-frontier audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.toFinalObligationDashboard.toFinalTargetConsumerCertificate

/-- Project the normalized exact-`42` Ramsey surface from the current-frontier audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toExact42ConsumerNormalizedRamsey
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate :=
  h.toFinalObligationDashboard.toExact42ConsumerNormalizedRamsey

/-- Project unified Ramsey consequences from the current-frontier audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toGlobalConsequenceBundle
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.toFinalObligationDashboard.toGlobalConsequenceBundle

/-- Project the Ramsey regular-10 target from the current-frontier audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toRamseyTenRegular
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasRamseyTenRegularAtDyadicTarget :=
  h.toFinalObligationDashboard.toRamseyTenRegular

/-- Project the exact-`42` profile with middle-degree ledgers from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toExact42WithMiddleSplits
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits :=
  h.toFinalObligationDashboard.toExact42WithMiddleSplits

/-- Project the exact-`42` three-row profile surface from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toExact42ProfileSurface
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ThreeRowProfileSurface :=
  h.toFinalObligationDashboard.toExact42ProfileSurface

/-- Project the local Ramsey endpoint ledger bundle from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toLocalLedgerBundle
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45MiddleDegreeLocalLedgerBundle :=
  h.toFinalObligationDashboard.toLocalLedgerBundle

/-- Project the `R(3,10) <= 42` row from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toThreeTenFortyTwo
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 3 10 42 :=
  h.toFinalObligationDashboard.toThreeTenFortyTwo

/-- Project the relaxed `R(4,5) <= 27` row from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toR45TwentySeven
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 4 5 27 :=
  h.toFinalObligationDashboard.toR45TwentySeven

/-- Project the propagated `R(10,10) <= 39246` row from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toR10Ten39246
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 10 10 39246 :=
  h.toFinalObligationDashboard.toR10Ten39246

/-- Project the admissible-bound consequence at `40960` from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toTenMemAdmissibleBounds_40960
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ∈ admissibleBounds 40960 :=
  h.toFinalObligationDashboard.toTenMemAdmissibleBounds_40960

/-- Project the extremal-function lower bound at `40960` from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toTenLeF_40960
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ≤ F 40960 :=
  h.toFinalObligationDashboard.toTenLeF_40960

/-- Project the normalized loss-32 first-bit selector from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toEvenDegreeModFourLoss32
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.toFinalObligationDashboard.toEvenDegreeModFourLoss32

/-- Project the D=5 external-block bridge from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toExternalBlockSelfBridgeFive
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
  h.toFinalObligationDashboard.toExternalBlockSelfBridgeFive

/-- Project terminal mixed-target imports from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toTerminalMixedCore
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.toFinalObligationDashboard.toTerminalMixedCore

/-- Project the terminal homogeneous-carry imports from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toHomogeneousCarryImports
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalMixedTypeHomogeneousCarryImports :=
  h.toFinalObligationDashboard.toHomogeneousCarryImports

/-- Project first-bit/co-cut obligations from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitCoCut
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toFinalObligationDashboard.toFirstBitCoCut

/-- Project the available-cut final first-bit wrapper from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitAvailableCutFinalWrapper
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom :=
  h.toFinalObligationDashboard.toFirstBitAvailableCutFinalWrapper

/-- Project the ordinary first-bit final branch wrappers from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitFinalBranchWrappers
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappers :=
  h.toFinalObligationDashboard.toFirstBitFinalBranchWrappers

/-- Project available-cut positive-atom imports from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitAvailableCutPositiveAtom
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalAvailableCutPositiveAtomBoundaryImports Basis WithHoles PositiveAtom :=
  h.toFinalObligationDashboard.toFirstBitAvailableCutPositiveAtom

/-- Project the available-cut collapse import from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitAvailableCutCollapse
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom :=
  h.toFinalObligationDashboard.toFirstBitAvailableCutCollapse

/-- Project the full-coordinate available-cut collapse import from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitFullCoordinateCollapse
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse
      WithHoles PositiveAtom :=
  h.toFinalObligationDashboard.toFirstBitFullCoordinateCollapse

/-- Project post-quotient anchored-packing imports from the audit certificate. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toFirstBitPostQuotientAnchoredPacking
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toFinalObligationDashboard.toFirstBitPostQuotientAnchoredPacking

/-- The current-frontier audit certificate closes `TargetStatement`. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierAuditCertificate
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdFinalObligationDashboard
    h.toFinalObligationDashboard

/-- The current-frontier dashboard alias also closes `TargetStatement`. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierDashboard
    (h : CertifiedProofMdCurrentFrontierDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdCurrentFrontierAuditCertificate h

/-- The integrated handoff closes `TargetStatement` through the audit route. -/
theorem targetStatement_of_certifiedProofMdIntegratedFrontierHandoffCertificate_via_currentFrontierAudit
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdCurrentFrontierAuditCertificate
    (certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff h)

@[simp]
theorem CertifiedProofMdFinalObligationDashboard.toCurrentFrontierAuditCertificate_finalDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toCurrentFrontierAuditCertificate.finalDashboard = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierAuditCertificate.toFinalObligationDashboard_finalDashboard
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalObligationDashboard = h.finalDashboard :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierAuditCertificate.toFinalTargetConsumerCertificate_finalDashboard
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate =
      h.finalDashboard.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem certifiedProofMdCurrentFrontierAuditCertificate_of_finalObligationDashboard_finalDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdCurrentFrontierAuditCertificate_of_finalObligationDashboard h).finalDashboard =
      h :=
  rfl

@[simp]
theorem certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff_finalDashboard
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff h).toFinalObligationDashboard =
      certifiedProofMdFinalObligationDashboard_of_integratedFrontierHandoff h :=
  rfl

@[simp]
theorem certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff_targetConsumer
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    (certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff h).toFinalTargetConsumerCertificate =
      h.toFinalTargetConsumerCertificate :=
  rfl

/-!
## Current-frontier target import facade

The current audit dashboard is still an assumption/local-certificate frontier.  The next layer packages
exactly the obligations already present in that dashboard into a consumer-facing import facade: the
small target-statement certificate, the normalized exact-`42` Ramsey audit, terminal mixed-target
imports, and the first-bit/co-cut obligation surface.
-/

/--
Consumer-facing import facade for the current proof-md frontier.  It is intentionally just a
repackaging of the current dashboard: `targetConsumer` closes the final target statement, while the
other fields keep the audit/checklist obligations available to downstream lanes.
-/
structure CertifiedProofMdCurrentFrontierTargetImports
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  exact42Ramsey : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Alias for consumers that want facade terminology rather than target-import terminology. -/
abbrev CertifiedProofMdCurrentFrontierConsumerFacade
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type :=
  CertifiedProofMdCurrentFrontierTargetImports
    Basis WithHoles PositiveAtom
    AnchoredPacking TraceTwinFree packingSize
    WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Project the final target consumer from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetConsumer

/-- Project the normalized exact-`42` Ramsey surface from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toExact42ConsumerNormalizedRamsey
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate :=
  h.exact42Ramsey

/-- Project the normalized global Ramsey consequences from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toGlobalConsequenceBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.exact42Ramsey.toGlobalConsequenceBundle

/-- Project the target-consumer Ramsey consequences from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toTargetConsumerGlobalConsequenceBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45GlobalConsequenceBundle :=
  h.targetConsumer.toGlobalConsequenceBundle

/-- Project the Ramsey regular-10 target through the normalized exact-`42` route. -/
def CertifiedProofMdCurrentFrontierTargetImports.toRamseyTenRegular
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasRamseyTenRegularAtDyadicTarget :=
  h.exact42Ramsey.toRamseyTenRegular

/-- Project the `R(3,10) <= 42` row from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toThreeTenFortyTwo
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 3 10 42 :=
  h.exact42Ramsey.toThreeTenFortyTwo

/-- Project the relaxed `R(4,5) <= 27` row from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toR45TwentySeven
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 4 5 27 :=
  h.exact42Ramsey.toR45TwentySeven

/-- Project the propagated `R(10,10) <= 39246` row from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toR10Ten39246
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasCliqueOrIndepSetBound 10 10 39246 :=
  h.exact42Ramsey.toR10Ten39246

/-- Project the admissible-bound consequence at `40960` from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toTenMemAdmissibleBounds_40960
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ∈ admissibleBounds 40960 :=
  h.exact42Ramsey.toTenMemAdmissibleBounds_40960

/-- Project the extremal-function lower bound at `40960` from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toTenLeF_40960
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    10 ≤ F 40960 :=
  h.exact42Ramsey.toTenLeF_40960

/-- Project the loss-32 first-bit selector from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toEvenDegreeModFourLoss32
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.targetConsumer.toEvenDegreeModFourLoss32

/-- Project the D=5 external-block bridge from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toExternalBlockSelfBridgeFive
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5 :=
  h.targetConsumer.toExternalBlockSelfBridgeFive

/-- Project terminal mixed-target imports from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toTerminalMixedCore
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project terminal homogeneous-carry imports from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toHomogeneousCarryImports
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalMixedTypeHomogeneousCarryImports :=
  h.terminalMixedCore.toHomogeneousCarryImports

/-- Project the first-bit/co-cut obligation surface from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitCoCut
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the available-cut first-bit wrapper from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitAvailableCutFinalWrapper
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutFinalWrapper

/-- Project the ordinary first-bit final branch wrappers from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitFinalBranchWrappers
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalPacketFinalBranchWrappers :=
  h.firstBitCoCut.toFinalBranchWrappers

/-- Project available-cut positive-atom imports from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitAvailableCutPositiveAtom
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitTerminalAvailableCutPositiveAtomBoundaryImports Basis WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutPositiveAtom

/-- Project the available-cut collapse import from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitAvailableCutCollapse
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom :=
  h.firstBitCoCut.toAvailableCutCollapse

/-- Project the full-coordinate available-cut collapse import from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitFullCoordinateCollapse
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse
      WithHoles PositiveAtom :=
  h.firstBitCoCut.toFullCoordinateCollapse

/-- Project post-quotient anchored-packing imports from the target-import facade. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFirstBitPostQuotientAnchoredPacking
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut.toPostQuotientAnchoredPacking

/-- Reinflate the target-import facade into the final obligation dashboard. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFinalObligationDashboard
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  firstBitColorCount := h.targetConsumer.firstBitColorCount
  firstBitColorCount_pos := h.targetConsumer.firstBitColorCount_pos
  firstBitColorCount_le32 := h.targetConsumer.firstBitColorCount_le32
  evenModFourColoringBound := h.targetConsumer.evenModFourColoringBound
  exact42Ramsey := h.exact42Ramsey
  cliqueOrIndepSetBound16 := h.targetConsumer.cliqueOrIndepSetBound16
  terminalTailFromFive := h.targetConsumer.terminalTailFromFive
  higherBitTargets := h.targetConsumer.higherBitTargets
  terminalMixedCore := h.terminalMixedCore
  firstBitCoCut := h.firstBitCoCut

/-- Package the final obligation dashboard as the current-frontier target-import facade. -/
def CertifiedProofMdFinalObligationDashboard.toCurrentFrontierTargetImports
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  targetConsumer := h.toFinalTargetConsumerCertificate
  exact42Ramsey := h.exact42Ramsey
  terminalMixedCore := h.terminalMixedCore
  firstBitCoCut := h.firstBitCoCut

/-- Non-dot constructor from the final obligation dashboard. -/
def certifiedProofMdCurrentFrontierTargetImports_of_finalObligationDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports

/-- Package the current-frontier audit certificate as the target-import facade. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toCurrentFrontierTargetImports
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toFinalObligationDashboard.toCurrentFrontierTargetImports

/-- Non-dot constructor from the current-frontier audit certificate. -/
def certifiedProofMdCurrentFrontierTargetImports_of_currentFrontierAuditCertificate
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports

/-- Non-dot constructor from the current-frontier dashboard alias. -/
def certifiedProofMdCurrentFrontierTargetImports_of_currentFrontierDashboard
    (h : CertifiedProofMdCurrentFrontierDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports

/-- Package the integrated frontier handoff certificate as the target-import facade. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toCurrentFrontierTargetImports
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  (certifiedProofMdCurrentFrontierAuditCertificate_of_integratedFrontierHandoff h).toCurrentFrontierTargetImports

/-- Non-dot constructor from the integrated frontier handoff certificate. -/
def certifiedProofMdCurrentFrontierTargetImports_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports

/-- The target-import facade closes `TargetStatement` through its small consumer. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierTargetImports
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdFinalTargetConsumerCertificate
    h.toFinalTargetConsumerCertificate

/-- The consumer-facade alias also closes `TargetStatement`. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierConsumerFacade
    (h : CertifiedProofMdCurrentFrontierConsumerFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdCurrentFrontierTargetImports h

/-- The target-import facade closes `TargetStatement` after reinflating to the final dashboard. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierTargetImports_via_finalDashboard
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdFinalObligationDashboard
    h.toFinalObligationDashboard

/-- Compact theorem-carrying view for target-statement consumers. -/
structure CertifiedProofMdCurrentFrontierTargetStatementBundle
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatement : TargetStatement

/-- Promote target imports to the theorem-carrying target-statement bundle. -/
def CertifiedProofMdCurrentFrontierTargetImports.toTargetStatementBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  targetImports := h
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierTargetImports h

/-- Promote the current-frontier audit certificate to the target-statement bundle. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toTargetStatementBundle
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports.toTargetStatementBundle

/-- Promote the integrated frontier handoff certificate to the target-statement bundle. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toCurrentFrontierTargetStatementBundle
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports.toTargetStatementBundle

/-- Non-dot constructor from the current-frontier audit certificate to the target-statement bundle. -/
def certifiedProofMdCurrentFrontierTargetStatementBundle_of_currentFrontierAuditCertificate
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toTargetStatementBundle

/-- Non-dot constructor from the integrated frontier handoff to the target-statement bundle. -/
def certifiedProofMdCurrentFrontierTargetStatementBundle_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetStatementBundle

/-- Project target imports from the theorem-carrying target-statement bundle. -/
def CertifiedProofMdCurrentFrontierTargetStatementBundle.toCurrentFrontierTargetImports
    (h : CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetImports

/-- Project the final target consumer from the theorem-carrying target-statement bundle. -/
def CertifiedProofMdCurrentFrontierTargetStatementBundle.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetImports.toFinalTargetConsumerCertificate

/-- Project the final obligation dashboard from the theorem-carrying target-statement bundle. -/
def CertifiedProofMdCurrentFrontierTargetStatementBundle.toFinalObligationDashboard
    (h : CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetImports.toFinalObligationDashboard

/-- The theorem-carrying target-statement bundle exposes its certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierTargetStatementBundle
    (h : CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  h.targetStatement

/-!
## Downstream current-frontier checklist and Ramsey-current bridge

The target-import facade is convenient for final proof-md consumers, but downstream lanes also want a
flat checklist exposing the theorem-only Ramsey bundle, exact-`42` profile data, terminal mixed-target
imports, and first-bit/co-cut surfaces at once.  The bridge below keeps this certified proof-md
checklist paired with the latest localized `RamseyTenR45CurrentFrontierConsumerSurface` without
asserting any new Ramsey row: all numerical Ramsey conclusions remain the assumption-backed
frontier already carried by the imported surfaces.
-/

/-- Project the profiled exact-`42` surface with middle-degree split ledgers from target imports. -/
def CertifiedProofMdCurrentFrontierTargetImports.toExact42WithMiddleSplits
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits :=
  h.exact42Ramsey.toExact42WithMiddleSplits

/-- Project the profiled exact-`42` three-row surface from target imports. -/
def CertifiedProofMdCurrentFrontierTargetImports.toExact42ProfileSurface
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyThreeTenExact42ThreeRowProfileSurface :=
  h.exact42Ramsey.toExact42ProfileSurface

/-- Project the local middle-degree ledger bundle from target imports. -/
def CertifiedProofMdCurrentFrontierTargetImports.toLocalLedgerBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45MiddleDegreeLocalLedgerBundle :=
  h.exact42Ramsey.toLocalLedgerBundle

/-- Package the target-import Ramsey rows as the reusable final-consequence surface. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFinalConsequenceSurface
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45FinalConsequenceSurface :=
  h.toGlobalConsequenceBundle.toFinalConsequenceSurface

/-- Package the target-import Ramsey rows as the parameter-free theorem bundle. -/
def CertifiedProofMdCurrentFrontierTargetImports.toUnifiedFinalTheoremBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45UnifiedFinalTheoremBundle :=
  h.toGlobalConsequenceBundle.toUnifiedFinalTheoremBundle h.toThreeTenFortyTwo

/-- Package the target-import Ramsey rows as compact numerical consequences. -/
def CertifiedProofMdCurrentFrontierTargetImports.toFinalNumericalConsequences
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45FinalNumericalConsequences :=
  h.toGlobalConsequenceBundle.toFinalNumericalConsequences h.toThreeTenFortyTwo

/--
Flat downstream checklist for the current proof-md frontier.  It is just a normalized view of
`CertifiedProofMdCurrentFrontierTargetImports`: target-statement closure, theorem-only Ramsey
consequences, exact-`42` profile data, terminal mixed-target imports, and first-bit/co-cut obligations.
-/
structure CertifiedProofMdCurrentFrontierDownstreamChecklist
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop) : Type where
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatement : TargetStatement
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  exact42Ramsey : CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate
  exact42WithMiddleSplits : RamseyThreeTenExact42ProfileWithDegreeNineEndpointMiddleSplits
  exact42Profile : RamseyThreeTenExact42ThreeRowProfileSurface
  localLedgers : RamseyTenR45MiddleDegreeLocalLedgerBundle
  globalConsequences : RamseyTenR45GlobalConsequenceBundle
  finalConsequences : RamseyTenR45FinalConsequenceSurface
  theoremBundle : RamseyTenR45UnifiedFinalTheoremBundle
  numericalConsequences : RamseyTenR45FinalNumericalConsequences
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  homogeneousCarryImports : FirstBitTerminalMixedTypeHomogeneousCarryImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalBranchWrappers : FirstBitTerminalPacketFinalBranchWrappers
  availableCutFinalWrapper :
    FirstBitTerminalPacketFinalBranchWrappersWithAvailableCutPositiveAtom
      Basis WithHoles PositiveAtom
  availableCutCollapse :
    FirstBitCoordinateSubboxAvailableCutPositiveAtomCollapse WithHoles PositiveAtom
  fullCoordinateCollapse :
    FirstBitCoordinateSubboxFullCoordinateAvailableCutPositiveAtomCollapse WithHoles PositiveAtom
  postQuotientAnchoredPacking :
    PositiveAtomPostQuotientAnchoredPackingImports
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Promote target imports to the flat downstream checklist. -/
def CertifiedProofMdCurrentFrontierTargetImports.toDownstreamChecklist
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo where
  targetImports := h
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierTargetImports h
  targetConsumer := h.toFinalTargetConsumerCertificate
  exact42Ramsey := h.toExact42ConsumerNormalizedRamsey
  exact42WithMiddleSplits := h.toExact42WithMiddleSplits
  exact42Profile := h.toExact42ProfileSurface
  localLedgers := h.toLocalLedgerBundle
  globalConsequences := h.toGlobalConsequenceBundle
  finalConsequences := h.toFinalConsequenceSurface
  theoremBundle := h.toUnifiedFinalTheoremBundle
  numericalConsequences := h.toFinalNumericalConsequences
  terminalMixedCore := h.toTerminalMixedCore
  homogeneousCarryImports := h.toHomogeneousCarryImports
  firstBitCoCut := h.toFirstBitCoCut
  finalBranchWrappers := h.toFirstBitFinalBranchWrappers
  availableCutFinalWrapper := h.toFirstBitAvailableCutFinalWrapper
  availableCutCollapse := h.toFirstBitAvailableCutCollapse
  fullCoordinateCollapse := h.toFirstBitFullCoordinateCollapse
  postQuotientAnchoredPacking := h.toFirstBitPostQuotientAnchoredPacking

/-- Promote the current-frontier audit certificate to the downstream checklist. -/
def CertifiedProofMdCurrentFrontierAuditCertificate.toDownstreamChecklist
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports.toDownstreamChecklist

/-- Promote the integrated frontier handoff to the downstream checklist. -/
def CertifiedProofMdIntegratedFrontierHandoffCertificate.toCurrentFrontierDownstreamChecklist
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports.toDownstreamChecklist

/-- Non-dot constructor from the current-frontier audit certificate to the downstream checklist. -/
def certifiedProofMdCurrentFrontierDownstreamChecklist_of_currentFrontierAuditCertificate
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toDownstreamChecklist

/-- Non-dot constructor from the integrated frontier handoff to the downstream checklist. -/
def certifiedProofMdCurrentFrontierDownstreamChecklist_of_integratedFrontierHandoff
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierDownstreamChecklist

/-- Project target imports from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toCurrentFrontierTargetImports
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetImports

/-- Project the final target consumer from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toFinalTargetConsumerCertificate
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetConsumer

/-- Project the normalized exact-`42` Ramsey certificate from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toExact42ConsumerNormalizedRamsey
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdExact42ConsumerNormalizedRamseyCertificate :=
  h.exact42Ramsey

/-- Project the theorem-only Ramsey bundle from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toUnifiedFinalTheoremBundle
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45UnifiedFinalTheoremBundle :=
  h.theoremBundle

/-- Project compact numerical Ramsey consequences from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toFinalNumericalConsequences
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    RamseyTenR45FinalNumericalConsequences :=
  h.numericalConsequences

/-- Project terminal mixed-target imports from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toTerminalMixedCore
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the downstream checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toFirstBitCoCut
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- The downstream checklist exposes its certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierDownstreamChecklist
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    TargetStatement :=
  h.targetStatement

/--
Bridge between proof-md target imports and the latest localized Ramsey current-frontier surface.
This keeps the two consumer-facing facades available together; the consistency lemmas below are
normalization statements between proof terms for the same carried propositions.
-/
structure CertifiedProofMdCurrentFrontierRamseySurfaceBridge
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α)) : Type where
  checklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v

/-- Pair a proof-md downstream checklist with a localized Ramsey current-frontier surface. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.withRamseySurface
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v where
  checklist := h
  ramseySurface := hramsey

/-- Build a proof-md/Ramsey bridge directly from target imports and a Ramsey current surface. -/
def CertifiedProofMdCurrentFrontierTargetImports.toRamseySurfaceBridge
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.toDownstreamChecklist.withRamseySurface hramsey

/-- Project the proof-md checklist from the proof-md/Ramsey bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toDownstreamChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.checklist

/-- Project target imports from the proof-md/Ramsey bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.checklist.toCurrentFrontierTargetImports

/-- Project the localized Ramsey current-frontier surface from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseySurface

/-- Project the certified target-statement bundle from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toCurrentFrontierTargetImports.toTargetStatementBundle

/-- Project proof-md's theorem-only Ramsey bundle from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toCertifiedUnifiedFinalTheoremBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45UnifiedFinalTheoremBundle :=
  h.checklist.toUnifiedFinalTheoremBundle

/-- Project the Ramsey surface's theorem-only bundle from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyUnifiedFinalTheoremBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45UnifiedFinalTheoremBundle :=
  h.ramseySurface.toUnifiedFinalTheoremBundle

/-- Project proof-md's compact numerical Ramsey consequences from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toCertifiedFinalNumericalConsequences
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45FinalNumericalConsequences :=
  h.checklist.toFinalNumericalConsequences

/-- Project the Ramsey surface's compact numerical consequences from the bridge. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyFinalNumericalConsequences
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45FinalNumericalConsequences :=
  h.ramseySurface.toFinalNumericalConsequences

/-- The bridge exposes `TargetStatement` through the proof-md checklist. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierRamseySurfaceBridge
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    TargetStatement :=
  h.checklist.targetStatement

/-- Proof-md and Ramsey-current theorem bundles normalize to proofs of the same proposition. -/
theorem CertifiedProofMdCurrentFrontierRamseySurfaceBridge.certifiedTheoremBundle_eq_ramseySurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toCertifiedUnifiedFinalTheoremBundle =
      h.toRamseyUnifiedFinalTheoremBundle := by
  exact Subsingleton.elim _ _

/-- Proof-md and Ramsey-current compact numerical packages normalize to the same proposition. -/
theorem CertifiedProofMdCurrentFrontierRamseySurfaceBridge.certifiedNumericalConsequences_eq_ramseySurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toCertifiedFinalNumericalConsequences =
      h.toRamseyFinalNumericalConsequences := by
  exact Subsingleton.elim _ _

/-!
## Public current-frontier dashboard facade

The bridge above keeps the proof-md checklist and the localized Ramsey surface together.  The facade
below is a more public dashboard layer: it simultaneously exposes target-statement/dashboard
normalization, Ramsey theorem checklists/target rows/normalization routes, and the terminal mixed
and first-bit obligation surfaces.  The packet-atom extension at the end is deliberately parameterized
by proposition-valued frontier assumptions, so it records current terminal packet-atom/principal-bucket
obligations without certifying any unsolved row.
-/

/--
Public proof-md/Ramsey dashboard facade for the current frontier.  It is a normalized projection of
`CertifiedProofMdCurrentFrontierRamseySurfaceBridge`, with no new mathematical content.
-/
structure CertifiedProofMdCurrentFrontierRamseyDashboardFacade
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α)) : Type where
  bridge :
    CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  downstreamChecklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo

/-- Promote the proof-md/Ramsey bridge to the public dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyDashboardFacade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v where
  bridge := h
  targetImports := h.toCurrentFrontierTargetImports
  downstreamChecklist := h.toDownstreamChecklist
  targetStatementBundle := h.toTargetStatementBundle
  finalDashboard := h.toCurrentFrontierTargetImports.toFinalObligationDashboard
  targetConsumer := h.toCurrentFrontierTargetImports.toFinalTargetConsumerCertificate
  ramseySurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyTheoremChecklist :=
    h.toRamseyCurrentFrontierConsumerSurface.toCurrentFrontierTheoremChecklist
  ramseyTargetRows := h.toRamseyCurrentFrontierConsumerSurface.toCurrentFrontierTargetRows
  ramseyNormalization :=
    h.toRamseyCurrentFrontierConsumerSurface.toCurrentFrontierNormalizationRoute
  terminalMixedCore := h.toDownstreamChecklist.toTerminalMixedCore
  firstBitCoCut := h.toDownstreamChecklist.toFirstBitCoCut

/-- Build the public dashboard facade directly from target imports and a Ramsey current surface. -/
def CertifiedProofMdCurrentFrontierTargetImports.toRamseyDashboardFacade
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  (h.toRamseySurfaceBridge hramsey).toRamseyDashboardFacade

/-- Build the public dashboard facade directly from a downstream checklist and Ramsey surface. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toRamseyDashboardFacade
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  (h.withRamseySurface hramsey).toRamseyDashboardFacade

/-- Project the underlying proof-md/Ramsey bridge from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toRamseySurfaceBridge
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.bridge

/-- Project target imports from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetImports

/-- Project the downstream checklist from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toDownstreamChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.downstreamChecklist

/-- Project the target-statement bundle from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final obligation dashboard from the public current-frontier facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toFinalObligationDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.finalDashboard

/-- Project the final target consumer from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetConsumer

/-- Project the localized Ramsey current-frontier consumer from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseySurface

/-- Project the Ramsey theorem checklist from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toRamseyCurrentFrontierTheoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierTheoremChecklist :=
  h.ramseyTheoremChecklist

/-- Project Ramsey target rows from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.ramseyTargetRows

/-- Project the Ramsey normalization route from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toRamseyCurrentFrontierNormalizationRoute
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierNormalizationRoute G s v :=
  h.ramseyNormalization

/-- Project terminal mixed-core imports from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- The public dashboard facade exposes its certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierRamseyDashboardFacade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    TargetStatement :=
  h.toTargetStatementBundle.targetStatement

/--
Terminal packet-atom/principal-bucket shadow dashboard extension.  The packet-atom and shadow rows
are explicit proposition-valued inputs; this bundle only ties them to the current proof-md/Ramsey
dashboard for downstream consumers.
-/
structure CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  facade :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier

/-- Attach packet-atom and principal-bucket shadow frontier imports to the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomShadow
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacket :
      FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
    (hshadow : principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  facade := h
  packetAtomShadow :=
    firstBitTerminalPacketAtomPrincipalBucketShadowImports_of_parts hpacket hshadow

/-- Attach a prepackaged packet-atom/principal-bucket shadow import bundle to the dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  facade := h
  packetAtomShadow := hpacketShadow

/-- Project the proof-md/Ramsey dashboard facade from the packet-atom extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toRamseyDashboardFacade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.facade

/-- Project target imports through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.facade.toCurrentFrontierTargetImports

/-- Project the Ramsey theorem checklist through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toRamseyCurrentFrontierTheoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTheoremChecklist :=
  h.facade.toRamseyCurrentFrontierTheoremChecklist

/-- Project Ramsey target rows through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.facade.toRamseyCurrentFrontierTargetRows

/-- Project the Ramsey normalization route through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toRamseyCurrentFrontierNormalizationRoute
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierNormalizationRoute G s v :=
  h.facade.toRamseyCurrentFrontierNormalizationRoute

/-- Project terminal mixed-core imports through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.facade.toTerminalMixedCore

/-- Project first-bit/co-cut obligations through the packet-atom dashboard extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.facade.toFirstBitCoCut

/-- Project the packet-atom/principal-bucket shadow imports from the terminal extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project packet-atom frontier imports from the terminal extension. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomShadow.to_packetAtomFrontier

/-- Project the principal-bucket shadow frontier assumption from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toPrincipalBucketShadowFrontier
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    principalBucketShadowFrontier :=
  h.packetAtomShadow.to_principalBucketShadowFrontier

/-- Project the size-refined packet-atom frontier assumption from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toSizeRefinedAtoms
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    sizeRefinedAtoms :=
  h.toPacketAtomFrontierImports.to_sizeRefinedAtoms

/-- Project the packet-atom defect-correction frontier assumption from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toDefectCorrection
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    defectCorrection :=
  h.toPacketAtomFrontierImports.to_defectCorrection

/-- Project the packet-atom anti-cancellation frontier assumption from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toUnionAntiCancellation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    unionAntiCancellation :=
  h.toPacketAtomFrontierImports.to_unionAntiCancellation

/-- Project a packet-atom selector obligation from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.packetAtomObligation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier)
    (selector : FirstBitTerminalPacketAtomFrontierSelector) :
    FirstBitTerminalPacketAtomFrontierSelector.obligation
      sizeRefinedAtoms defectCorrection unionAntiCancellation selector :=
  h.toPacketAtomFrontierImports.obligation selector

/-- Project a packet-atom/principal-bucket shadow selector obligation from the terminal extension. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.packetAtomShadowObligation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier)
    (selector : FirstBitTerminalPacketAtomPrincipalBucketShadowSelector) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowSelector.obligation
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier selector :=
  h.toPacketAtomShadowImports.obligation selector

/-- The packet-atom dashboard extension still exposes the certified proof-md target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdCurrentFrontierRamseyDashboardFacade h.facade

/-!
## Final public proof-md dashboard export

The facade and packet-atom shadow dashboard above are convenient for local consumers.  The following
export layer is intentionally flatter: it carries the target-statement/dashboard route, the Ramsey
current-frontier public rows, and the terminal mixed/co-cut surfaces in one public proof-md API.  The
terminal packet-atom export then attaches the explicit packet-atom/principal-bucket shadow imports
without changing their status as proposition-valued frontier assumptions.
-/

/--
Flat public proof-md dashboard export for the current frontier.  It records only data already
projected by `CertifiedProofMdCurrentFrontierRamseyDashboardFacade`, so it adds no new mathematical
content.
-/
structure CertifiedProofMdCurrentFrontierPublicDashboardExport
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α)) : Type where
  facade :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  downstreamChecklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatement : TargetStatement

/-- Promote the Ramsey dashboard facade to the flat public proof-md export. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v where
  facade := h
  targetStatementBundle := h.toTargetStatementBundle
  finalDashboard := h.toFinalObligationDashboard
  targetConsumer := h.toFinalTargetConsumerCertificate
  downstreamChecklist := h.toDownstreamChecklist
  ramseySurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyTheoremChecklist := h.toRamseyCurrentFrontierTheoremChecklist
  ramseyTargetRows := h.toRamseyCurrentFrontierTargetRows
  ramseyNormalization := h.toRamseyCurrentFrontierNormalizationRoute
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierRamseyDashboardFacade h

/-- Promote a proof-md/Ramsey bridge to the flat public proof-md export. -/
def CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.toRamseyDashboardFacade.toPublicDashboardExport

/-- Build the public proof-md export from target imports and a Ramsey current surface. -/
def CertifiedProofMdCurrentFrontierTargetImports.toPublicDashboardExport
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  (h.toRamseyDashboardFacade hramsey).toPublicDashboardExport

/-- Build the public proof-md export from a downstream checklist and a Ramsey current surface. -/
def CertifiedProofMdCurrentFrontierDownstreamChecklist.toPublicDashboardExport
    (h : CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  (h.toRamseyDashboardFacade hramsey).toPublicDashboardExport

/-- Project the Ramsey dashboard facade from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toRamseyDashboardFacade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.facade

/-- Project target imports from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.facade.toCurrentFrontierTargetImports

/-- Project the target-statement bundle from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final obligation dashboard from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toFinalObligationDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.finalDashboard

/-- Project the final target consumer from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetConsumer

/-- Project the downstream checklist from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toDownstreamChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.downstreamChecklist

/-- Project the Ramsey current-frontier consumer surface from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseySurface

/-- Project the Ramsey theorem checklist from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toRamseyCurrentFrontierTheoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierTheoremChecklist :=
  h.ramseyTheoremChecklist

/-- Project Ramsey target rows from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.ramseyTargetRows

/-- Project the Ramsey normalization route from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toRamseyCurrentFrontierNormalizationRoute
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    RamseyTenR45CurrentFrontierNormalizationRoute G s v :=
  h.ramseyNormalization

/-- Project terminal mixed-core imports from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- The public proof-md export exposes its certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    TargetStatement :=
  h.targetStatement

/-- The public proof-md export's explicit target statement normalizes with its bundle route. -/
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.targetStatement_eq_bundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toTargetStatementBundle.targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierPublicDashboardExport h := by
  exact Subsingleton.elim _ _

/-- Ramsey target rows in the public proof-md export normalize with the theorem-checklist route. -/
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.ramseyTargetRows_eq_theoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toRamseyCurrentFrontierTargetRows =
      h.toRamseyCurrentFrontierTheoremChecklist.toCurrentFrontierTargetRows := by
  exact Subsingleton.elim _ _

/--
Public export with terminal packet-atom/principal-bucket shadow imports attached.  The packet-atom
rows remain explicit assumptions, bundled only for downstream import convenience.
-/
structure CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  publicExport :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  terminalPacketAtomShadow :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier

/-- Promote the terminal packet-atom shadow dashboard to the final public packet-atom export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicExport := h.toRamseyDashboardFacade.toPublicDashboardExport
  terminalPacketAtomShadow := h
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports

/-- Attach packet-atom/shadow imports to an already flattened public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.withTerminalPacketAtomPublicExportImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicExport := h
  terminalPacketAtomShadow :=
    h.toRamseyDashboardFacade.withTerminalPacketAtomShadowImports hpacketShadow
  packetAtomFrontier := hpacketShadow.to_packetAtomFrontier
  packetAtomShadow := hpacketShadow

/-- Attach packet-atom/shadow frontier proofs to an already flattened public proof-md export. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.withTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacket :
      FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
    (hshadow : principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.withTerminalPacketAtomPublicExportImports
    (firstBitTerminalPacketAtomPrincipalBucketShadowImports_of_parts hpacket hshadow)

/-- Attach packet-atom/shadow imports directly to the Ramsey dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomPublicExportImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicDashboardExport.withTerminalPacketAtomPublicExportImports hpacketShadow

/-- Attach packet-atom/shadow frontier proofs directly to the Ramsey dashboard facade. -/
def CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacket :
      FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
    (hshadow : principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicDashboardExport.withTerminalPacketAtomPublicExport hpacket hshadow

/-- Project the public proof-md export from the terminal packet-atom public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.publicExport

/-- Project the terminal packet-atom shadow dashboard from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toTerminalPacketAtomShadowDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomShadow

/-- Project the Ramsey dashboard facade from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toRamseyDashboardFacade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.publicExport.toRamseyDashboardFacade

/-- Project target imports from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.publicExport.toCurrentFrontierTargetImports

/-- Project Ramsey target rows from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.publicExport.toRamseyCurrentFrontierTargetRows

/-- Project terminal mixed-core imports from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.publicExport.toTerminalMixedCore

/-- Project first-bit/co-cut obligations from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.publicExport.toFirstBitCoCut

/-- Project packet-atom frontier imports from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom/principal-bucket shadow imports from the terminal public export. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- The terminal public export exposes the certified proof-md target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  targetStatement_of_certifiedProofMdCurrentFrontierPublicDashboardExport h.publicExport

/-- Project the principal-bucket shadow frontier assumption from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toPrincipalBucketShadowFrontier
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    principalBucketShadowFrontier :=
  h.toPacketAtomShadowImports.to_principalBucketShadowFrontier

/-- Project the size-refined packet-atom frontier assumption from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toSizeRefinedAtoms
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    sizeRefinedAtoms :=
  h.toPacketAtomFrontierImports.to_sizeRefinedAtoms

/-- Project the packet-atom defect-correction frontier assumption from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toDefectCorrection
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    defectCorrection :=
  h.toPacketAtomFrontierImports.to_defectCorrection

/-- Project the packet-atom union anti-cancellation frontier assumption from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toUnionAntiCancellation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    unionAntiCancellation :=
  h.toPacketAtomFrontierImports.to_unionAntiCancellation

/-- Project a packet-atom selector obligation from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.packetAtomObligation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier)
    (selector : FirstBitTerminalPacketAtomFrontierSelector) :
    FirstBitTerminalPacketAtomFrontierSelector.obligation
      sizeRefinedAtoms defectCorrection unionAntiCancellation selector :=
  h.toPacketAtomFrontierImports.obligation selector

/-- Project a packet-atom/principal-bucket selector obligation from the terminal public export. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.packetAtomShadowObligation
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier)
    (selector : FirstBitTerminalPacketAtomPrincipalBucketShadowSelector) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowSelector.obligation
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier selector :=
  h.toPacketAtomShadowImports.obligation selector

/-- Packet-atom frontier imports in the terminal public export normalize with the shadow projection. -/
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.packetAtomFrontier_eq_shadowProjection
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports =
      h.toPacketAtomShadowImports.to_packetAtomFrontier := by
  exact Subsingleton.elim _ _

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toPublicDashboardExport_facade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toPublicDashboardExport.toRamseyDashboardFacade = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseyDashboardFacade.toPublicDashboardExport_targetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toPublicDashboardExport.toRamseyCurrentFrontierTargetRows =
      h.toRamseyCurrentFrontierTargetRows :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.withTerminalPacketAtomPublicExportImports_publicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    (h.withTerminalPacketAtomPublicExportImports hpacketShadow).toPublicDashboardExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard.toTerminalPacketAtomPublicExport_shadowDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomShadowDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport.toTerminalPacketAtomShadowDashboard = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyDashboardFacade_bridge
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toRamseyDashboardFacade.toRamseySurfaceBridge = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyDashboardFacade_targetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toRamseyDashboardFacade.toCurrentFrontierTargetImports =
      h.toCurrentFrontierTargetImports :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseySurfaceBridge.toRamseyDashboardFacade_ramseyRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseySurfaceBridge
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v) :
    h.toRamseyDashboardFacade.toRamseyCurrentFrontierTargetRows =
      h.toRamseyCurrentFrontierConsumerSurface.toCurrentFrontierTargetRows :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomShadow_facade
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacket :
      FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
    (hshadow : principalBucketShadowFrontier) :
    (h.withTerminalPacketAtomShadow hpacket hshadow).toRamseyDashboardFacade = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierRamseyDashboardFacade.withTerminalPacketAtomShadow_packetAtomFrontier
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierRamseyDashboardFacade
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacket :
      FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
    (hshadow : principalBucketShadowFrontier) :
    (h.withTerminalPacketAtomShadow hpacket hshadow).toPacketAtomFrontierImports = hpacket :=
  by
    exact Subsingleton.elim _ _

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetImports.toDownstreamChecklist_targetImports
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toDownstreamChecklist.targetImports = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetImports.toDownstreamChecklist_targetConsumer
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toDownstreamChecklist.toFinalTargetConsumerCertificate =
      h.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetImports.toDownstreamChecklist_theoremBundle
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toDownstreamChecklist.toUnifiedFinalTheoremBundle =
      h.toUnifiedFinalTheoremBundle :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetImports.toRamseySurfaceBridge_ramseySurface
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo)
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramsey : RamseyTenR45CurrentFrontierConsumerSurface G s v) :
    (h.toRamseySurfaceBridge hramsey).toRamseyCurrentFrontierConsumerSurface =
      hramsey :=
  rfl

@[simp]
theorem CertifiedProofMdFinalObligationDashboard.toCurrentFrontierTargetImports_toFinalObligationDashboard
    (h : CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toCurrentFrontierTargetImports.toFinalObligationDashboard = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierAuditCertificate.toCurrentFrontierTargetImports_toFinalObligationDashboard
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toCurrentFrontierTargetImports.toFinalObligationDashboard =
      h.toFinalObligationDashboard :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierAuditCertificate.toCurrentFrontierTargetImports_targetConsumer
    (h : CertifiedProofMdCurrentFrontierAuditCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toCurrentFrontierTargetImports.toFinalTargetConsumerCertificate =
      h.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem CertifiedProofMdIntegratedFrontierHandoffCertificate.toCurrentFrontierTargetImports_targetConsumer
    (h : CertifiedProofMdIntegratedFrontierHandoffCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toCurrentFrontierTargetImports.toFinalTargetConsumerCertificate =
      h.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetImports.toTargetStatementBundle_targetImports
    (h : CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toTargetStatementBundle.targetImports = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTargetStatementBundle.toFinalTargetConsumerCertificate_targetImports
    (h : CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo) :
    h.toFinalTargetConsumerCertificate =
      h.targetImports.toFinalTargetConsumerCertificate :=
  rfl

/-!
## Final public proof-md checklist

The public dashboard export and terminal packet-atom export above are convenient entry points, but
consumer lanes often need one theorem-only packet that also carries the Ramsey proof-md import surface
and the higher-bit/terminal dyadic hooks already present in the final target consumer.  The checklist
below is only packaging: all frontier rows remain supplied by the existing assumption/local-certificate
fields.
-/

/--
Final public proof-md checklist tying the flattened dashboard, terminal packet-atom shadow imports,
Ramsey proof-md import surface, and higher-bit terminal dyadic hooks into one consumer packet.  It does
not certify new rows; it re-exports the current frontier assumptions already carried by the inputs.
-/
structure CertifiedProofMdCurrentFrontierFinalPublicChecklist
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  publicExport :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  terminalPacketAtomExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  downstreamChecklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatement : TargetStatement

/-- Promote the terminal packet-atom public export to the final public checklist. -/
def CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicExport := h.toPublicDashboardExport
  terminalPacketAtomExport := h
  targetImports := h.toCurrentFrontierTargetImports
  targetStatementBundle := h.toPublicDashboardExport.toTargetStatementBundle
  finalDashboard := h.toPublicDashboardExport.toFinalObligationDashboard
  targetConsumer := h.toPublicDashboardExport.toFinalTargetConsumerCertificate
  downstreamChecklist := h.toPublicDashboardExport.toDownstreamChecklist
  ramseySurface := h.toPublicDashboardExport.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport :=
    h.toPublicDashboardExport.toRamseyCurrentFrontierConsumerSurface.toProofMdImport
  ramseyTheoremChecklist :=
    h.toPublicDashboardExport.toRamseyCurrentFrontierTheoremChecklist
  ramseyTargetRows := h.toRamseyCurrentFrontierTargetRows
  ramseyNormalization := h.toPublicDashboardExport.toRamseyCurrentFrontierNormalizationRoute
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  cliqueOrIndepSetBound16 :=
    h.toPublicDashboardExport.toFinalTargetConsumerCertificate.cliqueOrIndepSetBound16
  terminalTailFromFive :=
    h.toPublicDashboardExport.toFinalTargetConsumerCertificate.terminalTailFromFive
  higherBitTargets :=
    h.toPublicDashboardExport.toFinalTargetConsumerCertificate.higherBitTargets
  targetStatement :=
    targetStatement_of_certifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport h

/--
Attach a chosen Ramsey proof-md import and packet-atom shadow imports to an existing public dashboard
export, producing the final public checklist.  The Ramsey packet is indexed by the same `G, s, v` and
is not used to solve terminal obligations.
-/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.withRamseyProofMdImportAndTerminalPacketAtomImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    (hramseyProofMd : RamseyTenR45CurrentFrontierProofMdImport G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  let hterminal := h.withTerminalPacketAtomPublicExportImports hpacketShadow
  { publicExport := h
    terminalPacketAtomExport := hterminal
    targetImports := h.toCurrentFrontierTargetImports
    targetStatementBundle := h.toTargetStatementBundle
    finalDashboard := h.toFinalObligationDashboard
    targetConsumer := h.toFinalTargetConsumerCertificate
    downstreamChecklist := h.toDownstreamChecklist
    ramseySurface := h.toRamseyCurrentFrontierConsumerSurface
    ramseyProofMdImport := hramseyProofMd
    ramseyTheoremChecklist := h.toRamseyCurrentFrontierTheoremChecklist
    ramseyTargetRows := h.toRamseyCurrentFrontierTargetRows
    ramseyNormalization := h.toRamseyCurrentFrontierNormalizationRoute
    terminalMixedCore := h.toTerminalMixedCore
    firstBitCoCut := h.toFirstBitCoCut
    packetAtomFrontier := hterminal.toPacketAtomFrontierImports
    packetAtomShadow := hterminal.toPacketAtomShadowImports
    cliqueOrIndepSetBound16 := h.toFinalTargetConsumerCertificate.cliqueOrIndepSetBound16
    terminalTailFromFive := h.toFinalTargetConsumerCertificate.terminalTailFromFive
    higherBitTargets := h.toFinalTargetConsumerCertificate.higherBitTargets
    targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierPublicDashboardExport h }

/-- Build the final public checklist using the Ramsey import generated by the public dashboard. -/
def CertifiedProofMdCurrentFrontierPublicDashboardExport.toFinalPublicChecklistWithPacketAtomImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.withRamseyProofMdImportAndTerminalPacketAtomImports
    h.toRamseyCurrentFrontierConsumerSurface.toProofMdImport hpacketShadow

/-- Ramsey proof-md imports can be attached to a certified public dashboard and terminal packet atoms. -/
def RamseyTenR45CurrentFrontierProofMdImport.withCertifiedProofMdPublicDashboardExportAndTerminalPacketAtomImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (hramseyProofMd : RamseyTenR45CurrentFrontierProofMdImport G s v)
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.withRamseyProofMdImportAndTerminalPacketAtomImports hramseyProofMd hpacketShadow

/-- Project the public dashboard export from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.publicExport

/-- Project the terminal packet-atom public export from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomExport

/-- Project target imports from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetImports

/-- Project the target-statement bundle from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final obligation dashboard from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toFinalObligationDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.finalDashboard

/-- Project the final target consumer from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.targetConsumer

/-- Project the downstream checklist from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toDownstreamChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.downstreamChecklist

/-- Project the localized Ramsey surface from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseySurface

/-- Project the Ramsey proof-md import surface from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project Ramsey theorem checklist rows from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toRamseyCurrentFrontierTheoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTheoremChecklist :=
  h.ramseyTheoremChecklist

/-- Project Ramsey target rows from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.ramseyTargetRows

/-- Project the Ramsey normalization route from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toRamseyCurrentFrontierNormalizationRoute
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierNormalizationRoute G s v :=
  h.ramseyNormalization

/-- Project terminal mixed-core imports from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project packet-atom frontier imports from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom/principal-bucket shadow imports from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the `q = 16` terminal Ramsey bound from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.cliqueOrIndepSetBound16

/-- Project the terminal dyadic tail from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project the higher-bit fixed-witness dyadic targets from the final public checklist. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- The final public checklist exposes the certified proof-md target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The checklist target statement normalizes with its target-statement bundle route. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.targetStatement_eq_bundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle.targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist h := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md target rows normalize with the checklist target-row projection. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.ramseyProofMdImport_targetRows_eq_checklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierTargetRows =
      h.toRamseyCurrentFrontierTargetRows := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md normalization routes normalize with the checklist normalization projection. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.ramseyProofMdImport_normalization_eq_checklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierNormalizationRoute =
      h.toRamseyCurrentFrontierNormalizationRoute := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md current-frontier surfaces normalize with the checklist Ramsey surface. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.ramseyProofMdImport_currentFrontier_eq_checklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierConsumerSurface =
      h.toRamseyCurrentFrontierConsumerSurface := by
  exact Subsingleton.elim _ _

/-- Packet-atom frontier imports normalize with the principal-bucket shadow projection. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.packetAtomFrontier_eq_shadowProjection
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports =
      h.toPacketAtomShadowImports.to_packetAtomFrontier := by
  exact Subsingleton.elim _ _

/-- Terminal packet-atom public exports normalize with the checklist packet-atom projection. -/
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.terminalPacketAtomExport_packetAtomFrontier_eq_checklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport.toPacketAtomFrontierImports =
      h.toPacketAtomFrontierImports := by
  exact Subsingleton.elim _ _

@[simp]
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toFinalPublicChecklist_terminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist.toTerminalPacketAtomPublicExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport.toFinalPublicChecklist_publicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist.toPublicDashboardExport = h.toPublicDashboardExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.withRamseyProofMdImportAndTerminalPacketAtomImports_publicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    (hramseyProofMd : RamseyTenR45CurrentFrontierProofMdImport G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    (h.withRamseyProofMdImportAndTerminalPacketAtomImports
      hramseyProofMd hpacketShadow).toPublicDashboardExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.withRamseyProofMdImportAndTerminalPacketAtomImports_ramseyProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    (hramseyProofMd : RamseyTenR45CurrentFrontierProofMdImport G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    (h.withRamseyProofMdImportAndTerminalPacketAtomImports
      hramseyProofMd hpacketShadow).toRamseyCurrentFrontierProofMdImport = hramseyProofMd :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.toFinalPublicChecklistWithPacketAtomImports_publicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    (h.toFinalPublicChecklistWithPacketAtomImports hpacketShadow).toPublicDashboardExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicDashboardExport.toFinalPublicChecklistWithPacketAtomImports_ramseyProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v)
    {sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop}
    (hpacketShadow :
      FirstBitTerminalPacketAtomPrincipalBucketShadowImports
        (FirstBitTerminalPacketAtomFrontierImports
          sizeRefinedAtoms defectCorrection unionAntiCancellation)
        principalBucketShadowFrontier) :
    (h.toFinalPublicChecklistWithPacketAtomImports hpacketShadow).toRamseyCurrentFrontierProofMdImport =
      h.toRamseyCurrentFrontierConsumerSurface.toProofMdImport :=
  rfl

/-!
## Downstream proof-obligation manifest

The final public checklist above is the canonical producer packet.  The manifest below is a
consumer-facing matrix: it keeps the same checklist route, but presents the remaining public
frontier lanes under stable projections for proof-md importers.
-/

/--
Lean-facing obligation matrix for downstream proof-md consumers.  It is populated from the final
public checklist and deliberately contains only projections already exposed there.
-/
structure CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  publicDashboard :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  terminalPacketAtoms :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetConsumer : CertifiedProofMdFinalTargetConsumerCertificate
  downstreamChecklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatement : TargetStatement

/-- Flatten the final public checklist into the downstream proof-obligation matrix. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicDashboard := h.toPublicDashboardExport
  terminalPacketAtoms := h.toTerminalPacketAtomPublicExport
  targetImports := h.toCurrentFrontierTargetImports
  targetStatementBundle := h.toTargetStatementBundle
  finalDashboard := h.toFinalObligationDashboard
  targetConsumer := h.toFinalTargetConsumerCertificate
  downstreamChecklist := h.toDownstreamChecklist
  ramseySurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  ramseyTheoremChecklist := h.toRamseyCurrentFrontierTheoremChecklist
  ramseyTargetRows := h.toRamseyCurrentFrontierTargetRows
  ramseyNormalization := h.toRamseyCurrentFrontierNormalizationRoute
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist h

/--
Consumer manifest for the current public frontier.  The manifest stores the final public checklist and
derives its proof-obligation matrix from it, so downstream projections cannot drift from the checklist.
-/
structure CertifiedProofMdCurrentFrontierDownstreamManifest
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  finalChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier

/-- Constructor from the final public checklist to the downstream manifest. -/
def CertifiedProofMdCurrentFrontierFinalPublicChecklist.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  finalChecklist := h

/-- Non-dot constructor alias for orchestration scripts. -/
def certifiedProofMdCurrentFrontierDownstreamManifest_of_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toDownstreamManifest

/-- Recover the final public checklist from a downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalChecklist

/-- Compute the downstream proof-obligation matrix from a manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicChecklist.toDownstreamObligationMatrix

/-- Project the public dashboard export from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.toProofObligationMatrix.publicDashboard

/-- Project terminal packet-atom public imports from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toProofObligationMatrix.terminalPacketAtoms

/-- Project current-frontier target imports from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toCurrentFrontierTargetImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toProofObligationMatrix.targetImports

/-- Project the target-statement bundle from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toProofObligationMatrix.targetStatementBundle

/-- Project the Ramsey proof-md import surface from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.toProofObligationMatrix.ramseyProofMdImport

/-- Project the Ramsey current-frontier consumer surface from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.toProofObligationMatrix.ramseySurface

/-- Project Ramsey theorem-checklist rows from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toRamseyCurrentFrontierTheoremChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTheoremChecklist :=
  h.toProofObligationMatrix.ramseyTheoremChecklist

/-- Project Ramsey target rows from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toRamseyCurrentFrontierTargetRows
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierTargetRows :=
  h.toProofObligationMatrix.ramseyTargetRows

/-- Project the Ramsey normalization route from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toRamseyCurrentFrontierNormalizationRoute
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierNormalizationRoute G s v :=
  h.toProofObligationMatrix.ramseyNormalization

/-- Project terminal mixed-core imports from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.toProofObligationMatrix.terminalMixedCore

/-- Project first-bit/co-cut obligations from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toProofObligationMatrix.firstBitCoCut

/-- Project terminal packet-atom frontier imports from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.toProofObligationMatrix.packetAtomFrontier

/-- Project terminal packet-atom/principal-bucket shadow imports from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.toProofObligationMatrix.packetAtomShadow

/-- Project the `q = 16` terminal Ramsey bound from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.toProofObligationMatrix.q16TerminalBound

/-- Project the terminal dyadic tail from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.toProofObligationMatrix.terminalTailFromFive

/-- Project higher-bit fixed-witness dyadic targets from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.toProofObligationMatrix.higherBitTargets

/-- Project the final target-statement proof from the downstream manifest. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toProofObligationMatrix.targetStatement

/-- The downstream manifest exposes the certified proof-md target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

/-- The manifest target statement is exactly the target statement in its final public checklist. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.targetStatement_eq_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist
        h.toFinalPublicChecklist :=
  rfl

/-- The manifest target statement normalizes with the existing target-statement bundle. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.targetStatement_eq_bundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle.targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md target rows normalize with the manifest matrix row. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.ramseyProofMdImport_targetRows_eq_matrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierTargetRows =
      h.toRamseyCurrentFrontierTargetRows := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md normalization routes normalize with the manifest matrix route. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.ramseyProofMdImport_normalization_eq_matrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierNormalizationRoute =
      h.toRamseyCurrentFrontierNormalizationRoute := by
  exact Subsingleton.elim _ _

/-- Ramsey proof-md current-frontier surfaces normalize with the manifest Ramsey surface. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.ramseyProofMdImport_currentFrontier_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport.toCurrentFrontierConsumerSurface =
      h.toRamseyCurrentFrontierConsumerSurface := by
  exact Subsingleton.elim _ _

/-- Terminal packet-atom public imports normalize with the manifest packet-atom frontier row. -/
theorem
    CertifiedProofMdCurrentFrontierDownstreamManifest.terminalPacketAtomExport_packetAtomFrontier_eq_matrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport.toPacketAtomFrontierImports =
      h.toPacketAtomFrontierImports := by
  exact Subsingleton.elim _ _

/-- Packet-atom frontier imports normalize with the principal-bucket shadow projection. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.packetAtomFrontier_eq_shadowProjection
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports =
      h.toPacketAtomShadowImports.to_packetAtomFrontier := by
  exact Subsingleton.elim _ _

/-- Terminal packet-atom exports close the same target statement carried by the manifest. -/
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.terminalPacketAtomExport_targetStatement_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    targetStatement_of_certifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
        h.toTerminalPacketAtomPublicExport =
      targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h := by
  exact Subsingleton.elim _ _

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.toDownstreamManifest_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest.toFinalPublicChecklist = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicChecklist.toDownstreamObligationMatrix_targetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix.targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist h :=
  rfl

/-!
## Downstream audit ledger

The downstream manifest is already the canonical consumer handle.  The audit ledger below is a
second, deliberately redundant public layer: it records the manifest-derived matrix together with
the concrete public exports and terminal proof-md imports that external consumers usually need to
check before depending on the final frontier packet.  All fields are projections from the manifest;
the coherence equalities keep the audit layer pinned to the final public checklist.
-/

/--
Stable public export packet for downstream proof-md consumers.  It flattens the manifest into the
matrix row, Ramsey proof-md imports, packet-atom imports, first-bit/co-cut and terminal mixed-core
components, higher-bit tail inputs, target bundle, and final target consumer certificate.
-/
structure CertifiedProofMdCurrentFrontierConsumerObligationExport
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  matrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicDashboard :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  terminalPacketAtomExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  targetImports :
    CertifiedProofMdCurrentFrontierTargetImports
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalDashboard :
    CertifiedProofMdFinalObligationDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  downstreamChecklist :
    CertifiedProofMdCurrentFrontierDownstreamChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  ramseySurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement

/-- Flatten a downstream manifest into the stable consumer obligation export. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  matrix := h.toProofObligationMatrix
  finalChecklist := h.toFinalPublicChecklist
  publicDashboard := h.toPublicDashboardExport
  terminalPacketAtomExport := h.toTerminalPacketAtomPublicExport
  targetImports := h.toCurrentFrontierTargetImports
  targetStatementBundle := h.toTargetStatementBundle
  finalDashboard := h.toProofObligationMatrix.finalDashboard
  downstreamChecklist := h.toProofObligationMatrix.downstreamChecklist
  ramseySurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  ramseyTheoremChecklist := h.toRamseyCurrentFrontierTheoremChecklist
  ramseyTargetRows := h.toRamseyCurrentFrontierTargetRows
  ramseyNormalization := h.toRamseyCurrentFrontierNormalizationRoute
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  finalTargetConsumerCertificate := h.toProofObligationMatrix.targetConsumer
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h

/-- Project the downstream obligation matrix from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.matrix

/-- Project the final public checklist from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalChecklist

/-- Project the public dashboard export from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.publicDashboard

/-- Project the terminal packet-atom public export from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomExport

/-- Project the Ramsey proof-md import surface from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the target-statement bundle from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the terminal mixed-core import packet from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project the first-bit/co-cut obligation surface from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the `q = 16` terminal Ramsey bound from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail import from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project the higher-bit fixed-witness targets from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the final target consumer certificate from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the final target statement from the consumer obligation export. -/
def CertifiedProofMdCurrentFrontierConsumerObligationExport.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/--
Audit ledger for external consumers.  It stores a downstream manifest together with its flattened
consumer export and records the public coherence facts that prevent the matrix, checklist, Ramsey
proof-md import, packet-atom export, target bundle, and final consumer certificate from drifting.
-/
structure CertifiedProofMdCurrentFrontierDownstreamAuditLedger
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  manifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  matrix_eq_manifest :
    consumerExport.toProofObligationMatrix = manifest.toProofObligationMatrix
  finalChecklist_eq_manifest :
    consumerExport.toFinalPublicChecklist = manifest.toFinalPublicChecklist
  publicDashboard_eq_manifest :
    consumerExport.toPublicDashboardExport = manifest.toPublicDashboardExport
  terminalPacketAtomExport_eq_manifest :
    consumerExport.toTerminalPacketAtomPublicExport =
      manifest.toTerminalPacketAtomPublicExport
  ramseyProofMdImport_eq_manifest :
    consumerExport.toRamseyCurrentFrontierProofMdImport =
      manifest.toRamseyCurrentFrontierProofMdImport
  targetStatementBundle_eq_manifest :
    consumerExport.toTargetStatementBundle = manifest.toTargetStatementBundle
  finalTargetConsumer_eq_manifest :
    consumerExport.toFinalTargetConsumerCertificate =
      manifest.toFinalPublicChecklist.toFinalTargetConsumerCertificate
  targetStatement_eq_manifest :
    consumerExport.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest manifest

/-- Constructor from the downstream manifest to the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamManifest.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  manifest := h
  consumerExport := h.toConsumerObligationExport
  matrix_eq_manifest := rfl
  finalChecklist_eq_manifest := rfl
  publicDashboard_eq_manifest := rfl
  terminalPacketAtomExport_eq_manifest := rfl
  ramseyProofMdImport_eq_manifest := rfl
  targetStatementBundle_eq_manifest := rfl
  finalTargetConsumer_eq_manifest := rfl
  targetStatement_eq_manifest := rfl

/-- Non-dot constructor alias for consumers that already hold a downstream manifest. -/
def certifiedProofMdCurrentFrontierDownstreamAuditLedger_of_downstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toDownstreamAuditLedger

/-- Recover the manifest audited by the downstream audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.manifest

/-- Project the flattened consumer export from the downstream audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerExport

/-- Project the downstream obligation matrix from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toConsumerObligationExport.toProofObligationMatrix

/-- Project the final public checklist from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toConsumerObligationExport.toFinalPublicChecklist

/-- Project the public dashboard export from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicDashboardExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v :=
  h.toConsumerObligationExport.toPublicDashboardExport

/-- Project terminal packet-atom public imports from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toConsumerObligationExport.toTerminalPacketAtomPublicExport

/-- Project the Ramsey proof-md import surface from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.toConsumerObligationExport.toRamseyCurrentFrontierProofMdImport

/-- Project the target-statement bundle from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.toConsumerObligationExport.toTargetStatementBundle

/-- Project the final target consumer certificate from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.toConsumerObligationExport.toFinalTargetConsumerCertificate

/-- Project the final target statement from the audit ledger. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toConsumerObligationExport.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_matrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toProofObligationMatrix = h.toProofObligationMatrix :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toFinalPublicChecklist = h.toFinalPublicChecklist :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_publicDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toPublicDashboardExport = h.toPublicDashboardExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_terminalPacketAtom
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toTerminalPacketAtomPublicExport =
      h.toTerminalPacketAtomPublicExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_ramseyProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toRamseyCurrentFrontierProofMdImport =
      h.toRamseyCurrentFrontierProofMdImport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_targetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toTargetStatementBundle = h.toTargetStatementBundle :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_finalTargetConsumer
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toConsumerObligationExport_targetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toDownstreamAuditLedger_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger.toDownstreamManifest = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamManifest.toDownstreamAuditLedger_consumerExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger.toConsumerObligationExport = h.toConsumerObligationExport :=
  rfl

/-- The audit ledger matrix is the matrix computed by its manifest. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toProofObligationMatrix_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toProofObligationMatrix = h.toDownstreamManifest.toProofObligationMatrix :=
  h.matrix_eq_manifest

/-- The audit ledger final checklist is the final checklist stored by its manifest. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalPublicChecklist_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toDownstreamManifest.toFinalPublicChecklist :=
  h.finalChecklist_eq_manifest

/-- The audit ledger public dashboard export normalizes to the manifest projection. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicDashboardExport_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicDashboardExport = h.toDownstreamManifest.toPublicDashboardExport :=
  h.publicDashboard_eq_manifest

/-- The audit ledger terminal packet-atom export normalizes to the manifest projection. -/
@[simp]
theorem
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTerminalPacketAtomPublicExport_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport =
      h.toDownstreamManifest.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomExport_eq_manifest

/-- The audit ledger Ramsey proof-md import normalizes to the manifest projection. -/
@[simp]
theorem
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toRamseyCurrentFrontierProofMdImport_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport =
      h.toDownstreamManifest.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_manifest

/-- The audit ledger target bundle normalizes to the manifest projection. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTargetStatementBundle_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toDownstreamManifest.toTargetStatementBundle :=
  h.targetStatementBundle_eq_manifest

/-- The audit ledger final target consumer is the final consumer carried by the final checklist. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalTargetConsumerCertificate_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toDownstreamManifest.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumer_eq_manifest

/-- The audit ledger target statement normalizes to the manifest target statement. -/
@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toTargetStatement_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierDownstreamManifest h.toDownstreamManifest :=
  h.targetStatement_eq_manifest

/-!
## Final public audit coverage handoff

The downstream audit ledger is the redundant consistency handle.  The following public audit layer
turns it into a stable handoff surface: all downstream projections, Ramsey import rows, terminal
packet-atom exports, first-bit/co-cut and terminal mixed-core imports, q16/tail/higher-bit targets,
the target bundle, and the final consumer certificate are available from one normalized packet.
-/

/--
Public audit checklist for the current proof-md frontier.  Every data field is a projection of the
downstream audit ledger or of its consumer export, and the equality fields pin the public packet to
the audit ledger, downstream manifest, and final checklist routes.
-/
structure CertifiedProofMdCurrentFrontierPublicAuditChecklist
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  auditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  proofObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicDashboard :
    CertifiedProofMdCurrentFrontierPublicDashboardExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  ramseyTheoremChecklist : RamseyTenR45CurrentFrontierTheoremChecklist
  ramseyTargetRows : RamseyTenR45CurrentFrontierTargetRows
  ramseyNormalization : RamseyTenR45CurrentFrontierNormalizationRoute G s v
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatement : TargetStatement
  downstreamManifest_eq_auditLedger :
    downstreamManifest = auditLedger.toDownstreamManifest
  proofObligationMatrix_eq_auditLedger :
    proofObligationMatrix = auditLedger.toProofObligationMatrix
  consumerObligationExport_eq_auditLedger :
    consumerObligationExport = auditLedger.toConsumerObligationExport
  finalPublicChecklist_eq_auditLedger :
    finalPublicChecklist = auditLedger.toFinalPublicChecklist
  publicDashboard_eq_auditLedger :
    publicDashboard = auditLedger.toPublicDashboardExport
  terminalPacketAtomPublicExport_eq_auditLedger :
    terminalPacketAtomPublicExport = auditLedger.toTerminalPacketAtomPublicExport
  ramseyProofMdImport_eq_auditLedger :
    ramseyProofMdImport = auditLedger.toRamseyCurrentFrontierProofMdImport
  targetStatementBundle_eq_auditLedger :
    targetStatementBundle = auditLedger.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_auditLedger :
    finalTargetConsumerCertificate = auditLedger.toFinalTargetConsumerCertificate
  targetStatement_eq_auditLedger :
    targetStatement = auditLedger.toTargetStatement
  ramseyConsumerSurface_eq_consumerExport :
    ramseyConsumerSurface = consumerObligationExport.ramseySurface
  ramseyTheoremChecklist_eq_consumerExport :
    ramseyTheoremChecklist = consumerObligationExport.ramseyTheoremChecklist
  ramseyTargetRows_eq_consumerExport :
    ramseyTargetRows = consumerObligationExport.ramseyTargetRows
  ramseyNormalization_eq_consumerExport :
    ramseyNormalization = consumerObligationExport.ramseyNormalization
  terminalMixedCore_eq_consumerExport :
    terminalMixedCore = consumerObligationExport.toTerminalMixedCore
  firstBitCoCut_eq_consumerExport :
    firstBitCoCut = consumerObligationExport.toFirstBitCoCut
  packetAtomFrontier_eq_consumerExport :
    packetAtomFrontier = consumerObligationExport.packetAtomFrontier
  packetAtomShadow_eq_consumerExport :
    packetAtomShadow = consumerObligationExport.packetAtomShadow
  q16TerminalBound_eq_consumerExport :
    q16TerminalBound = consumerObligationExport.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_consumerExport :
    terminalTailFromFive = consumerObligationExport.toTerminalTailFromFive
  higherBitTargets_eq_consumerExport :
    higherBitTargets = consumerObligationExport.toHigherBitFixedWitnessTargetsFromEleven

/-- Promote the downstream audit ledger to the public audit checklist. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  auditLedger := h
  downstreamManifest := h.toDownstreamManifest
  proofObligationMatrix := h.toProofObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  publicDashboard := h.toPublicDashboardExport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  ramseyConsumerSurface := h.toConsumerObligationExport.ramseySurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  ramseyTheoremChecklist := h.toConsumerObligationExport.ramseyTheoremChecklist
  ramseyTargetRows := h.toConsumerObligationExport.ramseyTargetRows
  ramseyNormalization := h.toConsumerObligationExport.ramseyNormalization
  terminalMixedCore := h.toConsumerObligationExport.toTerminalMixedCore
  firstBitCoCut := h.toConsumerObligationExport.toFirstBitCoCut
  packetAtomFrontier := h.toConsumerObligationExport.packetAtomFrontier
  packetAtomShadow := h.toConsumerObligationExport.packetAtomShadow
  q16TerminalBound := h.toConsumerObligationExport.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toConsumerObligationExport.toTerminalTailFromFive
  higherBitTargets := h.toConsumerObligationExport.toHigherBitFixedWitnessTargetsFromEleven
  targetStatement := h.toTargetStatement
  downstreamManifest_eq_auditLedger := rfl
  proofObligationMatrix_eq_auditLedger := rfl
  consumerObligationExport_eq_auditLedger := rfl
  finalPublicChecklist_eq_auditLedger := rfl
  publicDashboard_eq_auditLedger := rfl
  terminalPacketAtomPublicExport_eq_auditLedger := rfl
  ramseyProofMdImport_eq_auditLedger := rfl
  targetStatementBundle_eq_auditLedger := rfl
  finalTargetConsumerCertificate_eq_auditLedger := rfl
  targetStatement_eq_auditLedger := rfl
  ramseyConsumerSurface_eq_consumerExport := rfl
  ramseyTheoremChecklist_eq_consumerExport := rfl
  ramseyTargetRows_eq_consumerExport := rfl
  ramseyNormalization_eq_consumerExport := rfl
  terminalMixedCore_eq_consumerExport := rfl
  firstBitCoCut_eq_consumerExport := rfl
  packetAtomFrontier_eq_consumerExport := rfl
  packetAtomShadow_eq_consumerExport := rfl
  q16TerminalBound_eq_consumerExport := rfl
  terminalTailFromFive_eq_consumerExport := rfl
  higherBitTargets_eq_consumerExport := rfl

/-- Non-dot constructor from the audit ledger to the public audit checklist. -/
def certifiedProofMdCurrentFrontierPublicAuditChecklist_of_downstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicAuditChecklist

/-- Project the audited downstream ledger from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.auditLedger

/-- Project the downstream manifest from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream proof-obligation matrix from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.proofObligationMatrix

/-- Project the consumer obligation export from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the terminal packet-atom public export from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project the target-statement bundle from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final consumer certificate from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the Ramsey proof-md import from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the Ramsey current-frontier surface from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the terminal mixed-core imports from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project the first-bit/co-cut obligation surface from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the q16 terminal Ramsey bound from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail import from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project the higher-bit fixed-witness target imports from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the final target statement from the public audit checklist. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The public audit checklist exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicAuditChecklist_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist.toDownstreamAuditLedger = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicAuditChecklist_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist.toFinalPublicChecklist = h.toFinalPublicChecklist :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toPublicAuditChecklist_consumerExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist.toConsumerObligationExport = h.toConsumerObligationExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toProofObligationMatrix_eq_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toProofObligationMatrix = h.toDownstreamAuditLedger.toProofObligationMatrix :=
  h.proofObligationMatrix_eq_auditLedger

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalPublicChecklist_eq_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toDownstreamAuditLedger.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_auditLedger

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toConsumerObligationExport_eq_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toDownstreamAuditLedger.toConsumerObligationExport :=
  h.consumerObligationExport_eq_auditLedger

/-- The public audit matrix is the matrix computed by its downstream manifest. -/
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toProofObligationMatrix_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toProofObligationMatrix = h.toDownstreamManifest.toProofObligationMatrix := by
  calc
    h.toProofObligationMatrix = h.toDownstreamAuditLedger.toProofObligationMatrix :=
      h.proofObligationMatrix_eq_auditLedger
    _ = h.toDownstreamAuditLedger.toDownstreamManifest.toProofObligationMatrix :=
      CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toProofObligationMatrix_eq_manifest
        h.toDownstreamAuditLedger
    _ = h.toDownstreamManifest.toProofObligationMatrix := by
      rw [h.downstreamManifest_eq_auditLedger]

/-- The public audit final checklist is the final checklist stored by its manifest. -/
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalPublicChecklist_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toDownstreamManifest.toFinalPublicChecklist := by
  calc
    h.toFinalPublicChecklist = h.toDownstreamAuditLedger.toFinalPublicChecklist :=
      h.finalPublicChecklist_eq_auditLedger
    _ = h.toDownstreamAuditLedger.toDownstreamManifest.toFinalPublicChecklist :=
      CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalPublicChecklist_eq_manifest
        h.toDownstreamAuditLedger
    _ = h.toDownstreamManifest.toFinalPublicChecklist := by
      rw [h.downstreamManifest_eq_auditLedger]

/-- The public audit final consumer is the consumer carried by the final public checklist. -/
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalTargetConsumerCertificate_eq_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
  calc
    h.toFinalTargetConsumerCertificate =
        h.toDownstreamAuditLedger.toFinalTargetConsumerCertificate :=
      h.finalTargetConsumerCertificate_eq_auditLedger
    _ =
        h.toDownstreamAuditLedger.toDownstreamManifest.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
      CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toFinalTargetConsumerCertificate_eq_manifest
        h.toDownstreamAuditLedger
    _ = h.toDownstreamManifest.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
      rw [h.downstreamManifest_eq_auditLedger]
    _ = h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
      rw [CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalPublicChecklist_eq_manifest h]

/-- The public audit target statement normalizes with the final public checklist target statement. -/
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.targetStatement_eq_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist
        h.toFinalPublicChecklist := by
  exact Subsingleton.elim _ _

/--
Final handoff coverage certificate.  This is the public audit checklist with the most common
downstream handles repeated as stable fields for consumers that want a small projection vocabulary.
-/
structure CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  auditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  proofObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatement : TargetStatement
  auditLedger_eq_publicAudit :
    auditLedger = publicAuditChecklist.toDownstreamAuditLedger
  downstreamManifest_eq_publicAudit :
    downstreamManifest = publicAuditChecklist.toDownstreamManifest
  proofObligationMatrix_eq_publicAudit :
    proofObligationMatrix = publicAuditChecklist.toProofObligationMatrix
  consumerObligationExport_eq_publicAudit :
    consumerObligationExport = publicAuditChecklist.toConsumerObligationExport
  finalPublicChecklist_eq_publicAudit :
    finalPublicChecklist = publicAuditChecklist.toFinalPublicChecklist
  terminalPacketAtomPublicExport_eq_publicAudit :
    terminalPacketAtomPublicExport = publicAuditChecklist.toTerminalPacketAtomPublicExport
  targetStatementBundle_eq_publicAudit :
    targetStatementBundle = publicAuditChecklist.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_publicAudit :
    finalTargetConsumerCertificate = publicAuditChecklist.toFinalTargetConsumerCertificate
  terminalMixedCore_eq_publicAudit :
    terminalMixedCore = publicAuditChecklist.toTerminalMixedCore
  firstBitCoCut_eq_publicAudit :
    firstBitCoCut = publicAuditChecklist.toFirstBitCoCut
  q16TerminalBound_eq_publicAudit :
    q16TerminalBound = publicAuditChecklist.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_publicAudit :
    terminalTailFromFive = publicAuditChecklist.toTerminalTailFromFive
  higherBitTargets_eq_publicAudit :
    higherBitTargets = publicAuditChecklist.toHigherBitFixedWitnessTargetsFromEleven
  targetStatement_eq_publicAudit :
    targetStatement = publicAuditChecklist.toTargetStatement

/-- Promote a public audit checklist to the final handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierPublicAuditChecklist.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicAuditChecklist := h
  auditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  proofObligationMatrix := h.toProofObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatement := h.toTargetStatement
  auditLedger_eq_publicAudit := rfl
  downstreamManifest_eq_publicAudit := rfl
  proofObligationMatrix_eq_publicAudit := rfl
  consumerObligationExport_eq_publicAudit := rfl
  finalPublicChecklist_eq_publicAudit := rfl
  terminalPacketAtomPublicExport_eq_publicAudit := rfl
  targetStatementBundle_eq_publicAudit := rfl
  finalTargetConsumerCertificate_eq_publicAudit := rfl
  terminalMixedCore_eq_publicAudit := rfl
  firstBitCoCut_eq_publicAudit := rfl
  q16TerminalBound_eq_publicAudit := rfl
  terminalTailFromFive_eq_publicAudit := rfl
  higherBitTargets_eq_publicAudit := rfl
  targetStatement_eq_publicAudit := rfl

/-- Promote a downstream audit ledger directly to the final handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicAuditChecklist.toHandoffCoverageCertificate

/-- Non-dot constructor from the audit ledger to the final handoff coverage certificate. -/
def certifiedProofMdCurrentFrontierHandoffCoverageCertificate_of_downstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toHandoffCoverageCertificate

/-- Project the public audit checklist from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the audited ledger from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.auditLedger

/-- Project the downstream manifest from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream matrix from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.proofObligationMatrix

/-- Project the consumer export from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the terminal packet-atom public export from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project the target-statement bundle from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final consumer certificate from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project first-bit/co-cut coverage from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project higher-bit target coverage from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the final target statement from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The handoff coverage certificate exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicAuditChecklist.toHandoffCoverageCertificate_publicAudit
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate.toPublicAuditChecklist = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierDownstreamAuditLedger.toHandoffCoverageCertificate_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate.toDownstreamAuditLedger = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalPublicChecklist_eq_publicAudit
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toPublicAuditChecklist.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_publicAudit

/-- The handoff coverage final checklist normalizes with the audited ledger route. -/
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalPublicChecklist_eq_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toDownstreamAuditLedger.toFinalPublicChecklist := by
  calc
    h.toFinalPublicChecklist = h.toPublicAuditChecklist.toFinalPublicChecklist :=
      h.finalPublicChecklist_eq_publicAudit
    _ = h.toPublicAuditChecklist.toDownstreamAuditLedger.toFinalPublicChecklist :=
      h.toPublicAuditChecklist.finalPublicChecklist_eq_auditLedger
    _ = h.toDownstreamAuditLedger.toFinalPublicChecklist := by
      rw [h.auditLedger_eq_publicAudit]

/-- The handoff coverage matrix normalizes with the audited downstream manifest. -/
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toProofObligationMatrix_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toProofObligationMatrix = h.toDownstreamManifest.toProofObligationMatrix := by
  calc
    h.toProofObligationMatrix = h.toPublicAuditChecklist.toProofObligationMatrix :=
      h.proofObligationMatrix_eq_publicAudit
    _ = h.toPublicAuditChecklist.toDownstreamManifest.toProofObligationMatrix :=
      CertifiedProofMdCurrentFrontierPublicAuditChecklist.toProofObligationMatrix_eq_manifest
        h.toPublicAuditChecklist
    _ = h.toDownstreamManifest.toProofObligationMatrix := by
      rw [h.downstreamManifest_eq_publicAudit]

/-- The handoff coverage final consumer normalizes with the final public checklist route. -/
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalTargetConsumerCertificate_eq_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
  calc
    h.toFinalTargetConsumerCertificate =
        h.toPublicAuditChecklist.toFinalTargetConsumerCertificate :=
      h.finalTargetConsumerCertificate_eq_publicAudit
    _ = h.toPublicAuditChecklist.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
      CertifiedProofMdCurrentFrontierPublicAuditChecklist.toFinalTargetConsumerCertificate_eq_finalChecklist
        h.toPublicAuditChecklist
    _ = h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
      rw [h.finalPublicChecklist_eq_publicAudit]

/-!
## Final consumer public handoff

The coverage certificate above is the canonical audited handle.  The final consumer layer below
keeps that certificate as the source of truth while exposing a concise projection vocabulary for
proof-md importers: final checklist, audit ledger, manifest/matrix, consumer export, Ramsey import
routes, terminal packet atoms, first-bit/co-cut and mixed-core obligations, q16/tail/higher-bit
targets, the target bundle, and the final consumer certificate.
-/

/-- Project the Ramsey consumer route from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.toPublicAuditChecklist.toRamseyCurrentFrontierConsumerSurface

/-- Project the Ramsey proof-md import route from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.toPublicAuditChecklist.toRamseyCurrentFrontierProofMdImport

/-- Project terminal mixed-core coverage from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project terminal packet-atom frontier imports from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.toConsumerObligationExport.packetAtomFrontier

/-- Project terminal packet-atom shadow imports from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.toConsumerObligationExport.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the handoff coverage certificate. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/--
Concise public handoff summary for downstream consumers.  It is entirely projection-backed by the
handoff coverage certificate, but repeats the stable public handles that consumers normally import.
-/
structure CertifiedProofMdCurrentFrontierPublicHandoffSummary
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  auditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  proofObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  publicAuditChecklist_eq_coverageCertificate :
    publicAuditChecklist = coverageCertificate.toPublicAuditChecklist
  auditLedger_eq_coverageCertificate :
    auditLedger = coverageCertificate.toDownstreamAuditLedger
  downstreamManifest_eq_coverageCertificate :
    downstreamManifest = coverageCertificate.toDownstreamManifest
  proofObligationMatrix_eq_coverageCertificate :
    proofObligationMatrix = coverageCertificate.toProofObligationMatrix
  consumerObligationExport_eq_coverageCertificate :
    consumerObligationExport = coverageCertificate.toConsumerObligationExport
  finalPublicChecklist_eq_coverageCertificate :
    finalPublicChecklist = coverageCertificate.toFinalPublicChecklist
  ramseyConsumerSurface_eq_coverageCertificate :
    ramseyConsumerSurface = coverageCertificate.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_coverageCertificate :
    ramseyProofMdImport = coverageCertificate.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_coverageCertificate :
    terminalPacketAtomPublicExport = coverageCertificate.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_coverageCertificate :
    terminalMixedCore = coverageCertificate.toTerminalMixedCore
  firstBitCoCut_eq_coverageCertificate :
    firstBitCoCut = coverageCertificate.toFirstBitCoCut
  packetAtomFrontier_eq_coverageCertificate :
    packetAtomFrontier = coverageCertificate.toPacketAtomFrontierImports
  packetAtomShadow_eq_coverageCertificate :
    packetAtomShadow = coverageCertificate.toPacketAtomShadowImports
  q16TerminalBound_eq_coverageCertificate :
    q16TerminalBound = coverageCertificate.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_coverageCertificate :
    terminalTailFromFive = coverageCertificate.toTerminalTailFromFive
  higherBitTargets_eq_coverageCertificate :
    higherBitTargets = coverageCertificate.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_coverageCertificate :
    targetStatementBundle = coverageCertificate.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_coverageCertificate :
    finalTargetConsumerCertificate = coverageCertificate.toFinalTargetConsumerCertificate
  targetStatement_eq_coverageCertificate :
    targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierHandoffCoverageCertificate
        coverageCertificate

/-- Promote a handoff coverage certificate to the concise public handoff summary. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  coverageCertificate := h
  publicAuditChecklist := h.toPublicAuditChecklist
  auditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  proofObligationMatrix := h.toProofObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierHandoffCoverageCertificate h
  publicAuditChecklist_eq_coverageCertificate := rfl
  auditLedger_eq_coverageCertificate := rfl
  downstreamManifest_eq_coverageCertificate := rfl
  proofObligationMatrix_eq_coverageCertificate := rfl
  consumerObligationExport_eq_coverageCertificate := rfl
  finalPublicChecklist_eq_coverageCertificate := rfl
  ramseyConsumerSurface_eq_coverageCertificate := rfl
  ramseyProofMdImport_eq_coverageCertificate := rfl
  terminalPacketAtomPublicExport_eq_coverageCertificate := rfl
  terminalMixedCore_eq_coverageCertificate := rfl
  firstBitCoCut_eq_coverageCertificate := rfl
  packetAtomFrontier_eq_coverageCertificate := rfl
  packetAtomShadow_eq_coverageCertificate := rfl
  q16TerminalBound_eq_coverageCertificate := rfl
  terminalTailFromFive_eq_coverageCertificate := rfl
  higherBitTargets_eq_coverageCertificate := rfl
  targetStatementBundle_eq_coverageCertificate := rfl
  finalTargetConsumerCertificate_eq_coverageCertificate := rfl
  targetStatement_eq_coverageCertificate := rfl

/-- Non-dot constructor from the coverage certificate to the public handoff summary. -/
def certifiedProofMdCurrentFrontierPublicHandoffSummary_of_handoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary

/-- Project the coverage certificate from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.auditLedger

/-- Project the downstream manifest from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.proofObligationMatrix

/-- Project the consumer obligation export from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer route from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import route from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom export from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project terminal mixed-core obligations from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project terminal packet-atom frontier imports from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project terminal packet-atom shadow imports from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project higher-bit fixed-witness targets from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final consumer certificate from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the final target statement from the public handoff summary. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The public handoff summary exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toPublicHandoffSummary_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary.toHandoffCoverageCertificate = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalPublicChecklist_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist =
      h.toHandoffCoverageCertificate.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toDownstreamAuditLedger_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger =
      h.toHandoffCoverageCertificate.toDownstreamAuditLedger :=
  h.auditLedger_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toConsumerObligationExport_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport =
      h.toHandoffCoverageCertificate.toConsumerObligationExport :=
  h.consumerObligationExport_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toRamseyCurrentFrontierProofMdImport_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport =
      h.toHandoffCoverageCertificate.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTerminalPacketAtomPublicExport_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport =
      h.toHandoffCoverageCertificate.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toTargetStatementBundle_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle =
      h.toHandoffCoverageCertificate.toTargetStatementBundle :=
  h.targetStatementBundle_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalTargetConsumerCertificate_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toHandoffCoverageCertificate.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_coverageCertificate

/-- The summary final checklist normalizes with the audit-ledger route. -/
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalPublicChecklist_eq_auditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist =
      h.toDownstreamAuditLedger.toFinalPublicChecklist := by
  calc
    h.toFinalPublicChecklist =
        h.toHandoffCoverageCertificate.toFinalPublicChecklist :=
      h.finalPublicChecklist_eq_coverageCertificate
    _ = h.toHandoffCoverageCertificate.toDownstreamAuditLedger.toFinalPublicChecklist :=
      CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalPublicChecklist_eq_auditLedger
        h.toHandoffCoverageCertificate
    _ = h.toDownstreamAuditLedger.toFinalPublicChecklist := by
      rw [h.auditLedger_eq_coverageCertificate]

/-- The summary final consumer normalizes with the final public checklist route. -/
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalTargetConsumerCertificate_eq_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
  calc
    h.toFinalTargetConsumerCertificate =
        h.toHandoffCoverageCertificate.toFinalTargetConsumerCertificate :=
      h.finalTargetConsumerCertificate_eq_coverageCertificate
    _ =
        h.toHandoffCoverageCertificate.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
      CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalTargetConsumerCertificate_eq_finalChecklist
        h.toHandoffCoverageCertificate
    _ = h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
      rw [← h.finalPublicChecklist_eq_coverageCertificate]

/-- The summary target statement normalizes with the coverage-certificate target statement. -/
theorem CertifiedProofMdCurrentFrontierPublicHandoffSummary.targetStatement_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierHandoffCoverageCertificate
        h.toHandoffCoverageCertificate :=
  h.targetStatement_eq_coverageCertificate

/--
Final consumer export for proof-md clients.  This is the compact handoff summary repackaged with
the exact route fields that downstream proof scripts import directly.
-/
structure CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  coverageCertificate_eq_summary :
    coverageCertificate = publicHandoffSummary.toHandoffCoverageCertificate
  finalPublicChecklist_eq_summary :
    finalPublicChecklist = publicHandoffSummary.toFinalPublicChecklist
  consumerObligationExport_eq_summary :
    consumerObligationExport = publicHandoffSummary.toConsumerObligationExport
  ramseyConsumerSurface_eq_summary :
    ramseyConsumerSurface = publicHandoffSummary.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_summary :
    ramseyProofMdImport = publicHandoffSummary.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_summary :
    terminalPacketAtomPublicExport = publicHandoffSummary.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_summary :
    terminalMixedCore = publicHandoffSummary.toTerminalMixedCore
  firstBitCoCut_eq_summary :
    firstBitCoCut = publicHandoffSummary.toFirstBitCoCut
  packetAtomFrontier_eq_summary :
    packetAtomFrontier = publicHandoffSummary.toPacketAtomFrontierImports
  packetAtomShadow_eq_summary :
    packetAtomShadow = publicHandoffSummary.toPacketAtomShadowImports
  q16TerminalBound_eq_summary :
    q16TerminalBound = publicHandoffSummary.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_summary :
    terminalTailFromFive = publicHandoffSummary.toTerminalTailFromFive
  higherBitTargets_eq_summary :
    higherBitTargets = publicHandoffSummary.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_summary :
    targetStatementBundle = publicHandoffSummary.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_summary :
    finalTargetConsumerCertificate = publicHandoffSummary.toFinalTargetConsumerCertificate
  targetStatement_eq_summary :
    targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierPublicHandoffSummary
        publicHandoffSummary
  finalPublicChecklist_eq_coverageCertificate :
    finalPublicChecklist = coverageCertificate.toFinalPublicChecklist
  finalTargetConsumerCertificate_eq_coverageCertificate :
    finalTargetConsumerCertificate = coverageCertificate.toFinalTargetConsumerCertificate

/-- Promote a public handoff summary to the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierPublicHandoffSummary.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  publicHandoffSummary := h
  coverageCertificate := h.toHandoffCoverageCertificate
  finalPublicChecklist := h.toFinalPublicChecklist
  consumerObligationExport := h.toConsumerObligationExport
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierPublicHandoffSummary h
  coverageCertificate_eq_summary := rfl
  finalPublicChecklist_eq_summary := rfl
  consumerObligationExport_eq_summary := rfl
  ramseyConsumerSurface_eq_summary := rfl
  ramseyProofMdImport_eq_summary := rfl
  terminalPacketAtomPublicExport_eq_summary := rfl
  terminalMixedCore_eq_summary := rfl
  firstBitCoCut_eq_summary := rfl
  packetAtomFrontier_eq_summary := rfl
  packetAtomShadow_eq_summary := rfl
  q16TerminalBound_eq_summary := rfl
  terminalTailFromFive_eq_summary := rfl
  higherBitTargets_eq_summary := rfl
  targetStatementBundle_eq_summary := rfl
  finalTargetConsumerCertificate_eq_summary := rfl
  targetStatement_eq_summary := rfl
  finalPublicChecklist_eq_coverageCertificate := h.finalPublicChecklist_eq_coverageCertificate
  finalTargetConsumerCertificate_eq_coverageCertificate :=
    h.finalTargetConsumerCertificate_eq_coverageCertificate

/-- Promote a coverage certificate directly to the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary.toFinalConsumerHandoffExport

/-- Non-dot constructor from the coverage certificate to the final consumer handoff export. -/
def certifiedProofMdCurrentFrontierFinalConsumerHandoffExport_of_handoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalConsumerHandoffExport

/-- Project the summary from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the coverage certificate from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary.toPublicAuditChecklist

/-- Project the downstream audit ledger from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary.toDownstreamAuditLedger

/-- Project the downstream manifest from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary.toDownstreamManifest

/-- Project the downstream obligation matrix from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toProofObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toPublicHandoffSummary.toProofObligationMatrix

/-- Project the consumer obligation export from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer route from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import route from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom export from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project terminal mixed-core obligations from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project packet-atom frontier imports from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom shadow imports from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project higher-bit fixed-witness targets from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final consumer certificate from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the final target statement from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The final consumer handoff export exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalConsumerHandoffExport_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport.toHandoffCoverageCertificate = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toPublicHandoffSummary_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate =
      h.toPublicHandoffSummary.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicChecklist_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist =
      h.toPublicHandoffSummary.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicChecklist_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist =
      h.toHandoffCoverageCertificate.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_coverageCertificate

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toConsumerObligationExport_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport =
      h.toPublicHandoffSummary.toConsumerObligationExport :=
  h.consumerObligationExport_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toRamseyCurrentFrontierProofMdImport_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport =
      h.toPublicHandoffSummary.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTerminalPacketAtomPublicExport_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport =
      h.toPublicHandoffSummary.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toTargetStatementBundle_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle =
      h.toPublicHandoffSummary.toTargetStatementBundle :=
  h.targetStatementBundle_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalTargetConsumerCertificate_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toPublicHandoffSummary.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_summary

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalTargetConsumerCertificate_eq_coverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toHandoffCoverageCertificate.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_coverageCertificate

/-- The export final consumer normalizes with the final public checklist route. -/
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalTargetConsumerCertificate_eq_finalChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
  calc
    h.toFinalTargetConsumerCertificate =
        h.toHandoffCoverageCertificate.toFinalTargetConsumerCertificate :=
      h.finalTargetConsumerCertificate_eq_coverageCertificate
    _ =
        h.toHandoffCoverageCertificate.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
      CertifiedProofMdCurrentFrontierHandoffCoverageCertificate.toFinalTargetConsumerCertificate_eq_finalChecklist
        h.toHandoffCoverageCertificate
    _ = h.toFinalPublicChecklist.toFinalTargetConsumerCertificate := by
      rw [← h.finalPublicChecklist_eq_coverageCertificate]

/-- The export target statement normalizes with its summary route. -/
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.targetStatement_eq_summary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierPublicHandoffSummary
        h.toPublicHandoffSummary :=
  h.targetStatement_eq_summary

/-!
## Final consumer dashboard and handoff manifest

The final consumer handoff export above is intentionally compact.  The dashboard and manifest below
repackage it into reader-facing audit objects: they keep the export as the source of truth while
also spelling out the public summary, audit ledger, downstream manifest/matrix, Ramsey route,
terminal route, target bundle, and remaining assumption-backed surfaces that proof-md consumers
still audit explicitly.
-/

/--
Concise inventory of the remaining assumption-backed surfaces in the current proof-md handoff.
This structure does not close any frontier row; it keeps the Ramsey, terminal, packet-atom, and
target-certificate inputs visible as the surfaces downstream readers still audit.
-/
structure CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement

/-- Extract the remaining assumption-backed surface manifest from the final consumer handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierFinalConsumerHandoffExport h

/--
Final public dashboard for proof-md consumers.  It packages the final consumer handoff export into a
stable audit object with explicit projections for every public summary, audit, downstream, Ramsey,
terminal, and target route used by downstream proof scripts.
-/
structure CertifiedProofMdCurrentFrontierFinalConsumerDashboard
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  handoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamAuditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  publicHandoffSummary_eq_export : publicHandoffSummary = handoffExport.toPublicHandoffSummary
  coverageCertificate_eq_export : coverageCertificate = handoffExport.toHandoffCoverageCertificate
  publicAuditChecklist_eq_export : publicAuditChecklist = handoffExport.toPublicAuditChecklist
  downstreamAuditLedger_eq_export : downstreamAuditLedger = handoffExport.toDownstreamAuditLedger
  downstreamManifest_eq_export : downstreamManifest = handoffExport.toDownstreamManifest
  downstreamObligationMatrix_eq_export :
    downstreamObligationMatrix = handoffExport.toProofObligationMatrix
  consumerObligationExport_eq_export :
    consumerObligationExport = handoffExport.toConsumerObligationExport
  finalPublicChecklist_eq_export : finalPublicChecklist = handoffExport.toFinalPublicChecklist
  ramseyConsumerSurface_eq_export :
    ramseyConsumerSurface = handoffExport.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_export :
    ramseyProofMdImport = handoffExport.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_export :
    terminalPacketAtomPublicExport = handoffExport.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_export : terminalMixedCore = handoffExport.toTerminalMixedCore
  firstBitCoCut_eq_export : firstBitCoCut = handoffExport.toFirstBitCoCut
  packetAtomFrontier_eq_export :
    packetAtomFrontier = handoffExport.toPacketAtomFrontierImports
  packetAtomShadow_eq_export : packetAtomShadow = handoffExport.toPacketAtomShadowImports
  q16TerminalBound_eq_export : q16TerminalBound = handoffExport.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_export : terminalTailFromFive = handoffExport.toTerminalTailFromFive
  higherBitTargets_eq_export :
    higherBitTargets = handoffExport.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_export : targetStatementBundle = handoffExport.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_export :
    finalTargetConsumerCertificate = handoffExport.toFinalTargetConsumerCertificate
  targetStatement_eq_export : targetStatement = handoffExport.toTargetStatement
  finalTargetConsumerCertificate_eq_finalPublicChecklist :
    finalTargetConsumerCertificate = finalPublicChecklist.toFinalTargetConsumerCertificate
  targetStatement_eq_finalPublicChecklist :
    targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist finalPublicChecklist

/-- Promote the final consumer handoff export to the stable final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  handoffExport := h
  publicHandoffSummary := h.toPublicHandoffSummary
  coverageCertificate := h.toHandoffCoverageCertificate
  publicAuditChecklist := h.toPublicAuditChecklist
  downstreamAuditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  downstreamObligationMatrix := h.toProofObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := targetStatement_of_certifiedProofMdCurrentFrontierFinalConsumerHandoffExport h
  publicHandoffSummary_eq_export := rfl
  coverageCertificate_eq_export := rfl
  publicAuditChecklist_eq_export := rfl
  downstreamAuditLedger_eq_export := rfl
  downstreamManifest_eq_export := rfl
  downstreamObligationMatrix_eq_export := rfl
  consumerObligationExport_eq_export := rfl
  finalPublicChecklist_eq_export := rfl
  ramseyConsumerSurface_eq_export := rfl
  ramseyProofMdImport_eq_export := rfl
  terminalPacketAtomPublicExport_eq_export := rfl
  terminalMixedCore_eq_export := rfl
  firstBitCoCut_eq_export := rfl
  packetAtomFrontier_eq_export := rfl
  packetAtomShadow_eq_export := rfl
  q16TerminalBound_eq_export := rfl
  terminalTailFromFive_eq_export := rfl
  higherBitTargets_eq_export := rfl
  targetStatementBundle_eq_export := rfl
  finalTargetConsumerCertificate_eq_export := rfl
  targetStatement_eq_export := rfl
  finalTargetConsumerCertificate_eq_finalPublicChecklist :=
    h.toFinalTargetConsumerCertificate_eq_finalChecklist
  targetStatement_eq_finalPublicChecklist := by
    exact Subsingleton.elim _ _

/-- Non-dot constructor for the final consumer dashboard from the final consumer handoff export. -/
def certifiedProofMdCurrentFrontierFinalConsumerDashboard_of_finalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalConsumerDashboard

/-- Project the source final consumer handoff export from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.handoffExport

/-- Project the public handoff summary from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the coverage certificate from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamAuditLedger

/-- Project the downstream manifest from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamObligationMatrix

/-- Project the consumer obligation export from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer surface from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom export from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project terminal mixed-core imports from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project packet-atom frontier imports from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom shadow imports from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project higher-bit fixed-witness targets from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final target consumer certificate from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the target statement from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- Project the concise remaining assumption-backed surface list from the final consumer dashboard. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := h.toTargetStatement

/-- A named handoff manifest view of the final consumer dashboard. -/
structure CertifiedProofMdCurrentFrontierFinalHandoffManifest
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  dashboard :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  handoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  remainingAssumptionSurfaces :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  handoffExport_eq_dashboard : handoffExport = dashboard.toFinalConsumerHandoffExport
  finalPublicChecklist_eq_dashboard : finalPublicChecklist = dashboard.toFinalPublicChecklist
  remainingAssumptionSurfaces_eq_dashboard :
    remainingAssumptionSurfaces = dashboard.toFinalRemainingAssumptionSurfaces
  finalTargetConsumerCertificate_eq_dashboard :
    finalTargetConsumerCertificate = dashboard.toFinalTargetConsumerCertificate
  targetStatement_eq_dashboard : targetStatement = dashboard.toTargetStatement

/-- Promote the final consumer dashboard to its named handoff manifest view. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  dashboard := h
  handoffExport := h.toFinalConsumerHandoffExport
  finalPublicChecklist := h.toFinalPublicChecklist
  remainingAssumptionSurfaces := h.toFinalRemainingAssumptionSurfaces
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := h.toTargetStatement
  handoffExport_eq_dashboard := rfl
  finalPublicChecklist_eq_dashboard := rfl
  remainingAssumptionSurfaces_eq_dashboard := rfl
  finalTargetConsumerCertificate_eq_dashboard := rfl
  targetStatement_eq_dashboard := rfl

/-- Promote the final consumer handoff export directly to the named final handoff manifest. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalConsumerDashboard.toFinalHandoffManifest

/-- Project the dashboard from the named final handoff manifest. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.dashboard

/-- Project the source handoff export from the named final handoff manifest. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.handoffExport

/-- Project the final public checklist from the named final handoff manifest. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the remaining assumption-backed surface list from the named final handoff manifest. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.remainingAssumptionSurfaces

/-- The dashboard exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

/-- The named final handoff manifest exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalConsumerDashboard_handoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard.toFinalConsumerHandoffExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalConsumerDashboard_remainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard.toFinalRemainingAssumptionSurfaces =
      h.toFinalRemainingAssumptionSurfaces :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalHandoffManifest_handoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalHandoffManifest.toFinalConsumerHandoffExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPublicHandoffSummary_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary = h.toFinalConsumerHandoffExport.toPublicHandoffSummary :=
  h.publicHandoffSummary_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toHandoffCoverageCertificate_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate =
      h.toFinalConsumerHandoffExport.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toPublicAuditChecklist_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist = h.toFinalConsumerHandoffExport.toPublicAuditChecklist :=
  h.publicAuditChecklist_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamAuditLedger_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger = h.toFinalConsumerHandoffExport.toDownstreamAuditLedger :=
  h.downstreamAuditLedger_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamManifest_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest = h.toFinalConsumerHandoffExport.toDownstreamManifest :=
  h.downstreamManifest_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toDownstreamObligationMatrix_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix = h.toFinalConsumerHandoffExport.toProofObligationMatrix :=
  h.downstreamObligationMatrix_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toConsumerObligationExport_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toFinalConsumerHandoffExport.toConsumerObligationExport :=
  h.consumerObligationExport_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicChecklist_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalConsumerHandoffExport.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTargetStatementBundle_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toFinalConsumerHandoffExport.toTargetStatementBundle :=
  h.targetStatementBundle_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalTargetConsumerCertificate_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalConsumerHandoffExport.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTargetStatement_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement = h.toFinalConsumerHandoffExport.toTargetStatement :=
  h.targetStatement_eq_export

/-- The dashboard final consumer normalizes with its final public checklist projection. -/
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalTargetConsumerCertificate_eq_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicChecklist.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_finalPublicChecklist

/-- The dashboard target statement normalizes with its final public checklist target route. -/
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toTargetStatement_eq_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicChecklist
        h.toFinalPublicChecklist :=
  h.targetStatement_eq_finalPublicChecklist

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalConsumerDashboard_handoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport =
      h.toFinalConsumerDashboard.toFinalConsumerHandoffExport :=
  h.handoffExport_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicChecklist_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalConsumerDashboard.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalRemainingAssumptionSurfaces_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces =
      h.toFinalConsumerDashboard.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_dashboard

/--
Final public handoff export for downstream proof-md importers.  This compact surface is still
assumption-backed: it repackages the final handoff manifest and dashboard without claiming the
remaining terminal/current-frontier assumptions are closed.
-/
structure CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  finalDashboard :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalHandoffManifest :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalConsumerHandoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  remainingAssumptionSurfaces :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamAuditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  finalDashboard_eq_manifest :
    finalDashboard = finalHandoffManifest.toFinalConsumerDashboard
  finalConsumerHandoffExport_eq_manifest :
    finalConsumerHandoffExport = finalHandoffManifest.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces_eq_manifest :
    remainingAssumptionSurfaces = finalHandoffManifest.toFinalRemainingAssumptionSurfaces
  finalPublicChecklist_eq_manifest :
    finalPublicChecklist = finalHandoffManifest.toFinalPublicChecklist
  finalTargetConsumerCertificate_eq_manifest :
    finalTargetConsumerCertificate = finalHandoffManifest.finalTargetConsumerCertificate
  targetStatement_eq_manifest :
    targetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalHandoffManifest
        finalHandoffManifest
  finalConsumerHandoffExport_eq_dashboard :
    finalConsumerHandoffExport = finalDashboard.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces_eq_dashboard :
    remainingAssumptionSurfaces = finalDashboard.toFinalRemainingAssumptionSurfaces
  finalPublicChecklist_eq_dashboard :
    finalPublicChecklist = finalDashboard.toFinalPublicChecklist
  finalTargetConsumerCertificate_eq_dashboard :
    finalTargetConsumerCertificate = finalDashboard.toFinalTargetConsumerCertificate
  targetStatement_eq_dashboard : targetStatement = finalDashboard.toTargetStatement
  publicHandoffSummary_eq_dashboard :
    publicHandoffSummary = finalDashboard.toPublicHandoffSummary
  coverageCertificate_eq_dashboard :
    coverageCertificate = finalDashboard.toHandoffCoverageCertificate
  publicAuditChecklist_eq_dashboard :
    publicAuditChecklist = finalDashboard.toPublicAuditChecklist
  downstreamAuditLedger_eq_dashboard :
    downstreamAuditLedger = finalDashboard.toDownstreamAuditLedger
  downstreamManifest_eq_dashboard : downstreamManifest = finalDashboard.toDownstreamManifest
  downstreamObligationMatrix_eq_dashboard :
    downstreamObligationMatrix = finalDashboard.toDownstreamObligationMatrix
  consumerObligationExport_eq_dashboard :
    consumerObligationExport = finalDashboard.toConsumerObligationExport
  ramseyConsumerSurface_eq_dashboard :
    ramseyConsumerSurface = finalDashboard.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_dashboard :
    ramseyProofMdImport = finalDashboard.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_dashboard :
    terminalPacketAtomPublicExport = finalDashboard.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_dashboard : terminalMixedCore = finalDashboard.toTerminalMixedCore
  firstBitCoCut_eq_dashboard : firstBitCoCut = finalDashboard.toFirstBitCoCut
  packetAtomFrontier_eq_dashboard :
    packetAtomFrontier = finalDashboard.toPacketAtomFrontierImports
  packetAtomShadow_eq_dashboard : packetAtomShadow = finalDashboard.toPacketAtomShadowImports
  q16TerminalBound_eq_dashboard : q16TerminalBound = finalDashboard.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_dashboard :
    terminalTailFromFive = finalDashboard.toTerminalTailFromFive
  higherBitTargets_eq_dashboard :
    higherBitTargets = finalDashboard.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_dashboard :
    targetStatementBundle = finalDashboard.toTargetStatementBundle

/-- Promote the final handoff manifest to the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  finalDashboard := h.toFinalConsumerDashboard
  finalHandoffManifest := h
  finalConsumerHandoffExport := h.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces := h.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary := h.toFinalConsumerDashboard.toPublicHandoffSummary
  coverageCertificate := h.toFinalConsumerDashboard.toHandoffCoverageCertificate
  publicAuditChecklist := h.toFinalConsumerDashboard.toPublicAuditChecklist
  downstreamAuditLedger := h.toFinalConsumerDashboard.toDownstreamAuditLedger
  downstreamManifest := h.toFinalConsumerDashboard.toDownstreamManifest
  downstreamObligationMatrix := h.toFinalConsumerDashboard.toDownstreamObligationMatrix
  consumerObligationExport := h.toFinalConsumerDashboard.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toFinalConsumerDashboard.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toFinalConsumerDashboard.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toFinalConsumerDashboard.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toFinalConsumerDashboard.toTerminalMixedCore
  firstBitCoCut := h.toFinalConsumerDashboard.toFirstBitCoCut
  packetAtomFrontier := h.toFinalConsumerDashboard.toPacketAtomFrontierImports
  packetAtomShadow := h.toFinalConsumerDashboard.toPacketAtomShadowImports
  q16TerminalBound := h.toFinalConsumerDashboard.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toFinalConsumerDashboard.toTerminalTailFromFive
  higherBitTargets := h.toFinalConsumerDashboard.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toFinalConsumerDashboard.toTargetStatementBundle
  finalTargetConsumerCertificate := h.finalTargetConsumerCertificate
  targetStatement := h.targetStatement
  finalDashboard_eq_manifest := rfl
  finalConsumerHandoffExport_eq_manifest := rfl
  remainingAssumptionSurfaces_eq_manifest := rfl
  finalPublicChecklist_eq_manifest := rfl
  finalTargetConsumerCertificate_eq_manifest := rfl
  targetStatement_eq_manifest := by
    exact Subsingleton.elim _ _
  finalConsumerHandoffExport_eq_dashboard := h.handoffExport_eq_dashboard
  remainingAssumptionSurfaces_eq_dashboard := h.remainingAssumptionSurfaces_eq_dashboard
  finalPublicChecklist_eq_dashboard := h.finalPublicChecklist_eq_dashboard
  finalTargetConsumerCertificate_eq_dashboard := h.finalTargetConsumerCertificate_eq_dashboard
  targetStatement_eq_dashboard := h.targetStatement_eq_dashboard
  publicHandoffSummary_eq_dashboard := rfl
  coverageCertificate_eq_dashboard := rfl
  publicAuditChecklist_eq_dashboard := rfl
  downstreamAuditLedger_eq_dashboard := rfl
  downstreamManifest_eq_dashboard := rfl
  downstreamObligationMatrix_eq_dashboard := rfl
  consumerObligationExport_eq_dashboard := rfl
  ramseyConsumerSurface_eq_dashboard := rfl
  ramseyProofMdImport_eq_dashboard := rfl
  terminalPacketAtomPublicExport_eq_dashboard := rfl
  terminalMixedCore_eq_dashboard := rfl
  firstBitCoCut_eq_dashboard := rfl
  packetAtomFrontier_eq_dashboard := rfl
  packetAtomShadow_eq_dashboard := rfl
  q16TerminalBound_eq_dashboard := rfl
  terminalTailFromFive_eq_dashboard := rfl
  higherBitTargets_eq_dashboard := rfl
  targetStatementBundle_eq_dashboard := rfl

/-- Non-dot constructor for the compact final public handoff export from a final handoff manifest. -/
def certifiedProofMdCurrentFrontierFinalPublicHandoffExport_of_finalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicHandoffExport

/-- Promote the final consumer dashboard to the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalHandoffManifest.toFinalPublicHandoffExport

/-- Promote the final consumer handoff export to the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalHandoffManifest.toFinalPublicHandoffExport
/-- Project the final dashboard from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalDashboard

/-- Project the final handoff manifest from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalHandoffManifest

/-- Project the final consumer handoff export from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalConsumerHandoffExport

/-- Project the remaining assumption-backed surfaces from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.remainingAssumptionSurfaces

/-- Project the public handoff summary from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the coverage certificate from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamAuditLedger

/-- Project the downstream manifest from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamObligationMatrix

/-- Project the consumer obligation export from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer surface from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom export from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project terminal mixed-core imports from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project packet-atom frontier imports from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom shadow imports from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project higher-bit fixed-witness targets from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final target consumer certificate from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the target statement from the compact final public handoff export. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The compact final public handoff export exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport.toFinalHandoffManifest = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport.toFinalConsumerDashboard = h.toFinalConsumerDashboard :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport_finalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport.toFinalConsumerHandoffExport =
      h.toFinalConsumerHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport_remainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport.toFinalRemainingAssumptionSurfaces =
      h.toFinalRemainingAssumptionSurfaces :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicHandoffExport_finalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport.toFinalPublicChecklist = h.toFinalPublicChecklist :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalConsumerDashboard_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard = h.toFinalHandoffManifest.toFinalConsumerDashboard :=
  h.finalDashboard_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalConsumerHandoffExport_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport = h.toFinalHandoffManifest.toFinalConsumerHandoffExport :=
  h.finalConsumerHandoffExport_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalRemainingAssumptionSurfaces_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces =
      h.toFinalHandoffManifest.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicChecklist_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalHandoffManifest.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalTargetConsumerCertificate_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalHandoffManifest.finalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTargetStatement_eq_manifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement =
      targetStatement_of_certifiedProofMdCurrentFrontierFinalHandoffManifest
        h.toFinalHandoffManifest :=
  h.targetStatement_eq_manifest

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalConsumerHandoffExport_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport =
      h.toFinalConsumerDashboard.toFinalConsumerHandoffExport :=
  h.finalConsumerHandoffExport_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalRemainingAssumptionSurfaces_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces =
      h.toFinalConsumerDashboard.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPublicHandoffSummary_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary = h.toFinalConsumerDashboard.toPublicHandoffSummary :=
  h.publicHandoffSummary_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toHandoffCoverageCertificate_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate =
      h.toFinalConsumerDashboard.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPublicAuditChecklist_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist = h.toFinalConsumerDashboard.toPublicAuditChecklist :=
  h.publicAuditChecklist_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamAuditLedger_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger = h.toFinalConsumerDashboard.toDownstreamAuditLedger :=
  h.downstreamAuditLedger_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamManifest_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest = h.toFinalConsumerDashboard.toDownstreamManifest :=
  h.downstreamManifest_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toDownstreamObligationMatrix_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix =
      h.toFinalConsumerDashboard.toDownstreamObligationMatrix :=
  h.downstreamObligationMatrix_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toConsumerObligationExport_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toFinalConsumerDashboard.toConsumerObligationExport :=
  h.consumerObligationExport_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicChecklist_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalConsumerDashboard.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toRamseyCurrentFrontierConsumerSurface_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierConsumerSurface =
      h.toFinalConsumerDashboard.toRamseyCurrentFrontierConsumerSurface :=
  h.ramseyConsumerSurface_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toRamseyCurrentFrontierProofMdImport_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport =
      h.toFinalConsumerDashboard.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalPacketAtomPublicExport_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport =
      h.toFinalConsumerDashboard.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalMixedCore_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalMixedCore = h.toFinalConsumerDashboard.toTerminalMixedCore :=
  h.terminalMixedCore_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFirstBitCoCut_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFirstBitCoCut = h.toFinalConsumerDashboard.toFirstBitCoCut :=
  h.firstBitCoCut_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPacketAtomFrontierImports_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports =
      h.toFinalConsumerDashboard.toPacketAtomFrontierImports :=
  h.packetAtomFrontier_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toPacketAtomShadowImports_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomShadowImports = h.toFinalConsumerDashboard.toPacketAtomShadowImports :=
  h.packetAtomShadow_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toCliqueOrIndepSetBound16_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toCliqueOrIndepSetBound16 = h.toFinalConsumerDashboard.toCliqueOrIndepSetBound16 :=
  h.q16TerminalBound_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTerminalTailFromFive_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalTailFromFive = h.toFinalConsumerDashboard.toTerminalTailFromFive :=
  h.terminalTailFromFive_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toHigherBitFixedWitnessTargetsFromEleven_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHigherBitFixedWitnessTargetsFromEleven =
      h.toFinalConsumerDashboard.toHigherBitFixedWitnessTargetsFromEleven :=
  h.higherBitTargets_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTargetStatementBundle_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toFinalConsumerDashboard.toTargetStatementBundle :=
  h.targetStatementBundle_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalTargetConsumerCertificate_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalConsumerDashboard.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_dashboard

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toTargetStatement_eq_dashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement = h.toFinalConsumerDashboard.toTargetStatement :=
  h.targetStatement_eq_dashboard
/--
Final public release bundle for consumers that want one named handoff object containing the
compact public export together with its dashboard, manifest, audit, downstream, Ramsey, and
remaining-assumption projections.  This is still a current-frontier bundle: the remaining
assumption surfaces are exported explicitly rather than discharged.
-/
structure CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  finalPublicHandoffExport :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalDashboard :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalHandoffManifest :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalConsumerHandoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  remainingAssumptionSurfaces :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamAuditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface : RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport : RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore : CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound : HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets : HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate : CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement : TargetStatement
  finalDashboard_eq_export :
    finalDashboard = finalPublicHandoffExport.toFinalConsumerDashboard
  finalHandoffManifest_eq_export :
    finalHandoffManifest = finalPublicHandoffExport.toFinalHandoffManifest
  finalConsumerHandoffExport_eq_export :
    finalConsumerHandoffExport = finalPublicHandoffExport.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces_eq_export :
    remainingAssumptionSurfaces = finalPublicHandoffExport.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary_eq_export :
    publicHandoffSummary = finalPublicHandoffExport.toPublicHandoffSummary
  coverageCertificate_eq_export :
    coverageCertificate = finalPublicHandoffExport.toHandoffCoverageCertificate
  publicAuditChecklist_eq_export :
    publicAuditChecklist = finalPublicHandoffExport.toPublicAuditChecklist
  downstreamAuditLedger_eq_export :
    downstreamAuditLedger = finalPublicHandoffExport.toDownstreamAuditLedger
  downstreamManifest_eq_export :
    downstreamManifest = finalPublicHandoffExport.toDownstreamManifest
  downstreamObligationMatrix_eq_export :
    downstreamObligationMatrix = finalPublicHandoffExport.toDownstreamObligationMatrix
  consumerObligationExport_eq_export :
    consumerObligationExport = finalPublicHandoffExport.toConsumerObligationExport
  finalPublicChecklist_eq_export :
    finalPublicChecklist = finalPublicHandoffExport.toFinalPublicChecklist
  ramseyConsumerSurface_eq_export :
    ramseyConsumerSurface = finalPublicHandoffExport.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_export :
    ramseyProofMdImport = finalPublicHandoffExport.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_export :
    terminalPacketAtomPublicExport = finalPublicHandoffExport.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_export :
    terminalMixedCore = finalPublicHandoffExport.toTerminalMixedCore
  firstBitCoCut_eq_export :
    firstBitCoCut = finalPublicHandoffExport.toFirstBitCoCut
  packetAtomFrontier_eq_export :
    packetAtomFrontier = finalPublicHandoffExport.toPacketAtomFrontierImports
  packetAtomShadow_eq_export :
    packetAtomShadow = finalPublicHandoffExport.toPacketAtomShadowImports
  q16TerminalBound_eq_export :
    q16TerminalBound = finalPublicHandoffExport.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_export :
    terminalTailFromFive = finalPublicHandoffExport.toTerminalTailFromFive
  higherBitTargets_eq_export :
    higherBitTargets = finalPublicHandoffExport.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_export :
    targetStatementBundle = finalPublicHandoffExport.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_export :
    finalTargetConsumerCertificate = finalPublicHandoffExport.toFinalTargetConsumerCertificate
  targetStatement_eq_export :
    targetStatement = finalPublicHandoffExport.toTargetStatement

/-- Promote the compact final public handoff export to the final public release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  finalPublicHandoffExport := h
  finalDashboard := h.toFinalConsumerDashboard
  finalHandoffManifest := h.toFinalHandoffManifest
  finalConsumerHandoffExport := h.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces := h.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary := h.toPublicHandoffSummary
  coverageCertificate := h.toHandoffCoverageCertificate
  publicAuditChecklist := h.toPublicAuditChecklist
  downstreamAuditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  downstreamObligationMatrix := h.toDownstreamObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := h.toTargetStatement
  finalDashboard_eq_export := rfl
  finalHandoffManifest_eq_export := rfl
  finalConsumerHandoffExport_eq_export := rfl
  remainingAssumptionSurfaces_eq_export := rfl
  publicHandoffSummary_eq_export := rfl
  coverageCertificate_eq_export := rfl
  publicAuditChecklist_eq_export := rfl
  downstreamAuditLedger_eq_export := rfl
  downstreamManifest_eq_export := rfl
  downstreamObligationMatrix_eq_export := rfl
  consumerObligationExport_eq_export := rfl
  finalPublicChecklist_eq_export := rfl
  ramseyConsumerSurface_eq_export := rfl
  ramseyProofMdImport_eq_export := rfl
  terminalPacketAtomPublicExport_eq_export := rfl
  terminalMixedCore_eq_export := rfl
  firstBitCoCut_eq_export := rfl
  packetAtomFrontier_eq_export := rfl
  packetAtomShadow_eq_export := rfl
  q16TerminalBound_eq_export := rfl
  terminalTailFromFive_eq_export := rfl
  higherBitTargets_eq_export := rfl
  targetStatementBundle_eq_export := rfl
  finalTargetConsumerCertificate_eq_export := rfl
  targetStatement_eq_export := rfl

/-- Non-dot constructor for the final public release bundle. -/
def certifiedProofMdCurrentFrontierFinalPublicReleaseBundle_of_finalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicReleaseBundle

/-- Promote a named final handoff manifest to the final public release bundle. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicHandoffExport.toFinalPublicReleaseBundle

/-- Promote a final consumer dashboard to the final public release bundle. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicHandoffExport.toFinalPublicReleaseBundle

/-- Promote a final consumer handoff export to the final public release bundle. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicHandoffExport.toFinalPublicReleaseBundle

/-- Project the source compact public handoff export from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicHandoffExport

/-- Project the final dashboard from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalDashboard

/-- Project the final handoff manifest from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalHandoffManifest

/-- Project the final consumer handoff export from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalConsumerHandoffExport

/-- Project the remaining assumption-backed surfaces from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.remainingAssumptionSurfaces

/-- Project the public handoff summary from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the coverage certificate from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamAuditLedger

/-- Project the downstream manifest from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamObligationMatrix

/-- Project the consumer obligation export from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer surface from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom public export from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project terminal mixed-core imports from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project first-bit/co-cut obligations from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project packet-atom frontier imports from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project packet-atom shadow imports from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project higher-bit fixed-witness targets from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final target consumer certificate from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the target statement from the release bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The final public release bundle exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicReleaseBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicReleaseBundle.toFinalPublicHandoffExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicReleaseBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicReleaseBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicReleaseBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicReleaseBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicReleaseBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicReleaseBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalConsumerDashboard_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard = h.toFinalPublicHandoffExport.toFinalConsumerDashboard :=
  h.finalDashboard_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalHandoffManifest_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalHandoffManifest = h.toFinalPublicHandoffExport.toFinalHandoffManifest :=
  h.finalHandoffManifest_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalConsumerHandoffExport_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport = h.toFinalPublicHandoffExport.toFinalConsumerHandoffExport :=
  h.finalConsumerHandoffExport_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalRemainingAssumptionSurfaces_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces =
      h.toFinalPublicHandoffExport.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPublicHandoffSummary_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary = h.toFinalPublicHandoffExport.toPublicHandoffSummary :=
  h.publicHandoffSummary_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toHandoffCoverageCertificate_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate =
      h.toFinalPublicHandoffExport.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPublicAuditChecklist_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist = h.toFinalPublicHandoffExport.toPublicAuditChecklist :=
  h.publicAuditChecklist_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamAuditLedger_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger = h.toFinalPublicHandoffExport.toDownstreamAuditLedger :=
  h.downstreamAuditLedger_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamManifest_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest = h.toFinalPublicHandoffExport.toDownstreamManifest :=
  h.downstreamManifest_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toDownstreamObligationMatrix_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix =
      h.toFinalPublicHandoffExport.toDownstreamObligationMatrix :=
  h.downstreamObligationMatrix_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toConsumerObligationExport_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toFinalPublicHandoffExport.toConsumerObligationExport :=
  h.consumerObligationExport_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicChecklist_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalPublicHandoffExport.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toRamseyCurrentFrontierConsumerSurface_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierConsumerSurface =
      h.toFinalPublicHandoffExport.toRamseyCurrentFrontierConsumerSurface :=
  h.ramseyConsumerSurface_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toRamseyCurrentFrontierProofMdImport_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport =
      h.toFinalPublicHandoffExport.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalPacketAtomPublicExport_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport =
      h.toFinalPublicHandoffExport.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalMixedCore_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalMixedCore = h.toFinalPublicHandoffExport.toTerminalMixedCore :=
  h.terminalMixedCore_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFirstBitCoCut_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFirstBitCoCut = h.toFinalPublicHandoffExport.toFirstBitCoCut :=
  h.firstBitCoCut_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPacketAtomFrontierImports_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports =
      h.toFinalPublicHandoffExport.toPacketAtomFrontierImports :=
  h.packetAtomFrontier_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toPacketAtomShadowImports_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomShadowImports = h.toFinalPublicHandoffExport.toPacketAtomShadowImports :=
  h.packetAtomShadow_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toCliqueOrIndepSetBound16_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toCliqueOrIndepSetBound16 = h.toFinalPublicHandoffExport.toCliqueOrIndepSetBound16 :=
  h.q16TerminalBound_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTerminalTailFromFive_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalTailFromFive = h.toFinalPublicHandoffExport.toTerminalTailFromFive :=
  h.terminalTailFromFive_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toHigherBitFixedWitnessTargetsFromEleven_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHigherBitFixedWitnessTargetsFromEleven =
      h.toFinalPublicHandoffExport.toHigherBitFixedWitnessTargetsFromEleven :=
  h.higherBitTargets_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTargetStatementBundle_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toFinalPublicHandoffExport.toTargetStatementBundle :=
  h.targetStatementBundle_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalTargetConsumerCertificate_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate =
      h.toFinalPublicHandoffExport.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_export

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toTargetStatement_eq_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement = h.toFinalPublicHandoffExport.toTargetStatement :=
  h.targetStatement_eq_export
/--
Final public archive bundle for downstream consumers that want a stable archive object above the
final release bundle.  It keeps the release bundle as the canonical source while naming the
public, audit, downstream, Ramsey, terminal, target-theorem, and remaining-assumption surfaces that
are still part of the current frontier rather than closed terminal proofs.
-/
structure CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  finalPublicReleaseBundle :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
          Basis WithHoles PositiveAtom
          AnchoredPacking TraceTwinFree packingSize
          WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
          G s v
          sizeRefinedAtoms defectCorrection unionAntiCancellation
          principalBucketShadowFrontier
  finalPublicHandoffExport :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalDashboard :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalHandoffManifest :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalConsumerHandoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  remainingAssumptionSurfaces :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamAuditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface :
    RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport :
    RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore :
    CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound :
    HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate :
    CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement :
    TargetStatement
  finalPublicHandoffExport_eq_release :
    finalPublicHandoffExport = finalPublicReleaseBundle.toFinalPublicHandoffExport
  finalDashboard_eq_release :
    finalDashboard = finalPublicReleaseBundle.toFinalConsumerDashboard
  finalHandoffManifest_eq_release :
    finalHandoffManifest = finalPublicReleaseBundle.toFinalHandoffManifest
  finalConsumerHandoffExport_eq_release :
    finalConsumerHandoffExport = finalPublicReleaseBundle.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces_eq_release :
    remainingAssumptionSurfaces = finalPublicReleaseBundle.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary_eq_release :
    publicHandoffSummary = finalPublicReleaseBundle.toPublicHandoffSummary
  coverageCertificate_eq_release :
    coverageCertificate = finalPublicReleaseBundle.toHandoffCoverageCertificate
  publicAuditChecklist_eq_release :
    publicAuditChecklist = finalPublicReleaseBundle.toPublicAuditChecklist
  downstreamAuditLedger_eq_release :
    downstreamAuditLedger = finalPublicReleaseBundle.toDownstreamAuditLedger
  downstreamManifest_eq_release :
    downstreamManifest = finalPublicReleaseBundle.toDownstreamManifest
  downstreamObligationMatrix_eq_release :
    downstreamObligationMatrix = finalPublicReleaseBundle.toDownstreamObligationMatrix
  consumerObligationExport_eq_release :
    consumerObligationExport = finalPublicReleaseBundle.toConsumerObligationExport
  finalPublicChecklist_eq_release :
    finalPublicChecklist = finalPublicReleaseBundle.toFinalPublicChecklist
  ramseyConsumerSurface_eq_release :
    ramseyConsumerSurface = finalPublicReleaseBundle.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_release :
    ramseyProofMdImport = finalPublicReleaseBundle.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_release :
    terminalPacketAtomPublicExport = finalPublicReleaseBundle.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_release :
    terminalMixedCore = finalPublicReleaseBundle.toTerminalMixedCore
  firstBitCoCut_eq_release :
    firstBitCoCut = finalPublicReleaseBundle.toFirstBitCoCut
  packetAtomFrontier_eq_release :
    packetAtomFrontier = finalPublicReleaseBundle.toPacketAtomFrontierImports
  packetAtomShadow_eq_release :
    packetAtomShadow = finalPublicReleaseBundle.toPacketAtomShadowImports
  q16TerminalBound_eq_release :
    q16TerminalBound = finalPublicReleaseBundle.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_release :
    terminalTailFromFive = finalPublicReleaseBundle.toTerminalTailFromFive
  higherBitTargets_eq_release :
    higherBitTargets = finalPublicReleaseBundle.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_release :
    targetStatementBundle = finalPublicReleaseBundle.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_release :
    finalTargetConsumerCertificate = finalPublicReleaseBundle.toFinalTargetConsumerCertificate
  targetStatement_eq_release :
    targetStatement = finalPublicReleaseBundle.toTargetStatement

/-- Promote the final public release bundle to the stable final public archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  finalPublicReleaseBundle := h
  finalPublicHandoffExport := h.toFinalPublicHandoffExport
  finalDashboard := h.toFinalConsumerDashboard
  finalHandoffManifest := h.toFinalHandoffManifest
  finalConsumerHandoffExport := h.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces := h.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary := h.toPublicHandoffSummary
  coverageCertificate := h.toHandoffCoverageCertificate
  publicAuditChecklist := h.toPublicAuditChecklist
  downstreamAuditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  downstreamObligationMatrix := h.toDownstreamObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := h.toTargetStatement
  finalPublicHandoffExport_eq_release := rfl
  finalDashboard_eq_release := rfl
  finalHandoffManifest_eq_release := rfl
  finalConsumerHandoffExport_eq_release := rfl
  remainingAssumptionSurfaces_eq_release := rfl
  publicHandoffSummary_eq_release := rfl
  coverageCertificate_eq_release := rfl
  publicAuditChecklist_eq_release := rfl
  downstreamAuditLedger_eq_release := rfl
  downstreamManifest_eq_release := rfl
  downstreamObligationMatrix_eq_release := rfl
  consumerObligationExport_eq_release := rfl
  finalPublicChecklist_eq_release := rfl
  ramseyConsumerSurface_eq_release := rfl
  ramseyProofMdImport_eq_release := rfl
  terminalPacketAtomPublicExport_eq_release := rfl
  terminalMixedCore_eq_release := rfl
  firstBitCoCut_eq_release := rfl
  packetAtomFrontier_eq_release := rfl
  packetAtomShadow_eq_release := rfl
  q16TerminalBound_eq_release := rfl
  terminalTailFromFive_eq_release := rfl
  higherBitTargets_eq_release := rfl
  targetStatementBundle_eq_release := rfl
  finalTargetConsumerCertificate_eq_release := rfl
  targetStatement_eq_release := rfl

/-- Non-dot constructor for the final public archive bundle. -/
def certifiedProofMdCurrentFrontierFinalPublicArchiveBundle_of_finalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle

/-- Promote a final public handoff export to the stable final public archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicReleaseBundle.toFinalPublicArchiveBundle

/-- Promote a final handoff manifest to the stable final public archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicReleaseBundle.toFinalPublicArchiveBundle

/-- Promote a final consumer dashboard to the stable final public archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicReleaseBundle.toFinalPublicArchiveBundle

/-- Promote a final consumer handoff export to the stable final public archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicReleaseBundle.toFinalPublicArchiveBundle

/-- Project the canonical final public release bundle from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicReleaseBundle

/-- Project the source compact public handoff export from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicHandoffExport

/-- Project the final dashboard from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalDashboard

/-- Project the final handoff manifest from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalHandoffManifest

/-- Project the final consumer handoff export from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalConsumerHandoffExport

/-- Project the remaining assumption-backed surfaces from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.remainingAssumptionSurfaces

/-- Project the public handoff summary from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the coverage certificate from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamAuditLedger

/-- Project the downstream manifest from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamObligationMatrix

/-- Project the consumer obligation export from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey consumer surface from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom public export from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project the terminal mixed-core imports from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project the first-bit/co-cut obligations from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the packet-atom frontier imports from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project the packet-atom shadow imports from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project the higher-bit fixed-witness targets from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final target consumer certificate from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the target statement from the archive bundle. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The final public archive bundle exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicArchiveBundle_releaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveBundle.toFinalPublicReleaseBundle = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicArchiveBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveBundle.toFinalPublicHandoffExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicArchiveBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicArchiveBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicArchiveBundle_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveBundle.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicHandoffExport_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport = h.toFinalPublicReleaseBundle.toFinalPublicHandoffExport :=
  h.finalPublicHandoffExport_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalConsumerDashboard_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard = h.toFinalPublicReleaseBundle.toFinalConsumerDashboard :=
  h.finalDashboard_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalHandoffManifest_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalHandoffManifest = h.toFinalPublicReleaseBundle.toFinalHandoffManifest :=
  h.finalHandoffManifest_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalConsumerHandoffExport_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport = h.toFinalPublicReleaseBundle.toFinalConsumerHandoffExport :=
  h.finalConsumerHandoffExport_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalRemainingAssumptionSurfaces_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces = h.toFinalPublicReleaseBundle.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPublicHandoffSummary_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary = h.toFinalPublicReleaseBundle.toPublicHandoffSummary :=
  h.publicHandoffSummary_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toHandoffCoverageCertificate_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate = h.toFinalPublicReleaseBundle.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPublicAuditChecklist_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist = h.toFinalPublicReleaseBundle.toPublicAuditChecklist :=
  h.publicAuditChecklist_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamAuditLedger_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger = h.toFinalPublicReleaseBundle.toDownstreamAuditLedger :=
  h.downstreamAuditLedger_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamManifest_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest = h.toFinalPublicReleaseBundle.toDownstreamManifest :=
  h.downstreamManifest_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toDownstreamObligationMatrix_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix = h.toFinalPublicReleaseBundle.toDownstreamObligationMatrix :=
  h.downstreamObligationMatrix_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toConsumerObligationExport_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toFinalPublicReleaseBundle.toConsumerObligationExport :=
  h.consumerObligationExport_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicChecklist_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalPublicReleaseBundle.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toRamseyCurrentFrontierConsumerSurface_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierConsumerSurface = h.toFinalPublicReleaseBundle.toRamseyCurrentFrontierConsumerSurface :=
  h.ramseyConsumerSurface_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toRamseyCurrentFrontierProofMdImport_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport = h.toFinalPublicReleaseBundle.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalPacketAtomPublicExport_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport = h.toFinalPublicReleaseBundle.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalMixedCore_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalMixedCore = h.toFinalPublicReleaseBundle.toTerminalMixedCore :=
  h.terminalMixedCore_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFirstBitCoCut_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFirstBitCoCut = h.toFinalPublicReleaseBundle.toFirstBitCoCut :=
  h.firstBitCoCut_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPacketAtomFrontierImports_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports = h.toFinalPublicReleaseBundle.toPacketAtomFrontierImports :=
  h.packetAtomFrontier_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toPacketAtomShadowImports_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomShadowImports = h.toFinalPublicReleaseBundle.toPacketAtomShadowImports :=
  h.packetAtomShadow_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toCliqueOrIndepSetBound16_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toCliqueOrIndepSetBound16 = h.toFinalPublicReleaseBundle.toCliqueOrIndepSetBound16 :=
  h.q16TerminalBound_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTerminalTailFromFive_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalTailFromFive = h.toFinalPublicReleaseBundle.toTerminalTailFromFive :=
  h.terminalTailFromFive_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toHigherBitFixedWitnessTargetsFromEleven_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHigherBitFixedWitnessTargetsFromEleven = h.toFinalPublicReleaseBundle.toHigherBitFixedWitnessTargetsFromEleven :=
  h.higherBitTargets_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTargetStatementBundle_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toFinalPublicReleaseBundle.toTargetStatementBundle :=
  h.targetStatementBundle_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalTargetConsumerCertificate_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate = h.toFinalPublicReleaseBundle.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_release

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toTargetStatement_eq_release
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement = h.toFinalPublicReleaseBundle.toTargetStatement :=
  h.targetStatement_eq_release

/--
Final public archive release for clients that want the latest archive layer together with the
release-critical projections named as release fields.  This remains a current-frontier surface: the
remaining assumptions are exposed through `remainingAssumptionSurfaces` rather than hidden as a
closed terminal proof.
-/
structure CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
    (Basis WithHoles PositiveAtom : ℕ → ℕ → Prop)
    (AnchoredPacking : Type*) (TraceTwinFree : AnchoredPacking → Prop)
    (packingSize : AnchoredPacking → ℕ)
    (WitnessCountAtLeast : ℕ → ℕ → Prop)
    (TwoDisjointTemplatesNeedTwo : Prop)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (v : ↑(s : Set α))
    (sizeRefinedAtoms defectCorrection unionAntiCancellation principalBucketShadowFrontier : Prop) :
    Type where
  finalPublicArchiveBundle :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicReleaseBundle :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicHandoffExport :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalDashboard :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalHandoffManifest :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalConsumerHandoffExport :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  remainingAssumptionSurfaces :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicHandoffSummary :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  coverageCertificate :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  publicAuditChecklist :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamAuditLedger :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamManifest :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  downstreamObligationMatrix :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  consumerObligationExport :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  finalPublicChecklist :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  ramseyConsumerSurface :
    RamseyTenR45CurrentFrontierConsumerSurface G s v
  ramseyProofMdImport :
    RamseyTenR45CurrentFrontierProofMdImport G s v
  terminalPacketAtomPublicExport :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier
  terminalMixedCore :
    CertifiedProofMdTerminalMixedTargetCoreImports
  firstBitCoCut :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  packetAtomFrontier :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation
  packetAtomShadow :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier
  q16TerminalBound :
    HasCliqueOrIndepSetBound 16 16 8388607
  terminalTailFromFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive
  higherBitTargets :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven
  targetStatementBundle :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
  finalTargetConsumerCertificate :
    CertifiedProofMdFinalTargetConsumerCertificate
  targetStatement :
    TargetStatement
  finalPublicReleaseBundle_eq_archive :
    finalPublicReleaseBundle = finalPublicArchiveBundle.toFinalPublicReleaseBundle
  finalPublicHandoffExport_eq_archive :
    finalPublicHandoffExport = finalPublicArchiveBundle.toFinalPublicHandoffExport
  finalDashboard_eq_archive :
    finalDashboard = finalPublicArchiveBundle.toFinalConsumerDashboard
  finalHandoffManifest_eq_archive :
    finalHandoffManifest = finalPublicArchiveBundle.toFinalHandoffManifest
  finalConsumerHandoffExport_eq_archive :
    finalConsumerHandoffExport = finalPublicArchiveBundle.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces_eq_archive :
    remainingAssumptionSurfaces = finalPublicArchiveBundle.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary_eq_archive :
    publicHandoffSummary = finalPublicArchiveBundle.toPublicHandoffSummary
  coverageCertificate_eq_archive :
    coverageCertificate = finalPublicArchiveBundle.toHandoffCoverageCertificate
  publicAuditChecklist_eq_archive :
    publicAuditChecklist = finalPublicArchiveBundle.toPublicAuditChecklist
  downstreamAuditLedger_eq_archive :
    downstreamAuditLedger = finalPublicArchiveBundle.toDownstreamAuditLedger
  downstreamManifest_eq_archive :
    downstreamManifest = finalPublicArchiveBundle.toDownstreamManifest
  downstreamObligationMatrix_eq_archive :
    downstreamObligationMatrix = finalPublicArchiveBundle.toDownstreamObligationMatrix
  consumerObligationExport_eq_archive :
    consumerObligationExport = finalPublicArchiveBundle.toConsumerObligationExport
  finalPublicChecklist_eq_archive :
    finalPublicChecklist = finalPublicArchiveBundle.toFinalPublicChecklist
  ramseyConsumerSurface_eq_archive :
    ramseyConsumerSurface = finalPublicArchiveBundle.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport_eq_archive :
    ramseyProofMdImport = finalPublicArchiveBundle.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport_eq_archive :
    terminalPacketAtomPublicExport = finalPublicArchiveBundle.toTerminalPacketAtomPublicExport
  terminalMixedCore_eq_archive :
    terminalMixedCore = finalPublicArchiveBundle.toTerminalMixedCore
  firstBitCoCut_eq_archive :
    firstBitCoCut = finalPublicArchiveBundle.toFirstBitCoCut
  packetAtomFrontier_eq_archive :
    packetAtomFrontier = finalPublicArchiveBundle.toPacketAtomFrontierImports
  packetAtomShadow_eq_archive :
    packetAtomShadow = finalPublicArchiveBundle.toPacketAtomShadowImports
  q16TerminalBound_eq_archive :
    q16TerminalBound = finalPublicArchiveBundle.toCliqueOrIndepSetBound16
  terminalTailFromFive_eq_archive :
    terminalTailFromFive = finalPublicArchiveBundle.toTerminalTailFromFive
  higherBitTargets_eq_archive :
    higherBitTargets = finalPublicArchiveBundle.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle_eq_archive :
    targetStatementBundle = finalPublicArchiveBundle.toTargetStatementBundle
  finalTargetConsumerCertificate_eq_archive :
    finalTargetConsumerCertificate = finalPublicArchiveBundle.toFinalTargetConsumerCertificate
  targetStatement_eq_archive :
    targetStatement = finalPublicArchiveBundle.toTargetStatement

/-- Promote the final public archive bundle to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier where
  finalPublicArchiveBundle := h
  finalPublicReleaseBundle := h.toFinalPublicReleaseBundle
  finalPublicHandoffExport := h.toFinalPublicHandoffExport
  finalDashboard := h.toFinalConsumerDashboard
  finalHandoffManifest := h.toFinalHandoffManifest
  finalConsumerHandoffExport := h.toFinalConsumerHandoffExport
  remainingAssumptionSurfaces := h.toFinalRemainingAssumptionSurfaces
  publicHandoffSummary := h.toPublicHandoffSummary
  coverageCertificate := h.toHandoffCoverageCertificate
  publicAuditChecklist := h.toPublicAuditChecklist
  downstreamAuditLedger := h.toDownstreamAuditLedger
  downstreamManifest := h.toDownstreamManifest
  downstreamObligationMatrix := h.toDownstreamObligationMatrix
  consumerObligationExport := h.toConsumerObligationExport
  finalPublicChecklist := h.toFinalPublicChecklist
  ramseyConsumerSurface := h.toRamseyCurrentFrontierConsumerSurface
  ramseyProofMdImport := h.toRamseyCurrentFrontierProofMdImport
  terminalPacketAtomPublicExport := h.toTerminalPacketAtomPublicExport
  terminalMixedCore := h.toTerminalMixedCore
  firstBitCoCut := h.toFirstBitCoCut
  packetAtomFrontier := h.toPacketAtomFrontierImports
  packetAtomShadow := h.toPacketAtomShadowImports
  q16TerminalBound := h.toCliqueOrIndepSetBound16
  terminalTailFromFive := h.toTerminalTailFromFive
  higherBitTargets := h.toHigherBitFixedWitnessTargetsFromEleven
  targetStatementBundle := h.toTargetStatementBundle
  finalTargetConsumerCertificate := h.toFinalTargetConsumerCertificate
  targetStatement := h.toTargetStatement
  finalPublicReleaseBundle_eq_archive := rfl
  finalPublicHandoffExport_eq_archive := rfl
  finalDashboard_eq_archive := rfl
  finalHandoffManifest_eq_archive := rfl
  finalConsumerHandoffExport_eq_archive := rfl
  remainingAssumptionSurfaces_eq_archive := rfl
  publicHandoffSummary_eq_archive := rfl
  coverageCertificate_eq_archive := rfl
  publicAuditChecklist_eq_archive := rfl
  downstreamAuditLedger_eq_archive := rfl
  downstreamManifest_eq_archive := rfl
  downstreamObligationMatrix_eq_archive := rfl
  consumerObligationExport_eq_archive := rfl
  finalPublicChecklist_eq_archive := rfl
  ramseyConsumerSurface_eq_archive := rfl
  ramseyProofMdImport_eq_archive := rfl
  terminalPacketAtomPublicExport_eq_archive := rfl
  terminalMixedCore_eq_archive := rfl
  firstBitCoCut_eq_archive := rfl
  packetAtomFrontier_eq_archive := rfl
  packetAtomShadow_eq_archive := rfl
  q16TerminalBound_eq_archive := rfl
  terminalTailFromFive_eq_archive := rfl
  higherBitTargets_eq_archive := rfl
  targetStatementBundle_eq_archive := rfl
  finalTargetConsumerCertificate_eq_archive := rfl
  targetStatement_eq_archive := rfl

/-- Non-dot constructor for the final public archive release. -/
def certifiedProofMdCurrentFrontierFinalPublicArchiveRelease_of_finalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveRelease

/-- Promote a final public release bundle to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle.toFinalPublicArchiveRelease

/-- Promote a final public handoff export to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle.toFinalPublicArchiveRelease

/-- Promote a final consumer dashboard to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle.toFinalPublicArchiveRelease

/-- Promote a final handoff manifest to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle.toFinalPublicArchiveRelease

/-- Promote a final consumer handoff export to the final public archive release. -/
def CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.toFinalPublicArchiveBundle.toFinalPublicArchiveRelease

/-- Project the canonical final public archive bundle from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicArchiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicArchiveBundle

/-- Project the canonical final public release bundle from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicReleaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicReleaseBundle

/-- Project the compact final public handoff export from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicHandoffExport

/-- Project the final consumer dashboard from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalConsumerDashboard
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalDashboard

/-- Project the final handoff manifest from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalHandoffManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalHandoffManifest

/-- Project the final consumer handoff export from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalConsumerHandoffExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalConsumerHandoffExport

/-- Project the remaining assumption-backed surfaces from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalRemainingAssumptionSurfaces
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalRemainingAssumptionSurfaces
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.remainingAssumptionSurfaces

/-- Project the public handoff summary from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPublicHandoffSummary
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicHandoffSummary
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicHandoffSummary

/-- Project the handoff coverage certificate from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toHandoffCoverageCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierHandoffCoverageCertificate
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.coverageCertificate

/-- Project the public audit checklist from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPublicAuditChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierPublicAuditChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.publicAuditChecklist

/-- Project the downstream audit ledger from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamAuditLedger
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamAuditLedger
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamAuditLedger

/-- Project the downstream manifest from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamManifest
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamManifest

/-- Project the downstream obligation matrix from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamObligationMatrix
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierDownstreamObligationMatrix
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.downstreamObligationMatrix

/-- Project the consumer obligation export from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toConsumerObligationExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierConsumerObligationExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.consumerObligationExport

/-- Project the final public checklist from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicChecklist
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierFinalPublicChecklist
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.finalPublicChecklist

/-- Project the Ramsey current-frontier consumer surface from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toRamseyCurrentFrontierConsumerSurface
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierConsumerSurface G s v :=
  h.ramseyConsumerSurface

/-- Project the Ramsey proof-md import from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toRamseyCurrentFrontierProofMdImport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    RamseyTenR45CurrentFrontierProofMdImport G s v :=
  h.ramseyProofMdImport

/-- Project the terminal packet-atom public export from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalPacketAtomPublicExport
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTerminalPacketAtomPublicExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier :=
  h.terminalPacketAtomPublicExport

/-- Project the terminal mixed-core imports from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalMixedCore
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdTerminalMixedTargetCoreImports :=
  h.terminalMixedCore

/-- Project the first-bit/co-cut obligation surface from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFirstBitCoCut
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFirstBitCoCutObligationSurface
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.firstBitCoCut

/-- Project the packet-atom frontier imports from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPacketAtomFrontierImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomFrontierImports
      sizeRefinedAtoms defectCorrection unionAntiCancellation :=
  h.packetAtomFrontier

/-- Project the packet-atom shadow imports from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPacketAtomShadowImports
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    FirstBitTerminalPacketAtomPrincipalBucketShadowImports
      (FirstBitTerminalPacketAtomFrontierImports
        sizeRefinedAtoms defectCorrection unionAntiCancellation)
      principalBucketShadowFrontier :=
  h.packetAtomShadow

/-- Project the q16 terminal Ramsey bound from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toCliqueOrIndepSetBound16
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasCliqueOrIndepSetBound 16 16 8388607 :=
  h.q16TerminalBound

/-- Project the terminal dyadic tail route from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalTailFromFive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridgeFiveFromFive :=
  h.terminalTailFromFive

/-- Project the higher-bit fixed-witness targets from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toHigherBitFixedWitnessTargetsFromEleven
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    HigherBitSmallModulusFixedWitnessTargetsFromEleven :=
  h.higherBitTargets

/-- Project the target-statement bundle from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTargetStatementBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdCurrentFrontierTargetStatementBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo :=
  h.targetStatementBundle

/-- Project the final target consumer certificate from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalTargetConsumerCertificate
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    CertifiedProofMdFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate

/-- Project the target statement from the archive release. -/
def CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTargetStatement
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.targetStatement

/-- The final public archive release exposes the certified target statement. -/
theorem targetStatement_of_certifiedProofMdCurrentFrontierFinalPublicArchiveRelease
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    TargetStatement :=
  h.toTargetStatement

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle.toFinalPublicArchiveRelease_archiveBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicArchiveBundle = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle.toFinalPublicArchiveRelease_releaseBundle
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicReleaseBundle
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicReleaseBundle = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicHandoffExport.toFinalPublicArchiveRelease_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicHandoffExport = h :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerDashboard.toFinalPublicArchiveRelease_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerDashboard
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalHandoffManifest.toFinalPublicArchiveRelease_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalHandoffManifest
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport.toFinalPublicArchiveRelease_export
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalConsumerHandoffExport
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicArchiveRelease.toFinalPublicHandoffExport =
      h.toFinalPublicHandoffExport :=
  rfl

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicReleaseBundle_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicReleaseBundle = h.toFinalPublicArchiveBundle.toFinalPublicReleaseBundle :=
  h.finalPublicReleaseBundle_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicHandoffExport_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicHandoffExport = h.toFinalPublicArchiveBundle.toFinalPublicHandoffExport :=
  h.finalPublicHandoffExport_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalConsumerDashboard_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerDashboard = h.toFinalPublicArchiveBundle.toFinalConsumerDashboard :=
  h.finalDashboard_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalHandoffManifest_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalHandoffManifest = h.toFinalPublicArchiveBundle.toFinalHandoffManifest :=
  h.finalHandoffManifest_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalConsumerHandoffExport_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalConsumerHandoffExport = h.toFinalPublicArchiveBundle.toFinalConsumerHandoffExport :=
  h.finalConsumerHandoffExport_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalRemainingAssumptionSurfaces_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalRemainingAssumptionSurfaces = h.toFinalPublicArchiveBundle.toFinalRemainingAssumptionSurfaces :=
  h.remainingAssumptionSurfaces_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPublicHandoffSummary_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicHandoffSummary = h.toFinalPublicArchiveBundle.toPublicHandoffSummary :=
  h.publicHandoffSummary_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toHandoffCoverageCertificate_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHandoffCoverageCertificate = h.toFinalPublicArchiveBundle.toHandoffCoverageCertificate :=
  h.coverageCertificate_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPublicAuditChecklist_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPublicAuditChecklist = h.toFinalPublicArchiveBundle.toPublicAuditChecklist :=
  h.publicAuditChecklist_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamAuditLedger_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamAuditLedger = h.toFinalPublicArchiveBundle.toDownstreamAuditLedger :=
  h.downstreamAuditLedger_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamManifest_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamManifest = h.toFinalPublicArchiveBundle.toDownstreamManifest :=
  h.downstreamManifest_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toDownstreamObligationMatrix_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toDownstreamObligationMatrix = h.toFinalPublicArchiveBundle.toDownstreamObligationMatrix :=
  h.downstreamObligationMatrix_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toConsumerObligationExport_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toConsumerObligationExport = h.toFinalPublicArchiveBundle.toConsumerObligationExport :=
  h.consumerObligationExport_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalPublicChecklist_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalPublicChecklist = h.toFinalPublicArchiveBundle.toFinalPublicChecklist :=
  h.finalPublicChecklist_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toRamseyCurrentFrontierConsumerSurface_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierConsumerSurface = h.toFinalPublicArchiveBundle.toRamseyCurrentFrontierConsumerSurface :=
  h.ramseyConsumerSurface_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toRamseyCurrentFrontierProofMdImport_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toRamseyCurrentFrontierProofMdImport = h.toFinalPublicArchiveBundle.toRamseyCurrentFrontierProofMdImport :=
  h.ramseyProofMdImport_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalPacketAtomPublicExport_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalPacketAtomPublicExport = h.toFinalPublicArchiveBundle.toTerminalPacketAtomPublicExport :=
  h.terminalPacketAtomPublicExport_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalMixedCore_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalMixedCore = h.toFinalPublicArchiveBundle.toTerminalMixedCore :=
  h.terminalMixedCore_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFirstBitCoCut_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFirstBitCoCut = h.toFinalPublicArchiveBundle.toFirstBitCoCut :=
  h.firstBitCoCut_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPacketAtomFrontierImports_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomFrontierImports = h.toFinalPublicArchiveBundle.toPacketAtomFrontierImports :=
  h.packetAtomFrontier_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toPacketAtomShadowImports_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toPacketAtomShadowImports = h.toFinalPublicArchiveBundle.toPacketAtomShadowImports :=
  h.packetAtomShadow_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toCliqueOrIndepSetBound16_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toCliqueOrIndepSetBound16 = h.toFinalPublicArchiveBundle.toCliqueOrIndepSetBound16 :=
  h.q16TerminalBound_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTerminalTailFromFive_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTerminalTailFromFive = h.toFinalPublicArchiveBundle.toTerminalTailFromFive :=
  h.terminalTailFromFive_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toHigherBitFixedWitnessTargetsFromEleven_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toHigherBitFixedWitnessTargetsFromEleven = h.toFinalPublicArchiveBundle.toHigherBitFixedWitnessTargetsFromEleven :=
  h.higherBitTargets_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTargetStatementBundle_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatementBundle = h.toFinalPublicArchiveBundle.toTargetStatementBundle :=
  h.targetStatementBundle_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toFinalTargetConsumerCertificate_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toFinalTargetConsumerCertificate = h.toFinalPublicArchiveBundle.toFinalTargetConsumerCertificate :=
  h.finalTargetConsumerCertificate_eq_archive

@[simp]
theorem CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease.toTargetStatement_eq_archive
    {α : Type} [DecidableEq α] {G : SimpleGraph α} {s : Finset α}
    {v : ↑(s : Set α)}
    (h : CertifiedProofMdCurrentFrontierFinalPublicArchiveRelease
      Basis WithHoles PositiveAtom
      AnchoredPacking TraceTwinFree packingSize
      WitnessCountAtLeast TwoDisjointTemplatesNeedTwo
      G s v
      sizeRefinedAtoms defectCorrection unionAntiCancellation
      principalBucketShadowFrontier) :
    h.toTargetStatement = h.toFinalPublicArchiveBundle.toTargetStatement :=
  h.targetStatement_eq_archive

end FinalObligationDashboard

end RegularInducedSubgraph
