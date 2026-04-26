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

end FinalObligationDashboard

end RegularInducedSubgraph
