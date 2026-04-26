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

end RegularInducedSubgraph
