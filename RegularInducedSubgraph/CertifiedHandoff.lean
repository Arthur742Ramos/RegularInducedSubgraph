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

end RegularInducedSubgraph
