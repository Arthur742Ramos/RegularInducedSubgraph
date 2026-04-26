import RegularInducedSubgraph.Modular.Asymptotic

namespace RegularInducedSubgraph

/-!
# Large-support first-bit coloring frontier

This file isolates the weakest first-bit coloring surface currently needed by the modular
handoff: a bounded mod-`4` coloring theorem only for large even-degree supports.  The
small supports remain handled by the existing empty/singleton reduction from
`HasLargeEvenDegreeModFourLoss32InducedSubgraph` to the full selector.
-/

/--
Large-support version of the even-degree bounded partition import surface.  Since the
loss-`32` selector is already known on supports of size at most `32`, the first-bit handoff only
needs a mod-four congruent-degree coloring theorem for even induced vertex sets with at least
`33` vertices.
-/
def HasLargeEvenDegreeModFourCongruentDegreeColoringBound (C : ℕ) : Prop := by
  classical
  exact
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) {s : Finset (Fin n)},
      33 ≤ s.card →
        (∀ v : ↑(s : Set (Fin n)), Even ((inducedOn G s).degree v)) →
          ∃ color : Fin n → Fin C,
            ∀ r : Fin C, InducesModEqDegree G (s.filter fun v => color v = r) 4

/-- The full even-degree coloring surface trivially restricts to large supports. -/
theorem hasLargeEvenDegreeModFourCongruentDegreeColoringBound_of_evenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hcolor : HasEvenDegreeModFourCongruentDegreeColoringBound C) :
    HasLargeEvenDegreeModFourCongruentDegreeColoringBound C := by
  intro n G s _hsLarge hsEven
  exact hcolor G (s := s) hsEven

/-- An arbitrary-set bounded partition theorem also supplies the large even-degree coloring surface. -/
theorem hasLargeEvenDegreeModFourCongruentDegreeColoringBound_of_modFourCongruentDegreeColoringBound
    {C : ℕ} (hcolor : HasModFourCongruentDegreeColoringBound C) :
    HasLargeEvenDegreeModFourCongruentDegreeColoringBound C :=
  hasLargeEvenDegreeModFourCongruentDegreeColoringBound_of_evenDegreeModFourCongruentDegreeColoringBound
    (hasEvenDegreeModFourCongruentDegreeColoringBound_of_modFourCongruentDegreeColoringBound
      hcolor)

/-- A large-support bounded mod-four coloring remains valid after adding unused colors. -/
theorem hasLargeEvenDegreeModFourCongruentDegreeColoringBound_mono {C D : ℕ} (hCD : C ≤ D)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    HasLargeEvenDegreeModFourCongruentDegreeColoringBound D := by
  intro n G s hsLarge hsEven
  classical
  rcases hcolor G (s := s) hsLarge hsEven with ⟨color, hclasses⟩
  refine ⟨fun v => Fin.castLE hCD (color v), ?_⟩
  intro r
  by_cases hr : r.val < C
  · let rC : Fin C := ⟨r.val, hr⟩
    have hfilter :
        (s.filter fun v => Fin.castLE hCD (color v) = r) =
          s.filter fun v => color v = rC := by
      ext v
      simp [rC, Fin.ext_iff]
    simpa [hfilter] using hclasses rC
  · have hfilter : (s.filter fun v => Fin.castLE hCD (color v) = r) = ∅ := by
      ext v
      constructor
      · intro hv
        have hvEq : Fin.castLE hCD (color v) = r := (Finset.mem_filter.mp hv).2
        have hval : (Fin.castLE hCD (color v)).val = r.val := by
          simpa using congrArg Fin.val hvEq
        exact False.elim <| hr (by
          have hc : (Fin.castLE hCD (color v)).val < C := by
            simpa using (color v).isLt
          rw [← hval]
          exact hc)
      · intro hv
        simp at hv
    rw [hfilter]
    exact inducesModEqDegree_empty G 4

/--
A large-support even-degree coloring theorem with at most `32` colors supplies the large-support
loss-`32` selector by taking the largest color class.
-/
theorem hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph := by
  intro n G s hsLarge hsEven
  classical
  rcases hcolor G (s := s) hsLarge hsEven with ⟨color, hclasses⟩
  rcases exists_mod_class_card_mul_ge_card (s := s) (q := C) hCpos color with
    ⟨r, hr⟩
  refine ⟨s.filter fun v => color v = r, ?_, ?_, hclasses r⟩
  · exact Finset.filter_subset _ _
  · exact le_trans hr (Nat.mul_le_mul_right _ hC)

/--
The large-support coloring surface is enough for the full loss-`32` selector: supports of size at
most `32` are handled by the existing empty/singleton normal form.
-/
theorem hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourLoss32InducedSubgraph
    (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor)

/-- The exact 32-color large-support even-degree partition form closes the large-support selector. -/
theorem hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound32
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound 32) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    (C := 32) (by decide) (by decide) hcolor

/-- The exact 32-color large-support even-degree partition form closes the full loss-`32` selector. -/
theorem hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound32
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound 32) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    (C := 32) (by decide) (by decide) hcolor

/--
Gallai plus a large-support bounded coloring theorem closes the loss-`64` parity-to-mod-`4` lift.
The first-bit coloring theorem is only used after the half-size even-degree cut has produced a large
bucket; all smaller buckets are discharged by the selector's empty/singleton normal form.
-/
theorem hasParityToModFourLoss64FixedWitnessLift_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    HasParityToModFourLoss64FixedWitnessLift :=
  hasParityToModFourLoss64FixedWitnessLift_of_evenDegreeModFourLoss32InducedSubgraph
    (hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor)

/-- Named first-bit import package for the large-support coloring frontier. -/
structure FirstBitLargeSupportColoringCertificate : Type where
  colorCount : ℕ
  colorCount_pos : 0 < colorCount
  colorCount_le32 : colorCount ≤ 32
  coloringBound : HasLargeEvenDegreeModFourCongruentDegreeColoringBound colorCount

/-- Package the full even-degree coloring surface as a large-support first-bit certificate. -/
def firstBitLargeSupportColoringCertificate_of_evenDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasEvenDegreeModFourCongruentDegreeColoringBound C) :
    FirstBitLargeSupportColoringCertificate where
  colorCount := C
  colorCount_pos := hCpos
  colorCount_le32 := hC
  coloringBound :=
    hasLargeEvenDegreeModFourCongruentDegreeColoringBound_of_evenDegreeModFourCongruentDegreeColoringBound
      hcolor

/-- Package an arbitrary-set bounded coloring theorem as a large-support first-bit certificate. -/
def firstBitLargeSupportColoringCertificate_of_modFourColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasModFourCongruentDegreeColoringBound C) :
    FirstBitLargeSupportColoringCertificate where
  colorCount := C
  colorCount_pos := hCpos
  colorCount_le32 := hC
  coloringBound :=
    hasLargeEvenDegreeModFourCongruentDegreeColoringBound_of_modFourCongruentDegreeColoringBound
      hcolor

/-- Project the large-support loss-`32` selector from the named first-bit package. -/
theorem FirstBitLargeSupportColoringCertificate.toLargeEvenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringCertificate) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    h.colorCount_pos h.colorCount_le32 h.coloringBound

/-- Project the full loss-`32` selector from the named first-bit package. -/
theorem FirstBitLargeSupportColoringCertificate.toEvenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringCertificate) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    h.colorCount_pos h.colorCount_le32 h.coloringBound

/-- Project the first-bit parity-to-mod-`4` lift from the named first-bit package. -/
theorem FirstBitLargeSupportColoringCertificate.toParityToModFourLoss64FixedWitnessLift
    (h : FirstBitLargeSupportColoringCertificate) :
    HasParityToModFourLoss64FixedWitnessLift :=
  hasParityToModFourLoss64FixedWitnessLift_of_largeEvenDegreeModFourCongruentDegreeColoringBound
    h.colorCount_pos h.colorCount_le32 h.coloringBound

/--
External-block terminal handoff with the first-bit coloring theorem required only on large even-degree
supports, using any positive `C <= 32` colors.
-/
theorem targetStatement_of_proofMdFinalHandoff_of_largeEvenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (sevenVertexBooleanCertificate :
      ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true)
    (largeEvenModFourColoringBound : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (fixedWitnessExternalBlockSelfBridgeFive :
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_evenDegreeModFourLoss32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
    sevenVertexBooleanCertificate
    (hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC largeEvenModFourColoringBound)
    ramseyTenSmallTable fixedWitnessExternalBlockSelfBridgeFive higherBitSelectors

/--
Current finite-Ramsey handoff with the first-bit coloring theorem required only for large even-degree
supports.  The conversion lands directly in the large-support selector used by this frontier.
-/
theorem targetStatement_of_proofMdFinalHandoff_of_largeEvenModFourColoringBound_le32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (sevenVertexBooleanCertificate :
      ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true)
    (largeEvenModFourColoringBound : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C)
    (ramseyTenSmallTable : RamseyTenSmallTable)
    (cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607)
    (cliqueOrIndepSetBoundTail :
      ∀ {j : ℕ}, 5 ≤ j →
        ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
          2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j)
    (higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_largeEvenDegreeModFourLoss32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
    sevenVertexBooleanCertificate
    (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC largeEvenModFourColoringBound)
    ramseyTenSmallTable cliqueOrIndepSetBound16 cliqueOrIndepSetBoundTail higherBitSelectors

/-- External-block frontier package using the large-support first-bit coloring certificate. -/
structure ProofMdLargeSupportColoringExternalBlockCertificate : Type where
  sevenVertexBooleanCertificate :
    ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true
  firstBit : FirstBitLargeSupportColoringCertificate
  ramseyTenSmallTable : RamseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The large-support coloring external-block package closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringExternalBlockCertificate
    (h : ProofMdLargeSupportColoringExternalBlockCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_largeEvenModFourColoringBound_le32_and_ramseyTenSmallTable_and_fixedWitnessExternalBlockSelfBridgeFive_and_higherBitAffineSelectorsFromEleven
    h.firstBit.colorCount_pos h.firstBit.colorCount_le32 h.sevenVertexBooleanCertificate
    h.firstBit.coloringBound h.ramseyTenSmallTable h.fixedWitnessExternalBlockSelfBridgeFive
    h.higherBitSelectors

/-- Current finite-Ramsey frontier package using the large-support first-bit coloring certificate. -/
structure ProofMdLargeSupportColoringCurrentFrontierCertificate : Type where
  sevenVertexBooleanCertificate :
    ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true
  firstBit : FirstBitLargeSupportColoringCertificate
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- The large-support coloring current-frontier package closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdFinalHandoff_of_largeEvenModFourColoringBound_le32_and_ramseyTenSmallTable_and_cliqueOrIndepSetBound16_and_tail_and_higherBitAffineSelectorsFromEleven
    h.firstBit.colorCount_pos h.firstBit.colorCount_le32 h.sevenVertexBooleanCertificate
    h.firstBit.coloringBound h.ramseyTenSmallTable h.cliqueOrIndepSetBound16
    h.cliqueOrIndepSetBoundTail h.higherBitSelectors

end RegularInducedSubgraph
