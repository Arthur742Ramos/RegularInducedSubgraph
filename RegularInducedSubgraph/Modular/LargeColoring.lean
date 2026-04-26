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

/-- The current first-bit selector surfaces derived from the large-support coloring frontier. -/
structure FirstBitCurrentSelectorAssumptions : Prop where
  largeEvenDegreeModFourLoss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  parityToModFourLoss64FixedWitnessLift : HasParityToModFourLoss64FixedWitnessLift

namespace FirstBitCurrentSelectorAssumptions

/-- Package the current first-bit selector surfaces from the large-support loss-`32` selector. -/
def ofLargeEvenDegreeModFourLoss32
    (hloss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph) :
    FirstBitCurrentSelectorAssumptions where
  largeEvenDegreeModFourLoss32 := hloss32
  evenDegreeModFourLoss32 :=
    hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourLoss32InducedSubgraph
      hloss32
  parityToModFourLoss64FixedWitnessLift :=
    hasParityToModFourLoss64FixedWitnessLift_of_evenDegreeModFourLoss32InducedSubgraph
      (hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourLoss32InducedSubgraph
        hloss32)

/-- Package the current first-bit selector surfaces from the full loss-`32` selector. -/
def ofEvenDegreeModFourLoss32
    (hloss32 : HasEvenDegreeModFourLoss32InducedSubgraph) :
    FirstBitCurrentSelectorAssumptions where
  largeEvenDegreeModFourLoss32 :=
    hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_evenDegreeModFourLoss32InducedSubgraph
      hloss32
  evenDegreeModFourLoss32 := hloss32
  parityToModFourLoss64FixedWitnessLift :=
    hasParityToModFourLoss64FixedWitnessLift_of_evenDegreeModFourLoss32InducedSubgraph hloss32

/-- Package the selector assumptions directly from a large-support bounded coloring theorem. -/
def ofLargeEvenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    FirstBitCurrentSelectorAssumptions :=
  ofLargeEvenDegreeModFourLoss32
    (hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor)

end FirstBitCurrentSelectorAssumptions

/-- Expose the large-support certificate as the current selector-assumption bundle. -/
def FirstBitLargeSupportColoringCertificate.toCurrentSelectorAssumptions
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitCurrentSelectorAssumptions :=
  FirstBitCurrentSelectorAssumptions.ofLargeEvenDegreeModFourCongruentDegreeColoringBound
    h.colorCount_pos h.colorCount_le32 h.coloringBound

/-- Package the selector assumptions from the named large-support certificate. -/
def FirstBitCurrentSelectorAssumptions.ofLargeSupportColoringCertificate
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitCurrentSelectorAssumptions :=
  h.toCurrentSelectorAssumptions

/-- Tags for the public facade names used by notes, archives, releases, and final handoff statements. -/
inductive FirstBitLargeSupportColoringFacadeKind : Type where
  | publicView
  | finalView
  | archiveView
  | releaseView

/-- A tagged facade around the canonical large-support first-bit coloring certificate. -/
structure FirstBitLargeSupportColoringFacade
    (_kind : FirstBitLargeSupportColoringFacadeKind) : Type where
  certificate : FirstBitLargeSupportColoringCertificate

/-- Public facade for the large-support first-bit coloring certificate. -/
abbrev FirstBitLargeSupportColoringPublicFacade : Type :=
  FirstBitLargeSupportColoringFacade FirstBitLargeSupportColoringFacadeKind.publicView

/-- Final-statement facade for the large-support first-bit coloring certificate. -/
abbrev FirstBitLargeSupportColoringFinalFacade : Type :=
  FirstBitLargeSupportColoringFacade FirstBitLargeSupportColoringFacadeKind.finalView

/-- Archive facade for the large-support first-bit coloring certificate. -/
abbrev FirstBitLargeSupportColoringArchiveFacade : Type :=
  FirstBitLargeSupportColoringFacade FirstBitLargeSupportColoringFacadeKind.archiveView

/-- Release facade for the large-support first-bit coloring certificate. -/
abbrev FirstBitLargeSupportColoringReleaseFacade : Type :=
  FirstBitLargeSupportColoringFacade FirstBitLargeSupportColoringFacadeKind.releaseView

/-- Retag the canonical certificate for a named facade. -/
def FirstBitLargeSupportColoringCertificate.asFacade
    (h : FirstBitLargeSupportColoringCertificate)
    (kind : FirstBitLargeSupportColoringFacadeKind) :
    FirstBitLargeSupportColoringFacade kind where
  certificate := h

/-- Retag the canonical certificate as the public facade. -/
def FirstBitLargeSupportColoringCertificate.asPublicFacade
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringPublicFacade :=
  h.asFacade FirstBitLargeSupportColoringFacadeKind.publicView

/-- Retag the canonical certificate as the final-statement facade. -/
def FirstBitLargeSupportColoringCertificate.asFinalFacade
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringFinalFacade :=
  h.asFacade FirstBitLargeSupportColoringFacadeKind.finalView

/-- Retag the canonical certificate as the archive facade. -/
def FirstBitLargeSupportColoringCertificate.asArchiveFacade
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringArchiveFacade :=
  h.asFacade FirstBitLargeSupportColoringFacadeKind.archiveView

/-- Retag the canonical certificate as the release facade. -/
def FirstBitLargeSupportColoringCertificate.asReleaseFacade
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringReleaseFacade :=
  h.asFacade FirstBitLargeSupportColoringFacadeKind.releaseView

/-- Forget a facade tag and recover the canonical certificate. -/
def FirstBitLargeSupportColoringFacade.toCertificate
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    FirstBitLargeSupportColoringCertificate :=
  h.certificate

/-- Expose the selector-assumption bundle from any facade tag. -/
def FirstBitLargeSupportColoringFacade.toCurrentSelectorAssumptions
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    FirstBitCurrentSelectorAssumptions :=
  h.certificate.toCurrentSelectorAssumptions

/-- Project the large-support loss-`32` selector from any facade tag. -/
def FirstBitLargeSupportColoringFacade.toLargeEvenDegreeModFourLoss32
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.certificate.toLargeEvenDegreeModFourLoss32

/-- Project the full loss-`32` selector from any facade tag. -/
def FirstBitLargeSupportColoringFacade.toEvenDegreeModFourLoss32
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.certificate.toEvenDegreeModFourLoss32

/-- Project the loss-`64` parity lift from any facade tag. -/
def FirstBitLargeSupportColoringFacade.toParityToModFourLoss64FixedWitnessLift
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.certificate.toParityToModFourLoss64FixedWitnessLift

@[simp] theorem FirstBitLargeSupportColoringCertificate.asFacade_certificate
    (h : FirstBitLargeSupportColoringCertificate)
    (kind : FirstBitLargeSupportColoringFacadeKind) :
    (h.asFacade kind).certificate = h := rfl

@[simp] theorem FirstBitLargeSupportColoringFacade.toCertificate_asFacade
    (h : FirstBitLargeSupportColoringCertificate)
    (kind : FirstBitLargeSupportColoringFacadeKind) :
    (h.asFacade kind).toCertificate = h := rfl

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

/--
The finite-Ramsey current-frontier package also supplies the external-block terminal certificate by
using the q=16/tail Ramsey fields to build the D=5 external-block bridge.
-/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toExternalBlockCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringExternalBlockCertificate where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := h.firstBit
  ramseyTenSmallTable := h.ramseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :=
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_five_of_cliqueOrIndepSetBound16_and_tail
      h.cliqueOrIndepSetBound16 h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- The current-frontier package closes the target through the external-block consumer surface. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierCertificate_viaExternalBlock
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringExternalBlockCertificate
    h.toExternalBlockCertificate

/--
Consumer-facing external-block bundle.  The first-bit input is presented through the release facade,
while projections below expose the current selector assumptions demanded by downstream handoff code.
-/
structure ProofMdLargeSupportColoringExternalBlockConsumerBundle : Type where
  sevenVertexBooleanCertificate :
    ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true
  firstBit : FirstBitLargeSupportColoringReleaseFacade
  ramseyTenSmallTable : RamseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge 5
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- Build the consumer-facing external-block bundle from the canonical certificate. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.ofExternalBlockCertificate
    (h : ProofMdLargeSupportColoringExternalBlockCertificate) :
    ProofMdLargeSupportColoringExternalBlockConsumerBundle where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := h.firstBit.asReleaseFacade
  ramseyTenSmallTable := h.ramseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitSelectors := h.higherBitSelectors

/-- Forget the consumer facade and recover the canonical external-block certificate. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.toExternalBlockCertificate
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    ProofMdLargeSupportColoringExternalBlockCertificate where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := h.firstBit.toCertificate
  ramseyTenSmallTable := h.ramseyTenSmallTable
  fixedWitnessExternalBlockSelfBridgeFive := h.fixedWitnessExternalBlockSelfBridgeFive
  higherBitSelectors := h.higherBitSelectors

/-- The selector assumptions exposed by the consumer-facing external-block bundle. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.firstBitSelectors
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.firstBit.toCurrentSelectorAssumptions

/-- Large-support loss-`32` first-bit selector exposed by the external-block consumer bundle. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.firstBitSelectors.largeEvenDegreeModFourLoss32

/-- Full loss-`32` first-bit selector exposed by the external-block consumer bundle. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.firstBitSelectors.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the external-block consumer bundle. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.firstBitSelectors.parityToModFourLoss64FixedWitnessLift

/-- The consumer-facing external-block bundle closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringExternalBlockConsumerBundle
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringExternalBlockCertificate
    h.toExternalBlockCertificate

/-- Build the external-block consumer bundle from the finite-Ramsey current-frontier certificate. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.ofCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringExternalBlockConsumerBundle :=
  ProofMdLargeSupportColoringExternalBlockConsumerBundle.ofExternalBlockCertificate
    h.toExternalBlockCertificate

/--
Consumer-facing current-frontier bundle.  It keeps the q=16 Ramsey field and the large-tail Ramsey
field visible while sharing the same release-facade first-bit selector projections.
-/
structure ProofMdLargeSupportColoringCurrentFrontierConsumerBundle : Type where
  sevenVertexBooleanCertificate :
    ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true
  firstBit : FirstBitLargeSupportColoringReleaseFacade
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- Build the current-frontier consumer bundle from the canonical current-frontier certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.ofCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringCurrentFrontierConsumerBundle where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := h.firstBit.asReleaseFacade
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- Forget the consumer facade and recover the canonical current-frontier certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    ProofMdLargeSupportColoringCurrentFrontierCertificate where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := h.firstBit.toCertificate
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- Convert the current-frontier consumer bundle to the external-block consumer surface. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toExternalBlockConsumerBundle
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    ProofMdLargeSupportColoringExternalBlockConsumerBundle :=
  ProofMdLargeSupportColoringExternalBlockConsumerBundle.ofCurrentFrontierCertificate
    h.toCurrentFrontierCertificate

/-- The selector assumptions exposed by the current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.firstBitSelectors
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.firstBit.toCurrentSelectorAssumptions

/-- Large-support loss-`32` first-bit selector exposed by the current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.firstBitSelectors.largeEvenDegreeModFourLoss32

/-- Full loss-`32` first-bit selector exposed by the current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.firstBitSelectors.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.firstBitSelectors.parityToModFourLoss64FixedWitnessLift

/-- The consumer-facing current-frontier bundle closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierConsumerBundle
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringCurrentFrontierCertificate
    h.toCurrentFrontierCertificate

/-- The current-frontier consumer bundle also closes the target through the external-block surface. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierConsumerBundle_viaExternalBlock
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringExternalBlockConsumerBundle
    h.toExternalBlockConsumerBundle

/--
Public/final/archive/release facade bundle for downstream first-bit consumers.  The fields are
deliberately redundant: consumers can keep their preferred facade tag while sharing the same current
selector assumptions and canonical large-support coloring certificate.
-/
structure FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle : Type where
  certificate : FirstBitLargeSupportColoringCertificate
  publicFacade : FirstBitLargeSupportColoringPublicFacade
  finalFacade : FirstBitLargeSupportColoringFinalFacade
  archiveFacade : FirstBitLargeSupportColoringArchiveFacade
  releaseFacade : FirstBitLargeSupportColoringReleaseFacade
  selectors : FirstBitCurrentSelectorAssumptions

/-- Build the public/final/archive/release facade bundle from the canonical certificate. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle where
  certificate := h
  publicFacade := h.asPublicFacade
  finalFacade := h.asFinalFacade
  archiveFacade := h.asArchiveFacade
  releaseFacade := h.asReleaseFacade
  selectors := h.toCurrentSelectorAssumptions

/-- Expose the public/final/archive/release facade bundle from the canonical certificate. -/
def FirstBitLargeSupportColoringCertificate.toPublicFinalArchiveReleaseBundle
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate h

/-- Forget a facade tag and recover the public/final/archive/release facade bundle. -/
def FirstBitLargeSupportColoringFacade.toPublicFinalArchiveReleaseBundle
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.toCertificate.toPublicFinalArchiveReleaseBundle

/-- Selector assumptions carried by the public/final/archive/release facade bundle. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toCurrentSelectorAssumptions
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectors

/-- Large-support loss-`32` selector carried by the facade bundle. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toLargeEvenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectors.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector carried by the facade bundle. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toEvenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectors.evenDegreeModFourLoss32

/-- Loss-`64` parity lift carried by the facade bundle. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toParityToModFourLoss64FixedWitnessLift
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.selectors.parityToModFourLoss64FixedWitnessLift

@[simp] theorem FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate_certificate
    (h : FirstBitLargeSupportColoringCertificate) :
    (FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate h).certificate = h :=
  rfl

@[simp] theorem FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate_releaseFacade
    (h : FirstBitLargeSupportColoringCertificate) :
    (FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate h).releaseFacade =
      h.asReleaseFacade :=
  rfl

@[simp] theorem FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate_selectors
    (h : FirstBitLargeSupportColoringCertificate) :
    (FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.ofCertificate h).selectors =
      h.toCurrentSelectorAssumptions :=
  rfl

/--
Checklist of the selector wrappers obtained from the large-support first-bit coloring input.  This is
a compact downstream surface for code that only needs the loss-`32` and loss-`64` consequences.
-/
structure FirstBitLargeSupportColoringWrapperChecklist : Prop where
  largeEvenDegreeModFourLoss32 : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  evenDegreeModFourLoss32 : HasEvenDegreeModFourLoss32InducedSubgraph
  parityToModFourLoss64FixedWitnessLift : HasParityToModFourLoss64FixedWitnessLift

/-- Build the wrapper checklist directly from a large-support bounded coloring theorem. -/
def FirstBitLargeSupportColoringWrapperChecklist.ofLargeEvenDegreeModFourCongruentDegreeColoringBound
    {C : ℕ} (hCpos : 0 < C) (hC : C ≤ 32)
    (hcolor : HasLargeEvenDegreeModFourCongruentDegreeColoringBound C) :
    FirstBitLargeSupportColoringWrapperChecklist where
  largeEvenDegreeModFourLoss32 :=
    hasLargeEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor
  evenDegreeModFourLoss32 :=
    hasEvenDegreeModFourLoss32InducedSubgraph_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor
  parityToModFourLoss64FixedWitnessLift :=
    hasParityToModFourLoss64FixedWitnessLift_of_largeEvenDegreeModFourCongruentDegreeColoringBound
      hCpos hC hcolor

/-- Build the wrapper checklist from the canonical large-support first-bit certificate. -/
def FirstBitLargeSupportColoringWrapperChecklist.ofCertificate
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringWrapperChecklist :=
  FirstBitLargeSupportColoringWrapperChecklist.ofLargeEvenDegreeModFourCongruentDegreeColoringBound
    h.colorCount_pos h.colorCount_le32 h.coloringBound

/-- Build the wrapper checklist from current selector assumptions. -/
def FirstBitCurrentSelectorAssumptions.toWrapperChecklist
    (h : FirstBitCurrentSelectorAssumptions) :
    FirstBitLargeSupportColoringWrapperChecklist where
  largeEvenDegreeModFourLoss32 := h.largeEvenDegreeModFourLoss32
  evenDegreeModFourLoss32 := h.evenDegreeModFourLoss32
  parityToModFourLoss64FixedWitnessLift := h.parityToModFourLoss64FixedWitnessLift

/-- Expose the wrapper checklist from the canonical large-support first-bit certificate. -/
def FirstBitLargeSupportColoringCertificate.toWrapperChecklist
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringWrapperChecklist :=
  FirstBitLargeSupportColoringWrapperChecklist.ofCertificate h

/-- Forget a facade tag and expose the wrapper checklist. -/
def FirstBitLargeSupportColoringFacade.toWrapperChecklist
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    FirstBitLargeSupportColoringWrapperChecklist :=
  h.toCertificate.toWrapperChecklist

/-- Expose the wrapper checklist from the public/final/archive/release facade bundle. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toWrapperChecklist
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    FirstBitLargeSupportColoringWrapperChecklist :=
  h.selectors.toWrapperChecklist

/--
External-block handoff facade pairing the consumer bundle with the public facade bundle, the
loss-wrapper checklist, and the target proof obtained from the packaged assumptions.
-/
structure ProofMdLargeSupportColoringExternalBlockHandoffFacade : Type where
  consumer : ProofMdLargeSupportColoringExternalBlockConsumerBundle
  firstBitBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  wrapperChecklist : FirstBitLargeSupportColoringWrapperChecklist
  targetStatement : TargetStatement

/-- Promote an external-block consumer bundle to the downstream handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.toHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade where
  consumer := h
  firstBitBundle := h.firstBit.toPublicFinalArchiveReleaseBundle
  wrapperChecklist := h.firstBit.toWrapperChecklist
  targetStatement := targetStatement_of_proofMdLargeSupportColoringExternalBlockConsumerBundle h

/-- Promote the canonical external-block certificate to the downstream handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockCertificate.toHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockCertificate) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  (ProofMdLargeSupportColoringExternalBlockConsumerBundle.ofExternalBlockCertificate h).toHandoffFacade

/-- Recover the canonical external-block certificate from the handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.toExternalBlockCertificate
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockCertificate :=
  h.consumer.toExternalBlockCertificate

/-- First-bit selector assumptions exposed by the external-block handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.firstBitSelectors
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    FirstBitCurrentSelectorAssumptions :=
  h.firstBitBundle.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by the external-block handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the external-block handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the external-block handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.wrapperChecklist.parityToModFourLoss64FixedWitnessLift

/-- The external-block handoff facade closes the target statement from its packaged assumptions. -/
theorem targetStatement_of_proofMdLargeSupportColoringExternalBlockHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    TargetStatement :=
  h.targetStatement

@[simp] theorem ProofMdLargeSupportColoringExternalBlockConsumerBundle.toHandoffFacade_consumer
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    h.toHandoffFacade.consumer = h :=
  rfl

/--
Current-frontier handoff facade.  It retains the current-frontier consumer bundle, the induced
external-block consumer facade, and the shared first-bit projection surfaces used by both routes.
-/
structure ProofMdLargeSupportColoringCurrentFrontierHandoffFacade : Type where
  consumer : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle
  currentFrontierCertificate : ProofMdLargeSupportColoringCurrentFrontierCertificate
  externalBlockConsumer : ProofMdLargeSupportColoringExternalBlockConsumerBundle
  externalBlockFacade : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  firstBitBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  wrapperChecklist : FirstBitLargeSupportColoringWrapperChecklist
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- Promote a current-frontier consumer bundle to the downstream handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    ProofMdLargeSupportColoringCurrentFrontierHandoffFacade where
  consumer := h
  currentFrontierCertificate := h.toCurrentFrontierCertificate
  externalBlockConsumer := h.toExternalBlockConsumerBundle
  externalBlockFacade :=
    ProofMdLargeSupportColoringExternalBlockConsumerBundle.toHandoffFacade
      h.toExternalBlockConsumerBundle
  firstBitBundle := h.firstBit.toPublicFinalArchiveReleaseBundle
  wrapperChecklist := h.firstBit.toWrapperChecklist
  targetStatement := targetStatement_of_proofMdLargeSupportColoringCurrentFrontierConsumerBundle h
  targetStatement_viaExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringCurrentFrontierConsumerBundle_viaExternalBlock h

/-- Promote the canonical current-frontier certificate to the downstream handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringCurrentFrontierHandoffFacade :=
  (ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.ofCurrentFrontierCertificate h).toHandoffFacade

/-- Recover the canonical current-frontier certificate from the handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringCurrentFrontierCertificate :=
  h.currentFrontierCertificate

/-- Recover the external-block consumer surface from the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toExternalBlockConsumerBundle
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockConsumerBundle :=
  h.externalBlockConsumer

/-- Recover the external-block handoff facade from the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toExternalBlockHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockFacade

/-- First-bit selector assumptions exposed by the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.firstBitSelectors
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    FirstBitCurrentSelectorAssumptions :=
  h.firstBitBundle.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.wrapperChecklist.parityToModFourLoss64FixedWitnessLift

/-- The current-frontier handoff facade closes the target statement from its packaged assumptions. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    TargetStatement :=
  h.targetStatement

/-- The current-frontier handoff facade also closes the target through the external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierHandoffFacade_viaExternalBlock
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

@[simp] theorem ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toHandoffFacade_consumer
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    h.toHandoffFacade.consumer = h :=
  rfl

/--
Current-selector endpoint for the large-support first-bit coloring input.  This packages the
canonical certificate together with the public/final/archive/release bundle and the selector checklist,
so downstream consumers can depend on one current endpoint rather than choosing a facade tag.
-/
structure FirstBitLargeSupportColoringCurrentSelectorEndpoint : Type where
  certificate : FirstBitLargeSupportColoringCertificate
  facadeBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  selectors : FirstBitCurrentSelectorAssumptions
  wrapperChecklist : FirstBitLargeSupportColoringWrapperChecklist

/-- Build the current-selector endpoint from the canonical large-support coloring certificate. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint where
  certificate := h
  facadeBundle := h.toPublicFinalArchiveReleaseBundle
  selectors := h.toCurrentSelectorAssumptions
  wrapperChecklist := h.toWrapperChecklist

/-- Build the current-selector endpoint from the public/final/archive/release bundle. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofBundle
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint where
  certificate := h.certificate
  facadeBundle := h
  selectors := h.selectors
  wrapperChecklist := h.toWrapperChecklist

/-- Recover the public/final/archive/release bundle from the current-selector endpoint. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.toPublicFinalArchiveReleaseBundle
    (h : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.facadeBundle

/-- Selector assumptions exposed by the current-selector endpoint. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.toCurrentSelectorAssumptions
    (h : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectors

/-- Large-support loss-`32` selector exposed by the current-selector endpoint. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.largeEvenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the current-selector endpoint. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.evenDegreeModFourLoss32
    (h : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.wrapperChecklist.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the current-selector endpoint. -/
def FirstBitLargeSupportColoringCurrentSelectorEndpoint.parityToModFourLoss64FixedWitnessLift
    (h : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.wrapperChecklist.parityToModFourLoss64FixedWitnessLift

/-- Expose a large-support certificate as the current-selector endpoint. -/
def FirstBitLargeSupportColoringCertificate.toCurrentSelectorEndpoint
    (h : FirstBitLargeSupportColoringCertificate) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate h

/-- Expose a tagged first-bit facade as the current-selector endpoint. -/
def FirstBitLargeSupportColoringFacade.toCurrentSelectorEndpoint
    {kind : FirstBitLargeSupportColoringFacadeKind}
    (h : FirstBitLargeSupportColoringFacade kind) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofBundle h.toPublicFinalArchiveReleaseBundle

/-- Expose a public/final/archive/release bundle as the current-selector endpoint. -/
def FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle.toCurrentSelectorEndpoint
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofBundle h

@[simp] theorem FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate_certificate
    (h : FirstBitLargeSupportColoringCertificate) :
    (FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate h).certificate = h :=
  rfl

@[simp] theorem FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate_selectors
    (h : FirstBitLargeSupportColoringCertificate) :
    (FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofCertificate h).selectors =
      h.toCurrentSelectorAssumptions :=
  rfl

@[simp] theorem FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofBundle_facadeBundle
    (h : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle) :
    (FirstBitLargeSupportColoringCurrentSelectorEndpoint.ofBundle h).facadeBundle = h :=
  rfl

/-- The external-block handoff facade exposed through the unified current-selector endpoint. -/
structure ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade : Type where
  handoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  targetStatement : TargetStatement

/-- The current-frontier handoff facade exposed through the unified current-selector endpoint. -/
structure ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade : Type where
  handoff : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade
  selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  externalBlockSelectorEndpointHandoff :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- The selector endpoint carried by an external-block handoff facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.firstBitBundle.toCurrentSelectorEndpoint

/-- The selector endpoint carried by a current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.firstBitBundle.toCurrentSelectorEndpoint

/-- Promote an external-block handoff facade to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringExternalBlockHandoffFacade.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade where
  handoff := h
  selectorEndpoint := h.toCurrentSelectorEndpoint
  targetStatement := h.targetStatement

/-- Promote an external-block consumer bundle to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringExternalBlockConsumerBundle.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockConsumerBundle) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.toHandoffFacade.toSelectorEndpointHandoffFacade

/-- Promote an external-block certificate to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringExternalBlockCertificate.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockCertificate) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.toHandoffFacade.toSelectorEndpointHandoffFacade

/-- Promote a current-frontier handoff facade to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade where
  handoff := h
  selectorEndpoint := h.toCurrentSelectorEndpoint
  externalBlockSelectorEndpointHandoff :=
    h.toExternalBlockHandoffFacade.toSelectorEndpointHandoffFacade
  targetStatement := h.targetStatement
  targetStatement_viaExternalBlock := h.targetStatement_viaExternalBlock

/-- Promote a current-frontier consumer bundle to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade :=
  h.toHandoffFacade.toSelectorEndpointHandoffFacade

/-- Promote a current-frontier certificate to the selector-endpoint facade. -/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade :=
  h.toHandoffFacade.toSelectorEndpointHandoffFacade

/-- Recover the external-block handoff facade from its selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.toExternalBlockHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.handoff

/-- Recover the current selector endpoint from the external-block selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.selectorEndpoint

/-- Selector assumptions exposed by the external-block selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.firstBitSelectors
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectorEndpoint.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by the external-block selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the external-block selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the external-block selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.selectorEndpoint.parityToModFourLoss64FixedWitnessLift

/-- The external-block selector-endpoint wrapper closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade) :
    TargetStatement :=
  h.targetStatement

/-- Recover the current-frontier handoff facade from its selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    ProofMdLargeSupportColoringCurrentFrontierHandoffFacade :=
  h.handoff

/-- Recover the external-block selector-endpoint wrapper from the current-frontier wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toExternalBlockSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.externalBlockSelectorEndpointHandoff

/-- Recover the external-block handoff facade from the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toExternalBlockHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockSelectorEndpointHandoff.toExternalBlockHandoffFacade

/-- Recover the current selector endpoint from the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.selectorEndpoint

/-- Selector assumptions exposed by the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.firstBitSelectors
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectorEndpoint.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.largeEvenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.evenDegreeModFourLoss32
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the current-frontier selector-endpoint wrapper. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.parityToModFourLoss64FixedWitnessLift
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.selectorEndpoint.parityToModFourLoss64FixedWitnessLift

/-- The current-frontier selector-endpoint wrapper closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    TargetStatement :=
  h.targetStatement

/-- The current-frontier selector-endpoint wrapper also closes the target through external blocks. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade_viaExternalBlock
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

/--
No-leftover assumption packet used by current-frontier selector consumers.  It mirrors the public
strict-cross/no-leftover split while staying independent of the heavier certified handoff imports.
-/
structure ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  strictCrossAtomDefect : terminalStrictCrossAtomDefect
  noLeftoverFourFourAtomDeletionDichotomy :
    terminalNoLeftoverFourFourAtomDeletionDichotomy
  noLeftoverUnitStrictAbsorptionOrLiftCollision :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- Project strict cross-atom defect control from the no-leftover packet. -/
def ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.strictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy. -/
def ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.noLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverUnitStrictAbsorptionOrLiftCollision

/--
Current-frontier selector handoff with the terminal no-leftover packet attached.  The target statement
continues to come from the current-frontier facade; the extra fields are for downstream deletion
consumers that want the no-leftover obligations adjacent to the first-bit selector endpoint.
-/
structure ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  selectorHandoff : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade
  noLeftoverAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- Attach no-leftover assumptions to a current-frontier selector-endpoint handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  selectorHandoff := h
  noLeftoverAssumptions := noLeftoverAssumptions
  targetStatement := h.targetStatement
  targetStatement_viaExternalBlock := h.targetStatement_viaExternalBlock

/-- Attach no-leftover assumptions directly to a current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toNoLeftoverSelectorHandoffFacade noLeftoverAssumptions

/-- Attach no-leftover assumptions directly to a current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toNoLeftoverSelectorHandoffFacade noLeftoverAssumptions

/-- Attach no-leftover assumptions directly to a current-frontier certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toNoLeftoverSelectorHandoffFacade noLeftoverAssumptions

/-- Recover the selector-endpoint current-frontier handoff from a no-leftover handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toCurrentFrontierSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade :=
  h.selectorHandoff

/-- Recover the current selector endpoint from a no-leftover handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.selectorHandoff.toCurrentSelectorEndpoint

/-- Recover the external-block selector wrapper from a no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toExternalBlockSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.selectorHandoff.toExternalBlockSelectorEndpointHandoffFacade

/-- Selector assumptions exposed by the no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectorHandoff.firstBitSelectors

/-- Large-support loss-`32` selector exposed by the no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.largeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorHandoff.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.evenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorHandoff.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.parityToModFourLoss64FixedWitnessLift
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.selectorHandoff.parityToModFourLoss64FixedWitnessLift

/-- Project strict cross-atom defect control from the no-leftover current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.noLeftoverAssumptions.toTerminalStrictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy from the current-frontier handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.noLeftoverAssumptions.toNoLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverAssumptions.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The no-leftover current-frontier handoff closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement

/-- The no-leftover current-frontier handoff also closes the target through external blocks. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade_viaExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

/--
Current-frontier assumptions needed after the current selector endpoint has supplied the first-bit
large-support package.  This separates the non-first-bit frontier obligations from the endpoint
itself so final consumers can pass a small packet plus a public-release selector facade.
-/
structure ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket : Type where
  sevenVertexBooleanCertificate :
    ∀ x : SevenVertexEdgeCode, sevenVertexCodeHasRegularFourOrFiveBool x = true
  ramseyTenSmallTable : RamseyTenSmallTable
  cliqueOrIndepSetBound16 : HasCliqueOrIndepSetBound 16 16 8388607
  cliqueOrIndepSetBoundTail :
    ∀ {j : ℕ}, 5 ≤ j →
      ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
        2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j
  higherBitSelectors : HigherBitSmallModulusAffineSelectorsFromEleven

/-- Extract the current-frontier assumption packet from the canonical certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- Extract the current-frontier assumption packet from the consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierConsumerBundle
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- Extract the current-frontier assumption packet from a current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierCertificate
    h.toCurrentFrontierCertificate

/-- Extract the current-frontier assumption packet from a selector-endpoint handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierSelectorEndpointHandoffFacade
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierHandoffFacade
    h.toCurrentFrontierHandoffFacade

/-- Extract the current-frontier assumption packet from the no-leftover selector handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierSelectorEndpointHandoffFacade
    h.toCurrentFrontierSelectorEndpointHandoffFacade

/-- Combine a current-selector endpoint with the frontier packet to recover the canonical certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.toCurrentFrontierCertificate
    (h : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    ProofMdLargeSupportColoringCurrentFrontierCertificate where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := selectorEndpoint.certificate
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- Combine a current-selector endpoint with the frontier packet to recover the consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.toCurrentFrontierConsumerBundle
    (h : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    ProofMdLargeSupportColoringCurrentFrontierConsumerBundle where
  sevenVertexBooleanCertificate := h.sevenVertexBooleanCertificate
  firstBit := selectorEndpoint.facadeBundle.releaseFacade
  ramseyTenSmallTable := h.ramseyTenSmallTable
  cliqueOrIndepSetBound16 := h.cliqueOrIndepSetBound16
  cliqueOrIndepSetBoundTail := h.cliqueOrIndepSetBoundTail
  higherBitSelectors := h.higherBitSelectors

/-- The frontier packet plus the current-selector endpoint close the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierAssumptionPacket_and_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringCurrentFrontierCertificate
    (h.toCurrentFrontierCertificate selectorEndpoint)

/-- The frontier packet plus the current-selector endpoint close the target through external blocks. -/
theorem targetStatement_of_proofMdLargeSupportColoringCurrentFrontierAssumptionPacket_and_currentSelectorEndpoint_viaExternalBlock
    (h : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringCurrentFrontierCertificate_viaExternalBlock
    (h.toCurrentFrontierCertificate selectorEndpoint)

/--
Public-release final consumer facade.  It is the final small handoff surface for downstream code that
wants the current selector endpoint, the external-block route, the current-frontier/no-leftover packets,
and both target wrappers packaged together.
-/
structure ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  publicReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  currentFrontierAssumptions : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  noLeftoverAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentFrontierSelectorHandoff :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade
  externalBlockSelectorHandoff :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade
  noLeftoverSelectorHandoff :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- Build the public-release final consumer facade from the no-leftover selector handoff. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.ofNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  selectorEndpoint := h.toCurrentSelectorEndpoint
  publicReleaseBundle := h.toCurrentSelectorEndpoint.toPublicFinalArchiveReleaseBundle
  currentFrontierAssumptions :=
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket.ofCurrentFrontierNoLeftoverSelectorHandoffFacade h
  noLeftoverAssumptions := h.noLeftoverAssumptions
  currentFrontierSelectorHandoff := h.toCurrentFrontierSelectorEndpointHandoffFacade
  externalBlockSelectorHandoff := h.toExternalBlockSelectorEndpointHandoffFacade
  noLeftoverSelectorHandoff := h
  targetStatement := h.targetStatement
  targetStatement_viaExternalBlock := h.targetStatement_viaExternalBlock

/-- Attach no-leftover assumptions and expose a selector-endpoint handoff as the final consumer facade. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.ofNoLeftoverSelectorHandoffFacade
    (h.toNoLeftoverSelectorHandoffFacade noLeftoverAssumptions)

/-- Attach no-leftover assumptions and expose a current-frontier handoff as the final consumer facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseFinalConsumerFacade noLeftoverAssumptions

/-- Attach no-leftover assumptions and expose a consumer bundle as the final consumer facade. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseFinalConsumerFacade noLeftoverAssumptions

/-- Attach no-leftover assumptions and expose a certificate as the final consumer facade. -/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseFinalConsumerFacade noLeftoverAssumptions

/-- Recover the current selector endpoint from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.selectorEndpoint

/-- Recover the public/final/archive/release bundle from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicReleaseBundle

/-- Recover the current-frontier assumption packet from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.currentFrontierAssumptions

/-- Recover the no-leftover assumption packet from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverAssumptions

/-- Recover the current-frontier selector handoff from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toCurrentFrontierSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade :=
  h.currentFrontierSelectorHandoff

/-- Recover the external-block selector handoff from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toExternalBlockSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.externalBlockSelectorHandoff

/-- Recover the external-block handoff facade from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockSelectorHandoff.toExternalBlockHandoffFacade

/-- Recover the no-leftover selector handoff from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverSelectorHandoff

/-- Selector assumptions exposed by the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.selectorEndpoint.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.largeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.largeEvenDegreeModFourLoss32

/-- Full loss-`32` selector exposed by the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.evenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.selectorEndpoint.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.parityToModFourLoss64FixedWitnessLift
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.selectorEndpoint.parityToModFourLoss64FixedWitnessLift

/-- Project strict cross-atom defect control from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.noLeftoverAssumptions.toTerminalStrictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.noLeftoverAssumptions.toNoLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverAssumptions.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The final consumer facade closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement

/-- The final consumer facade also closes the target through external blocks. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseFinalConsumerFacade_viaExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

/-- Promote a no-leftover selector handoff directly to the public-release final consumer facade. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.ofNoLeftoverSelectorHandoffFacade h

/--
Combined no-leftover/current-frontier packet cited by public-release consumers.  It keeps the
non-first-bit frontier assumptions adjacent to the terminal no-leftover deletion assumptions without
rebuilding any of the selector or handoff facades.
-/
structure ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  currentFrontierAssumptions : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  noLeftoverAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- Extract the no-leftover/current-frontier packet from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  currentFrontierAssumptions := h.toCurrentFrontierAssumptionPacket
  noLeftoverAssumptions := h.toNoLeftoverDeletionAssumptionPacket

/-- Expose the no-leftover/current-frontier packet from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade h

/-- Extract the no-leftover/current-frontier packet from the no-leftover selector handoff. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicReleaseFinalConsumerFacade.toNoLeftoverCurrentFrontierPacket

/-- Recover the current-frontier assumption packet from the no-leftover/current-frontier packet. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.currentFrontierAssumptions

/-- Recover the no-leftover deletion packet from the no-leftover/current-frontier packet. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverAssumptions

/-- Project strict cross-atom defect control from the no-leftover/current-frontier packet. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.noLeftoverAssumptions.toTerminalStrictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy from the combined packet. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.noLeftoverAssumptions.toNoLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverAssumptions.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- A combined no-leftover/current-frontier packet plus the current selector endpoint closes the target. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringCurrentFrontierAssumptionPacket_and_currentSelectorEndpoint
    h.currentFrontierAssumptions selectorEndpoint

/-- The combined packet plus the current selector endpoint also closes the external-block target route. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint_viaExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringCurrentFrontierAssumptionPacket_and_currentSelectorEndpoint_viaExternalBlock
    h.currentFrontierAssumptions selectorEndpoint

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade_currentFrontierAssumptions
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade h).currentFrontierAssumptions =
      h.toCurrentFrontierAssumptionPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade_noLeftoverAssumptions
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket.ofFinalConsumerFacade h).noLeftoverAssumptions =
      h.toNoLeftoverDeletionAssumptionPacket :=
  rfl

/--
Public-release/current-frontier citation bundle.  This is a non-duplicative citation layer: it keeps
the final consumer facade as the source of truth while naming the selector endpoint, handoff wrappers,
large-support selector, combined no-leftover/current-frontier packet, and final target wrappers that
downstream files are expected to consume.
-/
structure ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  largeSupportSelector : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  currentFrontierSelectorHandoff :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade
  externalBlockSelectorHandoff :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  noLeftoverSelectorHandoff :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- Build the public-release/current-frontier citation bundle from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  finalConsumerFacade := h
  publicReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  largeSupportSelector := h.largeEvenDegreeModFourLoss32
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  currentFrontierSelectorHandoff := h.toCurrentFrontierSelectorEndpointHandoffFacade
  externalBlockSelectorHandoff := h.toExternalBlockSelectorEndpointHandoffFacade
  externalBlockHandoff := h.toExternalBlockHandoffFacade
  noLeftoverSelectorHandoff := h.toNoLeftoverSelectorHandoffFacade
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  targetStatement := h.targetStatement
  targetStatement_viaExternalBlock := h.targetStatement_viaExternalBlock

/-- Expose the public-release/current-frontier citation bundle from the final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade h

/-- Build the citation bundle from a no-leftover selector handoff. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicReleaseFinalConsumerFacade.toPublicReleaseCurrentFrontierCitationBundle

/-- Attach no-leftover assumptions and cite a selector-endpoint handoff as the current frontier. -/
def ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  (h.toPublicReleaseFinalConsumerFacade noLeftoverAssumptions).toPublicReleaseCurrentFrontierCitationBundle

/-- Attach no-leftover assumptions and cite a current-frontier handoff facade. -/
def ProofMdLargeSupportColoringCurrentFrontierHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierHandoffFacade)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle noLeftoverAssumptions

/-- Attach no-leftover assumptions and cite a current-frontier consumer bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierConsumerBundle.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierConsumerBundle)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle noLeftoverAssumptions

/-- Attach no-leftover assumptions and cite a current-frontier certificate. -/
def ProofMdLargeSupportColoringCurrentFrontierCertificate.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierCertificate)
    (noLeftoverAssumptions :
      ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toSelectorEndpointHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle noLeftoverAssumptions

/-- Expose a no-leftover selector handoff as the public-release/current-frontier citation bundle. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofNoLeftoverSelectorHandoffFacade h

/-- Recover the final consumer facade from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalConsumerFacade

/-- Recover the public/final/archive/release bundle from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicReleaseBundle

/-- Recover the large-support loss-`32` selector from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toLargeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.largeSupportSelector

/-- Recover the current selector endpoint from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the current-frontier selector handoff from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toCurrentFrontierSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierSelectorEndpointHandoffFacade :=
  h.currentFrontierSelectorHandoff

/-- Recover the external-block selector handoff from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toExternalBlockSelectorEndpointHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockSelectorEndpointHandoffFacade :=
  h.externalBlockSelectorHandoff

/-- Recover the external-block handoff facade from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- Recover the no-leftover selector handoff from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toNoLeftoverSelectorHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverSelectorHandoff

/-- Recover the combined no-leftover/current-frontier packet from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the current-frontier assumption packet from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.noLeftoverCurrentFrontierPacket.toCurrentFrontierAssumptionPacket

/-- Recover the no-leftover deletion packet from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket.toNoLeftoverDeletionAssumptionPacket

/-- Selector assumptions exposed by the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorEndpoint.toCurrentSelectorAssumptions

/-- Full loss-`32` selector exposed by the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.evenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasEvenDegreeModFourLoss32InducedSubgraph :=
  h.currentSelectorEndpoint.evenDegreeModFourLoss32

/-- Loss-`64` parity lift exposed by the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.parityToModFourLoss64FixedWitnessLift
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasParityToModFourLoss64FixedWitnessLift :=
  h.currentSelectorEndpoint.parityToModFourLoss64FixedWitnessLift

/-- Project strict cross-atom defect control from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.toNoLeftoverDeletionAssumptionPacket.toTerminalStrictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy from the citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.toNoLeftoverDeletionAssumptionPacket.toNoLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toNoLeftoverDeletionAssumptionPacket.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The public-release/current-frontier citation bundle closes the target statement. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement

/-- The citation bundle also closes the target through the external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

/-- The final consumer facade closes the target through the current-frontier citation bundle. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseFinalConsumerFacade_viaCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
    h.toPublicReleaseCurrentFrontierCitationBundle

/-- The final consumer facade closes the external-block target through the citation bundle. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseFinalConsumerFacade_viaCurrentFrontierCitationBundle_externalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaExternalBlock
    h.toPublicReleaseCurrentFrontierCitationBundle

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade_finalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade h).finalConsumerFacade = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade h).currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade h).externalBlockHandoff =
      h.toExternalBlockHandoffFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.ofFinalConsumerFacade h).noLeftoverCurrentFrontierPacket =
      h.toNoLeftoverCurrentFrontierPacket :=
  rfl

/--
Final-public target obligations for downstream consumers.  The current public-release citation
bundle remains the source of truth; this packet only names the selector endpoint,
no-leftover/current-frontier packet, external-block handoff, final facade, and the target wrappers
that consumers should discharge or reuse.
-/
structure ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  citationBundle :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  targetStatement_fromCitationBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentSelector : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromCitationBundle_viaExternalBlock : TargetStatement
  targetStatement_fromNoLeftoverCurrentSelector_viaExternalBlock : TargetStatement

/-- Build the final-public obligation packet by reusing the current public-release citation bundle. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  citationBundle := h
  finalConsumerFacade := h.finalConsumerFacade
  currentSelectorEndpoint := h.currentSelectorEndpoint
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  externalBlockHandoff := h.externalBlockHandoff
  targetStatement_fromCitationBundle := h.targetStatement
  targetStatement_fromNoLeftoverCurrentSelector :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint
      h.noLeftoverCurrentFrontierPacket h.currentSelectorEndpoint
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringExternalBlockHandoffFacade h.externalBlockHandoff
  targetStatement_fromCitationBundle_viaExternalBlock := h.targetStatement_viaExternalBlock
  targetStatement_fromNoLeftoverCurrentSelector_viaExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint_viaExternalBlock
      h.noLeftoverCurrentFrontierPacket h.currentSelectorEndpoint

/-- Expose the final-public obligation packet from the public-release/current-frontier citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle h

/-- Expose the final-public obligation packet from the public-release final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicReleaseCurrentFrontierCitationBundle.toFinalPublicTargetObligationPacket

/-- Recover the public-release/current-frontier citation bundle from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.citationBundle

/-- Recover the public-release final consumer facade from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalConsumerFacade

/-- Recover the current selector endpoint from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the combined no-leftover/current-frontier packet from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the external-block handoff from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- Recover the public/final/archive/release bundle from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.citationBundle.publicReleaseBundle

/-- Recover the current-frontier assumption packet from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.noLeftoverCurrentFrontierPacket.toCurrentFrontierAssumptionPacket

/-- Recover the no-leftover deletion packet from final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket.toNoLeftoverDeletionAssumptionPacket

/-- Selector assumptions exposed by final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorEndpoint.toCurrentSelectorAssumptions

/-- Large-support loss-`32` selector exposed by final-public obligations. -/
def ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.largeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.currentSelectorEndpoint.largeEvenDegreeModFourLoss32

/-- The citation-bundle target wrapper exposed by final-public obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCitationBundle

/-- The no-leftover/current-selector target wrapper exposed by final-public obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaNoLeftoverCurrentSelector
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentSelector

/-- The external-block handoff target wrapper exposed by final-public obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaExternalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- The external-block citation target wrapper exposed by final-public obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaCitationExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCitationBundle_viaExternalBlock

/-- The no-leftover/current-selector external-block target wrapper exposed by final-public obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaNoLeftoverCurrentSelectorExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentSelector_viaExternalBlock

@[simp] theorem ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle_citationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle h).citationBundle =
      h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle h).currentSelectorEndpoint =
      h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle h).noLeftoverCurrentFrontierPacket =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicTargetObligationPacket.ofCurrentFrontierCitationBundle h).externalBlockHandoff =
      h.externalBlockHandoff :=
  rfl

/--
Final-public checkpoint facade for downstream consumers.  It pins the final target obligations next
to the public-release citation bundle so later files can cite one checkpoint while still projecting
the current selector endpoint, no-leftover/current-frontier packet, and external-block handoff.
-/
structure ProofMdLargeSupportColoringFinalPublicCheckpointFacade
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  targetObligations :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  citationBundle :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  targetStatement : TargetStatement
  targetStatement_viaExternalBlock : TargetStatement

/-- Build the final-public checkpoint from a final-public obligation packet. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  targetObligations := h
  citationBundle := h.citationBundle
  finalConsumerFacade := h.finalConsumerFacade
  publicReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint := h.currentSelectorEndpoint
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  externalBlockHandoff := h.externalBlockHandoff
  targetStatement := h.targetStatement_fromCitationBundle
  targetStatement_viaExternalBlock := h.targetStatement_fromCitationBundle_viaExternalBlock

/-- Build the final-public checkpoint directly from the current public-release citation bundle. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofFinalPublicTargetObligationPacket
    h.toFinalPublicTargetObligationPacket

/-- Expose the final-public checkpoint from the current public-release citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle h

/-- Expose the final-public checkpoint from the public-release final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicReleaseCurrentFrontierCitationBundle.toFinalPublicCheckpointFacade

/-- Expose the final-public checkpoint from a no-leftover selector handoff. -/
def ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringCurrentFrontierNoLeftoverSelectorHandoffFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicReleaseCurrentFrontierCitationBundle.toFinalPublicCheckpointFacade

/-- Recover the final target obligations from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.targetObligations

/-- Recover the public-release/current-frontier citation bundle from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.citationBundle

/-- Recover the current selector endpoint from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the external-block handoff from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- The final-public checkpoint closes the final target. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement

/-- The final-public checkpoint closes the final target through the external-block handoff route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade_viaExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_viaExternalBlock

/-- The current citation bundle closes the target through the final-public checkpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicCheckpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade
    h.toFinalPublicCheckpointFacade

/-- The current citation bundle closes the external-block target through the final-public checkpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicCheckpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade_viaExternalBlock
    h.toFinalPublicCheckpointFacade

@[simp] theorem ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle_citationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle h).citationBundle =
      h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle h).currentSelectorEndpoint =
      h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle h).noLeftoverCurrentFrontierPacket =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicCheckpointFacade.ofCurrentFrontierCitationBundle h).externalBlockHandoff =
      h.externalBlockHandoff :=
  rfl

/--
Final-public downstream target-obligation layer.  This consumes the final-public checkpoint and
names the exact selector/current-frontier obligations that downstream consumers need: the current
selector endpoint, the no-leftover/current-frontier packet, the external-block handoff, and the
target wrappers obtained by reusing the checkpoint and public citation bundle.
-/
structure ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  downstreamCheckpoint :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamTargetObligations :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamCitationBundle :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamFinalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamPublicReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  endpointForCurrentSelector : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  packetForNoLeftoverCurrentFrontier :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  packetForCurrentFrontier :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  packetForNoLeftoverDeletion :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  handoffForExternalBlock : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  targetStatement_fromCheckpoint : TargetStatement
  targetStatement_fromCheckpointExternalBlock : TargetStatement
  targetStatement_fromFinalTargetWrapper : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint_viaExternalBlock : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement

/-- Build the downstream target-obligation layer from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  downstreamCheckpoint := h
  downstreamTargetObligations := h.toFinalPublicTargetObligationPacket
  downstreamCitationBundle := h.toPublicReleaseCurrentFrontierCitationBundle
  downstreamFinalConsumerFacade := h.finalConsumerFacade
  downstreamPublicReleaseBundle := h.publicReleaseBundle
  endpointForCurrentSelector := h.currentSelectorEndpoint
  packetForNoLeftoverCurrentFrontier := h.noLeftoverCurrentFrontierPacket
  packetForCurrentFrontier :=
    h.noLeftoverCurrentFrontierPacket.toCurrentFrontierAssumptionPacket
  packetForNoLeftoverDeletion :=
    h.noLeftoverCurrentFrontierPacket.toNoLeftoverDeletionAssumptionPacket
  handoffForExternalBlock := h.externalBlockHandoff
  targetStatement_fromCheckpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade h
  targetStatement_fromCheckpointExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade_viaExternalBlock h
  targetStatement_fromFinalTargetWrapper :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket
      h.targetObligations
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaNoLeftoverCurrentSelector
      h.targetObligations
  targetStatement_fromCurrentSelectorEndpoint_viaExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaNoLeftoverCurrentSelectorExternalBlock
      h.targetObligations
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket_viaExternalBlockHandoff
      h.targetObligations

/-- Expose the downstream target-obligation layer from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade h

/-- Build the downstream target-obligation layer directly from the public citation bundle. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalPublicCheckpointFacade.toDownstreamTargetObligationLayer

/-- Expose the downstream target-obligation layer from the public citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofCurrentFrontierCitationBundle h

/-- Expose the downstream target-obligation layer from the public-release final consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalPublicCheckpointFacade.toDownstreamTargetObligationLayer

/-- Recover the final-public checkpoint from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamCheckpoint

/-- Recover the final target-obligation packet from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamTargetObligations

/-- Recover the public citation bundle from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamCitationBundle

/-- Recover the public-release final consumer facade from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamFinalConsumerFacade

/-- Recover the public/final/archive/release bundle from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.downstreamPublicReleaseBundle

/-- Recover the current selector endpoint from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.endpointForCurrentSelector

/-- Recover the no-leftover/current-frontier packet from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.packetForNoLeftoverCurrentFrontier

/-- Recover the external-block handoff from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.handoffForExternalBlock

/-- Recover the current-frontier assumption packet from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.packetForCurrentFrontier

/-- Recover the no-leftover deletion packet from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.packetForNoLeftoverDeletion

/-- Selector assumptions exposed by the downstream target-obligation layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.endpointForCurrentSelector.toCurrentSelectorAssumptions

/-- Project strict cross-atom defect control from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.packetForNoLeftoverDeletion.toTerminalStrictCrossAtomDefect

/-- Project the no-leftover four-four-atom deletion dichotomy from the downstream layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.packetForNoLeftoverDeletion.toNoLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.packetForNoLeftoverDeletion.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The downstream layer closes the final target by checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCheckpoint

/-- The downstream layer closes the final target through the final target wrapper. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaFinalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalTargetWrapper

/-- The downstream layer closes the final target through the current selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- The downstream layer closes the external-block target through the current selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCurrentSelectorEndpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint_viaExternalBlock

/-- The downstream layer closes the final target through the external-block handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaExternalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- The downstream layer closes the final target through the checkpoint external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCheckpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCheckpointExternalBlock

/-- The final-public checkpoint closes the target through the downstream target-obligation layer. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicCheckpointFacade_viaDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
    h.toDownstreamTargetObligationLayer

/-- The public citation bundle closes the target through the downstream target-obligation layer. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
    h.toFinalPublicDownstreamTargetObligationLayer

/-- The public citation bundle closes the current-selector external-block target through the downstream layer. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicDownstreamTargetObligationLayerCurrentSelectorExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCurrentSelectorEndpointExternalBlock
    h.toFinalPublicDownstreamTargetObligationLayer

@[simp] theorem ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade_downstreamCheckpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade h).downstreamCheckpoint =
      h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade_endpointForCurrentSelector
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade h).endpointForCurrentSelector =
      h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade_packetForNoLeftoverCurrentFrontier
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade h).packetForNoLeftoverCurrentFrontier =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade_handoffForExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.ofFinalPublicCheckpointFacade h).handoffForExternalBlock =
      h.externalBlockHandoff :=
  rfl

/--
Final-release/downstream-consumer endpoint bundle for the current proof frontier.  This is the
public endpoint beyond the downstream target-obligation layer: it keeps the layer itself, the
checkpoint/citation reuse handles, the final target wrapper, the current selector endpoint, the
no-leftover/current-frontier packet, and the external-block handoff in one structural packet.
-/
structure ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  downstreamLayer :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentProofFrontierCheckpoint :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalTargetWrapper :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentFrontierAssumptions :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  downstreamSelectors : FirstBitCurrentSelectorAssumptions
  terminalStrictCrossAtomDefect_obligation : terminalStrictCrossAtomDefect
  terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation :
    terminalNoLeftoverFourFourAtomDeletionDichotomy
  terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement_fromDownstreamCheckpoint : TargetStatement
  targetStatement_fromFinalTargetWrapper : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromPublicCitationCheckpointExternalBlock : TargetStatement

/-- Package the downstream final-public obligation layer as the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  downstreamLayer := h
  currentProofFrontierCheckpoint := h.toFinalPublicCheckpointFacade
  publicCitationReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  finalTargetWrapper := h.toFinalPublicTargetObligationPacket
  finalConsumerFacade := h.toPublicReleaseFinalConsumerFacade
  publicReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  currentFrontierAssumptions := h.toCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions := h.toNoLeftoverDeletionAssumptionPacket
  externalBlockHandoff := h.toExternalBlockHandoffFacade
  downstreamSelectors := h.firstBitSelectors
  terminalStrictCrossAtomDefect_obligation := h.toTerminalStrictCrossAtomDefect
  terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation :=
    h.toNoLeftoverFourFourAtomDeletionDichotomy
  terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation :=
    h.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement_fromDownstreamCheckpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer h
  targetStatement_fromFinalTargetWrapper :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaFinalTargetWrapper h
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCurrentSelectorEndpoint h
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaCurrentSelectorEndpoint h
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaExternalBlockHandoff h
  targetStatement_fromPublicCitationCheckpointReuse :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicCheckpoint
      h.downstreamCitationBundle
  targetStatement_fromPublicCitationCheckpointExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalPublicCheckpointExternalBlock
      h.downstreamCitationBundle

/-- Expose the final-release endpoint bundle from the downstream target-obligation layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h

/-- Build the final-release endpoint bundle from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toDownstreamTargetObligationLayer.toFinalReleaseDownstreamConsumerEndpointBundle

/-- Build the final-release endpoint bundle from the public citation bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalPublicDownstreamTargetObligationLayer.toFinalReleaseDownstreamConsumerEndpointBundle

/-- Build the final-release endpoint bundle from the final-consumer public facade. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalPublicDownstreamTargetObligationLayer.toFinalReleaseDownstreamConsumerEndpointBundle

/-- Expose the final-release endpoint bundle from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicCheckpointFacade h

/-- Expose the final-release endpoint bundle from the public citation bundle. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofCurrentFrontierCitationBundle h

/-- Expose the final-release endpoint bundle from the public final-consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofPublicReleaseFinalConsumerFacade h

/-- Recover the downstream target-obligation layer from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamLayer

/-- Recover the final-public checkpoint reused by the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.currentProofFrontierCheckpoint

/-- Recover the public citation bundle reused by the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicCitationReuse

/-- Recover the final target wrapper from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalTargetWrapper

/-- Recover the public final-consumer facade from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalConsumerFacade

/-- Recover the public final/archive/release bundle from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicReleaseBundle

/-- Recover the current-selector endpoint from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the external-block handoff from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- Recover the current-frontier assumptions from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.currentFrontierAssumptions

/-- Recover the no-leftover deletion assumptions from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverDeletionAssumptions

/-- Selector assumptions exposed by the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.downstreamSelectors

/-- Large-support loss-`32` selector exposed by the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.largeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.currentSelectorEndpoint.largeEvenDegreeModFourLoss32

/-- Project strict cross-atom defect control from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.terminalStrictCrossAtomDefect_obligation

/-- Project the no-leftover four-four-atom deletion dichotomy from the endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence from the endpoint. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation

/-- The final-release endpoint closes the target through downstream checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromDownstreamCheckpoint

/-- The final-release endpoint closes the target through the final target wrapper. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaFinalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalTargetWrapper

/-- The final-release endpoint closes the target through the current-selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- The final-release endpoint closes the target through the no-leftover/current-frontier packet. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- The final-release endpoint closes the target through the external-block handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaExternalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- The final-release endpoint closes the target through public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaPublicCitationCheckpointReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- The final-release endpoint closes the external-block route via public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaPublicCitationCheckpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointExternalBlock

/-- The downstream layer closes the target after packaging into the final-release endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer_viaFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
    h.toFinalReleaseDownstreamConsumerEndpointBundle

/-- The public citation bundle closes the target after packaging into the final-release endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
    h.toFinalReleaseDownstreamConsumerEndpointBundle

/-- The public citation bundle closes the public citation/checkpoint route through the final endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle_viaFinalReleaseDownstreamConsumerEndpointBundlePublicCitationCheckpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaPublicCitationCheckpointReuse
    h.toFinalReleaseDownstreamConsumerEndpointBundle

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_downstreamLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).downstreamLayer =
      h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_currentProofFrontierCheckpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).currentProofFrontierCheckpoint =
      h.toFinalPublicCheckpointFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_publicCitationReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).publicCitationReuse =
      h.toPublicReleaseCurrentFrontierCitationBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_finalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).finalTargetWrapper =
      h.toFinalPublicTargetObligationPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).noLeftoverCurrentFrontierPacket =
      h.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.ofFinalPublicDownstreamTargetObligationLayer h).externalBlockHandoff =
      h.toExternalBlockHandoffFacade :=
  rfl

/--
Public/final current-frontier endpoint wrapper for proof-md consumers.  This non-duplicative
facade keeps the final-release downstream endpoint as the source of truth while spelling out the
selector endpoint, no-leftover/current-frontier packet, external-block handoff, final target wrapper,
public citation/checkpoint reuse, downstream projections, and final-release bundle reuse expected by
current proof-frontier consumers.
-/
structure ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  finalReleaseEndpoint :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamObligationLayer :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalProofMdCheckpoint :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalTargetWrapper :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamSelectorObligations : FirstBitCurrentSelectorAssumptions
  largeSupportSelector : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentFrontierAssumptions : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  terminalStrictCrossAtomDefect_obligation : terminalStrictCrossAtomDefect
  terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation :
    terminalNoLeftoverFourFourAtomDeletionDichotomy
  terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement_fromFinalReleaseEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromCurrentSelectorExternalBlock : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromFinalTargetWrapper : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromPublicCitationCheckpointExternalBlock : TargetStatement

/-- Package the final-release endpoint bundle as the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  finalReleaseEndpoint := h
  downstreamObligationLayer := h.toFinalPublicDownstreamTargetObligationLayer
  finalProofMdCheckpoint := h.toFinalPublicCheckpointFacade
  publicCitationCheckpointReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  finalTargetWrapper := h.toFinalPublicTargetObligationPacket
  finalConsumerFacade := h.toPublicReleaseFinalConsumerFacade
  finalReleaseBundleReuse := h.toPublicFinalArchiveReleaseBundle
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamSelectorObligations := h.firstBitSelectors
  largeSupportSelector := h.largeEvenDegreeModFourLoss32
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  currentFrontierAssumptions := h.toCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions := h.toNoLeftoverDeletionAssumptionPacket
  externalBlockHandoff := h.toExternalBlockHandoffFacade
  terminalStrictCrossAtomDefect_obligation := h.toTerminalStrictCrossAtomDefect
  terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation :=
    h.toNoLeftoverFourFourAtomDeletionDichotomy
  terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation :=
    h.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
  targetStatement_fromFinalReleaseEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle h
  targetStatement_fromDownstreamObligationProjection :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      h.toFinalPublicDownstreamTargetObligationLayer
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaCurrentSelectorEndpoint
      h
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint
      h.toNoLeftoverCurrentFrontierPacket h.toCurrentSelectorEndpoint
  targetStatement_fromCurrentSelectorExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint_viaExternalBlock
      h.toNoLeftoverCurrentFrontierPacket h.toCurrentSelectorEndpoint
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaExternalBlockHandoff
      h
  targetStatement_fromFinalTargetWrapper :=
    targetStatement_of_proofMdLargeSupportColoringFinalPublicTargetObligationPacket
      h.toFinalPublicTargetObligationPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaPublicCitationCheckpointReuse
      h
  targetStatement_fromPublicCitationCheckpointExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle_viaPublicCitationCheckpointExternalBlock
      h

/-- Expose the public/final current-frontier wrapper from the final-release endpoint bundle. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h

/-- Expose the public/final current-frontier wrapper from the downstream obligation layer. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper

/-- Expose the public/final current-frontier wrapper from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper

/-- Expose the public/final current-frontier wrapper from public citation/checkpoint reuse. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper

/-- Expose the public/final current-frontier wrapper from the public final-consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toFinalReleaseDownstreamConsumerEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper

/-- Recover the final-release endpoint from the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalReleaseEndpoint

/-- Recover the downstream obligation layer from the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamObligationLayer

/-- Recover the final-public checkpoint from the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalPublicCheckpointFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalProofMdCheckpoint

/-- Recover public citation/checkpoint reuse from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicCitationCheckpointReuse

/-- Recover the final target wrapper from the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalTargetWrapper

/-- Recover the public final-consumer facade from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toPublicReleaseFinalConsumerFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalConsumerFacade

/-- Recover final-release bundle reuse from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.finalReleaseBundleReuse

/-- Recover the selector endpoint from the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the current-frontier assumptions from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toCurrentFrontierAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket :=
  h.currentFrontierAssumptions

/-- Recover the no-leftover deletion assumptions from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toNoLeftoverDeletionAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverDeletionAssumptions

/-- Recover the external-block handoff from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- Selector obligations exposed by the public/final current-frontier wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.firstBitSelectors
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitCurrentSelectorAssumptions :=
  h.downstreamSelectorObligations

/-- Large-support loss-`32` selector exposed by the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.largeEvenDegreeModFourLoss32
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    HasLargeEvenDegreeModFourLoss32InducedSubgraph :=
  h.largeSupportSelector

/-- Project strict cross-atom defect control from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.terminalStrictCrossAtomDefect_obligation

/-- Project the no-leftover four-four-atom deletion dichotomy from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.terminalNoLeftoverFourFourAtomDeletionDichotomy_obligation

/-- Project the no-leftover unit-strict-absorption/lift-collision consequence from the wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision_obligation

/-- The public/final current-frontier wrapper closes the target via final-release endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalReleaseEndpoint

/-- The wrapper closes the target through downstream obligation projection. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaDownstreamObligationProjection
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

/-- The wrapper closes the target through the current selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- The wrapper closes the target through the no-leftover/current-frontier packet. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- The wrapper closes the external-block target through no-leftover/current-selector reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaCurrentSelectorExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorExternalBlock

/-- The wrapper closes the target through the external-block handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaExternalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- The wrapper closes the target through the final target wrapper. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaFinalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalTargetWrapper

/-- The wrapper closes the target through public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaPublicCitationCheckpointReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- The wrapper closes the external-block route through public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaPublicCitationCheckpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointExternalBlock

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_finalReleaseEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).finalReleaseEndpoint =
      h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_downstreamObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).downstreamObligationLayer =
      h.toFinalPublicDownstreamTargetObligationLayer :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_finalProofMdCheckpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).finalProofMdCheckpoint =
      h.toFinalPublicCheckpointFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_publicCitationCheckpointReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).publicCitationCheckpointReuse =
      h.toPublicReleaseCurrentFrontierCitationBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_finalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).finalTargetWrapper =
      h.toFinalPublicTargetObligationPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_finalReleaseBundleReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).finalReleaseBundleReuse =
      h.toPublicFinalArchiveReleaseBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).noLeftoverCurrentFrontierPacket =
      h.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.ofFinalReleaseDownstreamConsumerEndpointBundle h).externalBlockHandoff =
      h.toExternalBlockHandoffFacade :=
  rfl

/--
Terminal selector names consumed by the final proof-md public endpoint.  The cases are exactly the
three terminal assumptions already projected by the public/final current-frontier endpoint wrapper.
-/
inductive ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector : Type where
  | strictCrossAtomDefect
  | noLeftoverFourFourAtomDeletionDichotomy
  | noLeftoverUnitStrictAbsorptionOrLiftCollision
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector

/-- The exact terminal obligation selected by a final proof-md consumer/public selector. -/
def obligation
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector → Prop
  | strictCrossAtomDefect => terminalStrictCrossAtomDefect
  | noLeftoverFourFourAtomDeletionDichotomy =>
      terminalNoLeftoverFourFourAtomDeletionDichotomy
  | noLeftoverUnitStrictAbsorptionOrLiftCollision =>
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision

end ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector

/--
Packet of exact terminal selector obligations for final proof-md public consumers.  It is
assumption-backed: every field is one of the terminal propositions supplied by the current wrapper.
-/
structure ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) : Prop where
  strictCrossAtomDefect : terminalStrictCrossAtomDefect
  noLeftoverFourFourAtomDeletionDichotomy :
    terminalNoLeftoverFourFourAtomDeletionDichotomy
  noLeftoverUnitStrictAbsorptionOrLiftCollision :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- Build the terminal selector-obligation packet from its three explicit assumptions. -/
theorem proofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket_of_parts
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (hstrict : terminalStrictCrossAtomDefect)
    (hdelete : terminalNoLeftoverFourFourAtomDeletionDichotomy)
    (hlift : terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  strictCrossAtomDefect := hstrict
  noLeftoverFourFourAtomDeletionDichotomy := hdelete
  noLeftoverUnitStrictAbsorptionOrLiftCollision := hlift

/-- Project the obligation named by a final proof-md consumer/public terminal selector. -/
theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket.obligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (selector : ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision selector := by
  cases selector
  · exact h.strictCrossAtomDefect
  · exact h.noLeftoverFourFourAtomDeletionDichotomy
  · exact h.noLeftoverUnitStrictAbsorptionOrLiftCollision

/--
Package the terminal selector obligations projected by the public/final current-frontier endpoint
wrapper into the exact terminal selector packet expected by final proof-md public consumers.
-/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicTerminalSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  strictCrossAtomDefect := h.toTerminalStrictCrossAtomDefect
  noLeftoverFourFourAtomDeletionDichotomy := h.toNoLeftoverFourFourAtomDeletionDichotomy
  noLeftoverUnitStrictAbsorptionOrLiftCollision :=
    h.toNoLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The wrapper discharges every terminal selector obligation in the final public packet. -/
theorem ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.finalProofMdConsumerPublicTerminalSelectorObligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (selector : ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision selector :=
  ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket.obligation
    h.toFinalProofMdConsumerPublicTerminalSelectorObligationPacket selector

/--
Final proof-md consumer/public endpoint bundle built from the public/final current-frontier wrapper.
It keeps the wrapper as the source of truth while exposing the terminal selector obligations, selector
endpoint, no-leftover/current-frontier packet, external-block handoff, final target wrapper, public
citation/checkpoint reuse, downstream obligation projection, and final-release bundle reuse.
-/
structure ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop) :
    Type where
  publicFinalCurrentFrontierEndpoint :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseEndpoint :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  terminalSelectorObligations :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  selectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamSelectorObligations : FirstBitCurrentSelectorAssumptions
  largeSupportSelector : HasLargeEvenDegreeModFourLoss32InducedSubgraph
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentFrontierAssumptions : ProofMdLargeSupportColoringCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions :
    ProofMdLargeSupportColoringNoLeftoverDeletionAssumptionPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  finalTargetWrapper :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalProofMdCheckpoint :
    ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalConsumerFacade :
    ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  targetStatement_fromPublicFinalCurrentFrontierEndpoint : TargetStatement
  targetStatement_fromTerminalSelectorObligations : TargetStatement
  targetStatement_fromFinalReleaseEndpoint : TargetStatement
  targetStatement_fromSelectorEndpoint : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromSelectorEndpointExternalBlock : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromFinalTargetWrapper : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromPublicCitationCheckpointExternalBlock : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement

/-- Promote the public/final current-frontier wrapper to the final proof-md consumer/public bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision where
  publicFinalCurrentFrontierEndpoint := h
  finalReleaseEndpoint := h.toFinalReleaseDownstreamConsumerEndpointBundle
  terminalSelectorObligations :=
    h.toFinalProofMdConsumerPublicTerminalSelectorObligationPacket
  selectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamSelectorObligations := h.firstBitSelectors
  largeSupportSelector := h.largeEvenDegreeModFourLoss32
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  currentFrontierAssumptions := h.toCurrentFrontierAssumptionPacket
  noLeftoverDeletionAssumptions := h.toNoLeftoverDeletionAssumptionPacket
  externalBlockHandoff := h.toExternalBlockHandoffFacade
  finalTargetWrapper := h.toFinalPublicTargetObligationPacket
  publicCitationCheckpointReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  downstreamObligationProjection := h.toFinalPublicDownstreamTargetObligationLayer
  finalProofMdCheckpoint := h.toFinalPublicCheckpointFacade
  finalConsumerFacade := h.toPublicReleaseFinalConsumerFacade
  finalReleaseBundleReuse := h.toPublicFinalArchiveReleaseBundle
  targetStatement_fromPublicFinalCurrentFrontierEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper h
  targetStatement_fromTerminalSelectorObligations :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper h
  targetStatement_fromFinalReleaseEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper h
  targetStatement_fromSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaCurrentSelectorEndpoint
      h
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaNoLeftoverCurrentFrontierPacket
      h
  targetStatement_fromSelectorEndpointExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaCurrentSelectorExternalBlock
      h
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaExternalBlockHandoff
      h
  targetStatement_fromFinalTargetWrapper :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaFinalTargetWrapper
      h
  targetStatement_fromPublicCitationCheckpointReuse :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaPublicCitationCheckpointReuse
      h
  targetStatement_fromPublicCitationCheckpointExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaPublicCitationCheckpointExternalBlock
      h
  targetStatement_fromDownstreamObligationProjection :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper_viaDownstreamObligationProjection
      h

/-- Expose the final proof-md consumer/public bundle from the public/final wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
    h

/-- Expose the final proof-md consumer/public bundle from the final-release endpoint. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle

/-- Expose the final proof-md consumer/public bundle from downstream obligation projections. -/
def ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle

/-- Expose the final proof-md consumer/public bundle from the final-public checkpoint. -/
def ProofMdLargeSupportColoringFinalPublicCheckpointFacade.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalPublicCheckpointFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle

/-- Expose the final proof-md consumer/public bundle from public citation/checkpoint reuse. -/
def ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle

/-- Expose the final proof-md consumer/public bundle from the public final-consumer facade. -/
def ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicReleaseFinalConsumerFacade
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.toPublicFinalCurrentFrontierEndpointWrapper.toFinalProofMdConsumerPublicEndpointBundle

/-- Recover the public/final current-frontier wrapper from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toPublicFinalCurrentFrontierEndpointWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicFinalCurrentFrontierEndpoint

/-- Recover the final-release downstream endpoint from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toFinalReleaseDownstreamConsumerEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalReleaseEndpoint

/-- Recover exact terminal selector obligations from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toTerminalSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.terminalSelectorObligations

/-- Recover the current selector endpoint from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.selectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the external-block handoff from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toExternalBlockHandoffFacade
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringExternalBlockHandoffFacade :=
  h.externalBlockHandoff

/-- Recover the final target wrapper from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toFinalPublicTargetObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalTargetWrapper

/-- Recover public citation/checkpoint reuse from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toPublicReleaseCurrentFrontierCitationBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicCitationCheckpointReuse

/-- Recover downstream obligation projections from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamObligationProjection

/-- Recover final-release bundle reuse from the final proof-md consumer bundle. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.finalReleaseBundleReuse

/-- Project strict cross-atom defect control from exact terminal selector obligations. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toTerminalStrictCrossAtomDefect
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalStrictCrossAtomDefect :=
  h.terminalSelectorObligations.strictCrossAtomDefect

/-- Project the no-leftover deletion dichotomy from exact terminal selector obligations. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toNoLeftoverFourFourAtomDeletionDichotomy
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverFourFourAtomDeletionDichotomy :=
  h.terminalSelectorObligations.noLeftoverFourFourAtomDeletionDichotomy

/-- Project the no-leftover absorption/lift consequence from exact terminal selector obligations. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toNoLeftoverUnitStrictAbsorptionOrLiftCollision
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.terminalSelectorObligations.noLeftoverUnitStrictAbsorptionOrLiftCollision

/-- The final proof-md consumer/public bundle discharges every exact terminal selector obligation. -/
theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.terminalSelectorObligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (selector : ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision selector :=
  ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket.obligation
    h.terminalSelectorObligations selector

/-- The final proof-md consumer/public endpoint closes the target via the public/final wrapper. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicFinalCurrentFrontierEndpoint

/-- The final proof-md consumer/public endpoint closes the target after terminal selector packaging. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaTerminalSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromTerminalSelectorObligations

/-- The final proof-md consumer/public endpoint closes the target via final-release reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaFinalReleaseEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalReleaseEndpoint

/-- The final proof-md consumer/public endpoint closes the target via the selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromSelectorEndpoint

/-- The final proof-md consumer/public endpoint closes through the no-leftover/current packet. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- The final proof-md consumer/public endpoint closes the no-leftover selector external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaSelectorEndpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromSelectorEndpointExternalBlock

/-- The final proof-md consumer/public endpoint closes through the external-block handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaExternalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- The final proof-md consumer/public endpoint closes through the final target wrapper. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaFinalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromFinalTargetWrapper

/-- The final proof-md consumer/public endpoint closes through public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaPublicCitationCheckpointReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- The final proof-md consumer/public endpoint closes the external-block citation route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaPublicCitationCheckpointExternalBlock
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointExternalBlock

/-- The final proof-md consumer/public endpoint closes through downstream obligation projection. -/
theorem targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaDownstreamObligationProjection
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_publicFinalCurrentFrontierEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).publicFinalCurrentFrontierEndpoint = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_terminalSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).terminalSelectorObligations =
      h.toFinalProofMdConsumerPublicTerminalSelectorObligationPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_selectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).selectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_noLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).noLeftoverCurrentFrontierPacket = h.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_externalBlockHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).externalBlockHandoff = h.toExternalBlockHandoffFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_finalTargetWrapper
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).finalTargetWrapper = h.toFinalPublicTargetObligationPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_publicCitationCheckpointReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).publicCitationCheckpointReuse =
      h.toPublicReleaseCurrentFrontierCitationBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_downstreamObligationProjection
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).downstreamObligationProjection =
      h.toFinalPublicDownstreamTargetObligationLayer :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper_finalReleaseBundleReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision) :
    (ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.ofPublicFinalCurrentFrontierEndpointWrapper
      h).finalReleaseBundleReuse = h.toPublicFinalArchiveReleaseBundle :=
  rfl

/--
Assumption-backed scalar-quotient/transpose packet for the proof-md public frontier.  The
transpose-rigidity input is deliberately split into its forward, reverse, and diagonal pieces; the
remaining fields name the parity-tetrahedron star phase handoff, the signed-`K4` quotient closure
classification, and the downstream target-selector consumer marker.
-/
structure ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
    (fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop) :
    Prop where
  terminalScalarSurfaces : FirstBitPacketTerminalScalarFrontierSurfaces
  quotientWithTerminalScalars : FirstBitPacketQuotientFrontierSurfacesWithTerminalScalars
  fullySplitTransposeForwardRigidityCert : fullySplitTransposeForwardRigidity
  fullySplitTransposeReverseRigidityCert : fullySplitTransposeReverseRigidity
  fullySplitTransposeDiagonalRigidityCert : fullySplitTransposeDiagonalRigidity
  parityTetrahedronStarPhaseHandoffCert : parityTetrahedronStarPhaseHandoff
  signedK4QuotientClosureClassificationCert : signedK4QuotientClosureClassification
  publicDownstreamTargetSelectorConsumersCert : publicDownstreamTargetSelectorConsumers

/-- Build the scalar-quotient/transpose assumption packet from its explicit endpoints. -/
theorem proofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket_of_parts
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (hterminalScalars : FirstBitPacketTerminalScalarFrontierSurfaces)
    (hquotientWithScalars : FirstBitPacketQuotientFrontierSurfacesWithTerminalScalars)
    (hforward : fullySplitTransposeForwardRigidity)
    (hreverse : fullySplitTransposeReverseRigidity)
    (hdiagonal : fullySplitTransposeDiagonalRigidity)
    (hphase : parityTetrahedronStarPhaseHandoff)
    (hclassification : signedK4QuotientClosureClassification)
    (hconsumers : publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers where
  terminalScalarSurfaces := hterminalScalars
  quotientWithTerminalScalars := hquotientWithScalars
  fullySplitTransposeForwardRigidityCert := hforward
  fullySplitTransposeReverseRigidityCert := hreverse
  fullySplitTransposeDiagonalRigidityCert := hdiagonal
  parityTetrahedronStarPhaseHandoffCert := hphase
  signedK4QuotientClosureClassificationCert := hclassification
  publicDownstreamTargetSelectorConsumersCert := hconsumers

/-- Project the terminal scalar surfaces from the scalar-quotient/transpose packet. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toTerminalScalarSurfaces
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    FirstBitPacketTerminalScalarFrontierSurfaces :=
  h.terminalScalarSurfaces

/-- Project the quotient frontier enriched with terminal scalars. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toQuotientWithTerminalScalars
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    FirstBitPacketQuotientFrontierSurfacesWithTerminalScalars :=
  h.quotientWithTerminalScalars

/-- Project the scalar-free quotient frontier from the scalar-quotient packet. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toQuotientFrontier
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    FirstBitPacketQuotientFrontierSurfaces :=
  h.quotientWithTerminalScalars.quotient

/-- Project the forward half of the split transpose-rigidity assumption. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toFullySplitTransposeForwardRigidity
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    fullySplitTransposeForwardRigidity :=
  h.fullySplitTransposeForwardRigidityCert

/-- Project the reverse half of the split transpose-rigidity assumption. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toFullySplitTransposeReverseRigidity
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    fullySplitTransposeReverseRigidity :=
  h.fullySplitTransposeReverseRigidityCert

/-- Project the diagonal/fixed-point part of the split transpose-rigidity assumption. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toFullySplitTransposeDiagonalRigidity
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    fullySplitTransposeDiagonalRigidity :=
  h.fullySplitTransposeDiagonalRigidityCert

/-- Project the parity-tetrahedron star phase handoff marker. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toParityTetrahedronStarPhaseHandoff
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    parityTetrahedronStarPhaseHandoff :=
  h.parityTetrahedronStarPhaseHandoffCert

/-- Project the signed-`K4` quotient closure classification marker. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toSignedK4QuotientClosureClassification
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    signedK4QuotientClosureClassification :=
  h.signedK4QuotientClosureClassificationCert

/-- Project the public downstream target-selector consumer marker. -/
theorem ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket.toPublicDownstreamTargetSelectorConsumers
    {fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    publicDownstreamTargetSelectorConsumers :=
  h.publicDownstreamTargetSelectorConsumersCert

/--
Public selector names for the scalar-quotient proof-md frontier.  The first three cases reuse the
terminal public selector obligations; the remaining cases name the scalar quotient, split transpose,
star-phase, signed-`K4`, and downstream-consumer assumptions.
-/
inductive ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector : Type where
  | terminalStrictCrossAtomDefectObligation
  | terminalNoLeftoverFourFourAtomDeletionDichotomyObligation
  | terminalNoLeftoverUnitStrictAbsorptionOrLiftCollisionObligation
  | terminalScalarFrontierSurfaces
  | quotientWithTerminalScalarsEndpoint
  | fullySplitTransposeForwardRigidityEndpoint
  | fullySplitTransposeReverseRigidityEndpoint
  | fullySplitTransposeDiagonalRigidityEndpoint
  | parityTetrahedronStarPhaseHandoffEndpoint
  | signedK4QuotientClosureClassificationEndpoint
  | publicDownstreamTargetSelectorConsumersEndpoint
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector

/-- The exact obligation selected by a scalar-quotient proof-md public target selector. -/
def obligation
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector → Prop
  | terminalStrictCrossAtomDefectObligation => terminalStrictCrossAtomDefect
  | terminalNoLeftoverFourFourAtomDeletionDichotomyObligation =>
      terminalNoLeftoverFourFourAtomDeletionDichotomy
  | terminalNoLeftoverUnitStrictAbsorptionOrLiftCollisionObligation =>
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | terminalScalarFrontierSurfaces => FirstBitPacketTerminalScalarFrontierSurfaces
  | quotientWithTerminalScalarsEndpoint => FirstBitPacketQuotientFrontierSurfacesWithTerminalScalars
  | fullySplitTransposeForwardRigidityEndpoint => fullySplitTransposeForwardRigidity
  | fullySplitTransposeReverseRigidityEndpoint => fullySplitTransposeReverseRigidity
  | fullySplitTransposeDiagonalRigidityEndpoint => fullySplitTransposeDiagonalRigidity
  | parityTetrahedronStarPhaseHandoffEndpoint => parityTetrahedronStarPhaseHandoff
  | signedK4QuotientClosureClassificationEndpoint => signedK4QuotientClosureClassification
  | publicDownstreamTargetSelectorConsumersEndpoint => publicDownstreamTargetSelectorConsumers

end ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector

/--
Obligation packet for public scalar-quotient target selectors.  It composes the existing final
proof-md terminal selector obligations with the explicit scalar quotient and split transpose packet.
-/
structure ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop) :
    Prop where
  terminalSelectorObligations :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientAssumptions :
    ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers

/-- Build the scalar-quotient public selector-obligation packet from its two component packets. -/
theorem proofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket_of_parts
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (hterminal :
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers where
  terminalSelectorObligations := hterminal
  scalarQuotientAssumptions := hscalar

/-- Project the obligation selected by a scalar-quotient proof-md public selector. -/
theorem ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector := by
  cases selector
  · exact h.terminalSelectorObligations.strictCrossAtomDefect
  · exact h.terminalSelectorObligations.noLeftoverFourFourAtomDeletionDichotomy
  · exact h.terminalSelectorObligations.noLeftoverUnitStrictAbsorptionOrLiftCollision
  · exact h.scalarQuotientAssumptions.terminalScalarSurfaces
  · exact h.scalarQuotientAssumptions.quotientWithTerminalScalars
  · exact h.scalarQuotientAssumptions.fullySplitTransposeForwardRigidityCert
  · exact h.scalarQuotientAssumptions.fullySplitTransposeReverseRigidityCert
  · exact h.scalarQuotientAssumptions.fullySplitTransposeDiagonalRigidityCert
  · exact h.scalarQuotientAssumptions.parityTetrahedronStarPhaseHandoffCert
  · exact h.scalarQuotientAssumptions.signedK4QuotientClosureClassificationCert
  · exact h.scalarQuotientAssumptions.publicDownstreamTargetSelectorConsumersCert

/--
Package the final proof-md terminal selectors together with explicit scalar quotient and transpose
assumptions into the public scalar-quotient target-selector obligations.
-/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toScalarQuotientPublicTargetSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers where
  terminalSelectorObligations := h.toTerminalSelectorObligationPacket
  scalarQuotientAssumptions := hscalar

/--
Assumption-backed endpoint bundle for public scalar-quotient proof-md consumers.  It keeps the
existing final proof-md/public endpoint as the source of target closure while carrying the scalar
quotient, fully split transpose-rigidity, parity-tetrahedron star phase handoff, signed-`K4`
classification, and downstream target-selector consumer obligations explicitly.
-/
structure ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop) :
    Type where
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalCurrentFrontierEndpoint :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseEndpoint :
    ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamObligationLayer :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  terminalSelectorObligations :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicTerminalSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientAssumptions :
    ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  publicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamSelectorObligations : FirstBitCurrentSelectorAssumptions
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  finalTargetWrapper :
    ProofMdLargeSupportColoringFinalPublicTargetObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientAssumptionPacket : TargetStatement
  targetStatement_fromPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromFullySplitTransposeForwardRigidity : TargetStatement
  targetStatement_fromFullySplitTransposeReverseRigidity : TargetStatement
  targetStatement_fromFullySplitTransposeDiagonalRigidity : TargetStatement
  targetStatement_fromParityTetrahedronStarPhaseHandoff : TargetStatement
  targetStatement_fromSignedK4QuotientClosureClassification : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumers : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement

/-- Build the scalar-quotient public endpoint bundle from the final proof-md public endpoint. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers where
  finalProofMdConsumerPublicEndpoint := h
  publicFinalCurrentFrontierEndpoint := h.toPublicFinalCurrentFrontierEndpointWrapper
  finalReleaseEndpoint := h.toFinalReleaseDownstreamConsumerEndpointBundle
  downstreamObligationLayer := h.toFinalPublicDownstreamTargetObligationLayer
  terminalSelectorObligations := h.toTerminalSelectorObligationPacket
  scalarQuotientAssumptions := hscalar
  publicTargetSelectorObligations := h.toScalarQuotientPublicTargetSelectorObligationPacket hscalar
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamSelectorObligations := h.downstreamSelectorObligations
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  externalBlockHandoff := h.toExternalBlockHandoffFacade
  finalTargetWrapper := h.toFinalPublicTargetObligationPacket
  publicCitationCheckpointReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  downstreamObligationProjection := h.toFinalPublicDownstreamTargetObligationLayer
  finalReleaseBundleReuse := h.toPublicFinalArchiveReleaseBundle
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromScalarQuotientAssumptionPacket :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromPublicTargetSelectorObligations :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromFullySplitTransposeForwardRigidity :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromFullySplitTransposeReverseRigidity :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromFullySplitTransposeDiagonalRigidity :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromParityTetrahedronStarPhaseHandoff :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromSignedK4QuotientClosureClassification :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromPublicDownstreamTargetSelectorConsumers :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle h
  targetStatement_fromDownstreamObligationProjection :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaDownstreamObligationProjection
      h
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaSelectorEndpoint
      h

/-- Expose the scalar-quotient public endpoint bundle from a final proof-md public endpoint. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
    h hscalar

/-- Expose the scalar-quotient public endpoint bundle from the public/final wrapper. -/
def ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper.toScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.toFinalProofMdConsumerPublicEndpointBundle.toScalarQuotientPublicEndpointBundle hscalar

/-- Expose the scalar-quotient public endpoint bundle from the final-release endpoint. -/
def ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle.toScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalReleaseDownstreamConsumerEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.toFinalProofMdConsumerPublicEndpointBundle.toScalarQuotientPublicEndpointBundle hscalar

/-- Recover the final proof-md public endpoint from the scalar-quotient bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalProofMdConsumerPublicEndpoint

/-- Recover the scalar-quotient/transpose assumption packet from the scalar-quotient bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toScalarQuotientTransposeAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientAssumptions

/-- Recover the public scalar-quotient target-selector obligation packet. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toPublicTargetSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.publicTargetSelectorObligations

/-- Recover the current selector endpoint from the scalar-quotient public bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover downstream target-obligation projections from the scalar-quotient public bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toFinalPublicDownstreamTargetObligationLayer
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamObligationLayer

/-- Recover the no-leftover/current-frontier packet from the scalar-quotient public bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toNoLeftoverCurrentFrontierPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover final-release bundle reuse from the scalar-quotient public bundle. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toPublicFinalArchiveReleaseBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.finalReleaseBundleReuse

/-- The scalar-quotient public bundle discharges every named target-selector obligation. -/
theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.publicTargetSelectorObligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.publicTargetSelectorObligations selector

/-- The scalar-quotient public endpoint closes the target via the final proof-md public endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromFinalProofMdConsumerPublicEndpoint

/-- The scalar-quotient public endpoint closes the target after scalar-quotient packaging. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaScalarQuotientAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientAssumptionPacket

/-- The scalar-quotient public endpoint closes the target through public target-selector obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaPublicTargetSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromPublicTargetSelectorObligations

/-- The scalar-quotient public endpoint closes the target through forward transpose rigidity. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaFullySplitTransposeForwardRigidity
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromFullySplitTransposeForwardRigidity

/-- The scalar-quotient public endpoint closes the target through reverse transpose rigidity. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaFullySplitTransposeReverseRigidity
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromFullySplitTransposeReverseRigidity

/-- The scalar-quotient public endpoint closes the target through diagonal transpose rigidity. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaFullySplitTransposeDiagonalRigidity
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromFullySplitTransposeDiagonalRigidity

/-- The scalar-quotient public endpoint closes the target through the parity-tetrahedron star phase handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaParityTetrahedronStarPhaseHandoff
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromParityTetrahedronStarPhaseHandoff

/-- The scalar-quotient public endpoint closes the target through signed-`K4` quotient classification. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaSignedK4QuotientClosureClassification
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromSignedK4QuotientClosureClassification

/-- The scalar-quotient public endpoint closes the target through downstream target-selector consumers. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaPublicDownstreamTargetSelectorConsumers
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumers

/-- The scalar-quotient public endpoint closes the target through downstream obligation projection. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaDownstreamObligationProjection
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

/-- The scalar-quotient public endpoint closes the target through the current selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

@[simp] theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle_finalProofMdConsumerPublicEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    (ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
      h hscalar).finalProofMdConsumerPublicEndpoint = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle_scalarQuotientAssumptions
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    (ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
      h hscalar).scalarQuotientAssumptions = hscalar :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle_publicTargetSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    (ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
      h hscalar).publicTargetSelectorObligations =
      h.toScalarQuotientPublicTargetSelectorObligationPacket hscalar :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle_currentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    (ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
      h hscalar).currentSelectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle_finalReleaseBundleReuse
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers) :
    (ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
      h hscalar).finalReleaseBundleReuse = h.toPublicFinalArchiveReleaseBundle :=
  rfl

/--
Rows of the typed `F`-graph residual interface beyond the scalar-quotient public endpoint.
The two local-host rows discharge the two- and three-exception packets; the remaining rows name
the four-exception `2/2` type-square skeletons, compact signed-quotient residual, and downstream
target-selector consumer closure.
-/
inductive ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow : Type where
  | localHostTwoExceptionalPacketDischarge
  | localHostThreeExceptionalPacketDischarge
  | fourExceptionTwoTwoTypeSquareSkeletons
  | compactSignedQuotientResidual
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow

/-- The proposition named by a typed `F`-graph residual endpoint row. -/
def obligation
    (localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop) :
    ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow → Prop
  | .localHostTwoExceptionalPacketDischarge => localHostTwoExceptionalPacketDischarge
  | .localHostThreeExceptionalPacketDischarge => localHostThreeExceptionalPacketDischarge
  | .fourExceptionTwoTwoTypeSquareSkeletons => fourExceptionTwoTwoTypeSquareSkeletons
  | .compactSignedQuotientResidual => compactSignedQuotientResidual
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow

/-- Explicit assumption packet for the typed `F`-graph residual endpoint rows. -/
structure ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
    (localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop) :
    Prop where
  localHostTwoExceptionalPacketDischargeCert : localHostTwoExceptionalPacketDischarge
  localHostThreeExceptionalPacketDischargeCert : localHostThreeExceptionalPacketDischarge
  fourExceptionTwoTwoTypeSquareSkeletonsCert : fourExceptionTwoTwoTypeSquareSkeletons
  compactSignedQuotientResidualCert : compactSignedQuotientResidual
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure

/-- Build the typed `F`-graph residual packet from its five endpoint assumptions. -/
theorem proofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket_of_parts
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (htwoLocal : localHostTwoExceptionalPacketDischarge)
    (hthreeLocal : localHostThreeExceptionalPacketDischarge)
    (hfourSkeletons : fourExceptionTwoTwoTypeSquareSkeletons)
    (hsignedResidual : compactSignedQuotientResidual)
    (hconsumerClosure : publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure where
  localHostTwoExceptionalPacketDischargeCert := htwoLocal
  localHostThreeExceptionalPacketDischargeCert := hthreeLocal
  fourExceptionTwoTwoTypeSquareSkeletonsCert := hfourSkeletons
  compactSignedQuotientResidualCert := hsignedResidual
  publicDownstreamTargetSelectorConsumerClosureCert := hconsumerClosure

/-- Project the local-host discharge of two-exception packets. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.toLocalHostTwoExceptionalPacketDischarge
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    localHostTwoExceptionalPacketDischarge :=
  h.localHostTwoExceptionalPacketDischargeCert

/-- Project the local-host discharge of three-exception packets. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.toLocalHostThreeExceptionalPacketDischarge
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    localHostThreeExceptionalPacketDischarge :=
  h.localHostThreeExceptionalPacketDischargeCert

/-- Project the remaining four-exception `2/2` type-square skeleton endpoint. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.toFourExceptionTwoTwoTypeSquareSkeletons
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    fourExceptionTwoTwoTypeSquareSkeletons :=
  h.fourExceptionTwoTwoTypeSquareSkeletonsCert

/-- Project the compact signed-quotient residual endpoint. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.toCompactSignedQuotientResidual
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    compactSignedQuotientResidual :=
  h.compactSignedQuotientResidualCert

/-- Project the public downstream target-selector consumer-closure endpoint. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.toPublicDownstreamTargetSelectorConsumerClosure
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Project the obligation selected by a typed `F`-graph residual row. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.rowObligation
    {localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (row : ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow) :
    ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow.obligation
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure row := by
  cases row
  · exact h.localHostTwoExceptionalPacketDischargeCert
  · exact h.localHostThreeExceptionalPacketDischargeCert
  · exact h.fourExceptionTwoTwoTypeSquareSkeletonsCert
  · exact h.compactSignedQuotientResidualCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/--
Public target selectors for the scalar-quotient endpoint enriched by the typed `F`-graph residual
rows.  Scalar-quotient selectors are reused rather than duplicated; the residual rows are appended as
explicit assumption-backed endpoints.
-/
inductive ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector : Type where
  | scalarQuotientSelector (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector)
  | typedFGraphResidualRow (row : ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow)
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector

/-- The exact obligation selected by a typed `F`-graph residual public target selector. -/
def obligation
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector → Prop
  | .scalarQuotientSelector selector =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector
  | .typedFGraphResidualRow row =>
      ProofMdLargeSupportColoringTypedFGraphResidualEndpointRow.obligation
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure row

end ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector

/--
Obligation packet for the typed `F`-graph residual public selectors.  It composes the existing
scalar-quotient public selector obligations with the five residual endpoint assumptions.
-/
structure ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop) :
    Prop where
  scalarQuotientPublicObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualAssumptions :
    ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure

/-- Build typed `F`-graph residual selector obligations from scalar and residual packets. -/
theorem proofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket_of_parts
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure where
  scalarQuotientPublicObligations := hscalar
  typedFGraphResidualAssumptions := hresidual

/-- Project the obligation selected by a typed `F`-graph residual public selector. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector := by
  cases selector with
  | scalarQuotientSelector scalarSelector =>
      exact
        ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
          h.scalarQuotientPublicObligations scalarSelector
  | typedFGraphResidualRow row =>
      exact
        ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket.rowObligation
          h.typedFGraphResidualAssumptions row

/-- Extend scalar-quotient public selector obligations with typed `F`-graph residual rows. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toTypedFGraphResidualPublicTargetSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure where
  scalarQuotientPublicObligations := h.toPublicTargetSelectorObligationPacket
  typedFGraphResidualAssumptions := hresidual

/--
Assumption-backed public endpoint bundle for the typed `F`-graph residual frontier.  The
scalar-quotient public endpoint remains the source of target closure; the typed residual rows are
carried explicitly for downstream consumers and projected through target-statement facades.
-/
structure ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
    (terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop) :
    Type where
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientAssumptions :
    ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualAssumptions :
    ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  localHostTwoExceptionalPacketDischarge_obligation :
    localHostTwoExceptionalPacketDischarge
  localHostThreeExceptionalPacketDischarge_obligation :
    localHostThreeExceptionalPacketDischarge
  fourExceptionTwoTwoTypeSquareSkeletons_obligation :
    fourExceptionTwoTwoTypeSquareSkeletons
  compactSignedQuotientResidual_obligation : compactSignedQuotientResidual
  publicDownstreamTargetSelectorConsumerClosure_obligation :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromTypedFGraphResidualTargetSelectorObligations : TargetStatement
  targetStatement_fromLocalHostTwoExceptionalPacketDischarge : TargetStatement
  targetStatement_fromLocalHostThreeExceptionalPacketDischarge : TargetStatement
  targetStatement_fromFourExceptionTwoTwoTypeSquareSkeletons : TargetStatement
  targetStatement_fromCompactSignedQuotientResidual : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement

/-- Build the typed `F`-graph residual public endpoint from scalar endpoint and residual assumptions. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure where
  scalarQuotientPublicEndpoint := h
  finalProofMdConsumerPublicEndpoint := h.toFinalProofMdConsumerPublicEndpointBundle
  scalarQuotientAssumptions := h.toScalarQuotientTransposeAssumptionPacket
  typedFGraphResidualAssumptions := hresidual
  scalarQuotientPublicObligations := h.toPublicTargetSelectorObligationPacket
  typedFGraphResidualTargetSelectorObligations :=
    h.toTypedFGraphResidualPublicTargetSelectorObligationPacket hresidual
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamObligationProjection := h.toFinalPublicDownstreamTargetObligationLayer
  finalReleaseBundleReuse := h.toPublicFinalArchiveReleaseBundle
  localHostTwoExceptionalPacketDischarge_obligation :=
    hresidual.toLocalHostTwoExceptionalPacketDischarge
  localHostThreeExceptionalPacketDischarge_obligation :=
    hresidual.toLocalHostThreeExceptionalPacketDischarge
  fourExceptionTwoTwoTypeSquareSkeletons_obligation :=
    hresidual.toFourExceptionTwoTwoTypeSquareSkeletons
  compactSignedQuotientResidual_obligation :=
    hresidual.toCompactSignedQuotientResidual
  publicDownstreamTargetSelectorConsumerClosure_obligation :=
    hresidual.toPublicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromScalarQuotientPublicEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle h
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle h
  targetStatement_fromTypedFGraphResidualTargetSelectorObligations :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaPublicTargetSelectorObligations
      h
  targetStatement_fromLocalHostTwoExceptionalPacketDischarge :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle h
  targetStatement_fromLocalHostThreeExceptionalPacketDischarge :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle h
  targetStatement_fromFourExceptionTwoTwoTypeSquareSkeletons :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle h
  targetStatement_fromCompactSignedQuotientResidual :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaSignedK4QuotientClosureClassification
      h
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaPublicDownstreamTargetSelectorConsumers
      h
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaCurrentSelectorEndpoint
      h
  targetStatement_fromDownstreamObligationProjection :=
    targetStatement_of_proofMdLargeSupportColoringScalarQuotientPublicEndpointBundle_viaDownstreamObligationProjection
      h

/-- Expose the typed `F`-graph residual endpoint from a scalar-quotient public endpoint. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toTypedFGraphResidualPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle
    h hresidual

/-- Build the typed residual endpoint directly from a final proof-md public endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  (h.toScalarQuotientPublicEndpointBundle hscalar).toTypedFGraphResidualPublicEndpointBundle
    hresidual

/-- Expose the typed residual endpoint from a final proof-md public endpoint. -/
def ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle.toTypedFGraphResidualPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision)
    (hscalar :
      ProofMdLargeSupportColoringScalarQuotientTransposeAssumptionPacket
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofFinalProofMdConsumerPublicEndpointBundle
    h hscalar hresidual

/-- Recover the scalar-quotient public endpoint from the typed `F`-graph residual bundle. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toScalarQuotientPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicEndpoint

/-- Recover the typed `F`-graph residual assumption packet. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toTypedFGraphResidualAssumptionPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualAssumptions

/-- Recover the typed `F`-graph residual target-selector obligation packet. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toTypedFGraphResidualPublicTargetSelectorObligationPacket
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualTargetSelectorObligations

/-- The typed residual endpoint bundle discharges every public residual selector obligation. -/
theorem ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.publicTargetSelectorObligation
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualTargetSelectorObligations selector

/-- Project the local-host two-exception discharge from the typed residual endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toLocalHostTwoExceptionalPacketDischarge
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    localHostTwoExceptionalPacketDischarge :=
  h.localHostTwoExceptionalPacketDischarge_obligation

/-- Project the local-host three-exception discharge from the typed residual endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toLocalHostThreeExceptionalPacketDischarge
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    localHostThreeExceptionalPacketDischarge :=
  h.localHostThreeExceptionalPacketDischarge_obligation

/-- Project the four-exception `2/2` type-square skeleton endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toFourExceptionTwoTwoTypeSquareSkeletons
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    fourExceptionTwoTwoTypeSquareSkeletons :=
  h.fourExceptionTwoTwoTypeSquareSkeletons_obligation

/-- Project the compact signed-quotient residual endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toCompactSignedQuotientResidual
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    compactSignedQuotientResidual :=
  h.compactSignedQuotientResidual_obligation

/-- Project the public downstream target-selector consumer closure endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toPublicDownstreamTargetSelectorConsumerClosure
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosure_obligation

/-- The typed `F`-graph residual endpoint closes the target by scalar-quotient public reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- The typed residual endpoint closes the target via final proof-md public endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaFinalProofMdConsumerPublicEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromFinalProofMdConsumerPublicEndpoint

/-- The typed residual endpoint closes the target through its residual target-selector obligations. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaTypedFGraphResidualTargetSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualTargetSelectorObligations

/-- The typed residual endpoint closes the target after local-host two-exception discharge. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaLocalHostTwoExceptionalPacketDischarge
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromLocalHostTwoExceptionalPacketDischarge

/-- The typed residual endpoint closes the target after local-host three-exception discharge. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaLocalHostThreeExceptionalPacketDischarge
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromLocalHostThreeExceptionalPacketDischarge

/-- The typed residual endpoint closes the target through the four-exception `2/2` skeleton facade. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaFourExceptionTwoTwoTypeSquareSkeletons
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromFourExceptionTwoTwoTypeSquareSkeletons

/-- The typed residual endpoint closes the target through the compact signed-quotient residual facade. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaCompactSignedQuotientResidual
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromCompactSignedQuotientResidual

/-- The typed residual endpoint closes the target through downstream target-selector consumer closure. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaPublicDownstreamTargetSelectorConsumerClosure
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The typed residual endpoint closes the target through the current selector endpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaCurrentSelectorEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- The typed residual endpoint closes the target through downstream obligation projection. -/
theorem targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaDownstreamObligationProjection
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

@[simp] theorem ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle_scalarQuotientPublicEndpoint
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    (ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle
      h hresidual).scalarQuotientPublicEndpoint = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle_typedFGraphResidualAssumptions
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    (ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle
      h hresidual).typedFGraphResidualAssumptions = hresidual :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle_typedFGraphResidualTargetSelectorObligations
    {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure : Prop}
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure) :
    (ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.ofScalarQuotientPublicEndpointBundle
      h hresidual).typedFGraphResidualTargetSelectorObligations =
        h.toTypedFGraphResidualPublicTargetSelectorObligationPacket hresidual :=
  rfl

/-
## Final public first-bit closure facade

This last layer keeps the closure structural: it records the typed `F`-graph residual facade,
the scalar-quotient public endpoint, and the remaining public diagnostics as explicit rows, but it
does not introduce an unconditional final theorem claim.
-/

section FirstBitPublicFinalClosure

variable {terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
  terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision fullySplitTransposeForwardRigidity
  fullySplitTransposeReverseRigidity fullySplitTransposeDiagonalRigidity
  parityTetrahedronStarPhaseHandoff signedK4QuotientClosureClassification
  publicDownstreamTargetSelectorConsumers localHostTwoExceptionalPacketDischarge
  localHostThreeExceptionalPacketDischarge fourExceptionTwoTwoTypeSquareSkeletons
  compactSignedQuotientResidual publicDownstreamTargetSelectorConsumerClosure
  allTernaryEndpointExhaustion nearThresholdBoundaryDiagnostics : Prop}

/-- Rows of the final public first-bit closure facade. -/
inductive ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow : Type where
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow

/-- The object or proposition selected by a final public first-bit closure row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow → Sort _
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow

/--
Obligation packet for the final public first-bit closure facade.  The typed residual facade and
scalar-quotient endpoint are carried as row objects; the remaining rows are assumption-backed
public diagnostics.
-/
structure ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket : Type where
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket

/-- Build final closure obligations from the typed residual facade and public diagnostics. -/
def ofTypedFGraphResidualPublicEndpointBundle
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket where
  typedFGraphResidualFacade := htyped
  scalarQuotientPublicEndpoint := htyped.toScalarQuotientPublicEndpointBundle
  allTernaryEndpointExhaustionCert := hallTernary
  nearThresholdBoundaryDiagnosticsCert := hnearThreshold
  publicDownstreamTargetSelectorConsumerClosureCert :=
    htyped.toPublicDownstreamTargetSelectorConsumerClosure

/-- Project the row selected by a final public first-bit closure obligation packet. -/
def obligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow.obligation row := by
  cases row
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

@[simp] theorem ofTypedFGraphResidualPublicEndpointBundle_typedFGraphResidualFacade
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    (ofTypedFGraphResidualPublicEndpointBundle htyped hallTernary hnearThreshold).typedFGraphResidualFacade =
      htyped :=
  rfl

@[simp] theorem ofTypedFGraphResidualPublicEndpointBundle_scalarQuotientPublicEndpoint
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    (ofTypedFGraphResidualPublicEndpointBundle htyped hallTernary hnearThreshold).scalarQuotientPublicEndpoint =
      htyped.toScalarQuotientPublicEndpointBundle :=
  rfl

@[simp] theorem ofTypedFGraphResidualPublicEndpointBundle_allTernaryEndpointExhaustion
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    (ofTypedFGraphResidualPublicEndpointBundle htyped hallTernary hnearThreshold).allTernaryEndpointExhaustionCert =
      hallTernary :=
  rfl

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket

/-- Package the typed residual facade as final public first-bit closure obligations. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toFirstBitPublicFinalClosureObligationPacket
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket.ofTypedFGraphResidualPublicEndpointBundle
    h hallTernary hnearThreshold

/-- Package a scalar-quotient endpoint plus typed residual assumptions as final closure obligations. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toFirstBitPublicFinalClosureObligationPacket
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toFirstBitPublicFinalClosureObligationPacket
    (h.toTypedFGraphResidualPublicEndpointBundle hresidual) hallTernary hnearThreshold

/--
Final public first-bit closure facade.  It packages the typed `F`-graph residual facade, the
scalar-quotient public endpoint, all-ternary endpoint exhaustion, near-threshold boundary
diagnostics, and public downstream target-selector consumer closure without adding an
unconditional final theorem.
-/
structure ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade : Type where
  finalClosureObligations :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  allTernaryEndpointExhaustion_obligation : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnostics_obligation : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosure_obligation :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade

/-- Build the final public first-bit closure facade from the typed residual facade. -/
def ofTypedFGraphResidualPublicEndpointBundle
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade where
  finalClosureObligations :=
    htyped.toFirstBitPublicFinalClosureObligationPacket hallTernary hnearThreshold
  typedFGraphResidualFacade := htyped
  scalarQuotientPublicEndpoint := htyped.toScalarQuotientPublicEndpointBundle
  typedFGraphResidualTargetSelectorObligations :=
    htyped.toTypedFGraphResidualPublicTargetSelectorObligationPacket
  currentSelectorEndpoint := htyped.currentSelectorEndpoint
  downstreamObligationProjection := htyped.downstreamObligationProjection
  finalReleaseBundleReuse := htyped.finalReleaseBundleReuse
  allTernaryEndpointExhaustion_obligation := hallTernary
  nearThresholdBoundaryDiagnostics_obligation := hnearThreshold
  publicDownstreamTargetSelectorConsumerClosure_obligation :=
    htyped.toPublicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromTypedFGraphResidualFacade :=
    targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle htyped
  targetStatement_fromScalarQuotientPublicEndpoint :=
    htyped.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromAllTernaryEndpointExhaustion :=
    htyped.targetStatement_fromTypedFGraphResidualTargetSelectorObligations
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    htyped.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaPublicDownstreamTargetSelectorConsumerClosure
      htyped
  targetStatement_fromCurrentSelectorEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaCurrentSelectorEndpoint
      htyped
  targetStatement_fromDownstreamObligationProjection :=
    targetStatement_of_proofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle_viaDownstreamObligationProjection
      htyped

/-- Build the final public first-bit closure facade from scalar and typed-residual assumptions. -/
def ofScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade :=
  ofTypedFGraphResidualPublicEndpointBundle
    (h.toTypedFGraphResidualPublicEndpointBundle hresidual) hallTernary hnearThreshold

/-- Recover final closure obligations from the facade. -/
def toFirstBitPublicFinalClosureObligationPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureObligationPacket :=
  h.finalClosureObligations

/-- Recover the typed residual facade from the final public first-bit closure facade. -/
def toTypedFGraphResidualPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualFacade

/-- Recover the scalar-quotient public endpoint from the final public first-bit closure facade. -/
def toScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicEndpoint

/-- Project the all-ternary endpoint exhaustion assumption. -/
def toAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    allTernaryEndpointExhaustion :=
  h.allTernaryEndpointExhaustion_obligation

/-- Project the near-threshold boundary diagnostics assumption. -/
def toNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    nearThresholdBoundaryDiagnostics :=
  h.nearThresholdBoundaryDiagnostics_obligation

/-- Project the downstream target-selector consumer closure assumption. -/
def toPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosure_obligation

/-- Project any final closure row from the final public first-bit closure facade. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow.obligation row :=
  h.finalClosureObligations.obligation row

/-- Select the target-statement facade corresponding to a final closure row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow → TargetStatement
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

@[simp] theorem ofTypedFGraphResidualPublicEndpointBundle_typedFGraphResidualFacade
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    (ofTypedFGraphResidualPublicEndpointBundle htyped hallTernary hnearThreshold).typedFGraphResidualFacade =
      htyped :=
  rfl

@[simp] theorem ofTypedFGraphResidualPublicEndpointBundle_allTernaryEndpointExhaustion
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    (ofTypedFGraphResidualPublicEndpointBundle htyped hallTernary hnearThreshold).allTernaryEndpointExhaustion_obligation =
      hallTernary :=
  rfl

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade

/-- Expose the final public first-bit closure facade from a typed residual endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toFirstBitPublicFinalClosureFacade
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade.ofTypedFGraphResidualPublicEndpointBundle
    h hallTernary hnearThreshold

/-- Expose the final public first-bit closure facade from a scalar-quotient public endpoint. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toFirstBitPublicFinalClosureFacade
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade.ofScalarQuotientPublicEndpointBundle
    h hresidual hallTernary hnearThreshold

/-- The final public first-bit closure facade closes the target by typed residual reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via the scalar-quotient public endpoint row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade via public downstream target-selector consumer closure. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Target-statement facade via current selector endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via downstream target-obligation projection. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaDownstreamObligationProjection
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

/-- Target-statement facade selected by any final closure row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade_viaRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureRow) :
    TargetStatement :=
  h.targetStatementForRow row

/--
Public rows exported by the downstream final-closure handoff.  These rows keep the final
first-bit facade together with the scalar-quotient, typed `F`-residual, current-selector, and
public target-selector closure endpoints needed by downstream proof-md consumers.
-/
inductive ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow : Type where
  | finalClosureFacade
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | downstreamObligationProjection
  | finalReleaseBundleReuse
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow

/-- The endpoint, packet, or assumption selected by a downstream final-closure handoff row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow → Sort _
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .finalReleaseBundleReuse => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow

/--
Downstream handoff bundle for the final public first-bit closure.  It keeps the recently
packaged final closure facade, the all-large typed `F` residual/scalar-quotient endpoints,
near-threshold diagnostics, all-ternary exhaustion, and both public target-selector closure
packets in a single assumption-backed interface.
-/
structure ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle : Type where
  finalClosureFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalReleaseBundleReuse : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromFinalReleaseBundleReuse : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle

/-- Build the downstream final-closure handoff bundle from the final closure facade. -/
def ofFinalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle where
  finalClosureFacade := h
  typedFGraphResidualFacade := h.toTypedFGraphResidualPublicEndpointBundle
  scalarQuotientPublicEndpoint := h.toScalarQuotientPublicEndpointBundle
  finalProofMdConsumerPublicEndpoint :=
    h.typedFGraphResidualFacade.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations :=
    h.scalarQuotientPublicEndpoint.toPublicTargetSelectorObligationPacket
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualTargetSelectorObligations
  currentSelectorEndpoint := h.currentSelectorEndpoint
  downstreamObligationProjection := h.downstreamObligationProjection
  finalReleaseBundleReuse := h.finalReleaseBundleReuse
  allTernaryEndpointExhaustionCert := h.toAllTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert := h.toNearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.toPublicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromFinalClosureFacade :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureFacade h
  targetStatement_fromTypedFGraphResidualFacade :=
    h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint :=
    h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.typedFGraphResidualFacade.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.scalarQuotientPublicEndpoint.targetStatement_fromPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualFacade.targetStatement_fromTypedFGraphResidualTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint :=
    h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromFinalReleaseBundleReuse :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle_viaFinalReleaseEndpoint
      h.typedFGraphResidualFacade.finalProofMdConsumerPublicEndpoint
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Build the handoff bundle directly from a typed `F` residual public endpoint. -/
def ofTypedFGraphResidualPublicEndpointBundle
    (htyped :
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  ofFinalClosureFacade
    (htyped.toFirstBitPublicFinalClosureFacade hallTernary hnearThreshold)

/-- Build the handoff bundle from scalar-quotient and typed residual assumptions. -/
def ofScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  ofFinalClosureFacade
    (h.toFirstBitPublicFinalClosureFacade hresidual hallTernary hnearThreshold)

/-- Recover the final closure facade from the downstream handoff bundle. -/
def toFirstBitPublicFinalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade :=
  h.finalClosureFacade

/-- Recover the typed `F` residual public endpoint from the downstream handoff bundle. -/
def toTypedFGraphResidualPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualFacade

/-- Recover the scalar-quotient public endpoint from the downstream handoff bundle. -/
def toScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicEndpoint

/-- Recover final proof-md/public endpoint reuse from the downstream handoff bundle. -/
def toFinalProofMdConsumerPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.finalProofMdConsumerPublicEndpoint

/-- Recover scalar-quotient public target-selector obligations from the handoff bundle. -/
def toScalarQuotientPublicTargetSelectorObligationPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicTargetSelectorObligations

/-- Recover typed `F` residual public target-selector obligations from the handoff bundle. -/
def toTypedFGraphResidualPublicTargetSelectorObligationPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualPublicTargetSelectorObligations

/-- Recover the current-selector endpoint from the downstream handoff bundle. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover downstream target-obligation projections from the handoff bundle. -/
def toFinalPublicDownstreamTargetObligationLayer
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.downstreamObligationProjection

/-- Recover final-release bundle reuse from the downstream handoff bundle. -/
def toPublicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.finalReleaseBundleReuse

/-- Project the all-ternary endpoint exhaustion assumption from the handoff bundle. -/
def toAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    allTernaryEndpointExhaustion :=
  h.allTernaryEndpointExhaustionCert

/-- Project near-threshold boundary diagnostics from the handoff bundle. -/
def toNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    nearThresholdBoundaryDiagnostics :=
  h.nearThresholdBoundaryDiagnosticsCert

/-- Project the public downstream target-selector consumer closure from the handoff bundle. -/
def toPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Project any public row from the downstream final-closure handoff bundle. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow.obligation row := by
  cases row
  · exact h.finalClosureFacade
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.downstreamObligationProjection
  · exact h.finalReleaseBundleReuse
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a downstream final-closure handoff row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow → TargetStatement
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint =>
      h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .finalReleaseBundleReuse => h.targetStatement_fromFinalReleaseBundleReuse
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The handoff bundle discharges every typed `F` residual public target selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The handoff bundle discharges every scalar-quotient public target selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

@[simp] theorem ofFinalClosureFacade_finalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).finalClosureFacade = h :=
  rfl

@[simp] theorem ofFinalClosureFacade_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).typedFGraphResidualFacade =
      h.toTypedFGraphResidualPublicEndpointBundle :=
  rfl

@[simp] theorem ofFinalClosureFacade_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).scalarQuotientPublicEndpoint =
      h.toScalarQuotientPublicEndpointBundle :=
  rfl

@[simp] theorem ofFinalClosureFacade_typedFGraphResidualPublicTargetSelectorObligations
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).typedFGraphResidualPublicTargetSelectorObligations =
      h.typedFGraphResidualTargetSelectorObligations :=
  rfl

@[simp] theorem ofFinalClosureFacade_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).allTernaryEndpointExhaustionCert =
      h.toAllTernaryEndpointExhaustion :=
  rfl

@[simp] theorem ofFinalClosureFacade_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).nearThresholdBoundaryDiagnosticsCert =
      h.toNearThresholdBoundaryDiagnostics :=
  rfl

@[simp] theorem ofFinalClosureFacade_publicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    (ofFinalClosureFacade h).publicDownstreamTargetSelectorConsumerClosureCert =
      h.toPublicDownstreamTargetSelectorConsumerClosure :=
  rfl

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle

/-- Expose the downstream final-closure handoff bundle from the final closure facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade.toFirstBitPublicFinalClosureHandoffBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.ofFinalClosureFacade h

/-- Expose the downstream final-closure handoff bundle from a typed residual endpoint. -/
def ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle.toFirstBitPublicFinalClosureHandoffBundle
    (h : ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.ofTypedFGraphResidualPublicEndpointBundle
    h hallTernary hnearThreshold

/-- Expose the downstream final-closure handoff bundle from scalar and typed residual assumptions. -/
def ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle.toFirstBitPublicFinalClosureHandoffBundle
    (h : ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers)
    (hresidual :
      ProofMdLargeSupportColoringTypedFGraphResidualAssumptionPacket
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure)
    (hallTernary : allTernaryEndpointExhaustion)
    (hnearThreshold : nearThresholdBoundaryDiagnostics) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.ofScalarQuotientPublicEndpointBundle
    h hresidual hallTernary hnearThreshold

/-- The downstream final-closure handoff closes the target by final closure facade reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromFinalClosureFacade

/-- Target-statement facade via the typed `F` residual endpoint in the handoff bundle. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via typed residual public target-selector closure. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaTypedFGraphResidualPublicTargetSelectors
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations

/-- Target-statement facade via scalar-quotient public target-selector closure. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaScalarQuotientPublicTargetSelectors
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations

/-- Target-statement facade via the current-selector endpoint carried by the handoff. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via downstream target-obligation projections. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaDownstreamObligationProjection
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

/-- Target-statement facade selected by any downstream final-closure handoff row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle_viaRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffRow) :
    TargetStatement :=
  h.targetStatementForRow row

/-!
## Public final-closure release certificate layer

This release-facing layer repackages the final closure handoff as stable rows for downstream
proof-md consumers.  It only projects assumptions and target facades already carried by the handoff.
-/

/--
Rows exported by the public final-closure release certificate.  The rows intentionally mix facade
objects, archive/release endpoints, target-selector packets, current-selector handoffs, and the
remaining diagnostic assumptions so downstream proof-md files can cite a single row selector.
-/
inductive ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow : Type where
  | finalClosureHandoffBundle
  | finalClosureFacade
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow

/-- The endpoint, packet, or assumption selected by a public final-closure release row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow → Sort _
  | .finalClosureHandoffBundle =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow

/--
Final-facing public release certificate facade for first-bit/large-support closure.  It is a pure
projection layer over the downstream final-closure handoff: every endpoint or diagnostic row is either
stored in the handoff or recovered through an existing public endpoint.
-/
structure ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade : Type where
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromFinalClosureHandoff : TargetStatement
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

namespace ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade

/-- Build the public final-closure release certificate facade from the downstream handoff bundle. -/
def ofHandoffBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade where
  finalClosureHandoff := h
  finalClosureFacade := h.toFirstBitPublicFinalClosureFacade
  typedFGraphResidualFacade := h.toTypedFGraphResidualPublicEndpointBundle
  scalarQuotientPublicEndpoint := h.toScalarQuotientPublicEndpointBundle
  finalProofMdConsumerPublicEndpoint := h.toFinalProofMdConsumerPublicEndpointBundle
  scalarQuotientPublicTargetSelectorObligations :=
    h.toScalarQuotientPublicTargetSelectorObligationPacket
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.toTypedFGraphResidualPublicTargetSelectorObligationPacket
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamObligationProjection := h.toFinalPublicDownstreamTargetObligationLayer
  publicFinalArchiveReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :=
    h.finalProofMdConsumerPublicEndpoint.toNoLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse :=
    h.finalProofMdConsumerPublicEndpoint.toPublicReleaseCurrentFrontierCitationBundle
  externalBlockHandoff := h.finalProofMdConsumerPublicEndpoint.toExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert := h.toAllTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert := h.toNearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.toPublicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromFinalClosureHandoff :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle h
  targetStatement_fromFinalClosureFacade := h.targetStatement_fromFinalClosureFacade
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint :=
    h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    targetStatement_of_proofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      h.finalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromFinalReleaseBundleReuse
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint
      h.finalProofMdConsumerPublicEndpoint.toNoLeftoverCurrentFrontierPacket h.currentSelectorEndpoint
  targetStatement_fromPublicCitationCheckpointReuse :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      h.finalProofMdConsumerPublicEndpoint.toPublicReleaseCurrentFrontierCitationBundle
  targetStatement_fromExternalBlockHandoff :=
    targetStatement_of_proofMdLargeSupportColoringExternalBlockHandoffFacade
      h.finalProofMdConsumerPublicEndpoint.toExternalBlockHandoffFacade
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Recover the downstream final-closure handoff bundle from the release certificate facade. -/
def toFirstBitPublicFinalClosureHandoffBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle :=
  h.finalClosureHandoff

/-- Recover the public/final/archive/release bundle from the release certificate facade. -/
def toPublicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicFinalArchiveReleaseBundle

/-- Recover the current selector endpoint from the release certificate facade. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the release certificate facade. -/
def toNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover public citation/checkpoint reuse from the release certificate facade. -/
def toPublicReleaseCurrentFrontierCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicCitationCheckpointReuse

/-- Project any public final-closure release row from the release certificate facade. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow.obligation row := by
  cases row
  · exact h.finalClosureHandoff
  · exact h.finalClosureFacade
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a public final-closure release row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow → TargetStatement
  | .finalClosureHandoffBundle => h.targetStatement_fromFinalClosureHandoff
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint => h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The release certificate facade discharges every typed `F` residual public selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The release certificate facade discharges every scalar-quotient public selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

@[simp] theorem ofHandoffBundle_finalClosureHandoff
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).finalClosureHandoff = h :=
  rfl

@[simp] theorem ofHandoffBundle_finalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).finalClosureFacade = h.toFirstBitPublicFinalClosureFacade :=
  rfl

@[simp] theorem ofHandoffBundle_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).typedFGraphResidualFacade = h.toTypedFGraphResidualPublicEndpointBundle :=
  rfl

@[simp] theorem ofHandoffBundle_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).scalarQuotientPublicEndpoint = h.toScalarQuotientPublicEndpointBundle :=
  rfl

@[simp] theorem ofHandoffBundle_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).currentSelectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ofHandoffBundle_publicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).publicFinalArchiveReleaseBundle = h.toPublicFinalArchiveReleaseBundle :=
  rfl

@[simp] theorem ofHandoffBundle_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).noLeftoverCurrentFrontierPacket =
      h.finalProofMdConsumerPublicEndpoint.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ofHandoffBundle_publicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).publicCitationCheckpointReuse =
      h.finalProofMdConsumerPublicEndpoint.toPublicReleaseCurrentFrontierCitationBundle :=
  rfl

@[simp] theorem ofHandoffBundle_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).allTernaryEndpointExhaustionCert = h.toAllTernaryEndpointExhaustion :=
  rfl

@[simp] theorem ofHandoffBundle_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    (ofHandoffBundle h).nearThresholdBoundaryDiagnosticsCert = h.toNearThresholdBoundaryDiagnostics :=
  rfl

end ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade

/-- Expose the public final-closure release certificate facade from a downstream handoff bundle. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.ofHandoffBundle h

/-- Expose the public final-closure release certificate facade from the final closure facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade.toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.toFirstBitPublicFinalClosureHandoffBundle.toFirstBitPublicFinalClosureReleaseCertificateFacade

/-- The public final-closure release certificate closes the target by handoff reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    TargetStatement :=
  h.targetStatement_fromFinalClosureHandoff

/-- Target-statement facade via the archive/release bundle row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade_viaPublicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    TargetStatement :=
  h.targetStatement_fromPublicFinalArchiveReleaseBundle

/-- Target-statement facade via selector-current-frontier packet reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade_viaNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- Target-statement facade selected by any public final-closure release row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade_viaRow
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade)
    (row : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseRow) :
    TargetStatement :=
  h.targetStatementForRow row

/--
Downstream selector/current-frontier handoff facade extracted from the final release certificate.  It
keeps the current selector endpoint adjacent to the no-leftover/current-frontier packet and public
citation checkpoint while reusing the archive/release bundle and downstream target obligations.
-/
structure ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade : Type where
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  targetStatement_fromSelectorCurrentFrontier : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement

namespace ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade

/-- Build the selector/current-frontier handoff facade from a public release certificate. -/
def ofReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade where
  releaseCertificateFacade := h
  finalClosureHandoff := h.toFirstBitPublicFinalClosureHandoffBundle
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  targetStatement_fromSelectorCurrentFrontier :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint_viaExternalBlock
      h.noLeftoverCurrentFrontierPacket h.currentSelectorEndpoint
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection

/-- Build the selector/current-frontier handoff facade directly from the final-closure handoff. -/
def ofHandoffBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  ofReleaseCertificateFacade h.toFirstBitPublicFinalClosureReleaseCertificateFacade

/-- Recover the public release certificate facade from the selector/current-frontier handoff. -/
def toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.releaseCertificateFacade

/-- Recover the current selector endpoint from the selector/current-frontier handoff. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the no-leftover/current-frontier packet from the selector/current-frontier handoff. -/
def toNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

@[simp] theorem ofReleaseCertificateFacade_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).currentSelectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).noLeftoverCurrentFrontierPacket =
      h.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_publicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).publicFinalArchiveReleaseBundle =
      h.toPublicFinalArchiveReleaseBundle :=
  rfl

end ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade

/-- Expose the selector/current-frontier handoff facade from the public release certificate. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.ofReleaseCertificateFacade h

/-- Expose the selector/current-frontier handoff facade from the downstream final-closure handoff. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.ofHandoffBundle h

/-- The selector/current-frontier handoff closes the target by current selector and frontier reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontier

/-- The selector/current-frontier handoff closes the external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade_viaExternalBlock
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierExternalBlock

/-- The selector/current-frontier handoff closes the target through public citation/checkpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade_viaPublicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-!
## Final release checkpoint consumer layer

This checkpoint layer is intentionally a facade: it records the already assumption-backed
final-release certificate and the selector/current-frontier handoff side-by-side, then normalizes the
typed residual, scalar quotient, ternary-exhaustion, near-threshold, downstream-selector, and current
selector endpoints for proof-md consumers.
-/

/--
Final-facing checkpoint certificate for downstream proof-md release consumers.  It keeps the public
final-closure release facade adjacent to the selector/current-frontier handoff and re-exports every
typed residual, scalar quotient, diagnostic, selector, and archive/release endpoint used by the last
first-bit facade layer.
-/
structure ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate : Type where
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  selectorCurrentFrontierHandoff :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  downstreamSelectorObligations : FirstBitCurrentSelectorAssumptions
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromFinalClosureHandoff : TargetStatement
  targetStatement_fromReleaseCertificateFacade : TargetStatement
  targetStatement_fromSelectorCurrentFrontier : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

/-- Rows exported by the final release checkpoint certificate. -/
inductive ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow : Type where
  | checkpointCertificate
  | releaseCertificateFacade
  | selectorCurrentFrontierHandoff
  | finalClosureHandoff
  | finalClosureFacade
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow

/-- The endpoint, packet, or assumption selected by a final release checkpoint row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow → Sort _
  | .checkpointCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  | .releaseCertificateFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  | .selectorCurrentFrontierHandoff =>
      ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  | .finalClosureHandoff =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow

namespace ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate

/-- Build the final release checkpoint certificate from the public final-closure release facade. -/
def ofReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate where
  releaseCertificateFacade := h
  selectorCurrentFrontierHandoff := h.toDownstreamSelectorCurrentFrontierHandoffFacade
  finalClosureHandoff := h.toFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade := h.finalClosureFacade
  typedFGraphResidualFacade := h.typedFGraphResidualFacade
  scalarQuotientPublicEndpoint := h.scalarQuotientPublicEndpoint
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations :=
    h.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualPublicTargetSelectorObligations
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamSelectorObligations := h.toCurrentSelectorEndpoint.toCurrentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.toPublicReleaseCurrentFrontierCitationBundle
  externalBlockHandoff := h.externalBlockHandoff
  allTernaryEndpointExhaustionCert := h.allTernaryEndpointExhaustionCert
  nearThresholdBoundaryDiagnosticsCert := h.nearThresholdBoundaryDiagnosticsCert
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.publicDownstreamTargetSelectorConsumerClosureCert
  targetStatement_fromFinalClosureHandoff := h.targetStatement_fromFinalClosureHandoff
  targetStatement_fromReleaseCertificateFacade :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
      h
  targetStatement_fromSelectorCurrentFrontier :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
      h.toDownstreamSelectorCurrentFrontierHandoffFacade
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade_viaExternalBlock
      h.toDownstreamSelectorCurrentFrontierHandoffFacade
  targetStatement_fromFinalClosureFacade := h.targetStatement_fromFinalClosureFacade
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint := h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff := h.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Build the final release checkpoint certificate from the selector/current-frontier handoff. -/
def ofSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate where
  releaseCertificateFacade := h.releaseCertificateFacade
  selectorCurrentFrontierHandoff := h
  finalClosureHandoff := h.finalClosureHandoff
  finalClosureFacade := h.releaseCertificateFacade.finalClosureFacade
  typedFGraphResidualFacade := h.releaseCertificateFacade.typedFGraphResidualFacade
  scalarQuotientPublicEndpoint := h.releaseCertificateFacade.scalarQuotientPublicEndpoint
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations :=
    h.releaseCertificateFacade.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.releaseCertificateFacade.typedFGraphResidualPublicTargetSelectorObligations
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  downstreamSelectorObligations := h.toCurrentSelectorEndpoint.toCurrentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.publicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.toNoLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.publicCitationCheckpointReuse
  externalBlockHandoff := h.releaseCertificateFacade.externalBlockHandoff
  allTernaryEndpointExhaustionCert :=
    h.releaseCertificateFacade.allTernaryEndpointExhaustionCert
  nearThresholdBoundaryDiagnosticsCert :=
    h.releaseCertificateFacade.nearThresholdBoundaryDiagnosticsCert
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.releaseCertificateFacade.publicDownstreamTargetSelectorConsumerClosureCert
  targetStatement_fromFinalClosureHandoff :=
    h.releaseCertificateFacade.targetStatement_fromFinalClosureHandoff
  targetStatement_fromReleaseCertificateFacade :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
      h.releaseCertificateFacade
  targetStatement_fromSelectorCurrentFrontier :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
      h
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade_viaExternalBlock
      h
  targetStatement_fromFinalClosureFacade :=
    h.releaseCertificateFacade.targetStatement_fromFinalClosureFacade
  targetStatement_fromTypedFGraphResidualFacade :=
    h.releaseCertificateFacade.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint :=
    h.releaseCertificateFacade.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.releaseCertificateFacade.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.releaseCertificateFacade.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.releaseCertificateFacade.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint :=
    h.releaseCertificateFacade.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.releaseCertificateFacade.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    targetStatement_of_proofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket_and_currentSelectorEndpoint
      h.noLeftoverCurrentFrontierPacket h.currentSelectorEndpoint
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff :=
    h.releaseCertificateFacade.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.releaseCertificateFacade.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.releaseCertificateFacade.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.releaseCertificateFacade.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Recover the public final-closure release certificate facade from the checkpoint. -/
def toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.releaseCertificateFacade

/-- Recover the selector/current-frontier handoff from the checkpoint. -/
def toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  h.selectorCurrentFrontierHandoff

/-- Recover the typed `F` residual public endpoint from the checkpoint. -/
def toTypedFGraphResidualPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualFacade

/-- Recover the scalar-quotient public endpoint from the checkpoint. -/
def toScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicEndpoint

/-- Recover the current selector endpoint from the checkpoint. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the current first-bit selector assumptions from the checkpoint. -/
def toCurrentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    FirstBitCurrentSelectorAssumptions :=
  h.downstreamSelectorObligations

/-- Recover final-release bundle reuse from the checkpoint. -/
def toPublicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicFinalArchiveReleaseBundle

/-- Project all-ternary endpoint exhaustion from the checkpoint. -/
def toAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    allTernaryEndpointExhaustion :=
  h.allTernaryEndpointExhaustionCert

/-- Project near-threshold boundary diagnostics from the checkpoint. -/
def toNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    nearThresholdBoundaryDiagnostics :=
  h.nearThresholdBoundaryDiagnosticsCert

/-- Project public downstream target-selector consumer closure from the checkpoint. -/
def toPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Project any final release checkpoint row from the checkpoint certificate. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow.obligation row := by
  cases row
  · exact h
  · exact h.releaseCertificateFacade
  · exact h.selectorCurrentFrontierHandoff
  · exact h.finalClosureHandoff
  · exact h.finalClosureFacade
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a final release checkpoint row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow → TargetStatement
  | .checkpointCertificate => h.targetStatement_fromReleaseCertificateFacade
  | .releaseCertificateFacade => h.targetStatement_fromReleaseCertificateFacade
  | .selectorCurrentFrontierHandoff => h.targetStatement_fromSelectorCurrentFrontier
  | .finalClosureHandoff => h.targetStatement_fromFinalClosureHandoff
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint =>
      h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The checkpoint certificate discharges every typed `F` residual public target selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The checkpoint certificate discharges every scalar-quotient public target selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

@[simp] theorem ofReleaseCertificateFacade_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).releaseCertificateFacade = h :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).selectorCurrentFrontierHandoff =
      h.toDownstreamSelectorCurrentFrontierHandoffFacade :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).typedFGraphResidualFacade = h.typedFGraphResidualFacade :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).scalarQuotientPublicEndpoint =
      h.scalarQuotientPublicEndpoint :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).currentSelectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_downstreamSelectorObligations
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).downstreamSelectorObligations =
      h.toCurrentSelectorEndpoint.toCurrentSelectorAssumptions :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).allTernaryEndpointExhaustionCert =
      h.allTernaryEndpointExhaustionCert :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).nearThresholdBoundaryDiagnosticsCert =
      h.nearThresholdBoundaryDiagnosticsCert :=
  rfl

@[simp] theorem ofReleaseCertificateFacade_publicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    (ofReleaseCertificateFacade h).publicDownstreamTargetSelectorConsumerClosureCert =
      h.publicDownstreamTargetSelectorConsumerClosureCert :=
  rfl

@[simp] theorem ofSelectorCurrentFrontierHandoffFacade_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    (ofSelectorCurrentFrontierHandoffFacade h).selectorCurrentFrontierHandoff = h :=
  rfl

@[simp] theorem ofSelectorCurrentFrontierHandoffFacade_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    (ofSelectorCurrentFrontierHandoffFacade h).releaseCertificateFacade =
      h.releaseCertificateFacade :=
  rfl

@[simp] theorem ofSelectorCurrentFrontierHandoffFacade_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    (ofSelectorCurrentFrontierHandoffFacade h).currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ofSelectorCurrentFrontierHandoffFacade_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    (ofSelectorCurrentFrontierHandoffFacade h).noLeftoverCurrentFrontierPacket =
      h.toNoLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ofSelectorCurrentFrontierHandoffFacade_publicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    (ofSelectorCurrentFrontierHandoffFacade h).publicFinalArchiveReleaseBundle =
      h.publicFinalArchiveReleaseBundle :=
  rfl

end ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate

/-- Expose the final release checkpoint certificate from the public release certificate. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.ofReleaseCertificateFacade h

/-- Expose the final release checkpoint certificate from the selector/current-frontier handoff. -/
def ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.ofSelectorCurrentFrontierHandoffFacade
    h

/-- Expose the final release checkpoint certificate from the downstream final-closure handoff. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle.toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  h.toFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate

/-- Expose the final release checkpoint certificate from the final closure facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade.toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  h.toFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate

/-- The final release checkpoint closes the target by release-certificate reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromReleaseCertificateFacade

/-- Target-statement facade via selector/current-frontier reuse in the checkpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaSelectorCurrentFrontier
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontier

/-- Target-statement facade via the selector/current-frontier external-block route. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaSelectorCurrentFrontierExternalBlock
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierExternalBlock

/-- Target-statement facade via typed `F` residual endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via the current selector endpoint carried by the checkpoint. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via the final public downstream target-obligation layer. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaDownstreamObligationProjection
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromDownstreamObligationProjection

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade via public downstream target-selector consumer closure. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Target-statement facade selected by any final release checkpoint row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalReleaseCheckpointCertificate.currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalReleaseCheckpointCertificate.typedFGraphResidualFacade =
      h.typedFGraphResidualFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointCertificate_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalReleaseCheckpointCertificate.scalarQuotientPublicEndpoint =
      h.scalarQuotientPublicEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleaseCheckpointCertificate_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    h.toFirstBitFinalReleaseCheckpointCertificate.currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleaseCheckpointCertificate_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    h.toFirstBitFinalReleaseCheckpointCertificate.selectorCurrentFrontierHandoff = h :=
  rfl

/--
Final-facing consumer bundle one step beyond the first-bit final release checkpoint certificate.
It keeps the checkpoint as the source of target closure while spelling out the release, handoff,
typed-`F` residual, scalar quotient, all-ternary, near-threshold, downstream-selector, and
current-selector endpoints that downstream proof-md consumers cite after the checkpoint.
-/
structure ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle : Type where
  checkpointCertificate : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  selectorCurrentFrontierHandoff :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  currentSelectorAssumptions : FirstBitCurrentSelectorAssumptions
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromCheckpointCertificate : TargetStatement
  targetStatement_fromReleaseCertificateFacade : TargetStatement
  targetStatement_fromSelectorCurrentFrontierHandoff : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

/-- Rows exported by the post-checkpoint final release consumer bundle. -/
inductive ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow : Type where
  | consumerBundle
  | checkpointCertificate
  | releaseCertificateFacade
  | finalClosureHandoff
  | selectorCurrentFrontierHandoff
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | currentSelectorAssumptions
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow

/-- The endpoint, packet, or assumption selected by a post-checkpoint consumer row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow → Sort _
  | .consumerBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  | .checkpointCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  | .releaseCertificateFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  | .finalClosureHandoff =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .selectorCurrentFrontierHandoff =>
      ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .currentSelectorAssumptions => FirstBitCurrentSelectorAssumptions
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow

namespace ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle

/-- Build the post-checkpoint consumer bundle from the final release checkpoint certificate. -/
def ofCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle where
  checkpointCertificate := h
  releaseCertificateFacade := h.toFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff := h.finalClosureHandoff
  selectorCurrentFrontierHandoff := h.toDownstreamSelectorCurrentFrontierHandoffFacade
  typedFGraphResidualFacade := h.toTypedFGraphResidualPublicEndpointBundle
  scalarQuotientPublicEndpoint := h.toScalarQuotientPublicEndpointBundle
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations := h.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualPublicTargetSelectorObligations
  currentSelectorEndpoint := h.toCurrentSelectorEndpoint
  currentSelectorAssumptions := h.toCurrentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.toPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.publicCitationCheckpointReuse
  externalBlockHandoff := h.externalBlockHandoff
  allTernaryEndpointExhaustionCert := h.toAllTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert := h.toNearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.toPublicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromCheckpointCertificate :=
    targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate h
  targetStatement_fromReleaseCertificateFacade := h.targetStatement_fromReleaseCertificateFacade
  targetStatement_fromSelectorCurrentFrontierHandoff :=
    h.targetStatement_fromSelectorCurrentFrontier
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    h.targetStatement_fromSelectorCurrentFrontierExternalBlock
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint :=
    h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff := h.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Build the post-checkpoint consumer bundle from the public release certificate facade. -/
def ofReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  ofCheckpointCertificate h.toFirstBitFinalReleaseCheckpointCertificate

/-- Build the post-checkpoint consumer bundle from the selector/current-frontier handoff. -/
def ofSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  ofCheckpointCertificate h.toFirstBitFinalReleaseCheckpointCertificate

/-- Recover the checkpoint certificate from the post-checkpoint consumer bundle. -/
def toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  h.checkpointCertificate

/-- Recover the public final-closure release certificate facade from the consumer bundle. -/
def toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.releaseCertificateFacade

/-- Recover the selector/current-frontier handoff from the consumer bundle. -/
def toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  h.selectorCurrentFrontierHandoff

/-- Recover the current selector endpoint from the consumer bundle. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover current selector assumptions from the consumer bundle. -/
def toCurrentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorAssumptions

/-- Project any post-checkpoint consumer row from the consumer bundle. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow.obligation row := by
  cases row
  · exact h
  · exact h.checkpointCertificate
  · exact h.releaseCertificateFacade
  · exact h.finalClosureHandoff
  · exact h.selectorCurrentFrontierHandoff
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.currentSelectorAssumptions
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a post-checkpoint consumer row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow → TargetStatement
  | .consumerBundle => h.targetStatement_fromCheckpointCertificate
  | .checkpointCertificate => h.targetStatement_fromCheckpointCertificate
  | .releaseCertificateFacade => h.targetStatement_fromReleaseCertificateFacade
  | .finalClosureHandoff => h.targetStatement_fromCheckpointCertificate
  | .selectorCurrentFrontierHandoff => h.targetStatement_fromSelectorCurrentFrontierHandoff
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint => h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .currentSelectorAssumptions => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The post-checkpoint consumer bundle discharges every typed `F` residual public selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The post-checkpoint consumer bundle discharges every scalar-quotient public selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

/-- The post-checkpoint consumer bundle closes the target by checkpoint reuse. -/
theorem targetStatement
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromCheckpointCertificate

/-- Target-statement facade via selector/current-frontier handoff reuse. -/
theorem targetStatement_viaSelectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierHandoff

/-- Target-statement facade via the selector/current-frontier external-block route. -/
theorem targetStatement_viaSelectorCurrentFrontierExternalBlock
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierExternalBlock

/-- Target-statement facade via typed `F` residual endpoint reuse. -/
theorem targetStatement_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade selected by any post-checkpoint consumer row. -/
theorem targetStatement_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ofCheckpointCertificate_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).checkpointCertificate = h :=
  rfl

@[simp] theorem ofCheckpointCertificate_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).releaseCertificateFacade =
      h.toFirstBitPublicFinalClosureReleaseCertificateFacade :=
  rfl

@[simp] theorem ofCheckpointCertificate_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).selectorCurrentFrontierHandoff =
      h.toDownstreamSelectorCurrentFrontierHandoffFacade :=
  rfl

@[simp] theorem ofCheckpointCertificate_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).typedFGraphResidualFacade =
      h.toTypedFGraphResidualPublicEndpointBundle :=
  rfl

@[simp] theorem ofCheckpointCertificate_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).scalarQuotientPublicEndpoint =
      h.toScalarQuotientPublicEndpointBundle :=
  rfl

@[simp] theorem ofCheckpointCertificate_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).currentSelectorEndpoint = h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ofCheckpointCertificate_currentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).currentSelectorAssumptions =
      h.toCurrentSelectorAssumptions :=
  rfl

@[simp] theorem ofCheckpointCertificate_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).allTernaryEndpointExhaustionCert =
      h.toAllTernaryEndpointExhaustion :=
  rfl

@[simp] theorem ofCheckpointCertificate_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    (ofCheckpointCertificate h).nearThresholdBoundaryDiagnosticsCert =
      h.toNearThresholdBoundaryDiagnostics :=
  rfl

end ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle

/-- Expose the post-checkpoint consumer bundle from the final release checkpoint certificate. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleaseCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.ofCheckpointCertificate h

/-- Expose the post-checkpoint consumer bundle from the public release certificate facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.ofReleaseCertificateFacade h

/-- Expose the post-checkpoint consumer bundle from the selector/current-frontier handoff facade. -/
def ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleaseCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.ofSelectorCurrentFrontierHandoffFacade h

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleaseCheckpointConsumerBundle_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalReleaseCheckpointConsumerBundle.currentSelectorEndpoint =
      h.toCurrentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleaseCheckpointConsumerBundle_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalReleaseCheckpointConsumerBundle.releaseCertificateFacade =
      h.toFirstBitPublicFinalClosureReleaseCertificateFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleaseCheckpointConsumerBundle_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalReleaseCheckpointConsumerBundle.checkpointCertificate =
      h.toFirstBitFinalReleaseCheckpointCertificate :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleaseCheckpointConsumerBundle_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    h.toFirstBitFinalReleaseCheckpointConsumerBundle.selectorCurrentFrontierHandoff = h :=
  rfl

/-- Final proof-md citation bundle exported after the checkpoint consumer bundle.

This layer is intentionally a consumer/citation facade: it republishes the checkpoint consumer
rows, the final-closure facade hidden inside the checkpoint certificate, and the target-statement
facades downstream proof-md files cite after the first-bit checkpoint release.
-/
structure ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle : Type where
  consumerBundle : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  checkpointCertificate : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  selectorCurrentFrontierHandoff :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  currentSelectorAssumptions : FirstBitCurrentSelectorAssumptions
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromConsumerBundle : TargetStatement
  targetStatement_fromCheckpointCertificate : TargetStatement
  targetStatement_fromReleaseCertificateFacade : TargetStatement
  targetStatement_fromFinalClosureHandoff : TargetStatement
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromSelectorCurrentFrontierHandoff : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

/-- Citation rows exported by the final post-checkpoint bundle. -/
inductive ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow : Type where
  | citationBundle
  | consumerBundle
  | checkpointCertificate
  | releaseCertificateFacade
  | finalClosureHandoff
  | finalClosureFacade
  | selectorCurrentFrontierHandoff
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | currentSelectorAssumptions
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow

/-- The endpoint, packet, facade, or assumption selected by a post-checkpoint citation row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow → Sort _
  | .citationBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
  | .consumerBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  | .checkpointCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  | .releaseCertificateFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  | .finalClosureHandoff =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .selectorCurrentFrontierHandoff =>
      ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .currentSelectorAssumptions => FirstBitCurrentSelectorAssumptions
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow

namespace ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle

/-- Build the final proof-md citation bundle from the checkpoint consumer bundle. -/
def ofConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle where
  consumerBundle := h
  checkpointCertificate := h.checkpointCertificate
  releaseCertificateFacade := h.releaseCertificateFacade
  finalClosureHandoff := h.finalClosureHandoff
  finalClosureFacade := h.checkpointCertificate.finalClosureFacade
  selectorCurrentFrontierHandoff := h.selectorCurrentFrontierHandoff
  typedFGraphResidualFacade := h.typedFGraphResidualFacade
  scalarQuotientPublicEndpoint := h.scalarQuotientPublicEndpoint
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations :=
    h.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualPublicTargetSelectorObligations
  currentSelectorEndpoint := h.currentSelectorEndpoint
  currentSelectorAssumptions := h.currentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.publicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.publicCitationCheckpointReuse
  externalBlockHandoff := h.externalBlockHandoff
  allTernaryEndpointExhaustionCert := h.allTernaryEndpointExhaustionCert
  nearThresholdBoundaryDiagnosticsCert := h.nearThresholdBoundaryDiagnosticsCert
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.publicDownstreamTargetSelectorConsumerClosureCert
  targetStatement_fromConsumerBundle :=
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.targetStatement h
  targetStatement_fromCheckpointCertificate := h.targetStatement_fromCheckpointCertificate
  targetStatement_fromReleaseCertificateFacade := h.targetStatement_fromReleaseCertificateFacade
  targetStatement_fromFinalClosureHandoff :=
    h.checkpointCertificate.targetStatement_fromFinalClosureHandoff
  targetStatement_fromFinalClosureFacade :=
    h.checkpointCertificate.targetStatement_fromFinalClosureFacade
  targetStatement_fromSelectorCurrentFrontierHandoff :=
    h.targetStatement_fromSelectorCurrentFrontierHandoff
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    h.targetStatement_fromSelectorCurrentFrontierExternalBlock
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint :=
    h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff := h.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Build the final proof-md citation bundle from the final release checkpoint certificate. -/
def ofCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ofConsumerBundle h.toFirstBitFinalReleaseCheckpointConsumerBundle

/-- Build the final proof-md citation bundle from the public release certificate facade. -/
def ofReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ofConsumerBundle h.toFirstBitFinalReleaseCheckpointConsumerBundle

/-- Build the final proof-md citation bundle from the selector/current-frontier handoff. -/
def ofSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ofConsumerBundle h.toFirstBitFinalReleaseCheckpointConsumerBundle

/-- Recover the checkpoint consumer bundle from the final citation bundle. -/
def toFirstBitFinalReleaseCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  h.consumerBundle

/-- Recover the final release checkpoint certificate from the final citation bundle. -/
def toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  h.checkpointCertificate

/-- Recover the public release certificate facade from the final citation bundle. -/
def toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.releaseCertificateFacade

/-- Recover the hidden final-closure facade from the final citation bundle. -/
def toFirstBitPublicFinalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade :=
  h.finalClosureFacade

/-- Recover the selector/current-frontier handoff from the final citation bundle. -/
def toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  h.selectorCurrentFrontierHandoff

/-- Recover the current selector endpoint from the final citation bundle. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover current selector assumptions from the final citation bundle. -/
def toCurrentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorAssumptions

/-- Project any final post-checkpoint citation row from the citation bundle. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow.obligation row := by
  cases row
  · exact h
  · exact h.consumerBundle
  · exact h.checkpointCertificate
  · exact h.releaseCertificateFacade
  · exact h.finalClosureHandoff
  · exact h.finalClosureFacade
  · exact h.selectorCurrentFrontierHandoff
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.currentSelectorAssumptions
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a final post-checkpoint citation row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow → TargetStatement
  | .citationBundle => h.targetStatement_fromConsumerBundle
  | .consumerBundle => h.targetStatement_fromConsumerBundle
  | .checkpointCertificate => h.targetStatement_fromCheckpointCertificate
  | .releaseCertificateFacade => h.targetStatement_fromReleaseCertificateFacade
  | .finalClosureHandoff => h.targetStatement_fromFinalClosureHandoff
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .selectorCurrentFrontierHandoff => h.targetStatement_fromSelectorCurrentFrontierHandoff
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint => h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .currentSelectorAssumptions => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The final citation bundle discharges every typed `F` residual public selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The final citation bundle discharges every scalar-quotient public selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

/-- The final citation bundle closes the target through the checkpoint consumer bundle. -/
theorem targetStatement
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromConsumerBundle

/-- Target-statement facade via final release checkpoint reuse. -/
theorem targetStatement_viaCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromCheckpointCertificate

/-- Target-statement facade via public final-closure release certificate reuse. -/
theorem targetStatement_viaReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromReleaseCertificateFacade

/-- Target-statement facade via final-closure handoff reuse. -/
theorem targetStatement_viaFinalClosureHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromFinalClosureHandoff

/-- Target-statement facade via final-closure facade reuse. -/
theorem targetStatement_viaFinalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromFinalClosureFacade

/-- Target-statement facade via selector/current-frontier handoff reuse. -/
theorem targetStatement_viaSelectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierHandoff

/-- Target-statement facade via selector/current-frontier external-block reuse. -/
theorem targetStatement_viaSelectorCurrentFrontierExternalBlock
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierExternalBlock

/-- Target-statement facade via typed `F` residual endpoint reuse. -/
theorem targetStatement_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via current-selector endpoint reuse. -/
theorem targetStatement_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via no-leftover/current-frontier packet reuse. -/
theorem targetStatement_viaNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- Target-statement facade via public current-frontier citation reuse. -/
theorem targetStatement_viaPublicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- Target-statement facade via external-block handoff reuse. -/
theorem targetStatement_viaExternalBlockHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromExternalBlockHandoff

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade via public downstream target-selector consumer closure. -/
theorem targetStatement_viaPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Target-statement facade selected by any final post-checkpoint citation row. -/
theorem targetStatement_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ofConsumerBundle_consumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).consumerBundle = h :=
  rfl

@[simp] theorem ofConsumerBundle_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).checkpointCertificate = h.checkpointCertificate :=
  rfl

@[simp] theorem ofConsumerBundle_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).releaseCertificateFacade = h.releaseCertificateFacade :=
  rfl

@[simp] theorem ofConsumerBundle_finalClosureHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).finalClosureHandoff = h.finalClosureHandoff :=
  rfl

@[simp] theorem ofConsumerBundle_finalClosureFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).finalClosureFacade = h.checkpointCertificate.finalClosureFacade :=
  rfl

@[simp] theorem ofConsumerBundle_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).selectorCurrentFrontierHandoff =
      h.selectorCurrentFrontierHandoff :=
  rfl

@[simp] theorem ofConsumerBundle_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).typedFGraphResidualFacade = h.typedFGraphResidualFacade :=
  rfl

@[simp] theorem ofConsumerBundle_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).scalarQuotientPublicEndpoint = h.scalarQuotientPublicEndpoint :=
  rfl

@[simp] theorem ofConsumerBundle_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).currentSelectorEndpoint = h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ofConsumerBundle_currentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).currentSelectorAssumptions = h.currentSelectorAssumptions :=
  rfl

@[simp] theorem ofConsumerBundle_publicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).publicCitationCheckpointReuse = h.publicCitationCheckpointReuse :=
  rfl

@[simp] theorem ofConsumerBundle_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).allTernaryEndpointExhaustionCert =
      h.allTernaryEndpointExhaustionCert :=
  rfl

@[simp] theorem ofConsumerBundle_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    (ofConsumerBundle h).nearThresholdBoundaryDiagnosticsCert =
      h.nearThresholdBoundaryDiagnosticsCert :=
  rfl

end ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle

/-- Expose the final post-checkpoint citation bundle from the checkpoint consumer bundle. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.ofConsumerBundle h

/-- Expose the final post-checkpoint citation bundle from the final release checkpoint certificate. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.ofCheckpointCertificate h

/-- Expose the final post-checkpoint citation bundle from the public release certificate facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.ofReleaseCertificateFacade h

/-- Expose the final post-checkpoint citation bundle from the selector/current-frontier handoff. -/
def ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.ofSelectorCurrentFrontierHandoffFacade h

/-- Downstream proof-md target citation through the final post-checkpoint bundle. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    TargetStatement :=
  ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.targetStatement h

/-- Downstream proof-md target citation selected by any post-checkpoint citation row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalReleasePostCheckpointCitationBundle_consumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.consumerBundle = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalReleasePostCheckpointCitationBundle_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.checkpointCertificate =
      h.checkpointCertificate :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleasePostCheckpointCitationBundle_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.checkpointCertificate = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalReleasePostCheckpointCitationBundle_consumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.consumerBundle =
      h.toFirstBitFinalReleaseCheckpointConsumerBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalReleasePostCheckpointCitationBundle_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.releaseCertificateFacade = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalReleasePostCheckpointCitationBundle_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    h.toFirstBitFinalReleasePostCheckpointCitationBundle.selectorCurrentFrontierHandoff = h :=
  rfl

/--
Final-facing first-bit citation consumer certificate exported after the post-checkpoint proof-md
citation bundle.  The certificate is deliberately redundant: downstream files can cite one
assumption-backed object while still projecting the checkpoint consumer, release certificate,
selector/current-frontier handoff, typed-`F` residual endpoint, scalar quotient endpoint,
diagnostic endpoints, no-leftover frontier packet, and current-selector endpoints.
-/
structure ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate : Type where
  postCheckpointCitationBundle :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
  checkpointConsumerBundle :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  checkpointCertificate : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  selectorCurrentFrontierHandoff :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  currentSelectorAssumptions : FirstBitCurrentSelectorAssumptions
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromPostCheckpointCitationBundle : TargetStatement
  targetStatement_fromCheckpointConsumerBundle : TargetStatement
  targetStatement_fromCheckpointCertificate : TargetStatement
  targetStatement_fromReleaseCertificateFacade : TargetStatement
  targetStatement_fromFinalClosureHandoff : TargetStatement
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromSelectorCurrentFrontierHandoff : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

/-- Rows exported by the final first-bit citation consumer certificate. -/
inductive ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow : Type where
  | citationConsumerCertificate
  | postCheckpointCitationBundle
  | checkpointConsumerBundle
  | checkpointCertificate
  | releaseCertificateFacade
  | finalClosureHandoff
  | finalClosureFacade
  | selectorCurrentFrontierHandoff
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | currentSelectorEndpoint
  | currentSelectorAssumptions
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow

/-- The endpoint, packet, facade, or assumption selected by a final citation consumer row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow → Sort _
  | .citationConsumerCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate
  | .postCheckpointCitationBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
  | .checkpointConsumerBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  | .checkpointCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  | .releaseCertificateFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  | .finalClosureHandoff =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .selectorCurrentFrontierHandoff =>
      ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .currentSelectorAssumptions => FirstBitCurrentSelectorAssumptions
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow

namespace ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate

/-- Build the final citation consumer certificate from the post-checkpoint citation bundle. -/
def ofPostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate where
  postCheckpointCitationBundle := h
  checkpointConsumerBundle := h.consumerBundle
  checkpointCertificate := h.checkpointCertificate
  releaseCertificateFacade := h.releaseCertificateFacade
  finalClosureHandoff := h.finalClosureHandoff
  finalClosureFacade := h.finalClosureFacade
  selectorCurrentFrontierHandoff := h.selectorCurrentFrontierHandoff
  typedFGraphResidualFacade := h.typedFGraphResidualFacade
  scalarQuotientPublicEndpoint := h.scalarQuotientPublicEndpoint
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations := h.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualPublicTargetSelectorObligations
  currentSelectorEndpoint := h.currentSelectorEndpoint
  currentSelectorAssumptions := h.currentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.publicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.publicCitationCheckpointReuse
  externalBlockHandoff := h.externalBlockHandoff
  allTernaryEndpointExhaustionCert := h.allTernaryEndpointExhaustionCert
  nearThresholdBoundaryDiagnosticsCert := h.nearThresholdBoundaryDiagnosticsCert
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.publicDownstreamTargetSelectorConsumerClosureCert
  targetStatement_fromPostCheckpointCitationBundle :=
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.targetStatement h
  targetStatement_fromCheckpointConsumerBundle :=
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.targetStatement
      h.consumerBundle
  targetStatement_fromCheckpointCertificate := h.targetStatement_fromCheckpointCertificate
  targetStatement_fromReleaseCertificateFacade := h.targetStatement_fromReleaseCertificateFacade
  targetStatement_fromFinalClosureHandoff := h.targetStatement_fromFinalClosureHandoff
  targetStatement_fromFinalClosureFacade := h.targetStatement_fromFinalClosureFacade
  targetStatement_fromSelectorCurrentFrontierHandoff :=
    h.targetStatement_fromSelectorCurrentFrontierHandoff
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    h.targetStatement_fromSelectorCurrentFrontierExternalBlock
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint := h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff := h.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Build the final citation consumer certificate from the checkpoint consumer bundle. -/
def ofCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ofPostCheckpointCitationBundle h.toFirstBitFinalReleasePostCheckpointCitationBundle

/-- Build the final citation consumer certificate from the final release checkpoint certificate. -/
def ofCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ofPostCheckpointCitationBundle h.toFirstBitFinalReleasePostCheckpointCitationBundle

/-- Build the final citation consumer certificate from the public release certificate facade. -/
def ofReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ofPostCheckpointCitationBundle h.toFirstBitFinalReleasePostCheckpointCitationBundle

/-- Build the final citation consumer certificate from the selector/current-frontier handoff. -/
def ofSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ofPostCheckpointCitationBundle h.toFirstBitFinalReleasePostCheckpointCitationBundle

/-- Recover the post-checkpoint citation bundle from the final citation consumer certificate. -/
def toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  h.postCheckpointCitationBundle

/-- Recover the checkpoint consumer bundle from the final citation consumer certificate. -/
def toFirstBitFinalReleaseCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle :=
  h.checkpointConsumerBundle

/-- Recover the final release checkpoint certificate from the final citation consumer certificate. -/
def toFirstBitFinalReleaseCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate :=
  h.checkpointCertificate

/-- Recover the public release certificate facade from the final citation consumer certificate. -/
def toFirstBitPublicFinalClosureReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade :=
  h.releaseCertificateFacade

/-- Recover the selector/current-frontier handoff from the final citation consumer certificate. -/
def toDownstreamSelectorCurrentFrontierHandoffFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade :=
  h.selectorCurrentFrontierHandoff

/-- Recover the typed `F` residual public endpoint from the final citation consumer certificate. -/
def toTypedFGraphResidualPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure :=
  h.typedFGraphResidualFacade

/-- Recover the scalar-quotient public endpoint from the final citation consumer certificate. -/
def toScalarQuotientPublicEndpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers :=
  h.scalarQuotientPublicEndpoint

/-- Recover the current selector endpoint from the final citation consumer certificate. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover current first-bit selector assumptions from the final citation consumer certificate. -/
def toCurrentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorAssumptions

/-- Recover final-release bundle reuse from the final citation consumer certificate. -/
def toPublicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle :=
  h.publicFinalArchiveReleaseBundle

/-- Recover the no-leftover current-frontier packet from the final citation consumer certificate. -/
def toNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the public current-frontier citation bundle from the final citation consumer certificate. -/
def toPublicReleaseCurrentFrontierCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicCitationCheckpointReuse

/-- Project all-ternary endpoint exhaustion from the final citation consumer certificate. -/
def toAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    allTernaryEndpointExhaustion :=
  h.allTernaryEndpointExhaustionCert

/-- Project near-threshold boundary diagnostics from the final citation consumer certificate. -/
def toNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    nearThresholdBoundaryDiagnostics :=
  h.nearThresholdBoundaryDiagnosticsCert

/-- Project public downstream target-selector consumer closure from the certificate. -/
def toPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    publicDownstreamTargetSelectorConsumerClosure :=
  h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Project any final citation consumer row from the certificate. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate)
    (row : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow.obligation row := by
  cases row
  · exact h
  · exact h.postCheckpointCitationBundle
  · exact h.checkpointConsumerBundle
  · exact h.checkpointCertificate
  · exact h.releaseCertificateFacade
  · exact h.finalClosureHandoff
  · exact h.finalClosureFacade
  · exact h.selectorCurrentFrontierHandoff
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.currentSelectorEndpoint
  · exact h.currentSelectorAssumptions
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a final citation consumer row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow → TargetStatement
  | .citationConsumerCertificate => h.targetStatement_fromPostCheckpointCitationBundle
  | .postCheckpointCitationBundle => h.targetStatement_fromPostCheckpointCitationBundle
  | .checkpointConsumerBundle => h.targetStatement_fromCheckpointConsumerBundle
  | .checkpointCertificate => h.targetStatement_fromCheckpointCertificate
  | .releaseCertificateFacade => h.targetStatement_fromReleaseCertificateFacade
  | .finalClosureHandoff => h.targetStatement_fromFinalClosureHandoff
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .selectorCurrentFrontierHandoff => h.targetStatement_fromSelectorCurrentFrontierHandoff
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint => h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .currentSelectorAssumptions => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The final citation consumer certificate discharges every typed `F` residual public selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The final citation consumer certificate discharges every scalar-quotient public selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

/-- The final citation consumer certificate closes the target through post-checkpoint citation reuse. -/
theorem targetStatement
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromPostCheckpointCitationBundle

/-- Target-statement facade via checkpoint consumer reuse. -/
theorem targetStatement_viaCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromCheckpointConsumerBundle

/-- Target-statement facade via final release checkpoint certificate reuse. -/
theorem targetStatement_viaCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromCheckpointCertificate

/-- Target-statement facade via public final-closure release certificate reuse. -/
theorem targetStatement_viaReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromReleaseCertificateFacade

/-- Target-statement facade via selector/current-frontier handoff reuse. -/
theorem targetStatement_viaSelectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierHandoff

/-- Target-statement facade via typed `F` residual endpoint reuse. -/
theorem targetStatement_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via current-selector endpoint reuse. -/
theorem targetStatement_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via no-leftover/current-frontier packet reuse. -/
theorem targetStatement_viaNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- Target-statement facade via public current-frontier citation reuse. -/
theorem targetStatement_viaPublicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade via public downstream target-selector consumer closure. -/
theorem targetStatement_viaPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Target-statement facade selected by any final citation consumer row. -/
theorem targetStatement_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate)
    (row : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ofPostCheckpointCitationBundle_postCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).postCheckpointCitationBundle = h :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_checkpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).checkpointConsumerBundle = h.consumerBundle :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).releaseCertificateFacade = h.releaseCertificateFacade :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).selectorCurrentFrontierHandoff =
      h.selectorCurrentFrontierHandoff :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).typedFGraphResidualFacade =
      h.typedFGraphResidualFacade :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).scalarQuotientPublicEndpoint =
      h.scalarQuotientPublicEndpoint :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).currentSelectorEndpoint = h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_publicFinalArchiveReleaseBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).publicFinalArchiveReleaseBundle =
      h.publicFinalArchiveReleaseBundle :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).noLeftoverCurrentFrontierPacket =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_publicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).publicCitationCheckpointReuse =
      h.publicCitationCheckpointReuse :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).allTernaryEndpointExhaustionCert =
      h.allTernaryEndpointExhaustionCert :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).nearThresholdBoundaryDiagnosticsCert =
      h.nearThresholdBoundaryDiagnosticsCert :=
  rfl

@[simp] theorem ofPostCheckpointCitationBundle_publicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    (ofPostCheckpointCitationBundle h).publicDownstreamTargetSelectorConsumerClosureCert =
      h.publicDownstreamTargetSelectorConsumerClosureCert :=
  rfl

end ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate

/-- Expose the final citation consumer certificate from the post-checkpoint citation bundle. -/
def ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.ofPostCheckpointCitationBundle h

/-- Expose the final citation consumer certificate from the checkpoint consumer bundle. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.ofCheckpointConsumerBundle h

/-- Expose the final citation consumer certificate from the final release checkpoint certificate. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.ofCheckpointCertificate h

/-- Expose the final citation consumer certificate from the public release certificate facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.ofReleaseCertificateFacade h

/-- Expose the final citation consumer certificate from the selector/current-frontier handoff. -/
def ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.ofSelectorCurrentFrontierHandoffFacade
    h

/-- Downstream proof-md target citation through the final citation consumer certificate. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    TargetStatement :=
  ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.targetStatement h

/-- Downstream proof-md target citation selected by any final citation consumer row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate)
    (row : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCitationConsumerCertificate_postCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCitationConsumerCertificate.postCheckpointCitationBundle = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCitationConsumerCertificate_checkpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCitationConsumerCertificate.checkpointConsumerBundle = h.consumerBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCitationConsumerCertificate_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCitationConsumerCertificate.releaseCertificateFacade =
      h.releaseCertificateFacade :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCitationConsumerCertificate_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCitationConsumerCertificate.currentSelectorEndpoint =
      h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalCitationConsumerCertificate_checkpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    h.toFirstBitFinalCitationConsumerCertificate.checkpointConsumerBundle = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalCitationConsumerCertificate_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalCitationConsumerCertificate.checkpointCertificate = h :=
  rfl

/--
Final current-frontier checkpoint bundle exported after the final first-bit citation consumer.
This is a citation-facing layer: it keeps the citation consumer certificate as the source of
truth while republishing the post-checkpoint citation, checkpoint consumer, release certificate,
handoff, typed-`F` residual, scalar quotient, current-selector, no-leftover current-frontier,
public current-frontier wrapper, and diagnostic endpoints that downstream files cite.
-/
structure ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle : Type where
  citationConsumerCertificate :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate
  postCheckpointCitationBundle :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
  checkpointConsumerBundle :
    ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  checkpointCertificate : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  releaseCertificateFacade :
    ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  finalClosureHandoff : ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  finalClosureFacade : ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  selectorCurrentFrontierHandoff :
    ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  typedFGraphResidualFacade :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  scalarQuotientPublicEndpoint :
    ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  finalProofMdConsumerPublicEndpoint :
    ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  scalarQuotientPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  typedFGraphResidualPublicTargetSelectorObligations :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure
  publicFinalCurrentFrontierEndpointWrapper :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  currentSelectorEndpoint : FirstBitLargeSupportColoringCurrentSelectorEndpoint
  currentSelectorAssumptions : FirstBitCurrentSelectorAssumptions
  downstreamObligationProjection :
    ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicFinalArchiveReleaseBundle : FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  publicCitationCheckpointReuse :
    ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  externalBlockHandoff : ProofMdLargeSupportColoringExternalBlockHandoffFacade
  allTernaryEndpointExhaustionCert : allTernaryEndpointExhaustion
  nearThresholdBoundaryDiagnosticsCert : nearThresholdBoundaryDiagnostics
  publicDownstreamTargetSelectorConsumerClosureCert :
    publicDownstreamTargetSelectorConsumerClosure
  targetStatement_fromCitationConsumerCertificate : TargetStatement
  targetStatement_fromPostCheckpointCitationBundle : TargetStatement
  targetStatement_fromCheckpointConsumerBundle : TargetStatement
  targetStatement_fromCheckpointCertificate : TargetStatement
  targetStatement_fromReleaseCertificateFacade : TargetStatement
  targetStatement_fromFinalClosureHandoff : TargetStatement
  targetStatement_fromFinalClosureFacade : TargetStatement
  targetStatement_fromSelectorCurrentFrontierHandoff : TargetStatement
  targetStatement_fromSelectorCurrentFrontierExternalBlock : TargetStatement
  targetStatement_fromTypedFGraphResidualFacade : TargetStatement
  targetStatement_fromScalarQuotientPublicEndpoint : TargetStatement
  targetStatement_fromFinalProofMdConsumerPublicEndpoint : TargetStatement
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations : TargetStatement
  targetStatement_fromPublicFinalCurrentFrontierEndpointWrapper : TargetStatement
  targetStatement_fromCurrentSelectorEndpoint : TargetStatement
  targetStatement_fromDownstreamObligationProjection : TargetStatement
  targetStatement_fromPublicFinalArchiveReleaseBundle : TargetStatement
  targetStatement_fromNoLeftoverCurrentFrontierPacket : TargetStatement
  targetStatement_fromPublicCitationCheckpointReuse : TargetStatement
  targetStatement_fromExternalBlockHandoff : TargetStatement
  targetStatement_fromAllTernaryEndpointExhaustion : TargetStatement
  targetStatement_fromNearThresholdBoundaryDiagnostics : TargetStatement
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure : TargetStatement

/-- Rows exported by the final current-frontier checkpoint bundle. -/
inductive ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow : Type where
  | checkpointBundle
  | citationConsumerCertificate
  | postCheckpointCitationBundle
  | checkpointConsumerBundle
  | checkpointCertificate
  | releaseCertificateFacade
  | finalClosureHandoff
  | finalClosureFacade
  | selectorCurrentFrontierHandoff
  | typedFGraphResidualFacade
  | scalarQuotientPublicEndpoint
  | finalProofMdConsumerPublicEndpoint
  | scalarQuotientPublicTargetSelectorObligations
  | typedFGraphResidualPublicTargetSelectorObligations
  | publicFinalCurrentFrontierEndpointWrapper
  | currentSelectorEndpoint
  | currentSelectorAssumptions
  | downstreamObligationProjection
  | publicFinalArchiveReleaseBundle
  | noLeftoverCurrentFrontierPacket
  | publicCitationCheckpointReuse
  | externalBlockHandoff
  | allTernaryEndpointExhaustion
  | nearThresholdBoundaryDiagnostics
  | publicDownstreamTargetSelectorConsumerClosure
  deriving DecidableEq, Repr

namespace ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow

/-- The endpoint, packet, facade, or assumption selected by a final current-frontier checkpoint row. -/
def obligation :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow → Sort _
  | .checkpointBundle =>
      ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle
  | .citationConsumerCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate
  | .postCheckpointCitationBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle
  | .checkpointConsumerBundle =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle
  | .checkpointCertificate =>
      ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate
  | .releaseCertificateFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade
  | .finalClosureHandoff =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureHandoffBundle
  | .finalClosureFacade =>
      ProofMdLargeSupportColoringFirstBitPublicFinalClosureFacade
  | .selectorCurrentFrontierHandoff =>
      ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade
  | .typedFGraphResidualFacade =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .scalarQuotientPublicEndpoint =>
      ProofMdLargeSupportColoringScalarQuotientPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .finalProofMdConsumerPublicEndpoint =>
      ProofMdLargeSupportColoringFinalProofMdConsumerPublicEndpointBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .scalarQuotientPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
        fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
        fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
        signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
        localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
        fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
        publicDownstreamTargetSelectorConsumerClosure
  | .publicFinalCurrentFrontierEndpointWrapper =>
      ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .currentSelectorEndpoint => FirstBitLargeSupportColoringCurrentSelectorEndpoint
  | .currentSelectorAssumptions => FirstBitCurrentSelectorAssumptions
  | .downstreamObligationProjection =>
      ProofMdLargeSupportColoringFinalPublicDownstreamTargetObligationLayer
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicFinalArchiveReleaseBundle => FirstBitLargeSupportColoringPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket =>
      ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .publicCitationCheckpointReuse =>
      ProofMdLargeSupportColoringPublicReleaseCurrentFrontierCitationBundle
        terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
        terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
  | .externalBlockHandoff => ProofMdLargeSupportColoringExternalBlockHandoffFacade
  | .allTernaryEndpointExhaustion => allTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => nearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      publicDownstreamTargetSelectorConsumerClosure

end ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow

namespace ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle

/-- Build the final current-frontier checkpoint from the final citation consumer certificate. -/
def ofFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle where
  citationConsumerCertificate := h
  postCheckpointCitationBundle := h.postCheckpointCitationBundle
  checkpointConsumerBundle := h.checkpointConsumerBundle
  checkpointCertificate := h.checkpointCertificate
  releaseCertificateFacade := h.releaseCertificateFacade
  finalClosureHandoff := h.finalClosureHandoff
  finalClosureFacade := h.finalClosureFacade
  selectorCurrentFrontierHandoff := h.selectorCurrentFrontierHandoff
  typedFGraphResidualFacade := h.typedFGraphResidualFacade
  scalarQuotientPublicEndpoint := h.scalarQuotientPublicEndpoint
  finalProofMdConsumerPublicEndpoint := h.finalProofMdConsumerPublicEndpoint
  scalarQuotientPublicTargetSelectorObligations := h.scalarQuotientPublicTargetSelectorObligations
  typedFGraphResidualPublicTargetSelectorObligations :=
    h.typedFGraphResidualPublicTargetSelectorObligations
  publicFinalCurrentFrontierEndpointWrapper :=
    h.publicCitationCheckpointReuse.toPublicFinalCurrentFrontierEndpointWrapper
  currentSelectorEndpoint := h.currentSelectorEndpoint
  currentSelectorAssumptions := h.currentSelectorAssumptions
  downstreamObligationProjection := h.downstreamObligationProjection
  publicFinalArchiveReleaseBundle := h.publicFinalArchiveReleaseBundle
  noLeftoverCurrentFrontierPacket := h.noLeftoverCurrentFrontierPacket
  publicCitationCheckpointReuse := h.publicCitationCheckpointReuse
  externalBlockHandoff := h.externalBlockHandoff
  allTernaryEndpointExhaustionCert := h.allTernaryEndpointExhaustionCert
  nearThresholdBoundaryDiagnosticsCert := h.nearThresholdBoundaryDiagnosticsCert
  publicDownstreamTargetSelectorConsumerClosureCert :=
    h.publicDownstreamTargetSelectorConsumerClosureCert
  targetStatement_fromCitationConsumerCertificate :=
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.targetStatement h
  targetStatement_fromPostCheckpointCitationBundle :=
    h.targetStatement_fromPostCheckpointCitationBundle
  targetStatement_fromCheckpointConsumerBundle := h.targetStatement_fromCheckpointConsumerBundle
  targetStatement_fromCheckpointCertificate := h.targetStatement_fromCheckpointCertificate
  targetStatement_fromReleaseCertificateFacade := h.targetStatement_fromReleaseCertificateFacade
  targetStatement_fromFinalClosureHandoff := h.targetStatement_fromFinalClosureHandoff
  targetStatement_fromFinalClosureFacade := h.targetStatement_fromFinalClosureFacade
  targetStatement_fromSelectorCurrentFrontierHandoff :=
    h.targetStatement_fromSelectorCurrentFrontierHandoff
  targetStatement_fromSelectorCurrentFrontierExternalBlock :=
    h.targetStatement_fromSelectorCurrentFrontierExternalBlock
  targetStatement_fromTypedFGraphResidualFacade := h.targetStatement_fromTypedFGraphResidualFacade
  targetStatement_fromScalarQuotientPublicEndpoint := h.targetStatement_fromScalarQuotientPublicEndpoint
  targetStatement_fromFinalProofMdConsumerPublicEndpoint :=
    h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  targetStatement_fromScalarQuotientPublicTargetSelectorObligations :=
    h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations :=
    h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  targetStatement_fromPublicFinalCurrentFrontierEndpointWrapper :=
    targetStatement_of_proofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      h.publicCitationCheckpointReuse.toPublicFinalCurrentFrontierEndpointWrapper
  targetStatement_fromCurrentSelectorEndpoint := h.targetStatement_fromCurrentSelectorEndpoint
  targetStatement_fromDownstreamObligationProjection :=
    h.targetStatement_fromDownstreamObligationProjection
  targetStatement_fromPublicFinalArchiveReleaseBundle :=
    h.targetStatement_fromPublicFinalArchiveReleaseBundle
  targetStatement_fromNoLeftoverCurrentFrontierPacket :=
    h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  targetStatement_fromPublicCitationCheckpointReuse :=
    h.targetStatement_fromPublicCitationCheckpointReuse
  targetStatement_fromExternalBlockHandoff := h.targetStatement_fromExternalBlockHandoff
  targetStatement_fromAllTernaryEndpointExhaustion :=
    h.targetStatement_fromAllTernaryEndpointExhaustion
  targetStatement_fromNearThresholdBoundaryDiagnostics :=
    h.targetStatement_fromNearThresholdBoundaryDiagnostics
  targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure :=
    h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Recover the final citation consumer certificate from the checkpoint bundle. -/
def toFirstBitFinalCitationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate :=
  h.citationConsumerCertificate

/-- Recover the post-checkpoint citation bundle from the checkpoint bundle. -/
def toFirstBitFinalReleasePostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle :=
  h.postCheckpointCitationBundle

/-- Recover the public/final current-frontier wrapper from the checkpoint bundle. -/
def toPublicFinalCurrentFrontierEndpointWrapper
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    ProofMdLargeSupportColoringPublicFinalCurrentFrontierEndpointWrapper
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.publicFinalCurrentFrontierEndpointWrapper

/-- Recover the no-leftover current-frontier packet from the checkpoint bundle. -/
def toNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    ProofMdLargeSupportColoringPublicReleaseNoLeftoverCurrentFrontierPacket
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision :=
  h.noLeftoverCurrentFrontierPacket

/-- Recover the current-selector endpoint from the checkpoint bundle. -/
def toCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    FirstBitLargeSupportColoringCurrentSelectorEndpoint :=
  h.currentSelectorEndpoint

/-- Recover the current-selector assumptions from the checkpoint bundle. -/
def toCurrentSelectorAssumptions
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    FirstBitCurrentSelectorAssumptions :=
  h.currentSelectorAssumptions

/-- Project any final current-frontier checkpoint row from the bundle. -/
def rowObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow.obligation row := by
  cases row
  · exact h
  · exact h.citationConsumerCertificate
  · exact h.postCheckpointCitationBundle
  · exact h.checkpointConsumerBundle
  · exact h.checkpointCertificate
  · exact h.releaseCertificateFacade
  · exact h.finalClosureHandoff
  · exact h.finalClosureFacade
  · exact h.selectorCurrentFrontierHandoff
  · exact h.typedFGraphResidualFacade
  · exact h.scalarQuotientPublicEndpoint
  · exact h.finalProofMdConsumerPublicEndpoint
  · exact h.scalarQuotientPublicTargetSelectorObligations
  · exact h.typedFGraphResidualPublicTargetSelectorObligations
  · exact h.publicFinalCurrentFrontierEndpointWrapper
  · exact h.currentSelectorEndpoint
  · exact h.currentSelectorAssumptions
  · exact h.downstreamObligationProjection
  · exact h.publicFinalArchiveReleaseBundle
  · exact h.noLeftoverCurrentFrontierPacket
  · exact h.publicCitationCheckpointReuse
  · exact h.externalBlockHandoff
  · exact h.allTernaryEndpointExhaustionCert
  · exact h.nearThresholdBoundaryDiagnosticsCert
  · exact h.publicDownstreamTargetSelectorConsumerClosureCert

/-- Select the target statement associated to a final current-frontier checkpoint row. -/
def targetStatementForRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow → TargetStatement
  | .checkpointBundle => h.targetStatement_fromCitationConsumerCertificate
  | .citationConsumerCertificate => h.targetStatement_fromCitationConsumerCertificate
  | .postCheckpointCitationBundle => h.targetStatement_fromPostCheckpointCitationBundle
  | .checkpointConsumerBundle => h.targetStatement_fromCheckpointConsumerBundle
  | .checkpointCertificate => h.targetStatement_fromCheckpointCertificate
  | .releaseCertificateFacade => h.targetStatement_fromReleaseCertificateFacade
  | .finalClosureHandoff => h.targetStatement_fromFinalClosureHandoff
  | .finalClosureFacade => h.targetStatement_fromFinalClosureFacade
  | .selectorCurrentFrontierHandoff => h.targetStatement_fromSelectorCurrentFrontierHandoff
  | .typedFGraphResidualFacade => h.targetStatement_fromTypedFGraphResidualFacade
  | .scalarQuotientPublicEndpoint => h.targetStatement_fromScalarQuotientPublicEndpoint
  | .finalProofMdConsumerPublicEndpoint => h.targetStatement_fromFinalProofMdConsumerPublicEndpoint
  | .scalarQuotientPublicTargetSelectorObligations =>
      h.targetStatement_fromScalarQuotientPublicTargetSelectorObligations
  | .typedFGraphResidualPublicTargetSelectorObligations =>
      h.targetStatement_fromTypedFGraphResidualPublicTargetSelectorObligations
  | .publicFinalCurrentFrontierEndpointWrapper =>
      h.targetStatement_fromPublicFinalCurrentFrontierEndpointWrapper
  | .currentSelectorEndpoint => h.targetStatement_fromCurrentSelectorEndpoint
  | .currentSelectorAssumptions => h.targetStatement_fromCurrentSelectorEndpoint
  | .downstreamObligationProjection => h.targetStatement_fromDownstreamObligationProjection
  | .publicFinalArchiveReleaseBundle => h.targetStatement_fromPublicFinalArchiveReleaseBundle
  | .noLeftoverCurrentFrontierPacket => h.targetStatement_fromNoLeftoverCurrentFrontierPacket
  | .publicCitationCheckpointReuse => h.targetStatement_fromPublicCitationCheckpointReuse
  | .externalBlockHandoff => h.targetStatement_fromExternalBlockHandoff
  | .allTernaryEndpointExhaustion => h.targetStatement_fromAllTernaryEndpointExhaustion
  | .nearThresholdBoundaryDiagnostics => h.targetStatement_fromNearThresholdBoundaryDiagnostics
  | .publicDownstreamTargetSelectorConsumerClosure =>
      h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- The final current-frontier checkpoint closes the target through its citation consumer. -/
theorem targetStatement
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromCitationConsumerCertificate

/-- Target-statement facade via post-checkpoint citation reuse. -/
theorem targetStatement_viaPostCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromPostCheckpointCitationBundle

/-- Target-statement facade via checkpoint consumer reuse. -/
theorem targetStatement_viaCheckpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromCheckpointConsumerBundle

/-- Target-statement facade via final release checkpoint certificate reuse. -/
theorem targetStatement_viaCheckpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromCheckpointCertificate

/-- Target-statement facade via public final-closure release certificate reuse. -/
theorem targetStatement_viaReleaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromReleaseCertificateFacade

/-- Target-statement facade via selector/current-frontier handoff reuse. -/
theorem targetStatement_viaSelectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromSelectorCurrentFrontierHandoff

/-- Target-statement facade via typed `F` residual endpoint reuse. -/
theorem targetStatement_viaTypedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromTypedFGraphResidualFacade

/-- Target-statement facade via scalar-quotient public endpoint reuse. -/
theorem targetStatement_viaScalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromScalarQuotientPublicEndpoint

/-- Target-statement facade via the public/final current-frontier wrapper. -/
theorem targetStatement_viaPublicFinalCurrentFrontierEndpointWrapper
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromPublicFinalCurrentFrontierEndpointWrapper

/-- Target-statement facade via current-selector endpoint reuse. -/
theorem targetStatement_viaCurrentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromCurrentSelectorEndpoint

/-- Target-statement facade via no-leftover/current-frontier packet reuse. -/
theorem targetStatement_viaNoLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromNoLeftoverCurrentFrontierPacket

/-- Target-statement facade via public current-frontier citation reuse. -/
theorem targetStatement_viaPublicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromPublicCitationCheckpointReuse

/-- Target-statement facade via all-ternary endpoint exhaustion diagnostics. -/
theorem targetStatement_viaAllTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromAllTernaryEndpointExhaustion

/-- Target-statement facade via near-threshold boundary diagnostics. -/
theorem targetStatement_viaNearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromNearThresholdBoundaryDiagnostics

/-- Target-statement facade via public downstream target-selector consumer closure. -/
theorem targetStatement_viaPublicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  h.targetStatement_fromPublicDownstreamTargetSelectorConsumerClosure

/-- Target-statement facade selected by any final current-frontier checkpoint row. -/
theorem targetStatement_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow) :
    TargetStatement :=
  h.targetStatementForRow row

/-- The checkpoint bundle discharges every typed `F` residual public selector. -/
theorem publicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle)
    (selector : ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector) :
    ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers
      localHostTwoExceptionalPacketDischarge localHostThreeExceptionalPacketDischarge
      fourExceptionTwoTwoTypeSquareSkeletons compactSignedQuotientResidual
      publicDownstreamTargetSelectorConsumerClosure selector :=
  ProofMdLargeSupportColoringTypedFGraphResidualPublicTargetSelectorObligationPacket.obligation
    h.typedFGraphResidualPublicTargetSelectorObligations selector

/-- The checkpoint bundle discharges every scalar-quotient public selector. -/
theorem scalarQuotientPublicTargetSelectorObligation
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle)
    (selector : ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector) :
    ProofMdLargeSupportColoringScalarQuotientPublicTargetSelector.obligation
      terminalStrictCrossAtomDefect terminalNoLeftoverFourFourAtomDeletionDichotomy
      terminalNoLeftoverUnitStrictAbsorptionOrLiftCollision
      fullySplitTransposeForwardRigidity fullySplitTransposeReverseRigidity
      fullySplitTransposeDiagonalRigidity parityTetrahedronStarPhaseHandoff
      signedK4QuotientClosureClassification publicDownstreamTargetSelectorConsumers selector :=
  ProofMdLargeSupportColoringScalarQuotientPublicTargetSelectorObligationPacket.obligation
    h.scalarQuotientPublicTargetSelectorObligations selector

@[simp] theorem ofFinalCitationConsumerCertificate_citationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).citationConsumerCertificate = h :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_postCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).postCheckpointCitationBundle =
      h.postCheckpointCitationBundle :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_checkpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).checkpointConsumerBundle =
      h.checkpointConsumerBundle :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).checkpointCertificate = h.checkpointCertificate :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).releaseCertificateFacade =
      h.releaseCertificateFacade :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).selectorCurrentFrontierHandoff =
      h.selectorCurrentFrontierHandoff :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_typedFGraphResidualFacade
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).typedFGraphResidualFacade =
      h.typedFGraphResidualFacade :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_scalarQuotientPublicEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).scalarQuotientPublicEndpoint =
      h.scalarQuotientPublicEndpoint :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_publicFinalCurrentFrontierEndpointWrapper
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).publicFinalCurrentFrontierEndpointWrapper =
      h.publicCitationCheckpointReuse.toPublicFinalCurrentFrontierEndpointWrapper :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).currentSelectorEndpoint = h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).noLeftoverCurrentFrontierPacket =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_publicCitationCheckpointReuse
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).publicCitationCheckpointReuse =
      h.publicCitationCheckpointReuse :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_allTernaryEndpointExhaustion
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).allTernaryEndpointExhaustionCert =
      h.allTernaryEndpointExhaustionCert :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_nearThresholdBoundaryDiagnostics
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).nearThresholdBoundaryDiagnosticsCert =
      h.nearThresholdBoundaryDiagnosticsCert :=
  rfl

@[simp] theorem ofFinalCitationConsumerCertificate_publicDownstreamTargetSelectorConsumerClosure
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    (ofFinalCitationConsumerCertificate h).publicDownstreamTargetSelectorConsumerClosureCert =
      h.publicDownstreamTargetSelectorConsumerClosureCert :=
  rfl

end ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle

/-- Expose the final current-frontier checkpoint bundle from the final citation consumer. -/
def ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle.ofFinalCitationConsumerCertificate h

/-- Expose the final current-frontier checkpoint bundle from the post-checkpoint citation bundle. -/
def ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  h.toFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle

/-- Expose the final current-frontier checkpoint bundle from the checkpoint consumer bundle. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  h.toFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle

/-- Expose the final current-frontier checkpoint bundle from the final release checkpoint certificate. -/
def ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  h.toFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle

/-- Expose the final current-frontier checkpoint bundle from the public release certificate facade. -/
def ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  h.toFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle

/-- Expose the final current-frontier checkpoint bundle from the selector/current-frontier handoff. -/
def ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle :=
  h.toFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle

/-- Downstream proof-md target citation through the final current-frontier checkpoint bundle. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle) :
    TargetStatement :=
  ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle.targetStatement h

/-- Downstream proof-md target citation selected by any final current-frontier checkpoint row. -/
theorem targetStatement_of_proofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle_viaRow
    (h : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointBundle)
    (row : ProofMdLargeSupportColoringFirstBitFinalCurrentFrontierCheckpointRow) :
    TargetStatement :=
  h.targetStatementForRow row

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_citationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.citationConsumerCertificate = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_postCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.postCheckpointCitationBundle =
      h.postCheckpointCitationBundle :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_publicFinalCurrentFrontierEndpointWrapper
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.publicFinalCurrentFrontierEndpointWrapper =
      h.publicCitationCheckpointReuse.toPublicFinalCurrentFrontierEndpointWrapper :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_currentSelectorEndpoint
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.currentSelectorEndpoint =
      h.currentSelectorEndpoint :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_noLeftoverCurrentFrontierPacket
    (h : ProofMdLargeSupportColoringFirstBitFinalCitationConsumerCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.noLeftoverCurrentFrontierPacket =
      h.noLeftoverCurrentFrontierPacket :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCurrentFrontierCheckpointBundle_postCheckpointCitationBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.postCheckpointCitationBundle = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle.toFirstBitFinalCurrentFrontierCheckpointBundle_citationConsumerCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleasePostCheckpointCitationBundle) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.citationConsumerCertificate =
      h.toFirstBitFinalCitationConsumerCertificate :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle.toFirstBitFinalCurrentFrontierCheckpointBundle_checkpointConsumerBundle
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointConsumerBundle) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.checkpointConsumerBundle = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate.toFirstBitFinalCurrentFrontierCheckpointBundle_checkpointCertificate
    (h : ProofMdLargeSupportColoringFirstBitFinalReleaseCheckpointCertificate) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.checkpointCertificate = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade.toFirstBitFinalCurrentFrontierCheckpointBundle_releaseCertificateFacade
    (h : ProofMdLargeSupportColoringFirstBitPublicFinalClosureReleaseCertificateFacade) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.releaseCertificateFacade = h :=
  rfl

@[simp] theorem ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade.toFirstBitFinalCurrentFrontierCheckpointBundle_selectorCurrentFrontierHandoff
    (h : ProofMdLargeSupportColoringFirstBitDownstreamSelectorCurrentFrontierHandoffFacade) :
    h.toFirstBitFinalCurrentFrontierCheckpointBundle.selectorCurrentFrontierHandoff = h :=
  rfl

end FirstBitPublicFinalClosure

end RegularInducedSubgraph
