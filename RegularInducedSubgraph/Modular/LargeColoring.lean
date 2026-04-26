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
end RegularInducedSubgraph
