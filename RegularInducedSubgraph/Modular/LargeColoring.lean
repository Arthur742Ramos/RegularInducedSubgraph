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

end RegularInducedSubgraph
