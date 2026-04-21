import RegularInducedSubgraph.Modular.Finite

namespace RegularInducedSubgraph

section FiniteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Auxiliary packaging for turning a fixed-control cascade into the exact control-block data used by
`HasExactControlBlockWitnessOfCard`.
-/
private def CascadeExactControlBlockData
    (G : SimpleGraph V) (s : Finset V) (chain : List (Finset V)) (t : Finset V) : Prop := by
  classical
  exact ∃ u : Finset V, ∃ blocks : List (Finset V × ℕ),
    u = cascadeTerminal s chain ∧
    blocks.length = chain.length + 1 ∧
    u ⊆ s ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated u blocks ∧
    u ∪ controlBlockUnion blocks = s ∪ t ∧
    ∃ D : ℕ,
      (∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      HasConstantExternalBlockDegrees G u blocks

lemma exists_exactControlBlockData_of_hasSingleControlCascadeFrom
    (G : SimpleGraph V) {s t : Finset V} {chain : List (Finset V)}
    (ht : 0 < t.card) (hst : Disjoint s t)
    (hcascade : HasSingleControlCascadeFrom G t s chain) :
    CascadeExactControlBlockData G s chain t := by
  classical
  induction chain generalizing s with
  | nil =>
      rcases hcascade with ⟨D, e, hdeg, hctrl⟩
      refine ⟨s, [(t, e)], rfl, by simp, subset_rfl, ?_, ?_, by simp, D, ?_, ?_⟩
      · simpa [NonemptyControlBlockUnion, controlBlockUnion] using ht
      · refine ⟨hst, ?_, trivial⟩
        simpa [controlBlockUnion]
      · intro v
        have hcast :
            (inducedOn G (s ∪ controlBlockUnion [(t, e)])).degree
                ⟨v.1, by simpa [controlBlockUnion, Finset.union_assoc] using
                  Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G (s ∪ t)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
          simpa [controlBlockUnion, Finset.union_assoc] using
            (inducedOn_degree_congr (G := G)
              (s := s ∪ controlBlockUnion [(t, e)]) (t := s ∪ t)
              (h := by simp [controlBlockUnion, Finset.union_assoc])
              (hs := by
                simpa [controlBlockUnion, Finset.union_assoc] using
                  Finset.mem_union.mpr (Or.inl v.2))
              (ht := Finset.mem_union.mpr (Or.inl v.2)))
        exact hcast.trans (hdeg v)
      · change (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) ∧ True
        refine ⟨?_, trivial⟩
        intro v
        simpa using hctrl v
  | cons s' chain ih =>
      rcases hcascade with ⟨hs', D, eDrop, hdeg, hdrop, hrest⟩
      have hs't : Disjoint s' t := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxS' hxT
        exact (Finset.disjoint_left.mp hst) (hs' hxS') hxT
      rcases ih hs't hrest with
        ⟨u, blocks, huTerm, hlen, huSub, hnonempty, hsep, hunion, _Dtail, _hdegTail, hextTail⟩
      have huSubTop : u ⊆ s := fun x hx => hs' (huSub hx)
      have huDrop : Disjoint u (s \ s') := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxU hxDrop
        exact (Finset.mem_sdiff.mp hxDrop).2 (huSub hxU)
      have hblocksSubset : controlBlockUnion blocks ⊆ s' ∪ t := by
        intro x hx
        have hxUnion : x ∈ u ∪ controlBlockUnion blocks := Finset.mem_union.mpr (Or.inr hx)
        simpa [hunion] using hxUnion
      have hdropUnion : Disjoint (s \ s') (s' ∪ t) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxDrop hxUnion
        rcases Finset.mem_union.mp hxUnion with hxS' | hxT
        · exact (Finset.mem_sdiff.mp hxDrop).2 hxS'
        · exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
      have hdropBlocks : Disjoint (s \ s') (controlBlockUnion blocks) :=
        hdropUnion.mono_right hblocksSubset
      have hsepNew : ControlBlocksSeparated u (((s \ s'), eDrop) :: blocks) := by
        exact ⟨huDrop, hdropBlocks, hsep⟩
      have hunionNew : u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks) = s ∪ t := by
        calc
          u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks)
              = (s \ s') ∪ (u ∪ controlBlockUnion blocks) := by
                  simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                    Finset.union_comm]
          _ = (s \ s') ∪ (s' ∪ t) := by rw [hunion]
          _ = s ∪ t := by
              rw [← Finset.union_assoc, Finset.sdiff_union_of_subset hs']
      have hnonemptyNew : NonemptyControlBlockUnion (((s \ s'), eDrop) :: blocks) := by
        have hsubset :
            controlBlockUnion blocks ⊆ controlBlockUnion (((s \ s'), eDrop) :: blocks) := by
          intro x hx
          simp [controlBlockUnion, hx]
        exact lt_of_lt_of_le hnonempty (Finset.card_le_card hsubset)
      have hdegNew :
          ∀ v : ↑(u : Set V),
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D := by
        intro v
        have hcast :
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G (s ∪ t)).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))⟩ := by
          simpa using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks)) (t := s ∪ t)
              (h := hunionNew)
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))))
        exact hcast.trans (hdeg ⟨v.1, huSub v.2⟩)
      have hdropConst : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ s')).card = eDrop := by
        intro v
        simpa using hdrop ⟨v.1, huSub v.2⟩
      have hextNew : HasConstantExternalBlockDegrees G u (((s \ s'), eDrop) :: blocks) := by
        exact ⟨hdropConst, hextTail⟩
      refine ⟨u, ((s \ s'), eDrop) :: blocks, huTerm, ?_, huSubTop, hnonemptyNew, hsepNew,
        hunionNew, D, hdegNew, hextNew⟩
      simp [hlen]

lemma hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasSingleControlCascadeWitnessOfCard G k) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, t, chain, hku, ht, hst, hfrom⟩
  rcases exists_exactControlBlockData_of_hasSingleControlCascadeFrom G ht hst hfrom with
    ⟨u, blocks, huTerm, _hlen, _huSub, hnonempty, hsep, _hunion, D, hdeg, hext⟩
  refine ⟨u, ?_, blocks, hnonempty, hsep, D, hdeg, hext⟩
  simpa [huTerm] using hku

lemma hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedSingleControlCascadeWitnessOfCard G k r) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  rcases hcascade with ⟨s, t, chain, hku, hlenBound, ht, hst, hfrom⟩
  rcases exists_exactControlBlockData_of_hasSingleControlCascadeFrom G ht hst hfrom with
    ⟨u, blocks, huTerm, hlen, _huSub, hnonempty, hsep, _hunion, D, hdeg, hext⟩
  refine ⟨u, ?_, blocks, ?_, hnonempty, hsep, D, hdeg, hext⟩
  · simpa [huTerm] using hku
  · simpa [hlen] using hlenBound

lemma hasSingleControlCascadeWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedSingleControlCascadeWitnessOfCard G k r) :
    HasSingleControlCascadeWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, t, chain, hku, _hlen, ht, hst, hfrom⟩
  exact ⟨s, t, chain, hku, ht, hst, hfrom⟩

lemma hasSingleControlCascadeWitnessOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasSingleControlCascadeWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩
  refine ⟨s, t, [], ?_, ht, hst, ?_⟩
  · simpa [cascadeTerminal] using hks
  · exact ⟨D, e, hdeg, hext⟩

theorem hasSingleControlExactWitnessOfCard_iff_hasSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlExactWitnessOfCard G k ↔ HasSingleControlCascadeWitnessOfCard G k := by
  constructor
  · exact hasSingleControlCascadeWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
  · intro hcascade
    exact hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
      (hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G hcascade)

theorem hasSingleControlBucketingWitnessOfCard_iff_hasSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlBucketingWitnessOfCard G k ↔ HasSingleControlCascadeWitnessOfCard G k := by
  constructor
  · intro hbuck
    exact hasSingleControlCascadeWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G hbuck)
  · intro hcascade
    exact hasSingleControlBucketingWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
        (hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G hcascade))

lemma hasRegularInducedSubgraphOfCard_of_hasSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasSingleControlCascadeWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G hcascade)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedSingleControlCascadeWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
      (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard
        G hcascade))

/--
Auxiliary packaging for turning a fixed-control multiblock cascade into the exact control-block data
used by `HasExactControlBlockWitnessOfCard`.
-/
private def ControlBlockCascadeExactData
    (G : SimpleGraph V) (s : Finset V) (chain : List (Finset V))
    (baseBlocks : List (Finset V × ℕ)) : Prop := by
  classical
  exact ∃ u : Finset V, ∃ blocks : List (Finset V × ℕ),
    u = cascadeTerminal s chain ∧
    blocks.length = chain.length + baseBlocks.length ∧
    u ⊆ s ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated u blocks ∧
    u ∪ controlBlockUnion blocks = s ∪ controlBlockUnion baseBlocks ∧
    ∃ D : ℕ,
      (∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      HasConstantExternalBlockDegrees G u blocks

lemma exists_controlBlockCascadeExactData_of_hasControlBlockCascadeFrom
    (G : SimpleGraph V) {s : Finset V} {baseBlocks : List (Finset V × ℕ)}
    {chain : List (Finset V)} (hnonempty : NonemptyControlBlockUnion baseBlocks)
    (hsep : ControlBlocksSeparated s baseBlocks)
    (hcascade : HasControlBlockCascadeFrom G baseBlocks s chain) :
    ControlBlockCascadeExactData G s chain baseBlocks := by
  classical
  induction chain generalizing s with
  | nil =>
      rcases hcascade with ⟨D, hdeg, hext⟩
      refine ⟨s, baseBlocks, rfl, by simp, subset_rfl, hnonempty, hsep, rfl, D, hdeg, hext⟩
  | cons s' chain ih =>
      rcases hcascade with ⟨hs', D, eDrop, hdeg, hdrop, hrest⟩
      have hsepStep : ControlBlocksSeparated s' baseBlocks :=
        controlBlocksSeparated_mono hs' hsep
      rcases ih hsepStep hrest with
        ⟨u, blocks, huTerm, hlen, huSub, hnonemptyTail, hsepTail, hunion, _Dtail, _hdegTail,
          hextTail⟩
      have huSubTop : u ⊆ s := fun x hx => hs' (huSub hx)
      have huDrop : Disjoint u (s \ s') := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxU hxDrop
        exact (Finset.mem_sdiff.mp hxDrop).2 (huSub hxU)
      have hblocksSubset : controlBlockUnion blocks ⊆ s' ∪ controlBlockUnion baseBlocks := by
        intro x hx
        have hxUnion : x ∈ u ∪ controlBlockUnion blocks := Finset.mem_union.mpr (Or.inr hx)
        simpa [hunion] using hxUnion
      have hsBase : Disjoint s (controlBlockUnion baseBlocks) :=
        disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
      have hdropUnion : Disjoint (s \ s') (s' ∪ controlBlockUnion baseBlocks) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxDrop hxUnion
        rcases Finset.mem_union.mp hxUnion with hxS' | hxBase
        · exact (Finset.mem_sdiff.mp hxDrop).2 hxS'
        · exact (Finset.disjoint_left.mp hsBase) (Finset.mem_sdiff.mp hxDrop).1 hxBase
      have hdropBlocks : Disjoint (s \ s') (controlBlockUnion blocks) :=
        hdropUnion.mono_right hblocksSubset
      have hsepNew : ControlBlocksSeparated u (((s \ s'), eDrop) :: blocks) := by
        exact ⟨huDrop, hdropBlocks, hsepTail⟩
      have hunionNew :
          u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks) =
            s ∪ controlBlockUnion baseBlocks := by
        calc
          u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks)
              = (s \ s') ∪ (u ∪ controlBlockUnion blocks) := by
                  simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                    Finset.union_comm]
          _ = (s \ s') ∪ (s' ∪ controlBlockUnion baseBlocks) := by rw [hunion]
          _ = s ∪ controlBlockUnion baseBlocks := by
                rw [← Finset.union_assoc, Finset.sdiff_union_of_subset hs']
      have hnonemptyNew : NonemptyControlBlockUnion (((s \ s'), eDrop) :: blocks) := by
        have hsubset :
            controlBlockUnion blocks ⊆ controlBlockUnion (((s \ s'), eDrop) :: blocks) := by
          intro x hx
          simp [controlBlockUnion, hx]
        exact lt_of_lt_of_le hnonemptyTail (Finset.card_le_card hsubset)
      have hdegNew :
          ∀ v : ↑(u : Set V),
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D := by
        intro v
        have hcast :
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G (s ∪ controlBlockUnion baseBlocks)).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))⟩ := by
          simpa using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))
              (t := s ∪ controlBlockUnion baseBlocks)
              (h := hunionNew)
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))))
        exact hcast.trans (hdeg ⟨v.1, huSub v.2⟩)
      have hdropConst : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ s')).card = eDrop := by
        intro v
        simpa using hdrop ⟨v.1, huSub v.2⟩
      have hextNew :
          HasConstantExternalBlockDegrees G u (((s \ s'), eDrop) :: blocks) := by
        exact ⟨hdropConst, hextTail⟩
      refine ⟨u, ((s \ s'), eDrop) :: blocks, huTerm, ?_, huSubTop, hnonemptyNew, hsepNew,
        hunionNew, D, hdegNew, hextNew⟩
      simp [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma hasControlBlockModularCascadeFrom_of_hasControlBlockCascadeFrom
    (G : SimpleGraph V) (q : ℕ) {blocks : List (Finset V × ℕ)} {s : Finset V}
    {chain : List (Finset V)} (hcascade : HasControlBlockCascadeFrom G blocks s chain) :
    HasControlBlockModularCascadeFrom G q blocks s chain := by
  classical
  induction chain generalizing s with
  | nil =>
      rcases hcascade with ⟨D, hdeg, hext⟩
      refine ⟨?_, hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s q hext⟩
      intro v w
      simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD q])
  | cons u chain ih =>
      rcases hcascade with ⟨hu, D, eDrop, hdeg, hdrop, hrest⟩
      refine ⟨hu, eDrop, ?_, ?_, ih hrest⟩
      · intro v w
        simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD q])
      · intro v
        simpa [hdrop v] using (Nat.ModEq.refl eDrop : eDrop ≡ eDrop [MOD q])

lemma hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
    (G : SimpleGraph V) {q : ℕ} {blocks : List (Finset V × ℕ)} {s : Finset V}
    [DecidableRel G.Adj]
    {chain : List (Finset V)} (hsep : ControlBlocksSeparated s blocks)
    (hcascade : HasFixedModulusCascadeFrom G q s chain)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasControlBlockModularCascadeFrom G q blocks s chain := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  induction chain generalizing s with
  | nil =>
      have hdeg0 :
          ∀ v w : ↑(s : Set V),
            (inducedOn G (s ∪ (∅ : Finset V))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (s ∪ (∅ : Finset V))).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        intro v w
        have hcastv :
            (inducedOn G (s ∪ (∅ : Finset V))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G s).degree v := by
          simpa [Finset.empty_union] using
            (inducedOn_degree_congr (G := G)
              (s := s ∪ (∅ : Finset V)) (t := s)
              (h := by simp [Finset.empty_union])
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := v.2))
        have hcastw :
            (inducedOn G (s ∪ (∅ : Finset V))).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
              (inducedOn G s).degree w := by
          simpa [Finset.empty_union] using
            (inducedOn_degree_congr (G := G)
              (s := s ∪ (∅ : Finset V)) (t := s)
              (h := by simp [Finset.empty_union])
              (hs := Finset.mem_union.mpr (Or.inl w.2))
              (ht := w.2))
        simpa [hcastv, hcastw] using hcascade v w
      refine ⟨?_, hext⟩
      intro v w
      have hraw :=
        modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
          (G := G) (s := s) (tail := (∅ : Finset V)) (q := q) hsep (by simp) hdeg0 hext v w
      have hcastv :
          (inducedOn G (s ∪ (controlBlockUnion blocks ∪ (∅ : Finset V)))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [Finset.union_assoc, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion blocks ∪ (∅ : Finset V)))
            (t := s ∪ controlBlockUnion blocks)
            (h := by simp [Finset.union_assoc, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      have hcastw :
          (inducedOn G (s ∪ (controlBlockUnion blocks ∪ (∅ : Finset V)))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
        simpa [Finset.union_assoc, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion blocks ∪ (∅ : Finset V)))
            (t := s ∪ controlBlockUnion blocks)
            (h := by simp [Finset.union_assoc, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl w.2)))
      simpa [hcastv, hcastw] using hraw
  | cons u chain ih =>
      rcases hcascade with ⟨hu, eDrop, hdeg, hdrop, hrest⟩
      have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hu hsep
      have hextU : HasConstantModExternalBlockDegrees G u q blocks :=
        hasConstantModExternalBlockDegrees_mono (G := G) hu hext
      have hdisjTail : Disjoint (controlBlockUnion blocks) (s \ u) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxBlocks hxTail
        exact (Finset.disjoint_left.mp (disjoint_controlBlockUnion_of_controlBlocksSeparated hsep))
          (Finset.mem_sdiff.mp hxTail).1 hxBlocks
      have hdeg0 :
          ∀ v w : ↑(u : Set V),
            (inducedOn G (u ∪ (s \ u))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (u ∪ (s \ u))).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        intro v w
        have hcastv :
            (inducedOn G (u ∪ (s \ u))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
          simpa [Finset.union_sdiff_of_subset hu] using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ (s \ u)) (t := s)
              (h := by simp [Finset.union_sdiff_of_subset hu])
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := hu v.2))
        have hcastw :
            (inducedOn G (u ∪ (s \ u))).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
              (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
          simpa [Finset.union_sdiff_of_subset hu] using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ (s \ u)) (t := s)
              (h := by simp [Finset.union_sdiff_of_subset hu])
              (hs := Finset.mem_union.mpr (Or.inl w.2))
              (ht := hu w.2))
        simpa [hcastv, hcastw] using hdeg v w
      refine ⟨hu, eDrop, ?_, hdrop, ih hsepU hrest hextU⟩
      intro v w
      have hraw :=
        modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
          (G := G) (s := u) (tail := s \ u) (q := q) hsepU hdisjTail hdeg0 hextU v w
      have hunion :
          u ∪ (controlBlockUnion blocks ∪ (s \ u)) = s ∪ controlBlockUnion blocks := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxU | hxRest
          · exact Finset.mem_union.mpr (Or.inl (hu hxU))
          · rcases Finset.mem_union.mp hxRest with hxBlocks | hxTail
            · exact Finset.mem_union.mpr (Or.inr hxBlocks)
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxTail).1)
        · intro hx
          rcases Finset.mem_union.mp hx with hxS | hxBlocks
          · by_cases hxU : x ∈ u
            · exact Finset.mem_union.mpr (Or.inl hxU)
            · exact
                Finset.mem_union.mpr
                  (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxS, hxU⟩))))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hxBlocks)))
      have hcastv :
          (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
        simpa [hunion] using
          (inducedOn_degree_congr (G := G)
            (s := u ∪ (controlBlockUnion blocks ∪ (s \ u)))
            (t := s ∪ controlBlockUnion blocks)
            (h := hunion)
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
      have hcastw :
          (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
        simpa [hunion] using
          (inducedOn_degree_congr (G := G)
            (s := u ∪ (controlBlockUnion blocks ∪ (s \ u)))
            (t := s ∪ controlBlockUnion blocks)
            (h := hunion)
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
      simpa [hcastv, hcastw] using hraw

lemma hasControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
    (G : SimpleGraph V) {k q : ℕ} {s : Finset V} {blocks : List (Finset V × ℕ)}
    [DecidableRel G.Adj]
    {chain : List (Finset V)} (hku : k ≤ (cascadeTerminal s chain).card)
    (hq : (cascadeTerminal s chain).card ≤ q) (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks) (hcascade : HasFixedModulusCascadeFrom G q s chain)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasControlBlockModularCascadeWitnessOfCard G k := by
  exact
    ⟨s, q, blocks, chain, hku, hq, hnonempty, hsep,
      hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
        G hsep hcascade hext⟩

lemma hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
    (G : SimpleGraph V) {k q r : ℕ} {s : Finset V} {blocks : List (Finset V × ℕ)}
    [DecidableRel G.Adj]
    {chain : List (Finset V)} (hku : k ≤ (cascadeTerminal s chain).card)
    (hq : (cascadeTerminal s chain).card ≤ q) (hlen : chain.length + blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks) (hsep : ControlBlocksSeparated s blocks)
    (hcascade : HasFixedModulusCascadeFrom G q s chain)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasBoundedControlBlockModularCascadeWitnessOfCard G k r := by
  exact
    ⟨s, q, blocks, chain, hku, hq, hlen, hnonempty, hsep,
      hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
        G hsep hcascade hext⟩

/--
Auxiliary packaging for turning a fixed-modulus multiblock cascade into the modular control-block
data used by `HasControlBlockModularBucketingWitnessOfCard`.
-/
private def ControlBlockCascadeModularData
    (G : SimpleGraph V) (q : ℕ) (s : Finset V) (chain : List (Finset V))
    (baseBlocks : List (Finset V × ℕ)) : Prop := by
  classical
  exact ∃ u : Finset V, ∃ blocks : List (Finset V × ℕ),
    u = cascadeTerminal s chain ∧
    blocks.length = chain.length + baseBlocks.length ∧
    u ⊆ s ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated u blocks ∧
    u ∪ controlBlockUnion blocks = s ∪ controlBlockUnion baseBlocks ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G (u ∪ controlBlockUnion blocks)).degree
          ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
          ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
    HasConstantModExternalBlockDegrees G u q blocks

lemma exists_controlBlockCascadeModularData_of_hasControlBlockModularCascadeFrom
    (G : SimpleGraph V) {q : ℕ} {s : Finset V} {baseBlocks : List (Finset V × ℕ)}
    {chain : List (Finset V)} (hnonempty : NonemptyControlBlockUnion baseBlocks)
    (hsep : ControlBlocksSeparated s baseBlocks)
    (hcascade : HasControlBlockModularCascadeFrom G q baseBlocks s chain) :
    ControlBlockCascadeModularData G q s chain baseBlocks := by
  classical
  induction chain generalizing s with
  | nil =>
      rcases hcascade with ⟨hdeg, hext⟩
      refine ⟨s, baseBlocks, rfl, by simp, subset_rfl, hnonempty, hsep, rfl, hdeg, hext⟩
  | cons s' chain ih =>
      rcases hcascade with ⟨hs', eDrop, hdeg, hdrop, hrest⟩
      have hsepStep : ControlBlocksSeparated s' baseBlocks := controlBlocksSeparated_mono hs' hsep
      rcases ih hsepStep hrest with
        ⟨u, blocks, huTerm, hlen, huSub, hnonemptyTail, hsepTail, hunion, _hdegTail, hextTail⟩
      have huSubTop : u ⊆ s := fun x hx => hs' (huSub hx)
      have huDrop : Disjoint u (s \ s') := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxU hxDrop
        exact (Finset.mem_sdiff.mp hxDrop).2 (huSub hxU)
      have hblocksSubset : controlBlockUnion blocks ⊆ s' ∪ controlBlockUnion baseBlocks := by
        intro x hx
        have hxUnion : x ∈ u ∪ controlBlockUnion blocks := Finset.mem_union.mpr (Or.inr hx)
        simpa [hunion] using hxUnion
      have hsBase : Disjoint s (controlBlockUnion baseBlocks) :=
        disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
      have hdropUnion : Disjoint (s \ s') (s' ∪ controlBlockUnion baseBlocks) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxDrop hxUnion
        rcases Finset.mem_union.mp hxUnion with hxS' | hxBase
        · exact (Finset.mem_sdiff.mp hxDrop).2 hxS'
        · exact (Finset.disjoint_left.mp hsBase) (Finset.mem_sdiff.mp hxDrop).1 hxBase
      have hdropBlocks : Disjoint (s \ s') (controlBlockUnion blocks) :=
        hdropUnion.mono_right hblocksSubset
      have hsepNew : ControlBlocksSeparated u (((s \ s'), eDrop) :: blocks) := by
        exact ⟨huDrop, hdropBlocks, hsepTail⟩
      have hunionNew :
          u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks) =
            s ∪ controlBlockUnion baseBlocks := by
        calc
          u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks)
              = (s \ s') ∪ (u ∪ controlBlockUnion blocks) := by
                  simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                    Finset.union_comm]
          _ = (s \ s') ∪ (s' ∪ controlBlockUnion baseBlocks) := by rw [hunion]
          _ = s ∪ controlBlockUnion baseBlocks := by
                rw [← Finset.union_assoc, Finset.sdiff_union_of_subset hs']
      have hnonemptyNew : NonemptyControlBlockUnion (((s \ s'), eDrop) :: blocks) := by
        have hsubset :
            controlBlockUnion blocks ⊆ controlBlockUnion (((s \ s'), eDrop) :: blocks) := by
          intro x hx
          simp [controlBlockUnion, hx]
        exact lt_of_lt_of_le hnonemptyTail (Finset.card_le_card hsubset)
      have hdegNew :
          ∀ v w : ↑(u : Set V),
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        intro v w
        have hcastv :
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G (s ∪ controlBlockUnion baseBlocks)).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))⟩ := by
          simpa using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))
              (t := s ∪ controlBlockUnion baseBlocks)
              (h := hunionNew)
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := Finset.mem_union.mpr (Or.inl (hs' (huSub v.2)))))
        have hcastw :
            (inducedOn G (u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
              (inducedOn G (s ∪ controlBlockUnion baseBlocks)).degree
                ⟨w.1, Finset.mem_union.mpr (Or.inl (hs' (huSub w.2)))⟩ := by
          simpa using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ controlBlockUnion (((s \ s'), eDrop) :: blocks))
              (t := s ∪ controlBlockUnion baseBlocks)
              (h := hunionNew)
              (hs := Finset.mem_union.mpr (Or.inl w.2))
              (ht := Finset.mem_union.mpr (Or.inl (hs' (huSub w.2)))))
        simpa [hcastv, hcastw] using hdeg ⟨v.1, huSub v.2⟩ ⟨w.1, huSub w.2⟩
      have hdropConst :
          ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ s')).card ≡ eDrop [MOD q] := by
        intro v
        simpa using hdrop ⟨v.1, huSub v.2⟩
      have hextNew :
          HasConstantModExternalBlockDegrees G u q (((s \ s'), eDrop) :: blocks) := by
        exact ⟨hdropConst, hextTail⟩
      refine ⟨u, ((s \ s'), eDrop) :: blocks, huTerm, ?_, huSubTop, hnonemptyNew, hsepNew,
        hunionNew, hdegNew, hextNew⟩
      simp [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockCascadeWitnessOfCard G k) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, baseBlocks, chain, hku, hnonempty, hsep, hfrom⟩
  rcases exists_controlBlockCascadeExactData_of_hasControlBlockCascadeFrom G hnonempty hsep hfrom with
    ⟨u, blocks, huTerm, _hlen, _huSub, hnonempty', hsep', _hunion, D, hdeg, hext⟩
  refine ⟨u, ?_, blocks, hnonempty', hsep', D, hdeg, hext⟩
  simpa [huTerm] using hku

lemma hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockCascadeWitnessOfCard G k r) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  rcases hcascade with ⟨s, baseBlocks, chain, hku, hlenBound, hnonempty, hsep, hfrom⟩
  rcases exists_controlBlockCascadeExactData_of_hasControlBlockCascadeFrom G hnonempty hsep hfrom
    with ⟨u, blocks, huTerm, hlen, _huSub, hnonempty', hsep', _hunion, D, hdeg, hext⟩
  refine ⟨u, ?_, blocks, ?_, hnonempty', hsep', D, hdeg, hext⟩
  · simpa [huTerm] using hku
  · simpa [hlen] using hlenBound

lemma hasControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockCascadeWitnessOfCard G k r) :
    HasControlBlockCascadeWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, baseBlocks, chain, hku, _hlen, hnonempty, hsep, hfrom⟩
  exact ⟨s, baseBlocks, chain, hku, hnonempty, hsep, hfrom⟩

lemma hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockCascadeWitnessOfCard G k) :
    HasControlBlockModularCascadeWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, baseBlocks, chain, hku, hnonempty, hsep, hfrom⟩
  refine ⟨s, (cascadeTerminal s chain).card, baseBlocks, chain, hku, le_rfl, hnonempty, hsep, ?_⟩
  exact hasControlBlockModularCascadeFrom_of_hasControlBlockCascadeFrom G
    (cascadeTerminal s chain).card hfrom

lemma hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockCascadeWitnessOfCard G k r) :
    HasBoundedControlBlockModularCascadeWitnessOfCard G k r := by
  classical
  rcases hcascade with ⟨s, baseBlocks, chain, hku, hlen, hnonempty, hsep, hfrom⟩
  refine ⟨s, (cascadeTerminal s chain).card, baseBlocks, chain, hku, le_rfl, hlen, hnonempty, hsep, ?_⟩
  exact hasControlBlockModularCascadeFrom_of_hasControlBlockCascadeFrom G
    (cascadeTerminal s chain).card hfrom

lemma hasControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockModularCascadeWitnessOfCard G k r) :
    HasControlBlockModularCascadeWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, q, baseBlocks, chain, hku, hq, _hlen, hnonempty, hsep, hfrom⟩
  exact ⟨s, q, baseBlocks, chain, hku, hq, hnonempty, hsep, hfrom⟩

lemma hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockModularCascadeWitnessOfCard G k) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  rcases hcascade with ⟨s, q, baseBlocks, chain, hku, hq, hnonempty, hsep, hfrom⟩
  rcases exists_controlBlockCascadeModularData_of_hasControlBlockModularCascadeFrom G hnonempty hsep
      hfrom with
    ⟨u, blocks, huTerm, _hlen, _huSub, hnonempty', hsep', _hunion, hdeg, hext⟩
  refine ⟨u, u, ?_, subset_rfl, q, ?_, blocks, hnonempty', hsep', ?_, ?_, hext⟩
  · simpa [huTerm] using hku
  · simpa [huTerm] using hq
  · intro v w
    have hcastv :
        (inducedOn G (u ∪ ((u \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((u \ u) ∪ controlBlockUnion blocks))
          (t := u ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (u ∪ ((u \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((u \ u) ∪ controlBlockUnion blocks))
          (t := u ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

lemma hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockModularCascadeWitnessOfCard G k r) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  classical
  rcases hcascade with ⟨s, q, baseBlocks, chain, hku, hq, hlenBound, hnonempty, hsep, hfrom⟩
  rcases exists_controlBlockCascadeModularData_of_hasControlBlockModularCascadeFrom G hnonempty hsep
      hfrom with
    ⟨u, blocks, huTerm, hlen, _huSub, hnonempty', hsep', _hunion, hdeg, hext⟩
  refine ⟨u, u, ?_, subset_rfl, q, ?_, blocks, ?_, hnonempty', hsep', ?_, ?_, hext⟩
  · simpa [huTerm] using hku
  · simpa [huTerm] using hq
  · simpa [hlen] using hlenBound
  · intro v w
    have hcastv :
        (inducedOn G (u ∪ ((u \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((u \ u) ∪ controlBlockUnion blocks))
          (t := u ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (u ∪ ((u \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((u \ u) ∪ controlBlockUnion blocks))
          (t := u ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

lemma hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockModularBucketingWitnessOfCard G k) :
    HasControlBlockModularCascadeWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, q, hq, blocks, hnonempty, hsep, hdeg, hdrop, hext⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropBlocks : Disjoint (s \ u) (controlBlockUnion blocks) := by
    have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
      disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxBlock
    exact (Finset.disjoint_left.mp hsBlocks) (Finset.mem_sdiff.mp hxDrop).1 hxBlock
  have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hus hsep
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := controlBlockUnion blocks) huDrop hdropBlocks hdeg hdrop
  refine ⟨u, q, blocks, [], ?_, hq, hnonempty, hsepU, ?_⟩
  · simpa [cascadeTerminal] using hku
  · exact ⟨hsmall, hext⟩

lemma hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasBoundedControlBlockModularCascadeWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, q, hq, blocks, hlen, hnonempty, hsep, hdeg, hdrop, hext⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropBlocks : Disjoint (s \ u) (controlBlockUnion blocks) := by
    have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
      disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxBlock
    exact (Finset.disjoint_left.mp hsBlocks) (Finset.mem_sdiff.mp hxDrop).1 hxBlock
  have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hus hsep
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := controlBlockUnion blocks) huDrop hdropBlocks hdeg hdrop
  refine ⟨u, q, blocks, [], ?_, hq, ?_, hnonempty, hsepU, ?_⟩
  · simpa [cascadeTerminal] using hku
  · simpa using hlen
  · exact ⟨hsmall, hext⟩

lemma hasControlBlockModularBucketingWitnessOfCard_of_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  refine ⟨u, s, hku, hu, q, hq, blocks, hnonempty, hsep, ?_, ?_, ?_⟩
  intro v w
  have hAmbient :
      u ∪ ((s \ u) ∪ controlBlockUnion blocks) = s ∪ controlBlockUnion blocks := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxU | hxRest
      · exact Finset.mem_union.mpr (Or.inl (hu hxU))
      · rcases Finset.mem_union.mp hxRest with hxDrop | hxBlocks
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
        · exact Finset.mem_union.mpr (Or.inr hxBlocks)
    · intro hx
      rcases Finset.mem_union.mp hx with hxS | hxBlocks
      · by_cases hxu : x ∈ u
        · exact Finset.mem_union.mpr (Or.inl hxu)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hxBlocks)))
  have hcastv :
      (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
          ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
          ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
    simpa using
      (inducedOn_degree_congr (G := G)
        (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
        (t := s ∪ controlBlockUnion blocks)
        (h := hAmbient)
        (hs := Finset.mem_union.mpr (Or.inl v.2))
        (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
  have hcastw :
      (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
          ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
          ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
    simpa using
      (inducedOn_degree_congr (G := G)
        (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
        (t := s ∪ controlBlockUnion blocks)
        (h := hAmbient)
        (hs := Finset.mem_union.mpr (Or.inl w.2))
        (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
  have hcastv' :
      (inducedOn G (u ∪ (s \ u ∪ controlBlockUnion blocks))).degree
          ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
          ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
    simpa [Finset.union_assoc] using hcastv
  have hcastw' :
      (inducedOn G (u ∪ (s \ u ∪ controlBlockUnion blocks))).degree
          ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
          ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
    simpa [Finset.union_assoc] using hcastw
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  simpa [hcastv', hcastw'] using hdeg v w
  · intro v w
    cases
      Subsingleton.elim (‹DecidableRel G.Adj›)
        (fun a b => Classical.propDecidable (G.Adj a b))
    exact hdrop v w
  · cases
      Subsingleton.elim (‹DecidableRel G.Adj›)
        (fun a b => Classical.propDecidable (G.Adj a b))
    exact hext

lemma hasControlBlockModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropBlocks : Disjoint (s \ u) (controlBlockUnion blocks) := by
    have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
      disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxBlocks
    exact (Finset.disjoint_left.mp hsBlocks) (Finset.mem_sdiff.mp hxDrop).1 hxBlocks
  have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hu hsep
  have huMod : InducesModEqDegree G u q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
      (G := G) (s := u) (q := q) hsepU hsmall hext
  have hhost' :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hhost v w
  have hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q] := by
    exact modEq_externalDegree_of_modEq_unionDegree_and_inducesModEqDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' huMod
  have hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := controlBlockUnion blocks) huDrop hdropBlocks hsmall hdrop
  have hbig' :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q] := by
    intro v w
    have hAmbient :
        u ∪ ((s \ u) ∪ controlBlockUnion blocks) = s ∪ controlBlockUnion blocks := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxU | hxRest
        · exact Finset.mem_union.mpr (Or.inl (hu hxU))
        · rcases Finset.mem_union.mp hxRest with hxDrop | hxBlocks
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
          · exact Finset.mem_union.mpr (Or.inr hxBlocks)
      · intro hx
        rcases Finset.mem_union.mp hx with hxS | hxBlocks
        · by_cases hxu : x ∈ u
          · exact Finset.mem_union.mpr (Or.inl hxu)
          · exact
              Finset.mem_union.mpr
                (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hxBlocks)))
    have hcastv :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
    have hcastw :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
    simpa [hcastv, hcastw] using hbig v w
  exact hasControlBlockModularBucketingWitnessOfCard_of_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G := G) hku hu hq hnonempty hsep hbig' hdrop hext

lemma hasExactControlBlockWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {d q : ℕ} (hinterval : InducesDegreeInterval G u d q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : HasConstantExternalBlockDegrees G u blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropBlocks : Disjoint (s \ u) (controlBlockUnion blocks) := by
    have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
      disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxBlock
    exact (Finset.disjoint_left.mp hsBlocks) (Finset.mem_sdiff.mp hxDrop).1 hxBlock
  have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hu hsep
  have hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hAmbient :
        u ∪ ((s \ u) ∪ controlBlockUnion blocks) = s ∪ controlBlockUnion blocks := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxU | hxRest
        · exact Finset.mem_union.mpr (Or.inl (hu hxU))
        · rcases Finset.mem_union.mp hxRest with hxDrop | hxBlocks
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
          · exact Finset.mem_union.mpr (Or.inr hxBlocks)
      · intro hx
        rcases Finset.mem_union.mp hx with hxS | hxBlocks
        · by_cases hxu : x ∈ u
          · exact Finset.mem_union.mpr (Or.inl hxu)
          · exact
              Finset.mem_union.mpr
                (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hxBlocks)))
    have hcastv :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
    have hcastw :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
    simpa [hcastv, hcastw] using hdeg v w
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := controlBlockUnion blocks) huDrop hdropBlocks hbig hdrop
  exact hasExactControlBlockWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalBlockDegrees
    (G := G) (s := u) (hks := hku) (d := d) (q := q) hinterval hnonempty hsepU hsmall hext

lemma hasExactControlBlockWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : HasConstantExternalBlockDegrees G u blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine
    hasExactControlBlockWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
      (G := G) (hku := hku) (hu := hu) (d := 0) ?_ hnonempty hsep hdeg hdrop hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G u) v)) hq

lemma hasControlBlockModularBucketingWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasNonemptyControlBlockModularWitnessOfCard G k) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, hnonempty, hsep, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, q, hq, blocks, hnonempty, hsep, ?_, ?_, hext⟩
  · intro v w
    have hcastv :
        (inducedOn G (s ∪ ((s \ s) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (s ∪ ((s \ s) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

lemma hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedNonemptyControlBlockModularWitnessOfCard G k r) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, q, hq, blocks, hlen, hnonempty, hsep, ?_, ?_, hext⟩
  · intro v w
    have hcastv :
        (inducedOn G (s ∪ ((s \ s) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (s ∪ ((s \ s) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

theorem hasNonemptyControlBlockModularWitnessOfCard_iff_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasNonemptyControlBlockModularWitnessOfCard G k ↔
      HasControlBlockModularBucketingWitnessOfCard G k := by
  constructor
  · exact hasControlBlockModularBucketingWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
  · exact hasNonemptyControlBlockModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G

theorem hasBoundedNonemptyControlBlockModularWitnessOfCard_iff_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedNonemptyControlBlockModularWitnessOfCard G k r ↔
      HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  constructor
  · exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard G
  · exact hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G

theorem hasControlBlockModularBucketingWitnessOfCard_iff_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasControlBlockModularBucketingWitnessOfCard G k ↔
      HasControlBlockModularCascadeWitnessOfCard G k := by
  constructor
  · exact hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
  · exact hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard G

theorem hasBoundedControlBlockModularBucketingWitnessOfCard_iff_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r ↔
      HasBoundedControlBlockModularCascadeWitnessOfCard G k r := by
  constructor
  · exact hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G
  · exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard G

theorem hasNonemptyControlBlockModularWitnessOfCard_iff_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasNonemptyControlBlockModularWitnessOfCard G k ↔
      HasControlBlockModularCascadeWitnessOfCard G k := by
  rw [hasNonemptyControlBlockModularWitnessOfCard_iff_hasControlBlockModularBucketingWitnessOfCard,
    hasControlBlockModularBucketingWitnessOfCard_iff_hasControlBlockModularCascadeWitnessOfCard]

theorem hasBoundedNonemptyControlBlockModularWitnessOfCard_iff_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedNonemptyControlBlockModularWitnessOfCard G k r ↔
      HasBoundedControlBlockModularCascadeWitnessOfCard G k r := by
  rw [hasBoundedNonemptyControlBlockModularWitnessOfCard_iff_hasBoundedControlBlockModularBucketingWitnessOfCard,
    hasBoundedControlBlockModularBucketingWitnessOfCard_iff_hasBoundedControlBlockModularCascadeWitnessOfCard]

theorem hasSingleControlModularWitnessOfCard_iff_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlModularWitnessOfCard G k ↔
      HasControlBlockModularBucketingWitnessOfCard G k := by
  rw [hasSingleControlModularWitnessOfCard_iff_hasNonemptyControlBlockModularWitnessOfCard,
    hasNonemptyControlBlockModularWitnessOfCard_iff_hasControlBlockModularBucketingWitnessOfCard]

theorem hasSingleControlModularWitnessOfCard_iff_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlModularWitnessOfCard G k ↔
      HasControlBlockModularCascadeWitnessOfCard G k := by
  rw [hasSingleControlModularWitnessOfCard_iff_hasNonemptyControlBlockModularWitnessOfCard,
    hasNonemptyControlBlockModularWitnessOfCard_iff_hasControlBlockModularCascadeWitnessOfCard]

lemma hasControlBlockWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockModularCascadeWitnessOfCard G k) :
    HasControlBlockWitnessOfCard G k := by
  exact hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard
      G hcascade)

lemma hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockModularCascadeWitnessOfCard G k r) :
    HasControlBlockWitnessOfCard G k := by
  exact hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G
    (hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
      G hcascade)

lemma hasModularWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockModularCascadeWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard G hcascade)

lemma hasModularWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockModularCascadeWitnessOfCard G k r) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard G hcascade)

lemma hasRegularInducedSubgraphOfCard_of_hasControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockModularCascadeWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard G hcascade)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockModularCascadeWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard G hcascade)

lemma hasRegularInducedSubgraphOfCard_of_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockCascadeWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G hcascade)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockCascadeWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
      (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
        G hcascade))

lemma hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasControlBlockCascadeWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, blocks, [], ?_, hnonempty, hsep, D, hdeg, hext⟩
  simpa [cascadeTerminal]

lemma hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hexact : HasBoundedExactControlBlockWitnessOfCard G k r) :
    HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  classical
  rcases hexact with ⟨s, hks, blocks, hlen, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, blocks, [], ?_, ?_, hnonempty, hsep, D, hdeg, hext⟩
  · simpa [cascadeTerminal]
  · simpa using hlen

theorem hasExactControlBlockWitnessOfCard_iff_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasExactControlBlockWitnessOfCard G k ↔ HasControlBlockCascadeWitnessOfCard G k := by
  constructor
  · exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
  · exact hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G

theorem hasBoundedExactControlBlockWitnessOfCard_iff_hasBoundedControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedExactControlBlockWitnessOfCard G k r ↔
      HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  constructor
  · exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
  · exact hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard G

lemma hasControlBlockCascadeWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasSingleControlCascadeWitnessOfCard G k) :
    HasControlBlockCascadeWitnessOfCard G k := by
  exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G hcascade)

lemma hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedSingleControlCascadeWitnessOfCard G k r) :
    HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard G
      hcascade)

lemma hasControlBlockBucketingWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hcascade : HasControlBlockCascadeWitnessOfCard G k) :
    HasControlBlockBucketingWitnessOfCard G k := by
  exact hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G hcascade)

lemma hasControlBlockCascadeWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockBucketingWitnessOfCard G k) :
    HasControlBlockCascadeWitnessOfCard G k := by
  exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G hbuck)

theorem hasControlBlockBucketingWitnessOfCard_iff_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasControlBlockBucketingWitnessOfCard G k ↔ HasControlBlockCascadeWitnessOfCard G k := by
  constructor
  · exact hasControlBlockCascadeWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G
  · exact hasControlBlockBucketingWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G

theorem hasSingleControlExactWitnessOfCard_iff_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlExactWitnessOfCard G k ↔ HasControlBlockBucketingWitnessOfCard G k := by
  rw [hasSingleControlExactWitnessOfCard_iff_hasExactControlBlockWitnessOfCard,
    hasExactControlBlockWitnessOfCard_iff_hasControlBlockBucketingWitnessOfCard]

theorem hasSingleControlExactWitnessOfCard_iff_hasControlBlockCascadeWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlExactWitnessOfCard G k ↔ HasControlBlockCascadeWitnessOfCard G k := by
  rw [hasSingleControlExactWitnessOfCard_iff_hasExactControlBlockWitnessOfCard,
    hasExactControlBlockWitnessOfCard_iff_hasControlBlockCascadeWitnessOfCard]

lemma hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockBucketingWitnessOfCard G k r) :
    HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard G
      hbuck)

lemma hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard_succ
    (G : SimpleGraph V) {k r : ℕ}
    (hcascade : HasBoundedControlBlockCascadeWitnessOfCard G k r) :
    HasBoundedControlBlockBucketingWitnessOfCard G k (r + 1) := by
  exact hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard_succ
    G
    (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard G
      hcascade)

lemma exists_large_fiber_of_mul_le_card
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (f : α → β) {n : ℕ} (hn : Fintype.card β * n ≤ s.card) :
    ∃ y : β, n ≤ (s.filter fun x => f x = y).card := by
  classical
  simpa [Finset.card_univ] using
    (Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := s) (t := (Finset.univ : Finset β)) (f := f)
      (hf := by intro a ha; simp)
      (ht := Finset.univ_nonempty)
      (hn := by simpa [Finset.card_univ] using hn))

lemma exists_large_mod_class_of_mul_le_card
    {α : Type*} [DecidableEq α] (s : Finset α) {q n : ℕ} (hq : 0 < q) (f : α → Fin q)
    (hn : q * n ≤ s.card) :
    ∃ r : Fin q, n ≤ (s.filter fun x => f x = r).card := by
  classical
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  simpa [Fintype.card_fin] using
    (exists_large_fiber_of_mul_le_card (s := s) (β := Fin q) (f := f)
      (hn := by simpa [Fintype.card_fin] using hn))

lemma exists_large_fiber_of_mul_pred_lt_card
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (f : α → β) {n : ℕ} (hn : Fintype.card β * (n - 1) < s.card) :
    ∃ y : β, n ≤ (s.filter fun x => f x = y).card := by
  classical
  cases n with
  | zero =>
      exact ⟨Classical.choice ‹Nonempty β›, Nat.zero_le _⟩
  | succ n =>
      rcases
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (s := s) (t := (Finset.univ : Finset β)) (f := f)
            (hf := by intro a ha; simp)
            (hn := by simpa [Finset.card_univ] using hn) with
        ⟨y, _hy, hlt⟩
      exact ⟨y, Nat.succ_le_of_lt (by simpa using hlt)⟩

lemma exists_large_mod_class_of_mul_pred_lt_card
    {α : Type*} [DecidableEq α] (s : Finset α) {q n : ℕ} (hq : 0 < q) (f : α → Fin q)
    (hn : q * (n - 1) < s.card) :
    ∃ r : Fin q, n ≤ (s.filter fun x => f x = r).card := by
  classical
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  simpa [Fintype.card_fin] using
    (exists_large_fiber_of_mul_pred_lt_card (s := s) (β := Fin q) (f := f)
      (hn := by simpa [Fintype.card_fin] using hn))

lemma exists_large_subset_with_constant_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) {k : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) :
    ∃ u : Finset V, u ⊆ s ∧ k ≤ u.card ∧
      ∃ e : ℕ, ∀ x ∈ u, (G.neighborFinset x ∩ t).card = e := by
  classical
  let f : V → Fin (t.card + 1) := fun x =>
    ⟨(G.neighborFinset x ∩ t).card,
      lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) (Nat.lt_succ_self t.card)⟩
  obtain ⟨r, hr⟩ := exists_large_mod_class_of_mul_le_card
    (s := s) (q := t.card + 1) (n := k) (hq := Nat.succ_pos _) (f := f)
    (hn := by simpa [Nat.succ_eq_add_one] using hsize)
  refine ⟨s.filter (fun x => f x = r), Finset.filter_subset _ _, hr, r.1, ?_⟩
  intro x hx
  have hxEq : f x = r := (Finset.mem_filter.mp hx).2
  simpa [f] using congrArg Fin.val hxEq

lemma exists_large_subset_with_constant_externalDegree_of_mul_pred_lt_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) {k : ℕ}
    (hsize : (t.card + 1) * (k - 1) < s.card) :
    ∃ u : Finset V, u ⊆ s ∧ k ≤ u.card ∧
      ∃ e : ℕ, ∀ x ∈ u, (G.neighborFinset x ∩ t).card = e := by
  classical
  let f : V → Fin (t.card + 1) := fun x =>
    ⟨(G.neighborFinset x ∩ t).card,
      lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) (Nat.lt_succ_self t.card)⟩
  obtain ⟨r, hr⟩ := exists_large_mod_class_of_mul_pred_lt_card
    (s := s) (q := t.card + 1) (n := k) (hq := Nat.succ_pos _) (f := f)
    (hn := by simpa [Nat.succ_eq_add_one] using hsize)
  refine ⟨s.filter (fun x => f x = r), Finset.filter_subset _ _, hr, r.1, ?_⟩
  intro x hx
  have hxEq : f x = r := (Finset.mem_filter.mp hx).2
  simpa [f] using congrArg Fin.val hxEq

lemma exists_large_subset_with_constant_externalDegree_and_hostDegree_of_constant_unionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {k D : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) (hst : Disjoint s t)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ e d : ℕ,
        (∀ x ∈ u, (G.neighborFinset x ∩ t).card = e) ∧
        (∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d) := by
  classical
  rcases exists_large_subset_with_constant_externalDegree (G := G) s t hsize with
    ⟨u, hus, hku, e, hctrl⟩
  have hconstRaw :
      ∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - e := by
    have hut : Disjoint u t := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxU hxT
      exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
    have htu : Disjoint t (s \ u) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxT hxDrop
      exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
    exact constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := t) (u := s \ u) hut htu
      (hdeg := by
        intro v
        have hUnion : u ∪ (t ∪ (s \ u)) = s ∪ t := by
          calc
            u ∪ (t ∪ (s \ u)) = (u ∪ (s \ u)) ∪ t := by
              simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
            _ = s ∪ t := by
              rw [Finset.union_comm u, Finset.sdiff_union_of_subset hus]
        have hcast :
            (inducedOn G (u ∪ (t ∪ (s \ u)))).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
              (inducedOn G (s ∪ t)).degree
                ⟨v.1, Finset.mem_union.mpr (Or.inl (hus v.2))⟩ := by
          simpa using
            (inducedOn_degree_congr (G := G)
              (s := u ∪ (t ∪ (s \ u))) (t := s ∪ t)
              (h := hUnion)
              (hs := Finset.mem_union.mpr (Or.inl v.2))
              (ht := Finset.mem_union.mpr (Or.inl (hus v.2))))
        exact hcast.trans (hdeg ⟨v.1, hus v.2⟩))
      (hext := by
        intro v
        exact hctrl v.1 v.2)
  have hconst :
      ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hus v.2⟩ = D - e := by
    intro v
    have hcast :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hus v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hus])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hus v.2))
    exact hcast.symm.trans (hconstRaw v)
  refine ⟨u, hus, hku, e, D - e, ?_, ?_⟩
  · intro x hx
    exact hctrl x hx
  · intro v
    exact hconst v

lemma exists_large_subset_with_constant_hostDegree_of_constant_unionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {k D : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) (hst : Disjoint s t)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  rcases
      exists_large_subset_with_constant_externalDegree_and_hostDegree_of_constant_unionDegree_and_card_bound
        (G := G) hsize hst hdeg with
    ⟨u, hu, hku, _e, d, _hext, hconst⟩
  exact ⟨u, hu, hku, d, hconst⟩

lemma exists_subset_with_constant_externalDegree_and_hostDegree_of_constant_unionDegree_and_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {k D : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) (hst : Disjoint s t)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ e d : ℕ,
        (∀ x ∈ u, (G.neighborFinset x ∩ t).card = e) ∧
        (∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d) := by
  rcases
      exists_large_subset_with_constant_externalDegree_and_hostDegree_of_constant_unionDegree_and_card_bound
        (G := G) hsize hst hdeg with
    ⟨u₁, hu₁, hku₁, e, d, hextU₁, hconstU₁⟩
  rcases exists_subset_card_eq_of_le_card hku₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  refine ⟨u, hu, hcardu, e, d, ?_, ?_⟩
  · intro x hx
    exact hextU₁ x (huu₁ hx)
  · intro v
    simpa [hu] using hconstU₁ ⟨v.1, huu₁ v.2⟩

lemma exists_subset_with_constant_hostDegree_of_constant_unionDegree_and_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {k D : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) (hst : Disjoint s t)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  rcases
      exists_subset_with_constant_externalDegree_and_hostDegree_of_constant_unionDegree_and_card_eq
        (G := G) hsize hst hdeg with
    ⟨u, hu, hcardu, _e, d, _hextU, hconstU⟩
  exact ⟨u, hu, hcardu, d, hconstU⟩

def controlBlockBucketCost : List (Finset V × ℕ) → ℕ
  | [] => 1
  | b :: bs => (b.1.card + 1) * controlBlockBucketCost bs

lemma exists_large_subset_with_constant_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (s : Finset V) {blocks : List (Finset V × ℕ)} {k : ℕ},
      controlBlockBucketCost blocks * k ≤ s.card →
      ControlBlocksSeparated s blocks →
      ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
        ∃ blocks' : List (Finset V × ℕ),
          SameControlBlockSupports blocks' blocks ∧
          ControlBlocksSeparated u blocks' ∧
          HasConstantExternalBlockDegrees G u blocks'
  | s, [], k, hsize, _hsep => by
      refine ⟨s, by intro x hx; exact hx, ?_, [], ?_, ?_, ?_⟩
      · simpa [controlBlockBucketCost] using hsize
      · trivial
      · trivial
      · trivial
  | s, (b :: bs), k, hsize, hsep => by
      rcases b with ⟨t, _e₀⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      have hsizeHead : (t.card + 1) * (controlBlockBucketCost bs * k) ≤ s.card := by
        simpa [controlBlockBucketCost, Nat.mul_assoc] using hsize
      rcases exists_large_subset_with_constant_externalDegree
          (G := G) (s := s) (t := t) (k := controlBlockBucketCost bs * k) hsizeHead with
        ⟨u₁, hu₁, hku₁, e, hctrl⟩
      have hsepTailU₁ : ControlBlocksSeparated u₁ bs :=
        controlBlocksSeparated_mono hu₁ hsepTail
      rcases exists_large_subset_with_constant_externalBlockDegrees
          (G := G) (s := u₁) (blocks := bs) (k := k) hku₁ hsepTailU₁ with
        ⟨u, huu₁, hku, blocks', hsameTail, hsepU, hextTail⟩
      refine ⟨u, fun x hx => hu₁ (huu₁ hx), hku, (t, e) :: blocks', ?_, ?_, ?_⟩
      · exact ⟨rfl, hsameTail⟩
      · refine ⟨?_, ?_, hsepU⟩
        · refine Finset.disjoint_left.mpr ?_
          intro x hxU hxT
          exact (Finset.disjoint_left.mp hst) (hu₁ (huu₁ hxU)) hxT
        · rw [controlBlockUnion_eq_of_sameControlBlockSupports hsameTail]
          exact htu
      · refine ⟨?_, hextTail⟩
        intro v
        exact hctrl v.1 (huu₁ v.2)

lemma exists_large_subset_with_constant_externalBlockDegrees_of_mul_pred_lt_card
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (s : Finset V) {blocks : List (Finset V × ℕ)} {k : ℕ},
      controlBlockBucketCost blocks * (k - 1) < s.card →
      ControlBlocksSeparated s blocks →
      ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
        ∃ blocks' : List (Finset V × ℕ),
          SameControlBlockSupports blocks' blocks ∧
          ControlBlocksSeparated u blocks' ∧
          HasConstantExternalBlockDegrees G u blocks'
  | s, [], k, hsize, _hsep => by
      refine ⟨s, by intro x hx; exact hx, ?_, [], ?_, ?_, ?_⟩
      · cases k with
        | zero => exact Nat.zero_le _
        | succ k =>
            simpa [controlBlockBucketCost] using Nat.succ_le_of_lt hsize
      · trivial
      · trivial
      · trivial
  | s, (b :: bs), k, hsize, hsep => by
      rcases b with ⟨t, _e₀⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      have hsizeHead :
          (t.card + 1) * ((controlBlockBucketCost bs * (k - 1) + 1) - 1) < s.card := by
        simpa [controlBlockBucketCost, Nat.mul_assoc] using hsize
      rcases exists_large_subset_with_constant_externalDegree_of_mul_pred_lt_card
          (G := G) (s := s) (t := t) (k := controlBlockBucketCost bs * (k - 1) + 1) hsizeHead with
        ⟨u₁, hu₁, hku₁, e, hctrl⟩
      have hsizeTail : controlBlockBucketCost bs * (k - 1) < u₁.card := by
        exact lt_of_lt_of_le (Nat.lt_succ_self _) hku₁
      have hsepTailU₁ : ControlBlocksSeparated u₁ bs :=
        controlBlocksSeparated_mono hu₁ hsepTail
      rcases exists_large_subset_with_constant_externalBlockDegrees_of_mul_pred_lt_card
          (G := G) (s := u₁) (blocks := bs) (k := k) hsizeTail hsepTailU₁ with
        ⟨u, huu₁, hku, blocks', hsameTail, hsepU, hextTail⟩
      refine ⟨u, fun x hx => hu₁ (huu₁ hx), hku, (t, e) :: blocks', ?_, ?_, ?_⟩
      · exact ⟨rfl, hsameTail⟩
      · refine ⟨?_, ?_, hsepU⟩
        · refine Finset.disjoint_left.mpr ?_
          intro x hxU hxT
          exact (Finset.disjoint_left.mp hst) (hu₁ (huu₁ hxU)) hxT
        · rw [controlBlockUnion_eq_of_sameControlBlockSupports hsameTail]
          exact htu
      · refine ⟨?_, hextTail⟩
        intro v
        exact hctrl v.1 (huu₁ v.2)

lemma exists_large_subset_with_constant_twoExternalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t₁ t₂ : Finset V) {k : ℕ}
    (hsize : (t₁.card + 1) * (t₂.card + 1) * k ≤ s.card) :
    ∃ u : Finset V, u ⊆ s ∧ k ≤ u.card ∧
      ∃ e₁ e₂ : ℕ,
        ∀ x ∈ u,
          (G.neighborFinset x ∩ t₁).card = e₁ ∧
            (G.neighborFinset x ∩ t₂).card = e₂ := by
  classical
  let f : V → Fin (t₁.card + 1) × Fin (t₂.card + 1) := fun x =>
    (⟨(G.neighborFinset x ∩ t₁).card,
        lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) (Nat.lt_succ_self t₁.card)⟩,
      ⟨(G.neighborFinset x ∩ t₂).card,
        lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) (Nat.lt_succ_self t₂.card)⟩)
  obtain ⟨y, hy⟩ := exists_large_fiber_of_mul_le_card
    (s := s) (β := Fin (t₁.card + 1) × Fin (t₂.card + 1)) (f := f)
    (hn := by
      simpa [Fintype.card_fin, Fintype.card_prod, Nat.mul_assoc] using hsize)
  rcases y with ⟨a, b⟩
  refine ⟨s.filter (fun x => f x = (a, b)), Finset.filter_subset _ _, hy, a.1, b.1, ?_⟩
  intro x hx
  have hxy : f x = (a, b) := (Finset.mem_filter.mp hx).2
  have hx₁ : (f x).1 = a := congrArg Prod.fst hxy
  have hx₂ : (f x).2 = b := congrArg Prod.snd hxy
  constructor
  · simpa [f] using congrArg Fin.val hx₁
  · simpa [f] using congrArg Fin.val hx₂

lemma exists_large_subset_with_constant_hostDegree_of_constant_twoBlockUnionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t₁ t₂ : Finset V} {k D : ℕ}
    (hsize : (t₁.card + 1) * (t₂.card + 1) * k ≤ s.card)
    (hst : Disjoint s (t₁ ∪ t₂)) (ht : Disjoint t₁ t₂)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  classical
  rcases exists_large_subset_with_constant_twoExternalDegrees (G := G) s t₁ t₂ hsize with
    ⟨u, hus, hku, e₁, e₂, hpair⟩
  have hconstRaw :
      ∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          D - (e₁ + e₂) := by
    have hut : Disjoint u (t₁ ∪ t₂) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxU hxT
      exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
    have htu : Disjoint (t₁ ∪ t₂) (s \ u) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxT hxDrop
      exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
    exact
      constant_unionDegree_of_constant_extendedUnionDegree_and_two_externalDegrees
        (G := G) (s := u) (t₁ := t₁) (t₂ := t₂) (u := s \ u) hut htu ht
        (hdeg := by
          intro v
          have hUnion : u ∪ ((t₁ ∪ t₂) ∪ (s \ u)) = s ∪ (t₁ ∪ t₂) := by
            calc
              u ∪ ((t₁ ∪ t₂) ∪ (s \ u)) = (u ∪ (s \ u)) ∪ (t₁ ∪ t₂) := by
                  simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
              _ = s ∪ (t₁ ∪ t₂) := by
                  rw [Finset.union_comm u, Finset.sdiff_union_of_subset hus]
          have hcast :
              (inducedOn G (u ∪ ((t₁ ∪ t₂) ∪ (s \ u)))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                (inducedOn G (s ∪ (t₁ ∪ t₂))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hus v.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ ((t₁ ∪ t₂) ∪ (s \ u))) (t := s ∪ (t₁ ∪ t₂))
                (h := hUnion)
                (hs := Finset.mem_union.mpr (Or.inl v.2))
                (ht := Finset.mem_union.mpr (Or.inl (hus v.2))))
          exact hcast.trans (hdeg ⟨v.1, hus v.2⟩))
        (hext₁ := by
          intro v
          exact (hpair v.1 v.2).1)
        (hext₂ := by
          intro v
          exact (hpair v.1 v.2).2)
  have hconst :
      ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hus v.2⟩ = D - (e₁ + e₂) := by
    intro v
    have hcast :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hus v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hus])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hus v.2))
    exact hcast.symm.trans (hconstRaw v)
  refine ⟨u, hus, hku, D - (e₁ + e₂), ?_⟩
  intro v
  exact hconst v

lemma exists_large_subset_with_constant_externalBlockDegrees_and_hostDegree_of_constant_blockUnionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {k D : ℕ}
    (hsize : controlBlockBucketCost blocks * k ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ blocks' : List (Finset V × ℕ),
        SameControlBlockSupports blocks' blocks ∧
        ControlBlocksSeparated u blocks' ∧
        HasConstantExternalBlockDegrees G u blocks' ∧
        ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  classical
  rcases exists_large_subset_with_constant_externalBlockDegrees
      (G := G) (s := s) (blocks := blocks) (k := k) hsize hsep with
    ⟨u, hu, hku, blocks', hsame, hsepU, hextU⟩
  have hUnionEq : controlBlockUnion blocks' = controlBlockUnion blocks :=
    controlBlockUnion_eq_of_sameControlBlockSupports hsame
  have hUnionDisj : Disjoint s (controlBlockUnion blocks') := by
    rw [hUnionEq]
    exact disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have hUnionDisjDrop : Disjoint (controlBlockUnion blocks') (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxBlocks hxDrop
    exact (Finset.disjoint_left.mp hUnionDisj.symm) hxBlocks (Finset.mem_sdiff.mp hxDrop).1
  have hconstRaw :
      ∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          D - controlBlockDegreeSum blocks' := by
    exact
      constant_unionDegree_of_constant_extendedUnionDegree_and_externalBlockDegrees
        (G := G) (s := u) (tail := s \ u) (blocks := blocks') (D := D) hsepU hUnionDisjDrop
        (by
          intro v
          have hAmbient :
              u ∪ (controlBlockUnion blocks' ∪ (s \ u)) = s ∪ controlBlockUnion blocks := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_union.mp hx with hxU | hxRest
              · exact Finset.mem_union.mpr (Or.inl (hu hxU))
              · rcases Finset.mem_union.mp hxRest with hxBlocks | hxDrop
                · exact Finset.mem_union.mpr (Or.inr (by simpa [hUnionEq] using hxBlocks))
                · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
            · intro hx
              rcases Finset.mem_union.mp hx with hxS | hxBlocks
              · by_cases hxu : x ∈ u
                · exact Finset.mem_union.mpr (Or.inl hxu)
                · exact
                    Finset.mem_union.mpr
                      (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
              · have hxBlocks' : x ∈ controlBlockUnion blocks' := by
                  rw [hUnionEq]
                  exact hxBlocks
                exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hxBlocks')))
          have hcast :
              (inducedOn G (u ∪ (controlBlockUnion blocks' ∪ (s \ u)))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (controlBlockUnion blocks' ∪ (s \ u)))
                (t := s ∪ controlBlockUnion blocks)
                (h := hAmbient)
                (hs := Finset.mem_union.mpr (Or.inl v.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
          exact hcast.trans (hdeg ⟨v.1, hu v.2⟩))
        hextU
  have hconst :
      ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = D - controlBlockDegreeSum blocks' := by
    intro v
    have hcast :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    exact hcast.symm.trans (hconstRaw v)
  refine ⟨u, hu, hku, blocks', hsame, hsepU, hextU, D - controlBlockDegreeSum blocks', ?_⟩
  intro v
  exact hconst v

lemma exists_large_subset_with_constant_hostDegree_of_constant_blockUnionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {k D : ℕ}
    (hsize : controlBlockBucketCost blocks * k ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  rcases
      exists_large_subset_with_constant_externalBlockDegrees_and_hostDegree_of_constant_blockUnionDegree_and_card_bound
        (G := G) hsize hsep hdeg with
    ⟨u, hu, hku, _blocks', _hsame, _hsepU, _hextU, d, hconst⟩
  exact ⟨u, hu, hku, d, hconst⟩

lemma exists_subset_with_constant_externalBlockDegrees_and_hostDegree_of_constant_blockUnionDegree_and_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {k D : ℕ}
    (hsize : controlBlockBucketCost blocks * k ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ blocks' : List (Finset V × ℕ),
        SameControlBlockSupports blocks' blocks ∧
        ControlBlocksSeparated u blocks' ∧
        HasConstantExternalBlockDegrees G u blocks' ∧
        ∃ d : ℕ,
          ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  rcases
      exists_large_subset_with_constant_externalBlockDegrees_and_hostDegree_of_constant_blockUnionDegree_and_card_bound
        (G := G) hsize hsep hdeg with
    ⟨u₁, hu₁, hku₁, blocks', hsame, hsepU₁, hextU₁, d, hconstU₁⟩
  rcases exists_subset_card_eq_of_le_card hku₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hextU : HasConstantExternalBlockDegrees G u blocks' :=
    hasConstantExternalBlockDegrees_mono (G := G) huu₁ hextU₁
  refine ⟨u, hu, hcardu, blocks', hsame, hsepU, hextU, d, ?_⟩
  intro v
  simpa [hu] using hconstU₁ ⟨v.1, huu₁ v.2⟩

lemma exists_subset_with_constant_hostDegree_of_constant_blockUnionDegree_and_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {k D : ℕ}
    (hsize : controlBlockBucketCost blocks * k ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
  rcases
      exists_subset_with_constant_externalBlockDegrees_and_hostDegree_of_constant_blockUnionDegree_and_card_eq
        (G := G) hsize hsep hdeg with
    ⟨u, hu, hcardu, _blocks', _hsame, _hsepU, _hextU, d, hconst⟩
  exact ⟨u, hu, hcardu, d, hconst⟩

lemma exists_large_subset_with_constant_modExternalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) {q k : ℕ}
    (hq : 0 < q) (hsize : q * k ≤ s.card) :
    ∃ u : Finset V, u ⊆ s ∧ k ≤ u.card ∧
      ∃ r : ℕ, ∀ x ∈ u, (G.neighborFinset x ∩ t).card ≡ r [MOD q] := by
  classical
  let f : V → Fin q := fun x => ⟨(G.neighborFinset x ∩ t).card % q, Nat.mod_lt _ hq⟩
  obtain ⟨r, hr⟩ := exists_large_mod_class_of_mul_le_card
    (s := s) (q := q) (n := k) (hq := hq) (f := f) hsize
  refine ⟨s.filter (fun x => f x = r), Finset.filter_subset _ _, hr, r.1, ?_⟩
  intro x hx
  have hxEq : f x = r := (Finset.mem_filter.mp hx).2
  simpa [Nat.ModEq, f, Nat.mod_eq_of_lt r.2] using congrArg Fin.val hxEq

lemma exists_subset_with_constant_modExternalDegree_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) {q k : ℕ}
    (hq : 0 < q) (hsize : q * k ≤ s.card) :
    ∃ u : Finset V, u ⊆ s ∧ u.card = k ∧
      ∃ r : ℕ, ∀ x ∈ u, (G.neighborFinset x ∩ t).card ≡ r [MOD q] := by
  rcases exists_large_subset_with_constant_modExternalDegree
      (G := G) s t (q := q) (k := k) hq hsize with
    ⟨u₁, hu₁, hku₁, r, hr⟩
  rcases exists_subset_card_eq_of_le_card hku₁ with ⟨u, huu₁, hcardu⟩
  refine ⟨u, ?_, hcardu, r, ?_⟩
  · intro x hx
    exact hu₁ (huu₁ hx)
  · intro x hx
    exact hr x (huu₁ hx)

lemma exists_large_subset_with_constant_modExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (s : Finset V) {q k : ℕ} {blocks : List (Finset V × ℕ)},
      0 < q →
      q ^ blocks.length * k ≤ s.card →
      ControlBlocksSeparated s blocks →
      ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
        ∃ blocks' : List (Finset V × ℕ),
          SameControlBlockSupports blocks' blocks ∧
          ControlBlocksSeparated u blocks' ∧
          HasConstantModExternalBlockDegrees G u q blocks'
  | s, q, k, [], hq, hsize, _hsep => by
      refine ⟨s, by intro x hx; exact hx, ?_, [], ?_, ?_, ?_⟩
      · simpa using hsize
      · trivial
      · trivial
      · trivial
  | s, q, k, (b :: bs), hq, hsize, hsep => by
      rcases b with ⟨t, _r₀⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      have hsizeHead : q * (q ^ bs.length * k) ≤ s.card := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize
      rcases exists_large_subset_with_constant_modExternalDegree
          (G := G) s t (q := q) (k := q ^ bs.length * k) hq hsizeHead with
        ⟨u₁, hu₁, hku₁, r, hctrl⟩
      have hsepTailU₁ : ControlBlocksSeparated u₁ bs :=
        controlBlocksSeparated_mono hu₁ hsepTail
      rcases exists_large_subset_with_constant_modExternalBlockDegrees
          (G := G) (s := u₁) (q := q) (blocks := bs) (k := k) hq hku₁ hsepTailU₁ with
        ⟨u, huu₁, hku, blocks', hsameTail, hsepU, hextTail⟩
      refine ⟨u, fun x hx => hu₁ (huu₁ hx), hku, (t, r) :: blocks', ?_, ?_, ?_⟩
      · exact ⟨rfl, hsameTail⟩
      · refine ⟨?_, ?_, hsepU⟩
        · refine Finset.disjoint_left.mpr ?_
          intro x hxU hxT
          exact (Finset.disjoint_left.mp hst) (hu₁ (huu₁ hxU)) hxT
        · rw [controlBlockUnion_eq_of_sameControlBlockSupports hsameTail]
          exact htu
      · refine ⟨?_, hextTail⟩
        intro v
        exact hctrl v.1 (huu₁ v.2)

lemma exists_large_subset_with_modEq_hostDegree_of_modEq_blockUnionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * k ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  classical
  rcases exists_large_subset_with_constant_modExternalBlockDegrees
      (G := G) (s := s) (q := q) (blocks := blocks) (k := k) hq hsize hsep with
    ⟨u, hu, hku, blocks', hsame, hsepU, hextU⟩
  have hUnionEq : controlBlockUnion blocks' = controlBlockUnion blocks :=
    controlBlockUnion_eq_of_sameControlBlockSupports hsame
  have hUnionDisj : Disjoint s (controlBlockUnion blocks') := by
    rw [hUnionEq]
    exact disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have hUnionDisjDrop : Disjoint (controlBlockUnion blocks') (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxBlocks hxDrop
    exact (Finset.disjoint_left.mp hUnionDisj.symm) hxBlocks (Finset.mem_sdiff.mp hxDrop).1
  have hconstRaw :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalBlockDegrees
        (G := G) (s := u) (tail := s \ u) (q := q) hsepU hUnionDisjDrop
        (by
          intro v w
          have hAmbient :
              u ∪ (controlBlockUnion blocks' ∪ (s \ u)) = s ∪ controlBlockUnion blocks := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_union.mp hx with hxU | hxRest
              · exact Finset.mem_union.mpr (Or.inl (hu hxU))
              · rcases Finset.mem_union.mp hxRest with hxBlocks | hxDrop
                · exact Finset.mem_union.mpr (Or.inr (by simpa [hUnionEq] using hxBlocks))
                · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
            · intro hx
              rcases Finset.mem_union.mp hx with hxS | hxBlocks
              · by_cases hxu : x ∈ u
                · exact Finset.mem_union.mpr (Or.inl hxu)
                · exact
                    Finset.mem_union.mpr
                      (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
              · have hxBlocks' : x ∈ controlBlockUnion blocks' := by
                  rw [hUnionEq]
                  exact hxBlocks
                exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hxBlocks')))
          have hcastv :
              (inducedOn G (u ∪ (controlBlockUnion blocks' ∪ (s \ u)))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (controlBlockUnion blocks' ∪ (s \ u)))
                (t := s ∪ controlBlockUnion blocks)
                (h := hAmbient)
                (hs := Finset.mem_union.mpr (Or.inl v.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
          have hcastw :
              (inducedOn G (u ∪ (controlBlockUnion blocks' ∪ (s \ u)))).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
                (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (controlBlockUnion blocks' ∪ (s \ u)))
                (t := s ∪ controlBlockUnion blocks)
                (h := hAmbient)
                (hs := Finset.mem_union.mpr (Or.inl w.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
          simpa [hcastv, hcastw] using hdeg ⟨v.1, hu v.2⟩ ⟨w.1, hu w.2⟩)
        hextU
  have hconst :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡ (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hconstRaw v w
  exact ⟨u, hu, hku, hconst⟩

lemma
    exists_large_subset_with_constant_modClass_and_modExternalBlockDegrees_and_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * (q * k) ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ a : Fin q, ∃ blocks' : List (Finset V × ℕ),
        SameControlBlockSupports blocks' blocks ∧
        ControlBlocksSeparated u blocks' ∧
        (∀ v : ↑(u : Set V),
          ⟨(inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
            Nat.mod_lt _ hq⟩ = a) ∧
        HasConstantModExternalBlockDegrees G u q blocks' ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) := by
  classical
  rcases exists_large_subset_with_constant_modExternalBlockDegrees
      (G := G) (s := s) (q := q) (blocks := blocks) (k := q * k) hq hsize hsep with
    ⟨u₁, hu₁, hqu₁, blocks', hsame, hsepU₁, hextU₁⟩
  let f : V → Fin q := fun x =>
    if hx : x ∈ s then
      ⟨(inducedOn G (s ∪ controlBlockUnion blocks')).degree
          ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩ % q, Nat.mod_lt _ hq⟩
    else
      ⟨0, hq⟩
  obtain ⟨a, ha⟩ := exists_large_mod_class_of_mul_le_card (s := u₁) (q := q) (n := k) hq f hqu₁
  let u : Finset V := u₁.filter fun x => f x = a
  have huu₁ : u ⊆ u₁ := Finset.filter_subset _ _
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hku : k ≤ u.card := by
    simpa [u] using ha
  have hUnionEq : controlBlockUnion blocks' = controlBlockUnion blocks :=
    controlBlockUnion_eq_of_sameControlBlockSupports hsame
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hUnionDisj : Disjoint s (controlBlockUnion blocks') := by
    rw [hUnionEq]
    exact disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have hUnionDisjDrop : Disjoint (controlBlockUnion blocks') (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxBlocks hxDrop
    exact (Finset.disjoint_left.mp hUnionDisj.symm) hxBlocks (Finset.mem_sdiff.mp hxDrop).1
  have hrestrict :
      ∀ {bs : List (Finset V × ℕ)},
        HasConstantModExternalBlockDegrees G u₁ q bs →
          HasConstantModExternalBlockDegrees G u q bs := by
    intro bs hbs
    induction bs with
    | nil =>
        trivial
    | cons b bs ih =>
        rcases hbs with ⟨hb, htail⟩
        refine ⟨?_, ih htail⟩
        intro v
        exact hb ⟨v.1, huu₁ v.2⟩
  have hextU : HasConstantModExternalBlockDegrees G u q blocks' := hrestrict hextU₁
  have hclass :
      ∀ v : ↑(u : Set V),
        ⟨(inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
          Nat.mod_lt _ hq⟩ = a := by
    intro v
    have hvEq : f v.1 = a := by
      have hvMem : v.1 ∈ u₁.filter fun x => f x = a := v.2
      exact (Finset.mem_filter.mp hvMem).2
    have hvClass :
        ⟨(inducedOn G (s ∪ controlBlockUnion blocks')).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
          Nat.mod_lt _ hq⟩ = a := by
      simpa [f, hu v.2] using hvEq
    have hcast :
        (inducedOn G (s ∪ controlBlockUnion blocks')).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
      simpa [hUnionEq] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ controlBlockUnion blocks') (t := s ∪ controlBlockUnion blocks)
          (h := by simp [hUnionEq])
          (hs := Finset.mem_union.mpr (Or.inl (hu v.2)))
          (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
    simpa [hcast] using hvClass
  have hconstRaw :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalBlockDegrees
        (G := G) (s := u) (tail := s \ u) (q := q) hsepU hUnionDisjDrop
        (by
          intro v w
          have hvEq : f v.1 = a := by
            have hvMem : v.1 ∈ u₁.filter fun x => f x = a := v.2
            exact (Finset.mem_filter.mp hvMem).2
          have hwEq : f w.1 = a := by
            have hwMem : w.1 ∈ u₁.filter fun x => f x = a := w.2
            exact (Finset.mem_filter.mp hwMem).2
          have hvClass :
              (inducedOn G (s ∪ controlBlockUnion blocks')).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡ a.1 [MOD q] := by
            simpa [Nat.ModEq, f, hu v.2, Nat.mod_eq_of_lt a.2] using congrArg Fin.val hvEq
          have hwClass :
              (inducedOn G (s ∪ controlBlockUnion blocks')).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ ≡ a.1 [MOD q] := by
            simpa [Nat.ModEq, f, hu w.2, Nat.mod_eq_of_lt a.2] using congrArg Fin.val hwEq
          have hAmbient :
              u ∪ (controlBlockUnion blocks' ∪ (s \ u)) = s ∪ controlBlockUnion blocks' := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_union.mp hx with hxU | hxRest
              · exact Finset.mem_union.mpr (Or.inl (hu hxU))
              · rcases Finset.mem_union.mp hxRest with hxBlocks | hxDrop
                · exact Finset.mem_union.mpr (Or.inr hxBlocks)
                · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hxDrop).1)
            · intro hx
              rcases Finset.mem_union.mp hx with hxS | hxBlocks
              · by_cases hxu : x ∈ u
                · exact Finset.mem_union.mpr (Or.inl hxu)
                · exact
                    Finset.mem_union.mpr
                      (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxS, hxu⟩))))
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hxBlocks)))
          have hcastv :
              (inducedOn G (u ∪ (controlBlockUnion blocks' ∪ (s \ u)))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                (inducedOn G (s ∪ controlBlockUnion blocks')).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (controlBlockUnion blocks' ∪ (s \ u)))
                (t := s ∪ controlBlockUnion blocks')
                (h := hAmbient)
                (hs := Finset.mem_union.mpr (Or.inl v.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
          have hcastw :
              (inducedOn G (u ∪ (controlBlockUnion blocks' ∪ (s \ u)))).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
                (inducedOn G (s ∪ controlBlockUnion blocks')).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (controlBlockUnion blocks' ∪ (s \ u)))
                (t := s ∪ controlBlockUnion blocks')
                (h := hAmbient)
                (hs := Finset.mem_union.mpr (Or.inl w.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
          simpa [hcastv, hcastw] using hvClass.trans hwClass.symm)
        hextU
  have hconst :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡ (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hconstRaw v w
  exact ⟨u, hu, hku, a, blocks', hsame, hsepU, hclass, hextU, hconst⟩

lemma exists_large_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * (q * k) ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  rcases
      exists_large_subset_with_constant_modClass_and_modExternalBlockDegrees_and_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
        (G := G) hq hsize hsep with
    ⟨u, hu, hku, _a, _blocks', _hsame, _hsepU, _hclass, _hextU, hconst⟩
  exact ⟨u, hu, hku, hconst⟩

lemma
    exists_subset_with_constant_modClass_and_modExternalBlockDegrees_and_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * (q * k) ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ a : Fin q, ∃ blocks' : List (Finset V × ℕ),
        SameControlBlockSupports blocks' blocks ∧
        ControlBlocksSeparated u blocks' ∧
        (∀ v : ↑(u : Set V),
          ⟨(inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
            Nat.mod_lt _ hq⟩ = a) ∧
        HasConstantModExternalBlockDegrees G u q blocks' ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) := by
  rcases
      exists_large_subset_with_constant_modClass_and_modExternalBlockDegrees_and_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
        (G := G) hq hsize hsep with
    ⟨u₁, hu₁, hku₁, a, blocks', hsame, hsepU₁, hclassU₁, hextU₁, hconstU₁⟩
  rcases exists_subset_card_eq_of_le_card hku₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hextU : HasConstantModExternalBlockDegrees G u q blocks' :=
    hasConstantModExternalBlockDegrees_mono (G := G) huu₁ hextU₁
  have hclassU :
      ∀ v : ↑(u : Set V),
        ⟨(inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
          Nat.mod_lt _ hq⟩ = a := by
    intro v
    simpa [hu] using hclassU₁ ⟨v.1, huu₁ v.2⟩
  have hconstU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    simpa [hu] using hconstU₁ ⟨v.1, huu₁ v.2⟩ ⟨w.1, huu₁ w.2⟩
  exact ⟨u, hu, hcardu, a, blocks', hsame, hsepU, hclassU, hextU, hconstU⟩

lemma exists_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * (q * k) ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  rcases
      exists_subset_with_constant_modClass_and_modExternalBlockDegrees_and_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_eq
        (G := G) hq hsize hsep with
    ⟨u, hu, hcardu, _a, _blocks', _hsame, _hsepU, _hclassU, _hextU, hconstU⟩
  exact ⟨u, hu, hcardu, hconstU⟩

lemma exists_large_mod_pair_of_mul_le_card
    {α : Type*} (s : Finset α) {q n : ℕ} (hq : 0 < q)
    (f g : α → Fin q) (hn : q * q * n ≤ s.card) :
    ∃ a b : Fin q, n ≤ (s.filter fun x => f x = a ∧ g x = b).card := by
  classical
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  obtain ⟨y, hy⟩ :=
    exists_large_fiber_of_mul_le_card (s := s) (β := Fin q × Fin q)
      (f := fun x => (f x, g x))
      (hn := by simpa [Fintype.card_fin, Fintype.card_prod, Nat.mul_assoc] using hn)
  rcases y with ⟨a, b⟩
  refine ⟨a, b, ?_⟩
  simpa using hy

lemma exists_large_subset_with_constant_mod_pair
    {α : Type*} (s : Finset α) {q n : ℕ} (hq : 0 < q)
    (f g : α → Fin q) (hn : q * q * n ≤ s.card) :
    ∃ u : Finset α, u ⊆ s ∧ n ≤ u.card ∧
      ∃ a b : Fin q, ∀ x ∈ u, f x = a ∧ g x = b := by
  classical
  obtain ⟨a, b, hab⟩ := exists_large_mod_pair_of_mul_le_card s hq f g hn
  refine ⟨s.filter fun x => f x = a ∧ g x = b, Finset.filter_subset _ _, hab, a, b, ?_⟩
  intro x hx
  exact Finset.mem_filter.mp hx |>.2

lemma exists_large_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q k : ℕ}
    (hq : 0 < q) (hsize : q * q * k ≤ s.card) (hst : Disjoint s t) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ a b : Fin q,
        (∀ v : ↑(u : Set V),
          ⟨(inducedOn G (s ∪ t)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
            Nat.mod_lt _ hq⟩ = a ∧
          ⟨(G.neighborFinset v ∩ t).card % q, Nat.mod_lt _ hq⟩ = b) ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) := by
  classical
  let f : V → Fin q := fun x =>
    if hx : x ∈ s then
      ⟨(inducedOn G (s ∪ t)).degree
          ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩ % q, Nat.mod_lt _ hq⟩
    else
      ⟨0, hq⟩
  let g : V → Fin q := fun x =>
    ⟨(G.neighborFinset x ∩ t).card % q, Nat.mod_lt _ hq⟩
  rcases exists_large_subset_with_constant_mod_pair (s := s) (q := q) (n := k) hq f g hsize with
    ⟨u, hu, hku, a, b, hpair⟩
  have hut : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  have htu : Disjoint t (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxT hxDrop
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have hconstRaw :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
        (G := G) (s := u) (t := t) (u := s \ u) hut htu
        (by
          intro v w
          have hvEq : f v.1 = a := (hpair v.1 v.2).1
          have hwEq : f w.1 = a := (hpair w.1 w.2).1
          have hvClass :
              (inducedOn G (s ∪ t)).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡ a.1 [MOD q] := by
            simpa [Nat.ModEq, f, hu v.2, Nat.mod_eq_of_lt a.2] using congrArg Fin.val hvEq
          have hwClass :
              (inducedOn G (s ∪ t)).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ ≡ a.1 [MOD q] := by
            simpa [Nat.ModEq, f, hu w.2, Nat.mod_eq_of_lt a.2] using congrArg Fin.val hwEq
          have hUnion : u ∪ (t ∪ (s \ u)) = s ∪ t := by
            calc
              u ∪ (t ∪ (s \ u)) = (u ∪ (s \ u)) ∪ t := by
                simp [Finset.union_left_comm, Finset.union_comm]
              _ = s ∪ t := by
                rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu]
          have hcastv :
              (inducedOn G (u ∪ (t ∪ (s \ u)))).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                (inducedOn G (s ∪ t)).degree
                  ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (t ∪ (s \ u))) (t := s ∪ t)
                (h := hUnion)
                (hs := Finset.mem_union.mpr (Or.inl v.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
          have hcastw :
              (inducedOn G (u ∪ (t ∪ (s \ u)))).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
                (inducedOn G (s ∪ t)).degree
                  ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
            simpa using
              (inducedOn_degree_congr (G := G)
                (s := u ∪ (t ∪ (s \ u))) (t := s ∪ t)
                (h := hUnion)
                (hs := Finset.mem_union.mpr (Or.inl w.2))
                (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
          simpa [hcastv, hcastw] using hvClass.trans hwClass.symm)
        (by
          intro v w
          have hvEq : g v.1 = b := (hpair v.1 v.2).2
          have hwEq : g w.1 = b := (hpair w.1 w.2).2
          have hvClass : (G.neighborFinset v ∩ t).card ≡ b.1 [MOD q] := by
            simpa [Nat.ModEq, g, Nat.mod_eq_of_lt b.2] using congrArg Fin.val hvEq
          have hwClass : (G.neighborFinset w ∩ t).card ≡ b.1 [MOD q] := by
            simpa [Nat.ModEq, g, Nat.mod_eq_of_lt b.2] using congrArg Fin.val hwEq
          exact hvClass.trans hwClass.symm)
  have hconst :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hconstRaw v w
  refine ⟨u, hu, hku, a, b, ?_, hconst⟩
  intro v
  rcases hpair v.1 v.2 with ⟨hvEq, hvExt⟩
  constructor
  · simpa [f, hu v.2] using hvEq
  · simpa [g] using hvExt

lemma exists_large_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q k : ℕ}
    (hq : 0 < q) (hsize : q * q * k ≤ s.card) (hst : Disjoint s t) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  rcases
      exists_large_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound
        (G := G) hq hsize hst with
    ⟨u, hu, hku, _a, _b, _hpair, hconst⟩
  exact ⟨u, hu, hku, hconst⟩

lemma exists_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q k : ℕ}
    (hq : 0 < q) (hsize : q * q * k ≤ s.card) (hst : Disjoint s t) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∃ a b : Fin q,
        (∀ v : ↑(u : Set V),
          ⟨(inducedOn G (s ∪ t)).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
            Nat.mod_lt _ hq⟩ = a ∧
          ⟨(G.neighborFinset v.1 ∩ t).card % q, Nat.mod_lt _ hq⟩ = b) ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) := by
  rcases
      exists_large_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound
        (G := G) hq hsize hst with
    ⟨u₁, hu₁, hku₁, a, b, hpairU₁, hconstU₁⟩
  rcases exists_subset_card_eq_of_le_card hku₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hpairU :
      ∀ v : ↑(u : Set V),
        ⟨(inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ % q,
          Nat.mod_lt _ hq⟩ = a ∧
        ⟨(G.neighborFinset v.1 ∩ t).card % q, Nat.mod_lt _ hq⟩ = b := by
    intro v
    simpa [hu] using hpairU₁ ⟨v.1, huu₁ v.2⟩
  have hconstU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    simpa [hu] using hconstU₁ ⟨v.1, huu₁ v.2⟩ ⟨w.1, huu₁ w.2⟩
  exact ⟨u, hu, hcardu, a, b, hpairU, hconstU⟩

lemma exists_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q k : ℕ}
    (hq : 0 < q) (hsize : q * q * k ≤ s.card) (hst : Disjoint s t) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, u.card = k ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  rcases
      exists_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_eq
        (G := G) hq hsize hst with
    ⟨u, hu, hcardu, _a, _b, _hpairU, hconstU⟩
  exact ⟨u, hu, hcardu, hconstU⟩

/--
Choose a small control set `t` of size `r < q` and delete it from the graph. If the graph still has
at least `q^2 k` remaining vertices, then one can find an exact-cardinality bucket `u` of size `k`
on which:

* the global degrees in `G` are constant modulo `q`,
* the degrees into `t` are actually equal,
* and the degrees in the deleted-host graph `G[univ \ t]` are constant modulo `q`.

This is the cleanest direct finite forcing theorem currently available from the one-control scalar
data alone: the only missing ingredient for a genuine modular bucketing witness is control of the
dropped-part residue.
-/
lemma
    exists_control_and_subset_with_constant_modDegree_and_exact_controlDegree_and_modEq_deletedHostDegree_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {q k r : ℕ}
    (hq : 0 < q) (hrq : r < q) (hsize : q * q * k + r ≤ Fintype.card V) :
    ∃ u t : Finset V, ∃ hu : u ⊆ Finset.univ \ t,
      u.card = k ∧ t.card = r ∧
      ∃ a : Fin q, ∃ e : ℕ,
        (∀ v : ↑(u : Set V), ⟨G.degree v.1 % q, Nat.mod_lt _ hq⟩ = a) ∧
        (∀ v : ↑(u : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G (Finset.univ \ t)).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G (Finset.univ \ t)).degree ⟨w.1, hu w.2⟩ [MOD q]) := by
  classical
  have hr : r ≤ Fintype.card V := by
    omega
  rcases exists_subset_card_eq_of_le_card (s := (Finset.univ : Finset V)) hr with
    ⟨t, htU, htcard⟩
  let s : Finset V := Finset.univ \ t
  have hsCard : s.card = Fintype.card V - r := by
    simpa [s, htcard] using Finset.card_sdiff_of_subset htU
  have hsize' : q * q * k ≤ s.card := by
    rw [hsCard]
    omega
  have hst : Disjoint s t := by
    simpa [s] using (Finset.sdiff_disjoint : Disjoint ((Finset.univ : Finset V) \ t) t)
  rcases
      exists_subset_with_constant_modPair_and_modEq_hostDegree_of_unionDegree_and_externalDegree_card_eq
        (G := G) (s := s) (t := t) (q := q) (k := k) hq hsize' hst with
    ⟨u, hu, hcardu, a, b, hpair, hhost⟩
  have hglobal :
      ∀ v : ↑(u : Set V), ⟨G.degree v.1 % q, Nat.mod_lt _ hq⟩ = a := by
    intro v
    have hUnion : s ∪ t = (Finset.univ : Finset V) := by
      ext x
      simp [s]
    have hdegUnion :
        (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ =
          (inducedOn G (Finset.univ : Finset V)).degree ⟨v.1, by simp⟩ := by
      exact inducedOn_degree_congr (G := G) hUnion
        (Finset.mem_union.mpr (Or.inl (hu v.2))) (by simp)
    have hdegUniv :
        (inducedOn G (Finset.univ : Finset V)).degree ⟨v.1, by simp⟩ = G.degree v.1 := by
      classical
      let f : ↑(((Finset.univ : Finset V) : Set V)) ↪ V :=
        Function.Embedding.subtype (· ∈ (((Finset.univ : Finset V) : Set V)))
      have hmap :
          ((inducedOn G (Finset.univ : Finset V)).neighborFinset ⟨v.1, by simp⟩).map f =
            G.neighborFinset v.1 ∩ (Finset.univ : Finset V) := by
        ext x
        simp [f, inducedOn, and_assoc]
      calc
        (inducedOn G (Finset.univ : Finset V)).degree ⟨v.1, by simp⟩ =
            (((inducedOn G (Finset.univ : Finset V)).neighborFinset ⟨v.1, by simp⟩).map f).card := by
              rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_map]
        _ = (G.neighborFinset v.1 ∩ (Finset.univ : Finset V)).card := by
              rw [hmap]
        _ = G.degree v.1 := by
              rw [Finset.inter_univ, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hdegEq :
        (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ = G.degree v.1 := by
      exact hdegUnion.trans hdegUniv
    simpa [hdegEq] using (hpair v).1
  by_cases huNonempty : u.Nonempty
  · obtain ⟨v0, hv0⟩ := huNonempty
    let e : ℕ := (G.neighborFinset v0 ∩ t).card
    have he_lt : e < q := by
      unfold e
      exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right))
        (by simpa [htcard] using hrq)
    have hext :
        ∀ v : ↑(u : Set V), (G.neighborFinset v.1 ∩ t).card = e := by
      intro v
      have hv_lt : (G.neighborFinset v.1 ∩ t).card < q := by
        exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right))
          (by simpa [htcard] using hrq)
      have hvEq : (G.neighborFinset v.1 ∩ t).card % q = b.1 := by
        simpa using congrArg Fin.val ((hpair v).2)
      have h0Eq : e % q = b.1 := by
        simpa [e, Nat.mod_eq_of_lt he_lt] using congrArg Fin.val ((hpair ⟨v0, hv0⟩).2)
      have hmod : (G.neighborFinset v.1 ∩ t).card ≡ e [MOD q] := by
        rw [Nat.ModEq, hvEq, h0Eq]
      rw [Nat.ModEq, Nat.mod_eq_of_lt hv_lt, Nat.mod_eq_of_lt he_lt] at hmod
      exact hmod
    exact ⟨u, t, hu, hcardu, htcard, a, e, hglobal, hext, hhost⟩
  · have huEmpty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp huNonempty
    subst huEmpty
    refine ⟨∅, t, by simp [s], hcardu, htcard, a, 0, ?_, ?_, ?_⟩
    · intro v
      exact False.elim (by simpa using v.2)
    · intro v
      exact False.elim (by simpa using v.2)
    · intro v w
      exact False.elim (by simpa using v.2)

/--
Concrete cubic-size specialization of the preceding theorem.

On `k^3 + k - 1` vertices one can already freeze the one-control scalar data at modulus `k` on a
bucket of size `k`, using a control set of size `k - 1`.
-/
lemma
    exists_control_and_subset_with_constant_modDegree_and_exact_controlDegree_and_modEq_deletedHostDegree_cubic_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (hsize : k * k * k + (k - 1) ≤ Fintype.card V) :
    ∃ u t : Finset V, ∃ hu : u ⊆ Finset.univ \ t,
      u.card = k ∧ t.card = k - 1 ∧
      ∃ a : Fin k, ∃ e : ℕ,
        (∀ v : ↑(u : Set V), ⟨G.degree v.1 % k, Nat.mod_lt _ hk⟩ = a) ∧
        (∀ v : ↑(u : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G (Finset.univ \ t)).degree ⟨v.1, hu v.2⟩ ≡
            (inducedOn G (Finset.univ \ t)).degree ⟨w.1, hu w.2⟩ [MOD k]) := by
  refine
    exists_control_and_subset_with_constant_modDegree_and_exact_controlDegree_and_modEq_deletedHostDegree_card_eq
      (G := G) (q := k) (k := k) (r := k - 1) hk ?_ hsize
  exact Nat.sub_lt hk (by decide : 0 < 1)

/--
The one-control exact-cardinality theorem already yields a composable fixed-modulus modular host
witness with one control block.
-/
lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_large_card
    (G : SimpleGraph V) {q k : ℕ}
    (hq : 1 < q) (hsize : q * q * k + (q - 1) ≤ Fintype.card V) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q 1 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq0 : 0 < q := lt_trans (by decide : 0 < 1) hq
  have hqPred : q - 1 < q := Nat.sub_lt hq0 (by decide : 0 < 1)
  rcases
      exists_control_and_subset_with_constant_modDegree_and_exact_controlDegree_and_modEq_deletedHostDegree_card_eq
        (G := G) (q := q) (k := k) (r := q - 1) hq0 hqPred hsize with
    ⟨u, t, hu, hcardu, htcard, _a, e, _hglobal, hext, hhost⟩
  refine ⟨u, Finset.univ \ t, ?_, hu, [(t, e)], ?_⟩
  · simpa [hcardu]
  · refine ⟨by simp, ?_⟩
    refine ⟨?_, ?_⟩
    · have htpos : 0 < t.card := by
        rw [htcard]
        exact Nat.sub_pos_of_lt hq
      unfold NonemptyControlBlockUnion
      simpa [controlBlockUnion] using htpos
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_, trivial⟩
        · simpa using (Finset.sdiff_disjoint : Disjoint ((Finset.univ : Finset V) \ t) t)
        · simp [controlBlockUnion]
      · refine ⟨hhost, ?_⟩
        refine ⟨?_, trivial⟩
        intro v
        simpa [hext v] using (Nat.ModEq.refl e : e ≡ e [MOD q])

/--
Inside a fixed-modulus witness of size `q * m`, one can delete any `q - 1` control vertices and
then pigeonhole the exact control degree on a bucket of size `m`. Subtracting the exact control
contribution from the ambient modular degree on the original witness leaves a one-control
fixed-modulus host witness of size `m`.
-/
lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard
    (G : SimpleGraph V) {q m : ℕ}
    (hq : 1 < q) (hm : 0 < m)
    (hfixed : HasFixedModulusWitnessOfCard G (q * m) q) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G m q 1 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hfixed with ⟨s₀, hqm, hmod₀⟩
  have hq0 : 0 < q := lt_trans (by decide : 0 < 1) hq
  have hqPred : q - 1 < q := Nat.sub_lt hq0 (by decide : 0 < 1)
  have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have htCardLe : q - 1 ≤ s₀.card := by
    have hqLe : q ≤ q * m := by
      simpa using Nat.mul_le_mul_left q (Nat.succ_le_of_lt hm)
    exact le_trans (Nat.le_of_lt hqPred) (le_trans hqLe hqm)
  rcases exists_subset_card_eq_of_le_card (s := s₀) htCardLe with ⟨t, htS₀, htcard⟩
  let s : Finset V := s₀ \ t
  have hsCard : s.card = s₀.card - (q - 1) := by
    simpa [s, htcard] using Finset.card_sdiff_of_subset htS₀
  have hsize₀ :
      q * (m - 1) + (q - 1) < s₀.card := by
    have hlt :
        q * (m - 1) + (q - 1) < q * (m - 1) + q := by
      exact Nat.add_lt_add_left hqPred (q * (m - 1))
    have hle : q * (m - 1) + q ≤ s₀.card := by
      calc
        q * (m - 1) + q = q * ((m - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = q * m := by rw [hmEq]
        _ ≤ s₀.card := hqm
    exact lt_of_lt_of_le hlt hle
  have hsize :
      (t.card + 1) * (m - 1) < s.card := by
    have htplus : t.card + 1 = q := by
      rw [htcard]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hq0)
    have hsize' : q * (m - 1) < s₀.card - (q - 1) := by
      rw [Nat.lt_sub_iff_add_lt]
      exact hsize₀
    simpa [htplus, hsCard]
      using hsize'
  have hst : Disjoint s t := by
    simpa [s] using (Finset.sdiff_disjoint : Disjoint (s₀ \ t) t)
  rcases exists_large_subset_with_constant_externalDegree_of_mul_pred_lt_card
      (G := G) s t (k := m) hsize with
    ⟨u, hu, hmu, e, hext⟩
  have hut : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  have htu : Disjoint t (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxT hxDrop
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huS₀ : ∀ {x : V}, x ∈ u → x ∈ s₀ := by
    intro x hxU
    exact (Finset.mem_sdiff.mp (hu hxU)).1
  have hdegUnion :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (t ∪ (s \ u)))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (t ∪ (s \ u)))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩
            [MOD q] := by
    intro v w
    have hAmbient : u ∪ (t ∪ (s \ u)) = s₀ := by
      calc
        u ∪ (t ∪ (s \ u)) = (u ∪ (s \ u)) ∪ t := by
          simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
        _ = s ∪ t := by
          rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu]
        _ = s₀ := by
          simpa [s] using (Finset.sdiff_union_of_subset htS₀ : (s₀ \ t) ∪ t = s₀)
    have hcastv :
        (inducedOn G (u ∪ (t ∪ (s \ u)))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s₀).degree ⟨v.1, huS₀ v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (t ∪ (s \ u))) (t := s₀)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := huS₀ v.2))
    have hcastw :
        (inducedOn G (u ∪ (t ∪ (s \ u)))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s₀).degree ⟨w.1, huS₀ w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (t ∪ (s \ u))) (t := s₀)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := huS₀ w.2))
    simpa [hcastv, hcastw] using hmod₀ ⟨v.1, huS₀ v.2⟩ ⟨w.1, huS₀ w.2⟩
  have hextPair :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
    intro v w
    simpa [hext v.1 v.2, hext w.1 w.2] using (Nat.ModEq.refl e : e ≡ e [MOD q])
  have hhostRaw :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
        (G := G) (s := u) (t := t) (u := s \ u) hut htu hdegUnion hextPair
  have hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (s \ u))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ (s \ u))).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (s \ u)) (t := s)
          (h := by rw [Finset.union_comm u, Finset.sdiff_union_of_subset hu])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hhostRaw v w
  refine ⟨u, s, hmu, hu, [(t, e)], by simp, ?_, ?_, hhost, ?_⟩
  · have htpos : 0 < t.card := by
      rw [htcard]
      exact Nat.sub_pos_of_lt hq
    unfold NonemptyControlBlockUnion
    simpa [controlBlockUnion] using htpos
  · refine ⟨hst, ?_, trivial⟩
    simp [controlBlockUnion]
  · refine ⟨?_, trivial⟩
    intro v
    simpa [hext v.1 v.2] using (Nat.ModEq.refl e : e ≡ e [MOD q])

lemma hasFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard
    (G : SimpleGraph V) {q m : ℕ}
    (hq : 1 < q) (hm : 0 < m)
    (hfixed : HasFixedModulusWitnessOfCard G (q * m) q) :
    HasFixedModulusControlBlockModularHostWitnessOfCard G m q := by
  exact
    hasFixedModulusControlBlockModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
      G
      (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard
        (G := G) hq hm hfixed)

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_step
    (G : SimpleGraph V) {q k r : ℕ}
    (hq : 1 < q) (hk : 0 < k)
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * k) q r) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q (r + 1) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hhost with ⟨u, s, hqk, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  have hq0 : 0 < q := lt_trans (by decide : 0 < 1) hq
  have hqPred : q - 1 < q := Nat.sub_lt hq0 (by decide : 0 < 1)
  have hkEq : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  have htCardLe : q - 1 ≤ u.card := by
    have hqLe : q ≤ q * k := by
      simpa using Nat.mul_le_mul_left q (Nat.succ_le_of_lt hk)
    exact le_trans (Nat.le_of_lt hqPred) (le_trans hqLe hqk)
  rcases exists_subset_card_eq_of_le_card (s := u) htCardLe with ⟨t, htU, htcard⟩
  let s' : Finset V := s \ t
  have htS : t ⊆ s := by
    intro x hx
    exact hu (htU hx)
  have hs'S : s' ⊆ s := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  have hsize :
      (t.card + 1) * (k - 1) < (u \ t).card := by
    have htplus : t.card + 1 = q := by
      rw [htcard]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hq0)
    have hcardUt : (u \ t).card = u.card - (q - 1) := by
      simpa [htcard] using Finset.card_sdiff_of_subset htU
    have hsize' : q * (k - 1) < u.card - (q - 1) := by
      rw [Nat.lt_sub_iff_add_lt]
      calc
        q * (k - 1) + (q - 1) < q * (k - 1) + q := by
          exact Nat.add_lt_add_left hqPred (q * (k - 1))
        _ = q * (k - 1) + q * 1 := by rw [Nat.mul_one]
        _ = q * ((k - 1) + 1) := by rw [← Nat.mul_add]
        _ = q * k := by rw [hkEq]
        _ ≤ u.card := hqk
    simpa [htplus, hcardUt] using hsize'
  rcases exists_large_subset_with_constant_externalDegree_of_mul_pred_lt_card
      (G := G) (s := u \ t) (t := t) (k := k) hsize with
    ⟨w, hw, hwk, e, hctrl⟩
  have hwU : w ⊆ u := by
    intro x hx
    exact (Finset.mem_sdiff.mp (hw hx)).1
  have hwS : w ⊆ s := by
    intro x hx
    exact hu (hwU hx)
  have hwS' : w ⊆ s' := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hwS hx, (Finset.mem_sdiff.mp (hw hx)).2⟩
  have hwt : Disjoint w t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxT
    exact (Finset.mem_sdiff.mp (hw hxW)).2 hxT
  have hs't : Disjoint s' t := by
    simpa [s'] using (Finset.sdiff_disjoint : Disjoint (s \ t) t)
  have htDrop : Disjoint t (s' \ w) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxT hxDrop
    exact (Finset.disjoint_left.mp hs't) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
    disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have htBlocks : Disjoint t (controlBlockUnion blocks) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxT hxBlock
    exact (Finset.disjoint_left.mp hsBlocks) (htS hxT) hxBlock
  have hsepS' : ControlBlocksSeparated s' blocks := controlBlocksSeparated_mono hs'S hsep
  have hsepNew : ControlBlocksSeparated s' ((t, e) :: blocks) := by
    exact ⟨hs't, htBlocks, hsepS'⟩
  have htpos : 0 < t.card := by
    rw [htcard]
    exact Nat.sub_pos_of_lt hq
  have hnonemptyNew : NonemptyControlBlockUnion ((t, e) :: blocks) := by
    unfold NonemptyControlBlockUnion
    rw [controlBlockUnion]
    exact lt_of_lt_of_le htpos (Finset.card_le_card (by
      intro x hx
      exact Finset.mem_union.mpr (Or.inl hx)))
  have hdegExtended :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (w ∪ (t ∪ (s' \ w)))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (w ∪ (t ∪ (s' \ w)))).degree ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩
            [MOD q] := by
    intro v w'
    have hAmbient : w ∪ (t ∪ (s' \ w)) = s := by
      calc
        w ∪ (t ∪ (s' \ w)) = (w ∪ (s' \ w)) ∪ t := by
          simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
        _ = s' ∪ t := by
          rw [Finset.union_comm w, Finset.sdiff_union_of_subset hwS']
        _ = s := by
          simpa [s'] using (Finset.sdiff_union_of_subset htS : (s \ t) ∪ t = s)
    have hcastv :
        (inducedOn G (w ∪ (t ∪ (s' \ w)))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hwS v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (t ∪ (s' \ w))) (t := s)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hwS v.2))
    have hcastw :
        (inducedOn G (w ∪ (t ∪ (s' \ w)))).degree ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ =
          (inducedOn G s).degree ⟨w'.1, hwS w'.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (t ∪ (s' \ w))) (t := s)
          (h := hAmbient)
          (hs := Finset.mem_union.mpr (Or.inl w'.2))
          (ht := hwS w'.2))
    simpa [hcastv, hcastw] using hdeg ⟨v.1, hwU v.2⟩ ⟨w'.1, hwU w'.2⟩
  have hextPair :
      ∀ v w' : ↑(w : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w' ∩ t).card [MOD q] := by
    intro v w'
    simpa [hctrl v.1 v.2, hctrl w'.1 w'.2] using (Nat.ModEq.refl e : e ≡ e [MOD q])
  have hdegNewRaw :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (w ∪ (s' \ w))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (w ∪ (s' \ w))).degree ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
        (G := G) (s := w) (t := t) (u := s' \ w) hwt htDrop hdegExtended hextPair
  have hdegNew :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s').degree ⟨v.1, hwS' v.2⟩ ≡
          (inducedOn G s').degree ⟨w'.1, hwS' w'.2⟩ [MOD q] := by
    intro v w'
    have hcastv :
        (inducedOn G (w ∪ (s' \ w))).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s').degree ⟨v.1, hwS' v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (s' \ w)) (t := s')
          (h := by rw [Finset.union_comm w, Finset.sdiff_union_of_subset hwS'])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hwS' v.2))
    have hcastw :
        (inducedOn G (w ∪ (s' \ w))).degree ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ =
          (inducedOn G s').degree ⟨w'.1, hwS' w'.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (s' \ w)) (t := s')
          (h := by rw [Finset.union_comm w, Finset.sdiff_union_of_subset hwS'])
          (hs := Finset.mem_union.mpr (Or.inl w'.2))
          (ht := hwS' w'.2))
    simpa [hcastv, hcastw] using hdegNewRaw v w'
  have hextNew : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) := by
    refine ⟨?_, hasConstantModExternalBlockDegrees_mono (G := G) hwU hext⟩
    intro v
    simpa [hctrl v.1 v.2] using (Nat.ModEq.refl e : e ≡ e [MOD q])
  refine ⟨w, s', hwk, hwS', (t, e) :: blocks, ?_, hnonemptyNew, hsepNew, hdegNew, hextNew⟩
  simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ hlen

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_iterate
    (G : SimpleGraph V) {q k r D : ℕ}
    (hq : 1 < q) (hk : 0 < k)
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q ^ D * k) q r) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q (r + D) := by
  induction D generalizing r with
  | zero =>
      simpa using hhost
  | succ D ih =>
      have hk' : 0 < q ^ D * k := by
        exact Nat.mul_pos (Nat.pow_pos (lt_trans (by decide : 0 < 1) hq)) hk
      have hstepInput :
          HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * (q ^ D * k)) q r := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhost
      have hstep :
          HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q ^ D * k) q (r + 1) := by
        exact
          hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_step
            (G := G) hq hk' hstepInput
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (r := r + 1) hstep

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard_pow
    (G : SimpleGraph V) {q k D : ℕ}
    (hq : 1 < q) (hk : 0 < k)
    (hfixed : HasFixedModulusWitnessOfCard G (q ^ (D + 1) * k) q) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q (D + 1) := by
  let m : ℕ := q ^ D * k
  have hm : 0 < m := by
    exact Nat.mul_pos (Nat.pow_pos (lt_trans (by decide : 0 < 1) hq)) hk
  have hhost :
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G m q 1 := by
    have hfixed' : HasFixedModulusWitnessOfCard G (q * m) q := by
      simpa [m, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfixed
    exact
      hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard
        (G := G) hq hm hfixed'
  simpa [m, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_iterate
      (G := G) (q := q) (k := k) (r := 1) (D := D) hq hk hhost

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_two_of_pos
    {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ((n - 1) / 4) 2 1 := by
  classical
  refine
    hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_large_card
      (G := G) (q := 2) (k := (n - 1) / 4) (by decide : 1 < 2) ?_
  have hfour : 4 * ((n - 1) / 4) ≤ n - 1 := Nat.mul_div_le (n - 1) 4
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, hpred] using
    Nat.add_le_add_right hfour 1

lemma hasExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_large_subset_with_constant_externalBlockDegrees
      (G := G) (s := s) (blocks := blocks) (k := n) hsize hsep with
    ⟨u₁, hu₁, hnu₁, blocks', hsame, hsepU₁, hextU₁⟩
  rcases exists_subset_card_eq_of_le_card hnu₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hextU : HasConstantExternalBlockDegrees G u blocks' :=
    hasConstantExternalBlockDegrees_mono (G := G) huu₁ hextU₁
  have hnonempty' : NonemptyControlBlockUnion blocks' := by
    unfold NonemptyControlBlockUnion at hnonempty ⊢
    rw [controlBlockUnion_eq_of_sameControlBlockSupports hsame]
    exact hnonempty
  exact
    hasExactControlBlockWitnessOfCard_of_hasRegularInducedSubgraphOfCard_inducedOn_and_externalBlockDegrees
      (G := G) (hrec u hu hcardu) hnonempty' hsepU hextU

lemma hasControlBlockCascadeWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasControlBlockCascadeWitnessOfCard G k := by
  exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
      (G := G) hsize hnonempty hsep hrec)

lemma hasControlBlockBucketingWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasControlBlockBucketingWitnessOfCard G k := by
  exact hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
      (G := G) hsize hnonempty hsep hrec)

lemma hasRegularInducedSubgraphOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
      (G := G) hsize hnonempty hsep hrec)

lemma hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_large_subset_with_constant_externalBlockDegrees
      (G := G) (s := s) (blocks := blocks) (k := n) hsize hsep with
    ⟨u₁, hu₁, hnu₁, blocks', hsame, hsepU₁, hextU₁⟩
  rcases exists_subset_card_eq_of_le_card hnu₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hextU : HasConstantExternalBlockDegrees G u blocks' :=
    hasConstantExternalBlockDegrees_mono (G := G) huu₁ hextU₁
  have hnonempty' : NonemptyControlBlockUnion blocks' := by
    unfold NonemptyControlBlockUnion at hnonempty ⊢
    rw [controlBlockUnion_eq_of_sameControlBlockSupports hsame]
    exact hnonempty
  have hlen' : blocks'.length ≤ r := by
    rw [length_eq_of_sameControlBlockSupports hsame]
    exact hlen
  exact
    hasBoundedExactControlBlockWitnessOfCard_of_hasRegularInducedSubgraphOfCard_inducedOn_and_externalBlockDegrees
      (G := G) (hrec u hu hcardu) hlen' hnonempty' hsepU hextU

lemma hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_strict
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * (n - 1) < s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_large_subset_with_constant_externalBlockDegrees_of_mul_pred_lt_card
      (G := G) (s := s) (blocks := blocks) (k := n) hsize hsep with
    ⟨u₁, hu₁, hnu₁, blocks', hsame, hsepU₁, hextU₁⟩
  rcases exists_subset_card_eq_of_le_card hnu₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hsepU : ControlBlocksSeparated u blocks' := controlBlocksSeparated_mono huu₁ hsepU₁
  have hextU : HasConstantExternalBlockDegrees G u blocks' :=
    hasConstantExternalBlockDegrees_mono (G := G) huu₁ hextU₁
  have hnonempty' : NonemptyControlBlockUnion blocks' := by
    unfold NonemptyControlBlockUnion at hnonempty ⊢
    rw [controlBlockUnion_eq_of_sameControlBlockSupports hsame]
    exact hnonempty
  have hlen' : blocks'.length ≤ r := by
    rw [length_eq_of_sameControlBlockSupports hsame]
    exact hlen
  exact
    hasBoundedExactControlBlockWitnessOfCard_of_hasRegularInducedSubgraphOfCard_inducedOn_and_externalBlockDegrees
      (G := G) (hrec u hu hcardu) hlen' hnonempty' hsepU hextU

lemma hasBoundedControlBlockCascadeWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
      (G := G) hsize hlen hnonempty hsep hrec)

lemma hasBoundedControlBlockCascadeWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_strict
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * (n - 1) < s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedControlBlockCascadeWitnessOfCard G k r := by
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_strict
      (G := G) hsize hlen hnonempty hsep hrec)

lemma hasBoundedControlBlockBucketingWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_succ
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * n ≤ s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedControlBlockBucketingWitnessOfCard G k (r + 1) := by
  exact hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard_succ
    G
    (hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive
      (G := G) hsize hlen hnonempty hsep hrec)

lemma
    hasBoundedControlBlockBucketingWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_strict_succ
    (G : SimpleGraph V) {s : Finset V} {blocks : List (Finset V × ℕ)} {n k r : ℕ}
    (hsize : controlBlockBucketCost blocks * (n - 1) < s.card)
    (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedControlBlockBucketingWitnessOfCard G k (r + 1) := by
  exact hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard_succ
    G
    (hasBoundedExactControlBlockWitnessOfCard_of_large_constant_externalBlockDegrees_and_recursive_strict
      (G := G) hsize hlen hnonempty hsep hrec)

lemma hasBoundedSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r : ℕ}
    (hsize : (t.card + 1) * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_large_subset_with_constant_externalDegree
      (G := G) s t (k := n) hsize with
    ⟨u₁, hu₁, hnu₁, e, hext₁⟩
  rcases exists_subset_card_eq_of_le_card hnu₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hext : ∀ x ∈ u, (G.neighborFinset x ∩ t).card = e := by
    intro x hx
    exact hext₁ x (huu₁ hx)
  have hut : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  rcases hrec u hu hcardu with ⟨w, hkw, d, hwd⟩
  let emb : inducedOn G u ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (u : Set V))) G
  let w' : Finset V := w.map (Function.Embedding.subtype (· ∈ (u : Set V)))
  have hwu : w' ⊆ u := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hkw' : k ≤ w'.card := by
    simpa [w'] using hkw
  have hwd' : InducesRegularOfDegree G w' d := by
    simpa [w', emb] using (inducesRegularOfDegree_of_embedding emb hwd)
  rw [InducesRegularOfDegree] at hwd'
  have hwt : Disjoint w' t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxT
    exact (Finset.disjoint_left.mp hut) (hwu hxW) hxT
  have hext' : ∀ v : ↑(w' : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext v.1 (hwu v.2)
  refine ⟨w', t, hkw', ht, htr, hwt, d + e, e, ?_, hext'⟩
  intro v
  calc
    (inducedOn G (w' ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G w').degree v + (G.neighborFinset v ∩ t).card := by
          exact degree_union_eq_degree_add_external (G := G) (s := w') (t := t) hwt v
    _ = d + e := by simp [hwd' v, hext' v]

lemma hasBoundedSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive_strict
    (G : SimpleGraph V) {s t : Finset V} {n k r : ℕ}
    (hsize : (t.card + 1) * (n - 1) < s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_large_subset_with_constant_externalDegree_of_mul_pred_lt_card
      (G := G) s t (k := n) hsize with
    ⟨u₁, hu₁, hnu₁, e, hext₁⟩
  rcases exists_subset_card_eq_of_le_card hnu₁ with ⟨u, huu₁, hcardu⟩
  have hu : u ⊆ s := fun x hx => hu₁ (huu₁ hx)
  have hext : ∀ x ∈ u, (G.neighborFinset x ∩ t).card = e := by
    intro x hx
    exact hext₁ x (huu₁ hx)
  have hut : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  rcases hrec u hu hcardu with ⟨w, hkw, d, hwd⟩
  let emb : inducedOn G u ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (u : Set V))) G
  let w' : Finset V := w.map (Function.Embedding.subtype (· ∈ (u : Set V)))
  have hwu : w' ⊆ u := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hkw' : k ≤ w'.card := by
    simpa [w'] using hkw
  have hwd' : InducesRegularOfDegree G w' d := by
    simpa [w', emb] using (inducesRegularOfDegree_of_embedding emb hwd)
  rw [InducesRegularOfDegree] at hwd'
  have hwt : Disjoint w' t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxT
    exact (Finset.disjoint_left.mp hut) (hwu hxW) hxT
  have hext' : ∀ v : ↑(w' : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext v.1 (hwu v.2)
  refine ⟨w', t, hkw', ht, htr, hwt, d + e, e, ?_, hext'⟩
  intro v
  calc
    (inducedOn G (w' ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G w').degree v + (G.neighborFinset v ∩ t).card := by
          exact degree_union_eq_degree_add_external (G := G) (s := w') (t := t) hwt v
    _ = d + e := by simp [hwd' v, hext' v]

lemma hasSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r : ℕ}
    (hsize : (t.card + 1) * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasSingleControlExactWitnessOfCard G k := by
  rcases
      hasBoundedSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive
        (G := G) hsize ht htr hst hrec with
    ⟨u, t', hku, ht', _htr, hut', D, e, hdeg, hext⟩
  exact ⟨u, t', hku, ht', hut', D, e, hdeg, hext⟩

lemma hasRegularInducedSubgraphOfCard_of_large_constant_externalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r : ℕ}
    (hsize : (t.card + 1) * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive
        (G := G) hsize ht htr hst hrec)

lemma
    hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
    (G : SimpleGraph V)
    {s t : Finset V} {n k r q : ℕ}
    (hnq : n ≤ q) (hq : 0 < q) (hsize : q * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases exists_subset_with_constant_modExternalDegree_card_eq
      (G := G) s t (q := q) (k := n) hq hsize with
    ⟨u, hu, hcardu, e, hext⟩
  have huq : u.card ≤ q := by
    simpa [hcardu] using hnq
  have hut : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  rcases hrec u hu hcardu with ⟨w, hkw, d, hwd⟩
  let emb : inducedOn G u ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (u : Set V))) G
  let w' : Finset V := w.map (Function.Embedding.subtype (· ∈ (u : Set V)))
  have hwu : w' ⊆ u := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hkw' : k ≤ w'.card := by
    simpa [w'] using hkw
  have hwq : w'.card ≤ q := by
    exact le_trans (Finset.card_le_card hwu) huq
  have hwd' : InducesRegularOfDegree G w' d := by
    simpa [w', emb] using (inducesRegularOfDegree_of_embedding emb hwd)
  rw [InducesRegularOfDegree] at hwd'
  have hwt : Disjoint w' t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxT
    exact (Finset.disjoint_left.mp hut) (hwu hxW) hxT
  have hext' : ∀ v : ↑(w' : Set V), (G.neighborFinset v ∩ t).card ≡ e [MOD q] := by
    intro v
    exact hext v.1 (hwu v.2)
  have hdeg' :
      ∀ v w : ↑(w' : Set V),
        (inducedOn G (w' ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (w' ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hv := degree_union_eq_degree_add_external (G := G) (s := w') (t := t) hwt v
    have hw := degree_union_eq_degree_add_external (G := G) (s := w') (t := t) hwt w
    have hmain :
        (inducedOn G w').degree v + (G.neighborFinset v ∩ t).card ≡
          (inducedOn G w').degree w + (G.neighborFinset w ∩ t).card [MOD q] := by
      simpa [hwd' v, hwd' w] using
        (Nat.ModEq.add (Nat.ModEq.refl d) ((hext' v).trans (hext' w).symm))
    simpa [hv, hw] using
      hmain
  have hextPair :
      ∀ v w : ↑(w' : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
    intro v w
    exact (hext' v).trans (hext' w).symm
  exact ⟨w', t, hkw', ht, htr, hwt, q, hwq, hdeg', hextPair⟩

lemma
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r q : ℕ}
    (hnq : n ≤ q) (hq : 0 < q) (hsize : q * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
      (hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
        (G := G) hnq hq hsize ht htr hst hrec)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_lt_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r q : ℕ}
    (hkr : r < k) (hnq : n ≤ q) (hq : 0 < q) (hsize : q * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
      G hkr
      (hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
        (G := G) hnq hq hsize ht htr hst hrec)

lemma
    hasSingleControlExactWitnessOfCard_of_lt_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
    (G : SimpleGraph V) {s t : Finset V} {n k r q : ℕ}
    (hkr : r < k) (hnq : n ≤ q) (hq : 0 < q) (hsize : q * n ≤ s.card)
    (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hrec :
      ∀ u : Finset V, u ⊆ s → u.card = n →
        HasRegularInducedSubgraphOfCard (inducedOn G u) k) :
    HasSingleControlExactWitnessOfCard G k := by
  exact
    hasSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
      G hkr
      (hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_large_constant_modExternalDegree_and_recursive
        (G := G) hnq hq hsize ht htr hst hrec)

theorem hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasModularWitnessOfCard G k ↔ HasRegularInducedSubgraphOfCard G k := by
  constructor
  · exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
  · exact hasModularWitnessOfCard_of_hasRegularInducedSubgraphOfCard G

theorem hasControlBlockWitnessOfCard_iff_hasRegularInducedSubgraphOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasControlBlockWitnessOfCard G k ↔ HasRegularInducedSubgraphOfCard G k := by
  rw [hasControlBlockWitnessOfCard_iff_hasModularWitnessOfCard,
    hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard]

theorem hasLowDegreeModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasLowDegreeModularWitnessOfCard G k ↔ HasRegularInducedSubgraphOfCard G k := by
  constructor
  · exact hasRegularInducedSubgraphOfCard_of_hasLowDegreeModularWitnessOfCard G
  · exact hasLowDegreeModularWitnessOfCard_of_hasRegularInducedSubgraphOfCard G

end FiniteGraph

end RegularInducedSubgraph
