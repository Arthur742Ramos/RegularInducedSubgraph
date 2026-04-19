import RegularInducedSubgraph.Threshold

namespace RegularInducedSubgraph

section FiniteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
All degrees in the induced graph on `s` are congruent modulo `q`.

This packages the modular route so later statements do not need explicit decidability assumptions in
their signatures.
-/
def InducesModEqDegree (G : SimpleGraph V) (s : Finset V) (q : ℕ) : Prop := by
  classical
  exact ∀ v w : ↑(s : Set V), (inducedOn G s).degree v ≡ (inducedOn G s).degree w [MOD q]

/--
All induced degrees on `s` are strictly smaller than the modulus `q`.

This packages the stronger modular-collapse hypothesis without exposing extra decidability instances
in theorem signatures.
-/
def InducesDegreeLtModulus (G : SimpleGraph V) (s : Finset V) (q : ℕ) : Prop := by
  classical
  exact ∀ v : ↑(s : Set V), (inducedOn G s).degree v < q

/--
All induced degrees on `s` lie in the half-open interval `[d, d + q)`.

This is a more flexible exact-collapse hypothesis than `InducesDegreeLtModulus`: congruent degrees
modulo `q` already force exact equality as soon as they all lie in any interval of width `< q`.
-/
def InducesDegreeInterval (G : SimpleGraph V) (s : Finset V) (d q : ℕ) : Prop := by
  classical
  exact ∀ v : ↑(s : Set V),
    d ≤ (inducedOn G s).degree v ∧ (inducedOn G s).degree v < d + q

/--
A modular witness of size at least `k`: an induced subgraph on at least `k` vertices whose degrees
are all congruent modulo some modulus at least its cardinality.
-/
def HasModularWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ q : ℕ, s.card ≤ q ∧ InducesModEqDegree G s q

/--
A sharper modular witness of size at least `k`: an induced subgraph on at least `k` vertices whose
degrees are congruent modulo some modulus already larger than every induced degree.
-/
def HasLowDegreeModularWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ q : ℕ,
    InducesDegreeLtModulus G s q ∧ InducesModEqDegree G s q

private lemma degree_inducedOn_eq_card_neighborFinset_inter_modular
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : ↑(s : Set V)) :
    (inducedOn G s).degree v = (G.neighborFinset v ∩ s).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G s).neighborFinset v).map (Function.Embedding.subtype (· ∈ (s : Set V))) =
        G.neighborFinset v ∩ s := by
    ext x
    simp [inducedOn, and_assoc]
  calc
    ((inducedOn G s).neighborFinset v).card =
        (((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ (s : Set V)))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset v ∩ s).card := by rw [hmap]

private lemma card_neighborFinset_inter_union
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hst : Disjoint s t) (v : V) :
    (G.neighborFinset v ∩ (s ∪ t)).card =
      (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card := by
  have hdisj :
      Disjoint (G.neighborFinset v ∩ s) (G.neighborFinset v ∩ t) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxS hxT
    exact (Finset.disjoint_left.mp hst
      (Finset.mem_inter.mp hxS).2 (Finset.mem_inter.mp hxT).2)
  have hunion :
      G.neighborFinset v ∩ (s ∪ t) =
        (G.neighborFinset v ∩ s) ∪ (G.neighborFinset v ∩ t) := by
    ext x
    simp [and_left_comm, and_assoc, and_or_left]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma degree_union_eq_degree_add_external
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hst : Disjoint s t)
    (v : ↑(s : Set V)) :
    (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
      (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
  calc
    (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
      = (G.neighborFinset v ∩ (s ∪ t)).card := by
          exact degree_inducedOn_eq_card_neighborFinset_inter_modular
            (G := G) (s := s ∪ t) ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
    _ = (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card := by
          exact card_neighborFinset_inter_union (G := G) hst v
    _ = (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
          rw [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s) (v := v)]

lemma inducedOn_degree_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (h : s = t)
    {v : V} (hs : v ∈ s) (ht : v ∈ t) :
    (inducedOn G s).degree ⟨v, hs⟩ = (inducedOn G t).degree ⟨v, ht⟩ := by
  subst h
  cases Subsingleton.elim hs ht
  rfl

def SameControlBlockSupports : List (Finset V × ℕ) → List (Finset V × ℕ) → Prop
  | [], [] => True
  | b :: bs, b' :: bs' => b.1 = b'.1 ∧ SameControlBlockSupports bs bs'
  | _, _ => False

lemma controlBlockUnion_eq_of_sameControlBlockSupports :
    ∀ {blocks blocks' : List (Finset V × ℕ)},
      SameControlBlockSupports blocks blocks' →
        controlBlockUnion blocks = controlBlockUnion blocks' := by
  intro blocks blocks' hsame
  induction blocks generalizing blocks' with
  | nil =>
      cases blocks' with
      | nil => rfl
      | cons b bs => cases hsame
  | cons b bs ih =>
      cases blocks' with
      | nil => cases hsame
      | cons b' bs' =>
          rcases hsame with ⟨hb, htail⟩
          simp [controlBlockUnion, hb, ih htail]

lemma length_eq_of_sameControlBlockSupports :
    ∀ {blocks blocks' : List (Finset V × ℕ)},
      SameControlBlockSupports blocks blocks' →
        blocks.length = blocks'.length := by
  intro blocks blocks' hsame
  induction blocks generalizing blocks' with
  | nil =>
      cases blocks' with
      | nil => rfl
      | cons b bs => cases hsame
  | cons b bs ih =>
      cases blocks' with
      | nil => cases hsame
      | cons b' bs' =>
          rcases hsame with ⟨_hb, htail⟩
          simp [ih htail]

lemma controlBlocksSeparated_mono {s t : Finset V} (hts : t ⊆ s) :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks → ControlBlocksSeparated t blocks := by
  intro blocks hsep
  induction blocks with
  | nil =>
      trivial
  | cons b bs ih =>
      rcases hsep with ⟨hst, htail, hsepTail⟩
      refine ⟨?_, htail, ih hsepTail⟩
      refine Finset.disjoint_left.mpr ?_
      intro x hxT hxB
      exact (Finset.disjoint_left.mp hst) (hts hxT) hxB

lemma exists_subset_card_eq_of_le_card {α : Type*} {s : Finset α} {k : ℕ}
    (hk : k ≤ s.card) : ∃ t : Finset α, t ⊆ s ∧ t.card = k := by
  rcases Finset.powersetCard_nonempty.2 hk with ⟨t, ht⟩
  exact ⟨t, (Finset.mem_powersetCard.mp ht).1, (Finset.mem_powersetCard.mp ht).2⟩

lemma disjoint_controlBlockUnion_of_controlBlocksSeparated {s : Finset V} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks → Disjoint s (controlBlockUnion blocks) := by
  intro blocks hsep
  induction blocks with
  | nil =>
      simp [controlBlockUnion]
  | cons b bs ih =>
      rcases hsep with ⟨hst, _htail, hsepTail⟩
      rw [controlBlockUnion, Finset.disjoint_union_right]
      exact ⟨hst, ih hsepTail⟩

lemma inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hst : Disjoint s t) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    InducesModEqDegree G s q := by
  classical
  rw [InducesModEqDegree]
  intro v w
  have hsum :
      (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card ≡
        (inducedOn G s).degree w + (G.neighborFinset w ∩ t).card [MOD q] := by
    simpa [degree_union_eq_degree_add_external (G := G) (hst := hst) (v := v),
      degree_union_eq_degree_add_external (G := G) (hst := hst) (v := w)] using hdeg v w
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact Nat.ModEq.add_right_cancel (hext v w) hsum

lemma modEq_externalDegree_of_modEq_unionDegree_and_inducesModEqDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hst : Disjoint s t) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hmod : InducesModEqDegree G s q) :
    ∀ v w : ↑(s : Set V),
      (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesModEqDegree] at hmod
  intro v w
  have hbig :
      (G.neighborFinset v ∩ (s ∪ t)).card ≡
        (G.neighborFinset w ∩ (s ∪ t)).card [MOD q] := by
    simpa [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ t)
      (v := ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩),
      degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ t)
      (v := ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩)] using hdeg v w
  have hsplitv :
      (G.neighborFinset v ∩ (s ∪ t)).card =
        (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card := by
    exact card_neighborFinset_inter_union (G := G) hst v
  have hsplitw :
      (G.neighborFinset w ∩ (s ∪ t)).card =
        (G.neighborFinset w ∩ s).card + (G.neighborFinset w ∩ t).card := by
    exact card_neighborFinset_inter_union (G := G) hst w
  have hsmall :
      (G.neighborFinset v ∩ s).card ≡ (G.neighborFinset w ∩ s).card [MOD q] := by
    have hsmall' : (inducedOn G s).degree v % q = (inducedOn G s).degree w % q := by
      simpa [Nat.ModEq] using hmod v w
    rw [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s) (v := v),
      degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s) (v := w)] at hsmall'
    simpa [Nat.ModEq] using hsmall'
  have hsum :
      (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card ≡
        (G.neighborFinset w ∩ s).card + (G.neighborFinset w ∩ t).card [MOD q] := by
    simpa [hsplitv, hsplitw] using hbig
  have hsum' :
      (G.neighborFinset v ∩ t).card + (G.neighborFinset v ∩ s).card ≡
        (G.neighborFinset w ∩ t).card + (G.neighborFinset w ∩ s).card [MOD q] := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  exact Nat.ModEq.add_right_cancel hsmall hsum'

lemma inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree
    (G : SimpleGraph V) {s : Finset V} {d q : ℕ}
    (hinterval : InducesDegreeInterval G s d q)
    (hmod : InducesModEqDegree G s q) :
    ∃ d' : ℕ, InducesRegularOfDegree G s d' := by
  classical
  dsimp [InducesDegreeInterval] at hinterval
  rw [InducesModEqDegree] at hmod
  by_cases hs : s.Nonempty
  · obtain ⟨v0, hv0⟩ := hs
    refine ⟨(inducedOn G s).degree ⟨v0, hv0⟩, ?_⟩
    rw [InducesRegularOfDegree]
    intro v
    rcases hinterval v with ⟨hdv, hv_lt⟩
    rcases hinterval ⟨v0, hv0⟩ with ⟨hd0, hv0_lt⟩
    have hshift :
        (inducedOn G s).degree v - d ≡
          (inducedOn G s).degree ⟨v0, hv0⟩ - d [MOD q] := by
      exact Nat.ModEq.sub_right hdv hd0 (hmod v ⟨v0, hv0⟩)
    have hv_sub_lt : (inducedOn G s).degree v - d < q := by
      omega
    have hv0_sub_lt : (inducedOn G s).degree ⟨v0, hv0⟩ - d < q := by
      omega
    rw [Nat.ModEq, Nat.mod_eq_of_lt hv_sub_lt, Nat.mod_eq_of_lt hv0_sub_lt] at hshift
    omega
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    exact ⟨0, inducesRegularOfDegree_empty G⟩

lemma inducesRegularOfDegree_of_degree_lt_modulus_of_inducesModEqDegree
    (G : SimpleGraph V) {s : Finset V} {q : ℕ}
    (hbound : InducesDegreeLtModulus G s q)
    (hmod : InducesModEqDegree G s q) :
    ∃ d : ℕ, InducesRegularOfDegree G s d := by
  refine inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree
    (G := G) (d := 0) ?_ hmod
  dsimp [InducesDegreeInterval, InducesDegreeLtModulus]
  intro v
  exact ⟨Nat.zero_le _, by simpa [Nat.zero_add] using hbound v⟩

lemma hasRegularInducedSubgraphOfCard_of_degreeInterval_of_inducesModEqDegree
    (G : SimpleGraph V) {k : ℕ} {s : Finset V} {d q : ℕ} (hks : k ≤ s.card)
    (hinterval : InducesDegreeInterval G s d q)
    (hmod : InducesModEqDegree G s q) :
    HasRegularInducedSubgraphOfCard G k := by
  rcases inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree G hinterval hmod with
    ⟨d', hd'⟩
  exact ⟨s, hks, d', hd'⟩

lemma inducesRegularOfDegree_of_maxDegree_lt_modulus_of_inducesModEqDegree
    (G : SimpleGraph V) {s : Finset V} {q : ℕ}
    (hq : InducesDegreeLtModulus G s q)
    (hmod : InducesModEqDegree G s q) :
    ∃ d : ℕ, InducesRegularOfDegree G s d := by
  exact inducesRegularOfDegree_of_degree_lt_modulus_of_inducesModEqDegree G hq hmod

lemma inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree
    (G : SimpleGraph V) {s : Finset V} {q : ℕ} (hq : s.card ≤ q)
    (hmod : InducesModEqDegree G s q) :
    ∃ d : ℕ, InducesRegularOfDegree G s d := by
  classical
  refine inducesRegularOfDegree_of_degree_lt_modulus_of_inducesModEqDegree G ?_ hmod
  dsimp [InducesDegreeLtModulus]
  intro v
  exact lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G s) v)) hq

lemma hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hmod : HasModularWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  rcases hmod with ⟨s, hks, q, hq, hsmod⟩
  rcases inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hq hsmod with
    ⟨d, hd⟩
  exact ⟨s, hks, d, hd⟩

lemma hasRegularInducedSubgraphOfCard_of_hasLowDegreeModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hmod : HasLowDegreeModularWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  rcases hmod with ⟨s, hks, q, hq, hsmod⟩
  rcases inducesRegularOfDegree_of_degree_lt_modulus_of_inducesModEqDegree G hq hsmod with
    ⟨d, hd⟩
  exact ⟨s, hks, d, hd⟩

lemma hasModularWitnessOfCard_of_hasRegularInducedSubgraphOfCard
    (G : SimpleGraph V) {k : ℕ} (hreg : HasRegularInducedSubgraphOfCard G k) :
    HasModularWitnessOfCard G k := by
  classical
  rcases hreg with ⟨s, hks, d, hd⟩
  refine ⟨s, hks, s.card, le_rfl, ?_⟩
  rw [InducesModEqDegree]
  intro v w
  simpa [hd v, hd w] using (Nat.ModEq.refl d)

lemma hasLowDegreeModularWitnessOfCard_of_hasRegularInducedSubgraphOfCard
    (G : SimpleGraph V) {k : ℕ} (hreg : HasRegularInducedSubgraphOfCard G k) :
    HasLowDegreeModularWitnessOfCard G k := by
  classical
  rcases hreg with ⟨s, hks, d, hd⟩
  refine ⟨s, hks, d + 1, ?_, ?_⟩
  · rw [InducesDegreeLtModulus]
    intro v
    simpa [hd v] using Nat.lt_succ_self d
  · rw [InducesModEqDegree]
    intro v w
    simpa [hd v, hd w] using (Nat.ModEq.refl d)

lemma hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (hst : Disjoint s t) {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasModularWitnessOfCard G k := by
  refine ⟨s, hks, q, hq, ?_⟩
  exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree G hst hdeg hext

lemma hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (hst : Disjoint s t) {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
    (hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
      G hks hst hq hdeg hext)

lemma hasRegularInducedSubgraphOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (hst : Disjoint s t) {d q : ℕ}
    (hinterval : InducesDegreeInterval G s d q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_degreeInterval_of_inducesModEqDegree G hks hinterval
    (inducesModEqDegree_of_modEq_unionDegree_and_externalDegree G hst hdeg hext)

/--
Two-block modular transport: if the ambient degrees on `s ∪ t₁ ∪ t₂` are constant modulo `q` on
`s`, and the external degrees into each disjoint control block `t₁`, `t₂` are separately constant
modulo `q` on `s`, then the induced degrees on `s` are constant modulo `q`.
-/
lemma inducesModEqDegree_of_modEq_unionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t₁ t₂ : Finset V}
    (hst : Disjoint s (t₁ ∪ t₂)) (ht : Disjoint t₁ t₂) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext₁ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₁).card ≡ (G.neighborFinset w ∩ t₁).card [MOD q])
    (hext₂ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₂).card ≡ (G.neighborFinset w ∩ t₂).card [MOD q]) :
    InducesModEqDegree G s q := by
  refine inducesModEqDegree_of_modEq_unionDegree_and_externalDegree G hst hdeg ?_
  intro v w
  have hv :
      (G.neighborFinset v ∩ (t₁ ∪ t₂)).card =
        (G.neighborFinset v ∩ t₁).card + (G.neighborFinset v ∩ t₂).card := by
    exact card_neighborFinset_inter_union (G := G) ht v
  have hw :
      (G.neighborFinset w ∩ (t₁ ∪ t₂)).card =
        (G.neighborFinset w ∩ t₁).card + (G.neighborFinset w ∩ t₂).card := by
    exact card_neighborFinset_inter_union (G := G) ht w
  rw [hv, hw]
  exact Nat.ModEq.add (hext₁ v w) (hext₂ v w)

lemma hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t₁ t₂ : Finset V} (hks : k ≤ s.card) (hst : Disjoint s (t₁ ∪ t₂))
    (ht : Disjoint t₁ t₂) {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext₁ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₁).card ≡ (G.neighborFinset w ∩ t₁).card [MOD q])
    (hext₂ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₂).card ≡ (G.neighborFinset w ∩ t₂).card [MOD q]) :
    HasModularWitnessOfCard G k := by
  refine ⟨s, hks, q, hq, ?_⟩
  exact inducesModEqDegree_of_modEq_unionDegree_and_two_externalDegrees G hst ht hdeg hext₁ hext₂

lemma hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_modEq_unionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t₁ t₂ : Finset V} (hks : k ≤ s.card) (hst : Disjoint s (t₁ ∪ t₂))
    (ht : Disjoint t₁ t₂) {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext₁ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₁).card ≡ (G.neighborFinset w ∩ t₁).card [MOD q])
    (hext₂ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₂).card ≡ (G.neighborFinset w ∩ t₂).card [MOD q]) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
    (hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_two_externalDegrees
      G hks hst ht hq hdeg hext₁ hext₂)

/--
If the ambient degrees on `s ∪ t ∪ u` are constant modulo `q` on `s`, and the external degrees into
the disjoint block `t` are constant modulo `q` on `s`, then the ambient degrees on `s ∪ u` are
constant modulo `q` on `s`.
-/
lemma modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t u : Finset V}
    (hst : Disjoint s t) (htu : Disjoint t u) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (t ∪ u))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (t ∪ u))).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    ∀ v w : ↑(s : Set V),
      (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (s ∪ u)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
  have hdisj : Disjoint (s ∪ u) t := by
    rw [Finset.disjoint_union_left]
    exact ⟨hst, htu.symm⟩
  intro v w
  have hbig :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card ≡
        (G.neighborFinset w ∩ (s ∪ (t ∪ u))).card [MOD q] := by
    simpa [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ (t ∪ u))
      (v := ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩),
      degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ (t ∪ u))
      (v := ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩)] using hdeg v w
  have hsplitv :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card =
        (G.neighborFinset v ∩ (s ∪ u)).card + (G.neighborFinset v ∩ t).card := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (card_neighborFinset_inter_union (G := G) (s := s ∪ u) (t := t) hdisj v)
  have hsplitw :
      (G.neighborFinset w ∩ (s ∪ (t ∪ u))).card =
        (G.neighborFinset w ∩ (s ∪ u)).card + (G.neighborFinset w ∩ t).card := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (card_neighborFinset_inter_union (G := G) (s := s ∪ u) (t := t) hdisj w)
  have hsum :
      (G.neighborFinset v ∩ (s ∪ u)).card + (G.neighborFinset v ∩ t).card ≡
        (G.neighborFinset w ∩ (s ∪ u)).card + (G.neighborFinset w ∩ t).card [MOD q] := by
    simpa [hsplitv, hsplitw] using hbig
  have hsmall :
      (G.neighborFinset v ∩ (s ∪ u)).card ≡
        (G.neighborFinset w ∩ (s ∪ u)).card [MOD q] := by
    exact Nat.ModEq.add_right_cancel (hext v w) hsum
  simpa [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ u)
    (v := ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩),
    degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ u)
    (v := ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩)] using hsmall

/--
If the ambient degrees on `s ∪ u` are constant modulo `q` on `s`, and the external degrees into the
disjoint block `t` are constant modulo `q` on `s`, then the ambient degrees on `s ∪ t ∪ u` are
constant modulo `q` on `s`.
-/
lemma modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t u : Finset V}
    (hst : Disjoint s t) (htu : Disjoint t u) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ u)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    ∀ v w : ↑(s : Set V),
      (inducedOn G (s ∪ (t ∪ u))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (s ∪ (t ∪ u))).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
  have hdisj : Disjoint (s ∪ u) t := by
    rw [Finset.disjoint_union_left]
    exact ⟨hst, htu.symm⟩
  intro v w
  have hsmall :
      (G.neighborFinset v ∩ (s ∪ u)).card ≡
        (G.neighborFinset w ∩ (s ∪ u)).card [MOD q] := by
    simpa [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ u)
      (v := ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩),
      degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ u)
      (v := ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩)] using hdeg v w
  have hsplitv :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card =
        (G.neighborFinset v ∩ (s ∪ u)).card + (G.neighborFinset v ∩ t).card := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (card_neighborFinset_inter_union (G := G) (s := s ∪ u) (t := t) hdisj v)
  have hsplitw :
      (G.neighborFinset w ∩ (s ∪ (t ∪ u))).card =
        (G.neighborFinset w ∩ (s ∪ u)).card + (G.neighborFinset w ∩ t).card := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (card_neighborFinset_inter_union (G := G) (s := s ∪ u) (t := t) hdisj w)
  have hbig :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card ≡
        (G.neighborFinset w ∩ (s ∪ (t ∪ u))).card [MOD q] := by
    simpa [hsplitv, hsplitw] using Nat.ModEq.add hsmall (hext v w)
  simpa [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ (t ∪ u))
    (v := ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩),
    degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s ∪ (t ∪ u))
    (v := ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩)] using hbig

/--
`HasConstantModExternalBlockDegrees G s q blocks` records that each control block carries a
prescribed constant residue for the external degree data on `s`.
-/
def HasConstantModExternalBlockDegrees (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (q : ℕ) : List (Finset V × ℕ) → Prop
  | [] => True
  | b :: bs =>
      (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ b.1).card ≡ b.2 [MOD q]) ∧
        HasConstantModExternalBlockDegrees G s q bs

/--
Exact constant block-degree data can be reduced modulo any modulus.
-/
lemma hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (q : ℕ)
    {blocks : List (Finset V × ℕ)} (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasConstantModExternalBlockDegrees G s q blocks := by
  induction blocks with
  | nil =>
      simpa [HasConstantExternalBlockDegrees, HasConstantModExternalBlockDegrees] using hext
  | cons b bs ih =>
      dsimp [HasConstantExternalBlockDegrees] at hext
      dsimp [HasConstantModExternalBlockDegrees]
      rcases hext with ⟨hhead, htail⟩
      refine ⟨?_, ih htail⟩
      intro v
      simpa [hhead v] using (Nat.ModEq.refl b.2 : b.2 ≡ b.2 [MOD q])

lemma hasConstantExternalBlockDegrees_mono
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hts : t ⊆ s)
    {blocks : List (Finset V × ℕ)} (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasConstantExternalBlockDegrees G t blocks := by
  induction blocks with
  | nil =>
      simpa [HasConstantExternalBlockDegrees] using hext
  | cons b bs ih =>
      dsimp [HasConstantExternalBlockDegrees] at hext ⊢
      rcases hext with ⟨hhead, htail⟩
      refine ⟨?_, ih htail⟩
      intro v
      exact hhead ⟨v.1, hts v.2⟩

lemma hasConstantModExternalBlockDegrees_mono
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hts : t ⊆ s)
    {blocks : List (Finset V × ℕ)} (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasConstantModExternalBlockDegrees G t q blocks := by
  induction blocks with
  | nil =>
      simpa [HasConstantModExternalBlockDegrees] using hext
  | cons b bs ih =>
      dsimp [HasConstantModExternalBlockDegrees] at hext ⊢
      rcases hext with ⟨hhead, htail⟩
      refine ⟨?_, ih htail⟩
      intro v
      exact hhead ⟨v.1, hts v.2⟩

lemma constant_externalDegree_controlBlockUnion_of_hasConstantExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
      HasConstantExternalBlockDegrees G s blocks →
      ∀ v : ↑(s : Set V),
        (G.neighborFinset v ∩ controlBlockUnion blocks).card = controlBlockDegreeSum blocks
  | [], _hsep, _hext, v => by
      simp [controlBlockUnion, controlBlockDegreeSum]
  | (b :: bs), hsep, hext, v => by
      rcases b with ⟨t, e⟩
      rcases hsep with ⟨_hst, htu, hsepTail⟩
      rcases hext with ⟨hextHead, hextTail⟩
      have hsplit :
          (G.neighborFinset v ∩ controlBlockUnion ((t, e) :: bs)).card =
            (G.neighborFinset v ∩ t).card + (G.neighborFinset v ∩ controlBlockUnion bs).card := by
        simpa [controlBlockUnion] using
          (card_neighborFinset_inter_union (G := G) (s := t) (t := controlBlockUnion bs) htu v)
      rw [hsplit, hextHead v]
      simpa [controlBlockDegreeSum] using
        constant_externalDegree_controlBlockUnion_of_hasConstantExternalBlockDegrees
          (G := G) hsepTail hextTail v

lemma modEq_externalDegree_controlBlockUnion_of_hasConstantModExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} {q : ℕ} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
      HasConstantModExternalBlockDegrees G s q blocks →
      ∀ v : ↑(s : Set V),
        (G.neighborFinset v ∩ controlBlockUnion blocks).card ≡ controlBlockDegreeSum blocks [MOD q]
  | [], _hsep, _hext, v => by
      simpa [controlBlockUnion, controlBlockDegreeSum] using
        (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])
  | (b :: bs), hsep, hext, v => by
      rcases b with ⟨t, e⟩
      rcases hsep with ⟨_hst, htu, hsepTail⟩
      rcases hext with ⟨hextHead, hextTail⟩
      have hsplit :
          (G.neighborFinset v ∩ controlBlockUnion ((t, e) :: bs)).card =
            (G.neighborFinset v ∩ t).card + (G.neighborFinset v ∩ controlBlockUnion bs).card := by
        simpa [controlBlockUnion] using
          (card_neighborFinset_inter_union (G := G) (s := t) (t := controlBlockUnion bs) htu v)
      rw [hsplit, controlBlockDegreeSum]
      exact Nat.ModEq.add (hextHead v)
        (modEq_externalDegree_controlBlockUnion_of_hasConstantModExternalBlockDegrees
          (G := G) (q := q) hsepTail hextTail v)

/--
Multiscale modular transport: if the ambient degree on `s` is constant modulo `q` inside the graph
induced on `s` plus a separated list of control blocks, and each block contributes a separately
constant external residue on `s`, then the induced degrees on `s` are constant modulo `q`.
-/
lemma inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} {q : ℕ} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) →
      HasConstantModExternalBlockDegrees G s q blocks →
      InducesModEqDegree G s q
  | [], _hsep, hdeg, _hext => by
      exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
        (G := G) (s := s) (t := ∅) (by simp)
        (hdeg := by
          intro v w
          simpa [controlBlockUnion] using hdeg v w)
        (hext := by
          intro v w
          simpa using (Nat.ModEq.refl 0))
  | (b :: bs), hsep, hdeg, hext => by
      rcases b with ⟨t, r⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      rcases hext with ⟨hextHeadConst, hextTail⟩
      have hextHead :
          ∀ v w : ↑(s : Set V),
            (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
        intro v w
        exact (hextHeadConst v).trans (hextHeadConst w).symm
      have hdegTail :
          ∀ v w : ↑(s : Set V),
            (inducedOn G (s ∪ controlBlockUnion bs)).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (s ∪ controlBlockUnion bs)).degree
                ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        exact
          modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
            (G := G) (s := s) (t := t) (u := controlBlockUnion bs) hst htu
            (hdeg := by
              intro v w
              simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                Finset.union_comm] using hdeg v w)
            (hext := hextHead)
      exact inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
        (G := G) (s := s) (q := q) hsepTail hdegTail hextTail

/--
If the ambient degrees on `s ∪ controlBlockUnion blocks ∪ tail` are constant modulo `q` on `s`,
and each separated control block contributes a separately constant external residue on `s`, then the
ambient degrees on `s ∪ tail` are constant modulo `q` on `s`.
-/
lemma modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s tail : Finset V} {q : ℕ} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
      Disjoint (controlBlockUnion blocks) tail →
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (controlBlockUnion blocks ∪ tail))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (controlBlockUnion blocks ∪ tail))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) →
      HasConstantModExternalBlockDegrees G s q blocks →
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ tail)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ tail)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]
  | [], _hsep, _hdisj, hdeg, _hext => by
      intro v w
      have hcastv :
          (inducedOn G (s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ tail)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))
            (t := s ∪ tail)
            (h := by simp [controlBlockUnion, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      have hcastw :
          (inducedOn G (s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ tail)).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
        simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))
            (t := s ∪ tail)
            (h := by simp [controlBlockUnion, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl w.2)))
      simpa [hcastv, hcastw] using hdeg v w
  | (b :: bs), hsep, hdisj, hdeg, hext => by
      rcases b with ⟨t, r⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      rcases hext with ⟨hextHeadConst, hextTail⟩
      have hextHead :
          ∀ v w : ↑(s : Set V),
            (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
        intro v w
        exact (hextHeadConst v).trans (hextHeadConst w).symm
      have hdisjTail : Disjoint (controlBlockUnion bs) tail := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxBs hxTail
        exact (Finset.disjoint_left.mp hdisj)
          (by
            simpa [controlBlockUnion] using
              (Finset.mem_union.mpr (Or.inr hxBs) : x ∈ t ∪ controlBlockUnion bs))
          hxTail
      have htuTail : Disjoint t (controlBlockUnion bs ∪ tail) := by
        rw [Finset.disjoint_union_right]
        refine ⟨htu, ?_⟩
        refine Finset.disjoint_left.mpr ?_
        intro x hxT hxTail
        exact (Finset.disjoint_left.mp hdisj) (by simp [controlBlockUnion, hxT]) hxTail
      have hdegTail :
          ∀ v w : ↑(s : Set V),
            (inducedOn G (s ∪ (controlBlockUnion bs ∪ tail))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (s ∪ (controlBlockUnion bs ∪ tail))).degree
                ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        exact
          modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
            (G := G) (s := s) (t := t) (u := controlBlockUnion bs ∪ tail) hst htuTail
            (hdeg := by
              intro v w
              have hcastv :
                  (inducedOn G (s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))).degree
                      ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                    (inducedOn G (s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))).degree
                      ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
                simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                  Finset.union_comm] using
                  (inducedOn_degree_congr (G := G)
                    (s := s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))
                    (t := s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))
                    (h := by
                      simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                        Finset.union_comm])
                    (hs := Finset.mem_union.mpr (Or.inl v.2))
                    (ht := Finset.mem_union.mpr (Or.inl v.2)))
              have hcastw :
                  (inducedOn G (s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))).degree
                      ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
                    (inducedOn G (s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))).degree
                      ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
                simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                  Finset.union_comm] using
                  (inducedOn_degree_congr (G := G)
                    (s := s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))
                    (t := s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))
                    (h := by
                      simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                        Finset.union_comm])
                    (hs := Finset.mem_union.mpr (Or.inl w.2))
                    (ht := Finset.mem_union.mpr (Or.inl w.2)))
              simpa [hcastv, hcastw] using hdeg v w)
            (hext := hextHead)
      exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalBlockDegrees
        (G := G) (s := s) (tail := tail) (q := q) hsepTail hdisjTail hdegTail hextTail

/--
If the ambient degrees on `s ∪ tail` are constant modulo `q` on `s`, and each separated control
block contributes a separately constant external residue on `s`, then the ambient degrees on
`s ∪ controlBlockUnion blocks ∪ tail` are constant modulo `q` on `s`.
-/
lemma modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s tail : Finset V} {q : ℕ} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
      Disjoint (controlBlockUnion blocks) tail →
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ tail)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ tail)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) →
      HasConstantModExternalBlockDegrees G s q blocks →
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (controlBlockUnion blocks ∪ tail))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (controlBlockUnion blocks ∪ tail))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]
  | [], _hsep, _hdisj, hdeg, _hext => by
      intro v w
      have hcastv :
          (inducedOn G (s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ tail)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))
            (t := s ∪ tail)
            (h := by simp [controlBlockUnion, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      have hcastw :
          (inducedOn G (s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ tail)).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
        simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))
            (t := s ∪ tail)
            (h := by simp [controlBlockUnion, Finset.empty_union])
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl w.2)))
      simpa [hcastv, hcastw] using hdeg v w
  | (b :: bs), hsep, hdisj, hdeg, hext => by
      rcases b with ⟨t, r⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      rcases hext with ⟨hextHeadConst, hextTail⟩
      have hdisjHead : Disjoint t tail := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxT hxTail
        exact (Finset.disjoint_left.mp hdisj) (by simp [controlBlockUnion, hxT]) hxTail
      have hdisjTail : Disjoint (controlBlockUnion bs) tail := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxBs hxTail
        exact (Finset.disjoint_left.mp hdisj) (by simp [controlBlockUnion, hxBs]) hxTail
      have hdegTail :
          ∀ v w : ↑(s : Set V),
            (inducedOn G (s ∪ (controlBlockUnion bs ∪ tail))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
              (inducedOn G (s ∪ (controlBlockUnion bs ∪ tail))).degree
                ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
        exact
          modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
            (G := G) (s := s) (tail := tail) (q := q) hsepTail hdisjTail hdeg hextTail
      have hextHead :
          ∀ v w : ↑(s : Set V),
            (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q] := by
        intro v w
        exact (hextHeadConst v).trans (hextHeadConst w).symm
      have htuTail : Disjoint t (controlBlockUnion bs ∪ tail) := by
        rw [Finset.disjoint_union_right]
        exact ⟨htu, hdisjHead⟩
      intro v w
      have hcastv :
          (inducedOn G (s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))
            (t := s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))
            (h := by
              simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      have hcastw :
          (inducedOn G (s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
        simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))
            (t := s ∪ (controlBlockUnion ((t, r) :: bs) ∪ tail))
            (h := by
              simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm])
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl w.2)))
      simpa [hcastv, hcastw] using
        (modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalDegree
          (G := G) (s := s) (t := t) (u := controlBlockUnion bs ∪ tail)
          hst htuTail hdegTail hextHead v w)

lemma hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasModularWitnessOfCard G k := by
  refine ⟨s, hks, q, hq, ?_⟩
  exact inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees G hsep hdeg hext

lemma hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
    (hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalBlockDegrees
      G hks hq hsep hdeg hext)

lemma hasRegularInducedSubgraphOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {d q : ℕ}
    (hinterval : InducesDegreeInterval G s d q)
    {blocks : List (Finset V × ℕ)} (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_degreeInterval_of_inducesModEqDegree G hks hinterval
    (inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees G hsep hdeg hext)

/--
A nonempty control-block union, ruling out the vacuous empty-block case.
-/
def NonemptyControlBlockUnion (blocks : List (Finset V × ℕ)) : Prop :=
  0 < (controlBlockUnion blocks).card

/--
A nonempty exact control-block witness of size at least `k`: a large vertex set `s` together with a
genuinely present separated control-block family whose exact ambient and external degree data force
regularity on `G[s]`.
-/
def HasExactControlBlockWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧
    ∃ blocks : List (Finset V × ℕ),
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      ∃ D : ℕ,
        (∀ v : ↑(s : Set V),
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
        HasConstantExternalBlockDegrees G s blocks

/--
A bounded nonempty exact control-block witness: as above, but using at most `r` control blocks.
-/
def HasBoundedExactControlBlockWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧
    ∃ blocks : List (Finset V × ℕ),
      blocks.length ≤ r ∧
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      ∃ D : ℕ,
        (∀ v : ↑(s : Set V),
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
        HasConstantExternalBlockDegrees G s blocks

/--
A single-control exact witness of size at least `k`: a large set `s` together with one genuinely
nonempty control set `t` such that the ambient degrees on `G[s ∪ t]` and the external degrees into
`t` are each constant on `s`.
-/
def HasSingleControlExactWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, k ≤ s.card ∧ 0 < t.card ∧ Disjoint s t ∧
    ∃ D e : ℕ,
      (∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)

/--
A single-control exact witness with an explicit control-size budget `r`.
-/
def HasBoundedSingleControlExactWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, k ≤ s.card ∧ 0 < t.card ∧ t.card ≤ r ∧ Disjoint s t ∧
    ∃ D e : ℕ,
      (∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)

/--
A single-control modular witness of size at least `k`: a large set `s` together with one genuinely
nonempty control set `t` and a modulus `q ≥ |s|` such that the ambient degrees on `G[s ∪ t]` and the
external degrees into `t` are each constant modulo `q` on `s`.
-/
def HasSingleControlModularWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, k ≤ s.card ∧ 0 < t.card ∧ Disjoint s t ∧
    ∃ q : ℕ, s.card ≤ q ∧
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      (∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q])

/--
A single-control modular witness with an explicit control-size budget `r`.
-/
def HasBoundedSingleControlModularWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, k ≤ s.card ∧ 0 < t.card ∧ t.card ≤ r ∧ Disjoint s t ∧
    ∃ q : ℕ, s.card ≤ q ∧
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      (∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q])

/--
A single-control modular bucketing witness of size at least `k`: a large bucket `u` inside a host
set `s`, a nonempty disjoint control set `t`, and a modulus `q ≥ |u|`, such that on `u` the ambient
degrees in `G[u ∪ ((s \ u) ∪ t)]`, the dropped-part degrees into `s \ u`, and the control-set
degrees into `t` are all constant modulo `q`.
-/
def HasSingleControlModularBucketingWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, k ≤ u.card ∧ u ⊆ s ∧ 0 < t.card ∧ Disjoint s t ∧
    ∃ q : ℕ, u.card ≤ q ∧
      (∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      (∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
      (∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q])

/--
A bounded single-control modular bucketing witness with an explicit control-size budget `r`.
-/
def HasBoundedSingleControlModularBucketingWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, k ≤ u.card ∧ u ⊆ s ∧ 0 < t.card ∧ t.card ≤ r ∧ Disjoint s t ∧
    ∃ q : ℕ, u.card ≤ q ∧
      (∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      (∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
      (∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q])

/--
A single-control bucketing witness of size at least `k`: a large bucket `u` inside a host set `s`
and a nonempty disjoint control set `t`, such that on `u` the ambient degree in
`G[u ∪ ((s \ u) ∪ t)]`, the degree into the dropped vertices `s \ u`, and the degree into `t` are
all constant.
-/
def HasSingleControlBucketingWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, k ≤ u.card ∧ u ⊆ s ∧ 0 < t.card ∧ Disjoint s t ∧
    ∃ D eDrop eCtrl : ℕ,
      (∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
      (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = eCtrl)

/--
A single-control bucketing witness with an explicit control-size budget `r`.
-/
def HasBoundedSingleControlBucketingWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, k ≤ u.card ∧ u ⊆ s ∧ 0 < t.card ∧ t.card ≤ r ∧ Disjoint s t ∧
    ∃ D eDrop eCtrl : ℕ,
      (∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
      (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
      (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = eCtrl)

/--
A multiblock bucketing witness of size at least `k`: a large bucket `u` inside a host set `s` and a
nonempty separated control-block family `blocks`, such that on `u` the ambient degree in
`G[u ∪ ((s \ u) ∪ controlBlockUnion blocks)]`, the degree into the dropped vertices `s \ u`, and
the degrees into every control block are all constant.
-/
def HasControlBlockBucketingWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ u ⊆ s ∧
    ∃ blocks : List (Finset V × ℕ),
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      ∃ D eDrop : ℕ,
        (∀ v : ↑(u : Set V),
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
        (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
        HasConstantExternalBlockDegrees G u blocks

/--
A bounded multiblock bucketing witness where the eventual exact control-block witness uses at most
`r` control blocks; one slot is reserved for the dropped part `s \ u`.
-/
def HasBoundedControlBlockBucketingWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ u ⊆ s ∧
    ∃ blocks : List (Finset V × ℕ),
      blocks.length + 1 ≤ r ∧
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      ∃ D eDrop : ℕ,
        (∀ v : ↑(u : Set V),
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
        (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
        HasConstantExternalBlockDegrees G u blocks

/--
A multiblock modular bucketing witness of size at least `k`: a large bucket `u` inside a host set `s`
and a nonempty separated control-block family `blocks`, together with a modulus `q ≥ |u|`, such that
on `u` the ambient degree in `G[u ∪ ((s \ u) ∪ controlBlockUnion blocks)]`, the dropped-part degree
into `s \ u`, and the degrees into every control block are all constant modulo `q`.
-/
def HasControlBlockModularBucketingWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ u ⊆ s ∧
    ∃ q : ℕ, u.card ≤ q ∧
      ∃ blocks : List (Finset V × ℕ),
        NonemptyControlBlockUnion blocks ∧
        ControlBlocksSeparated s blocks ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
            (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
        (∀ v w : ↑(u : Set V),
          (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
        HasConstantModExternalBlockDegrees G u q blocks

/--
A bounded multiblock modular bucketing witness using at most `r` control blocks. Unlike the exact
version, the dropped part stays as modular residue data and does not consume an extra control-block
slot.
-/
def HasBoundedControlBlockModularBucketingWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ u ⊆ s ∧
    ∃ q : ℕ, u.card ≤ q ∧
      ∃ blocks : List (Finset V × ℕ),
        blocks.length ≤ r ∧
        NonemptyControlBlockUnion blocks ∧
        ControlBlocksSeparated s blocks ∧
        (∀ v w : ↑(u : Set V),
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
            (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
              ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
        (∀ v w : ↑(u : Set V),
          (G.neighborFinset v ∩ (s \ u)).card ≡ (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
        HasConstantModExternalBlockDegrees G u q blocks

/--
`cascadeTerminal s chain` is the final surviving bucket obtained by repeatedly replacing the current
host by the next bucket in `chain`.
-/
def cascadeTerminal (s : Finset V) : List (Finset V) → Finset V
  | [] => s
  | u :: chain => cascadeTerminal u chain

/--
`HasSingleControlCascadeFrom G t s chain` records a multistage refinement from a host `s` down a
chain of smaller buckets while keeping a fixed external control set `t`. At each proper step the
ambient degree in `G[s ∪ t]` and the degree into the dropped part `s \ u` are frozen on the next
bucket `u`; at the terminal bucket, the ambient degree in `G[u ∪ t]` and the degree into `t` are
frozen.
-/
def HasSingleControlCascadeFrom (G : SimpleGraph V) (t : Finset V) :
    Finset V → List (Finset V) → Prop := by
  classical
  exact fun s chain =>
    match chain with
    | [] =>
        ∃ D e : ℕ,
          (∀ v : ↑(s : Set V),
            (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
          (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    | u :: chain =>
        ∃ hu : u ⊆ s, ∃ D eDrop : ℕ,
          (∀ v : ↑(u : Set V),
            (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ = D) ∧
          (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
          HasSingleControlCascadeFrom G t u chain

/--
A single-control cascade witness of size at least `k`: a host `s`, a nonempty disjoint control set
`t`, and a chain of bucket refinements whose terminal bucket has size at least `k`.
-/
def HasSingleControlCascadeWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    0 < t.card ∧
    Disjoint s t ∧
    HasSingleControlCascadeFrom G t s chain

/--
A bounded single-control cascade witness, where the final exact control-block witness will use at
most `r` control blocks (one for each cascade drop, plus the terminal control set `t`).
-/
def HasBoundedSingleControlCascadeWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    chain.length + 1 ≤ r ∧
    0 < t.card ∧
    Disjoint s t ∧
    HasSingleControlCascadeFrom G t s chain

/--
`HasControlBlockCascadeFrom G blocks s chain` records a multistage refinement from a host `s` down a
chain of smaller buckets while keeping a fixed separated control-block family `blocks`. At each
proper step the ambient degree in `G[s ∪ controlBlockUnion blocks]` and the degree into the dropped
part `s \ u` are frozen on the next bucket `u`; at the terminal bucket, the ambient degree in
`G[s ∪ controlBlockUnion blocks]` and every external block degree are frozen.
-/
def HasControlBlockCascadeFrom (G : SimpleGraph V) (blocks : List (Finset V × ℕ)) :
    Finset V → List (Finset V) → Prop := by
  classical
  exact fun s chain =>
    match chain with
    | [] =>
        ∃ D : ℕ,
          (∀ v : ↑(s : Set V),
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) ∧
          HasConstantExternalBlockDegrees G s blocks
    | u :: chain =>
        ∃ hu : u ⊆ s, ∃ D eDrop : ℕ,
          (∀ v : ↑(u : Set V),
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                ⟨v, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ = D) ∧
          (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card = eDrop) ∧
          HasControlBlockCascadeFrom G blocks u chain

/--
A multiblock cascade witness of size at least `k`: a host `s`, a nonempty separated control-block
family, and a chain of bucket refinements whose terminal bucket has size at least `k`.
-/
def HasControlBlockCascadeWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ blocks : List (Finset V × ℕ), ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated s blocks ∧
    HasControlBlockCascadeFrom G blocks s chain

/--
A bounded multiblock cascade witness, where the final exact control-block witness uses at most `r`
control blocks (one for each cascade drop, plus the initial fixed control-block family).
-/
def HasBoundedControlBlockCascadeWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ blocks : List (Finset V × ℕ), ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    chain.length + blocks.length ≤ r ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated s blocks ∧
    HasControlBlockCascadeFrom G blocks s chain

/--
`HasControlBlockModularCascadeFrom G q blocks s chain` is the modular analogue of
`HasControlBlockCascadeFrom`: the modulus `q` is fixed across the whole refinement, the ambient
degree on each surviving bucket is constant modulo `q`, and each dropped part contributes an
explicit constant residue modulo `q`.
-/
def HasControlBlockModularCascadeFrom (G : SimpleGraph V) (q : ℕ)
    (blocks : List (Finset V × ℕ)) : Finset V → List (Finset V) → Prop := by
  classical
  exact fun s chain =>
    match chain with
    | [] =>
        (∀ v w : ↑(s : Set V),
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
              ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
        HasConstantModExternalBlockDegrees G s q blocks
    | u :: chain =>
        ∃ hu : u ⊆ s, ∃ eDrop : ℕ,
          (∀ v w : ↑(u : Set V),
            (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                ⟨v, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
              (inducedOn G (s ∪ controlBlockUnion blocks)).degree
                ⟨w, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q]) ∧
          (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card ≡ eDrop [MOD q]) ∧
          HasControlBlockModularCascadeFrom G q blocks u chain

/--
A modular multiblock cascade witness of size at least `k`: a host `s`, a modulus `q`, a nonempty
separated control-block family, and a chain of bucket refinements whose terminal bucket has size at
least `k` and at most `q`.
-/
def HasControlBlockModularCascadeWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ q : ℕ, ∃ blocks : List (Finset V × ℕ), ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    (cascadeTerminal s chain).card ≤ q ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated s blocks ∧
    HasControlBlockModularCascadeFrom G q blocks s chain

/--
A bounded modular multiblock cascade witness using at most `r` total control blocks after all drops
are packaged.
-/
def HasBoundedControlBlockModularCascadeWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ q : ℕ, ∃ blocks : List (Finset V × ℕ), ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    (cascadeTerminal s chain).card ≤ q ∧
    chain.length + blocks.length ≤ r ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated s blocks ∧
    HasControlBlockModularCascadeFrom G q blocks s chain

/--
A control-block witness of size at least `k`: a large vertex set `s`, a modulus `q ≥ |s|`, and a
separated list of control blocks whose ambient and external degree data force modular equality on
`G[s]`.
-/
def HasControlBlockWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ q : ℕ, s.card ≤ q ∧
    ∃ blocks : List (Finset V × ℕ),
      ControlBlocksSeparated s blocks ∧
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G s q blocks

/--
A genuine modular control-block witness of size at least `k`: as above, but requiring a genuinely
present separated control-block family.
-/
def HasNonemptyControlBlockModularWitnessOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ q : ℕ, s.card ≤ q ∧
    ∃ blocks : List (Finset V × ℕ),
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G s q blocks

/--
A bounded genuine modular control-block witness using at most `r` control blocks.
-/
def HasBoundedNonemptyControlBlockModularWitnessOfCard (G : SimpleGraph V) (k r : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ q : ℕ, s.card ≤ q ∧
    ∃ blocks : List (Finset V × ℕ),
      blocks.length ≤ r ∧
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      (∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G s q blocks

lemma hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasControlBlockWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, hsep, hdeg, hext⟩
  exact hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalBlockDegrees
    G hks hq hsep hdeg hext

lemma hasControlBlockWitnessOfCard_of_hasModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hmod : HasModularWitnessOfCard G k) :
    HasControlBlockWitnessOfCard G k := by
  classical
  rcases hmod with ⟨s, hks, q, hq, hsmod⟩
  rw [InducesModEqDegree] at hsmod
  refine ⟨s, hks, q, hq, [], ?_, ?_, ?_⟩
  · simp [ControlBlocksSeparated]
  · intro v w
    have hcastv :
        (inducedOn G (s ∪ controlBlockUnion ([] : List (Finset V × ℕ)))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree v := by
      simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
          (s := s ∪ controlBlockUnion ([] : List (Finset V × ℕ)))
          (t := s)
          (h := by simp [controlBlockUnion])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := v.2))
    have hcastw :
        (inducedOn G (s ∪ controlBlockUnion ([] : List (Finset V × ℕ)))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree w := by
      simpa [controlBlockUnion, Finset.empty_union] using
          (inducedOn_degree_congr (G := G)
          (s := s ∪ controlBlockUnion ([] : List (Finset V × ℕ)))
          (t := s)
          (h := by simp [controlBlockUnion])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := w.2))
    simpa [hcastv, hcastw] using hsmod v w
  · simp [HasConstantModExternalBlockDegrees]

theorem hasControlBlockWitnessOfCard_iff_hasModularWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasControlBlockWitnessOfCard G k ↔ HasModularWitnessOfCard G k := by
  constructor
  · exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
  · exact hasControlBlockWitnessOfCard_of_hasModularWitnessOfCard G

lemma hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasControlBlockWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
    (hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G hctrl)

lemma hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedExactControlBlockWitnessOfCard G k r) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, blocks, _hlen, hnonempty, hsep, D, hdeg, hext⟩
  exact ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩

lemma hasControlBlockWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasControlBlockWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, _hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, hks, s.card, le_rfl, blocks, hsep, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s s.card hext⟩
  intro v w
  simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D)

lemma hasNonemptyControlBlockModularWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedNonemptyControlBlockModularWitnessOfCard G k r) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, _hlen, hnonempty, hsep, hdeg, hext⟩
  exact ⟨s, hks, q, hq, blocks, hnonempty, hsep, hdeg, hext⟩

lemma hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasNonemptyControlBlockModularWitnessOfCard G k) :
    HasControlBlockWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, _hnonempty, hsep, hdeg, hext⟩
  exact ⟨s, hks, q, hq, blocks, hsep, hdeg, hext⟩

lemma hasControlBlockWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedNonemptyControlBlockModularWitnessOfCard G k r) :
    HasControlBlockWitnessOfCard G k := by
  exact hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hasNonemptyControlBlockModularWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
      G hctrl)

lemma hasModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasNonemptyControlBlockModularWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G hctrl)

lemma hasModularWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedNonemptyControlBlockModularWitnessOfCard G k r) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard G hctrl)

lemma hasRegularInducedSubgraphOfCard_of_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasNonemptyControlBlockModularWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G hctrl)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hctrl : HasBoundedNonemptyControlBlockModularWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard G hctrl)

lemma hasNonemptyControlBlockModularWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, hks, s.card, le_rfl, blocks, hnonempty, hsep, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s s.card hext⟩
  intro v w
  simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD s.card])

lemma hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ} (hexact : HasBoundedExactControlBlockWitnessOfCard G k r) :
    HasBoundedNonemptyControlBlockModularWitnessOfCard G k r := by
  classical
  rcases hexact with ⟨s, hks, blocks, hlen, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, hks, s.card, le_rfl, blocks, hlen, hnonempty, hsep, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s s.card hext⟩
  intro v w
  simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD s.card])

lemma hasExactControlBlockWitnessOfCard_of_inducesRegularOfDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k d : ℕ} {s : Finset V} (hks : k ≤ s.card)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hreg : InducesRegularOfDegree G s d)
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesRegularOfDegree] at hreg
  have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
    disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = d + controlBlockDegreeSum blocks := by
    intro v
    rw [degree_union_eq_degree_add_external (G := G) (hst := hsBlocks) (v := v)]
    calc
      (inducedOn G s).degree v + (G.neighborFinset v ∩ controlBlockUnion blocks).card
          = d + (G.neighborFinset v ∩ controlBlockUnion blocks).card := by
            rw [hreg v]
      _ = d + controlBlockDegreeSum blocks := by
        rw [constant_externalDegree_controlBlockUnion_of_hasConstantExternalBlockDegrees
          (G := G) hsep hext v]
  exact ⟨s, hks, blocks, hnonempty, hsep, d + controlBlockDegreeSum blocks, hdeg, hext⟩

lemma hasBoundedExactControlBlockWitnessOfCard_of_inducesRegularOfDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r d : ℕ} {s : Finset V} (hks : k ≤ s.card)
    {blocks : List (Finset V × ℕ)} (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hreg : InducesRegularOfDegree G s d)
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesRegularOfDegree] at hreg
  have hsBlocks : Disjoint s (controlBlockUnion blocks) :=
    disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
  have hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = d + controlBlockDegreeSum blocks := by
    intro v
    rw [degree_union_eq_degree_add_external (G := G) (hst := hsBlocks) (v := v)]
    calc
      (inducedOn G s).degree v + (G.neighborFinset v ∩ controlBlockUnion blocks).card
          = d + (G.neighborFinset v ∩ controlBlockUnion blocks).card := by
            rw [hreg v]
      _ = d + controlBlockDegreeSum blocks := by
        rw [constant_externalDegree_controlBlockUnion_of_hasConstantExternalBlockDegrees
          (G := G) hsep hext v]
  exact ⟨s, hks, blocks, hlen, hnonempty, hsep, d + controlBlockDegreeSum blocks, hdeg, hext⟩

lemma
    hasNonemptyControlBlockModularWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k d : ℕ} {s : Finset V} (hks : k ≤ s.card) {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hreg : InducesRegularOfDegree G s d)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesRegularOfDegree] at hreg
  have hsmod :
      ∀ v w : ↑(s : Set V),
        (inducedOn G s).degree v ≡ (inducedOn G s).degree w [MOD q] := by
    intro v w
    simpa [hreg v, hreg w] using (Nat.ModEq.refl d : d ≡ d [MOD q])
  have hsmod' :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ (∅ : Finset V))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ (∅ : Finset V))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
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
    simpa [hcastv, hcastw] using hsmod v w
  have hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hraw :=
      modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
        (G := G) (s := s) (tail := (∅ : Finset V)) (q := q) (blocks := blocks)
        hsep (by simp) hsmod' hext v w
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
  exact ⟨s, hks, q, hq, blocks, hnonempty, hsep, hdeg, hext⟩

lemma hasModularWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k d : ℕ} {s : Finset V} (hks : k ≤ s.card) {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hreg : InducesRegularOfDegree G s d)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hasNonemptyControlBlockModularWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modExternalBlockDegrees
      (G := G) hks hq hnonempty hsep hreg hext)

lemma hasExactControlBlockWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {d q : ℕ}
    (hinterval : InducesDegreeInterval G s d q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  rcases inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree G hinterval
      (inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
        (G := G) hsep hdeg
        (hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s q hext)) with
    ⟨d', hd'⟩
  exact hasExactControlBlockWitnessOfCard_of_inducesRegularOfDegree_and_externalBlockDegrees
    (G := G) hks hnonempty hsep hd' hext

lemma hasExactControlBlockWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine
    hasExactControlBlockWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalBlockDegrees
      (G := G) (hks := hks) (d := 0) ?_ hnonempty hsep hdeg hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G s) v)) hq

lemma hasExactControlBlockWitnessOfCard_of_hasRegularInducedSubgraphOfCard_inducedOn_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V}
    (hreg : HasRegularInducedSubgraphOfCard (inducedOn G s) k)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hreg with ⟨t, hkt, d, htd⟩
  let e : inducedOn G s ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (s : Set V))) G
  let u : Finset V := t.map (Function.Embedding.subtype (· ∈ (s : Set V)))
  have hus : u ⊆ s := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hku : k ≤ u.card := by
    simpa [u] using hkt
  have hud : InducesRegularOfDegree G u d := by
    simpa [u, e] using (inducesRegularOfDegree_of_embedding e htd)
  exact
    hasExactControlBlockWitnessOfCard_of_inducesRegularOfDegree_and_externalBlockDegrees
      (G := G) hku hnonempty (controlBlocksSeparated_mono hus hsep) hud
      (hasConstantExternalBlockDegrees_mono (G := G) hus hext)

lemma hasBoundedExactControlBlockWitnessOfCard_of_hasRegularInducedSubgraphOfCard_inducedOn_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s : Finset V}
    (hreg : HasRegularInducedSubgraphOfCard (inducedOn G s) k)
    {blocks : List (Finset V × ℕ)} (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  rcases hreg with ⟨t, hkt, d, htd⟩
  let e : inducedOn G s ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (s : Set V))) G
  let u : Finset V := t.map (Function.Embedding.subtype (· ∈ (s : Set V)))
  have hus : u ⊆ s := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hku : k ≤ u.card := by
    simpa [u] using hkt
  have hud : InducesRegularOfDegree G u d := by
    simpa [u, e] using (inducesRegularOfDegree_of_embedding e htd)
  exact
    hasBoundedExactControlBlockWitnessOfCard_of_inducesRegularOfDegree_and_externalBlockDegrees
      (G := G) hku hlen hnonempty (controlBlocksSeparated_mono hus hsep) hud
      (hasConstantExternalBlockDegrees_mono (G := G) hus hext)

lemma
    hasNonemptyControlBlockModularWitnessOfCard_of_card_le_modulus_of_hasRegularInducedSubgraphOfCard_inducedOn_and_modExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V}
    (hreg : HasRegularInducedSubgraphOfCard (inducedOn G s) k)
    {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
  classical
  rcases hreg with ⟨t, hkt, d, htd⟩
  let e : inducedOn G s ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ (s : Set V))) G
  let u : Finset V := t.map (Function.Embedding.subtype (· ∈ (s : Set V)))
  have hus : u ⊆ s := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact v.2
  have hku : k ≤ u.card := by
    simpa [u] using hkt
  have huq : u.card ≤ q := by
    exact le_trans (Finset.card_le_card hus) hq
  have hud : InducesRegularOfDegree G u d := by
    simpa [u, e] using (inducesRegularOfDegree_of_embedding e htd)
  exact
    hasNonemptyControlBlockModularWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modExternalBlockDegrees
      (G := G) hku huq hnonempty (controlBlocksSeparated_mono hus hsep) hud
      (hasConstantModExternalBlockDegrees_mono (G := G) hus hext)

lemma
    hasModularWitnessOfCard_of_card_le_modulus_of_hasRegularInducedSubgraphOfCard_inducedOn_and_modExternalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V}
    (hreg : HasRegularInducedSubgraphOfCard (inducedOn G s) k)
    {q : ℕ} (hq : s.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks)
    (hsep : ControlBlocksSeparated s blocks)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hasNonemptyControlBlockModularWitnessOfCard_of_card_le_modulus_of_hasRegularInducedSubgraphOfCard_inducedOn_and_modExternalBlockDegrees
      (G := G) hreg hq hnonempty hsep hext)

lemma hasSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (hst : Disjoint s t)
    {d q e : ℕ} (hinterval : InducesDegreeInterval G s d q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hsmod : InducesModEqDegree G s q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) hst hdeg
        (by
          intro v w
          simpa [hext v, hext w] using (Nat.ModEq.refl e : e ≡ e [MOD q]))
  rcases inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree G hinterval hsmod with
    ⟨d', hd'⟩
  refine ⟨s, t, hks, ht, hst, d' + e, e, ?_, hext⟩
  intro v
  calc
    (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
        = (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
            exact degree_union_eq_degree_add_external (G := G) (hst := hst) (v := v)
    _ = d' + e := by rw [hd' v, hext v]

lemma hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (hst : Disjoint s t)
    {q e : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine hasSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := ht) (hst := hst) (d := 0) ?_ hdeg hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G s) v)) hq

lemma hasBoundedSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (htr : t.card ≤ r)
    (hst : Disjoint s t) {d q e : ℕ} (hinterval : InducesDegreeInterval G s d q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hsmod : InducesModEqDegree G s q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) hst hdeg
        (by
          intro v w
          simpa [hext v, hext w] using (Nat.ModEq.refl e : e ≡ e [MOD q]))
  rcases inducesRegularOfDegree_of_degreeInterval_of_inducesModEqDegree G hinterval hsmod with
    ⟨d', hd'⟩
  refine ⟨s, t, hks, ht, htr, hst, d' + e, e, ?_, hext⟩
  intro v
  calc
    (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
        = (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
            exact degree_union_eq_degree_add_external (G := G) (hst := hst) (v := v)
    _ = d' + e := by rw [hd' v, hext v]

lemma hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (htr : t.card ≤ r)
    (hst : Disjoint s t) {q e : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine hasBoundedSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := ht) (htr := htr) (hst := hst) (d := 0) ?_ hdeg hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G s) v)) hq

lemma hasSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (hst : Disjoint s t)
    {D e : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩

lemma hasBoundedSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (htr : t.card ≤ r)
    (hst : Disjoint s t) {D e : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact ⟨s, t, hks, ht, htr, hst, D, e, hdeg, hext⟩

lemma hasSingleControlModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (hst : Disjoint s t)
    {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasSingleControlModularWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact ⟨s, t, hks, ht, hst, q, hq, hdeg, hext⟩

lemma hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (htr : t.card ≤ r)
    (hst : Disjoint s t) {q : ℕ} (hq : s.card ≤ q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact ⟨s, t, hks, ht, htr, hst, q, hq, hdeg, hext⟩

lemma hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, _hnonempty, hsep, D, hdeg, hext⟩
  exact hasRegularInducedSubgraphOfCard_of_constant_unionDegree_and_externalBlockDegrees
    G hks hsep hdeg hext

lemma hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩
  refine hasSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := hnonempty)
    (hst := disjoint_controlBlockUnion_of_controlBlocksSeparated hsep)
    (D := D) (e := controlBlockDegreeSum blocks) ?_ ?_
  · intro v
    simpa using hdeg v
  · intro v
    exact constant_externalDegree_controlBlockUnion_of_hasConstantExternalBlockDegrees G hsep hext v

lemma hasExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩
  refine ⟨s, hks, [(t, e)], ?_, ?_, D, ?_, ?_⟩
  · unfold NonemptyControlBlockUnion
    simpa using ht
  · refine ⟨hst, ?_, trivial⟩
    simp [controlBlockUnion]
  · intro v
    have hcast :
        (inducedOn G (s ∪ controlBlockUnion [(t, e)])).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [controlBlockUnion, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ controlBlockUnion [(t, e)])
          (t := s ∪ t)
          (h := by simp [controlBlockUnion, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    exact hcast.trans (hdeg v)
  · refine ⟨?_, trivial⟩
    intro v
    simpa using hext v

lemma hasBoundedExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ} (hr : 0 < r)
    (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩
  refine ⟨s, hks, [(t, e)], ?_, ?_, ?_, D, ?_, ?_⟩
  · simpa using hr
  · unfold NonemptyControlBlockUnion
    simpa using ht
  · refine ⟨hst, ?_, trivial⟩
    simp [controlBlockUnion]
  · intro v
    have hcast :
        (inducedOn G (s ∪ controlBlockUnion [(t, e)])).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [controlBlockUnion, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ controlBlockUnion [(t, e)])
          (t := s ∪ t)
          (h := by simp [controlBlockUnion, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    exact hcast.trans (hdeg v)
  · refine ⟨?_, trivial⟩
    intro v
    simpa using hext v

theorem hasSingleControlExactWitnessOfCard_iff_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlExactWitnessOfCard G k ↔ HasExactControlBlockWitnessOfCard G k := by
  constructor
  · exact hasExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
  · exact hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard G

lemma hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, _ht, hst, D, e, hdeg, hext⟩
  exact hasRegularInducedSubgraphOfCard_of_constant_unionDegree_and_externalDegree
    G hks hst hdeg hext

lemma hasSingleControlModularWitnessOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasSingleControlModularWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩
  refine hasSingleControlModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := ht) (hst := hst) (q := s.card) le_rfl ?_ ?_
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD s.card])
  · intro v w
    simpa [hext v, hext w] using (Nat.ModEq.refl e : e ≡ e [MOD s.card])

lemma hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G k r) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, htr, hst, D, e, hdeg, hext⟩
  refine hasBoundedSingleControlModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := ht) (htr := htr) (hst := hst) (q := s.card) le_rfl ?_ ?_
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD s.card])
  · intro v w
    simpa [hext v, hext w] using (Nat.ModEq.refl e : e ≡ e [MOD s.card])

lemma hasBoundedSingleControlExactWitnessOfCard_mono
    (G : SimpleGraph V) {k l r : ℕ} (hkl : k ≤ l)
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G l r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hls, ht, htr, hst, D, e, hdeg, hext⟩
  exact ⟨s, t, le_trans hkl hls, ht, htr, hst, D, e, hdeg, hext⟩

lemma hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k r : ℕ} {s t : Finset V} (hks : k ≤ s.card) (ht : 0 < t.card) (htr : t.card ≤ r)
    (hst : Disjoint s t) {q : ℕ} (hq : s.card ≤ q) (htq : t.card < q)
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hsmod : InducesModEqDegree G s q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) hst hdeg hext
  rcases inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hq hsmod with
    ⟨d, hd⟩
  by_cases hs : s.Nonempty
  · obtain ⟨v0, hv0⟩ := hs
    set e : ℕ := (G.neighborFinset v0 ∩ t).card with he
    have he_lt : e < q := by
      rw [he]
      exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
    have hext_exact : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e := by
      intro v
      have hv_lt : (G.neighborFinset v ∩ t).card < q := by
        exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
      have hmod : (G.neighborFinset v ∩ t).card ≡ e [MOD q] := by
        rw [he]
        exact hext v ⟨v0, hv0⟩
      rw [Nat.ModEq, Nat.mod_eq_of_lt hv_lt, Nat.mod_eq_of_lt he_lt] at hmod
      exact hmod
    refine hasBoundedSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
      (G := G) (hks := hks) (ht := ht) (htr := htr) (hst := hst) (D := d + e) (e := e) ?_
      hext_exact
    intro v
    calc
      (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
            exact degree_union_eq_degree_add_external (G := G) (s := s) (t := t) hst v
      _ = d + e := by simp [hd v, hext_exact v]
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    refine hasBoundedSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
      (G := G) (hks := hks) (ht := ht) (htr := htr) (hst := hst) (D := 0) (e := 0) ?_ ?_
    · intro v
      exact False.elim (by simpa using v.2)
    · intro v
      exact False.elim (by simpa using v.2)

lemma hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hkr : r < k)
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, htr, hst, q, hq, hdeg, hext⟩
  have htq : t.card < q := by
    exact lt_of_le_of_lt htr (lt_of_lt_of_le hkr (le_trans hks hq))
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_unionDegree_and_externalDegree
      (G := G) hks ht htr hst hq htq hdeg hext

lemma hasSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hkr : r < k)
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasSingleControlExactWitnessOfCard G k := by
  rcases
      hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
        G hkr hsingle with
    ⟨s, t, hks, ht, _htr, hst, D, e, hdeg, hext⟩
  exact ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩

lemma hasSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasSingleControlModularWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, _htr, hst, q, hq, hdeg, hext⟩
  exact ⟨s, t, hks, ht, hst, q, hq, hdeg, hext⟩

lemma hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlModularWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, _ht, hst, q, hq, hdeg, hext⟩
  exact hasModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    G hks hst hq hdeg hext

lemma hasModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
    (hasSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G hsingle)

lemma hasRegularInducedSubgraphOfCard_of_hasSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlModularWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasModularWitnessOfCard G
    (hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G hsingle)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasSingleControlModularWitnessOfCard G
    (hasSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G hsingle)

lemma hasSingleControlModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hctrl : HasNonemptyControlBlockModularWitnessOfCard G k) :
    HasSingleControlModularWitnessOfCard G k := by
  classical
  rcases hctrl with ⟨s, hks, q, hq, blocks, hnonempty, hsep, hdeg, hext⟩
  refine hasSingleControlModularWitnessOfCard_of_card_le_modulus_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := hnonempty)
    (hst := disjoint_controlBlockUnion_of_controlBlocksSeparated hsep) (q := q) hq ?_ ?_
  · intro v w
    simpa using hdeg v w
  · intro v w
    exact (modEq_externalDegree_controlBlockUnion_of_hasConstantModExternalBlockDegrees
      (G := G) (q := q) hsep hext v).trans
      ((modEq_externalDegree_controlBlockUnion_of_hasConstantModExternalBlockDegrees
        (G := G) (q := q) hsep hext w).symm)

lemma hasNonemptyControlBlockModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlModularWitnessOfCard G k) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, q, hq, hdeg, hext⟩
  by_cases hs : s.Nonempty
  · rcases hs with ⟨v0, hv0⟩
    refine ⟨s, hks, q, hq, [(t, (G.neighborFinset v0 ∩ t).card)], ?_, ?_, ?_, ?_⟩
    · unfold NonemptyControlBlockUnion
      simpa using ht
    · refine ⟨hst, ?_, trivial⟩
      simp [controlBlockUnion]
    · intro v w
      have hcastv :
          (inducedOn G (s ∪ controlBlockUnion [(t, (G.neighborFinset v0 ∩ t).card)])).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ t)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [controlBlockUnion, Finset.union_assoc] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ controlBlockUnion [(t, (G.neighborFinset v0 ∩ t).card)])
            (t := s ∪ t)
            (h := by simp [controlBlockUnion, Finset.union_assoc])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      have hcastw :
          (inducedOn G (s ∪ controlBlockUnion [(t, (G.neighborFinset v0 ∩ t).card)])).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
            (inducedOn G (s ∪ t)).degree ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
        simpa [controlBlockUnion, Finset.union_assoc] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ controlBlockUnion [(t, (G.neighborFinset v0 ∩ t).card)])
            (t := s ∪ t)
            (h := by simp [controlBlockUnion, Finset.union_assoc])
            (hs := Finset.mem_union.mpr (Or.inl w.2))
            (ht := Finset.mem_union.mpr (Or.inl w.2)))
      simpa [hcastv, hcastw] using hdeg v w
    · refine ⟨?_, trivial⟩
      intro v
      simpa using hext v ⟨v0, hv0⟩
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    refine ⟨∅, hks, q, hq, [(t, 0)], ?_, ?_, ?_, ?_⟩
    · unfold NonemptyControlBlockUnion
      simpa using ht
    · simp [ControlBlocksSeparated, controlBlockUnion]
    · intro v w
      exfalso
      simpa using v.2
    · refine ⟨?_, trivial⟩
      intro v
      exfalso
      simpa using v.2

theorem hasSingleControlModularWitnessOfCard_iff_hasNonemptyControlBlockModularWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlModularWitnessOfCard G k ↔ HasNonemptyControlBlockModularWitnessOfCard G k := by
  constructor
  · exact hasNonemptyControlBlockModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
  · exact hasSingleControlModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G

lemma hasSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasSingleControlModularBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, _htr, hst, q, hq, hdeg, hdrop, hctrl⟩
  exact ⟨u, s, t, hku, hus, ht, hst, q, hq, hdeg, hdrop, hctrl⟩

lemma hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlBucketingWitnessOfCard G k) :
    HasSingleControlModularBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  refine ⟨u, s, t, hku, hus, ht, hst, u.card, le_rfl, ?_, ?_, ?_⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD u.card])
  · intro v w
    simpa [hdrop v, hdrop w] using (Nat.ModEq.refl eDrop : eDrop ≡ eDrop [MOD u.card])
  · intro v w
    simpa [hctrl v, hctrl w] using (Nat.ModEq.refl eCtrl : eCtrl ≡ eCtrl [MOD u.card])

lemma hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlBucketingWitnessOfCard G k r) :
    HasBoundedSingleControlModularBucketingWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, htr, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  refine ⟨u, s, t, hku, hus, ht, htr, hst, u.card, le_rfl, ?_, ?_, ?_⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD u.card])
  · intro v w
    simpa [hdrop v, hdrop w] using (Nat.ModEq.refl eDrop : eDrop ≡ eDrop [MOD u.card])
  · intro v w
    simpa [hctrl v, hctrl w] using (Nat.ModEq.refl eCtrl : eCtrl ≡ eCtrl [MOD u.card])

lemma hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlModularBucketingWitnessOfCard G k) :
    HasSingleControlModularWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, hst, q, hq, hdeg, hdrop, hctrl⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact ⟨u, t, hku, ht, huT, q, hq, hsmall, hctrl⟩

lemma hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, htr, hst, q, hq, hdeg, hdrop, hctrl⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact ⟨u, t, hku, ht, htr, huT, q, hq, hsmall, hctrl⟩

lemma hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlModularWitnessOfCard G k) :
    HasSingleControlModularBucketingWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, q, hq, hdeg, hctrl⟩
  refine ⟨s, s, t, hks, by intro x hx; exact hx, ht, hst, q, hq, ?_, ?_, hctrl⟩
  · intro v w
    have hcastv :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

lemma hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlModularWitnessOfCard G k r) :
    HasBoundedSingleControlModularBucketingWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, htr, hst, q, hq, hdeg, hctrl⟩
  refine ⟨s, s, t, hks, by intro x hx; exact hx, ht, htr, hst, q, hq, ?_, ?_, hctrl⟩
  · intro v w
    have hcastv :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hdeg v w
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q])

lemma hasSingleControlModularBucketingWitnessOfCard_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasSingleControlModularBucketingWitnessOfCard G k := by
  refine ⟨u, s, t, hku, hu, ht, hst, q, hq, ?_, ?_, ?_⟩
  · cases
      Subsingleton.elim (‹DecidableRel G.Adj›)
        (fun a b => Classical.propDecidable (G.Adj a b))
    exact hdeg
  · cases
      Subsingleton.elim (‹DecidableRel G.Adj›)
        (fun a b => Classical.propDecidable (G.Adj a b))
    exact hdrop
  · cases
      Subsingleton.elim (‹DecidableRel G.Adj›)
        (fun a b => Classical.propDecidable (G.Adj a b))
    exact hctrl

lemma hasSingleControlModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasSingleControlModularBucketingWitnessOfCard G k := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  have huMod : InducesModEqDegree G u q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) huT hsmall hctrl
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
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q] := by
    exact modEq_externalDegree_of_modEq_unionDegree_and_inducesModEqDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' huMod
  have hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hsmall hdrop
  exact hasSingleControlModularBucketingWitnessOfCard_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G := G) hku hu ht hst hq hbig hdrop hctrl

lemma hasSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {d q e : ℕ} (hinterval : InducesDegreeInterval G u d q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact hasSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G := G) (s := u) (t := t) (hks := hku) (ht := ht) (hst := huT)
    (d := d) (q := q) (e := e) hinterval hsmall hext

lemma hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {q e : ℕ} (hq : u.card ≤ q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine
    hasSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
      (G := G) (hku := hku) (hu := hu) (ht := ht) (hst := hst) (d := 0) ?_ hdeg hdrop hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G u) v)) hq

lemma hasBoundedSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {d q e : ℕ} (hinterval : InducesDegreeInterval G u d q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hu hxU) hxT
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ t)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact hasBoundedSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_unionDegree_and_externalDegree
    (G := G) (hks := hku) (ht := ht) (htr := htr) (hst := huT)
    (d := d) (q := q) (e := e) hinterval hsmall hext

lemma hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {q e : ℕ} (hq : u.card ≤ q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine
    hasBoundedSingleControlExactWitnessOfCard_of_degreeInterval_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
      (G := G) (hku := hku) (hu := hu) (ht := ht) (htr := htr) (hst := hst) (d := 0) ?_
      hdeg hdrop hext
  intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simpa [Nat.zero_add] using
    lt_of_lt_of_le (by simpa using (SimpleGraph.degree_lt_card_verts (G := inducedOn G u) v)) hq

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q) (htq : t.card < q)
    (hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  by_cases huNonempty : u.Nonempty
  · obtain ⟨v0, hv0⟩ := huNonempty
    set e : ℕ := (G.neighborFinset v0 ∩ t).card with he
    have he_lt : e < q := by
      rw [he]
      exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
    have hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e := by
      intro v
      have hv_lt : (G.neighborFinset v ∩ t).card < q := by
        exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
      have hmod : (G.neighborFinset v ∩ t).card ≡ e [MOD q] := by
        rw [he]
        exact hctrl v ⟨v0, hv0⟩
      rw [Nat.ModEq, Nat.mod_eq_of_lt hv_lt, Nat.mod_eq_of_lt he_lt] at hmod
      exact hmod
    exact
      hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
        (G := G) hku hu ht htr hst hq hdeg hdrop hext
  · have hu' : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp huNonempty
    subst hu'
    refine
      hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
        (G := G) (e := 0) hku hu ht htr hst hq hdeg hdrop ?_
    intro v
    exact False.elim (by simpa using v.2)

theorem hasSingleControlModularWitnessOfCard_iff_hasSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlModularWitnessOfCard G k ↔
      HasSingleControlModularBucketingWitnessOfCard G k := by
  constructor
  · exact hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
  · exact hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G

theorem hasBoundedSingleControlModularWitnessOfCard_iff_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedSingleControlModularWitnessOfCard G k r ↔
      HasBoundedSingleControlModularBucketingWitnessOfCard G k r := by
  constructor
  · exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
  · exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard G

lemma hasModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlModularBucketingWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
    (hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G hbuck)

lemma hasModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
      G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlModularBucketingWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasSingleControlModularWitnessOfCard G
    (hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
      G hbuck)

lemma hasSingleControlExactWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G k r) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, _htr, hst, D, e, hdeg, hext⟩
  exact ⟨s, t, hks, ht, hst, D, e, hdeg, hext⟩

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
    (hasSingleControlExactWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G hsingle)

lemma hasSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlBucketingWitnessOfCard G k r) :
    HasSingleControlBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, _htr, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  exact ⟨u, s, t, hku, hus, ht, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩

lemma hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlBucketingWitnessOfCard G k) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
  have hsmall :
      ∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - eDrop := by
    exact constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact ⟨u, t, hku, ht, huT, D - eDrop, eCtrl, hsmall, hctrl⟩

lemma hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlBucketingWitnessOfCard G k r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, htr, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
  have hdropT : Disjoint (s \ u) t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxT
    exact (Finset.disjoint_left.mp hst) (Finset.mem_sdiff.mp hxDrop).1 hxT
  have huT : Disjoint u t := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxT
    exact (Finset.disjoint_left.mp hst) (hus hxU) hxT
  have hsmall :
      ∀ v : ↑(u : Set V),
        (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - eDrop := by
    exact constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hdeg hdrop
  exact ⟨u, t, hku, ht, htr, huT, D - eDrop, eCtrl, hsmall, hctrl⟩

lemma hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hkr : r < k)
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hu, ht, htr, hst, q, hq, hdeg, hdrop, hctrl⟩
  have htq : t.card < q := by
    exact lt_of_le_of_lt htr (lt_of_lt_of_le hkr (le_trans hku hq))
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
      (G := G) (u := u) (s := s) (t := t) (q := q) hku hu ht htr hst hq htq hdeg hdrop hctrl

lemma hasSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hkr : r < k)
    (hbuck : HasBoundedSingleControlModularBucketingWitnessOfCard G k r) :
    HasSingleControlExactWitnessOfCard G k := by
  exact hasSingleControlExactWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularBucketingWitnessOfCard
      G hkr hbuck)

lemma hasSingleControlBucketingWitnessOfCard_of_hasSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hsingle : HasSingleControlExactWitnessOfCard G k) :
    HasSingleControlBucketingWitnessOfCard G k := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, hst, D, eCtrl, hdeg, hctrl⟩
  refine ⟨s, s, t, hks, by intro x hx; exact hx, ht, hst, D, 0, eCtrl, ?_, ?_, hctrl⟩
  · intro v
    have hcast :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    exact hcast.trans (hdeg v)
  · intro v
    simp

lemma hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G k r) :
    HasBoundedSingleControlBucketingWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, htr, hst, D, eCtrl, hdeg, hctrl⟩
  refine ⟨s, s, t, hks, by intro x hx; exact hx, ht, htr, hst, D, 0, eCtrl, ?_, ?_, hctrl⟩
  · intro v
    have hcast :
        (inducedOn G (s ∪ ((s \ s) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ t)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [Finset.sdiff_self, Finset.union_assoc] using
        (inducedOn_degree_congr (G := G)
          (s := s ∪ ((s \ s) ∪ t))
          (t := s ∪ t)
          (h := by simp [Finset.sdiff_self, Finset.union_assoc])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    exact hcast.trans (hdeg v)
  · intro v
    simp

theorem hasSingleControlExactWitnessOfCard_iff_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasSingleControlExactWitnessOfCard G k ↔ HasSingleControlBucketingWitnessOfCard G k := by
  constructor
  · exact hasSingleControlBucketingWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
  · exact hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G

theorem hasBoundedSingleControlExactWitnessOfCard_iff_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) (k r : ℕ) :
    HasBoundedSingleControlExactWitnessOfCard G k r ↔
      HasBoundedSingleControlBucketingWitnessOfCard G k r := by
  constructor
  · exact hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
  · exact hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard G

lemma hasSingleControlModularWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlBucketingWitnessOfCard G k) :
    HasSingleControlModularWitnessOfCard G k := by
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlExactWitnessOfCard G
    (hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G hbuck)

lemma hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlBucketingWitnessOfCard G k r) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
      G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlBucketingWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
    (hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedSingleControlBucketingWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
      G hbuck)

lemma hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasControlBlockBucketingWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, blocks, hnonempty, hsep, D, 0, ?_, ?_, hext⟩
  · intro v
    have hcast :
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
    exact hcast.trans (hdeg v)
  · intro v
    simp

lemma hasControlBlockBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasSingleControlBucketingWitnessOfCard G k) :
    HasControlBlockBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, t, hku, hus, ht, hst, D, eDrop, eCtrl, hdeg, hdrop, hctrl⟩
  refine ⟨u, s, hku, hus, [(t, eCtrl)], ?_, ?_, D, eDrop, ?_, hdrop, ?_⟩
  · simpa [NonemptyControlBlockUnion, controlBlockUnion] using ht
  · simp [ControlBlocksSeparated, controlBlockUnion, hst]
  · intro v
    have hcast :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion [(t, eCtrl)]))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa [controlBlockUnion_singleton, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion [(t, eCtrl)]))
          (t := u ∪ ((s \ u) ∪ t))
          (h := by
            simp [controlBlockUnion_singleton, Finset.union_assoc, Finset.union_left_comm,
              Finset.union_comm])
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    exact hcast.trans (hdeg v)
  · simpa [HasConstantExternalBlockDegrees] using And.intro hctrl True.intro

lemma hasControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockBucketingWitnessOfCard G k r) :
    HasControlBlockBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, blocks, _hlen, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩
  exact ⟨u, s, hku, hus, blocks, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩

lemma hasControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, q, hq, blocks, _hlen, hnonempty, hsep, hdeg, hdrop, hext⟩
  exact ⟨u, s, hku, hus, q, hq, blocks, hnonempty, hsep, hdeg, hdrop, hext⟩

lemma hasControlBlockModularBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hexact : HasExactControlBlockWitnessOfCard G k) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  rcases hexact with ⟨s, hks, blocks, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, s.card, le_rfl, blocks, hnonempty, hsep, ?_, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s s.card hext⟩
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
    simpa [hcastv, hcastw, hdeg v, hdeg w] using
      (Nat.ModEq.refl D : D ≡ D [MOD s.card])
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD s.card])

lemma hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ} (hexact : HasBoundedExactControlBlockWitnessOfCard G k r) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  classical
  rcases hexact with ⟨s, hks, blocks, hlen, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, s.card, le_rfl, blocks, hlen, hnonempty, hsep, ?_, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G s s.card hext⟩
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
    simpa [hcastv, hcastw, hdeg v, hdeg w] using
      (Nat.ModEq.refl D : D ≡ D [MOD s.card])
  · intro v w
    simpa [Finset.sdiff_self] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD s.card])

lemma hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockBucketingWitnessOfCard G k) :
    HasControlBlockModularBucketingWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, blocks, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩
  refine ⟨u, s, hku, hus, u.card, le_rfl, blocks, hnonempty, hsep, ?_, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G u u.card hext⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD u.card])
  · intro v w
    simpa [hdrop v, hdrop w] using (Nat.ModEq.refl eDrop : eDrop ≡ eDrop [MOD u.card])

lemma hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ} (hbuck : HasBoundedControlBlockBucketingWitnessOfCard G k r) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, blocks, hlen, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩
  have hlen' : blocks.length ≤ r := by
    have hsucc : blocks.length ≤ blocks.length + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.le_succ blocks.length
    exact le_trans hsucc hlen
  refine ⟨u, s, hku, hus, u.card, le_rfl, blocks, hlen', hnonempty, hsep, ?_, ?_,
    hasConstantModExternalBlockDegrees_of_hasConstantExternalBlockDegrees G u u.card hext⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D : D ≡ D [MOD u.card])
  · intro v w
    simpa [hdrop v, hdrop w] using (Nat.ModEq.refl eDrop : eDrop ≡ eDrop [MOD u.card])

lemma hasNonemptyControlBlockModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockModularBucketingWitnessOfCard G k) :
    HasNonemptyControlBlockModularWitnessOfCard G k := by
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
  exact ⟨u, hku, q, hq, blocks, hnonempty, hsepU, hsmall, hext⟩

lemma hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasBoundedNonemptyControlBlockModularWitnessOfCard G k r := by
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
  exact ⟨u, hku, q, hq, blocks, hlen, hnonempty, hsepU, hsmall, hext⟩

lemma hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockModularBucketingWitnessOfCard G k) :
    HasControlBlockWitnessOfCard G k := by
  exact hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hasNonemptyControlBlockModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard
      G hbuck)

lemma hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasControlBlockWitnessOfCard G k := by
  exact hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hasControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
      G hbuck)

lemma hasModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockModularBucketingWitnessOfCard G k) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G hbuck)

lemma hasModularWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasModularWitnessOfCard G k := by
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockModularBucketingWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockModularBucketingWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G
    (hasControlBlockWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G hbuck)

lemma hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockBucketingWitnessOfCard G k) :
    HasExactControlBlockWitnessOfCard G k := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, blocks, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩
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
  have hsepU : ControlBlocksSeparated u blocks :=
    controlBlocksSeparated_mono hus hsep
  have hnonempty' : NonemptyControlBlockUnion ((s \ u, eDrop) :: blocks) := by
    unfold NonemptyControlBlockUnion
    rw [controlBlockUnion]
    exact lt_of_lt_of_le hnonempty (Finset.card_le_card (Finset.subset_union_right))
  have hext' : HasConstantExternalBlockDegrees G u ((s \ u, eDrop) :: blocks) := by
    exact ⟨hdrop, hext⟩
  have hsep' : ControlBlocksSeparated u ((s \ u, eDrop) :: blocks) := by
    exact ⟨huDrop, hdropBlocks, hsepU⟩
  refine ⟨u, hku, ((s \ u, eDrop) :: blocks), hnonempty', hsep', D, ?_, hext'⟩
  simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hdeg

lemma hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockBucketingWitnessOfCard G k r) :
    HasBoundedExactControlBlockWitnessOfCard G k r := by
  classical
  rcases hbuck with ⟨u, s, hku, hus, blocks, hlen, hnonempty, hsep, D, eDrop, hdeg, hdrop, hext⟩
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
  have hsepU : ControlBlocksSeparated u blocks :=
    controlBlocksSeparated_mono hus hsep
  have hnonempty' : NonemptyControlBlockUnion ((s \ u, eDrop) :: blocks) := by
    unfold NonemptyControlBlockUnion
    rw [controlBlockUnion]
    exact lt_of_lt_of_le hnonempty (Finset.card_le_card (Finset.subset_union_right))
  have hext' : HasConstantExternalBlockDegrees G u ((s \ u, eDrop) :: blocks) := by
    exact ⟨hdrop, hext⟩
  have hsep' : ControlBlocksSeparated u ((s \ u, eDrop) :: blocks) := by
    exact ⟨huDrop, hdropBlocks, hsepU⟩
  refine ⟨u, hku, ((s \ u, eDrop) :: blocks), hlen, hnonempty', hsep', D, ?_, hext'⟩
  simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hdeg

lemma hasRegularInducedSubgraphOfCard_of_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k : ℕ} (hbuck : HasControlBlockBucketingWitnessOfCard G k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G hbuck)

lemma hasRegularInducedSubgraphOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hbuck : HasBoundedControlBlockBucketingWitnessOfCard G k r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact hasRegularInducedSubgraphOfCard_of_hasExactControlBlockWitnessOfCard G
    (hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
      (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
        G hbuck))

theorem hasExactControlBlockWitnessOfCard_iff_hasControlBlockBucketingWitnessOfCard
    (G : SimpleGraph V) (k : ℕ) :
    HasExactControlBlockWitnessOfCard G k ↔ HasControlBlockBucketingWitnessOfCard G k := by
  constructor
  · exact hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G
  · exact hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G

lemma hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard_succ
    (G : SimpleGraph V) {k r : ℕ}
    (hexact : HasBoundedExactControlBlockWitnessOfCard G k r) :
    HasBoundedControlBlockBucketingWitnessOfCard G k (r + 1) := by
  classical
  rcases hexact with ⟨s, hks, blocks, hlen, hnonempty, hsep, D, hdeg, hext⟩
  refine ⟨s, s, hks, by intro x hx; exact hx, blocks, ?_, hnonempty, hsep, D, 0, ?_, ?_, hext⟩
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.succ_le_succ hlen
  · intro v
    have hcast :
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
    exact hcast.trans (hdeg v)
  · intro v
    simp

end FiniteGraph

end RegularInducedSubgraph
