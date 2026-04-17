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

private lemma degree_union_eq_degree_add_external
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

private lemma inducedOn_degree_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (h : s = t)
    {v : V} (hs : v ∈ s) (ht : v ∈ t) :
    (inducedOn G s).degree ⟨v, hs⟩ = (inducedOn G t).degree ⟨v, ht⟩ := by
  subst h
  cases Subsingleton.elim hs ht
  rfl

private def SameControlBlockSupports : List (Finset V × ℕ) → List (Finset V × ℕ) → Prop
  | [], [] => True
  | b :: bs, b' :: bs' => b.1 = b'.1 ∧ SameControlBlockSupports bs bs'
  | _, _ => False

private lemma controlBlockUnion_eq_of_sameControlBlockSupports :
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

private lemma controlBlocksSeparated_mono {s t : Finset V} (hts : t ⊆ s) :
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

private lemma disjoint_controlBlockUnion_of_controlBlocksSeparated {s : Finset V} :
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
  refine ⟨s, controlBlockUnion blocks, hks, hnonempty,
    disjoint_controlBlockUnion_of_controlBlocksSeparated hsep, D, controlBlockDegreeSum blocks, ?_, ?_⟩
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
  refine ⟨s, t, hks, ht, hst, s.card, le_rfl, ?_, ?_⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D)
  · intro v w
    simpa [hext v, hext w] using (Nat.ModEq.refl e)

lemma hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard
    (G : SimpleGraph V) {k r : ℕ}
    (hsingle : HasBoundedSingleControlExactWitnessOfCard G k r) :
    HasBoundedSingleControlModularWitnessOfCard G k r := by
  classical
  rcases hsingle with ⟨s, t, hks, ht, htr, hst, D, e, hdeg, hext⟩
  refine ⟨s, t, hks, ht, htr, hst, s.card, le_rfl, ?_, ?_⟩
  · intro v w
    simpa [hdeg v, hdeg w] using (Nat.ModEq.refl D)
  · intro v w
    simpa [hext v, hext w] using (Nat.ModEq.refl e)

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
  refine ⟨s, controlBlockUnion blocks, hks, hnonempty,
    disjoint_controlBlockUnion_of_controlBlocksSeparated hsep, q, hq, ?_, ?_⟩
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

lemma exists_large_subset_with_constant_hostDegree_of_constant_unionDegree_and_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {k D : ℕ}
    (hsize : (t.card + 1) * k ≤ s.card) (hst : Disjoint s t)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∃ d : ℕ, ∀ v : ↑(u : Set V), (inducedOn G s).degree ⟨v.1, hu v.2⟩ = d := by
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
    have huDrop : Disjoint u (s \ u) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxU hxDrop
      exact (Finset.mem_sdiff.mp hxDrop).2 hxU
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
  refine ⟨u, hus, hku, D - e, ?_⟩
  intro v
  exact hconst v

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
  refine ⟨u, hu, hku, D - controlBlockDegreeSum blocks', ?_⟩
  intro v
  exact hconst v

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

lemma exists_large_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V}
    {blocks : List (Finset V × ℕ)} {q k : ℕ}
    (hq : 0 < q) (hsize : q ^ blocks.length * (q * k) ≤ s.card)
    (hsep : ControlBlocksSeparated s blocks) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
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
  exact ⟨u, hu, hku, hconst⟩

lemma exists_large_mod_pair_of_mul_le_card
    {α : Type*} [DecidableEq α] (s : Finset α) {q n : ℕ} (hq : 0 < q)
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
    {α : Type*} [DecidableEq α] (s : Finset α) {q n : ℕ} (hq : 0 < q)
    (f g : α → Fin q) (hn : q * q * n ≤ s.card) :
    ∃ u : Finset α, u ⊆ s ∧ n ≤ u.card ∧
      ∃ a b : Fin q, ∀ x ∈ u, f x = a ∧ g x = b := by
  classical
  obtain ⟨a, b, hab⟩ := exists_large_mod_pair_of_mul_le_card s hq f g hn
  refine ⟨s.filter fun x => f x = a ∧ g x = b, Finset.filter_subset _ _, hab, a, b, ?_⟩
  intro x hx
  exact Finset.mem_filter.mp hx |>.2

lemma exists_large_subset_with_modEq_hostDegree_of_unionDegree_and_externalDegree_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q k : ℕ}
    (hq : 0 < q) (hsize : q * q * k ≤ s.card) (hst : Disjoint s t) :
    ∃ u : Finset V, ∃ hu : u ⊆ s, k ≤ u.card ∧
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
  have hsep : ControlBlocksSeparated s [(t, 0)] := by
    simp [ControlBlocksSeparated, controlBlockUnion, hst]
  simpa [controlBlockUnion, pow_one, Nat.mul_assoc] using
    (exists_large_subset_with_modEq_hostDegree_of_blockUnionDegree_and_externalBlockDegrees_card_bound
      (G := G) (s := s) (blocks := [(t, 0)]) (q := q) (k := k) hq
      (by simpa [pow_one, Nat.mul_assoc] using hsize) hsep)

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

section Threshold

/--
Discrete modular form of the power-sequence target: on the subsequence `b^k`, every linear-size
target `M * k` should eventually admit a modular witness.
-/
def EventualNatPowerModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasModularWitnessOfCard G (M * k)

/--
Stronger exact control-block target: on the subsequence `b^k`, every linear-size demand eventually
admits a nonempty exact control-block witness.
-/
def EventualNatPowerExactControlBlockDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasExactControlBlockWitnessOfCard G (M * k)

/--
Bounded exact control-block target: the same nonempty exact witness exists using at most `r`
control blocks.
-/
def EventualNatPowerBoundedExactControlBlockDomination (b r : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedExactControlBlockWitnessOfCard G (M * k) r

/--
Single-control exact target: on graphs with `b^k` vertices, every linear-size demand eventually
admits one nonempty control set that freezes both ambient and external degrees.
-/
def EventualNatPowerSingleControlExactDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlExactWitnessOfCard G (M * k)

/--
Single-control exact target with an explicit control-size budget `u k` at scale `k`.
-/
def EventualNatPowerBoundedSingleControlExactDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlExactWitnessOfCard G (M * k) (u k)

/--
Single-control modular target: on graphs with `b^k` vertices, every linear-size demand eventually
admits one nonempty control set that freezes both ambient and external degrees modulo a modulus at
least the bucket size.
-/
def EventualNatPowerSingleControlModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlModularWitnessOfCard G (M * k)

/--
Single-control modular target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlModularDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlModularWitnessOfCard G (M * k) (u k)

/--
Single-control modular bucketing target: a large bucket survives inside a host set while the ambient
degree and both relevant external residues are frozen modulo a modulus at least the bucket size.
-/
def EventualNatPowerSingleControlModularBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlModularBucketingWitnessOfCard G (M * k)

/--
Single-control modular bucketing target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlModularBucketingDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedSingleControlModularBucketingWitnessOfCard G (M * k) (u k)

/--
Single-control bucketing target: a large bucket survives inside a host set while the host ambient
degree and both relevant external degrees are frozen.
-/
def EventualNatPowerSingleControlBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlBucketingWitnessOfCard G (M * k)

/--
Single-control bucketing target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlBucketingDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlBucketingWitnessOfCard G (M * k) (u k)

/--
Multiblock bucketing target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a large bucket together with a nonempty separated control-block family whose ambient and
external degree data are frozen on that bucket.
-/
def EventualNatPowerControlBlockBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockBucketingWitnessOfCard G (M * k)

/--
Bounded multiblock bucketing target: the final exact control-block witness extracted from the
bucketing data uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockBucketingDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedControlBlockBucketingWitnessOfCard G (M * k) (r k)

/--
Multiblock modular bucketing target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a large bucket together with a nonempty separated control-block family whose
ambient degree, dropped-part residue, and control-block residues are all frozen modulo a modulus at
least the bucket size.
-/
def EventualNatPowerControlBlockModularBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockModularBucketingWitnessOfCard G (M * k)

/--
Bounded multiblock modular bucketing target: the modular bucketing data uses at most `r k`
control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockModularBucketingDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedControlBlockModularBucketingWitnessOfCard G (M * k) (r k)

/--
Single-control cascade target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a fixed-control cascade whose terminal bucket has the required size.
-/
def EventualNatPowerSingleControlCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlCascadeWitnessOfCard G (M * k)

/--
Bounded single-control cascade target: the final exact control-block witness extracted from the
cascade uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedSingleControlCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlCascadeWitnessOfCard G (M * k) (r k)

/--
Multiblock cascade target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a fixed separated control-block family together with a cascade whose terminal bucket has the
required size.
-/
def EventualNatPowerControlBlockCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockCascadeWitnessOfCard G (M * k)

/--
Bounded multiblock cascade target: the final exact control-block witness extracted from the cascade
uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedControlBlockCascadeWitnessOfCard G (M * k) (r k)

/--
Modular multiblock cascade target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a fixed-modulus separated control-block cascade whose terminal bucket already fits
under that modulus.
-/
def EventualNatPowerControlBlockModularCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockModularCascadeWitnessOfCard G (M * k)

/--
Bounded modular multiblock cascade target: after all drops are packaged, the cascade uses at most
`r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockModularCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedControlBlockModularCascadeWitnessOfCard G (M * k) (r k)

/--
Sharper power-sequence target: on the subsequence `b^k`, every linear-size demand eventually admits
a modular witness whose modulus already beats the maximum induced degree.
-/
def EventualNatPowerLowDegreeModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasLowDegreeModularWitnessOfCard G (M * k)

/--
Power-sequence control-block target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a control-block witness.
-/
def EventualNatPowerControlBlockDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockWitnessOfCard G (M * k)

/--
Power-sequence genuine control-block target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a modular control-block witness with a genuinely present separated control-block
family.
-/
def EventualNatPowerNonemptyControlBlockModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasNonemptyControlBlockModularWitnessOfCard G (M * k)

/--
Bounded genuine control-block target with an explicit control-block budget `r k`.
-/
def EventualNatPowerBoundedNonemptyControlBlockModularDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedNonemptyControlBlockModularWitnessOfCard G (M * k) (r k)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerExactControlBlockDomination
    {b r : ℕ}
    (hctrl : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ}
    (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ}
    (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    (eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ}
    (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerControlBlockBucketingDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockBucketingDomination

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} :
    EventualNatPowerControlBlockBucketingDomination b ↔
      EventualNatPowerControlBlockCascadeDomination b := by
  constructor
  · exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockCascadeDomination
  · exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockBucketingDomination

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerBoundedControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockModularCascadeDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockModularCascadeDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockModularCascadeDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerControlBlockModularBucketingDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  constructor
  · exact eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
  · exact eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination

theorem eventualNatPowerControlBlockDomination_implies_eventualNatPowerModularDomination {b : ℕ}
    (hctrl : EventualNatPowerControlBlockDomination b) :
    EventualNatPowerModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerControlBlockDomination b) : TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hctrl M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerExactControlBlockDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hexact : EventualNatPowerExactControlBlockDomination b) : TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockDomination
      hexact)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_targetStatement
    {b r : ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerBoundedExactControlBlockDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerExactControlBlockDomination
      hctrl)

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  have := hK hk G
  exact hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard G this)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerBoundedControlBlockBucketingDomination_succ
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockBucketingDomination b (fun k => r k + 1) := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard_succ
    G
    (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    (eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
      hcascade)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerControlBlockCascadeDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerControlBlockBucketingDomination b := by
  rw [eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination,
    eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerExactControlBlockDomination]

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerControlBlockCascadeDomination b := by
  rw [eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination,
    eventualNatPowerControlBlockCascadeDomination_iff_eventualNatPowerExactControlBlockDomination]

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerControlBlockCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerNonemptyControlBlockModularDomination b ↔
      EventualNatPowerControlBlockModularBucketingDomination b := by
  constructor
  · exact eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
  · exact eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination

theorem eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerNonemptyControlBlockModularDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  rw [eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination,
    eventualNatPowerControlBlockModularBucketingDomination_iff_eventualNatPowerControlBlockModularCascadeDomination]

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_iff_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ} :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b r ↔
      EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  constructor
  · exact eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
  · exact eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerModularDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hmod : EventualNatPowerModularDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hmod M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockDomination_iff_eventualNatPowerModularDomination
    {b : ℕ} :
    EventualNatPowerControlBlockDomination b ↔ EventualNatPowerModularDomination b := by
  constructor
  · exact eventualNatPowerControlBlockDomination_implies_eventualNatPowerModularDomination
  · exact eventualNatPowerModularDomination_implies_eventualNatPowerControlBlockDomination

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) : TargetStatement := by
  exact eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
      hbuck)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockDomination
      hctrl)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) : TargetStatement := by
  exact eventualNatPowerNonemptyControlBlockModularDomination_implies_targetStatement hb
    (eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
      hctrl)

theorem eventualNatPowerControlBlockModularCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerControlBlockModularCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerControlBlockModularCascadeDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerBoundedSingleControlModularDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerNonemptyControlBlockModularDomination b := by
  constructor
  · exact eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
  · exact eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerSingleControlModularDomination

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerControlBlockModularBucketingDomination b := by
  rw [eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination,
    eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination]

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  rw [eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination,
    eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination]

theorem eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlModularBucketingDomination b u) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ} :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔
      EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  constructor
  · exact eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
  · intro hbuck
    intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard G
      (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerSingleControlModularBucketingDomination b := by
  constructor
  · exact eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
  · intro hbuck
    intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G
      (hK hk G)

theorem eventualNatPowerSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlModularBucketingDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlBucketingDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlBucketingWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlExactDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerSingleControlBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerSingleControlBucketingDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
  · exact eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination
    {b : ℕ} {u : ℕ → ℕ} :
    EventualNatPowerBoundedSingleControlExactDomination b u ↔
      EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  constructor
  · exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlBucketingDomination
  · exact eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlCascadeDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlCascadeWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerSingleControlCascadeDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
  · exact eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerSingleControlBucketingDomination_iff_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlBucketingDomination b ↔
      EventualNatPowerSingleControlCascadeDomination b := by
  constructor
  · intro hbuck
    exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
      (eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
        hbuck)
  · intro hcascade
    exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
      (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination
        hcascade)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlModularDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hsingle : EventualNatPowerSingleControlExactDomination b) :
    TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hsingle : EventualNatPowerSingleControlModularDomination b) :
    TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlModularDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerSingleControlModularDomination
      hsingle)

theorem eventualNatPowerSingleControlModularBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerSingleControlModularBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerSingleControlModularDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedSingleControlModularBucketingDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
      hsingle)

theorem eventualNatPowerSingleControlBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) : TargetStatement := by
  exact eventualNatPowerBoundedSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination
      hbuck)

theorem eventualNatPowerControlBlockBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
      hbuck)

theorem eventualNatPowerLowDegreeModularDomination_implies_eventualNatPowerDomination {b : ℕ}
    (hmod : EventualNatPowerLowDegreeModularDomination b) :
    EventualNatPowerDomination b := by
  intro M
  rcases hmod M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  rw [le_F_iff]
  intro G
  exact hasRegularInducedSubgraphOfCard_of_hasLowDegreeModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerLowDegreeModularDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hmod : EventualNatPowerLowDegreeModularDomination b) : TargetStatement := by
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1
    (eventualNatPowerLowDegreeModularDomination_implies_eventualNatPowerDomination hmod)

theorem eventualNatPowerModularDomination_iff_eventualNatPowerDomination {b : ℕ} :
    EventualNatPowerModularDomination b ↔ EventualNatPowerDomination b := by
  constructor
  · intro hmod
    intro M
    rcases hmod M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact (hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard G (M * k)).mp (hK hk G)
  · intro hpow
    intro M
    rcases hpow M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact (hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard G (M * k)).mpr
      ((le_F_iff.mp (hK hk)) G)

theorem eventualNatPowerControlBlockDomination_iff_eventualNatPowerDomination {b : ℕ} :
    EventualNatPowerControlBlockDomination b ↔ EventualNatPowerDomination b := by
  rw [eventualNatPowerControlBlockDomination_iff_eventualNatPowerModularDomination,
    eventualNatPowerModularDomination_iff_eventualNatPowerDomination]

theorem eventualNatPowerControlBlockDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualNatPowerControlBlockDomination b ↔ TargetStatement := by
  rw [eventualNatPowerControlBlockDomination_iff_eventualNatPowerDomination]
  exact eventualNatPowerDomination_iff_targetStatement hb

theorem eventualNatPowerModularDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualNatPowerModularDomination b ↔ TargetStatement := by
  rw [eventualNatPowerModularDomination_iff_eventualNatPowerDomination]
  exact eventualNatPowerDomination_iff_targetStatement hb

theorem eventualNatPowerModularDomination_four_iff_targetStatement :
    EventualNatPowerModularDomination 4 ↔ TargetStatement := by
  simpa using eventualNatPowerModularDomination_iff_targetStatement (b := 4) (by decide : 1 < 4)

end Threshold

end RegularInducedSubgraph
