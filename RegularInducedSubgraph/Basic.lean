import Mathlib

namespace RegularInducedSubgraph

section RegularityTransport

variable {V : Type*} [Fintype V]

private lemma regularOfEq {G H : SimpleGraph V} [hdecG : DecidableRel G.Adj]
    [hdecH : DecidableRel H.Adj] {d : ℕ} (hGH : G = H) (hreg : G.IsRegularOfDegree d) :
    H.IsRegularOfDegree d := by
  subst hGH
  cases Subsingleton.elim hdecG hdecH
  exact hreg

end RegularityTransport

section FiniteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph induced by a finite vertex set, viewed as a graph on the corresponding subtype. -/
abbrev inducedOn (G : SimpleGraph V) (s : Finset V) : SimpleGraph ↑(s : Set V) :=
  G.induce (s : Set V)

private lemma inducedOn_degree_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (h : s = t)
    {v : V} (hs : v ∈ s) (ht : v ∈ t) :
    (inducedOn G s).degree ⟨v, hs⟩ = (inducedOn G t).degree ⟨v, ht⟩ := by
  subst h
  cases Subsingleton.elim hs ht
  rfl

/-- A finite set of vertices induces a regular graph of degree `d`. -/
def InducesRegularOfDegree (G : SimpleGraph V) (s : Finset V) (d : ℕ) : Prop := by
  classical
  exact (inducedOn G s).IsRegularOfDegree d

/-- `G` contains a regular induced subgraph on at least `k` vertices. -/
def HasRegularInducedSubgraphOfCard (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ ∃ d : ℕ, InducesRegularOfDegree G s d

lemma inducesRegularOfDegree_empty (G : SimpleGraph V) :
    InducesRegularOfDegree G ∅ 0 := by
  classical
  change (inducedOn G ∅).IsRegularOfDegree 0
  intro v
  cases v.2

lemma inducesRegularOfDegree_of_isClique (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsClique (s : Set V)) : InducesRegularOfDegree G s (s.card - 1) := by
  classical
  rw [InducesRegularOfDegree]
  rw [SimpleGraph.isClique_iff_induce_eq] at hs
  have hs' : inducedOn G s = (⊤ : SimpleGraph ↑(s : Set V)) := by
    simpa [inducedOn] using hs
  exact regularOfEq (G := (⊤ : SimpleGraph ↑(s : Set V))) (H := inducedOn G s) hs'.symm <|
    by simpa using (SimpleGraph.IsRegularOfDegree.top (V := ↑(s : Set V)))

lemma inducesRegularOfDegree_of_induce_eq_bot (G : SimpleGraph V) (s : Finset V)
    (hs : G.induce (s : Set V) = ⊥) : InducesRegularOfDegree G s 0 := by
  classical
  rw [InducesRegularOfDegree]
  have hs' : inducedOn G s = (⊥ : SimpleGraph ↑(s : Set V)) := by
    simpa [inducedOn] using hs
  exact regularOfEq (G := (⊥ : SimpleGraph ↑(s : Set V))) (H := inducedOn G s) hs'.symm <|
    by
      intro v
      simp

lemma inducesRegularOfDegree_of_isIndepSet (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsIndepSet (s : Set V)) : InducesRegularOfDegree G s 0 := by
  classical
  rw [InducesRegularOfDegree]
  have hs' : inducedOn G s = (⊥ : SimpleGraph ↑(s : Set V)) := by
    ext u v
    constructor
    · intro huv
      exfalso
      exact hs u.2 v.2 (Subtype.coe_injective.ne huv.ne) huv
    · intro huv
      cases huv
  exact regularOfEq (G := (⊥ : SimpleGraph ↑(s : Set V))) (H := inducedOn G s) hs'.symm <| by
    intro v
    simp

lemma hasRegularInducedSubgraphOfCard_of_isClique (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsClique (s : Set V)) : HasRegularInducedSubgraphOfCard G s.card := by
  exact ⟨s, le_rfl, s.card - 1, inducesRegularOfDegree_of_isClique G s hs⟩

lemma hasRegularInducedSubgraphOfCard_of_induce_eq_bot (G : SimpleGraph V) (s : Finset V)
    (hs : G.induce (s : Set V) = ⊥) : HasRegularInducedSubgraphOfCard G s.card := by
  exact ⟨s, le_rfl, 0, inducesRegularOfDegree_of_induce_eq_bot G s hs⟩

lemma hasRegularInducedSubgraphOfCard_of_isIndepSet (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsIndepSet (s : Set V)) : HasRegularInducedSubgraphOfCard G s.card := by
  exact ⟨s, le_rfl, 0, inducesRegularOfDegree_of_isIndepSet G s hs⟩

lemma inducesRegularOfDegree_singleton (G : SimpleGraph V) (v : V) :
    InducesRegularOfDegree G ({v} : Finset V) 0 := by
  classical
  have hs : G.IsClique ((({v} : Finset V) : Set V)) := by
    simp
  simpa using inducesRegularOfDegree_of_isClique (G := G) ({v} : Finset V) hs

lemma hasRegularInducedSubgraphOfCard_zero (G : SimpleGraph V) :
    HasRegularInducedSubgraphOfCard G 0 := by
  refine ⟨∅, Nat.zero_le _, 0, inducesRegularOfDegree_empty G⟩

lemma hasRegularInducedSubgraphOfCard_one (G : SimpleGraph V) [Nonempty V] :
    HasRegularInducedSubgraphOfCard G 1 := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨{v}, by simp, 0, inducesRegularOfDegree_singleton G v⟩

private lemma inducedOn_degree_lt_card
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (v : ↑(s : Set V)) :
    (inducedOn G s).degree v < s.card := by
  classical
  have hproper :
      (inducedOn G s).neighborFinset v ⊂ (Finset.univ : Finset ↑(s : Set V)) := by
    refine ⟨by intro x _; simp, ?_⟩
    intro hsubset
    have hv : v ∈ (inducedOn G s).neighborFinset v := hsubset (by simp)
    exact
      (SimpleGraph.irrefl (inducedOn G s))
        ((SimpleGraph.mem_neighborFinset (inducedOn G s) v v).mp hv)
  have hlt := Finset.card_lt_card hproper
  rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_univ] at hlt
  have hcard : Fintype.card ↑(s : Set V) = s.card := by
    exact Fintype.card_ofFinset s (by simp)
  simpa [hcard] using hlt

/--
Exact-marker congruence closure: if `s` has size `q` and every internal degree in `G[s]` has the
same residue `r` modulo `q`, then all internal degrees are exactly `r`, so `G[s]` is regular.
-/
lemma inducesRegularOfDegree_of_card_eq_and_degree_modEq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} {q r : ℕ}
    (hcard : s.card = q)
    (hmod : ∀ v : ↑(s : Set V), (inducedOn G s).degree v % q = r) :
    InducesRegularOfDegree G s r := by
  classical
  rw [InducesRegularOfDegree]
  intro v
  have hlt : (inducedOn G s).degree v < q := by
    simpa [hcard] using inducedOn_degree_lt_card (G := G) (s := s) v
  have hv := hmod v
  rw [Nat.mod_eq_of_lt hlt] at hv
  convert hv

/--
Exact-marker form of the previous lemma: a `q`-vertex set whose internal degrees are congruent
modulo `q` already supplies a regular induced subgraph of cardinality `q`.
-/
lemma hasRegularInducedSubgraphOfCard_of_card_eq_and_degree_modEq
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} {q r : ℕ}
    (hcard : s.card = q)
    (hmod : ∀ v : ↑(s : Set V), (inducedOn G s).degree v % q = r) :
    HasRegularInducedSubgraphOfCard G q := by
  exact ⟨s, by omega, r,
    inducesRegularOfDegree_of_card_eq_and_degree_modEq G hcard hmod⟩

private lemma degree_inducedOn_eq_card_neighborFinset_inter
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
          exact degree_inducedOn_eq_card_neighborFinset_inter
            (G := G) (s := s ∪ t) ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
    _ = (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card := by
          exact card_neighborFinset_inter_union (G := G) hst v
    _ = (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
          rw [degree_inducedOn_eq_card_neighborFinset_inter (G := G) (s := s) (v := v)]

/--
If every vertex of `s` has the same degree inside the ambient induced graph on `s ∪ t` and the
same number of neighbors in the disjoint control set `t`, then the induced graph on `s` is
regular.
-/
lemma inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} (hst : Disjoint s t) {D e : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    InducesRegularOfDegree G s (D - e) := by
  classical
  rw [InducesRegularOfDegree]
  intro v
  have hdeg_union :
      (G.neighborFinset v ∩ (s ∪ t)).card = D := by
    exact
      (degree_inducedOn_eq_card_neighborFinset_inter (G := G) (s := s ∪ t)
        ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩).symm.trans (hdeg v)
  have hsplit :
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
  have hcard :
      (G.neighborFinset v ∩ s).card = D - e := by
    have hsum :
        (G.neighborFinset v ∩ s).card + e = D := by
      calc
        (G.neighborFinset v ∩ s).card + e
            = (G.neighborFinset v ∩ s).card + (G.neighborFinset v ∩ t).card := by
                rw [← hext v]
        _ = (G.neighborFinset v ∩ (s ∪ t)).card := by
              rw [← hsplit]
        _ = D := hdeg_union
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  set N : Finset ↑(s : Set V) :=
    @SimpleGraph.neighborFinset _ (inducedOn G s) v
      ((fun v => (inducedOn G s).neighborSetFintype v) v) with hN
  have hmap_s :
      N.map (Function.Embedding.subtype (· ∈ (s : Set V))) =
        G.neighborFinset v ∩ s := by
    ext x
    simp [hN, inducedOn]
  have hNcard : N.card = D - e := by
    calc
      N.card = (N.map (Function.Embedding.subtype (· ∈ (s : Set V)))).card := by
        rw [Finset.card_map]
      _ = (G.neighborFinset v ∩ s).card := by rw [hmap_s]
      _ = D - e := hcard
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  simpa [hN] using hNcard

lemma hasRegularInducedSubgraphOfCard_of_constant_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t : Finset V} (hks : k ≤ s.card) (hst : Disjoint s t)
    {D e : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasRegularInducedSubgraphOfCard G k := by
  exact ⟨s, hks, D - e,
    inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree G hst hdeg hext⟩

/--
Two-block version of the control-set transport lemma: if the ambient degree on `s ∪ t₁ ∪ t₂` is
constant on `s`, and the degrees into each disjoint control block `t₁` and `t₂` are separately
constant on `s`, then the induced graph on `s` is regular.
-/
lemma inducesRegularOfDegree_of_constant_unionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t₁ t₂ : Finset V}
    (hst : Disjoint s (t₁ ∪ t₂)) (ht : Disjoint t₁ t₂) {D e₁ e₂ : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext₁ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₁).card = e₁)
    (hext₂ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₂).card = e₂) :
    InducesRegularOfDegree G s (D - (e₁ + e₂)) := by
  refine inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree G hst hdeg ?_
  intro v
  have hdisj :
      Disjoint (G.neighborFinset v ∩ t₁) (G.neighborFinset v ∩ t₂) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx₁ hx₂
    exact (Finset.disjoint_left.mp ht
      (Finset.mem_inter.mp hx₁).2 (Finset.mem_inter.mp hx₂).2)
  have hunion :
      G.neighborFinset v ∩ (t₁ ∪ t₂) =
        (G.neighborFinset v ∩ t₁) ∪ (G.neighborFinset v ∩ t₂) := by
    ext x
    simp [and_left_comm, and_assoc, and_or_left]
  calc
    (G.neighborFinset v ∩ (t₁ ∪ t₂)).card
        = ((G.neighborFinset v ∩ t₁) ∪ (G.neighborFinset v ∩ t₂)).card := by rw [hunion]
    _ = (G.neighborFinset v ∩ t₁).card + (G.neighborFinset v ∩ t₂).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = e₁ + e₂ := by rw [hext₁ v, hext₂ v]

lemma hasRegularInducedSubgraphOfCard_of_constant_unionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s t₁ t₂ : Finset V} (hks : k ≤ s.card) (hst : Disjoint s (t₁ ∪ t₂))
    (ht : Disjoint t₁ t₂) {D e₁ e₂ : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ (t₁ ∪ t₂))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext₁ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₁).card = e₁)
    (hext₂ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₂).card = e₂) :
    HasRegularInducedSubgraphOfCard G k := by
  exact ⟨s, hks, D - (e₁ + e₂),
    inducesRegularOfDegree_of_constant_unionDegree_and_two_externalDegrees
      G hst ht hdeg hext₁ hext₂⟩

/--
If the ambient degree on `s ∪ t ∪ u` is constant on `s` and the degree into the disjoint block `t`
is constant on `s`, then the ambient degree on `s ∪ u` is constant on `s`.
-/
lemma constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t u : Finset V}
    (hst : Disjoint s t) (htu : Disjoint t u) {D e : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ (t ∪ u))).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) :
    ∀ v : ↑(s : Set V),
      (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - e := by
  have hdisj : Disjoint (s ∪ u) t := by
    rw [Finset.disjoint_union_left]
    exact ⟨hst, htu.symm⟩
  intro v
  have hdeg_big :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card = D := by
    exact
      (degree_inducedOn_eq_card_neighborFinset_inter (G := G) (s := s ∪ (t ∪ u))
        ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩).symm.trans (hdeg v)
  have hsplit :
      (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card =
        (G.neighborFinset v ∩ (s ∪ u)).card + (G.neighborFinset v ∩ t).card := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (card_neighborFinset_inter_union (G := G) (s := s ∪ u) (t := t) hdisj v)
  have hsmall :
      (G.neighborFinset v ∩ (s ∪ u)).card = D - e := by
    have hsum : (G.neighborFinset v ∩ (s ∪ u)).card + e = D := by
      calc
        (G.neighborFinset v ∩ (s ∪ u)).card + e
            = (G.neighborFinset v ∩ (s ∪ u)).card + (G.neighborFinset v ∩ t).card := by
                rw [hext v]
        _ = (G.neighborFinset v ∩ (s ∪ (t ∪ u))).card := by
              rw [hsplit]
        _ = D := hdeg_big
    exact Nat.eq_sub_of_add_eq hsum
  calc
    (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
      = (G.neighborFinset v ∩ (s ∪ u)).card := by
          exact degree_inducedOn_eq_card_neighborFinset_inter
            (G := G) (s := s ∪ u) ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩
    _ = D - e := hsmall

/--
Two-block version of the previous transport lemma: if the ambient degree on
`s ∪ t₁ ∪ t₂ ∪ u` is constant on `s`, and the degrees into the disjoint control
blocks `t₁`, `t₂` are separately constant on `s`, then the ambient degree on
`s ∪ u` is constant on `s`.
-/
lemma constant_unionDegree_of_constant_extendedUnionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t₁ t₂ u : Finset V}
    (hst : Disjoint s (t₁ ∪ t₂)) (htu : Disjoint (t₁ ∪ t₂) u) (ht : Disjoint t₁ t₂)
    {D e₁ e₂ : ℕ}
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ ((t₁ ∪ t₂) ∪ u))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext₁ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₁).card = e₁)
    (hext₂ : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t₂).card = e₂) :
    ∀ v : ↑(s : Set V),
      (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - (e₁ + e₂) := by
  have hext :
      ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ (t₁ ∪ t₂)).card = e₁ + e₂ := by
    intro v
    have hdisj :
        Disjoint (G.neighborFinset v ∩ t₁) (G.neighborFinset v ∩ t₂) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx₁ hx₂
      exact (Finset.disjoint_left.mp ht
        (Finset.mem_inter.mp hx₁).2 (Finset.mem_inter.mp hx₂).2)
    have hunion :
        G.neighborFinset v ∩ (t₁ ∪ t₂) =
          (G.neighborFinset v ∩ t₁) ∪ (G.neighborFinset v ∩ t₂) := by
      ext x
      simp [and_left_comm, and_assoc, and_or_left]
    calc
      (G.neighborFinset v ∩ (t₁ ∪ t₂)).card
          = ((G.neighborFinset v ∩ t₁) ∪ (G.neighborFinset v ∩ t₂)).card := by rw [hunion]
      _ = (G.neighborFinset v ∩ t₁).card + (G.neighborFinset v ∩ t₂).card := by
            rw [Finset.card_union_of_disjoint hdisj]
      _ = e₁ + e₂ := by rw [hext₁ v, hext₂ v]
  exact
    constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
      (G := G) (s := s) (t := t₁ ∪ t₂) (u := u) hst htu
      (hdeg := hdeg) (hext := hext)

/-- Union of a list of control blocks. -/
def controlBlockUnion : List (Finset V × ℕ) → Finset V
  | [] => ∅
  | b :: bs => b.1 ∪ controlBlockUnion bs

@[simp] lemma controlBlockUnion_singleton (b : Finset V × ℕ) :
    controlBlockUnion [b] = b.1 := by
  simp [controlBlockUnion]

/-- Sum of the prescribed external degrees for a list of control blocks. -/
def controlBlockDegreeSum : List (Finset V × ℕ) → ℕ
  | [] => 0
  | b :: bs => b.2 + controlBlockDegreeSum bs

/--
`ControlBlocksSeparated s blocks` says each control block is disjoint from `s` and from the union of
all later control blocks.
-/
def ControlBlocksSeparated (s : Finset V) : List (Finset V × ℕ) → Prop
  | [] => True
  | b :: bs => Disjoint s b.1 ∧ Disjoint b.1 (controlBlockUnion bs) ∧ ControlBlocksSeparated s bs

/--
`HasConstantExternalBlockDegrees G s blocks` records that each control block carries the prescribed
constant external degree on `s`.
-/
def HasConstantExternalBlockDegrees (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    List (Finset V × ℕ) → Prop
  | [] => True
  | b :: bs =>
      (∀ v : ↑(s : Set V), (G.neighborFinset v ∩ b.1).card = b.2) ∧
        HasConstantExternalBlockDegrees G s bs

/--
If the ambient degree on `s ∪ controlBlockUnion blocks ∪ u` is constant on `s`, and the degree into
each separated control block is constant on `s`, then the ambient degree on `s ∪ u` is constant on
`s`.
-/
lemma constant_unionDegree_of_constant_extendedUnionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s tail : Finset V} :
    ∀ {blocks : List (Finset V × ℕ)} {D : ℕ},
      ControlBlocksSeparated s blocks →
      Disjoint (controlBlockUnion blocks) tail →
      (∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ (controlBlockUnion blocks ∪ tail))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) →
      HasConstantExternalBlockDegrees G s blocks →
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ tail)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          D - controlBlockDegreeSum blocks
  | [], D, _hsep, _hdisj, hdeg, _hext => by
      intro v
      have hcast :
          (inducedOn G (s ∪ tail)).degree ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
            (inducedOn G (s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
        simpa [controlBlockUnion] using
          (inducedOn_degree_congr (G := G)
            (s := s ∪ tail)
            (t := s ∪ (controlBlockUnion ([] : List (Finset V × ℕ)) ∪ tail))
            (h := by simp [controlBlockUnion])
            (hs := Finset.mem_union.mpr (Or.inl v.2))
            (ht := Finset.mem_union.mpr (Or.inl v.2)))
      simpa [controlBlockDegreeSum] using hcast.trans (hdeg v)
  | (b :: bs), D, hsep, hdisj, hdeg, hext => by
      rcases b with ⟨t, e⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      rcases hext with ⟨hextHead, hextTail⟩
      rw [controlBlockUnion, Finset.disjoint_union_left] at hdisj
      rcases hdisj with ⟨htTail, hdisjTail⟩
      have htuTail : Disjoint t (controlBlockUnion bs ∪ tail) := by
        rw [Finset.disjoint_union_right]
        exact ⟨htu, htTail⟩
      have hdegTail :
          ∀ v : ↑(s : Set V),
            (inducedOn G (s ∪ (controlBlockUnion bs ∪ tail))).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - e := by
        exact
          constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
            (G := G) (s := s) (t := t) (u := controlBlockUnion bs ∪ tail) hst htuTail
            (hdeg := by
              intro v
              have hcast :
                  (inducedOn G (s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))).degree
                      ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
                    (inducedOn G (s ∪ (controlBlockUnion ((t, e) :: bs) ∪ tail))).degree
                      ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
                simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                  Finset.union_comm] using
                  (inducedOn_degree_congr (G := G)
                    (s := s ∪ (t ∪ (controlBlockUnion bs ∪ tail)))
                    (t := s ∪ (controlBlockUnion ((t, e) :: bs) ∪ tail))
                    (h := by
                      simp [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                        Finset.union_comm])
                    (hs := Finset.mem_union.mpr (Or.inl v.2))
                    (ht := Finset.mem_union.mpr (Or.inl v.2)))
              exact hcast.trans (hdeg v))
            (hext := hextHead)
      intro v
      simpa [controlBlockDegreeSum, Nat.sub_sub] using
        (constant_unionDegree_of_constant_extendedUnionDegree_and_externalBlockDegrees
          (G := G) (s := s) (tail := tail) (blocks := bs) (D := D - e)
          hsepTail hdisjTail hdegTail hextTail v)

/--
Multiscale exact transport: if the ambient degree on `s` is constant inside the graph induced on `s`
plus a separated list of control blocks, and the degree into each block is separately constant on
`s`, then `G[s]` is regular.
-/
lemma inducesRegularOfDegree_of_constant_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} :
    ∀ {blocks : List (Finset V × ℕ)} {D : ℕ},
      ControlBlocksSeparated s blocks →
      (∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D) →
      HasConstantExternalBlockDegrees G s blocks →
      InducesRegularOfDegree G s (D - controlBlockDegreeSum blocks)
  | [], D, _hsep, hdeg, _hext => by
      simpa [controlBlockDegreeSum] using
        (inducesRegularOfDegree_of_constant_unionDegree_and_externalDegree
          (G := G) (s := s) (t := ∅) (D := D) (e := 0) (by simp)
          (hdeg := by
            intro v
            simpa [controlBlockUnion] using hdeg v)
          (hext := by
            intro v
            simp))
  | (b :: bs), D, hsep, hdeg, hext => by
      rcases b with ⟨t, e⟩
      rcases hsep with ⟨hst, htu, hsepTail⟩
      rcases hext with ⟨hextHead, hextTail⟩
      have hdegTail :
          ∀ v : ↑(s : Set V),
            (inducedOn G (s ∪ controlBlockUnion bs)).degree
                ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D - e := by
        exact
          constant_unionDegree_of_constant_extendedUnionDegree_and_externalDegree
            (G := G) (s := s) (t := t) (u := controlBlockUnion bs) hst htu
            (hdeg := by
              intro v
              simpa [controlBlockUnion, Finset.union_assoc, Finset.union_left_comm,
                Finset.union_comm] using hdeg v)
            (hext := hextHead)
      simpa [controlBlockDegreeSum, Nat.sub_sub] using
        (inducesRegularOfDegree_of_constant_unionDegree_and_externalBlockDegrees
          (G := G) (s := s) (blocks := bs) (D := D - e) hsepTail hdegTail hextTail)

lemma hasRegularInducedSubgraphOfCard_of_constant_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {s : Finset V} (hks : k ≤ s.card) {blocks : List (Finset V × ℕ)} {D : ℕ}
    (hsep : ControlBlocksSeparated s blocks)
    (hdeg :
      ∀ v : ↑(s : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ = D)
    (hext : HasConstantExternalBlockDegrees G s blocks) :
    HasRegularInducedSubgraphOfCard G k := by
  exact ⟨s, hks, D - controlBlockDegreeSum blocks,
    inducesRegularOfDegree_of_constant_unionDegree_and_externalBlockDegrees
      G hsep hdeg hext⟩

private noncomputable def finsetSubtypeMapEquiv {W : Type*} [DecidableEq W]
    {s : Finset V} (f : V ↪ W) : ↑(s : Set V) ≃ ↑((s.map f) : Set W) :=
  Equiv.ofBijective
    (fun v => ⟨f v, by simpa using Finset.mem_map.mpr ⟨v, by simpa using v.2, rfl⟩⟩)
    (by
      constructor
      · intro v w hvw
        apply Subtype.ext
        exact f.injective (Subtype.ext_iff.mp hvw)
      · intro w
        rcases Finset.mem_map.mp (by simpa using w.2) with ⟨v, hv, hfw⟩
        refine ⟨⟨v, by simpa using hv⟩, ?_⟩
        apply Subtype.ext
        exact hfw)

private noncomputable def inducedOnIsoMap {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ↪g G') (s : Finset V) :
    inducedOn G s ≃g inducedOn G' (s.map e.toEmbedding) where
  toEquiv := finsetSubtypeMapEquiv e.toEmbedding
  map_rel_iff' := by
    intro a b
    simpa [finsetSubtypeMapEquiv, inducedOn] using (e.map_adj_iff (v := a) (w := b))

lemma inducesRegularOfDegree_of_embedding {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ↪g G') {s : Finset V} {d : ℕ}
    (hs : InducesRegularOfDegree G s d) :
    InducesRegularOfDegree G' (s.map e.toEmbedding) d := by
  classical
  let hIso := inducedOnIsoMap e s
  rw [InducesRegularOfDegree] at hs ⊢
  intro v
  calc
    (inducedOn G' (s.map e.toEmbedding)).degree v =
        (inducedOn G s).degree (hIso.symm v) := by
          simpa using (SimpleGraph.Iso.degree_eq hIso (hIso.symm v))
    _ = d := hs (hIso.symm v)

lemma hasRegularInducedSubgraphOfCard_of_embedding {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ↪g G') {k : ℕ}
    (hk : HasRegularInducedSubgraphOfCard G k) : HasRegularInducedSubgraphOfCard G' k := by
  rcases hk with ⟨s, hks, d, hd⟩
  refine ⟨s.map e.toEmbedding, ?_, d, inducesRegularOfDegree_of_embedding e hd⟩
  simpa using hks

end FiniteGraph

end RegularInducedSubgraph
