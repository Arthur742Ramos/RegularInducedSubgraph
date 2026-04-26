import RegularInducedSubgraph.Problem
import Mathlib.Data.Nat.Choose.Bounds

open scoped Classical BigOperators

namespace RegularInducedSubgraph

private lemma indepInsertOfSubsetFilter {α : Type*} [DecidableEq α] {G : SimpleGraph α} {a : α}
    {s t : Finset α} {n : ℕ} (ht : t ⊆ (s.erase a).filter fun b => ¬ G.Adj a b)
    (hind : G.IsNIndepSet (n + 1) t) : G.IsNIndepSet (n + 2) (insert a t) := by
  classical
  rw [← SimpleGraph.isNClique_compl] at hind ⊢
  refine hind.insert ?_
  intro b hb
  have hb' : b ∈ (s.erase a).filter fun b => ¬ G.Adj a b := ht hb
  rcases Finset.mem_filter.mp hb' with ⟨hbs, hnot⟩
  have hab : a ≠ b := (Finset.mem_erase.mp hbs).1.symm
  exact (SimpleGraph.compl_adj _ _ _).2 ⟨hab, hnot⟩

private lemma indepInsertOfSubsetFilter_succ {α : Type*} [DecidableEq α] {G : SimpleGraph α}
    {a : α} {s t : Finset α} {n : ℕ}
    (ht : t ⊆ (s.erase a).filter fun b => ¬ G.Adj a b)
    (hind : G.IsNIndepSet n t) : G.IsNIndepSet (n + 1) (insert a t) := by
  classical
  rw [← SimpleGraph.isNClique_compl] at hind ⊢
  refine hind.insert ?_
  intro b hb
  have hb' : b ∈ (s.erase a).filter fun b => ¬ G.Adj a b := ht hb
  rcases Finset.mem_filter.mp hb' with ⟨hbs, hnot⟩
  have hab : a ≠ b := (Finset.mem_erase.mp hbs).1.symm
  exact (SimpleGraph.compl_adj _ _ _).2 ⟨hab, hnot⟩

/--
A finite Ramsey bound on a prescribed vertex set: if `s` is large enough, then `G` contains either
an `(m + 1)`-clique or an `(n + 1)`-independent set inside `s`.
-/
theorem ramsey_finset {α : Type*} (G : SimpleGraph α) :
    ∀ m n s, Nat.choose (m + n) m ≤ s.card →
      (∃ t ⊆ s, G.IsNClique (m + 1) t) ∨ ∃ t ⊆ s, G.IsNIndepSet (n + 1) t := by
  classical
  have hmain :
      ∀ p m n, m + n = p → ∀ s : Finset α, Nat.choose (m + n) m ≤ s.card →
        (∃ t ⊆ s, G.IsNClique (m + 1) t) ∨ ∃ t ⊆ s, G.IsNIndepSet (n + 1) t := by
    intro p
    induction' p using Nat.strong_induction_on with p ih
    intro m n hmn s hs
    cases m with
    | zero =>
        have hpos : 0 < s.card := lt_of_lt_of_le (by simpa using Nat.choose_pos (Nat.zero_le n)) hs
        rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
        left
        refine ⟨{a}, ?_, ?_⟩
        · intro b hb
          have hba : b = a := by simpa [Finset.mem_singleton] using hb
          simpa [hba] using ha
        · simp [SimpleGraph.isNClique_iff]
    | succ m =>
        cases n with
        | zero =>
            have hpos : 0 < s.card :=
              lt_of_lt_of_le (by simpa using Nat.choose_pos (Nat.le_refl (m + 1))) hs
            rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
            right
            refine ⟨{a}, ?_, ?_⟩
            · intro b hb
              have hba : b = a := by simpa [Finset.mem_singleton] using hb
              simpa [hba] using ha
            · simp [SimpleGraph.isNIndepSet_iff, SimpleGraph.isIndepSet_iff]
        | succ n =>
            have hpos : 0 < s.card := lt_of_lt_of_le (by
              simpa [Nat.add_assoc] using
                Nat.choose_pos (show m + 1 ≤ m + 1 + (n + 1) by omega)) hs
            rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
            set N : Finset α := (s.erase a).filter (G.Adj a) with hN
            set M : Finset α := (s.erase a).filter fun b => ¬ G.Adj a b with hM
            have hN_sub_s : N ⊆ s := by
              intro x hx
              rw [hN] at hx
              exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
            have hM_sub_s : M ⊆ s := by
              intro x hx
              rw [hM] at hx
              exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
            have hpart : N.card + M.card = (s.erase a).card := by
              rw [hN, hM]
              simpa using (Finset.card_filter_add_card_filter_not (s := s.erase a) (p := G.Adj a))
            have hchoose :
                Nat.choose ((m + 1) + (n + 1)) (m + 1) =
                  Nat.choose (m + (n + 1)) m + Nat.choose ((m + 1) + n) (m + 1) := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Nat.choose_succ_succ' (m + n + 1) m)
            have hlarge :
                Nat.choose (m + (n + 1)) m ≤ N.card ∨
                  Nat.choose ((m + 1) + n) (m + 1) ≤ M.card := by
              by_contra hcontra
              have hNlt : N.card < Nat.choose (m + (n + 1)) m := by
                exact Nat.lt_of_not_ge fun h => hcontra (Or.inl h)
              have hMlt : M.card < Nat.choose ((m + 1) + n) (m + 1) := by
                exact Nat.lt_of_not_ge fun h => hcontra (Or.inr h)
              have hErase : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
              have hsCard : s.card = N.card + M.card + 1 := by
                rw [hpart, hErase]
                omega
              have hsumlt :
                  N.card + M.card <
                    Nat.choose (m + (n + 1)) m + Nat.choose ((m + 1) + n) (m + 1) :=
                Nat.add_lt_add hNlt hMlt
              have hsmall : s.card < Nat.choose ((m + 1) + (n + 1)) (m + 1) := by
                rw [hsCard, hchoose]
                omega
              exact (Nat.not_lt_of_ge hs) hsmall
            cases hlarge with
            | inl hNlarge =>
                have hrecN := ih (m + (n + 1)) (by omega) m (n + 1) rfl N hNlarge
                cases hrecN with
                | inl hClique =>
                    rcases hClique with ⟨t, htN, hct⟩
                    left
                    refine ⟨insert a t, ?_, ?_⟩
                    · intro x hx
                      rcases Finset.mem_insert.mp hx with rfl | hx
                      · exact ha
                      · exact hN_sub_s (htN hx)
                    · exact hct.insert (fun b hb => (Finset.mem_filter.mp (htN hb)).2)
                | inr hIndep =>
                    rcases hIndep with ⟨t, htN, hit⟩
                    right
                    exact ⟨t, subset_trans htN hN_sub_s, hit⟩
            | inr hMlarge =>
                have hrecM := ih ((m + 1) + n) (by omega) (m + 1) n rfl M hMlarge
                cases hrecM with
                | inl hClique =>
                    rcases hClique with ⟨t, htM, hct⟩
                    left
                    exact ⟨t, subset_trans htM hM_sub_s, hct⟩
                | inr hIndep =>
                    rcases hIndep with ⟨t, htM, hit⟩
                    right
                    refine ⟨insert a t, ?_, indepInsertOfSubsetFilter (s := s) htM hit⟩
                    intro x hx
                    rcases Finset.mem_insert.mp hx with rfl | hx
                    · exact ha
                    · exact hM_sub_s (htM hx)
  intro m n s hs
  exact hmain (m + n) m n rfl s hs

/-- A finite off-diagonal Ramsey upper bound, localized to every prescribed vertex set. -/
def HasCliqueOrIndepSetBound (a b N : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α), N ≤ s.card →
    (∃ t ⊆ s, G.IsNClique a t) ∨ ∃ t ⊆ s, G.IsNIndepSet b t

/-- A Ramsey bound remains valid if the required ambient threshold is increased. -/
theorem HasCliqueOrIndepSetBound.mono {a b N N' : ℕ}
    (h : HasCliqueOrIndepSetBound a b N) (hNN' : N ≤ N') :
    HasCliqueOrIndepSetBound a b N' := by
  intro α _ G s hs
  exact h G s (le_trans hNN' hs)

/-- The binomial Ramsey theorem as a reusable finite-bound package. -/
theorem hasCliqueOrIndepSetBound_of_ramsey_finset
    {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hchoose : Nat.choose ((a - 1) + (b - 1)) (a - 1) ≤ N) :
    HasCliqueOrIndepSetBound a b N := by
  intro α _ G s hs
  have h := ramsey_finset G (a - 1) (b - 1) s (le_trans hchoose hs)
  simpa [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using h

/-- Symmetry of finite Ramsey bounds, by passing to the complement graph. -/
theorem HasCliqueOrIndepSetBound.symm {a b N : ℕ}
    (h : HasCliqueOrIndepSetBound a b N) : HasCliqueOrIndepSetBound b a N := by
  intro α _ G s hs
  rcases h Gᶜ s hs with hclique | hindep
  · right
    rcases hclique with ⟨t, hts, ht⟩
    refine ⟨t, hts, ?_⟩
    simpa [SimpleGraph.isNClique_compl] using ht
  · left
    rcases hindep with ⟨t, hts, ht⟩
    refine ⟨t, hts, ?_⟩
    rw [← SimpleGraph.isNClique_compl] at ht
    simpa using ht

/--
Ramsey recurrence for the localized finite-bound package:
`R(a + 1, b + 1) <= R(a, b + 1) + R(a + 1, b)`.
-/
theorem HasCliqueOrIndepSetBound.step
    {a b N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hleft : HasCliqueOrIndepSetBound a (b + 1) N₁)
    (hright : HasCliqueOrIndepSetBound (a + 1) b N₂) :
    HasCliqueOrIndepSetBound (a + 1) (b + 1) (N₁ + N₂) := by
  intro α _ G s hs
  classical
  have hsumpos : 0 < N₁ + N₂ := by omega
  have hspos : 0 < s.card := lt_of_lt_of_le hsumpos hs
  rcases Finset.card_pos.mp hspos with ⟨v, hv⟩
  set A : Finset α := (s.erase v).filter (G.Adj v) with hA
  set B : Finset α := (s.erase v).filter fun w => ¬ G.Adj v w with hB
  have hA_sub_s : A ⊆ s := by
    intro x hx
    rw [hA] at hx
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
  have hB_sub_s : B ⊆ s := by
    intro x hx
    rw [hB] at hx
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
  have hpart : A.card + B.card = (s.erase v).card := by
    rw [hA, hB]
    simpa using (Finset.card_filter_add_card_filter_not (s := s.erase v) (p := G.Adj v))
  have hlarge : N₁ ≤ A.card ∨ N₂ ≤ B.card := by
    by_contra hcontra
    have hAlt : A.card < N₁ := Nat.lt_of_not_ge fun hge => hcontra (Or.inl hge)
    have hBlt : B.card < N₂ := Nat.lt_of_not_ge fun hge => hcontra (Or.inr hge)
    have hErase : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
    have hsCard : s.card = A.card + B.card + 1 := by
      rw [hpart, hErase]
      omega
    have hsmall : s.card < N₁ + N₂ := by omega
    exact (Nat.not_lt_of_ge hs) hsmall
  rcases hlarge with hAlarge | hBlarge
  · rcases hleft G A hAlarge with hclique | hindep
    · left
      rcases hclique with ⟨t, htA, hct⟩
      refine ⟨insert v t, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · exact hA_sub_s (htA hx)
      · exact hct.insert (fun w hw => (Finset.mem_filter.mp (htA hw)).2)
    · right
      rcases hindep with ⟨t, htA, hit⟩
      exact ⟨t, subset_trans htA hA_sub_s, hit⟩
  · rcases hright G B hBlarge with hclique | hindep
    · left
      rcases hclique with ⟨t, htB, hct⟩
      exact ⟨t, subset_trans htB hB_sub_s, hct⟩
    · right
      rcases hindep with ⟨t, htB, hit⟩
      refine ⟨insert v t, ?_, indepInsertOfSubsetFilter_succ (s := s) htB hit⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hB_sub_s (htB hx)

/-- Ramsey recurrence followed by monotonicity of the ambient threshold. -/
theorem HasCliqueOrIndepSetBound.step_mono
    {a b N₁ N₂ N : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hleft : HasCliqueOrIndepSetBound a (b + 1) N₁)
    (hright : HasCliqueOrIndepSetBound (a + 1) b N₂)
    (hN : N₁ + N₂ ≤ N) :
    HasCliqueOrIndepSetBound (a + 1) (b + 1) N :=
  HasCliqueOrIndepSetBound.mono
    (HasCliqueOrIndepSetBound.step hN₁ hN₂ hleft hright) hN

/-- If a set has neither side of a Ramsey alternative, its cardinality is below the bound. -/
theorem card_lt_of_no_clique_or_indep
    {a b N : ℕ} (h : HasCliqueOrIndepSetBound a b N)
    {α : Type} [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (hnoClique : ¬ ∃ t : Finset α, t ⊆ s ∧ G.IsNClique a t)
    (hnoIndep : ¬ ∃ t : Finset α, t ⊆ s ∧ G.IsNIndepSet b t) :
    s.card < N := by
  by_contra hlt
  have hN : N ≤ s.card := le_of_not_gt hlt
  rcases h G s hN with hclique | hindep
  · exact hnoClique hclique
  · exact hnoIndep hindep

/-- Internal degree in an induced finite vertex set, written as an external neighbor intersection. -/
theorem inducedOn_degree_eq_card_neighborFinset_inter
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset α) (v : ↑(s : Set α)) :
    (inducedOn G s).degree v = (G.neighborFinset v ∩ s).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G s).neighborFinset v).map (Function.Embedding.subtype (· ∈ (s : Set α))) =
        G.neighborFinset v ∩ s := by
    ext x
    simp [inducedOn, and_assoc]
  calc
    ((inducedOn G s).neighborFinset v).card =
        (((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ (s : Set α)))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset v ∩ s).card := by rw [hmap]

/--
In a graph with no `4`-clique and no independent `5`-set, a local `R(3,5)` bound forces every
neighborhood to have size below that bound.
-/
theorem degree_lt_of_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {N : ℕ} (h35 : HasCliqueOrIndepSetBound 3 5 N)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    G.degree v < N := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_lt_of_no_clique_or_indep h35 G (G.neighborFinset v) ?_ ?_
  · rintro ⟨t, htN, htClique⟩
    exact hnoK4 ⟨insert v t, htClique.insert (by
      intro w hw
      exact (G.mem_neighborFinset v w).mp (htN hw))⟩
  · rintro ⟨t, _htN, htIndep⟩
    exact hnoI5 ⟨t, htIndep⟩

/--
In a `26`-vertex graph with no `4`-clique and no independent `5`-set, a local `R(4,4)` bound
forces every vertex to have degree at least `8`.
-/
theorem eight_le_degree_of_card_twenty_six_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (h44 : HasCliqueOrIndepSetBound 4 4 18)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    8 ≤ G.degree v := by
  classical
  set nonNbrs : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) with hnonNbrs
  have hNonNbrsLt : nonNbrs.card < 18 := by
    refine card_lt_of_no_clique_or_indep h44 G nonNbrs ?_ ?_
    · rintro ⟨t, _ht, htClique⟩
      exact hnoK4 ⟨t, htClique⟩
    · rintro ⟨t, ht, htIndep⟩
      exact hnoI5 ⟨insert v t, by
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        refine htIndep.insert ?_
        intro b hb
        have hb' : b ∈ nonNbrs := ht hb
        rw [hnonNbrs] at hb'
        rcases Finset.mem_filter.mp hb' with ⟨hbs, hnot⟩
        have hvb : v ≠ b := (Finset.mem_erase.mp hbs).1.symm
        exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvb, hnot⟩⟩
  have hpart :
      (G.neighborFinset v).card + nonNbrs.card = (Finset.univ.erase v).card := by
    have hneighbor :
        G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
      ext w
      by_cases hwv : w = v
      · subst w
        simp
      · simp [hwv]
    rw [hneighbor, hnonNbrs]
    simpa using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
  have htotal : (Finset.univ.erase v).card = 25 := by
    have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
    rw [Finset.card_univ, hcard] at h
    simpa using h
  have hdegCard : G.degree v = (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  rw [hdegCard]
  omega

/-- A concise degree interval for any hypothetical `R(4,5)` counterexample on 26 vertices. -/
theorem degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (h35 : HasCliqueOrIndepSetBound 3 5 14)
    (h44 : HasCliqueOrIndepSetBound 4 4 18)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    8 ≤ G.degree v ∧ G.degree v ≤ 13 := by
  constructor
  · exact eight_le_degree_of_card_twenty_six_no_clique_four_no_indep_five
      G hcard h44 hnoK4 hnoI5 v
  · exact Nat.le_of_lt_succ
      (by
        simpa using
          degree_lt_of_no_clique_four_no_indep_five G h35 hnoK4 hnoI5 v)

/-- The diagonal base `R(3,3) <= 6`, from the generic binomial Ramsey theorem. -/
theorem hasCliqueOrIndepSetBound_three_three_six :
    HasCliqueOrIndepSetBound 3 3 6 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 3) (b := 3) (N := 6) (by decide) (by decide) (by decide)

/-- A direct hand proof of the small off-diagonal bound `R(3,4) <= 9` on a full finite type. -/
theorem exists_clique_three_or_indep_four_of_card_nine
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 9) :
    (∃ t : Finset α, G.IsNClique 3 t) ∨ ∃ t : Finset α, G.IsNIndepSet 4 t := by
  classical
  by_cases hK3 : ∃ t : Finset α, G.IsNClique 3 t
  · exact Or.inl hK3
  · right
    by_cases hHigh : ∃ v : α, 4 ≤ G.degree v
    · rcases hHigh with ⟨v, hvdeg⟩
      have hNcard : 4 ≤ (G.neighborFinset v).card := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hvdeg
      rcases Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 4) hNcard with
        ⟨t, htN, htcard⟩
      refine ⟨t, ?_⟩
      refine ⟨?_, htcard⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      by_contra habAdj
      have hva : G.Adj v a := (G.mem_neighborFinset v a).mp (htN ha)
      have hvb : G.Adj v b := (G.mem_neighborFinset v b).mp (htN hb)
      exact hK3 ⟨{v, a, b}, SimpleGraph.is3Clique_triple_iff.mpr ⟨hva, hvb, habAdj⟩⟩
    · have hdeg_le_three : ∀ v : α, G.degree v ≤ 3 := by
        intro v
        by_contra hv
        exact hHigh ⟨v, by omega⟩
      have hlow : ∃ v : α, G.degree v ≤ 2 := by
        by_contra hnone
        have hdeg_eq_three : ∀ v : α, G.degree v = 3 := by
          intro v
          have hge : 3 ≤ G.degree v := by
            have hvnot : ¬ G.degree v ≤ 2 := by
              intro hvle
              exact hnone ⟨v, hvle⟩
            omega
          exact le_antisymm (hdeg_le_three v) hge
        have hsum_three : (∑ v : α, G.degree v) = 27 := by
          calc
            (∑ v : α, G.degree v) = ∑ _v : α, 3 := by
              exact Finset.sum_congr rfl (fun v _ => hdeg_eq_three v)
            _ = Fintype.card α * 3 := by simp
            _ = 27 := by rw [hcard]
        have hsum_edges := G.sum_degrees_eq_twice_card_edges
        omega
      rcases hlow with ⟨v, hvdeg⟩
      set nonNbrs : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) with hnonNbrs
      have hpart :
          (G.neighborFinset v).card + nonNbrs.card = (Finset.univ.erase v).card := by
        have hneighbor :
            G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
          ext w
          by_cases hwv : w = v
          · subst w
            simp
          · simp [hwv]
        rw [hneighbor, hnonNbrs]
        simpa using
          (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
      have htotal : (Finset.univ.erase v).card = 8 := by
        have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
        rw [Finset.card_univ, hcard] at h
        simpa using h
      have hneighborCardLe : (G.neighborFinset v).card ≤ 2 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hvdeg
      have hnonNbrsCard : 6 ≤ nonNbrs.card := by omega
      rcases hasCliqueOrIndepSetBound_three_three_six G nonNbrs hnonNbrsCard with
        hClique | hIndep
      · rcases hClique with ⟨t, _ht, htClique⟩
        exact False.elim (hK3 ⟨t, htClique⟩)
      · rcases hIndep with ⟨t, htNonNbrs, htIndep⟩
        refine ⟨insert v t, ?_⟩
        rw [hnonNbrs] at htNonNbrs
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        refine htIndep.insert ?_
        intro b hb
        have hb' := htNonNbrs hb
        rcases Finset.mem_filter.mp hb' with ⟨hbs, hnot⟩
        have hvb : v ≠ b := (Finset.mem_erase.mp hbs).1.symm
        exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvb, hnot⟩

/-- The small off-diagonal Ramsey bound `R(3,4) <= 9`. -/
theorem hasCliqueOrIndepSetBound_three_four_nine :
    HasCliqueOrIndepSetBound 3 4 9 := by
  intro α _ G s hs
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases Finset.exists_subset_card_eq (s := s) (n := 9) hs with ⟨u, hus, hucard⟩
  let H : SimpleGraph ↑(u : Set α) := inducedOn G u
  have hHcard : Fintype.card ↑(u : Set α) = 9 := by
    simpa [hucard] using (Fintype.card_coe u)
  rcases exists_clique_three_or_indep_four_of_card_nine H hHcard with hClique | hIndep
  · left
    rcases hClique with ⟨t, htClique⟩
    refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨v, _hv, rfl⟩
      exact hus v.2
    · rw [SimpleGraph.isNClique_iff] at htClique ⊢
      constructor
      · rw [SimpleGraph.isClique_iff]
        intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨vx, hvx, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨vy, hvy, rfl⟩
        have hvxy : vx ≠ vy := by
          intro h
          exact hxy (by simpa [h])
        simpa [H, inducedOn] using htClique.1 hvx hvy hvxy
      · simpa using htClique.2
  · right
    rcases hIndep with ⟨t, htIndep⟩
    refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨v, _hv, rfl⟩
      exact hus v.2
    · rw [SimpleGraph.isNIndepSet_iff] at htIndep ⊢
      constructor
      · rw [SimpleGraph.isIndepSet_iff] at htIndep ⊢
        intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨vx, hvx, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨vy, hvy, rfl⟩
        have hvxy : vx ≠ vy := by
          intro h
          exact hxy (by simpa [h])
        simpa [H, inducedOn] using htIndep.1 hvx hvy hvxy
      · simpa using htIndep.2

/-- The recurrence from `R(2,5) <= 5` and `R(3,4) <= 9` gives `R(3,5) <= 14`. -/
theorem hasCliqueOrIndepSetBound_three_five_fourteen :
    HasCliqueOrIndepSetBound 3 5 14 := by
  have h25 : HasCliqueOrIndepSetBound 2 5 5 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 2) (b := 5) (N := 5) (by decide) (by decide) (by decide)
  have hstep : HasCliqueOrIndepSetBound 3 5 (5 + 9) :=
    HasCliqueOrIndepSetBound.step (a := 2) (b := 4) (N₁ := 5) (N₂ := 9)
      (by decide : 0 < 5) (by decide : 0 < 9) h25
      hasCliqueOrIndepSetBound_three_four_nine
  intro α _ G s hs
  exact hstep (α := α) G s (by omega)

/-- The recurrence from `R(3,4) <= 9` and symmetry gives `R(4,4) <= 18`. -/
theorem hasCliqueOrIndepSetBound_four_four_eighteen :
    HasCliqueOrIndepSetBound 4 4 18 := by
  have hstep : HasCliqueOrIndepSetBound 4 4 (9 + 9) :=
    HasCliqueOrIndepSetBound.step (a := 3) (b := 3) (N₁ := 9) (N₂ := 9)
      (by decide : 0 < 9) (by decide : 0 < 9)
      hasCliqueOrIndepSetBound_three_four_nine
      (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine)
  intro α _ G s hs
  exact hstep (α := α) G s (by omega)

/--
Unconditional degree pressure on any 26-vertex `R(4,5)` counterexample: every degree lies in
`[8,13]`.  The only finite Ramsey input used here, `R(3,4) <= 9`, is proved directly above.
-/
theorem degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five_unconditional
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    8 ≤ G.degree v ∧ G.degree v ≤ 13 :=
  degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five G hcard
    hasCliqueOrIndepSetBound_three_five_fourteen
    hasCliqueOrIndepSetBound_four_four_eighteen hnoK4 hnoI5 v

/-- A neighborhood cannot contain a triangle when adjoining its center would make a `4`-clique. -/
theorem no_clique_three_in_neighborFinset_of_no_clique_four
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t) (v : α) :
    (by
      classical
      exact ¬ ∃ t : Finset α, t ⊆ G.neighborFinset v ∧ G.IsNClique 3 t) := by
  classical
  rintro ⟨t, ht, htClique⟩
  exact hnoK4 ⟨insert v t, htClique.insert (by
    intro w hw
    exact (G.mem_neighborFinset v w).mp (ht hw))⟩

/-- A neighborhood inherits the absence of independent `5`-sets. -/
theorem no_indep_five_in_neighborFinset_of_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    (by
      classical
      exact ¬ ∃ t : Finset α, t ⊆ G.neighborFinset v ∧ G.IsNIndepSet 5 t) := by
  classical
  rintro ⟨t, _ht, htIndep⟩
  exact hnoI5 ⟨t, htIndep⟩

/-- A non-neighborhood inherits the absence of `4`-cliques. -/
theorem no_clique_four_in_nonNeighborFinset_of_no_clique_four
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t) (v : α) :
    (by
      classical
      exact ¬ ∃ t : Finset α,
        t ⊆ (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) ∧ G.IsNClique 4 t) := by
  classical
  rintro ⟨t, _ht, htClique⟩
  exact hnoK4 ⟨t, htClique⟩

/--
A non-neighborhood cannot contain an independent `4`-set, since adjoining the center would make
an independent `5`-set.
-/
theorem no_indep_four_in_nonNeighborFinset_of_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t) (v : α) :
    ¬ ∃ t : Finset α,
      t ⊆ (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) ∧ G.IsNIndepSet 4 t := by
  classical
  rintro ⟨t, ht, htIndep⟩
  exact hnoI5 ⟨insert v t, by
    rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
    refine htIndep.insert ?_
    intro w hw
    have hwNon := ht hw
    rcases Finset.mem_filter.mp hwNon with ⟨hwErase, hvw⟩
    have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩⟩

/-- The non-neighborhood of a degree-`13` vertex in a `26`-vertex graph has size `12`. -/
theorem nonNeighborFinset_card_eq_twelve_of_card_twenty_six_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26) {v : α} (hdegv : G.degree v = 13) :
    ((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).card = 12 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  have hpart :
      (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
    have hneighbor :
        G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
      ext w
      by_cases hwv : w = v
      · subst w
        simp
      · simp [hwv]
    rw [hneighbor]
    simpa [nonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
  have htotal : (Finset.univ.erase v).card = 25 := by
    have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
    rw [Finset.card_univ, hcard] at h
    simpa using h
  have hneighborCard : (G.neighborFinset v).card = 13 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
  simpa [nonNbrsV] using (by omega : nonNbrsV.card = 12)

/-- The non-neighborhood of a degree-`8` vertex in a `26`-vertex graph has size `17`. -/
theorem nonNeighborFinset_card_eq_seventeen_of_card_twenty_six_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26) {v : α} (hdegv : G.degree v = 8) :
    ((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).card = 17 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  have hpart :
      (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
    have hneighbor :
        G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
      ext w
      by_cases hwv : w = v
      · subst w
        simp
      · simp [hwv]
    rw [hneighbor]
    simpa [nonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
  have htotal : (Finset.univ.erase v).card = 25 := by
    have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
    rw [Finset.card_univ, hcard] at h
    simpa using h
  have hneighborCard : (G.neighborFinset v).card = 8 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
  simpa [nonNbrsV] using (by omega : nonNbrsV.card = 17)

/-- The trivial off-diagonal bound `R(2,5) <= 5`. -/
theorem hasCliqueOrIndepSetBound_two_five_five :
    HasCliqueOrIndepSetBound 2 5 5 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 2) (b := 5) (N := 5) (by decide) (by decide) (by decide)

/-- The trivial off-diagonal bound `R(4,2) <= 4`. -/
theorem hasCliqueOrIndepSetBound_four_two_four :
    HasCliqueOrIndepSetBound 4 2 4 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 4) (b := 2) (N := 4) (by decide) (by decide) (by decide)

/--
In any graph with no `4`-clique and no independent `5`-set, adjacent vertices have at most four
common neighbors.
-/
theorem common_neighbor_card_le_four_of_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 4 := by
  classical
  have hlt :
      (G.neighborFinset u ∩ G.neighborFinset v).card < 5 := by
    refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_two_five_five G
      (G.neighborFinset u ∩ G.neighborFinset v) ?_ ?_
    · rintro ⟨t, htCommon, htClique⟩
      have hvt : ∀ w ∈ t, G.Adj v w := by
        intro w hw
        exact (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp (htCommon hw)).2
      have hut : ∀ w ∈ t, G.Adj u w := by
        intro w hw
        exact (G.mem_neighborFinset u w).mp (Finset.mem_inter.mp (htCommon hw)).1
      have hCliqueWithV : G.IsNClique 3 (insert v t) := htClique.insert hvt
      have hCliqueWithUV : G.IsNClique 4 (insert u (insert v t)) := by
        refine hCliqueWithV.insert ?_
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · exact huv
        · exact hut w hwt
      exact hnoK4 ⟨insert u (insert v t), hCliqueWithUV⟩
    · rintro ⟨t, _htCommon, htIndep⟩
      exact hnoI5 ⟨t, htIndep⟩
  exact Nat.le_of_lt_succ hlt

/--
If a vertex has degree `13` in a graph with no `4`-clique and no independent `5`-set, then every
neighbor has at least four common neighbors with it.
-/
theorem four_le_common_neighbor_card_of_degree_thirteen_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegv : G.degree v = 13) :
    4 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  let nonNbrsInNv : Finset α :=
    (G.neighborFinset v).erase u |>.filter fun w => ¬ G.Adj u w
  have huN : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr huv.symm
  have hcommon :
      G.neighborFinset u ∩ G.neighborFinset v =
        ((G.neighborFinset v).erase u).filter (G.Adj u) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_inter.mp hw with ⟨hwu, hwv⟩
      have huw : G.Adj u w := (G.mem_neighborFinset u w).mp hwu
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨huw.ne.symm, hwv⟩, huw⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, huw⟩
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u w).mpr huw, (Finset.mem_erase.mp hwErase).2⟩
  have hpart :
      (G.neighborFinset u ∩ G.neighborFinset v).card + nonNbrsInNv.card =
        ((G.neighborFinset v).erase u).card := by
    rw [hcommon]
    simpa [nonNbrsInNv] using
      (Finset.card_filter_add_card_filter_not
        (s := (G.neighborFinset v).erase u) (p := G.Adj u))
  have htotal : ((G.neighborFinset v).erase u).card = 12 := by
    have hcardNv : (G.neighborFinset v).card = 13 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
    rw [Finset.card_erase_of_mem huN, hcardNv]
  have hNonNbrsLt : nonNbrsInNv.card < 9 := by
    refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_three_four_nine G
      nonNbrsInNv ?_ ?_
    · rintro ⟨t, htNon, htClique⟩
      exact hnoK4 ⟨insert v t, htClique.insert (by
        intro w hw
        have hwNon := htNon hw
        simp only [nonNbrsInNv, Finset.mem_filter] at hwNon
        exact (G.mem_neighborFinset v w).mp (Finset.mem_erase.mp hwNon.1).2)⟩
    · rintro ⟨t, htNon, htIndep⟩
      exact hnoI5 ⟨insert u t, by
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        refine htIndep.insert ?_
        intro w hw
        have hwNon := htNon hw
        simp only [nonNbrsInNv, Finset.mem_filter] at hwNon
        rcases hwNon with ⟨hwErase, huw⟩
        have huw_ne : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
        exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, huw⟩⟩
  omega

/--
If a vertex has degree `13` in a graph with no `4`-clique and no independent `5`-set, then every
neighbor has exactly four common neighbors with it.
-/
theorem common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegv : G.degree v = 13) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 4 :=
  le_antisymm
    (common_neighbor_card_le_four_of_no_clique_four_no_indep_five G hnoK4 hnoI5 huv)
    (four_le_common_neighbor_card_of_degree_thirteen_no_clique_four_no_indep_five
      G hnoK4 hnoI5 huv hdegv)

/--
The neighborhood of a degree-`13` vertex in any no-`K₄`/no-independent-`5` graph is a regular
induced graph of degree `4`.
-/
theorem neighborFinset_isRegularOfDegree_four_of_degree_thirteen_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {v : α} (hdegv : G.degree v = 13) :
    (inducedOn G (G.neighborFinset v)).IsRegularOfDegree 4 := by
  intro u
  have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp u.2
  have huv : G.Adj u v := hvu.symm
  rw [inducedOn_degree_eq_card_neighborFinset_inter]
  exact common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
    G hnoK4 hnoI5 huv hdegv

/--
If `v` has degree `13`, then every non-neighbor of `v` is adjacent to at least five vertices
inside the neighborhood of `v`.
-/
theorem five_le_neighbor_inter_neighborFinset_card_of_degree_thirteen_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : ¬ G.Adj u v) (hdegv : G.degree v = 13) :
    5 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  let nonNbrsOfUInNv : Finset α := (G.neighborFinset v).filter (fun w => ¬ G.Adj u w)
  have hpart :
      (G.neighborFinset u ∩ G.neighborFinset v).card + nonNbrsOfUInNv.card =
        (G.neighborFinset v).card := by
    have hcommon :
        G.neighborFinset u ∩ G.neighborFinset v =
          (G.neighborFinset v).filter (G.Adj u) := by
      ext w
      constructor
      · intro hw
        rcases Finset.mem_inter.mp hw with ⟨hwu, hwv⟩
        exact Finset.mem_filter.mpr ⟨hwv, (G.mem_neighborFinset u w).mp hwu⟩
      · intro hw
        rcases Finset.mem_filter.mp hw with ⟨hwv, huw⟩
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u w).mpr huw, hwv⟩
    rw [hcommon]
    simpa [nonNbrsOfUInNv] using
      (Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (p := G.Adj u))
  have hNvCard : (G.neighborFinset v).card = 13 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
  have hNonNbrsLt : nonNbrsOfUInNv.card < 9 := by
    refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_three_four_nine G
      nonNbrsOfUInNv ?_ ?_
    · rintro ⟨t, htNon, htClique⟩
      exact hnoK4 ⟨insert v t, htClique.insert (by
        intro w hw
        have hwNon := htNon hw
        simp only [nonNbrsOfUInNv, Finset.mem_filter] at hwNon
        exact (G.mem_neighborFinset v w).mp hwNon.1)⟩
    · rintro ⟨t, htNon, htIndep⟩
      exact hnoI5 ⟨insert u t, by
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        refine htIndep.insert ?_
        intro w hw
        have hwNon := htNon hw
        simp only [nonNbrsOfUInNv, Finset.mem_filter] at hwNon
        have huw_ne : u ≠ w := by
          intro huw_eq
          subst w
          exact huv ((G.mem_neighborFinset v u).mp hwNon.1).symm
        exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, hwNon.2⟩⟩
  omega

/--
If `v` has degree `13`, then every non-neighbor of `v` has at least three neighbors on the
non-neighborhood side of `v`.
-/
theorem three_le_neighbor_in_nonNeighborFinset_card_of_degree_thirteen_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 13) :
    3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
      (G.Adj u)).card := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (fun w => ¬ G.Adj u w)
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  have huNonNbrsV : u ∈ nonNbrsV := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv_ne, by simp⟩, hvu⟩
  have hpart :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card =
        (nonNbrsV.erase u).card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV.erase u) (p := G.Adj u))
  have hNonNbrsVCard : nonNbrsV.card = 12 := by
    have hpartV :
        (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
      have hneighbor :
          G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
        ext w
        by_cases hwv : w = v
        · subst w
          simp
        · simp [hwv]
      rw [hneighbor]
      simpa [nonNbrsV] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    have hneighborCard : (G.neighborFinset v).card = 13 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
    omega
  have htotal : (nonNbrsV.erase u).card = 11 := by
    rw [Finset.card_erase_of_mem huNonNbrsV, hNonNbrsVCard]
  have hNonNbrsLe : nonNbrsOfUInNonNbrsV.card ≤ 8 := by
    have hlt : nonNbrsOfUInNonNbrsV.card < 9 := by
      refine card_lt_of_no_clique_or_indep
        (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G
        nonNbrsOfUInNonNbrsV ?_ ?_
      · rintro ⟨t, _htNon, htClique⟩
        exact hnoK4 ⟨t, htClique⟩
      · rintro ⟨t, htNon, htIndep⟩
        exact hnoI5 ⟨insert u (insert v t), by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          have hCliqueWithV : Gᶜ.IsNClique 4 (insert v t) := by
            refine htIndep.insert ?_
            intro w hw
            have hwNon := htNon hw
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            have hwNonNbrsV : w ∈ nonNbrsV := (Finset.mem_erase.mp hwNon.1).2
            simp only [nonNbrsV, Finset.mem_filter] at hwNonNbrsV
            rcases hwNonNbrsV with ⟨hwErase, hvw⟩
            have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩
          refine hCliqueWithV.insert ?_
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwt
          · exact (SimpleGraph.compl_adj _ _ _).2 ⟨huv_ne, huv⟩
          · have hwNon := htNon hwt
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            rcases hwNon with ⟨hwErase, huw⟩
            have huw_ne : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, huw⟩⟩
    exact Nat.le_of_lt_succ hlt
  have hNbrsGe : 3 ≤ nbrsOfUInNonNbrsV.card := by omega
  simpa [nonNbrsV, nbrsOfUInNonNbrsV] using hNbrsGe

/-- Split the degree of a vertex across the neighborhood and non-neighborhood of a non-neighbor. -/
theorem degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v : α} (huv : ¬ G.Adj u v) :
    G.degree u =
      (G.neighborFinset u ∩ G.neighborFinset v).card +
        (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
          (G.Adj u)).card := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  have hcommon :
      (G.neighborFinset u).filter (G.Adj v) =
        G.neighborFinset u ∩ G.neighborFinset v := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwu, hvw⟩
      exact Finset.mem_inter.mpr ⟨hwu, (G.mem_neighborFinset v w).mpr hvw⟩
    · intro hw
      rcases Finset.mem_inter.mp hw with ⟨hwu, hwv⟩
      exact Finset.mem_filter.mpr ⟨hwu, (G.mem_neighborFinset v w).mp hwv⟩
  have hnon :
      (G.neighborFinset u).filter (fun w => ¬ G.Adj v w) = nbrsOfUInNonNbrsV := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwu, hvw⟩
      have huw : G.Adj u w := (G.mem_neighborFinset u w).mp hwu
      have hwv_ne : w ≠ v := by
        intro hwv_eq
        subst w
        exact huv huw
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr
          ⟨huw.ne.symm, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hwv_ne, by simp⟩, hvw⟩⟩,
          huw⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, huw⟩
      have hwNonNbrsV : w ∈ nonNbrsV := (Finset.mem_erase.mp hwErase).2
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset u w).mpr huw, (Finset.mem_filter.mp hwNonNbrsV).2⟩
  have hpart :=
    Finset.card_filter_add_card_filter_not (s := G.neighborFinset u) (p := G.Adj v)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← hpart, hcommon, hnon]

/-- A two-vertex partition identity for nonadjacent pairs in a `26`-vertex graph. -/
theorem degree_add_degree_add_common_non_neighbor_card_eq_twenty_four_add_common_neighbor_card_of_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) :
    G.degree u + G.degree v +
        (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
          (fun w => ¬ G.Adj u w)).card =
      24 + (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (fun w => ¬ G.Adj u w)
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  have huNonNbrsV : u ∈ nonNbrsV := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv_ne, by simp⟩, hvu⟩
  have hpartSide :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card =
        (nonNbrsV.erase u).card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV.erase u) (p := G.Adj u))
  have hErase :
      (nonNbrsV.erase u).card + 1 = nonNbrsV.card := by
    have hpos : 0 < nonNbrsV.card := Finset.card_pos.mpr ⟨u, huNonNbrsV⟩
    rw [Finset.card_erase_of_mem huNonNbrsV]
    omega
  have hpartV :
      (G.neighborFinset v).card + nonNbrsV.card = 25 := by
    have hneighbor :
        G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
      ext w
      by_cases hwv : w = v
      · subst w
        simp
      · simp [hwv]
    have hpartition :
        ((Finset.univ.erase v).filter (G.Adj v)).card + nonNbrsV.card =
          (Finset.univ.erase v).card := by
      simpa [nonNbrsV] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    simpa [hneighbor, htotal] using hpartition
  have hdegV : (G.neighborFinset v).card = G.degree v := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hsplit :
      G.degree u =
        (G.neighborFinset u ∩ G.neighborFinset v).card + nbrsOfUInNonNbrsV.card := by
    simpa [nonNbrsV, nbrsOfUInNonNbrsV] using
      degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
        G huv
  have hsideTotal :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card + 1 = nonNbrsV.card := by
    omega
  have hVTotal : G.degree v + nonNbrsV.card = 25 := by
    simpa [hdegV] using hpartV
  have hmain :
      G.degree u + G.degree v + nonNbrsOfUInNonNbrsV.card =
        24 + (G.neighborFinset u ∩ G.neighborFinset v).card := by
    have hVSide := hVTotal
    rw [← hsideTotal] at hVSide
    rw [hsplit]
    omega
  simpa [nonNbrsV, nonNbrsOfUInNonNbrsV] using hmain

/-- A non-neighbor sees at least `degree(v) - 8` vertices inside `v`'s neighborhood. -/
theorem degree_sub_eight_le_common_neighbor_card_of_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : ¬ G.Adj u v) :
    G.degree v - 8 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  let nonNbrsOfUInNv : Finset α := (G.neighborFinset v).filter (fun w => ¬ G.Adj u w)
  have hpart :
      (G.neighborFinset u ∩ G.neighborFinset v).card + nonNbrsOfUInNv.card =
        (G.neighborFinset v).card := by
    have hcommon :
        G.neighborFinset u ∩ G.neighborFinset v =
          (G.neighborFinset v).filter (G.Adj u) := by
      ext w
      constructor
      · intro hw
        rcases Finset.mem_inter.mp hw with ⟨hwu, hwv⟩
        exact Finset.mem_filter.mpr ⟨hwv, (G.mem_neighborFinset u w).mp hwu⟩
      · intro hw
        rcases Finset.mem_filter.mp hw with ⟨hwv, huw⟩
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u w).mpr huw, hwv⟩
    rw [hcommon]
    simpa [nonNbrsOfUInNv] using
      (Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (p := G.Adj u))
  have hNvCard : (G.neighborFinset v).card = G.degree v := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hNonNbrsLe : nonNbrsOfUInNv.card ≤ 8 := by
    have hlt : nonNbrsOfUInNv.card < 9 := by
      refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_three_four_nine G
        nonNbrsOfUInNv ?_ ?_
      · rintro ⟨t, htNon, htClique⟩
        exact hnoK4 ⟨insert v t, htClique.insert (by
          intro w hw
          have hwNon := htNon hw
          simp only [nonNbrsOfUInNv, Finset.mem_filter] at hwNon
          exact (G.mem_neighborFinset v w).mp hwNon.1)⟩
      · rintro ⟨t, htNon, htIndep⟩
        exact hnoI5 ⟨insert u t, by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          refine htIndep.insert ?_
          intro w hw
          have hwNon := htNon hw
          simp only [nonNbrsOfUInNv, Finset.mem_filter] at hwNon
          have huw_ne : u ≠ w := by
            intro huw_eq
            subst w
            exact huv ((G.mem_neighborFinset v u).mp hwNon.1).symm
          exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, hwNon.2⟩⟩
    exact Nat.le_of_lt_succ hlt
  omega

/--
A non-neighbor sees at least `16 - degree(v)` vertices on `v`'s non-neighborhood side in a
26-vertex counterexample.
-/
theorem sixteen_sub_degree_le_neighbor_in_nonNeighborFinset_card_of_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) :
    16 - G.degree v ≤
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (fun w => ¬ G.Adj u w)
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  have huNonNbrsV : u ∈ nonNbrsV := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv_ne, by simp⟩, hvu⟩
  have hpart :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card =
        (nonNbrsV.erase u).card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV.erase u) (p := G.Adj u))
  have hNonNbrsVCard : nonNbrsV.card = 25 - G.degree v := by
    have hpartV :
        (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
      have hneighbor :
          G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
        ext w
        by_cases hwv : w = v
        · subst w
          simp
        · simp [hwv]
      rw [hneighbor]
      simpa [nonNbrsV] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    have hneighborCard : (G.neighborFinset v).card = G.degree v := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have htotal : (nonNbrsV.erase u).card = 24 - G.degree v := by
    rw [Finset.card_erase_of_mem huNonNbrsV, hNonNbrsVCard]
    omega
  have hNonNbrsLe : nonNbrsOfUInNonNbrsV.card ≤ 8 := by
    have hlt : nonNbrsOfUInNonNbrsV.card < 9 := by
      refine card_lt_of_no_clique_or_indep
        (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G
        nonNbrsOfUInNonNbrsV ?_ ?_
      · rintro ⟨t, _htNon, htClique⟩
        exact hnoK4 ⟨t, htClique⟩
      · rintro ⟨t, htNon, htIndep⟩
        exact hnoI5 ⟨insert u (insert v t), by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          have hCliqueWithV : Gᶜ.IsNClique 4 (insert v t) := by
            refine htIndep.insert ?_
            intro w hw
            have hwNon := htNon hw
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            have hwNonNbrsV : w ∈ nonNbrsV := (Finset.mem_erase.mp hwNon.1).2
            simp only [nonNbrsV, Finset.mem_filter] at hwNonNbrsV
            rcases hwNonNbrsV with ⟨hwErase, hvw⟩
            have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩
          refine hCliqueWithV.insert ?_
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwt
          · exact (SimpleGraph.compl_adj _ _ _).2 ⟨huv_ne, huv⟩
          · have hwNon := htNon hwt
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            rcases hwNon with ⟨hwErase, huw⟩
            have huw_ne : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, huw⟩⟩
    exact Nat.le_of_lt_succ hlt
  simpa [nonNbrsV, nbrsOfUInNonNbrsV] using (by omega : 16 - G.degree v ≤ nbrsOfUInNonNbrsV.card)

/--
If a degree-`8` vertex is nonadjacent to a degree-`13` vertex, then its degree splits as exactly
`5 + 3` across the degree-`13` vertex's neighborhood and non-neighborhood sides.
-/
theorem neighbor_counts_eq_of_degree_eight_nonadjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v)
    (hdegu : G.degree u = 8) (hdegv : G.degree v = 13) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 5 ∧
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card = 3 := by
  have hN :
      5 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card :=
    five_le_neighbor_inter_neighborFinset_card_of_degree_thirteen_nonadjacent
      G hnoK4 hnoI5 huv hdegv
  have hM :
      3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card :=
    three_le_neighbor_in_nonNeighborFinset_card_of_degree_thirteen_nonadjacent
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  have hsum :
      (G.neighborFinset u ∩ G.neighborFinset v).card +
        (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
          (G.Adj u)).card = 8 := by
    rw [← degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
      G huv, hdegu]
  constructor <;> omega

/-- Split the degree of a vertex across a neighbor's neighborhood and non-neighborhood. -/
theorem degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v : α} (huv : G.Adj u v) :
    G.degree u =
      1 + (G.neighborFinset u ∩ G.neighborFinset v).card +
        (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := nonNbrsV.filter (G.Adj u)
  have hvIn : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
  have hcommon :
      ((G.neighborFinset u).erase v).filter (G.Adj v) =
        G.neighborFinset u ∩ G.neighborFinset v := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, hvw⟩
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_erase.mp hwErase).2, (G.mem_neighborFinset v w).mpr hvw⟩
    · intro hw
      rcases Finset.mem_inter.mp hw with ⟨hwu, hwv⟩
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hwv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hvw.ne.symm, hwu⟩, hvw⟩
  have hnon :
      ((G.neighborFinset u).erase v).filter (fun w => ¬ G.Adj v w) =
        nbrsOfUInNonNbrsV := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, hvw⟩
      have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (Finset.mem_erase.mp hwErase).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hwErase).1, by simp⟩, hvw⟩,
          huw⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwNonNbrsV, huw⟩
      rcases Finset.mem_filter.mp hwNonNbrsV with ⟨hwEraseV, hvw⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hwEraseV).1, (G.mem_neighborFinset u w).mpr huw⟩,
          hvw⟩
  have hpart :
      (((G.neighborFinset u).erase v).filter (G.Adj v)).card +
        (((G.neighborFinset u).erase v).filter (fun w => ¬ G.Adj v w)).card =
          ((G.neighborFinset u).erase v).card := by
    simpa using
      (Finset.card_filter_add_card_filter_not (s := (G.neighborFinset u).erase v)
        (p := G.Adj v))
  have hcard :
      (G.neighborFinset u).card = ((G.neighborFinset u).erase v).card + 1 := by
    have hpos : 0 < (G.neighborFinset u).card := Finset.card_pos.mpr ⟨v, hvIn⟩
    have herase :
        ((G.neighborFinset u).erase v).card = (G.neighborFinset u).card - 1 :=
      Finset.card_erase_of_mem hvIn
    rw [herase]
    omega
  calc
    G.degree u = (G.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ = ((G.neighborFinset u).erase v).card + 1 := hcard
    _ =
        (((G.neighborFinset u).erase v).filter (G.Adj v)).card +
          (((G.neighborFinset u).erase v).filter (fun w => ¬ G.Adj v w)).card + 1 := by
            rw [hpart]
     _ = 1 + (G.neighborFinset u ∩ G.neighborFinset v).card +
        (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card := by
             rw [hcommon, hnon]
             simp [nbrsOfUInNonNbrsV, nonNbrsV, Nat.add_assoc, Nat.add_comm]

/--
For a degree-`13` vertex, any non-neighbor has between `5` and `10` neighbors in its
neighborhood side, and between `3` and `8` neighbors in its non-neighborhood side.
-/
theorem neighbor_count_bounds_of_nonadjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 13) :
    5 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card ∧
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 10 ∧
      3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card ∧
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card ≤ 8 := by
  have hN :
      5 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card :=
    five_le_neighbor_inter_neighborFinset_card_of_degree_thirteen_nonadjacent
      G hnoK4 hnoI5 huv hdegv
  have hM :
      3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card :=
    three_le_neighbor_in_nonNeighborFinset_card_of_degree_thirteen_nonadjacent
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  have hdegLe : G.degree u ≤ 13 :=
    (degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five_unconditional
      G hcard hnoK4 hnoI5 u).2
  have hsum :
      G.degree u =
        (G.neighborFinset u ∩ G.neighborFinset v).card +
          (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
            (G.Adj u)).card :=
    degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
      G huv
  constructor
  · exact hN
  constructor
  · omega
  constructor
  · exact hM
  · omega

/--
For a degree-`13` vertex, summing over its non-neighborhood gives at least five incident edges
back into the neighborhood per non-neighbor.
-/
theorem five_mul_nonNeighborFinset_card_le_sum_common_neighbor_card_of_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {v : α} (hdegv : G.degree v = 13) :
    5 * ((Finset.univ.erase v).filter (fun u => ¬ G.Adj v u)).card ≤
      Finset.sum ((Finset.univ.erase v).filter (fun u => ¬ G.Adj v u))
        (fun u => (G.neighborFinset u ∩ G.neighborFinset v).card) := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun u => ¬ G.Adj v u)
  have hconst :
      Finset.sum nonNbrsV (fun _ => 5) = 5 * nonNbrsV.card := by
    simp [Nat.mul_comm]
  rw [← hconst]
  exact Finset.sum_le_sum (by
    intro u hu
    have huv : ¬ G.Adj u v := by
      intro huv
      exact (Finset.mem_filter.mp hu).2 huv.symm
    exact five_le_neighbor_inter_neighborFinset_card_of_degree_thirteen_nonadjacent
      G hnoK4 hnoI5 huv hdegv)

/--
For a degree-`13` vertex, any neighbor has exactly four common neighbors and between `3` and
`8` neighbors on the non-neighborhood side.
-/
theorem neighbor_count_bounds_of_adjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegv : G.degree v = 13) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 4 ∧
      3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter
        (G.Adj u)).card ∧
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter
        (G.Adj u)).card ≤ 8 := by
  have hcommon :
      (G.neighborFinset u ∩ G.neighborFinset v).card = 4 :=
    common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
      G hnoK4 hnoI5 huv hdegv
  have hdegBounds :=
    degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five_unconditional
      G hcard hnoK4 hnoI5 u
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  constructor
  · exact hcommon
  constructor <;> omega

/--
If a degree-`8` vertex is adjacent to a degree-`13` vertex, then it has exactly three neighbors
on the degree-`13` vertex's non-neighborhood side.
-/
theorem neighbor_in_nonNeighborFinset_card_eq_three_of_degree_eight_adjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegu : G.degree u = 8) (hdegv : G.degree v = 13) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card = 3 := by
  have hcommon :
      (G.neighborFinset u ∩ G.neighborFinset v).card = 4 :=
    common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
      G hnoK4 hnoI5 huv hdegv
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  omega

/--
If a degree-`13` vertex is adjacent to any vertex, then it has exactly eight neighbors on that
vertex's non-neighborhood side.
-/
theorem neighbor_in_nonNeighborFinset_card_eq_eight_of_degree_thirteen_adjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegu : G.degree u = 13) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card = 8 := by
  have hcommonRev :
      (G.neighborFinset v ∩ G.neighborFinset u).card = 4 :=
    common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
      G hnoK4 hnoI5 huv.symm hdegu
  have hcommon :
      (G.neighborFinset u ∩ G.neighborFinset v).card = 4 := by
    simpa [Finset.inter_comm] using hcommonRev
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  omega

/-- Two adjacent degree-`13` vertices have exactly four common non-neighbors. -/
theorem common_non_neighbor_card_eq_four_of_adjacent_degree_thirteen_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegu : G.degree u = 13)
    (hdegv : G.degree v = 13) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter
      (fun w => ¬ G.Adj u w)).card = 4 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := nonNbrsV.filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := nonNbrsV.filter (fun w => ¬ G.Adj u w)
  have hpart :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card = nonNbrsV.card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV) (p := G.Adj u))
  have hNonNbrsVCard : nonNbrsV.card = 12 := by
    simpa [nonNbrsV] using
      nonNeighborFinset_card_eq_twelve_of_card_twenty_six_degree_thirteen
        G hcard hdegv
  have hNbrsCard : nbrsOfUInNonNbrsV.card = 8 := by
    simpa [nonNbrsV, nbrsOfUInNonNbrsV] using
      neighbor_in_nonNeighborFinset_card_eq_eight_of_degree_thirteen_adjacent
        G hnoK4 hnoI5 huv hdegu
  have hNonNbrsCard : nonNbrsOfUInNonNbrsV.card = 4 := by omega
  simpa [nonNbrsV, nonNbrsOfUInNonNbrsV] using hNonNbrsCard

/-- In any 26-vertex counterexample, a neighbor has at least three edges to the other side. -/
theorem three_le_neighbor_in_nonNeighborFinset_card_of_adjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) :
    3 ≤ (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card := by
  have hdegLower :
      8 ≤ G.degree u :=
    (degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five_unconditional
      G hcard hnoK4 hnoI5 u).1
  have hcommonLe :
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 4 :=
    common_neighbor_card_le_four_of_no_clique_four_no_indep_five G hnoK4 hnoI5 huv
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  omega

/-- A neighbor has at least `degree - 5` edges to the other side of the cut. -/
theorem degree_sub_five_le_neighbor_in_nonNeighborFinset_card_of_adjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) :
    G.degree u - 5 ≤
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card := by
  have hcommonLe :
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 4 :=
    common_neighbor_card_le_four_of_no_clique_four_no_indep_five G hnoK4 hnoI5 huv
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  omega

/-- Summed over a whole neighborhood, every neighbor contributes at least three cross edges. -/
theorem three_mul_neighborFinset_card_le_sum_neighbor_in_nonNeighborFinset_card
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    3 * (G.neighborFinset v).card ≤
      Finset.sum (G.neighborFinset v)
        (fun u =>
          (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card) := by
  classical
  have hconst :
      Finset.sum (G.neighborFinset v) (fun _ => 3) = 3 * (G.neighborFinset v).card := by
    simp [Nat.mul_comm]
  rw [← hconst]
  exact Finset.sum_le_sum (by
    intro u hu
    have huv : G.Adj u v := ((G.mem_neighborFinset v u).mp hu).symm
    exact three_le_neighbor_in_nonNeighborFinset_card_of_adjacent
      G hcard hnoK4 hnoI5 huv)

/--
If `v` has degree `13` and `u` is adjacent to it, then `u`'s whole degree is five plus
the number of its edges to the non-neighborhood side of `v`.
-/
theorem degree_eq_five_add_neighbor_in_nonNeighborFinset_card_of_adjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegv : G.degree v = 13) :
    G.degree u =
      5 + (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card := by
  have hcommon :
      (G.neighborFinset u ∩ G.neighborFinset v).card = 4 :=
    common_neighbor_card_eq_four_of_degree_thirteen_no_clique_four_no_indep_five
      G hnoK4 hnoI5 huv hdegv
  have hsplit :=
    degree_eq_one_add_common_neighbor_add_neighbor_in_nonNeighborFinset_of_adjacent G huv
  omega

/-- A degree-`8` neighbor of a degree-`13` vertex is forced to have exactly three cross edges. -/
theorem neighbor_in_nonNeighborFinset_card_eq_three_of_adjacent_degree_eight_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegu : G.degree u = 8) (hdegv : G.degree v = 13) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card = 3 := by
  have hdeg :=
    degree_eq_five_add_neighbor_in_nonNeighborFinset_card_of_adjacent_degree_thirteen
      G hnoK4 hnoI5 huv hdegv
  omega

/--
For a neighbor of a degree-`13` vertex, the number of cross edges to the non-neighborhood side is
exactly `degree - 5`.
-/
theorem neighbor_in_nonNeighborFinset_card_eq_degree_sub_five_of_adjacent_degree_thirteen
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv : G.Adj u v) (hdegv : G.degree v = 13) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).filter (G.Adj u)).card =
      G.degree u - 5 := by
  have hdeg :=
    degree_eq_five_add_neighbor_in_nonNeighborFinset_card_of_adjacent_degree_thirteen
      G hnoK4 hnoI5 huv hdegv
  omega

/--
In any graph with no `4`-clique and no independent `5`-set, two distinct nonadjacent vertices have
at most eight common non-neighbors outside the pair.
-/
theorem common_non_neighbor_card_le_eight_of_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) :
    (((Finset.univ.erase u).erase v).filter
      (fun w => ¬ G.Adj u w ∧ ¬ G.Adj v w)).card ≤ 8 := by
  classical
  let commonNonNbrs : Finset α :=
    ((Finset.univ.erase u).erase v).filter (fun w => ¬ G.Adj u w ∧ ¬ G.Adj v w)
  have hlt : commonNonNbrs.card < 9 := by
    refine card_lt_of_no_clique_or_indep
      (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G
      commonNonNbrs ?_ ?_
    · rintro ⟨t, _htCommon, htClique⟩
      exact hnoK4 ⟨t, htClique⟩
    · rintro ⟨t, htCommon, htIndep⟩
      exact hnoI5 ⟨insert u (insert v t), by
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        have hCliqueWithV : Gᶜ.IsNClique 4 (insert v t) := by
          refine htIndep.insert ?_
          intro w hw
          have hwCommon := htCommon hw
          simp only [commonNonNbrs, Finset.mem_filter] at hwCommon
          rcases hwCommon with ⟨hwErase, _huw, hvw⟩
          have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
          exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩
        refine hCliqueWithV.insert ?_
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · exact (SimpleGraph.compl_adj _ _ _).2 ⟨huv_ne, huv⟩
        · have hwCommon := htCommon hwt
          simp only [commonNonNbrs, Finset.mem_filter] at hwCommon
          rcases hwCommon with ⟨hwErase, hnotu, _hnotv⟩
          have hwEraseU : w ∈ Finset.univ.erase u := (Finset.mem_erase.mp hwErase).2
          have hu_ne_w : u ≠ w := (Finset.mem_erase.mp hwEraseU).1.symm
          exact (SimpleGraph.compl_adj _ _ _).2 ⟨hu_ne_w, hnotu⟩⟩
  simpa [commonNonNbrs] using Nat.le_of_lt_succ hlt

/-- A nonadjacent pair has combined degree at least `16` plus its common-neighbor count. -/
theorem sixteen_add_common_neighbor_card_le_degree_add_degree_of_nonadjacent
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) :
    16 + (G.neighborFinset u ∩ G.neighborFinset v).card ≤ G.degree u + G.degree v := by
  classical
  let commonNonNbrsInV : Finset α :=
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u).filter
      (fun w => ¬ G.Adj u w)
  have hNNle : commonNonNbrsInV.card ≤ 8 := by
    have hlt : commonNonNbrsInV.card < 9 := by
      refine card_lt_of_no_clique_or_indep
        (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G
        commonNonNbrsInV ?_ ?_
      · rintro ⟨t, _htCommon, htClique⟩
        exact hnoK4 ⟨t, htClique⟩
      · rintro ⟨t, htCommon, htIndep⟩
        exact hnoI5 ⟨insert u (insert v t), by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          have hCliqueWithV : Gᶜ.IsNClique 4 (insert v t) := by
            refine htIndep.insert ?_
            intro w hw
            have hwCommon := htCommon hw
            simp only [commonNonNbrsInV, Finset.mem_filter] at hwCommon
            rcases hwCommon with ⟨hwEraseU, _huw⟩
            have hwNonV : w ∈ (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) :=
              (Finset.mem_erase.mp hwEraseU).2
            rcases Finset.mem_filter.mp hwNonV with ⟨hwEraseV, hvw⟩
            have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwEraseV).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩
          refine hCliqueWithV.insert ?_
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwt
          · exact (SimpleGraph.compl_adj _ _ _).2 ⟨huv_ne, huv⟩
          · have hwCommon := htCommon hwt
            simp only [commonNonNbrsInV, Finset.mem_filter] at hwCommon
            rcases hwCommon with ⟨hwEraseU, huw⟩
            have hu_ne_w : u ≠ w := (Finset.mem_erase.mp hwEraseU).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨hu_ne_w, huw⟩⟩
    exact Nat.le_of_lt_succ hlt
  have hpartition :
      G.degree u + G.degree v + commonNonNbrsInV.card =
        24 + (G.neighborFinset u ∩ G.neighborFinset v).card := by
    simpa [commonNonNbrsInV] using
      degree_add_degree_add_common_non_neighbor_card_eq_twenty_four_add_common_neighbor_card_of_nonadjacent
        G hcard huv_ne huv
  omega

/--
If a vertex has degree `8` in a `26`-vertex graph with no `4`-clique and no independent `5`-set,
then every non-neighbor has exactly eight common non-neighbors with it inside the non-neighborhood
of the degree-`8` vertex.
-/
theorem common_non_neighbor_in_nonNeighborhood_card_eq_eight_of_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 8) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
      (fun w => ¬ G.Adj u w)).card = 8 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (fun w => ¬ G.Adj u w)
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  have huNonNbrsV : u ∈ nonNbrsV := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv_ne, by simp⟩, hvu⟩
  have hpart :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card =
        (nonNbrsV.erase u).card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV.erase u) (p := G.Adj u))
  have hNonNbrsVCard : nonNbrsV.card = 17 := by
    have hpartV :
        (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
      have hneighbor :
          G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
        ext w
        by_cases hwv : w = v
        · subst w
          simp
        · simp [hwv]
      rw [hneighbor]
      simpa [nonNbrsV] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    have hneighborCard : (G.neighborFinset v).card = 8 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
    omega
  have htotal : (nonNbrsV.erase u).card = 16 := by
    rw [Finset.card_erase_of_mem huNonNbrsV, hNonNbrsVCard]
  have hNbrsLt : nbrsOfUInNonNbrsV.card < 9 := by
    refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_three_four_nine G
      nbrsOfUInNonNbrsV ?_ ?_
    · rintro ⟨t, htNbrs, htClique⟩
      exact hnoK4 ⟨insert u t, htClique.insert (by
        intro w hw
        have hwNbrs := htNbrs hw
        simp only [nbrsOfUInNonNbrsV, Finset.mem_filter] at hwNbrs
        exact hwNbrs.2)⟩
    · rintro ⟨t, htNbrs, htIndep⟩
      exact hnoI5 ⟨insert v t, by
        rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
        refine htIndep.insert ?_
        intro w hw
        have hwNbrs := htNbrs hw
        simp only [nbrsOfUInNonNbrsV, Finset.mem_filter] at hwNbrs
        have hwNonNbrsV : w ∈ nonNbrsV := (Finset.mem_erase.mp hwNbrs.1).2
        simp only [nonNbrsV, Finset.mem_filter] at hwNonNbrsV
        rcases hwNonNbrsV with ⟨hwErase, hvw⟩
        have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
        exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩⟩
  have hNonNbrsLe : nonNbrsOfUInNonNbrsV.card ≤ 8 := by
    have hlt :
        nonNbrsOfUInNonNbrsV.card < 9 := by
      refine card_lt_of_no_clique_or_indep
        (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G
        nonNbrsOfUInNonNbrsV ?_ ?_
      · rintro ⟨t, _htNon, htClique⟩
        exact hnoK4 ⟨t, htClique⟩
      · rintro ⟨t, htNon, htIndep⟩
        exact hnoI5 ⟨insert u (insert v t), by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          have hCliqueWithV : Gᶜ.IsNClique 4 (insert v t) := by
            refine htIndep.insert ?_
            intro w hw
            have hwNon := htNon hw
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            have hwNonNbrsV : w ∈ nonNbrsV := (Finset.mem_erase.mp hwNon.1).2
            simp only [nonNbrsV, Finset.mem_filter] at hwNonNbrsV
            rcases hwNonNbrsV with ⟨hwErase, hvw⟩
            have hvw_ne : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvw_ne, hvw⟩
          refine hCliqueWithV.insert ?_
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hwt
          · exact (SimpleGraph.compl_adj _ _ _).2 ⟨huv_ne, huv⟩
          · have hwNon := htNon hwt
            simp only [nonNbrsOfUInNonNbrsV, Finset.mem_filter] at hwNon
            rcases hwNon with ⟨hwErase, huw⟩
            have huw_ne : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
            exact (SimpleGraph.compl_adj _ _ _).2 ⟨huw_ne, huw⟩⟩
    exact Nat.le_of_lt_succ hlt
  have hNonNbrsGe : 8 ≤ nonNbrsOfUInNonNbrsV.card := by omega
  have hEq : nonNbrsOfUInNonNbrsV.card = 8 := le_antisymm hNonNbrsLe hNonNbrsGe
  simpa [nonNbrsV, nonNbrsOfUInNonNbrsV] using hEq

/--
The non-neighborhood of a degree-`8` vertex in a `26`-vertex no-`K₄`/no-independent-`5`
graph is a regular induced graph of degree `8`.
-/
theorem nonNeighborFinset_isRegularOfDegree_eight_of_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {v : α} (hdegv : G.degree v = 8) :
    (inducedOn G ((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w))).IsRegularOfDegree 8 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  intro u
  let nbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (G.Adj u)
  let nonNbrsOfUInNonNbrsV : Finset α := (nonNbrsV.erase u).filter (fun w => ¬ G.Adj u w)
  have huNonNbrsV : (u : α) ∈ nonNbrsV := u.2
  have huv_ne : (u : α) ≠ v := by
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp huNonNbrsV).1).1
  have huv : ¬ G.Adj (u : α) v := by
    intro huv
    exact (Finset.mem_filter.mp huNonNbrsV).2 huv.symm
  have hNbrs :
      G.neighborFinset (u : α) ∩ nonNbrsV = nbrsOfUInNonNbrsV := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_inter.mp hw with ⟨hwu, hwNonNbrsV⟩
      have huw : G.Adj (u : α) w := (G.mem_neighborFinset (u : α) w).mp hwu
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨huw.ne.symm, hwNonNbrsV⟩, huw⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, huw⟩
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset (u : α) w).mpr huw, (Finset.mem_erase.mp hwErase).2⟩
  have hpart :
      nbrsOfUInNonNbrsV.card + nonNbrsOfUInNonNbrsV.card =
        (nonNbrsV.erase u).card := by
    simpa [nbrsOfUInNonNbrsV, nonNbrsOfUInNonNbrsV] using
      (Finset.card_filter_add_card_filter_not (s := nonNbrsV.erase u) (p := G.Adj (u : α)))
  have hNonNbrsVCard : nonNbrsV.card = 17 := by
    have hpartV :
        (G.neighborFinset v).card + nonNbrsV.card = (Finset.univ.erase v).card := by
      have hneighbor :
          G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
        ext w
        by_cases hwv : w = v
        · subst w
          simp
        · simp [hwv]
      rw [hneighbor]
      simpa [nonNbrsV] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    have hneighborCard : (G.neighborFinset v).card = 8 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
    omega
  have htotal : (nonNbrsV.erase u).card = 16 := by
    rw [Finset.card_erase_of_mem huNonNbrsV, hNonNbrsVCard]
  have hNonNbrsEq : nonNbrsOfUInNonNbrsV.card = 8 := by
    simpa [nonNbrsV, nonNbrsOfUInNonNbrsV] using
      common_non_neighbor_in_nonNeighborhood_card_eq_eight_of_degree_eight
        G hcard hnoK4 hnoI5 huv_ne huv hdegv
  have hNbrsCard : nbrsOfUInNonNbrsV.card = 8 := by omega
  rw [inducedOn_degree_eq_card_neighborFinset_inter, hNbrs]
  exact hNbrsCard

/--
Every non-neighbor of a degree-`8` vertex has exactly eight neighbors inside that vertex's
non-neighborhood.
-/
theorem neighbor_in_nonNeighborFinset_card_eq_eight_of_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 8) :
    (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
      (G.Adj u)).card = 8 := by
  classical
  let nonNbrsV : Finset α := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  have huNonNbrsV : u ∈ nonNbrsV := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨huv_ne, by simp⟩, hvu⟩
  have hNbrs :
      G.neighborFinset u ∩ nonNbrsV = (nonNbrsV.erase u).filter (G.Adj u) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_inter.mp hw with ⟨hwu, hwNonNbrsV⟩
      have huw : G.Adj u w := (G.mem_neighborFinset u w).mp hwu
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨huw.ne.symm, hwNonNbrsV⟩, huw⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwErase, huw⟩
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u w).mpr huw, (Finset.mem_erase.mp hwErase).2⟩
  have hreg :=
    nonNeighborFinset_isRegularOfDegree_eight_of_degree_eight G hcard hnoK4 hnoI5 hdegv
  have hInternal :
      (G.neighborFinset u ∩ nonNbrsV).card = 8 := by
    have hdeg := hreg ⟨u, huNonNbrsV⟩
    rw [inducedOn_degree_eq_card_neighborFinset_inter] at hdeg
    simpa [nonNbrsV] using hdeg
  simpa [nonNbrsV, hNbrs] using hInternal

/--
If a degree-`13` vertex is nonadjacent to a degree-`8` vertex, then its degree splits as exactly
`5 + 8` across the degree-`8` vertex's neighborhood and non-neighborhood sides.
-/
theorem neighbor_counts_eq_of_degree_thirteen_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v)
    (hdegu : G.degree u = 13) (hdegv : G.degree v = 8) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 5 ∧
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card = 8 := by
  have hside :
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card = 8 :=
    neighbor_in_nonNeighborFinset_card_eq_eight_of_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  have hsplit :=
    degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
      G huv
  constructor
  · omega
  · exact hside

/--
If `v` has degree `8`, every non-neighbor `u` has degree equal to eight plus its common-neighbor
count with `v`.
-/
theorem degree_eq_eight_add_common_neighbor_card_of_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 8) :
    G.degree u = (G.neighborFinset u ∩ G.neighborFinset v).card + 8 := by
  have hside :
      (((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).erase u |>.filter
        (G.Adj u)).card = 8 :=
    neighbor_in_nonNeighborFinset_card_eq_eight_of_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  have hsplit :=
    degree_eq_neighbor_inter_neighborFinset_add_neighbor_in_nonNeighborFinset_of_nonadjacent
      G huv
  omega

/-- A non-neighbor of a degree-`8` vertex has at most five common neighbors with it. -/
theorem common_neighbor_card_le_five_of_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 8) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 5 := by
  have hdegUpper :
      G.degree u ≤ 13 :=
    (degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five_unconditional
      G hcard hnoK4 hnoI5 u).2
  have hdeg :=
    degree_eq_eight_add_common_neighbor_card_of_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  omega

/-- Nonadjacent degree-`8` vertices have no common neighbors. -/
theorem common_neighbor_card_eq_zero_of_nonadjacent_degree_eight_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v)
    (hdegu : G.degree u = 8) (hdegv : G.degree v = 8) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 0 := by
  have hdeg :=
    degree_eq_eight_add_common_neighbor_card_of_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  omega

/--
For a non-neighbor of a degree-`8` vertex, the common-neighbor count is exactly `degree - 8`.
-/
theorem common_neighbor_card_eq_degree_sub_eight_of_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v : α} (huv_ne : u ≠ v) (huv : ¬ G.Adj u v) (hdegv : G.degree v = 8) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = G.degree u - 8 := by
  have hdeg :=
    degree_eq_eight_add_common_neighbor_card_of_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegv
  omega

/-- Two degree-`8` vertices with a common neighbor must be adjacent. -/
theorem adj_of_common_neighbor_degree_eight_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {u v w : α} (huv_ne : u ≠ v)
    (hdegu : G.degree u = 8) (hdegv : G.degree v = 8)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    G.Adj u v := by
  by_contra huv
  have hzero :
      (G.neighborFinset u ∩ G.neighborFinset v).card = 0 :=
    common_neighbor_card_eq_zero_of_nonadjacent_degree_eight_degree_eight
      G hcard hnoK4 hnoI5 huv_ne huv hdegu hdegv
  have hwCommon : w ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset u w).mpr huw, (G.mem_neighborFinset v w).mpr hvw⟩
  have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨w, hwCommon⟩
  omega

/-- The degree-`8` neighbors of any fixed vertex form a clique. -/
theorem degree_eight_neighbors_isClique
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (w : α) :
    G.IsClique (((G.neighborFinset w).filter (fun u => G.degree u = 8)) : Set α) := by
  rw [SimpleGraph.isClique_iff]
  intro a ha b hb hab
  rcases Finset.mem_filter.mp ha with ⟨haw_mem, hdega⟩
  rcases Finset.mem_filter.mp hb with ⟨hbw_mem, hdegb⟩
  have haw : G.Adj a w := ((G.mem_neighborFinset w a).mp haw_mem).symm
  have hbw : G.Adj b w := ((G.mem_neighborFinset w b).mp hbw_mem).symm
  exact adj_of_common_neighbor_degree_eight_degree_eight
    G hcard hnoK4 hnoI5 hab hdega hdegb haw hbw

/-- A two-step path among degree-`8` vertices must close to a triangle. -/
theorem degree_eight_two_step_path_closes
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {a b c : α} (hac_ne : a ≠ c)
    (hdega : G.degree a = 8) (hdegc : G.degree c = 8)
    (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.Adj a c :=
  adj_of_common_neighbor_degree_eight_degree_eight
    G hcard hnoK4 hnoI5 hac_ne hdega hdegc hab hbc.symm

/-- No vertex in a hypothetical 26-vertex counterexample has four degree-`8` neighbors. -/
theorem degree_eight_neighborFinset_card_le_three
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (w : α) :
    ((G.neighborFinset w).filter (fun u => G.degree u = 8)).card ≤ 3 := by
  classical
  by_contra hle
  have hfour : 4 ≤ ((G.neighborFinset w).filter (fun u => G.degree u = 8)).card := by
    omega
  rcases Finset.exists_subset_card_eq
      (s := (G.neighborFinset w).filter (fun u => G.degree u = 8)) (n := 4) hfour with
    ⟨t, ht, htcard⟩
  exact hnoK4 ⟨t, by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      have ha' := ht ha
      have hb' := ht hb
      rcases Finset.mem_filter.mp ha' with ⟨haw_mem, hdega⟩
      rcases Finset.mem_filter.mp hb' with ⟨hbw_mem, hdegb⟩
      have haw : G.Adj a w := ((G.mem_neighborFinset w a).mp haw_mem).symm
      have hbw : G.Adj b w := ((G.mem_neighborFinset w b).mp hbw_mem).symm
      exact adj_of_common_neighbor_degree_eight_degree_eight
        G hcard hnoK4 hnoI5 hab hdega hdegb haw hbw
    · exact htcard⟩

/-- A degree-`8` vertex has at most two degree-`8` neighbors. -/
theorem degree_eight_neighborFinset_card_le_two_of_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {v : α} (hdegv : G.degree v = 8) :
    ((G.neighborFinset v).filter (fun u => G.degree u = 8)).card ≤ 2 := by
  classical
  by_contra hle
  have hthree : 3 ≤ ((G.neighborFinset v).filter (fun u => G.degree u = 8)).card := by
    omega
  rcases Finset.exists_subset_card_eq
      (s := (G.neighborFinset v).filter (fun u => G.degree u = 8)) (n := 3) hthree with
    ⟨t, ht, htcard⟩
  have htClique : G.IsNClique 3 t := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      have ha' := ht ha
      have hb' := ht hb
      rcases Finset.mem_filter.mp ha' with ⟨hav_mem, hdega⟩
      rcases Finset.mem_filter.mp hb' with ⟨hbv_mem, hdegb⟩
      have hav : G.Adj a v := ((G.mem_neighborFinset v a).mp hav_mem).symm
      have hbv : G.Adj b v := ((G.mem_neighborFinset v b).mp hbv_mem).symm
      exact adj_of_common_neighbor_degree_eight_degree_eight
        G hcard hnoK4 hnoI5 hab hdega hdegb hav hbv
    · exact htcard
  exact hnoK4 ⟨insert v t, htClique.insert (by
    intro u hu
    have hu' := ht hu
    exact (G.mem_neighborFinset v u).mp (Finset.mem_filter.mp hu').1)⟩

/-- Three pairwise nonadjacent degree-`8` vertices cannot occur in a 26-vertex counterexample. -/
theorem not_three_pairwise_nonadjacent_degree_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    {a b c : α} (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c)
    (hdega : G.degree a = 8) (hdegb : G.degree b = 8) (hdegc : G.degree c = 8)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c) (hbc : ¬ G.Adj b c) :
    False := by
  classical
  let NA : Finset α := G.neighborFinset a
  let NB : Finset α := G.neighborFinset b
  let NC : Finset α := G.neighborFinset c
  let S : Finset α := (NA ∪ NB) ∪ NC
  have hNAcard : NA.card = 8 := by
    simpa [NA, SimpleGraph.card_neighborFinset_eq_degree] using hdega
  have hNBcard : NB.card = 8 := by
    simpa [NB, SimpleGraph.card_neighborFinset_eq_degree] using hdegb
  have hNCcard : NC.card = 8 := by
    simpa [NC, SimpleGraph.card_neighborFinset_eq_degree] using hdegc
  have hABzero : (NA ∩ NB).card = 0 := by
    simpa [NA, NB] using
      common_neighbor_card_eq_zero_of_nonadjacent_degree_eight_degree_eight
        G hcard hnoK4 hnoI5 hab_ne hab hdega hdegb
  have hACzero : (NA ∩ NC).card = 0 := by
    simpa [NA, NC] using
      common_neighbor_card_eq_zero_of_nonadjacent_degree_eight_degree_eight
        G hcard hnoK4 hnoI5 hac_ne hac hdega hdegc
  have hBCzero : (NB ∩ NC).card = 0 := by
    simpa [NB, NC] using
      common_neighbor_card_eq_zero_of_nonadjacent_degree_eight_degree_eight
        G hcard hnoK4 hnoI5 hbc_ne hbc hdegb hdegc
  have hABdis : Disjoint NA NB := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx : x ∈ NA ∩ NB := Finset.mem_inter.mpr ⟨hxA, hxB⟩
    have hpos : 0 < (NA ∩ NB).card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hACdis : Disjoint NA NC := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hx : x ∈ NA ∩ NC := Finset.mem_inter.mpr ⟨hxA, hxC⟩
    have hpos : 0 < (NA ∩ NC).card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hBCdis : Disjoint NB NC := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    have hx : x ∈ NB ∩ NC := Finset.mem_inter.mpr ⟨hxB, hxC⟩
    have hpos : 0 < (NB ∩ NC).card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hAB_C_dis : Disjoint (NA ∪ NB) NC := by
    rw [Finset.disjoint_left]
    intro x hxAB hxC
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact (Finset.disjoint_left.mp hACdis hxA) hxC
    · exact (Finset.disjoint_left.mp hBCdis hxB) hxC
  have hSCard : S.card = 24 := by
    have hABCard : (NA ∪ NB).card = 16 := by
      rw [Finset.card_union_of_disjoint hABdis, hNAcard, hNBcard]
    rw [show S = (NA ∪ NB) ∪ NC from rfl]
    rw [Finset.card_union_of_disjoint hAB_C_dis, hABCard, hNCcard]
  have haS : a ∉ S := by
    intro haS
    rcases Finset.mem_union.mp haS with hABmem | haNC
    · rcases Finset.mem_union.mp hABmem with haNA | haNB
      · exact ((G.mem_neighborFinset a a).mp (by simpa [NA] using haNA)).ne rfl
      · exact hab (((G.mem_neighborFinset b a).mp (by simpa [NB] using haNB)).symm)
    · exact hac (((G.mem_neighborFinset c a).mp (by simpa [NC] using haNC)).symm)
  have hbS : b ∉ S := by
    intro hbS
    rcases Finset.mem_union.mp hbS with hABmem | hbNC
    · rcases Finset.mem_union.mp hABmem with hbNA | hbNB
      · exact hab ((G.mem_neighborFinset a b).mp (by simpa [NA] using hbNA))
      · exact ((G.mem_neighborFinset b b).mp (by simpa [NB] using hbNB)).ne rfl
    · exact hbc (((G.mem_neighborFinset c b).mp (by simpa [NC] using hbNC)).symm)
  have hcS : c ∉ S := by
    intro hcS
    rcases Finset.mem_union.mp hcS with hABmem | hcNC
    · rcases Finset.mem_union.mp hABmem with hcNA | hcNB
      · exact hac ((G.mem_neighborFinset a c).mp (by simpa [NA] using hcNA))
      · exact hbc ((G.mem_neighborFinset b c).mp (by simpa [NB] using hcNB))
    · exact ((G.mem_neighborFinset c c).mp (by simpa [NC] using hcNC)).ne rfl
  let T : Finset α := insert a (insert b (insert c S))
  have hc_not : c ∉ S := hcS
  have hb_not : b ∉ insert c S := by
    simpa [hbc_ne, hbS]
  have ha_not : a ∉ insert b (insert c S) := by
    simpa [hab_ne, hac_ne, haS]
  have hTcard : T.card = 27 := by
    rw [show T = insert a (insert b (insert c S)) from rfl]
    rw [Finset.card_insert_of_notMem ha_not, Finset.card_insert_of_notMem hb_not,
      Finset.card_insert_of_notMem hc_not, hSCard]
  have hTle : T.card ≤ (Finset.univ : Finset α).card := by
    exact Finset.card_le_card (by intro x _hx; simp)
  rw [Finset.card_univ, hcard, hTcard] at hTle
  omega

/-- There are at most eight degree-`8` vertices in a 26-vertex counterexample. -/
theorem degree_eight_vertices_card_le_eight
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t) :
    ((Finset.univ : Finset α).filter (fun v => G.degree v = 8)).card ≤ 8 := by
  classical
  let D8 : Finset α := (Finset.univ : Finset α).filter (fun v => G.degree v = 8)
  have hlt : D8.card < 9 := by
    refine card_lt_of_no_clique_or_indep
      (HasCliqueOrIndepSetBound.symm hasCliqueOrIndepSetBound_three_four_nine) G D8 ?_ ?_
    · rintro ⟨t, _htD8, htClique⟩
      exact hnoK4 ⟨t, htClique⟩
    · rintro ⟨t, htD8, htIndep⟩
      rcases Finset.card_eq_three.mp htIndep.card_eq with ⟨a, b, c, hab_ne, hac_ne, hbc_ne, rfl⟩
      have hdega : G.degree a = 8 := by
        exact (Finset.mem_filter.mp (htD8 (by simp))).2
      have hdegb : G.degree b = 8 := by
        exact (Finset.mem_filter.mp (htD8 (by simp [hab_ne.symm]))).2
      have hdegc : G.degree c = 8 := by
        exact (Finset.mem_filter.mp (htD8 (by simp [hac_ne.symm, hbc_ne.symm]))).2
      have hab : ¬ G.Adj a b := htIndep.isIndepSet (by simp) (by simp [hab_ne.symm]) hab_ne
      have hac : ¬ G.Adj a c :=
        htIndep.isIndepSet (by simp) (by simp [hac_ne.symm, hbc_ne.symm]) hac_ne
      have hbc : ¬ G.Adj b c :=
        htIndep.isIndepSet (by simp [hab_ne.symm]) (by simp [hac_ne.symm, hbc_ne.symm]) hbc_ne
      exact not_three_pairwise_nonadjacent_degree_eight
        G hcard hnoK4 hnoI5 hab_ne hac_ne hbc_ne hdega hdegb hdegc hab hac hbc
  simpa [D8] using Nat.le_of_lt_succ hlt

/-- In fact there are at most six degree-`8` vertices in a 26-vertex counterexample. -/
theorem degree_eight_vertices_card_le_six
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t) :
    ((Finset.univ : Finset α).filter (fun v => G.degree v = 8)).card ≤ 6 := by
  classical
  let D8 : Finset α := (Finset.univ : Finset α).filter (fun v => G.degree v = 8)
  by_contra hle
  have hseven : 7 ≤ D8.card := by
    simpa [D8] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
  have hpos : 0 < D8.card := by omega
  rcases Finset.card_pos.mp hpos with ⟨a, haD8⟩
  have hdega : G.degree a = 8 := (Finset.mem_filter.mp haD8).2
  let A : Finset α := (D8.erase a).filter (G.Adj a)
  let B : Finset α := (D8.erase a).filter (fun b => ¬ G.Adj a b)
  have hpart : A.card + B.card = (D8.erase a).card := by
    simpa [A, B] using
      (Finset.card_filter_add_card_filter_not (s := D8.erase a) (p := G.Adj a))
  have hA_le : A.card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) <|
      degree_eight_neighborFinset_card_le_two_of_degree_eight G hcard hnoK4 hnoI5 hdega
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxErase, hax⟩
    have hxD8 : x ∈ D8 := (Finset.mem_erase.mp hxErase).2
    exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset a x).mpr hax, (Finset.mem_filter.mp hxD8).2⟩
  have hEraseCard : (D8.erase a).card = D8.card - 1 := Finset.card_erase_of_mem haD8
  have hBge : 4 ≤ B.card := by omega
  rcases hasCliqueOrIndepSetBound_four_two_four G B hBge with hClique | hIndep
  · rcases hClique with ⟨t, _htB, htClique⟩
    exact hnoK4 ⟨t, htClique⟩
  · rcases hIndep with ⟨t, htB, htIndep⟩
    rcases Finset.card_eq_two.mp htIndep.card_eq with ⟨b, c, hbc_ne, rfl⟩
    have hbB : b ∈ B := htB (by simp)
    have hcB : c ∈ B := htB (by simp [hbc_ne.symm])
    rcases Finset.mem_filter.mp hbB with ⟨hbErase, hab⟩
    rcases Finset.mem_filter.mp hcB with ⟨hcErase, hac⟩
    have hab_ne : a ≠ b := (Finset.mem_erase.mp hbErase).1.symm
    have hac_ne : a ≠ c := (Finset.mem_erase.mp hcErase).1.symm
    have hbD8 : b ∈ D8 := (Finset.mem_erase.mp hbErase).2
    have hcD8 : c ∈ D8 := (Finset.mem_erase.mp hcErase).2
    have hdegb : G.degree b = 8 := (Finset.mem_filter.mp hbD8).2
    have hdegc : G.degree c = 8 := (Finset.mem_filter.mp hcD8).2
    have hbc : ¬ G.Adj b c :=
      htIndep.isIndepSet (by simp) (by simp [hbc_ne.symm]) hbc_ne
    exact not_three_pairwise_nonadjacent_degree_eight
      G hcard hnoK4 hnoI5 hab_ne hac_ne hbc_ne hdega hdegb hdegc hab hac hbc

/--
If the degree-`8` class reaches the current cap `6`, every degree-`8` vertex has exactly two
degree-`8` neighbors.
-/
theorem degree_eight_neighborFinset_card_eq_two_of_degree_eight_vertices_card_eq_six
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (hD8card : ((Finset.univ : Finset α).filter (fun v => G.degree v = 8)).card = 6)
    {a : α} (hdega : G.degree a = 8) :
    ((G.neighborFinset a).filter (fun v => G.degree v = 8)).card = 2 := by
  classical
  let D8 : Finset α := (Finset.univ : Finset α).filter (fun v => G.degree v = 8)
  have haD8 : a ∈ D8 := by
    exact Finset.mem_filter.mpr ⟨by simp, hdega⟩
  let A : Finset α := (D8.erase a).filter (G.Adj a)
  let B : Finset α := (D8.erase a).filter (fun b => ¬ G.Adj a b)
  have hpart : A.card + B.card = (D8.erase a).card := by
    simpa [A, B] using
      (Finset.card_filter_add_card_filter_not (s := D8.erase a) (p := G.Adj a))
  have hA_le : A.card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) <|
      degree_eight_neighborFinset_card_le_two_of_degree_eight G hcard hnoK4 hnoI5 hdega
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxErase, hax⟩
    have hxD8 : x ∈ D8 := (Finset.mem_erase.mp hxErase).2
    exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset a x).mpr hax, (Finset.mem_filter.mp hxD8).2⟩
  have hEraseCard : (D8.erase a).card = 5 := by
    rw [Finset.card_erase_of_mem haD8, hD8card]
  have hB_le : B.card ≤ 3 := by
    by_contra hle
    have hfour : 4 ≤ B.card := by omega
    rcases hasCliqueOrIndepSetBound_four_two_four G B hfour with hClique | hIndep
    · rcases hClique with ⟨t, _htB, htClique⟩
      exact hnoK4 ⟨t, htClique⟩
    · rcases hIndep with ⟨t, htB, htIndep⟩
      rcases Finset.card_eq_two.mp htIndep.card_eq with ⟨b, c, hbc_ne, rfl⟩
      have hbB : b ∈ B := htB (by simp)
      have hcB : c ∈ B := htB (by simp [hbc_ne.symm])
      rcases Finset.mem_filter.mp hbB with ⟨hbErase, hab⟩
      rcases Finset.mem_filter.mp hcB with ⟨hcErase, hac⟩
      have hab_ne : a ≠ b := (Finset.mem_erase.mp hbErase).1.symm
      have hac_ne : a ≠ c := (Finset.mem_erase.mp hcErase).1.symm
      have hbD8 : b ∈ D8 := (Finset.mem_erase.mp hbErase).2
      have hcD8 : c ∈ D8 := (Finset.mem_erase.mp hcErase).2
      have hdegb : G.degree b = 8 := (Finset.mem_filter.mp hbD8).2
      have hdegc : G.degree c = 8 := (Finset.mem_filter.mp hcD8).2
      have hbc : ¬ G.Adj b c :=
        htIndep.isIndepSet (by simp) (by simp [hbc_ne.symm]) hbc_ne
      exact not_three_pairwise_nonadjacent_degree_eight
        G hcard hnoK4 hnoI5 hab_ne hac_ne hbc_ne hdega hdegb hdegc hab hac hbc
  have hAcard : A.card = 2 := by omega
  have hAeq : A = (G.neighborFinset a).filter (fun v => G.degree v = 8) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxErase, hax⟩
      have hxD8 : x ∈ D8 := (Finset.mem_erase.mp hxErase).2
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset a x).mpr hax, (Finset.mem_filter.mp hxD8).2⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxa, hdegx⟩
      have hax : G.Adj a x := (G.mem_neighborFinset a x).mp hxa
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr
          ⟨hax.ne.symm, Finset.mem_filter.mpr ⟨by simp, hdegx⟩⟩,
          hax⟩
  simpa [hAeq] using hAcard

/-- The generic binomial theorem gives the textbook bound `R(3,4) <= 10`. -/
theorem hasCliqueOrIndepSetBound_three_four_ten :
    HasCliqueOrIndepSetBound 3 4 10 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 3) (b := 4) (N := 10) (by decide) (by decide) (by decide)

/-- The generic binomial theorem gives `R(3,5) <= 15`. -/
theorem hasCliqueOrIndepSetBound_three_five_fifteen :
    HasCliqueOrIndepSetBound 3 5 15 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 3) (b := 5) (N := 15) (by decide) (by decide) (by decide)

/-- The binomial theorem gives the symmetric local bound `R(4,4) <= 20`. -/
theorem hasCliqueOrIndepSetBound_four_four_twenty :
    HasCliqueOrIndepSetBound 4 4 20 := by
  exact hasCliqueOrIndepSetBound_of_ramsey_finset
    (a := 4) (b := 4) (N := 20) (by decide) (by decide) (by decide)

/--
Unconditional weak degree pressure on any 26-vertex `R(4,5)` counterexample: every degree lies in
`[6,14]`.  This uses only the generic binomial Ramsey theorem and the recurrence above.
-/
theorem weak_degree_mem_Icc_of_card_twenty_six_no_clique_four_no_indep_five
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 26)
    (hnoK4 : ¬ ∃ t : Finset α, G.IsNClique 4 t)
    (hnoI5 : ¬ ∃ t : Finset α, G.IsNIndepSet 5 t)
    (v : α) :
    6 ≤ G.degree v ∧ G.degree v ≤ 14 := by
  constructor
  · have hnonNbrsLt :
        ((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).card < 20 := by
      refine card_lt_of_no_clique_or_indep hasCliqueOrIndepSetBound_four_four_twenty G
        ((Finset.univ.erase v).filter fun w => ¬ G.Adj v w) ?_ ?_
      · rintro ⟨t, _ht, htClique⟩
        exact hnoK4 ⟨t, htClique⟩
      · rintro ⟨t, ht, htIndep⟩
        exact hnoI5 ⟨insert v t, by
          rw [← SimpleGraph.isNClique_compl] at htIndep ⊢
          refine htIndep.insert ?_
          intro b hb
          have hb' : b ∈ (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w) := ht hb
          rcases Finset.mem_filter.mp hb' with ⟨hbs, hnot⟩
          have hvb : v ≠ b := (Finset.mem_erase.mp hbs).1.symm
          exact (SimpleGraph.compl_adj _ _ _).2 ⟨hvb, hnot⟩⟩
    have hpart :
        (G.neighborFinset v).card +
          ((Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)).card =
            (Finset.univ.erase v).card := by
      have hneighbor :
          G.neighborFinset v = (Finset.univ.erase v).filter (G.Adj v) := by
        ext w
        by_cases hwv : w = v
        · subst w
          simp
        · simp [hwv]
      rw [hneighbor]
      simpa using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v) (p := G.Adj v))
    have htotal : (Finset.univ.erase v).card = 25 := by
      have h := Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := v) (by simp)
      rw [Finset.card_univ, hcard] at h
      simpa using h
    have hdegCard : G.degree v = (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    rw [hdegCard]
    omega
  · have hdeglt : G.degree v < 15 :=
      degree_lt_of_no_clique_four_no_indep_five G
        hasCliqueOrIndepSetBound_three_five_fifteen hnoK4 hnoI5 v
    omega

/-- Package a symmetric Ramsey bound as the polynomial tail witness used by terminal handoffs. -/
theorem cliqueOrIndepSetBoundTail_of_poly_bound {j N : ℕ}
    (h : HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) N)
    (hpoly : 2 * N + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j) :
    ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
      2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j :=
  ⟨N, h, hpoly⟩

/-- Same tail package with the polynomial bound written as `q^6`, where `q = 2^j`. -/
theorem cliqueOrIndepSetBoundTail_of_pow_six_bound {j N : ℕ}
    (h : HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) N)
    (hpoly : 2 * N + 1 ≤ (2 ^ j) ^ 6) :
    ∃ R : ℕ, HasCliqueOrIndepSetBound (2 ^ j) (2 ^ j) R ∧
      2 * R + 1 ≤ (2 ^ j) ^ 5 * 2 ^ j :=
  cliqueOrIndepSetBoundTail_of_poly_bound h (by
    simpa [pow_succ] using hpoly)

/--
Small off-diagonal Ramsey table sufficient for the `40960` regular-10 target.  The generic
binomial Ramsey bounds supply the `R(3,k)` row, so the only external finite inputs needed here
are `R(4,5) <= 26`; the `R(5,5)` input is then the recurrence bound `52`.
-/
structure RamseyTenSmallTable : Prop where
  r45 : HasCliqueOrIndepSetBound 4 5 26

theorem hasCliqueOrIndepSetBound_10_10_of_ramseyTenSmallTable
    (h : RamseyTenSmallTable) : HasCliqueOrIndepSetBound 10 10 40304 := by
  have h36 : HasCliqueOrIndepSetBound 3 6 21 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 3) (b := 6) (N := 21) (by decide) (by decide) (by decide)
  have h37 : HasCliqueOrIndepSetBound 3 7 28 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 3) (b := 7) (N := 28) (by decide) (by decide) (by decide)
  have h38 : HasCliqueOrIndepSetBound 3 8 36 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 3) (b := 8) (N := 36) (by decide) (by decide) (by decide)
  have h39 : HasCliqueOrIndepSetBound 3 9 45 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 3) (b := 9) (N := 45) (by decide) (by decide) (by decide)
  have h3_10 : HasCliqueOrIndepSetBound 3 10 55 := by
    exact hasCliqueOrIndepSetBound_of_ramsey_finset
      (a := 3) (b := 10) (N := 55) (by decide) (by decide) (by decide)
  have h46 : HasCliqueOrIndepSetBound 4 6 47 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 3) (b := 5) (N₁ := 21) (N₂ := 26)
      (N := 47) (by decide) (by decide) h36 h.r45 (by norm_num)
  have h47 : HasCliqueOrIndepSetBound 4 7 75 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 3) (b := 6) (N₁ := 28) (N₂ := 47)
      (N := 75) (by decide) (by decide) h37 h46 (by norm_num)
  have h48 : HasCliqueOrIndepSetBound 4 8 111 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 3) (b := 7) (N₁ := 36) (N₂ := 75)
      (N := 111) (by decide) (by decide) h38 h47 (by norm_num)
  have h49 : HasCliqueOrIndepSetBound 4 9 156 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 3) (b := 8) (N₁ := 45) (N₂ := 111)
      (N := 156) (by decide) (by decide) h39 h48 (by norm_num)
  have h4_10 : HasCliqueOrIndepSetBound 4 10 211 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 3) (b := 9) (N₁ := 55) (N₂ := 156)
      (N := 211) (by decide) (by decide) h3_10 h49 (by norm_num)
  have h55 : HasCliqueOrIndepSetBound 5 5 52 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 4) (N₁ := 26) (N₂ := 26)
      (N := 52) (by decide) (by decide) h.r45 (HasCliqueOrIndepSetBound.symm h.r45)
      (by norm_num)
  have h56 : HasCliqueOrIndepSetBound 5 6 99 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 5) (N₁ := 47) (N₂ := 52)
      (N := 99) (by decide) (by decide) h46 h55 (by norm_num)
  have h57 : HasCliqueOrIndepSetBound 5 7 174 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 6) (N₁ := 75) (N₂ := 99)
      (N := 174) (by decide) (by decide) h47 h56 (by norm_num)
  have h58 : HasCliqueOrIndepSetBound 5 8 285 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 7) (N₁ := 111) (N₂ := 174)
      (N := 285) (by decide) (by decide) h48 h57 (by norm_num)
  have h59 : HasCliqueOrIndepSetBound 5 9 441 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 8) (N₁ := 156) (N₂ := 285)
      (N := 441) (by decide) (by decide) h49 h58 (by norm_num)
  have h5_10 : HasCliqueOrIndepSetBound 5 10 652 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 4) (b := 9) (N₁ := 211) (N₂ := 441)
      (N := 652) (by decide) (by decide) h4_10 h59 (by norm_num)
  have h66 : HasCliqueOrIndepSetBound 6 6 198 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 5) (b := 5) (N₁ := 99) (N₂ := 99)
      (N := 198) (by decide) (by decide) h56 h56.symm (by norm_num)
  have h67 : HasCliqueOrIndepSetBound 6 7 372 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 5) (b := 6) (N₁ := 174) (N₂ := 198)
      (N := 372) (by decide) (by decide) h57 h66 (by norm_num)
  have h68 : HasCliqueOrIndepSetBound 6 8 657 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 5) (b := 7) (N₁ := 285) (N₂ := 372)
      (N := 657) (by decide) (by decide) h58 h67 (by norm_num)
  have h69 : HasCliqueOrIndepSetBound 6 9 1098 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 5) (b := 8) (N₁ := 441) (N₂ := 657)
      (N := 1098) (by decide) (by decide) h59 h68 (by norm_num)
  have h6_10 : HasCliqueOrIndepSetBound 6 10 1750 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 5) (b := 9) (N₁ := 652) (N₂ := 1098)
      (N := 1750) (by decide) (by decide) h5_10 h69 (by norm_num)
  have h77 : HasCliqueOrIndepSetBound 7 7 744 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 6) (b := 6) (N₁ := 372) (N₂ := 372)
      (N := 744) (by decide) (by decide) h67 h67.symm (by norm_num)
  have h78 : HasCliqueOrIndepSetBound 7 8 1401 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 6) (b := 7) (N₁ := 657) (N₂ := 744)
      (N := 1401) (by decide) (by decide) h68 h77 (by norm_num)
  have h79 : HasCliqueOrIndepSetBound 7 9 2499 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 6) (b := 8) (N₁ := 1098) (N₂ := 1401)
      (N := 2499) (by decide) (by decide) h69 h78 (by norm_num)
  have h7_10 : HasCliqueOrIndepSetBound 7 10 4249 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 6) (b := 9) (N₁ := 1750) (N₂ := 2499)
      (N := 4249) (by decide) (by decide) h6_10 h79 (by norm_num)
  have h88 : HasCliqueOrIndepSetBound 8 8 2802 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 7) (b := 7) (N₁ := 1401) (N₂ := 1401)
      (N := 2802) (by decide) (by decide) h78 h78.symm (by norm_num)
  have h89 : HasCliqueOrIndepSetBound 8 9 5301 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 7) (b := 8) (N₁ := 2499) (N₂ := 2802)
      (N := 5301) (by decide) (by decide) h79 h88 (by norm_num)
  have h8_10 : HasCliqueOrIndepSetBound 8 10 9550 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 7) (b := 9) (N₁ := 4249) (N₂ := 5301)
      (N := 9550) (by decide) (by decide) h7_10 h89 (by norm_num)
  have h99 : HasCliqueOrIndepSetBound 9 9 10602 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 8) (b := 8) (N₁ := 5301) (N₂ := 5301)
      (N := 10602) (by decide) (by decide) h89 h89.symm (by norm_num)
  have h9_10 : HasCliqueOrIndepSetBound 9 10 20152 := by
    exact HasCliqueOrIndepSetBound.step_mono (a := 8) (b := 9) (N₁ := 9550) (N₂ := 10602)
      (N := 20152) (by decide) (by decide) h8_10 h99 (by norm_num)
  have h10_9 : HasCliqueOrIndepSetBound 10 9 20152 := HasCliqueOrIndepSetBound.symm h9_10
  intro α _ G s hs
  exact
    HasCliqueOrIndepSetBound.step_mono (a := 9) (b := 9) (N₁ := 20152) (N₂ := 20152)
      (N := 40304) (by decide) (by decide) h9_10 h10_9 (by norm_num) G s hs

/-- The small Ramsey table is enough for the 40960-vertex regular induced 10-set target. -/
theorem hasRegularInducedSubgraphOfCard_ten_of_ramseyTenSmallTable
    (h : RamseyTenSmallTable) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : 40960 ≤ Fintype.card V) :
    HasRegularInducedSubgraphOfCard G 10 := by
  classical
  have hbound : 40304 ≤ (Finset.univ : Finset V).card := by
    simpa using (le_trans (by decide : 40304 ≤ 40960) hcard)
  rcases hasCliqueOrIndepSetBound_10_10_of_ramseyTenSmallTable h G Finset.univ hbound with
    hclique | hindep
  · rcases hclique with ⟨s, _hs, hsclique⟩
    simpa [hsclique.card_eq] using
      (hasRegularInducedSubgraphOfCard_of_isClique G s hsclique.isClique)
  · rcases hindep with ⟨s, _hs, hsindep⟩
    simpa [hsindep.card_eq] using
      (hasRegularInducedSubgraphOfCard_of_isIndepSet G s hsindep.isIndepSet)

lemma four_pow_bound_mem_admissibleBounds (m n : ℕ) (hn : 4 ^ m ≤ n) :
    m + 1 ∈ admissibleBounds n := by
  intro G
  have hchoose : Nat.choose (m + m) m ≤ n := by
    calc
      Nat.choose (m + m) m ≤ 2 ^ (m + m) := Nat.choose_le_two_pow _ _
      _ = 4 ^ m := by rw [show 4 = 2 ^ 2 by decide, ← pow_mul, two_mul]
      _ ≤ n := hn
  rcases ramsey_finset G m m Finset.univ (by simpa using hchoose) with h | h
  · rcases h with ⟨s, hs, hclique⟩
    simpa [hclique.card_eq] using
      (hasRegularInducedSubgraphOfCard_of_isClique G s hclique.isClique)
  · rcases h with ⟨s, hs, hindep⟩
    simpa [hindep.card_eq] using
      (hasRegularInducedSubgraphOfCard_of_isIndepSet G s hindep.isIndepSet)

theorem four_pow_bound_le_F (m n : ℕ) (hn : 4 ^ m ≤ n) : m + 1 ≤ F n := by
  exact le_csSup (admissibleBounds_bddAbove n) (four_pow_bound_mem_admissibleBounds m n hn)

theorem nat_log_four_bound (n : ℕ) (hn : 0 < n) : Nat.log 4 n + 1 ≤ F n := by
  exact four_pow_bound_le_F (Nat.log 4 n) n (Nat.pow_log_le_self 4 (Nat.ne_of_gt hn))

theorem real_log_div_log_four_lt_F (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) / Real.log 4 < F n := by
  have hlogb : Real.logb 4 n < (Nat.log 4 n + 1 : ℝ) := by
    have hfloor : ⌊Real.logb 4 n⌋₊ = Nat.log 4 n := Real.natFloor_logb_natCast 4 n
    calc
      Real.logb 4 n < ⌊Real.logb 4 n⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = Nat.log 4 n + 1 := by rw [hfloor]
  have hbound : (Nat.log 4 n + 1 : ℝ) ≤ F n := by
    exact_mod_cast nat_log_four_bound n hn
  calc
    Real.log (n : ℝ) / Real.log 4 = Real.logb 4 n := by rw [Real.log_div_log]
    _ < Nat.log 4 n + 1 := hlogb
    _ ≤ F n := hbound

theorem real_log_lower_bound (n : ℕ) (hn : 0 < n) :
    (1 / Real.log 4) * Real.log (n : ℝ) ≤ F n := by
  have hlt : Real.log (n : ℝ) / Real.log 4 < (F n : ℝ) := real_log_div_log_four_lt_F n hn
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using le_of_lt hlt

theorem eventually_real_log_lower_bound :
    ∀ᶠ n : ℕ in Filter.atTop, (1 / Real.log 4) * Real.log (n : ℝ) ≤ F n := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact real_log_lower_bound n (by simpa using hn)

theorem exists_pos_eventual_log_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c * Real.log (n : ℝ) ≤ F n := by
  refine ⟨1 / Real.log 4, one_div_pos.2 (Real.log_pos (by norm_num)),
    eventually_real_log_lower_bound⟩

theorem exists_pos_eventual_ratio_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ (F n : ℝ) / Real.log (n : ℝ) := by
  refine ⟨1 / Real.log 4, one_div_pos.2 (Real.log_pos (by norm_num)), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2, eventually_real_log_lower_bound] with n hn hbound
  have hlog : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hn))
  exact (le_div_iff₀ hlog).2 hbound

end RegularInducedSubgraph
