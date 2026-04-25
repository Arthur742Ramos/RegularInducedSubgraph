import RegularInducedSubgraph.Problem
import Mathlib.Data.Nat.Choose.Bounds

open scoped Classical

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
