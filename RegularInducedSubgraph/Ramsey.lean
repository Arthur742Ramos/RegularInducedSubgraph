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
