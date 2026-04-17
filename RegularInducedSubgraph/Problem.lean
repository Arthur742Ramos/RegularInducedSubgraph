import RegularInducedSubgraph.Basic

open Filter

namespace RegularInducedSubgraph

/-- Bounds that work uniformly for every graph on `n` labelled vertices. -/
def admissibleBounds (n : ℕ) : Set ℕ :=
  { k | ∀ G : SimpleGraph (Fin n), HasRegularInducedSubgraphOfCard G k }

/-- The extremal function from the problem statement. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup (admissibleBounds n)

lemma zero_mem_admissibleBounds (n : ℕ) : 0 ∈ admissibleBounds n := by
  intro G
  exact hasRegularInducedSubgraphOfCard_zero G

/-- A direct filter-language formalization of `F(n) / log n → ∞`. -/
def TargetStatement : Prop :=
  Tendsto (fun n : ℕ => (F n : ℝ) / Real.log (n : ℝ)) atTop atTop

/--
An equivalent-looking lower-bound form that is usually easier to attack combinatorially:
eventually `F(n)` dominates every constant multiple of `log n`.
-/
def EventualLogDomination : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → C * Real.log (n : ℝ) ≤ F n

lemma admissibleBounds_bddAbove (n : ℕ) : BddAbove (admissibleBounds n) := by
  refine ⟨n, ?_⟩
  intro k hk
  rcases hk (⊥ : SimpleGraph (Fin n)) with ⟨s, hks, d, hd⟩
  exact le_trans hks (by simpa using s.card_le_univ)

lemma one_mem_admissibleBounds_of_pos {n : ℕ} (hn : 0 < n) : 1 ∈ admissibleBounds n := by
  intro G
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hasRegularInducedSubgraphOfCard_one G

lemma one_le_F_of_pos {n : ℕ} (hn : 0 < n) : 1 ≤ F n := by
  exact le_csSup (admissibleBounds_bddAbove n) (one_mem_admissibleBounds_of_pos hn)

lemma admissibleBounds_mono {n m : ℕ} (hnm : n ≤ m) :
    admissibleBounds n ⊆ admissibleBounds m := by
  intro k hk G
  let H : SimpleGraph (Fin n) := G.comap (Fin.castLEEmb hnm)
  exact hasRegularInducedSubgraphOfCard_of_embedding
    (SimpleGraph.Embedding.comap (Fin.castLEEmb hnm) G) (hk H)

lemma mem_admissibleBounds_of_le {n k ℓ : ℕ} (hℓk : ℓ ≤ k)
    (hk : k ∈ admissibleBounds n) : ℓ ∈ admissibleBounds n := by
  intro G
  rcases hk G with ⟨s, hks, d, hd⟩
  exact ⟨s, le_trans hℓk hks, d, hd⟩

lemma F_mem_admissibleBounds (n : ℕ) : F n ∈ admissibleBounds n := by
  exact Nat.sSup_mem ⟨0, zero_mem_admissibleBounds n⟩ (admissibleBounds_bddAbove n)

lemma le_F_iff {n k : ℕ} : k ≤ F n ↔ k ∈ admissibleBounds n := by
  constructor
  · intro hk
    exact mem_admissibleBounds_of_le hk (F_mem_admissibleBounds n)
  · intro hk
    exact le_csSup (admissibleBounds_bddAbove n) hk

lemma F_monotone : Monotone F := by
  intro n m hnm
  rw [le_F_iff]
  exact admissibleBounds_mono hnm (F_mem_admissibleBounds n)

/-- The least graph order that forces a regular induced subgraph on at least `k` vertices. -/
noncomputable def forcingThreshold (k : ℕ) : ℕ :=
  sInf { n : ℕ | k ≤ F n }

theorem eventualLogDomination_implies_targetStatement
    (hdom : EventualLogDomination) : TargetStatement := by
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  by_cases hB : B ≤ 0
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) hn))
    have hnonneg : 0 ≤ (F n : ℝ) / Real.log (n : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg (F n)) (le_of_lt hlog)
    exact le_trans hB hnonneg
  · obtain ⟨N, hN⟩ := hdom B
    filter_upwards [Filter.eventually_ge_atTop (max N 2)] with n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hlog : 0 < Real.log (n : ℝ) := by
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
      exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) hn2))
    exact (le_div_iff₀ hlog).2 (hN hnN)

theorem targetStatement_implies_eventualLogDomination
    (htarget : TargetStatement) : EventualLogDomination := by
  intro C
  by_cases hC : 0 ≤ C
  · have hEventually : ∀ᶠ n : ℕ in atTop, C ≤ (F n : ℝ) / Real.log (n : ℝ) :=
      (Filter.tendsto_atTop.mp htarget) C
    have hEventually' : {n : ℕ | C ≤ (F n : ℝ) / Real.log (n : ℝ)} ∈ atTop := hEventually
    rcases Filter.mem_atTop_sets.mp hEventually' with ⟨N, hN⟩
    refine ⟨max N 2, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hratio : C ≤ (F n : ℝ) / Real.log (n : ℝ) := hN n hnN
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hlog : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) hn2))
    exact (le_div_iff₀ hlog).1 hratio
  · refine ⟨1, ?_⟩
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hmul : C * Real.log (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hlog_nonneg
    exact le_trans hmul (Nat.cast_nonneg (F n))

theorem targetStatement_iff_eventualLogDomination :
    TargetStatement ↔ EventualLogDomination := by
  constructor
  · exact targetStatement_implies_eventualLogDomination
  · exact eventualLogDomination_implies_targetStatement

end RegularInducedSubgraph
