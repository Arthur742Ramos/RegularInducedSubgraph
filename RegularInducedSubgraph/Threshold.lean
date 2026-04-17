import RegularInducedSubgraph.Ramsey

open Filter

namespace RegularInducedSubgraph

lemma forcingThreshold_nonempty (k : ℕ) : ({n : ℕ | k ≤ F n} : Set ℕ).Nonempty := by
  refine ⟨4 ^ k, le_trans (Nat.le_succ k) ?_⟩
  exact four_pow_bound_le_F k (4 ^ k) le_rfl

lemma forcingThreshold_spec (k : ℕ) : k ≤ F (forcingThreshold k) := by
  exact Nat.sInf_mem (forcingThreshold_nonempty k)

lemma forcingThreshold_le_of_le_F {k n : ℕ} (hk : k ≤ F n) : forcingThreshold k ≤ n := by
  exact Nat.sInf_le hk

lemma le_F_of_forcingThreshold_le {k n : ℕ} (hkn : forcingThreshold k ≤ n) : k ≤ F n := by
  exact le_trans (forcingThreshold_spec k) (F_monotone hkn)

theorem le_F_iff_forcingThreshold_le {k n : ℕ} : k ≤ F n ↔ forcingThreshold k ≤ n := by
  constructor
  · exact forcingThreshold_le_of_le_F
  · exact le_F_of_forcingThreshold_le

theorem forcingThreshold_mono : Monotone forcingThreshold := by
  intro k ℓ hkℓ
  rw [← le_F_iff_forcingThreshold_le]
  exact le_trans hkℓ (forcingThreshold_spec ℓ)

theorem forcingThreshold_le_four_pow (k : ℕ) : forcingThreshold (k + 1) ≤ 4 ^ k := by
  exact forcingThreshold_le_of_le_F (four_pow_bound_le_F k (4 ^ k) le_rfl)

/--
An inverse-scale formulation of the main problem: every base `a > 1` should eventually dominate
the forcing threshold `forcingThreshold k`.
-/
def EventualSubexponentialThreshold : Prop :=
  ∀ a : ℝ, 1 < a → ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    forcingThreshold k ≤ Nat.ceil (a ^ (k : ℝ))

/--
A geometric-sequence formulation of the main problem: for a fixed integer base `b > 1`, the values
of `F` on the subsequence `b^k` should eventually dominate every linear function of `k`.
-/
def EventualPowerDomination (b : ℕ) : Prop :=
  ∀ C : ℝ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → C * (k : ℝ) ≤ F (b ^ k)

/--
An entirely discrete version of `EventualPowerDomination`: on the subsequence `b^k`, `F` should
eventually dominate every natural-number multiple of `k`.
-/
def EventualNatPowerDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → M * k ≤ F (b ^ k)

theorem eventualLogDomination_implies_eventualSubexponentialThreshold
    (hdom : EventualLogDomination) : EventualSubexponentialThreshold := by
  intro a ha
  let C : ℝ := 2 / Real.log a
  have hloga_pos : 0 < Real.log a := Real.log_pos ha
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  obtain ⟨N, hN⟩ := hdom C
  have hceil_tendsto : Tendsto (fun k : ℕ => Nat.ceil (a ^ (k : ℝ))) atTop atTop := by
    simpa [Real.rpow_natCast] using
      (tendsto_nat_ceil_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt ha))
  have hceil_eventually : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → N ≤ Nat.ceil (a ^ (k : ℝ)) := by
    simpa using (Filter.tendsto_atTop.1 hceil_tendsto) N
  rcases hceil_eventually with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  refine forcingThreshold_le_of_le_F ?_
  have hpow_pos : 0 < a ^ (k : ℝ) := Real.rpow_pos_of_pos (lt_trans zero_lt_one ha) _
  have hk_mul : (k : ℝ) ≤ C * Real.log (a ^ (k : ℝ)) := by
    rw [show C = 2 / Real.log a by rfl, Real.log_rpow (lt_trans zero_lt_one ha)]
    field_simp [hloga_pos.ne']
    nlinarith
  have hlog_mono :
      Real.log (a ^ (k : ℝ)) ≤ Real.log (Nat.ceil (a ^ (k : ℝ)) : ℝ) := by
    exact Real.log_le_log hpow_pos (Nat.le_ceil _)
  have hk_log : (k : ℝ) ≤ C * Real.log (Nat.ceil (a ^ (k : ℝ)) : ℝ) := by
    exact le_trans hk_mul (mul_le_mul_of_nonneg_left hlog_mono hC_nonneg)
  have hkFreal : (k : ℝ) ≤ F (Nat.ceil (a ^ (k : ℝ))) := by
    exact le_trans hk_log (hN (hK hk))
  exact_mod_cast hkFreal

theorem targetStatement_implies_eventualSubexponentialThreshold
    (htarget : TargetStatement) : EventualSubexponentialThreshold := by
  exact eventualLogDomination_implies_eventualSubexponentialThreshold
    (targetStatement_implies_eventualLogDomination htarget)

theorem eventualSubexponentialThreshold_implies_eventualLogDomination
    (hsub : EventualSubexponentialThreshold) : EventualLogDomination := by
  intro C
  by_cases hC : 0 < C
  · let a : ℝ := Real.exp (1 / (2 * C))
    have ha : 1 < a := by
      dsimp [a]
      exact Real.one_lt_exp_iff.2 (by positivity)
    have ha_pos : 0 < a := lt_trans zero_lt_one ha
    obtain ⟨K, hK⟩ := hsub a ha
    let N : ℕ := max (Nat.ceil (a ^ (2 : ℝ))) (Nat.ceil (Real.exp (K / C)))
    refine ⟨N, ?_⟩
    intro n hn
    let k : ℕ := Nat.ceil (C * Real.log (n : ℝ))
    have hn_a2 : a ^ (2 : ℝ) ≤ n := by
      exact Nat.ceil_le.mp (le_trans (le_max_left _ _) hn)
    have hn_exp : Real.exp (K / C) ≤ n := by
      exact Nat.ceil_le.mp (le_trans (le_max_right _ _) hn)
    have hn_one : 1 ≤ n := by
      have hceil_one : 1 ≤ Nat.ceil (a ^ (2 : ℝ)) := by
        rw [Nat.one_le_ceil_iff]
        positivity
      exact le_trans hceil_one (le_trans (le_max_left _ _) hn)
    have hk_ge : K ≤ k := by
      have hKlog : (K : ℝ) / C ≤ Real.log (n : ℝ) := by
        simpa using Real.log_le_log (Real.exp_pos (K / C)) hn_exp
      have hKmul : (K : ℝ) ≤ C * Real.log (n : ℝ) := by
        rw [div_le_iff₀ hC] at hKlog
        simpa [mul_comm, mul_left_comm, mul_assoc] using hKlog
      exact_mod_cast (le_trans hKmul (Nat.le_ceil _))
    have hk_upper : (k : ℝ) ≤ C * Real.log (n : ℝ) + 1 := by
      exact (Nat.ceil_lt_add_one
        (mul_nonneg hC.le (Real.log_nonneg (by exact_mod_cast hn_one)))).le
    have hak_le : a ^ (k : ℝ) ≤ a * Real.sqrt n := by
      calc
        a ^ (k : ℝ) ≤ a ^ (C * Real.log (n : ℝ) + 1) := by
          exact Real.rpow_le_rpow_of_exponent_le ha.le hk_upper
        _ = a * Real.sqrt n := by
          rw [show a = Real.exp (1 / (2 * C)) by rfl, ← Real.exp_mul]
          have hsplit :
              (1 / (2 * C)) * (C * Real.log (n : ℝ) + 1) =
                1 / (2 * C) + (Real.log (n : ℝ)) / 2 := by
            field_simp [hC.ne']
            ring_nf
          rw [hsplit, Real.exp_add, Real.sqrt_eq_rpow]
          rw [Real.rpow_def_of_pos (by exact_mod_cast hn_one)]
          ring_nf
    have ha_le_sqrt : a ≤ Real.sqrt n := by
      rw [← Real.sqrt_sq (le_of_lt ha_pos),
        Real.sqrt_le_sqrt_iff (show 0 ≤ (n : ℝ) by positivity)]
      simpa [Real.rpow_two] using hn_a2
    have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hmul_le : a * Real.sqrt n ≤ n := by
      calc
        a * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
          gcongr
        _ = n := by
          exact Real.mul_self_sqrt (by positivity)
    have hakn : a ^ (k : ℝ) ≤ n := le_trans hak_le hmul_le
    have hthreshold : forcingThreshold k ≤ n := by
      refine le_trans (hK hk_ge) ?_
      exact Nat.ceil_le.2 hakn
    have hkF : k ≤ F n := le_F_of_forcingThreshold_le hthreshold
    have hClog_le_k : C * Real.log (n : ℝ) ≤ k := Nat.le_ceil _
    exact le_trans hClog_le_k (by exact_mod_cast hkF)
  · refine ⟨1, ?_⟩
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hmul : C * Real.log (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) hlog_nonneg
    exact le_trans hmul (Nat.cast_nonneg (F n))

theorem eventualSubexponentialThreshold_iff_targetStatement :
    EventualSubexponentialThreshold ↔ TargetStatement := by
  constructor
  · intro hsub
    exact eventualLogDomination_implies_targetStatement
      (eventualSubexponentialThreshold_implies_eventualLogDomination hsub)
  · exact targetStatement_implies_eventualSubexponentialThreshold

theorem eventualLogDomination_implies_eventualPowerDomination {b : ℕ} (hb : 1 < b)
    (hdom : EventualLogDomination) : EventualPowerDomination b := by
  intro C
  let D : ℝ := C / Real.log (b : ℝ)
  have hlogb_pos : 0 < Real.log (b : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hb)
  obtain ⟨N, hN⟩ := hdom D
  refine ⟨Nat.clog b N, ?_⟩
  intro k hk
  have hN_le : N ≤ b ^ k := by
    calc
      N ≤ b ^ Nat.clog b N := Nat.le_pow_clog hb N
      _ ≤ b ^ k := Nat.pow_le_pow_right (Nat.zero_lt_of_lt (lt_trans Nat.zero_lt_one hb)) hk
  have hbound : D * Real.log ((b ^ k : ℕ) : ℝ) ≤ F (b ^ k) := hN hN_le
  calc
    C * (k : ℝ) = D * Real.log ((b ^ k : ℕ) : ℝ) := by
      rw [show D = C / Real.log (b : ℝ) by rfl]
      rw [show ((b ^ k : ℕ) : ℝ) = (b : ℝ) ^ (k : ℝ) by
        rw [Nat.cast_pow, Real.rpow_natCast]]
      rw [Real.log_rpow (by positivity)]
      field_simp [hlogb_pos.ne']
    _ ≤ F (b ^ k) := hbound

theorem eventualNatPowerDomination_iff_eventualPowerDomination {b : ℕ} :
    EventualNatPowerDomination b ↔ EventualPowerDomination b := by
  constructor
  · intro hnat C
    by_cases hC : 0 ≤ C
    · let M : ℕ := Nat.ceil C
      obtain ⟨K, hK⟩ := hnat M
      refine ⟨K, ?_⟩
      intro k hk
      have hCM : C ≤ M := Nat.le_ceil C
      have hMk : (M : ℝ) * (k : ℝ) ≤ F (b ^ k) := by
        exact_mod_cast hK hk
      exact le_trans (mul_le_mul_of_nonneg_right hCM (Nat.cast_nonneg k)) hMk
    · refine ⟨0, ?_⟩
      intro k hk
      have hmul : C * (k : ℝ) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) (Nat.cast_nonneg k)
      exact le_trans hmul (Nat.cast_nonneg (F (b ^ k)))
  · intro hreal M
    obtain ⟨K, hK⟩ := hreal M
    refine ⟨K, ?_⟩
    intro k hk
    exact_mod_cast hK hk

theorem eventualPowerDomination_implies_eventualLogDomination {b : ℕ} (hb : 1 < b)
    (hpow : EventualPowerDomination b) : EventualLogDomination := by
  intro C
  by_cases hC : 0 < C
  · let B : ℝ := 2 * C * Real.log (b : ℝ)
    have hlogb_pos : 0 < Real.log (b : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hb)
    obtain ⟨K, hK⟩ := hpow B
    refine ⟨max (b ^ K) b, ?_⟩
    intro n hn
    let k : ℕ := Nat.log b n
    have hb_le_n : b ≤ n := le_trans (le_max_right _ _) hn
    have hK_le_n : b ^ K ≤ n := le_trans (le_max_left _ _) hn
    have hn_pos : 0 < n := lt_of_lt_of_le (lt_trans Nat.zero_lt_one hb) hb_le_n
    have hk_ge : K ≤ k := by
      have hlog_mono : Nat.log b (b ^ K) ≤ Nat.log b n := Nat.log_mono_right hK_le_n
      simpa [k, Nat.log_pow hb] using hlog_mono
    have hk_one : 1 ≤ k := by
      exact Nat.succ_le_of_lt (by simpa [k] using Nat.log_pos hb hb_le_n)
    have hpow_le : b ^ k ≤ n := Nat.pow_log_le_self b (Nat.ne_of_gt hn_pos)
    have hBk : B * (k : ℝ) ≤ F (b ^ k) := hK hk_ge
    have hBk_le : B * (k : ℝ) ≤ F n := by
      exact le_trans hBk (by exact_mod_cast F_monotone hpow_le)
    have hpow_lt : (n : ℝ) < (b : ℝ) ^ (k + 1 : ℕ) := by
      simpa [Nat.cast_pow] using
        (show (n : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) by
          exact_mod_cast Nat.lt_pow_succ_log_self hb n)
    have hlog_lt : Real.log (n : ℝ) < ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
      have hlog_lt' : Real.log (n : ℝ) < Real.log ((b : ℝ) ^ (k + 1 : ℕ)) := by
        exact Real.log_lt_log (by exact_mod_cast hn_pos) hpow_lt
      rw [show ((b : ℝ) ^ (k + 1 : ℕ)) = (b : ℝ) ^ (((k + 1 : ℕ) : ℝ)) by
        rw [Real.rpow_natCast]] at hlog_lt'
      exact hlog_lt'.trans_eq (by rw [Real.log_rpow (by positivity)])
    have hk_two_nat : k + 1 ≤ 2 * k := by
      omega
    have hk_two : (((k + 1 : ℕ) : ℝ)) ≤ 2 * (k : ℝ) := by
      exact_mod_cast hk_two_nat
    have hmain : C * Real.log (n : ℝ) < B * (k : ℝ) := by
      calc
        C * Real.log (n : ℝ) < C * ((((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ))) := by
          gcongr
        _ ≤ C * (((2 * (k : ℝ)) * Real.log (b : ℝ))) := by
          gcongr
        _ = B * (k : ℝ) := by
          dsimp [B]
          ring
    exact le_trans (le_of_lt hmain) hBk_le
  · refine ⟨1, ?_⟩
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hmul : C * Real.log (n : ℝ) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) hlog_nonneg
    exact le_trans hmul (Nat.cast_nonneg (F n))

theorem eventualPowerDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualPowerDomination b ↔ TargetStatement := by
  constructor
  · intro hpow
    exact eventualLogDomination_implies_targetStatement
      (eventualPowerDomination_implies_eventualLogDomination hb hpow)
  · intro htarget
    exact eventualLogDomination_implies_eventualPowerDomination hb
      (targetStatement_implies_eventualLogDomination htarget)

theorem eventualNatPowerDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualNatPowerDomination b ↔ TargetStatement := by
  rw [eventualNatPowerDomination_iff_eventualPowerDomination]
  exact eventualPowerDomination_iff_targetStatement hb

theorem eventualPowerDomination_four_iff_targetStatement :
    EventualPowerDomination 4 ↔ TargetStatement := by
  simpa using eventualPowerDomination_iff_targetStatement (b := 4) (by decide : 1 < 4)

theorem eventualNatPowerDomination_four_iff_targetStatement :
    EventualNatPowerDomination 4 ↔ TargetStatement := by
  simpa using eventualNatPowerDomination_iff_targetStatement (b := 4) (by decide : 1 < 4)

end RegularInducedSubgraph
