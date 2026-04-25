import Mathlib

/-!
# Arithmetic and endpoint frontier for the host-side reduction

This file records the Lean-facing arithmetic part of the current host frontier from
`notes/current-roadmap.md`, `notes/remaining-gap-math-memo.md`, and
`notes/last-gap-proof-roadmap.md`.

The graph-theoretic host packages live in `Modular.Finite`.  The reductions in the notes also use a
pure arithmetic normal form for the pure-side overlap strip.  The main formal outputs here are:

* `NormalizedOverlapProfile`: the complement-normalized pure-side overlap profile;
* `normalizedOverlapProfile_defectBudget_eq`: the exact identity
  `d_X + d_Y = 3s - q - 1`;
* `q64_normalizedOverlapProfile_iff`: the normalized `q = 64` overlap list;
* `q64_overlapDefectPair_iff` and `q64_balancedHigherOrderPacket_iff`: the reduction of the
  `q = 64` higher-order packets to `(26,6,7)` and `(30,12,13)`;
* `q64_balancedHigherOrderPacket_height_iff`: the balanced-ladder height form
  `m = 16 -> (30,12,13)` and `m = 18 -> (26,6,7)`.
* `q64_existsCleanQuartet_not_blocked_iff_triple_noncover`: the finite set-theoretic equivalence
  between quartic-blocker noncover and triple noncover.
* `q64_relationTriangle_iff_compositionObstruction`: the binary-slice composition obstruction
   formulation of the distributed corner triangle.
* `Q64RemainingHostFrontier`: the abstract Lean statement of the two ingredients left by the
   notes: common-shadow synchronization plus the localized alternating-hexagon scalar theorem.
* `q64_twoFiberRow_iff`: the two-fiber single-flip row classification
   `0000,0001,0101,0011,0111`.
* `q64_two_child_carry_endpoint_not_additive`: the dyadic endpoint where both child carry tests
  vanish but the coarse carry bit is nonzero.
-/

namespace RegularInducedSubgraph

section HostFrontierArithmetic

/--
The pure-side interior codimension range from the host-frontier notes:
`6 ≤ s ≤ q / 2 - 2` and `s ≡ 2 [MOD 4]`.
-/
def PureSideCodimension (q s : ℕ) : Prop :=
  6 ≤ s ∧ s ≤ q / 2 - 2 ∧ s % 4 = 2

/--
The complement-normalized same-graph overlap strip.

Here `s` is the residual codimension and `alpha` is the internal regularity parameter after
normalizing by global complement.  The interval
`q - 2s ≤ alpha ≤ floor((q - s - 1) / 2)` is the overlap strip from the notes.
-/
def NormalizedOverlapProfile (q s alpha : ℕ) : Prop :=
  PureSideCodimension q s ∧ q + 1 ≤ 3 * s ∧ q - 2 * s ≤ alpha ∧
    alpha ≤ (q - s - 1) / 2

/-- The `X`-side sparse defect parameter in the normalized overlap strip. -/
def normalizedDefectX (q s alpha : ℕ) : ℕ :=
  alpha - (q - 2 * s)

/-- The `Y`-side sparse defect parameter in the normalized overlap strip. -/
def normalizedDefectY (s alpha : ℕ) : ℕ :=
  s - 1 - alpha

/-- The total normalized defect budget `h(s) = 3s - q - 1`. -/
def normalizedDefectBudget (q s : ℕ) : ℕ :=
  3 * s - q - 1

lemma NormalizedOverlapProfile.two_mul_codimension_le_modulus
    {q s alpha : ℕ} (h : NormalizedOverlapProfile q s alpha) :
    2 * s ≤ q := by
  rcases h with ⟨⟨_, hs, _⟩, _⟩
  omega

lemma NormalizedOverlapProfile.alpha_le_codim_sub_one
    {q s alpha : ℕ} (h : NormalizedOverlapProfile q s alpha) :
    alpha ≤ s - 1 := by
  rcases h with ⟨⟨_, hs, _⟩, _, _, hhalf⟩
  omega

lemma NormalizedOverlapProfile.defectX_le_defectY
    {q s alpha : ℕ} (h : NormalizedOverlapProfile q s alpha) :
    normalizedDefectX q s alpha ≤ normalizedDefectY s alpha := by
  unfold normalizedDefectX normalizedDefectY
  have h2s : 2 * s ≤ q := h.two_mul_codimension_le_modulus
  have hAlpha : alpha ≤ s - 1 := h.alpha_le_codim_sub_one
  rcases h with ⟨_, _, hlow, hhalf⟩
  omega

lemma normalizedOverlapProfile_defectBudget_eq
    {q s alpha : ℕ} (h : NormalizedOverlapProfile q s alpha) :
    normalizedDefectX q s alpha + normalizedDefectY s alpha =
      normalizedDefectBudget q s := by
  unfold normalizedDefectX normalizedDefectY normalizedDefectBudget
  have h2s : 2 * s ≤ q := h.two_mul_codimension_le_modulus
  have hlow : q - 2 * s ≤ alpha := h.2.2.1
  have hAlpha : alpha ≤ s - 1 := h.alpha_le_codim_sub_one
  omega

lemma normalizedOverlapProfile_defectBudget_le_iff
    {q s alpha H : ℕ} (h : NormalizedOverlapProfile q s alpha) :
    normalizedDefectX q s alpha + normalizedDefectY s alpha ≤ H ↔
      normalizedDefectBudget q s ≤ H := by
  rw [normalizedOverlapProfile_defectBudget_eq h]

lemma normalizedDefectBudget_add_four
    {q s : ℕ} (h : q + 1 ≤ 3 * s) :
    normalizedDefectBudget q (s + 4) = normalizedDefectBudget q s + 12 := by
  unfold normalizedDefectBudget
  omega

lemma normalizedDefectBudget_le_half_sub_seven_of_pureSide
    {q s : ℕ} (h : PureSideCodimension q s) :
    normalizedDefectBudget q s ≤ q / 2 - 7 := by
  unfold PureSideCodimension at h
  unfold normalizedDefectBudget
  omega

lemma normalizedDefectBudget_top_even (m : ℕ) :
    normalizedDefectBudget (2 * m) (m - 2) = m - 7 := by
  unfold normalizedDefectBudget
  omega

/-- The normalized `q = 64` overlap profiles are exactly the three codimensions `22, 26, 30`. -/
theorem q64_normalizedOverlap_codimension_iff {s : ℕ} :
    (∃ alpha, NormalizedOverlapProfile 64 s alpha) ↔
      s = 22 ∨ s = 26 ∨ s = 30 := by
  constructor
  · rintro ⟨alpha, hprofile⟩
    unfold NormalizedOverlapProfile PureSideCodimension at hprofile
    omega
  · intro hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨20, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension
      omega
    · refine ⟨12, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension
      omega
    · refine ⟨4, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension
      omega

/--
Exact normalized `q = 64` overlap list:
`(s, alpha) = (22,20)`, `s = 26` with `12 ≤ alpha ≤ 18`, or
`s = 30` with `4 ≤ alpha ≤ 16`.
-/
theorem q64_normalizedOverlapProfile_iff {s alpha : ℕ} :
    NormalizedOverlapProfile 64 s alpha ↔
      (s = 22 ∧ alpha = 20) ∨
        (s = 26 ∧ 12 ≤ alpha ∧ alpha ≤ 18) ∨
          (s = 30 ∧ 4 ≤ alpha ∧ alpha ≤ 16) := by
  constructor
  · intro h
    unfold NormalizedOverlapProfile PureSideCodimension at h
    omega
  · intro h
    unfold NormalizedOverlapProfile PureSideCodimension
    omega

/--
A normalized `q = 64` overlap profile, recorded by codimension and the two sparse defect
parameters.
-/
def Q64OverlapDefectPair (s dX dY : ℕ) : Prop :=
  ∃ alpha, NormalizedOverlapProfile 64 s alpha ∧
    dX = normalizedDefectX 64 s alpha ∧ dY = normalizedDefectY s alpha

/--
The higher-order `q = 64` overlap pairs are the normalized defect pairs after removing the isolated
one-defect rung `s = 22`.
-/
def Q64HigherOrderOverlap (s dX dY : ℕ) : Prop :=
  Q64OverlapDefectPair s dX dY ∧ 22 < s

/--
The balanced higher-order packets are exactly the defect pairs with adjacent central coordinates,
`dY = dX + 1`.
-/
def Q64BalancedHigherOrderPacket (s dX dY : ℕ) : Prop :=
  Q64HigherOrderOverlap s dX dY ∧ dY = dX + 1

/--
Balanced-ladder height coordinates for `q = 64`, using the note formulas
`s = 62 - 2m`, `d_X = 60 - 3m`, and `d_Y = 61 - 3m`.
-/
def Q64BalancedLadderHeightPacket (m s dX dY : ℕ) : Prop :=
  s = 62 - 2 * m ∧ dX = 60 - 3 * m ∧ dY = 61 - 3 * m

/--
The full normalized `q = 64` defect-pair list: the isolated one-defect pair `(22,0,1)`, the
budget-`13` family `(26,d,13-d)`, and the budget-`25` family `(30,d,25-d)`.
-/
theorem q64_overlapDefectPair_iff {s dX dY : ℕ} :
    Q64OverlapDefectPair s dX dY ↔
      (s = 22 ∧ dX = 0 ∧ dY = 1) ∨
        (s = 26 ∧ dX ≤ 6 ∧ dY = 13 - dX) ∨
          (s = 30 ∧ dX ≤ 12 ∧ dY = 25 - dX) := by
  constructor
  · rintro ⟨alpha, hprofile, rfl, rfl⟩
    unfold NormalizedOverlapProfile PureSideCodimension normalizedDefectX normalizedDefectY at *
    omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, hdx, rfl⟩ | ⟨rfl, hdx, rfl⟩)
    · refine ⟨20, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension normalizedDefectX normalizedDefectY
      omega
    · refine ⟨12 + dX, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension normalizedDefectX normalizedDefectY
      omega
    · refine ⟨4 + dX, ?_⟩
      unfold NormalizedOverlapProfile PureSideCodimension normalizedDefectX normalizedDefectY
      omega

/--
After deleting the isolated one-defect rung, the `q = 64` higher-order overlap kernel is exactly the
two families `(26,d,13-d)` and `(30,d,25-d)`.
-/
theorem q64_higherOrderOverlap_iff {s dX dY : ℕ} :
    Q64HigherOrderOverlap s dX dY ↔
      (s = 26 ∧ dX ≤ 6 ∧ dY = 13 - dX) ∨
        (s = 30 ∧ dX ≤ 12 ∧ dY = 25 - dX) := by
  rw [Q64HigherOrderOverlap, q64_overlapDefectPair_iff]
  constructor
  · rintro ⟨hpair, hs22⟩
    omega
  · intro h
    constructor <;> omega

/--
Among the higher-order `q = 64` overlap pairs, the only balanced packets are `(26,6,7)` and
`(30,12,13)`.
-/
theorem q64_balancedHigherOrderPacket_iff {s dX dY : ℕ} :
    Q64BalancedHigherOrderPacket s dX dY ↔
      (s = 26 ∧ dX = 6 ∧ dY = 7) ∨ (s = 30 ∧ dX = 12 ∧ dY = 13) := by
  rw [Q64BalancedHigherOrderPacket, q64_higherOrderOverlap_iff]
  constructor
  · rintro ⟨hpair, hbalanced⟩
    omega
  · intro h
    constructor <;> omega

/--
The two balanced higher-order `q = 64` packets are exactly the balanced-ladder heights
`m = 16` and `m = 18`.
-/
theorem q64_balancedHigherOrderPacket_height_iff {s dX dY : ℕ} :
    Q64BalancedHigherOrderPacket s dX dY ↔
      ∃ m, (m = 16 ∨ m = 18) ∧ Q64BalancedLadderHeightPacket m s dX dY := by
  rw [q64_balancedHigherOrderPacket_iff]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · refine ⟨18, ?_⟩
      unfold Q64BalancedLadderHeightPacket
      omega
    · refine ⟨16, ?_⟩
      unfold Q64BalancedLadderHeightPacket
      omega
  · rintro ⟨m, hm, hpacket⟩
    unfold Q64BalancedLadderHeightPacket at hpacket
    omega

/--
The concrete balanced `+4` reroot arithmetic: the height-`16` packet `(30,12,13)` is one balanced
ladder step below the height-`18` packet `(26,6,7)`.
-/
theorem q64_balanced_reroot_step :
    Q64BalancedLadderHeightPacket 16 30 12 13 ∧
      Q64BalancedLadderHeightPacket 18 26 6 7 := by
  unfold Q64BalancedLadderHeightPacket
  omega

/-- Pair-rigid marked-fiber split on a balanced rung. -/
def BalancedMarkedSplit (m A₁ A₂ B₁ B₂ : ℕ) : Prop :=
  A₁ = m / 2 ∧ A₂ = m / 2 ∧ B₁ = m / 2 + 1 ∧ B₂ = m / 2 + 1

theorem q64_balanced_markedSplit_height16 :
    BalancedMarkedSplit 16 8 8 9 9 := by
  unfold BalancedMarkedSplit
  omega

theorem q64_balanced_markedSplit_height18 :
    BalancedMarkedSplit 18 9 9 10 10 := by
  unfold BalancedMarkedSplit
  omega

end HostFrontierArithmetic

section Q64PromotionEndpoint

/-!
## Abstract endpoint: quartic blockers, triple noncover, and binary-slice composition

The definitions below are intentionally graph-agnostic.  They formalize the finite endpoint that the
notes isolate after the graph-theoretic Section 40 reductions:

* a clean quartet region `Gamma`;
* a quartic blocker set `B4`;
* the projection to triples after fixing one `B`-coordinate;
* the bad triples whose entire completion fiber is blocked;
* the three binary compatibility relations around the residual `L`-corner.

This gives Lean names to the remaining theorem shape without adding axioms: the open mathematical
content is packaged as explicit `Prop`s at the end of the section.
-/

/-- The visible three-coordinate corner after fixing one marked `B`-coordinate. -/
abbrev Q64CornerTriple (A₁ A₂ B₂ : Type*) :=
  A₁ × A₂ × B₂

/-- A quartet is a visible corner triple together with the missing marked `B`-root. -/
abbrev Q64CornerQuartet (A₁ A₂ B₂ B₁ : Type*) :=
  Q64CornerTriple A₁ A₂ B₂ × B₁

variable {A₁ A₂ B₂ B₁ : Type*}
variable [DecidableEq A₁] [DecidableEq A₂] [DecidableEq B₂] [DecidableEq B₁]

/-- Projection of the lower-arity-clean quartet region to its visible triples. -/
def q64TripleSet (Gamma : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)) :
    Finset (Q64CornerTriple A₁ A₂ B₂) :=
  Gamma.image Prod.fst

/-- Completion fiber over a visible triple after fixing the missing `B`-coordinate. -/
def q64CompletionFiber
    (Gamma : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁))
    (tau : Q64CornerTriple A₁ A₂ B₂) : Finset B₁ :=
  (Gamma.filter fun x => x.1 = tau).image Prod.snd

lemma q64_mem_completionFiber
    {Gamma : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)}
    {tau : Q64CornerTriple A₁ A₂ B₂} {u : B₁} :
    u ∈ q64CompletionFiber Gamma tau ↔ (tau, u) ∈ Gamma := by
  unfold q64CompletionFiber
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨x, hx, hxu⟩
    rcases Finset.mem_filter.mp hx with ⟨hxG, hxtau⟩
    cases x
    simp_all
  · intro h
    exact Finset.mem_image.mpr ⟨(tau, u), by simp [h], rfl⟩

/-- The unblocked part of a completion fiber. -/
def q64GoodCompletionFiber
    (Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁))
    (tau : Q64CornerTriple A₁ A₂ B₂) : Finset B₁ :=
  (q64CompletionFiber Gamma tau).filter fun u => (tau, u) ∉ B4

lemma q64_mem_goodCompletionFiber
    {Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)}
    {tau : Q64CornerTriple A₁ A₂ B₂} {u : B₁} :
    u ∈ q64GoodCompletionFiber Gamma B4 tau ↔
      (tau, u) ∈ Gamma ∧ (tau, u) ∉ B4 := by
  unfold q64GoodCompletionFiber
  simp [q64_mem_completionFiber]

/--
Universally blocked triples: every lower-arity-clean completion in the missing coordinate is a
quartic blocker.
-/
def q64BadTripleSet
    (Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)) :
    Finset (Q64CornerTriple A₁ A₂ B₂) :=
  (q64TripleSet Gamma).filter fun tau => q64GoodCompletionFiber Gamma B4 tau = ∅

lemma q64_mem_badTripleSet
    {Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)}
    {tau : Q64CornerTriple A₁ A₂ B₂} :
    tau ∈ q64BadTripleSet Gamma B4 ↔
      tau ∈ q64TripleSet Gamma ∧ q64GoodCompletionFiber Gamma B4 tau = ∅ := by
  unfold q64BadTripleSet
  simp

/-- The nonterminal certifying-quartet statement: some clean quartet is not a quartic blocker. -/
def Q64QuarticBlockerNoncover
    (Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)) : Prop :=
  ∃ x, x ∈ Gamma ∧ x ∉ B4

/-- Triple noncover: not every clean triple is universally blocked along the missing fiber. -/
def Q64TripleNoncover
    (Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)) : Prop :=
  ∃ tau, tau ∈ q64TripleSet Gamma ∧ tau ∉ q64BadTripleSet Gamma B4

lemma q64_existsCleanQuartet_not_blocked_iff_exists_goodTriple
    {Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)} :
    Q64QuarticBlockerNoncover Gamma B4 ↔
      ∃ tau, tau ∈ q64TripleSet Gamma ∧ (q64GoodCompletionFiber Gamma B4 tau).Nonempty := by
  constructor
  · rintro ⟨x, hxG, hxB⟩
    refine ⟨x.1, ?_, ?_⟩
    · unfold q64TripleSet
      exact Finset.mem_image.mpr ⟨x, hxG, rfl⟩
    · refine ⟨x.2, ?_⟩
      exact q64_mem_goodCompletionFiber.mpr ⟨by simpa using hxG, by simpa using hxB⟩
  · rintro ⟨tau, _htau, hgood⟩
    rcases hgood with ⟨u, hu⟩
    exact ⟨(tau, u), (q64_mem_goodCompletionFiber.mp hu).1,
      (q64_mem_goodCompletionFiber.mp hu).2⟩

/--
Pure finite reduction of the nonterminal side:
`Gamma_4 \ B_4` is nonempty iff `Tri_u \ Bad_u` is nonempty.
-/
theorem q64_existsCleanQuartet_not_blocked_iff_triple_noncover
    {Gamma B4 : Finset (Q64CornerQuartet A₁ A₂ B₂ B₁)} :
    Q64QuarticBlockerNoncover Gamma B4 ↔ Q64TripleNoncover Gamma B4 := by
  rw [q64_existsCleanQuartet_not_blocked_iff_exists_goodTriple]
  unfold Q64TripleNoncover
  constructor
  · rintro ⟨tau, htau, hgood⟩
    refine ⟨tau, htau, ?_⟩
    intro hbad
    have hempty := (q64_mem_badTripleSet.mp hbad).2
    rw [hempty] at hgood
    exact Finset.not_nonempty_empty hgood
  · rintro ⟨tau, htau, hnotbad⟩
    refine ⟨tau, htau, ?_⟩
    by_contra hno
    have hempty : q64GoodCompletionFiber Gamma B4 tau = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hno
    exact hnotbad (q64_mem_badTripleSet.mpr ⟨htau, hempty⟩)

/-- A three-edge `L`-corner in the visible triple coordinates. -/
def Q64LCorner
    (x₀ x₁ : A₁) (y₀ y₁ : A₂) (z₀ z₁ : B₂) :
    Finset (Q64CornerTriple A₁ A₂ B₂) :=
  {(x₀, y₀, z₀), (x₁, y₀, z₁), (x₁, y₁, z₀)}

/-- A triple system has the saturated `L`-corner normal form from the notes. -/
def IsQ64LCorner (Sigma : Finset (Q64CornerTriple A₁ A₂ B₂)) : Prop :=
  ∃ x₀ x₁ : A₁, ∃ y₀ y₁ : A₂, ∃ z₀ z₁ : B₂,
    Sigma = Q64LCorner x₀ x₁ y₀ y₁ z₀ z₁

lemma q64_mem_LCorner_iff
    {x₀ x₁ : A₁} {y₀ y₁ : A₂} {z₀ z₁ : B₂}
    {tau : Q64CornerTriple A₁ A₂ B₂} :
    tau ∈ Q64LCorner x₀ x₁ y₀ y₁ z₀ z₁ ↔
      tau = (x₀, y₀, z₀) ∨ tau = (x₁, y₀, z₁) ∨ tau = (x₁, y₁, z₀) := by
  unfold Q64LCorner
  simp

section BinarySliceRelations

variable {U : Type*} [DecidableEq U]

/--
The completion fiber of an `R_x` edge through the two relations incident with the eliminated root.
-/
def q64EdgeCompletionFiber (R_y R_z : Finset (U × U)) (e : U × U) : Finset U :=
  ((R_y.filter fun p => p.2 = e.1).image Prod.fst) ∩
    ((R_z.filter fun p => p.2 = e.2).image Prod.fst)

lemma q64_mem_edgeCompletionFiber
    {R_y R_z : Finset (U × U)} {e : U × U} {u : U} :
    u ∈ q64EdgeCompletionFiber R_y R_z e ↔
      (u, e.1) ∈ R_y ∧ (u, e.2) ∈ R_z := by
  unfold q64EdgeCompletionFiber
  constructor
  · intro hu
    rcases Finset.mem_inter.mp hu with ⟨hy, hz⟩
    rcases Finset.mem_image.mp hy with ⟨p, hp, hpu⟩
    rcases Finset.mem_filter.mp hp with ⟨hpRy, hp2⟩
    rcases Finset.mem_image.mp hz with ⟨q, hq, hqu⟩
    rcases Finset.mem_filter.mp hq with ⟨hqRz, hq2⟩
    cases p
    cases q
    simp_all
  · rintro ⟨hy, hz⟩
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(u, e.1), by simp [hy], rfl⟩
    · exact Finset.mem_image.mpr ⟨(u, e.2), by simp [hz], rfl⟩

/--
The distributed alternating hexagon data, recorded as the three binary slice compatibilities
around the corner.
-/
def Q64DistributedHexagon (R_y R_z R_x : Finset (U × U)) (u₀ u₁ u₂ : U) : Prop :=
  (u₀, u₁) ∈ R_y ∧ (u₀, u₂) ∈ R_z ∧ (u₁, u₂) ∈ R_x

/-- Existence of a labelled binary-slice triangle. -/
def Q64RelationTriangle (R_y R_z R_x : Finset (U × U)) : Prop :=
  ∃ u₀ u₁ u₂, Q64DistributedHexagon R_y R_z R_x u₀ u₁ u₂

/--
Composition obstruction `K`: an `R_x` edge has a nonempty completion fiber through `R_y` and `R_z`.
-/
def Q64CompositionObstruction (R_y R_z R_x : Finset (U × U)) : Prop :=
  ∃ e ∈ R_x, (q64EdgeCompletionFiber R_y R_z e).Nonempty

theorem q64_relationTriangle_iff_compositionObstruction
    {R_y R_z R_x : Finset (U × U)} :
    Q64RelationTriangle R_y R_z R_x ↔ Q64CompositionObstruction R_y R_z R_x := by
  constructor
  · rintro ⟨u₀, u₁, u₂, hy, hz, hx⟩
    refine ⟨(u₁, u₂), hx, ?_⟩
    exact ⟨u₀, q64_mem_edgeCompletionFiber.mpr ⟨hy, hz⟩⟩
  · rintro ⟨e, hx, hnonempty⟩
    rcases hnonempty with ⟨u₀, hu₀⟩
    rcases e with ⟨u₁, u₂⟩
    exact
      ⟨u₀, u₁, u₂, (q64_mem_edgeCompletionFiber.mp hu₀).1,
        (q64_mem_edgeCompletionFiber.mp hu₀).2, hx⟩

/-- The anti-composition / triangle-free endpoint statement for the three binary relations. -/
def Q64AntiComposition (R_y R_z R_x : Finset (U × U)) : Prop :=
  ∀ e ∈ R_x, q64EdgeCompletionFiber R_y R_z e = ∅

theorem q64_antiComposition_iff_not_relationTriangle
    {R_y R_z R_x : Finset (U × U)} :
    Q64AntiComposition R_y R_z R_x ↔ ¬ Q64RelationTriangle R_y R_z R_x := by
  rw [q64_relationTriangle_iff_compositionObstruction]
  unfold Q64AntiComposition Q64CompositionObstruction
  constructor
  · intro hanti hobs
    rcases hobs with ⟨e, he, hne⟩
    rw [hanti e he] at hne
    exact Finset.not_nonempty_empty hne
  · intro hno e he
    by_contra hneEmpty
    have hne : (q64EdgeCompletionFiber R_y R_z e).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hneEmpty
    exact hno ⟨e, he, hne⟩

/-- Common-shadow synchronization for every distributed hexagon. -/
def Q64TwoOffRootCommonShadowSynchronization
    (Synchronizes : U → U → U → Prop) (R_y R_z R_x : Finset (U × U)) : Prop :=
  ∀ ⦃u₀ u₁ u₂ : U⦄,
    Q64DistributedHexagon R_y R_z R_x u₀ u₁ u₂ → Synchronizes u₀ u₁ u₂

/-- The localized alternating-hexagon scalar theorem `S(T_hex) = 2`. -/
def Q64LocalizedAlternatingHexagonScalarTheorem
    (Synchronizes : U → U → U → Prop) (S : U → U → U → ℕ)
    (R_y R_z R_x : Finset (U × U)) : Prop :=
  ∀ ⦃u₀ u₁ u₂ : U⦄,
    Q64DistributedHexagon R_y R_z R_x u₀ u₁ u₂ →
      Synchronizes u₀ u₁ u₂ → S u₀ u₁ u₂ = 2

/--
The remaining host frontier after all current reductions: synchronize a distributed hexagon onto one
common Section 40 frame/shadow, then prove the localized scalar value is `2`.
-/
def Q64RemainingHostFrontier
    (Synchronizes : U → U → U → Prop) (S : U → U → U → ℕ)
    (R_y R_z R_x : Finset (U × U)) : Prop :=
  Q64TwoOffRootCommonShadowSynchronization Synchronizes R_y R_z R_x ∧
    Q64LocalizedAlternatingHexagonScalarTheorem Synchronizes S R_y R_z R_x

omit [DecidableEq U] in
theorem Q64RemainingHostFrontier.certifies
    {Synchronizes : U → U → U → Prop} {S : U → U → U → ℕ}
    {R_y R_z R_x : Finset (U × U)}
    (hfront : Q64RemainingHostFrontier Synchronizes S R_y R_z R_x)
    {u₀ u₁ u₂ : U} (hhex : Q64DistributedHexagon R_y R_z R_x u₀ u₁ u₂) :
    Synchronizes u₀ u₁ u₂ ∧ S u₀ u₁ u₂ = 2 := by
  exact ⟨hfront.1 hhex, hfront.2 hhex (hfront.1 hhex)⟩

end BinarySliceRelations

/--
Terminal scalar package on the height-`18` rung: the precursor contributes
`sigma = 1`, and the marked contribution is `eps_A + eps_B`.
-/
def Q64TerminalScalarData (epsA epsB sigma marked scalar : ℕ) : Prop :=
  epsA ≤ 1 ∧ epsB ≤ 1 ∧ sigma = 1 ∧ marked = epsA + epsB ∧ scalar = sigma + marked

theorem q64_terminalScalar_eq_two_iff
    {epsA epsB sigma marked scalar : ℕ}
    (h : Q64TerminalScalarData epsA epsB sigma marked scalar) :
    scalar = 2 ↔ epsA + epsB = 1 := by
  unfold Q64TerminalScalarData at h
  omega

/--
Common-localized hexagon scalar package: both marked deleted one-error adds are present
(`marked = 2`), side-swap symmetry gives `iotaA = iotaB`, and singleton mass is
`sigma = iotaA + iotaB`.
-/
def Q64HexagonScalarData (iotaA iotaB sigma marked scalar : ℕ) : Prop :=
  iotaA ≤ 1 ∧ iotaB ≤ 1 ∧ iotaA = iotaB ∧ sigma = iotaA + iotaB ∧ marked = 2 ∧
    scalar = sigma + marked

theorem q64_hexagonScalar_eq_two_iff
    {iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64HexagonScalarData iotaA iotaB sigma marked scalar) :
    scalar = 2 ↔ iotaA = 0 ∧ iotaB = 0 := by
  unfold Q64HexagonScalarData at h
  omega

theorem q64_hexagonScalar_cases
    {iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64HexagonScalarData iotaA iotaB sigma marked scalar) :
    (scalar = 2 ∧ sigma = 0) ∨ (scalar = 4 ∧ sigma = 2) := by
  unfold Q64HexagonScalarData at h
  omega

/--
Synchronized-seed scalar package from the common-frame branch.  The hidden seed error is a bit;
the two marked one-error contributions are always present, and the only possible extra scalar
mass is the symmetric pair `2 * epsSeed`.
-/
def Q64SynchronizedSeedScalarData
    (epsSeed iotaA iotaB sigma marked scalar : ℕ) : Prop :=
  epsSeed ≤ 1 ∧ iotaA = epsSeed ∧ iotaB = epsSeed ∧ sigma = 2 * epsSeed ∧
    marked = 2 ∧ scalar = sigma + marked

theorem q64_synchronizedSeedScalar_formula
    {epsSeed iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64SynchronizedSeedScalarData epsSeed iotaA iotaB sigma marked scalar) :
    scalar = 2 + 2 * epsSeed := by
  unfold Q64SynchronizedSeedScalarData at h
  omega

theorem q64_synchronizedSeedScalar_eq_two_iff
    {epsSeed iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64SynchronizedSeedScalarData epsSeed iotaA iotaB sigma marked scalar) :
    scalar = 2 ↔ epsSeed = 0 := by
  unfold Q64SynchronizedSeedScalarData at h
  omega

theorem q64_synchronizedSeedScalar_zero
    {epsSeed iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64SynchronizedSeedScalarData epsSeed iotaA iotaB sigma marked scalar)
    (hz : epsSeed = 0) :
    sigma = 0 ∧ scalar = 2 ∧ iotaA = 0 ∧ iotaB = 0 := by
  unfold Q64SynchronizedSeedScalarData at h
  omega

theorem q64_synchronizedSeedScalar_cases
    {epsSeed iotaA iotaB sigma marked scalar : ℕ}
    (h : Q64SynchronizedSeedScalarData epsSeed iotaA iotaB sigma marked scalar) :
    (epsSeed = 0 ∧ scalar = 2 ∧ sigma = 0) ∨
      (epsSeed = 1 ∧ scalar = 4 ∧ sigma = 2) := by
  unfold Q64SynchronizedSeedScalarData at h
  omega

section TwoFiberRows

/--
The two-fiber row normal form after one-edge predecessor/persistence:
`d00` is the reference corner, the entries are bits, and persistence gives
`d10 ≤ d11` and `d01 ≤ d11`.
-/
def Q64TwoFiberRow (d00 d10 d01 d11 : ℕ) : Prop :=
  d00 = 0 ∧ d10 ≤ 1 ∧ d01 ≤ 1 ∧ d11 ≤ 1 ∧ d10 ≤ d11 ∧ d01 ≤ d11

/-- The exact two-fiber row list: `0000, 0001, 0101, 0011, 0111`. -/
theorem q64_twoFiberRow_iff {d00 d10 d01 d11 : ℕ} :
    Q64TwoFiberRow d00 d10 d01 d11 ↔
      (d00 = 0 ∧ d10 = 0 ∧ d01 = 0 ∧ d11 = 0) ∨
      (d00 = 0 ∧ d10 = 0 ∧ d01 = 0 ∧ d11 = 1) ∨
      (d00 = 0 ∧ d10 = 1 ∧ d01 = 0 ∧ d11 = 1) ∨
      (d00 = 0 ∧ d10 = 0 ∧ d01 = 1 ∧ d11 = 1) ∨
      (d00 = 0 ∧ d10 = 1 ∧ d01 = 1 ∧ d11 = 1) := by
  unfold Q64TwoFiberRow
  omega

def q64RowInOmega10 (d10 : ℕ) : Prop := d10 = 1

def q64RowInOmega01 (d01 : ℕ) : Prop := d01 = 1

theorem q64_twoFiberRow_in_neither_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    ¬ q64RowInOmega10 d10 ∧ ¬ q64RowInOmega01 d01 ↔
      (d00 = 0 ∧ d10 = 0 ∧ d01 = 0 ∧ d11 = 0) ∨
      (d00 = 0 ∧ d10 = 0 ∧ d01 = 0 ∧ d11 = 1) := by
  unfold Q64TwoFiberRow q64RowInOmega10 q64RowInOmega01 at *
  omega

theorem q64_twoFiberRow_inOmega10_notOmega01_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64RowInOmega10 d10 ∧ ¬ q64RowInOmega01 d01 ↔
      d00 = 0 ∧ d10 = 1 ∧ d01 = 0 ∧ d11 = 1 := by
  unfold Q64TwoFiberRow q64RowInOmega10 q64RowInOmega01 at *
  omega

theorem q64_twoFiberRow_inOmega01_notOmega10_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64RowInOmega01 d01 ∧ ¬ q64RowInOmega10 d10 ↔
      d00 = 0 ∧ d10 = 0 ∧ d01 = 1 ∧ d11 = 1 := by
  unfold Q64TwoFiberRow q64RowInOmega10 q64RowInOmega01 at *
  omega

theorem q64_twoFiberRow_inOmega10_andOmega01_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64RowInOmega10 d10 ∧ q64RowInOmega01 d01 ↔
      d00 = 0 ∧ d10 = 1 ∧ d01 = 1 ∧ d11 = 1 := by
  unfold Q64TwoFiberRow q64RowInOmega10 q64RowInOmega01 at *
  omega

/-- Mixed second difference of a terminal two-fiber row. -/
def q64TwoFiberMixedSecondDifference (d00 d10 d01 d11 : ℕ) : ℤ :=
  (d11 : ℤ) - d10 - d01 + d00

/--
For the five allowed terminal rows, the mixed second difference is one of `+1,0,-1`.
The positive row is `0001`; the negative row is `0111`.
-/
theorem q64_twoFiberMixedSecondDifference_cases
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64TwoFiberMixedSecondDifference d00 d10 d01 d11 = 1 ∨
      q64TwoFiberMixedSecondDifference d00 d10 d01 d11 = 0 ∨
        q64TwoFiberMixedSecondDifference d00 d10 d01 d11 = -1 := by
  rcases q64_twoFiberRow_iff.mp hrow with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp [q64TwoFiberMixedSecondDifference]

/-- The unique positive mixed row is `0001`. -/
theorem q64_twoFiberMixedSecondDifference_pos_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64TwoFiberMixedSecondDifference d00 d10 d01 d11 = 1 ↔
      d00 = 0 ∧ d10 = 0 ∧ d01 = 0 ∧ d11 = 1 := by
  rcases q64_twoFiberRow_iff.mp hrow with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp [q64TwoFiberMixedSecondDifference]

/-- The unique negative mixed row is `0111`. -/
theorem q64_twoFiberMixedSecondDifference_neg_iff
    {d00 d10 d01 d11 : ℕ} (hrow : Q64TwoFiberRow d00 d10 d01 d11) :
    q64TwoFiberMixedSecondDifference d00 d10 d01 d11 = -1 ↔
      d00 = 0 ∧ d10 = 1 ∧ d01 = 1 ∧ d11 = 1 := by
  rcases q64_twoFiberRow_iff.mp hrow with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp [q64TwoFiberMixedSecondDifference]

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Rows contributing to `Omega_10`. -/
def q64Omega10 (d10 : K → ℕ) : Finset K :=
  Finset.univ.filter fun k => d10 k = 1

/-- Rows contributing to `Omega_01`. -/
def q64Omega01 (d01 : K → ℕ) : Finset K :=
  Finset.univ.filter fun k => d01 k = 1

omit [DecidableEq K] in
lemma q64_mem_omega10 {d10 : K → ℕ} {k : K} :
    k ∈ q64Omega10 d10 ↔ d10 k = 1 := by
  unfold q64Omega10
  simp

omit [DecidableEq K] in
lemma q64_mem_omega01 {d01 : K → ℕ} {k : K} :
    k ∈ q64Omega01 d01 ↔ d01 k = 1 := by
  unfold q64Omega01
  simp

/--
The quotient-side two-fiber single-flip overlap lemma, isolated as the remaining graph-geometric
claim: nonempty `Omega_10` and `Omega_01` must overlap.
-/
def Q64TwoFiberSingleFlipOverlap (d10 d01 : K → ℕ) : Prop :=
  (q64Omega10 d10).Nonempty →
    (q64Omega01 d01).Nonempty →
      ((q64Omega10 d10) ∩ (q64Omega01 d01)).Nonempty

theorem q64_exists_0111_of_omega_inter_nonempty
    {d00 d10 d01 d11 : K → ℕ}
    (hrow : ∀ k, Q64TwoFiberRow (d00 k) (d10 k) (d01 k) (d11 k))
    (hinter : ((q64Omega10 d10) ∩ (q64Omega01 d01)).Nonempty) :
    ∃ k, d00 k = 0 ∧ d10 k = 1 ∧ d01 k = 1 ∧ d11 k = 1 := by
  rcases hinter with ⟨k, hk⟩
  rcases Finset.mem_inter.mp hk with ⟨h10, h01⟩
  exact
    ⟨k, (q64_twoFiberRow_inOmega10_andOmega01_iff (hrow k)).mp
      ⟨q64_mem_omega10.mp h10, q64_mem_omega01.mp h01⟩⟩

/--
Under the allowed row list, a nonempty but disjoint `Omega_10/Omega_01` table is exactly witnessed
by a `0101` row and a `0011` row.
-/
theorem q64_mixed_pair_of_omega_nonempty_of_disjoint
    {d00 d10 d01 d11 : K → ℕ}
    (hrow : ∀ k, Q64TwoFiberRow (d00 k) (d10 k) (d01 k) (d11 k))
    (h10 : (q64Omega10 d10).Nonempty) (h01 : (q64Omega01 d01).Nonempty)
    (hdisj : (q64Omega10 d10 ∩ q64Omega01 d01) = ∅) :
    (∃ k, d00 k = 0 ∧ d10 k = 1 ∧ d01 k = 0 ∧ d11 k = 1) ∧
      ∃ l, d00 l = 0 ∧ d10 l = 0 ∧ d01 l = 1 ∧ d11 l = 1 := by
  rcases h10 with ⟨k, hk10⟩
  have hk01not : ¬ d01 k = 1 := by
    intro hk01
    have hkInter : k ∈ q64Omega10 d10 ∩ q64Omega01 d01 := by
      exact Finset.mem_inter.mpr ⟨hk10, q64_mem_omega01.mpr hk01⟩
    rw [hdisj] at hkInter
    simp at hkInter
  have hkPattern :=
    (q64_twoFiberRow_inOmega10_notOmega01_iff (hrow k)).mp
      ⟨q64_mem_omega10.mp hk10, hk01not⟩
  rcases h01 with ⟨l, hl01⟩
  have hl10not : ¬ d10 l = 1 := by
    intro hl10
    have hlInter : l ∈ q64Omega10 d10 ∩ q64Omega01 d01 := by
      exact Finset.mem_inter.mpr ⟨q64_mem_omega10.mpr hl10, hl01⟩
    rw [hdisj] at hlInter
    simp at hlInter
  have hlPattern :=
    (q64_twoFiberRow_inOmega01_notOmega10_iff (hrow l)).mp
      ⟨q64_mem_omega01.mp hl01, hl10not⟩
  exact ⟨⟨k, hkPattern⟩, ⟨l, hlPattern⟩⟩

/--
The exact abstract remainder: with only the terminal two-fiber row axioms, nonempty opposite fibers
either overlap in a common `0111` row or else realize the mixed non-overlap pair `0101/0011`.
-/
theorem q64_twoFiber_overlap_or_mixed_pair
    {d00 d10 d01 d11 : K → ℕ}
    (hrow : ∀ k, Q64TwoFiberRow (d00 k) (d10 k) (d01 k) (d11 k))
    (h10 : (q64Omega10 d10).Nonempty) (h01 : (q64Omega01 d01).Nonempty) :
    ((q64Omega10 d10) ∩ (q64Omega01 d01)).Nonempty ∨
      ((∃ k, d00 k = 0 ∧ d10 k = 1 ∧ d01 k = 0 ∧ d11 k = 1) ∧
        ∃ l, d00 l = 0 ∧ d10 l = 0 ∧ d01 l = 1 ∧ d11 l = 1) := by
  by_cases hinter : ((q64Omega10 d10) ∩ (q64Omega01 d01)).Nonempty
  · exact Or.inl hinter
  · exact Or.inr
      (q64_mixed_pair_of_omega_nonempty_of_disjoint hrow h10 h01
        (Finset.not_nonempty_iff_eq_empty.mp hinter))

theorem q64_twoFiberSingleFlipOverlap_inter_ne_empty
    {d10 d01 : K → ℕ}
    (hoverlap : Q64TwoFiberSingleFlipOverlap d10 d01)
    (h10 : (q64Omega10 d10).Nonempty) (h01 : (q64Omega01 d01).Nonempty) :
    (q64Omega10 d10 ∩ q64Omega01 d01) ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (hoverlap h10 h01)

/-- The reduced non-overlap quotient-side table has exactly the two rows `0101` and `0011`. -/
def q64ReducedNonOverlapRowD00 (_ : Fin 2) : ℕ := 0

/-- The first coordinate of the reduced non-overlap quotient-side table. -/
def q64ReducedNonOverlapRowD10 (k : Fin 2) : ℕ := if k = 0 then 1 else 0

/-- The second coordinate of the reduced non-overlap quotient-side table. -/
def q64ReducedNonOverlapRowD01 (k : Fin 2) : ℕ := if k = 0 then 0 else 1

/-- The terminal coordinate of the reduced non-overlap quotient-side table. -/
def q64ReducedNonOverlapRowD11 (_ : Fin 2) : ℕ := 1

/-- The reduced non-overlap table satisfies the terminal two-fiber row axioms. -/
theorem q64_reducedNonOverlap_twoFiberRows :
    ∀ k : Fin 2,
      Q64TwoFiberRow (q64ReducedNonOverlapRowD00 k) (q64ReducedNonOverlapRowD10 k)
        (q64ReducedNonOverlapRowD01 k) (q64ReducedNonOverlapRowD11 k) := by
  intro k
  fin_cases k <;>
    simp [Q64TwoFiberRow, q64ReducedNonOverlapRowD00, q64ReducedNonOverlapRowD10,
      q64ReducedNonOverlapRowD01, q64ReducedNonOverlapRowD11]

/-- The reduced two-row table has both shadows nonempty but no common overlap. -/
theorem q64_reducedNonOverlap_twoFiberTable :
    (q64Omega10 q64ReducedNonOverlapRowD10).Nonempty ∧
      (q64Omega01 q64ReducedNonOverlapRowD01).Nonempty ∧
        q64Omega10 q64ReducedNonOverlapRowD10 ∩ q64Omega01 q64ReducedNonOverlapRowD01 = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, by simp [q64Omega10, q64ReducedNonOverlapRowD10]⟩
  · exact ⟨1, by simp [q64Omega01, q64ReducedNonOverlapRowD01]⟩
  · ext k
    fin_cases k <;> simp [q64Omega10, q64Omega01, q64ReducedNonOverlapRowD10,
      q64ReducedNonOverlapRowD01]

/-- The reduced table has no common `0111` witness. -/
theorem q64_reducedNonOverlap_no_common_0111 :
    ¬ ∃ k : Fin 2,
      q64ReducedNonOverlapRowD00 k = 0 ∧ q64ReducedNonOverlapRowD10 k = 1 ∧
        q64ReducedNonOverlapRowD01 k = 1 ∧ q64ReducedNonOverlapRowD11 k = 1 := by
  rintro ⟨k, _h00, h10, h01, _h11⟩
  fin_cases k <;> simp [q64ReducedNonOverlapRowD10, q64ReducedNonOverlapRowD01] at h10 h01

/-- Therefore the mixed non-overlap table is a genuine countermodel to pure abstract overlap. -/
theorem q64_reducedNonOverlap_not_twoFiberSingleFlipOverlap :
    ¬ Q64TwoFiberSingleFlipOverlap q64ReducedNonOverlapRowD10
      q64ReducedNonOverlapRowD01 := by
  intro hoverlap
  rcases q64_reducedNonOverlap_twoFiberTable with ⟨h10, h01, hdisj⟩
  have hinter := hoverlap h10 h01
  rw [hdisj] at hinter
  simpa using hinter

/--
The row list and nonempty opposite fibers alone do not force a common `0111` row.  The reduced
`{0101,0011}` table satisfies all raw two-fiber row axioms, so any closure of the missing-`0111`
endpoint must use additional boundary/provenance/history input.
-/
theorem q64_twoFiberRows_nonempty_do_not_force_common_0111 :
    ¬ (∀ (X : Type) [Fintype X] [DecidableEq X] (d00 d10 d01 d11 : X → ℕ),
        (∀ x, Q64TwoFiberRow (d00 x) (d10 x) (d01 x) (d11 x)) →
          (q64Omega10 d10).Nonempty →
            (q64Omega01 d01).Nonempty →
              ∃ x, d00 x = 0 ∧ d10 x = 1 ∧ d01 x = 1 ∧ d11 x = 1) := by
  intro h
  rcases q64_reducedNonOverlap_twoFiberTable with ⟨h10, h01, _hdisj⟩
  exact q64_reducedNonOverlap_no_common_0111
    (h (X := Fin 2) q64ReducedNonOverlapRowD00 q64ReducedNonOverlapRowD10
      q64ReducedNonOverlapRowD01 q64ReducedNonOverlapRowD11
      q64_reducedNonOverlap_twoFiberRows h10 h01)

/--
Equivalently, raw terminal row axioms plus nonempty `Omega_10` and `Omega_01` do not imply the
two-fiber single-flip overlap conclusion.
-/
theorem q64_twoFiberRows_nonempty_do_not_force_overlap :
    ¬ (∀ (X : Type) [Fintype X] [DecidableEq X] (d00 d10 d01 d11 : X → ℕ),
        (∀ x, Q64TwoFiberRow (d00 x) (d10 x) (d01 x) (d11 x)) →
          (q64Omega10 d10).Nonempty →
            (q64Omega01 d01).Nonempty →
              ((q64Omega10 d10) ∩ (q64Omega01 d01)).Nonempty) := by
  intro h
  rcases q64_reducedNonOverlap_twoFiberTable with ⟨h10, h01, hdisj⟩
  have hoverlap :
      ((q64Omega10 q64ReducedNonOverlapRowD10) ∩
          (q64Omega01 q64ReducedNonOverlapRowD01)).Nonempty :=
    h (X := Fin 2) q64ReducedNonOverlapRowD00 q64ReducedNonOverlapRowD10
      q64ReducedNonOverlapRowD01 q64ReducedNonOverlapRowD11
      q64_reducedNonOverlap_twoFiberRows h10 h01
  rw [hdisj] at hoverlap
  rcases hoverlap with ⟨x, hx⟩
  simpa using hx

end TwoFiberRows

section RootedTemplateTransversal

variable {Anchor Candidate : Type*}

/-- The two-anchor subsets of a deleted-anchor set. -/
def q64AnchorPairs (D : Finset Anchor) : Finset (Finset Anchor) :=
  D.powerset.filter fun E => E.card = 2

lemma q64_mem_anchorPairs {D E : Finset Anchor} :
    E ∈ q64AnchorPairs D ↔ E ⊆ D ∧ E.card = 2 := by
  unfold q64AnchorPairs
  simp

/--
Candidatewise rooted two-switch extraction: every candidate completer for the full compatible
multi-swap already completes a two-anchor subswap.
-/
def Q64CandidatewiseTwoSwitchExtraction
    (D : Finset Anchor) (Completes : Candidate → Finset Anchor → Prop) : Prop :=
  ∀ v, Completes v D → ∃ E ∈ q64AnchorPairs D, Completes v E

/--
The candidatewise extraction theorem implies the pair-density conclusion for the finite candidate
set: a positive full multi-swap has a positive two-subswap.
-/
theorem q64_positive_pair_of_candidatewise_twoSwitch
    {D : Finset Anchor} {Completes : Candidate → Finset Anchor → Prop}
    (hextract : Q64CandidatewiseTwoSwitchExtraction D Completes)
    (hpos : ∃ v, Completes v D) :
    ∃ E ∈ q64AnchorPairs D, ∃ v, Completes v E := by
  rcases hpos with ⟨v, hv⟩
  rcases hextract v hv with ⟨E, hE, hcomp⟩
  exact ⟨E, hE, v, hcomp⟩

variable {Fiber : Type*} [Fintype Fiber] [DecidableEq Fiber]

/--
Integer-valued low-degree vector: fibers in `I` have degree `delta - 1`, and all other fibers have
degree `delta`.
-/
def Q64LowDegreeVector (I : Finset Fiber) (d : Fiber → ℤ) (delta : ℤ) : Prop :=
  ∀ F, (F ∈ I → d F = delta - 1) ∧ (F ∉ I → d F = delta)

/--
If the low fibers are exactly `I`, then the total degree is
`|F| * delta - |I|`.  This is the arithmetic part of the equitable-seed-to-degree-congruent
reduction.
-/
theorem q64_sum_lowDegreeVector
    {I : Finset Fiber} {d : Fiber → ℤ} {delta : ℤ}
    (h : Q64LowDegreeVector I d delta) :
    (Finset.univ.sum d : ℤ) = (Fintype.card Fiber : ℤ) * delta - (I.card : ℤ) := by
  classical
  let J : Finset Fiber := Finset.univ \ I
  have hdisj : Disjoint I J := by
    unfold J
    exact Finset.disjoint_sdiff
  have hunion : I ∪ J = Finset.univ := by
    unfold J
    ext F
    by_cases hF : F ∈ I <;> simp [hF]
  calc
    (Finset.univ.sum d : ℤ) = (I ∪ J).sum d := by rw [hunion]
    _ = I.sum d + J.sum d := by exact Finset.sum_union hdisj
    _ = I.sum (fun _ => delta - 1) + J.sum (fun _ => delta) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro F hF
        exact (h F).1 hF
      · apply Finset.sum_congr rfl
        intro F hF
        exact (h F).2 (Finset.mem_sdiff.mp hF).2
    _ = (I.card : ℤ) * (delta - 1) + (J.card : ℤ) * delta := by
      simp [Finset.sum_const]
      ring_nf
    _ = (I.card : ℤ) * delta - (I.card : ℤ) + (J.card : ℤ) * delta := by
      ring_nf
    _ = ((I.card : ℤ) + (J.card : ℤ)) * delta - (I.card : ℤ) := by
      ring_nf
    _ = (Fintype.card Fiber : ℤ) * delta - (I.card : ℤ) := by
      have hcard : I.card + J.card = Fintype.card Fiber := by
        have hcardUnion := congrArg Finset.card hunion
        rw [Finset.card_union_of_disjoint hdisj] at hcardUnion
        simpa using hcardUnion
      have hcardz : (I.card : ℤ) + (J.card : ℤ) = (Fintype.card Fiber : ℤ) := by
        exact_mod_cast hcard
      rw [← hcardz]

end RootedTemplateTransversal

section SharedSliceExchange

/--
Binary normal form for a load-preserving shared-slice pair exchange:
the endpoint degree changes are determined by the signed outside-transfer sum and the internal
edge-status change.
-/
def Q64PairExchangeBinaryNormalForm
    (transfer eps eps' deltaF deltaG : ℤ) : Prop :=
  deltaF = transfer + (eps' - eps) ∧ deltaG = -transfer + (eps' - eps)

theorem q64_pairExchange_unit_transfer
    {transfer eps eps' deltaF deltaG : ℤ}
    (h : Q64PairExchangeBinaryNormalForm transfer eps eps' deltaF deltaG)
    (hstatus : eps' = eps) (htransfer : transfer = -1) :
    deltaF = -1 ∧ deltaG = 1 := by
  unfold Q64PairExchangeBinaryNormalForm at h
  omega

/-- A fixed-status feasible outside-load spectrum is an integer interval. -/
def Q64FixedStatusInterval (Lambda : Finset ℤ) : Prop :=
  ∃ lo hi : ℤ, ∀ z : ℤ, z ∈ Lambda ↔ lo ≤ z ∧ z ≤ hi

/--
The interval plus predecessor/nonminimality part: if the reference load is in an interval and is
not minimal, then the predecessor load is feasible.
-/
theorem q64_fixedStatus_predecessor_mem_of_interval
    {Lambda : Finset ℤ} {lo hi ref : ℤ}
    (hLambda : ∀ z : ℤ, z ∈ Lambda ↔ lo ≤ z ∧ z ≤ hi)
    (href : ref ∈ Lambda) (hlo : lo < ref) :
    ref - 1 ∈ Lambda := by
  rw [hLambda] at href ⊢
  omega

/-- The two-fiber missing-corner / anti-Horn square theorem for a feasible bit table. -/
def Q64TwoFiberMissingCorner (Feasible : Bool → Bool → Prop) : Prop :=
  Feasible false false → Feasible true false → Feasible false true → Feasible true true

theorem q64_no_three_corner_counterexample_of_missingCorner
    {Feasible : Bool → Bool → Prop}
    (hcorner : Q64TwoFiberMissingCorner Feasible) :
    ¬ (Feasible false false ∧ Feasible true false ∧ Feasible false true ∧
      ¬ Feasible true true) := by
  rintro ⟨h00, h10, h01, hnot11⟩
  exact hnot11 (hcorner h00 h10 h01)

/-- The abstract anti-Horn feasible set `{00,10,01}` from the pair-exchange audit. -/
def q64AntiHornFeasible (x y : Bool) : Prop := x = false ∨ y = false

/-- The anti-Horn table has every one-coordinate predecessor from `00`, but misses `11`. -/
theorem q64_antiHorn_three_corner_counterexample :
    q64AntiHornFeasible false false ∧ q64AntiHornFeasible true false ∧
      q64AntiHornFeasible false true ∧ ¬ q64AntiHornFeasible true true := by
  simp [q64AntiHornFeasible]

/--
Concrete formal no-go for the packaged pair-exchange route: one-coordinate predecessor data alone do
not imply the mixed two-coordinate corner.
-/
theorem q64_antiHorn_not_twoFiberMissingCorner :
    ¬ Q64TwoFiberMissingCorner q64AntiHornFeasible := by
  intro hcorner
  rcases q64_antiHorn_three_corner_counterexample with ⟨h00, h10, h01, hnot11⟩
  exact hnot11 (hcorner h00 h10 h01)

end SharedSliceExchange

section OneCornerMedianFiber

variable {Point Witness Fiber : Type*}

/--
Ambient-to-fixed shared-slice lift: ambient binary-cylinder membership at the forced median point
produces an actual fixed-frame shadow point in the shared slice.
-/
def Q64AmbientToFixedSharedSliceLift
    (AmbientBinaryCylinder FixedFrameShadow SharedSliceEntry : Prop) : Prop :=
  AmbientBinaryCylinder → FixedFrameShadow ∧ SharedSliceEntry

/--
Prescribed shared-slice entry is the sharpened form: the fixed-frame shadow point lies in the
admissible shared-slice cylinder, not merely somewhere in the visible slice.
-/
def Q64PrescribedSharedSliceEntry
    (FixedFrameShadow SharedSliceEntry AdmissibleCylinderEntry : Prop) : Prop :=
  FixedFrameShadow → SharedSliceEntry → AdmissibleCylinderEntry

/--
One-corner median-fiber determinacy: on the distinguished median fiber, each local fiber is
all-or-nothing with respect to the incidence predicate.
-/
def Q64OneCornerMedianFiberCylinderDeterminacy
    (M : Set Point) (localFiber : Fiber → Set Point) (incidence : Point → Prop) : Prop :=
  ∀ F, (∀ ⦃m⦄, m ∈ M → m ∈ localFiber F → incidence m) ∨
    ∀ ⦃m⦄, m ∈ M → m ∈ localFiber F → ¬ incidence m

/--
Hidden-edge invariance for one witness on the median fiber.
-/
def Q64HiddenEdgeInvariance
    (M : Set Point) (Step : Point → Point → Prop) (sees : Witness → Point → Prop) : Prop :=
  ∀ a ⦃x y⦄, x ∈ M → y ∈ M → Step x y → (sees a x ↔ sees a y)

/--
Single-witness median-fiber monotonicity: every hidden-edge path inside the median fiber preserves
the witness incidence.
-/
def Q64SingleWitnessMedianFiberMonotonicity
    (M : Set Point) (Step : Point → Point → Prop) (sees : Witness → Point → Prop) : Prop :=
  ∀ a ⦃x y⦄,
    Relation.ReflTransGen (fun p q => p ∈ M ∧ q ∈ M ∧ Step p q) x y →
      (sees a x ↔ sees a y)

/-- Hidden-edge invariance along edges implies single-witness monotonicity along hidden-edge paths. -/
theorem q64_singleWitnessMonotonicity_of_hiddenEdgeInvariance
    {M : Set Point} {Step : Point → Point → Prop} {sees : Witness → Point → Prop}
    (hinv : Q64HiddenEdgeInvariance M Step sees) :
    Q64SingleWitnessMedianFiberMonotonicity M Step sees := by
  intro a x y hpath
  induction hpath with
  | refl => exact Iff.rfl
  | tail _hxy hyz ih =>
      exact ih.trans (hinv a hyz.1 hyz.2.1 hyz.2.2)

/-- Integer mixed second difference on the normalized hidden median square. -/
def q64MedianSquareMixedSecondDifference (p : Bool → Bool → ℤ) : ℤ :=
  p true true - p true false - p false true + p false false

/-- The single-witness median-square interaction sign law. -/
def Q64MedianSquareInteractionSignLaw (p : Bool → Bool → ℤ) : Prop :=
  q64MedianSquareMixedSecondDifference p ≤ 0

/-- Integer-valued positive-AND square, the pointwise sign-law forbidden pattern. -/
def Q64IntPositiveANDAtom (p : Bool → Bool → ℤ) : Prop :=
  p false false = 0 ∧ p true false = 0 ∧ p false true = 0 ∧ p true true = 1

/-- A pointwise median-square sign law excludes the successor-side positive-AND square. -/
theorem q64_no_intPositiveAND_of_medianSquareSignLaw
    {p : Bool → Bool → ℤ} (hsign : Q64MedianSquareInteractionSignLaw p) :
    ¬ Q64IntPositiveANDAtom p := by
  intro hpos
  unfold Q64MedianSquareInteractionSignLaw at hsign
  rcases hpos with ⟨h00, h10, h01, h11⟩
  have hdiff : q64MedianSquareMixedSecondDifference p = 1 := by
    simp [q64MedianSquareMixedSecondDifference, h00, h10, h01, h11]
  rw [hdiff] at hsign
  omega

/-- The five terminal square row types left by the normalized endpoint catalogue. -/
inductive Q64TerminalSquareRow
  | r0000
  | r0001
  | r0101
  | r0011
  | r0111
  deriving DecidableEq, Repr

/-- Integer characteristic table for a terminal square row, in `(00,10,01,11)` order. -/
def Q64TerminalSquareRow.eval : Q64TerminalSquareRow → Bool → Bool → ℤ
  | .r0000, _, _ => 0
  | .r0001, true, true => 1
  | .r0001, _, _ => 0
  | .r0101, true, _ => 1
  | .r0101, false, _ => 0
  | .r0011, _, true => 1
  | .r0011, _, false => 0
  | .r0111, false, false => 0
  | .r0111, _, _ => 1

/-- In the terminal row catalogue, only `0001` has positive mixed second difference. -/
theorem q64_terminalSquareRow_positive_mixed_iff
    {row : Q64TerminalSquareRow} :
    0 < q64MedianSquareMixedSecondDifference row.eval ↔ row = .r0001 := by
  cases row <;> simp [Q64TerminalSquareRow.eval, q64MedianSquareMixedSecondDifference]

/-- In the terminal row catalogue, only `0111` has negative mixed second difference. -/
theorem q64_terminalSquareRow_negative_mixed_iff
    {row : Q64TerminalSquareRow} :
    q64MedianSquareMixedSecondDifference row.eval < 0 ↔ row = .r0111 := by
  cases row <;> simp [Q64TerminalSquareRow.eval, q64MedianSquareMixedSecondDifference]

/-- The raw-space Mobius cancellation identity for the terminal rows. -/
theorem q64_terminalSquareRow_mobius_identity :
    ∀ x y,
      Q64TerminalSquareRow.eval .r0001 x y + Q64TerminalSquareRow.eval .r0111 x y =
        Q64TerminalSquareRow.eval .r0101 x y + Q64TerminalSquareRow.eval .r0011 x y := by
  intro x y
  cases x <;> cases y <;>
    simp [Q64TerminalSquareRow.eval]

/--
Mobius-leak cycle endpoint: scalar mixed mass may cancel, but unless the cycle has trivial package
holonomy it reduces to a shortest rank-one successor-side `0001` loop.
-/
def Q64MobiusLeakCycleNormalForm
    (MobiusLeakCycle TrivialHolonomyTelescopes NontrivialHolonomyLoop SuccessorSide0001 : Prop) :
    Prop :=
  MobiusLeakCycle →
    TrivialHolonomyTelescopes ∨ (NontrivialHolonomyLoop ∧ SuccessorSide0001)

/--
Shortest nontrivial package-monodromy loops are reduced by any common-package chord; the survivor is a
sign-coherent simple cycle of adjacent package-change `0001` edges.
-/
def Q64MonodromyLoopChordlessNormalForm
    (ShortestNontrivialLoop CommonPackageChord ProperCommonPackageTelescoping
      SmallerOneCornerFailure SignCoherentSimple0001Cycle : Prop) : Prop :=
  ShortestNontrivialLoop →
    CommonPackageChord ∨ ProperCommonPackageTelescoping ∨ SmallerOneCornerFailure ∨
      SignCoherentSimple0001Cycle

/--
The final sign-coherent monodromy survivor carries a cyclic interval atom whose number of package
changes is bounded by the modulus.
-/
def Q64CyclicIntervalAtomBound
    (q : ℕ) (PackageChanges : Finset U) (CyclicIntervalAtom : Prop) : Prop :=
  CyclicIntervalAtom → PackageChanges.card ≤ q

/--
The moved coordinate orbit of a final monodromy cycle is anonymous to admissible rows unless a first
distinguishing edge already gives a smaller one-corner package failure.
-/
def Q64AnonymousCoordinateOrbitReduction
    (CoordinateOrbit AnonymousToAdmissibleRows SmallerOneCornerPackageFailure : Prop) : Prop :=
  CoordinateOrbit → AnonymousToAdmissibleRows ∨ SmallerOneCornerPackageFailure

/--
Nontrivial monodromy is the admissible-module-primality failure for the anonymous coordinate orbit:
without an ambient breaker it is a prime-shell module/local exit; with one, the breaker must be routed
into first-return provenance.
-/
def Q64MonodromyAsAdmissibleModuleFailure
    (NontrivialMonodromy PrimeShellModuleOrLocalExit AmbientBreakerNeedsRouting : Prop) : Prop :=
  NontrivialMonodromy → PrimeShellModuleOrLocalExit ∨ AmbientBreakerNeedsRouting

/--
Restricting a minimal ambient breaker to the cyclic monodromy order leaves either a consecutive
interval face or a crossing-cut primitive circuit face.
-/
def Q64CyclicBreakerRestrictionNormalForm
    (MinimalCyclicBreaker ConsecutiveIntervalFace CrossingPrimitiveCircuitFace : Prop) : Prop :=
  MinimalCyclicBreaker → ConsecutiveIntervalFace ∨ CrossingPrimitiveCircuitFace

/--
Choosing the cyclic breaker with the fewest sign changes sharpens the normal form to a two-transition
interval atom or a four-or-more-transition primitive circuit with no realized diagonal.
-/
def Q64FewestSignChangesCyclicBreaker
    (FewestSignChangesBreaker TwoTransitionIntervalAtom FourPlusTransitionPrimitiveNoDiagonal :
      Prop) : Prop :=
  FewestSignChangesBreaker → TwoTransitionIntervalAtom ∨ FourPlusTransitionPrimitiveNoDiagonal

/--
Abstract equal-residue cycles with only constant admissible rows demonstrate that cyclic arithmetic
alone does not promote a breaker to a realized first-return subcarrier.
-/
def Q64AbstractEqualResidueCycleNoPromotion
    (EqualResidueCycle ConstantAdmissibleRows AmbientSplitter NoPromotionFromArithmetic : Prop) :
    Prop :=
  EqualResidueCycle → ConstantAdmissibleRows → AmbientSplitter → NoPromotionFromArithmetic

/--
Omni-saturating the carrier collapses any longer active monodromy cycle to a bipartite module, a local
exit, or the single-active-pair endpoint.
-/
def Q64OmniSaturatedMonodromyCollapse
    (LongActiveMonodromy BipartiteModule LocalExit SingleActivePair : Prop) : Prop :=
  LongActiveMonodromy → BipartiteModule ∨ LocalExit ∨ SingleActivePair

/--
Breaker sign-normalization: constant-on-pair and opposite-sign breakers fall to local/common-package
cases, so the survivor is a same-sign separator row outside the admissible package.
-/
def Q64BreakerSignNormalization
    (Breaker ConstantOnPair OppositeSign LocalOrCommonPackage SameSignSeparatorOutsidePackage :
      Prop) : Prop :=
  Breaker →
    ConstantOnPair ∨ OppositeSign ∨ LocalOrCommonPackage ∨ SameSignSeparatorOutsidePackage

/-- If the closed sign-normalization branches are impossible, only the same-sign separator survives. -/
theorem q64_sameSignSeparator_of_breakerSignNormalization
    {Breaker ConstantOnPair OppositeSign LocalOrCommonPackage SameSignSeparatorOutsidePackage : Prop}
    (hnorm :
      Q64BreakerSignNormalization Breaker ConstantOnPair OppositeSign LocalOrCommonPackage
        SameSignSeparatorOutsidePackage)
    (hnoConst : ¬ ConstantOnPair) (hnoOpp : ¬ OppositeSign)
    (hnoLocal : ¬ LocalOrCommonPackage) (hbreaker : Breaker) :
    SameSignSeparatorOutsidePackage := by
  rcases hnorm hbreaker with hconst | hopp | hlocal | hsame
  · exact False.elim (hnoConst hconst)
  · exact False.elim (hnoOpp hopp)
  · exact False.elim (hnoLocal hlocal)
  · exact hsame

/--
Choosing a same-sign breaker with minimum side leaves either the singleton-side promotion gap or the
crossing primitive `2×2` circuit.
-/
def Q64MinimumSideBreakerNormalForm
    (MinimumSideBreaker SingletonSidePromotionGap CrossingPrimitiveCircuit : Prop) : Prop :=
  MinimumSideBreaker → SingletonSidePromotionGap ∨ CrossingPrimitiveCircuit

/--
The singleton-side promotion gap is stable under first-failed-row iteration: every departure closes
locally, contradicts minimum side, forms the primitive circuit, or leaves a high-error same-sign
isolator loop on one row.
-/
def Q64SingletonSideIterationNormalForm
    (SingletonSidePromotionGap LocalDeparture MinimumSideContradiction PrimitiveCircuit
      HighErrorSameSignIsolatorLoop : Prop) : Prop :=
  SingletonSidePromotionGap →
    LocalDeparture ∨ MinimumSideContradiction ∨ PrimitiveCircuit ∨ HighErrorSameSignIsolatorLoop

/--
After local quotienting, distinct isolators either coalesce by the same-trace/twin catalogue or
regenerate the same square-transverse breaker, leaving a single high-error isolator self-loop.
-/
def Q64IsolatorLoopQuotientNormalForm
    (HighErrorSameSignIsolatorLoop SameTraceTwinCoalescence SquareTransverseBreaker
      SingleHighErrorIsolatorSelfLoop : Prop) : Prop :=
  HighErrorSameSignIsolatorLoop →
    SameTraceTwinCoalescence ∨ SquareTransverseBreaker ∨ SingleHighErrorIsolatorSelfLoop

/--
Pure same-defect token loops close locally, so the remaining single isolator self-loop is the
defect-switching fully skew square.
-/
def Q64IsolatorSelfLoopToDefectSwitchingSquare
    (SingleHighErrorIsolatorSelfLoop PureSameDefectTokenLoopClosed DefectSwitchingFullySkewSquare :
      Prop) : Prop :=
  SingleHighErrorIsolatorSelfLoop →
    PureSameDefectTokenLoopClosed ∨ DefectSwitchingFullySkewSquare

/--
The defect-switching fully skew square is the final honest gap: a reduced trace model exists unless
genuine first-return history promotes the isolated row or a larger side to a complete transported bag.
-/
def Q64DefectSwitchingSelfLoopPromotionGap
    (DefectSwitchingFullySkewSquare IsolatedRowPromoted LargerSideCompleteTransportedBag
      ReducedTraceSelfLoopModel : Prop) : Prop :=
  DefectSwitchingFullySkewSquare →
    IsolatedRowPromoted ∨ LargerSideCompleteTransportedBag ∨ ReducedTraceSelfLoopModel

/--
If the defect-switching square is seated with the singleton isolator as first axis, the remaining rows
have zero mixed second difference, so the complete slack bag lies in a sub-`q` side and low-set
congruence closes that in-frame branch.
-/
def Q64SingletonFirstAxisSeatedClosure
    (SingletonFirstAxisSeated ZeroMixedSecondDifferenceRows SubqCompleteSlackSide
      LowSetCongruenceKilled : Prop) : Prop :=
  SingletonFirstAxisSeated →
    ZeroMixedSecondDifferenceRows ∧ SubqCompleteSlackSide ∧ LowSetCongruenceKilled

/--
Axis analysis for the final defect-switching square: either the singleton isolator is the first axis, or
first-return transport drifts the square to an incomparable first axis.
-/
def Q64DefectSwitchingSquareAxisAnalysis
    (DefectSwitchingFullySkewSquare SingletonFirstAxisSeated
      TransportDriftsToIncomparableFirstAxis : Prop) : Prop :=
  DefectSwitchingFullySkewSquare →
    SingletonFirstAxisSeated ∨ TransportDriftsToIncomparableFirstAxis

/--
Common-frame ordered axis-lock: first-return transport cannot drift to an incomparable first axis except
through a local exit or the primitive `2×2` circuit.
-/
def Q64CommonFrameOrderedAxisLock
    (TransportDriftsToIncomparableFirstAxis LocalExit PrimitiveCircuit : Prop) : Prop :=
  TransportDriftsToIncomparableFirstAxis → LocalExit ∨ PrimitiveCircuit

/--
Equivalent single-turn common-frame gluing form: consecutive dirty axes force the first
package-change edge to carry a complete smaller marker or a local exit.
-/
def Q64SingleTurnCommonFrameGluing
    (ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker LocalExit : Prop) : Prop :=
  ConsecutiveDirtyAxes → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit

/--
Hidden-median form of the common-frame gluing gap: nonempty opposite single-flip fibers `Omega_10`
and `Omega_01` must share a common `0111` witness, except for the abstract mixed non-overlap table
`{0101,0011}`.
-/
def Q64TwoFiberSingleFlipOverlapLemma
    (Omega10Nonempty Omega01Nonempty Common0111Witness MixedNonOverlapPair0101_0011 : Prop) :
    Prop :=
  Omega10Nonempty → Omega01Nonempty → Common0111Witness ∨ MixedNonOverlapPair0101_0011

/--
Binary pair-status constancy on the one-corner median fiber, in the form isolated by the final
hidden-median reduction: either the pair status is constant on that fiber, or the failure is already the
successor-side `0001` shared-slack marker.
-/
def Q64OneCornerMedianPairStatusConstancy
    (OneCornerMedianFiber PairStatusConstant SuccessorSide0001SharedSlackMarker : Prop) : Prop :=
  OneCornerMedianFiber → PairStatusConstant ∨ SuccessorSide0001SharedSlackMarker

/--
Scalar wall-order potentials cannot see the final obstruction: their edge signs are coboundaries with
zero square circulation, whereas the forbidden `0001` row is same-row two-face curvature.
-/
def Q64ScalarWallOrderPotentialNoGo
    (ScalarWallOrderPotential EdgeSignsAreCoboundaries ZeroSquareCirculation
      SameRowTwoFaceCurvature : Prop) : Prop :=
  ScalarWallOrderPotential →
    EdgeSignsAreCoboundaries ∧ ZeroSquareCirculation ∧ SameRowTwoFaceCurvature

/-- The same-row two-face curvature appears only after both successor increments are placed in one
peeled package. -/
def Q64SameRowCurvatureRequiresCommonPeeledPackage
    (SameRowTwoFaceCurvature BothSuccessorIncrementsInOnePeeledPackage : Prop) : Prop :=
  SameRowTwoFaceCurvature → BothSuccessorIncrementsInOnePeeledPackage

/--
Commutator form of common-frame gluing: consecutive dirty axes either have commuting successor package
identifications, or a nontrivial commutator remains.
-/
def Q64CommonFrameSuccessorCommutation
    (ConsecutiveDirtyAxes SuccessorPackageIdentificationsCommute NontrivialCommutator : Prop) :
    Prop :=
  ConsecutiveDirtyAxes → SuccessorPackageIdentificationsCommute ∨ NontrivialCommutator

/--
A nontrivial successor-package commutator is exactly the mixed `{0101,0011}` non-overlap table, or
after marking the first package leak, the positive `0001` shared-slack row.
-/
def Q64SuccessorPackageCommutatorNormalForm
    (NontrivialCommutator MixedNonOverlapPair0101_0011 Positive0001PackageLeak : Prop) : Prop :=
  NontrivialCommutator → MixedNonOverlapPair0101_0011 ∨ Positive0001PackageLeak

/--
Finite order of the package commutator produces only an anonymous coordinate orbit unless a boundary
splitter has already been promoted; the anonymous-orbit branch is just admissible-module primeness again.
-/
def Q64FiniteCommutatorOrderReduction
    (FiniteCommutatorOrder AnonymousCoordinateOrbit PromotedBoundarySplitter : Prop) : Prop :=
  FiniteCommutatorOrder → AnonymousCoordinateOrbit ∨ PromotedBoundarySplitter

/--
Flat-connection restatement of the final obstruction: every failure is a nonfilled repair face, a
curved filled face, or a flat nontrivial monodromy loop.
-/
def Q64FlatConnectionFailureTrichotomy
    (FlatConnectionFailure NonfilledRepairFace CurvedFilledFace FlatNontrivialMonodromyLoop :
      Prop) : Prop :=
  FlatConnectionFailure →
    NonfilledRepairFace ∨ CurvedFilledFace ∨ FlatNontrivialMonodromyLoop

/--
The three flat-connection failures are exactly the existing endpoints: square-transverse breaker,
shared-slack q-marker, and admissible-module primeness.
-/
def Q64FlatConnectionFailureEndpointIdentification
    (NonfilledRepairFace CurvedFilledFace FlatNontrivialMonodromyLoop SquareTransverseBreaker
      SharedSlackQMarker AdmissibleModulePrimenessAgain : Prop) : Prop :=
  (NonfilledRepairFace → SquareTransverseBreaker) ∧
    (CurvedFilledFace → SharedSlackQMarker) ∧
      (FlatNontrivialMonodromyLoop → AdmissibleModulePrimenessAgain)

/-- Shortest saturated flat loops leave no independent higher-polygon residue. -/
def Q64ShortestFlatLoopSaturation
    (ShortestFlatLoop OddCycle LongEvenCycle TwoPointAdjacentPackageChangeTurn ModuleOrLocalExit :
      Prop) : Prop :=
  ShortestFlatLoop → OddCycle ∨ LongEvenCycle ∨ TwoPointAdjacentPackageChangeTurn ∨ ModuleOrLocalExit

/-- Ternary dirty-row configurations close pairwise or reduce to the already-known flat/curved atoms. -/
def Q64TernaryDirtyRowReduction
    (TernaryDirtyRows PairwiseClosure FlatMonodromyTriangle Curved0001Face : Prop) : Prop :=
  TernaryDirtyRows → PairwiseClosure ∨ FlatMonodromyTriangle ∨ Curved0001Face

/--
Signed-edge normal form for the remaining adjacent turn: opposite signs give the balanced flip,
same signs give the singleton-isolator edge, and in either case the unresolved data are the dirty
chart change rather than the sign choice.
-/
def Q64AdjacentTurnSignedEdgeNormalForm
    (AdjacentTurn OppositeSigns BalancedFlip SameSigns SingletonIsolatorEdge DirtyChartChange :
      Prop) : Prop :=
  AdjacentTurn →
    (OppositeSigns ∧ BalancedFlip ∧ DirtyChartChange) ∨
      (SameSigns ∧ SingletonIsolatorEdge ∧ DirtyChartChange)

/--
Carrier trichotomy for the dirty chart-change edge: it has a proper complete subcarrier, crosses another
dirty edge as the primitive `2×2` circuit, or is an admissible module split only by a non-promoted
ambient row.
-/
def Q64DirtyChartChangeCarrierTrichotomy
    (DirtyChartChangeCarrier ProperCompleteSubcarrier Primitive2x2Circuit
      NonPromotedAmbientSplitAdmissibleModule : Prop) : Prop :=
  DirtyChartChangeCarrier →
    ProperCompleteSubcarrier ∨ Primitive2x2Circuit ∨ NonPromotedAmbientSplitAdmissibleModule

/-- Minimum-side normalization on the admissible-module branch returns to the singleton-isolator
self-loop. -/
def Q64AdmissibleModuleMinimumSideSingletonLoop
    (AdmissibleModuleFailure MinimumSideNormalization SingletonIsolatorSelfLoop : Prop) : Prop :=
  AdmissibleModuleFailure → MinimumSideNormalization → SingletonIsolatorSelfLoop

/--
Out-of-frame axis drift is the same rank-one frame slip: it is a nonfilled face, a curved face, a flat
monodromy loop, or the irreducible dirty chart-change edge.
-/
def Q64OutOfFrameAxisDriftRankOneSlip
    (OutOfFrameAxisDrift NonfilledFace CurvedFace FlatMonodromyLoop DirtyChartChangeEdge : Prop) :
    Prop :=
  OutOfFrameAxisDrift → NonfilledFace ∨ CurvedFace ∨ FlatMonodromyLoop ∨ DirtyChartChangeEdge

/--
Reduced two-chart boundary-certificate endpoint for the dirty slip: the slipped coordinate must carry a
complete shared-slack side, or its absence is a smaller square-transverse breaker.
-/
def Q64TwoChartSlipBoundaryCertificate
    (DirtyChartChangeEdge CompleteSharedSlackSide SmallerSquareTransverseBreaker : Prop) : Prop :=
  DirtyChartChangeEdge → CompleteSharedSlackSide ∨ SmallerSquareTransverseBreaker

/--
Once the slipped splitter is an ordered boundary row, the two-chart boundary certificate is formal: the
internal failure set is a whole splitter side and hence a smaller complete marker.
-/
def Q64OrderedBoundarySlipCertificate
    (OrderedBoundaryRow InternalFailureWholeSplitterSide SmallerCompleteMarker : Prop) : Prop :=
  OrderedBoundaryRow → InternalFailureWholeSplitterSide ∧ SmallerCompleteMarker

/--
Ambient-to-boundary transport endpoint: transport reaches an ordered boundary row, exits locally, or
leaves the minimal one-state high-error bounce on the same slipped side.
-/
def Q64AmbientToBoundaryTransportWithBounce
    (AmbientSplitter OrderedBoundaryRow LocalExit OneStateHighErrorBounceSameSlippedSide : Prop) :
    Prop :=
  AmbientSplitter → OrderedBoundaryRow ∨ LocalExit ∨ OneStateHighErrorBounceSameSlippedSide

/--
The one-state bounce is the common shadow of the three named host frontiers; if none of them kills it,
the survivor is the same missing-`0111` table.
-/
def Q64OneStateBounceHostFrontierShadow
    (OneStateHighErrorBounce PairChamberHiddenChoiceSeparation AnchoredPersistenceNoSplitQPlus
      AnchoredOneCornerLiftQj Missing0111Table : Prop) : Prop :=
  OneStateHighErrorBounce →
    PairChamberHiddenChoiceSeparation ∨ AnchoredPersistenceNoSplitQPlus ∨
      AnchoredOneCornerLiftQj ∨ Missing0111Table

/--
A prime-shell breaker of the two bounced rows reduces to a same-cut high-error clone packet: an
admissible module whose ambient breaker is still not promoted.
-/
def Q64SameCutHighErrorClonePacketReduction
    (PrimeShellBreakerOfBouncedRows SameCutHighErrorClonePacket
      AdmissibleModuleWithUnpromotedAmbientBreaker : Prop) : Prop :=
  PrimeShellBreakerOfBouncedRows →
    SameCutHighErrorClonePacket ∧ AdmissibleModuleWithUnpromotedAmbientBreaker

/--
Recentring on two clone rows is self-similar: it does not decrease the carrier; maximal clone packets
form a directed package-change cycle; saturation reduces that cycle to the two-packet `{0101,0011}` atom
unless a boundary provenance certificate breaks the loop.
-/
def Q64ClonePacketCycleReduction
    (SameCutHighErrorClonePacket BoundaryProvenanceCertificate TwoPacketNonOverlapAtom0101_0011 :
      Prop) : Prop :=
  SameCutHighErrorClonePacket → BoundaryProvenanceCertificate ∨ TwoPacketNonOverlapAtom0101_0011

/--
If same-cut clone closure were hereditary under ambient breakers, primeness would close the endpoint by
a module argument; the missing heredity is exactly boundary provenance.
-/
def Q64SameCutCloneHeredityOrBoundaryProvenance
    (SameCutCloneClosure HereditaryUnderAmbientBreakers ModuleClosure BoundaryProvenance : Prop) :
    Prop :=
  SameCutCloneClosure → (HereditaryUnderAmbientBreakers ∧ ModuleClosure) ∨ BoundaryProvenance

/--
Acyclic clone-package graphs close by the same module argument, so the hereditary failure is a two-state
package transposition.
-/
def Q64ClonePackageGraphReduction
    (ClonePackageGraph AcyclicClonePackageGraph TwoStatePackageTransposition : Prop) : Prop :=
  ClonePackageGraph → AcyclicClonePackageGraph ∨ TwoStatePackageTransposition

/--
The two-state package transposition is the rank-one flat holonomy/missing-`0111` atom.  Its anchored
subcase closes; an irreducible transposition moves the anchor and is the anchored frame-slip endpoint.
-/
def Q64TwoStateTranspositionFrameSlip
    (TwoStatePackageTransposition AnchoredSubcaseClosed IrreducibleMovesAnchor
      AnchoredFrameSlipEndpoint : Prop) : Prop :=
  TwoStatePackageTransposition → AnchoredSubcaseClosed ∨
    (IrreducibleMovesAnchor ∧ AnchoredFrameSlipEndpoint)

/--
Choosing the first package-label change on a shortest flat anchor path reduces an anchored frame slip to
a single chamber-flat anchored slip edge.
-/
def Q64ShortestFlatAnchorPathReduction
    (AnchoredFrameSlipEndpoint SingleChamberFlatAnchoredSlipEdge : Prop) : Prop :=
  AnchoredFrameSlipEndpoint → SingleChamberFlatAnchoredSlipEdge

/--
The one-corner lift kills the single chamber-flat anchored slip; failure of that lift is the `0001`
square.
-/
def Q64SingleChamberFlatSlipLiftDichotomy
    (SingleChamberFlatAnchoredSlipEdge OneCornerLiftClosed OneCornerLiftFailure0001Square : Prop) :
    Prop :=
  SingleChamberFlatAnchoredSlipEdge → OneCornerLiftClosed ∨ OneCornerLiftFailure0001Square

/--
One-edge form of the endpoint: a minimal square-transverse breaker whose first dirty failed row is fully
skew on the same support and changes only the hidden package label has exactly the two-fiber
non-overlap table with missing `0111`.
-/
def Q64OneEdgeHiddenLabelSlipNormalForm
    (MinimalSquareTransverseBreaker FirstDirtyRowFullySkewSameSupport HiddenPackageLabelOnlyChange
      TwoFiberNonOverlapMissing0111 : Prop) : Prop :=
  MinimalSquareTransverseBreaker → FirstDirtyRowFullySkewSameSupport →
    HiddenPackageLabelOnlyChange → TwoFiberNonOverlapMissing0111

/--
Hidden-cover formulation: visible chamber data carry an unbranched nontrivial two-sheeted
hidden-package cover, equivalently a nonzero flat `Z/2` holonomy class.
-/
def Q64HiddenPackageCoverHolonomy
    (VisibleChamberData UnbranchedNontrivialTwoSheetedHiddenPackageCover
      NonzeroFlatZMod2HolonomyClass : Prop) : Prop :=
  VisibleChamberData →
    UnbranchedNontrivialTwoSheetedHiddenPackageCover ∨ NonzeroFlatZMod2HolonomyClass

/--
Branch points of the hidden package cover are exactly one-corner lift failures or square-transverse
breakers; odd filled faces are the `0001` marker.
-/
def Q64HiddenCoverBranchPointClassification
    (HiddenPackageCoverBranchPoint OneCornerLiftFailure SquareTransverseBreaker OddFilledFace
      Marker0001 : Prop) : Prop :=
  (HiddenPackageCoverBranchPoint → OneCornerLiftFailure ∨ SquareTransverseBreaker) ∧
    (OddFilledFace → Marker0001)

/-- Coordinate cancellation kills hidden holonomy when every repeated-coordinate swap is filled and flat. -/
def Q64CoordinateCancellationKillsHolonomy
    (EveryRepeatedCoordinateSwapFilledFlat NonzeroFlatZMod2HolonomyClass : Prop) : Prop :=
  EveryRepeatedCoordinateSwapFilledFlat → ¬ NonzeroFlatZMod2HolonomyClass

/--
The remaining cubical input after coordinate cancellation: rank-one coordinate-swap completeness along
a shortest holonomy loop, or a live candidate-switching gate failure.
-/
def Q64RankOneCoordinateSwapCompleteness
    (ShortestHolonomyLoop CoordinateSwapComplete CandidateSwitchingGateFailure : Prop) : Prop :=
  ShortestHolonomyLoop → CoordinateSwapComplete ∨ CandidateSwitchingGateFailure

/--
The fixed-candidate half of coordinate-swap completeness is closed by interval arithmetic; a live
candidate-switching gate failure localizes to the three-corner anti-Horn square with absent `11`.
-/
def Q64CandidateSwitchingGateFailureNormalForm
    (CandidateSwitchingGateFailure FixedCandidateIntervalClosed ThreeCornerAntiHornMissing11 :
      Prop) : Prop :=
  CandidateSwitchingGateFailure →
    FixedCandidateIntervalClosed ∨ ThreeCornerAntiHornMissing11

/--
Candidate data on the anti-Horn square form a three-certificate cycle; repeated or sink certificates
return to the fixed-candidate interval calculation.
-/
def Q64ThreeCertificateCycleNormalForm
    (ThreeCornerAntiHornMissing11 ThreeCertificateCycle RepeatedCertificate SinkCertificate
      FixedCandidateIntervalCalculation : Prop) : Prop :=
  ThreeCornerAntiHornMissing11 →
    ThreeCertificateCycle ∨ RepeatedCertificate ∨ SinkCertificate ∨
      FixedCandidateIntervalCalculation

/--
First breakers on the three-certificate cycle have no independent ternary residue: two same-sign
breakers coalesce in one residual frame or expose the same two-state package-change edge.
-/
def Q64ThreeCertificateBreakerReduction
    (ThreeCertificateCycle SameSignBreakersCoalesce TwoStatePackageChangeEdge : Prop) : Prop :=
  ThreeCertificateCycle → SameSignBreakersCoalesce ∨ TwoStatePackageChangeEdge

/--
The geometric form of the certificate cycle is a distributed alternating hexagon, `K_{3,3}` minus a
perfect matching; once any cyclic five-vertex seed is localized on one Section 40 frame, the scalar part
is automatic and the live input is distributed-hexagon-to-one-frame synchronization.
-/
def Q64DistributedHexagonSynchronizationEndpoint
    (DistributedAlternatingHexagonK33MinusPerfectMatching Section40P5SeedLocalized
      DistributedHexagonToOneFrameSynchronization : Prop) : Prop :=
  DistributedAlternatingHexagonK33MinusPerfectMatching →
    Section40P5SeedLocalized ∨ DistributedHexagonToOneFrameSynchronization

/--
The distributed-hexagon synchronization endpoint is equivalent to ambient-to-fixed fiber-preserving
shared-slice lift, compatible degree-congruent transversal for one shared slice, and adjacent-slice
admissibility at the unique median-entry point.
-/
def Q64SharedSliceSynchronizationEquivalence
    (DistributedHexagonToOneFrameSynchronization AmbientToFixedFiberPreservingSharedSliceLift
      CompatibleDegreeCongruentTransversalOneSharedSlice AdjacentSliceAdmissibilityAtMedianEntry :
      Prop) : Prop :=
  (DistributedHexagonToOneFrameSynchronization ↔ AmbientToFixedFiberPreservingSharedSliceLift) ∧
    (AmbientToFixedFiberPreservingSharedSliceLift ↔
      CompatibleDegreeCongruentTransversalOneSharedSlice) ∧
      (CompatibleDegreeCongruentTransversalOneSharedSlice ↔
        AdjacentSliceAdmissibilityAtMedianEntry)

/--
The visible half of adjacent-slice lift is closed; the hidden half is single-witness uniformity on the
median fiber.  A mixed witness reduces to the successor-side `0001` square.
-/
def Q64MedianFiberUniformityEndpoint
    (AdjacentSliceAdmissibilityAtMedianEntry VisibleHalfClosed SingleWitnessUniformityOnMedianFiber
      MixedWitnessOnMedianFiber SuccessorSide0001Square : Prop) : Prop :=
  AdjacentSliceAdmissibilityAtMedianEntry →
    VisibleHalfClosed ∧
      (SingleWitnessUniformityOnMedianFiber ∨
        (MixedWitnessOnMedianFiber ∧ SuccessorSide0001Square))

/--
After one-edge predecessor/persistence inputs are factored off, the quotient table is again the
`{0101,0011}` table with missing `0111`, equivalently fixed pair-chamber cylinder rigidity for the
elementary hidden choice.
-/
def Q64FixedPairChamberCylinderRigidityEndpoint
    (PredecessorPersistenceFactored QuotientTable0101_0011Missing0111
      FixedPairChamberCylinderRigidity : Prop) : Prop :=
  PredecessorPersistenceFactored →
    (QuotientTable0101_0011Missing0111 ↔ FixedPairChamberCylinderRigidity)

/--
The intrinsic two-square form is elementary two-sided silent-component injectivity; basin localization
reduces it to boundary outgoing anchored witness persistence plus realized componentwise singleton on
`Q^+`.
-/
def Q64SilentComponentBasinLocalization
    (TwoSidedSilentComponentInjectivity BoundaryOutgoingAnchoredWitnessPersistence
      RealizedComponentwiseSingletonQPlus HostOpppair123Surface : Prop) : Prop :=
  TwoSidedSilentComponentInjectivity →
    BoundaryOutgoingAnchoredWitnessPersistence ∧ RealizedComponentwiseSingletonQPlus ∧
      HostOpppair123Surface

/--
The one-square endpoint is edgelessness of the silent graph or incident-square opposite-defect wall
detection; its minimal failure is one chamber-flat silent edge, and vertex potentials cannot exclude it.
-/
def Q64SilentGraphOneSquareEndpoint
    (EdgelessSilentGraph IncidentSquareOppositeDefectWallDetection ChamberFlatSilentEdge
      VertexPotentialsCannotExclude : Prop) : Prop :=
  EdgelessSilentGraph ∨ IncidentSquareOppositeDefectWallDetection ∨
    (ChamberFlatSilentEdge ∧ VertexPotentialsCannotExclude)

/--
Prefix-star sign uniqueness for silent edges with fixed lower packet prefix and first changed
coordinate: opposite signs force the anchored one-corner lift or the `0001` failure.
-/
def Q64PrefixStarSignUniqueness
    (SilentEdgeFixedLowerPacketPrefix FirstChangedCoordinate OppositeSigns AnchoredOneCornerLift
      SuccessorSide0001Failure : Prop) : Prop :=
  SilentEdgeFixedLowerPacketPrefix → FirstChangedCoordinate → OppositeSigns →
    AnchoredOneCornerLift ∨ SuccessorSide0001Failure

/--
Support-local fourth-corner route to transverse-breaker admissibility: fixed-candidate interval failures
close, clean marked support closes, and the only live case is dirty budget-one `Abs(1)` /
reanchor-breaker prime-shell cycle-breaker.
-/
def Q64SupportLocalFourthCornerToAbs1Route
    (SupportLocalFourthCorner FixedCandidateIntervalClosed CleanMarkedSupportClosed
      DirtyBudgetOneAbs1ReanchorBreaker TransverseBreakerAdmissibility : Prop) : Prop :=
  SupportLocalFourthCorner →
    FixedCandidateIntervalClosed ∨ CleanMarkedSupportClosed ∨
      DirtyBudgetOneAbs1ReanchorBreaker ∨ TransverseBreakerAdmissibility

/--
Minimum-side normalization of the dirty budget-one reanchor-breaker branch turns it into a one-point
isolator self-loop.
-/
def Q64DirtyBudgetOneReanchorMinimumSide
    (DirtyBudgetOneAbs1ReanchorBreaker MinimumSideNormalization OnePointIsolatorSelfLoop : Prop) :
    Prop :=
  DirtyBudgetOneAbs1ReanchorBreaker → MinimumSideNormalization → OnePointIsolatorSelfLoop

/--
At the one-point isolator self-loop, an aligned defect-switching square is sub-`q` and impossible; any
survivor is axis drift, equivalently the same rank-one package slip / common-frame gluing endpoint.
-/
def Q64OnePointIsolatorSelfLoopNormalForm
    (OnePointIsolatorSelfLoop AlignedDefectSwitchingSquareSubqImpossible
      AxisDriftRankOnePackageSlip : Prop) : Prop :=
  OnePointIsolatorSelfLoop →
    AlignedDefectSwitchingSquareSubqImpossible ∨ AxisDriftRankOnePackageSlip

/--
Edge-table purification for the final two-sheeted hidden-package cover: a nonlocal ambient separator is
either a mixed-edge branch point, a base-boundary cut, or the global sheet character.
-/
def Q64HiddenPackageCoverEdgeTablePurification
    (NonlocalAmbientSeparator MixedEdgeBranchPoint BaseBoundaryCut
      GlobalSheetCharacterSeparator : Prop) : Prop :=
  NonlocalAmbientSeparator →
    MixedEdgeBranchPoint ∨ BaseBoundaryCut ∨ GlobalSheetCharacterSeparator

/--
Modulus split for a promoted sheet side: odd moduli already give a smaller q-marker, while dyadic
moduli leave the half-carrier carry identified in the tail of `proof.md`.
-/
def Q64PromotedSheetSideModulusSplit
    (PromotedSheetSide OddModulus DyadicModulus SmallerQMarker HalfCarrierCarry : Prop) : Prop :=
  PromotedSheetSide → (OddModulus → SmallerQMarker) ∧ (DyadicModulus → HalfCarrierCarry)

/--
The remaining 2-primary sheet-character provenance problem: the global sheet separator must promote to
a first-return boundary side, or its first discontinuity is a branch point (`0001` / square-transverse).
-/
def Q64TwoPrimarySheetCharacterProvenance
    (GlobalSheetCharacterSeparator FirstReturnBoundarySide BranchPoint0001OrSquareTransverse : Prop) :
    Prop :=
  GlobalSheetCharacterSeparator → FirstReturnBoundarySide ∨ BranchPoint0001OrSquareTransverse

/--
Dyadic sheet multiplicity reduction in the final cover: even sheet multiplicity closes, so the only
dyadic survivor is the primitive half-carrier carry.
-/
def Q64DyadicSheetMultiplicityReduction
    (DyadicSheetCase EvenSheetMultiplicityClosed PrimitiveHalfCarrierCarry : Prop) : Prop :=
  DyadicSheetCase → EvenSheetMultiplicityClosed ∨ PrimitiveHalfCarrierCarry

/--
Tree-gauge normalization collapses the distributed hidden-package monodromy of the primitive survivor
to one anchored rank-one slip edge.
-/
def Q64TreeGaugeSingleSlipReduction
    (DistributedMonodromy PrimitiveHalfCarrierCarry AnchoredRankOneSlipEdge : Prop) : Prop :=
  DistributedMonodromy → PrimitiveHalfCarrierCarry → AnchoredRankOneSlipEdge

/--
Single-slip child-realization endpoint: the anchored slip is either an ordered first-return boundary edge
with one `q/2` child carrier, or its first failed star transport is a branch point.
-/
def Q64SingleSlipChildRealization
    (AnchoredRankOneSlipEdge OrderedFirstReturnBoundaryEdge QHalfChildCarrier
      BranchPoint0001OrSquareTransverse : Prop) : Prop :=
  AnchoredRankOneSlipEdge →
    (OrderedFirstReturnBoundaryEdge ∧ QHalfChildCarrier) ∨ BranchPoint0001OrSquareTransverse

/--
Locally star-flat slip-edge provenance: a primitive anchored slip edge whose anchored star faces are all
filled and flat is ordered first-return boundary unless hidden-sheet renaming is a branch square.
-/
def Q64StarFlatSlipEdgeProvenance
    (PrimitiveAnchoredSlipEdge EveryAnchoredStarFaceFilledFlat OrderedFirstReturnBoundaryEdge
      BranchSquare : Prop) : Prop :=
  PrimitiveAnchoredSlipEdge →
    EveryAnchoredStarFaceFilledFlat → OrderedFirstReturnBoundaryEdge ∨ BranchSquare

/--
Peripheral boundary tests add no new endpoint: the first failed commutation from the slip edge to an old
boundary row is a nonfilled/curved face, hence already a local exit or branch square.
-/
def Q64PeripheralBoundaryTestReduction
    (PeripheralBoundaryTest NonfilledOrCurvedFace LocalExit BranchSquare : Prop) : Prop :=
  PeripheralBoundaryTest → NonfilledOrCurvedFace ∧ (LocalExit ∨ BranchSquare)

/--
Star-to-boundary normality is the final local atom from the moving proof tail: a locally star-flat
sheet-character separator commuting with the whole boundary history is ordered first-return admissible,
unless the first static commutation square fails to be a genuine first-return exchange square.
-/
def Q64StarToBoundaryNormality
    (LocallyStarFlatSheetCharacterSeparator BoundaryHistoryCommutation
      OrderedFirstReturnBoundaryEdge StaticNotFirstReturnSquare : Prop) : Prop :=
  LocallyStarFlatSheetCharacterSeparator →
    BoundaryHistoryCommutation → OrderedFirstReturnBoundaryEdge ∨ StaticNotFirstReturnSquare

/-- A static-but-not-first-return commutation square exposes an exchange-gate edge. -/
def Q64StaticNotFirstReturnExchangeGate
    (StaticNotFirstReturnSquare ExchangeGateEdge : Prop) : Prop :=
  StaticNotFirstReturnSquare → ExchangeGateEdge

/--
A prime breaker of the exchange gate either closes in the fixed-trace/clean local catalogue or becomes a
minimal square-transverse breaker.
-/
def Q64ExchangeGatePrimeBreakerReduction
    (ExchangeGateEdge FixedTraceCleanLocal MinimalSquareTransverseBreaker : Prop) : Prop :=
  ExchangeGateEdge → FixedTraceCleanLocal ∨ MinimalSquareTransverseBreaker

/--
Boundary-exchange closure: the first dirty row of the minimal square-transverse breaker gives a proper
child carrier, a primitive circuit, a branch square, or the support-preserving gate-parallel bounce.
-/
def Q64BoundaryExchangeDirtyRowReduction
    (MinimalSquareTransverseBreaker ProperChildCarrier PrimitiveCircuit BranchSquare
      GateParallelSheetCharacterBounce : Prop) : Prop :=
  MinimalSquareTransverseBreaker →
    ProperChildCarrier ∨ PrimitiveCircuit ∨ BranchSquare ∨ GateParallelSheetCharacterBounce

/--
The gate-parallel sheet-character bounce is the same two-chart renaming atom, whose smallest form is an
idempotent one-edge boundary-normality failure.
-/
def Q64GateParallelBounceNormalForm
    (GateParallelSheetCharacterBounce IdempotentOneEdgeBoundaryNormalityFailure : Prop) : Prop :=
  GateParallelSheetCharacterBounce → IdempotentOneEdgeBoundaryNormalityFailure

/--
Named smallest live atom: a global sheet character commutes flatly with all boundary history but is not
admitted as a first-return boundary edge.
-/
def Q64IdempotentBoundaryNormalityFailure
    (GlobalSheetCharacter FlatBoundaryCommutation NotFirstReturnBoundaryEdge : Prop) : Prop :=
  GlobalSheetCharacter ∧ FlatBoundaryCommutation ∧ NotFirstReturnBoundaryEdge

/--
No higher-rank deck group remains: two distinct sheet-character separators either expose a
base-boundary child carrier/gate breaker or collapse to fixed-trace twins, leaving one central deck
involution.
-/
def Q64DeckGroupRankOneReduction
    (TwoDistinctSheetCharacterSeparators BaseBoundaryChildCarrier GateBreaker FixedTraceTwins
      UniqueCentralDeckInvolution : Prop) : Prop :=
  TwoDistinctSheetCharacterSeparators →
    BaseBoundaryChildCarrier ∨ GateBreaker ∨ FixedTraceTwins ∨ UniqueCentralDeckInvolution

/--
Boundary-category fullness for the rank-one deck atom: the unique central involution is already in the
ordered first-return category, or the obstruction is prefix-insertion fullness for the central sheet edge.
-/
def Q64RankOneBoundaryCategoryFullness
    (UniqueCentralDeckInvolution FirstReturnCategoryMembership PrefixInsertionFullness : Prop) :
    Prop :=
  UniqueCentralDeckInvolution → FirstReturnCategoryMembership ∨ PrefixInsertionFullness

/--
Abstract index-two extensions show local category axioms alone are insufficient: all reduced local tests
can hold while the central involution stays outside the first-return category.
-/
def Q64IndexTwoBoundaryCategoryNoGo
    (AllReducedLocalTests CentralInvolutionOutsideFirstReturnCategory : Prop) : Prop :=
  AllReducedLocalTests ∧ CentralInvolutionOutsideFirstReturnCategory

/--
Lowering to modulus `q/2` closes exactly when one sheet is a first-return child carrier; otherwise the
same rank-one atom is prefix-insertion fullness.
-/
def Q64HalfModulusLoweringOrPrefixInsertion
    (PrimitiveDyadicSheetAtom FirstReturnChildCarrier LowerModulusCloses
      PrefixInsertionFullness : Prop) : Prop :=
  PrimitiveDyadicSheetAtom → (FirstReturnChildCarrier ∧ LowerModulusCloses) ∨ PrefixInsertionFullness

/--
Root-edge fullness after prefix commutations erase the history: an ambient separator of the primitive
`q/2` child carrier is a first-return child edge or gives a local/branch exit.
-/
def Q64RootEdgeFullness
    (AmbientSeparatorPrimitiveChildCarrier FirstReturnChildEdge LocalExit BranchExit : Prop) :
    Prop :=
  AmbientSeparatorPrimitiveChildCarrier → FirstReturnChildEdge ∨ LocalExit ∨ BranchExit

/--
Root reseating invariance: the ambient separator can be chosen as the first boundary of an equivalent
terminal descent, unless the reseating exposes the branch square.
-/
def Q64RootReseatingInvariance
    (AmbientSeparatorPrimitiveChildCarrier EquivalentTerminalFirstBoundary BranchSquare : Prop) :
    Prop :=
  AmbientSeparatorPrimitiveChildCarrier → EquivalentTerminalFirstBoundary ∨ BranchSquare

/--
Root selector fullness, the current graph-specific endpoint: realized ambient child-cut rows are
selectable as initial first-return boundaries, barring local or branch exits.
-/
def Q64RootSelectorFullness
    (RealizedAmbientChildCutRow InitialFirstReturnBoundary LocalExit BranchExit : Prop) : Prop :=
  RealizedAmbientChildCutRow → InitialFirstReturnBoundary ∨ LocalExit ∨ BranchExit

/--
Memory-free selector theorem: at the anchored prefix, eligibility is decided by prefix-local tests unless
there is hidden dependence on a vanished first-return word.
-/
def Q64MemoryFreeSelectorTheorem
    (AnchoredPrefixEligibility PrefixLocalAdmitted HiddenSelectorMemory : Prop) : Prop :=
  AnchoredPrefixEligibility → PrefixLocalAdmitted ∨ HiddenSelectorMemory

/--
A globally restart-minimal terminal descent removes hidden selector memory unless the first divergence is
an already classified local/branch exchange failure.
-/
def Q64RestartMinimalityKillsHiddenMemory
    (HiddenSelectorMemory RestartAdmissibility LocalBranchExchangeFailure : Prop) : Prop :=
  HiddenSelectorMemory → RestartAdmissibility ∨ LocalBranchExchangeFailure

/--
Restart admissibility is controlled by the finite terminal-template residue vector: a nonzero vector
closes by its first nonzero coordinate, so a survivor has hidden restart residue.
-/
def Q64RestartResidueVectorDichotomy
    (RestartAdmissibility NonzeroRestartResidueVector ClosedFirstNonzeroCoordinate
      HiddenRestartResidue : Prop) : Prop :=
  RestartAdmissibility →
    (NonzeroRestartResidueVector ∧ ClosedFirstNonzeroCoordinate) ∨ HiddenRestartResidue

/--
Provenance saturation at the anchored prefix: after saturating residue-zero prefix-local rows, a hidden
restart residue is either removed or becomes a residue-zero non-square row.
-/
def Q64AnchoredPrefixProvenanceSaturation
    (HiddenRestartResidue ResidueZeroPrefixLocalSaturation ResidueZeroNonSquareRow : Prop) :
    Prop :=
  HiddenRestartResidue → ResidueZeroPrefixLocalSaturation ∨ ResidueZeroNonSquareRow

/--
`FR^sat` saturation compatibility, the latest final audit endpoint: first-return-complete support in the
residue-saturated exchange complex descends unchanged to the original first-return family.
-/
def Q64FRSatSaturationCompatibility
    (FRSatFirstReturnCompleteSupport OriginalFirstReturnCompleteSupport : Prop) : Prop :=
  FRSatFirstReturnCompleteSupport → OriginalFirstReturnCompleteSupport

/--
Intrinsic exchange-completeness makes the saturation audit pass: the low-set congruence depends only on
the four graph corners and the terminal residue vector.
-/
def Q64IntrinsicExchangeCompletenessAudit
    (FourGraphCorners TerminalResidueVector FRSatFirstReturnCompleteSupport
      OriginalFirstReturnCompleteSupport : Prop) : Prop :=
  FourGraphCorners → TerminalResidueVector →
    FRSatFirstReturnCompleteSupport → OriginalFirstReturnCompleteSupport

/--
Path-saturation equivalence: replacing the historical path convention by the intrinsic
exchange-complete convention does not change terminal-host descent except through a local/branch exit.
-/
def Q64PathSaturationEquivalence
    (HistoricalPathConvention CanonicalSaturatedConvention TerminalHostDescentUnchanged
      LocalBranchExit : Prop) : Prop :=
  HistoricalPathConvention →
    CanonicalSaturatedConvention → TerminalHostDescentUnchanged ∨ LocalBranchExit

/--
Saturated provenance/support-decrease in `FR^sat`: a splitter fails prefix-local tests, has nonzero first
terminal residue, or is a zero-residue `FR^sat` boundary whose first packet-internal failure is a smaller
exchange-complete q-marker.
-/
def Q64SaturatedProvenanceSupportDecrease
    (Splitter PrefixLocalFailure NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary
      ExchangeCompleteSmallerQMarker : Prop) : Prop :=
  Splitter →
    PrefixLocalFailure ∨ NonzeroFirstTerminalResidue ∨
      (ZeroResidueFRSatBoundary ∧ ExchangeCompleteSmallerQMarker)

/--
Concrete row-level skeleton for the canonical saturated first-return exchange complex `FR^sat`.
The fields are intentionally minimal: the graph-specific work is to prove that zero-residue
prefix-local splitter rows are saturated boundaries and carry exchange-complete smaller packet support.
-/
structure Q64FRSatExchangeComplex (Row Packet : Type*) where
  splitter : Row → Prop
  prefixLocal : Row → Prop
  terminalResidue : Row → ℤ
  inFRSat : Row → Prop
  support : Row → Finset Packet
  exchangeComplete : Finset Packet → Prop

/--
Unsaturated row-level exchange data before closing the first-return family under zero-residue,
prefix-local rows.
-/
structure Q64FRSatRawExchangeComplex (Row Packet : Type*) where
  splitter : Row → Prop
  prefixLocal : Row → Prop
  terminalResidue : Row → ℤ
  support : Row → Finset Packet
  exchangeComplete : Finset Packet → Prop

/--
The canonical `FR^sat` enlargement: every zero-residue prefix-local row is admitted as a saturated
first-return boundary.
-/
def Q64FRSatRawExchangeComplex.saturate {Row Packet : Type*}
    (C : Q64FRSatRawExchangeComplex Row Packet) : Q64FRSatExchangeComplex Row Packet where
  splitter := C.splitter
  prefixLocal := C.prefixLocal
  terminalResidue := C.terminalResidue
  inFRSat := fun r => C.prefixLocal r ∧ C.terminalResidue r = 0
  support := C.support
  exchangeComplete := C.exchangeComplete

/--
Support completion for `FR^sat`: the support of every zero-residue prefix-local splitter row is declared
exchange-complete in the completed saturated exchange complex.
-/
def Q64FRSatRawExchangeComplex.completeSupports {Row Packet : Type*}
    (C : Q64FRSatRawExchangeComplex Row Packet) : Q64FRSatRawExchangeComplex Row Packet where
  splitter := C.splitter
  prefixLocal := C.prefixLocal
  terminalResidue := C.terminalResidue
  support := C.support
  exchangeComplete := fun S =>
    ∃ r, C.splitter r ∧ C.prefixLocal r ∧ C.terminalResidue r = 0 ∧ C.support r = S

/-- Zero-residue prefix-local rows are boundaries in the saturated enlargement by construction. -/
theorem q64_inFRSat_saturate_of_prefixLocal_zeroResidue
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) {r : Row}
    (hprefix : C.prefixLocal r) (hzero : C.terminalResidue r = 0) :
    C.saturate.inFRSat r := by
  exact ⟨hprefix, hzero⟩

/--
In the support-completed raw complex, a zero-residue prefix-local splitter row has exchange-complete
support by construction.
-/
theorem q64_exchangeComplete_completeSupports_of_zeroResidue
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) {r : Row}
    (hsplit : C.splitter r) (hprefix : C.prefixLocal r) (hzero : C.terminalResidue r = 0) :
    C.completeSupports.exchangeComplete (C.completeSupports.support r) := by
  exact ⟨r, hsplit, hprefix, hzero, rfl⟩

/-- A saturated row fails the prefix-local eligibility test. -/
def Q64FRSatPrefixLocalFailure {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.splitter r ∧ ¬ C.prefixLocal r

/-- A saturated row passes the prefix-local eligibility test. -/
def Q64FRSatPrefixLocalPass {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.splitter r ∧ C.prefixLocal r

/-- A prefix-local saturated row has nonzero first terminal residue. -/
def Q64FRSatNonzeroFirstTerminalResidue {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.splitter r ∧ C.prefixLocal r ∧ C.terminalResidue r ≠ 0

/-- A prefix-local saturated row has zero terminal residue. -/
def Q64FRSatTerminalResidueZero {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.splitter r ∧ C.prefixLocal r ∧ C.terminalResidue r = 0

/-- A zero-residue prefix-local row is admitted as an `FR^sat` boundary. -/
def Q64FRSatZeroResidueBoundary {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.splitter r ∧ C.prefixLocal r ∧ C.terminalResidue r = 0 ∧ C.inFRSat r

/-- The packet-internal failure support of the row is exchange-complete in `FR^sat`. -/
def Q64FRSatExchangeCompleteSmallerQMarker {Row Packet : Type*}
    (C : Q64FRSatExchangeComplex Row Packet) (r : Row) : Prop :=
  C.exchangeComplete (C.support r)

/--
Granular proof obligations for saturated provenance/support-decrease in the canonical `FR^sat`
convention.  This deliberately separates the real mathematical content from convention bookkeeping:
first classify a splitter by prefix-local tests, then by terminal residue, then prove the zero-residue
case is an `FR^sat` boundary with an exchange-complete smaller packet-internal q-marker.
-/
structure Q64CanonicalSaturatedBranchData
    (Splitter PrefixLocalFailure PrefixLocalPass NonzeroFirstTerminalResidue TerminalResidueZero
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker : Prop) : Prop where
  prefixStep : Splitter → PrefixLocalFailure ∨ PrefixLocalPass
  residueStep : PrefixLocalPass → NonzeroFirstTerminalResidue ∨ TerminalResidueZero
  frsatBoundary : PrefixLocalPass → TerminalResidueZero → ZeroResidueFRSatBoundary
  packetInternalFailure :
    PrefixLocalPass → TerminalResidueZero → ExchangeCompleteSmallerQMarker

/--
The branch-data certificate is exactly the non-bookkeeping content needed for the saturated
provenance/support-decrease theorem.
-/
theorem q64_saturatedProvenanceSupportDecrease_of_canonicalSaturatedBranchData
    {Splitter PrefixLocalFailure PrefixLocalPass NonzeroFirstTerminalResidue TerminalResidueZero
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker : Prop}
    (hdata :
      Q64CanonicalSaturatedBranchData Splitter PrefixLocalFailure PrefixLocalPass
        NonzeroFirstTerminalResidue TerminalResidueZero ZeroResidueFRSatBoundary
        ExchangeCompleteSmallerQMarker) :
    Q64SaturatedProvenanceSupportDecrease Splitter PrefixLocalFailure
      NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker := by
  intro hsplit
  rcases hdata.prefixStep hsplit with hprefix | hpass
  · exact Or.inl hprefix
  rcases hdata.residueStep hpass with hnonzero | hzero
  · exact Or.inr (Or.inl hnonzero)
  · exact Or.inr (Or.inr ⟨hdata.frsatBoundary hpass hzero,
      hdata.packetInternalFailure hpass hzero⟩)

/--
A concrete `FR^sat` row-level complex supplies the abstract branch-data certificate once the two
graph-specific zero-residue facts are proved: boundary admission and exchange-complete smaller support.
-/
theorem q64_canonicalSaturatedBranchData_of_frsatExchangeComplex
    {Row Packet : Type*} (C : Q64FRSatExchangeComplex Row Packet) (r : Row)
    (hboundary :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 → C.inFRSat r)
    (hpacket :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 →
        C.exchangeComplete (C.support r)) :
    Q64CanonicalSaturatedBranchData (C.splitter r) (Q64FRSatPrefixLocalFailure C r)
      (Q64FRSatPrefixLocalPass C r) (Q64FRSatNonzeroFirstTerminalResidue C r)
      (Q64FRSatTerminalResidueZero C r) (Q64FRSatZeroResidueBoundary C r)
      (Q64FRSatExchangeCompleteSmallerQMarker C r) := by
  classical
  refine
    { prefixStep := ?_
      residueStep := ?_
      frsatBoundary := ?_
      packetInternalFailure := ?_ }
  · intro hsplit
    by_cases hprefix : C.prefixLocal r
    · exact Or.inr ⟨hsplit, hprefix⟩
    · exact Or.inl ⟨hsplit, hprefix⟩
  · intro hpass
    by_cases hzero : C.terminalResidue r = 0
    · exact Or.inr ⟨hpass.1, hpass.2, hzero⟩
    · exact Or.inl ⟨hpass.1, hpass.2, hzero⟩
  · intro hpass hzero
    exact ⟨hpass.1, hpass.2, hzero.2.2, hboundary hpass.1 hpass.2 hzero.2.2⟩
  · intro hpass hzero
    exact hpacket hpass.1 hpass.2 hzero.2.2

/--
Concrete `FR^sat` row-level branch classification gives the saturated provenance/support-decrease
theorem for that row.
-/
theorem q64_saturatedProvenanceSupportDecrease_of_frsatExchangeComplex
    {Row Packet : Type*} (C : Q64FRSatExchangeComplex Row Packet) (r : Row)
    (hboundary :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 → C.inFRSat r)
    (hpacket :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 →
        C.exchangeComplete (C.support r)) :
    Q64SaturatedProvenanceSupportDecrease (C.splitter r) (Q64FRSatPrefixLocalFailure C r)
      (Q64FRSatNonzeroFirstTerminalResidue C r) (Q64FRSatZeroResidueBoundary C r)
      (Q64FRSatExchangeCompleteSmallerQMarker C r) :=
  q64_saturatedProvenanceSupportDecrease_of_canonicalSaturatedBranchData
    (q64_canonicalSaturatedBranchData_of_frsatExchangeComplex C r hboundary hpacket)

/--
In the explicit saturated enlargement, the boundary-admission half is definitional.  The remaining
graph-specific input is exactly the packet-internal exchange-completeness of zero-residue splitter rows.
-/
theorem q64_saturatedProvenanceSupportDecrease_of_rawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    (hpacket :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 →
        C.exchangeComplete (C.support r)) :
    Q64SaturatedProvenanceSupportDecrease (C.saturate.splitter r)
      (Q64FRSatPrefixLocalFailure C.saturate r)
      (Q64FRSatNonzeroFirstTerminalResidue C.saturate r)
      (Q64FRSatZeroResidueBoundary C.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.saturate r) := by
  exact
    q64_saturatedProvenanceSupportDecrease_of_frsatExchangeComplex C.saturate r
      (fun _hsplit hprefix hzero =>
        q64_inFRSat_saturate_of_prefixLocal_zeroResidue C hprefix hzero)
      hpacket

/--
The explicit saturated enlargement supplies the granular branch-data certificate once zero-residue
supports are known to be exchange-complete.
-/
theorem q64_canonicalSaturatedBranchData_of_rawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    (hpacket :
      C.splitter r → C.prefixLocal r → C.terminalResidue r = 0 →
        C.exchangeComplete (C.support r)) :
    Q64CanonicalSaturatedBranchData (C.saturate.splitter r)
      (Q64FRSatPrefixLocalFailure C.saturate r) (Q64FRSatPrefixLocalPass C.saturate r)
      (Q64FRSatNonzeroFirstTerminalResidue C.saturate r)
      (Q64FRSatTerminalResidueZero C.saturate r)
      (Q64FRSatZeroResidueBoundary C.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.saturate r) := by
  exact
    q64_canonicalSaturatedBranchData_of_frsatExchangeComplex C.saturate r
      (fun _hsplit hprefix hzero =>
        q64_inFRSat_saturate_of_prefixLocal_zeroResidue C hprefix hzero)
      hpacket

/--
After both zero-residue boundary saturation and support completion, the granular branch-data certificate
is structural.
-/
theorem q64_canonicalSaturatedBranchData_of_completedRawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row) :
    Q64CanonicalSaturatedBranchData (C.completeSupports.saturate.splitter r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r)
      (Q64FRSatPrefixLocalPass C.completeSupports.saturate r)
      (Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (Q64FRSatTerminalResidueZero C.completeSupports.saturate r)
      (Q64FRSatZeroResidueBoundary C.completeSupports.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r) := by
  exact
    q64_canonicalSaturatedBranchData_of_rawFRSatSaturation C.completeSupports r
      (fun hsplit hprefix hzero =>
        q64_exchangeComplete_completeSupports_of_zeroResidue C hsplit hprefix hzero)

/--
After both zero-residue boundary saturation and support completion, the row-level saturated
provenance/support-decrease theorem is purely structural.
-/
theorem q64_saturatedProvenanceSupportDecrease_of_completedRawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row) :
    Q64SaturatedProvenanceSupportDecrease (C.completeSupports.saturate.splitter r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r)
      (Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (Q64FRSatZeroResidueBoundary C.completeSupports.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r) := by
  exact
    q64_saturatedProvenanceSupportDecrease_of_canonicalSaturatedBranchData
      (q64_canonicalSaturatedBranchData_of_completedRawFRSatSaturation C r)

/--
Canonical saturated first-return convention: boundaries are chosen in `FR^sat` after support
minimization and a fixed lexicographic tie-break.
-/
def Q64CanonicalSaturatedFirstReturnConvention
    (BoundariesChosenInFRSat SupportMinimized LexicographicTieBreak : Prop) : Prop :=
  BoundariesChosenInFRSat ∧ SupportMinimized ∧ LexicographicTieBreak

/--
The canonical saturated convention supplies the saturated provenance/support-decrease theorem directly;
older unsaturated paths are handled separately by path-saturation equivalence.
-/
def Q64CanonicalSaturatedProvenanceTheorem
    (CanonicalSaturatedConvention Splitter PrefixLocalFailure NonzeroFirstTerminalResidue
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker : Prop) : Prop :=
  CanonicalSaturatedConvention →
    Q64SaturatedProvenanceSupportDecrease Splitter PrefixLocalFailure NonzeroFirstTerminalResidue
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker

/--
Completed `FR^sat` supplies the canonical saturated provenance theorem structurally: once the raw
first-return complex is saturated and zero-residue supports are completed, the convention hypotheses no
longer add separate graph-theoretic content.
-/
theorem q64_canonicalSaturatedProvenanceTheorem_of_completedRawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    {CanonicalSaturatedConvention : Prop} :
    Q64CanonicalSaturatedProvenanceTheorem CanonicalSaturatedConvention
      (C.completeSupports.saturate.splitter r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r)
      (Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (Q64FRSatZeroResidueBoundary C.completeSupports.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r) := by
  intro _hcanonical
  exact q64_saturatedProvenanceSupportDecrease_of_completedRawFRSatSaturation C r

/--
If an older unsaturated path must be preserved, the remaining obligation is a homotopy/comparison theorem
from that path to the canonical saturated path.
-/
def Q64UnsaturatedToSaturatedPathComparison
    (OlderUnsaturatedPath CanonicalSaturatedPath HomotopyComparison LocalBranchExit : Prop) :
    Prop :=
  OlderUnsaturatedPath → CanonicalSaturatedPath → HomotopyComparison ∨ LocalBranchExit

/--
The path-saturation equivalence used to transport Theorem G back to the historical path convention
is exactly the unsaturated-to-saturated comparison plus the assertion that homotopic comparisons
preserve terminal-host descent.
-/
theorem q64_pathSaturationEquivalence_of_unsaturatedToSaturatedPathComparison
    {HistoricalPathConvention CanonicalSaturatedConvention HomotopyComparison
      TerminalHostDescentUnchanged LocalBranchExit : Prop}
    (hcomparison :
      Q64UnsaturatedToSaturatedPathComparison HistoricalPathConvention
        CanonicalSaturatedConvention HomotopyComparison LocalBranchExit)
    (hhomotopy : HomotopyComparison → TerminalHostDescentUnchanged) :
    Q64PathSaturationEquivalence HistoricalPathConvention CanonicalSaturatedConvention
      TerminalHostDescentUnchanged LocalBranchExit := by
  intro hhistorical hcanonical
  rcases hcomparison hhistorical hcanonical with hhom | hexit
  · exact Or.inl (hhomotopy hhom)
  · exact Or.inr hexit

/-- Finite commutator order yields common-frame gluing only after the anonymous-orbit and promoted
boundary branches are routed. -/
theorem q64_singleTurnCommonFrameGluing_of_finiteCommutatorOrderReduction
    {ConsecutiveDirtyAxes FiniteCommutatorOrder AnonymousCoordinateOrbit PromotedBoundarySplitter
      FirstPackageChangeCompleteSmallerMarker LocalExit : Prop}
    (hfinite :
      Q64FiniteCommutatorOrderReduction FiniteCommutatorOrder AnonymousCoordinateOrbit
        PromotedBoundarySplitter)
    (horder : ConsecutiveDirtyAxes → FiniteCommutatorOrder)
    (horbit : AnonymousCoordinateOrbit → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hpromoted : PromotedBoundarySplitter → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hfinite (horder haxes) with horbit' | hpromoted'
  · exact horbit horbit'
  · exact hpromoted hpromoted'

/-- Dirty chart-change carrier analysis gives single-turn gluing once all three carrier branches route. -/
theorem q64_singleTurnCommonFrameGluing_of_dirtyChartCarrier
    {ConsecutiveDirtyAxes AdjacentTurn OppositeSigns BalancedFlip SameSigns SingletonIsolatorEdge
      DirtyChartChange DirtyChartChangeCarrier ProperCompleteSubcarrier Primitive2x2Circuit
      NonPromotedAmbientSplitAdmissibleModule FirstPackageChangeCompleteSmallerMarker LocalExit :
      Prop}
    (hturn : ConsecutiveDirtyAxes → AdjacentTurn)
    (hnormal :
      Q64AdjacentTurnSignedEdgeNormalForm AdjacentTurn OppositeSigns BalancedFlip SameSigns
        SingletonIsolatorEdge DirtyChartChange)
    (hcarrier : DirtyChartChange → DirtyChartChangeCarrier)
    (htri :
      Q64DirtyChartChangeCarrierTrichotomy DirtyChartChangeCarrier ProperCompleteSubcarrier
        Primitive2x2Circuit NonPromotedAmbientSplitAdmissibleModule)
    (hproper : ProperCompleteSubcarrier → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hprimitive : Primitive2x2Circuit → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hmodule :
      NonPromotedAmbientSplitAdmissibleModule →
        FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hnormal (hturn haxes) with hbalanced | hisolator
  · rcases hbalanced with ⟨_, _, hdirty⟩
    rcases htri (hcarrier hdirty) with hsub | hcircuit | hmodule'
    · exact hproper hsub
    · exact hprimitive hcircuit
    · exact hmodule hmodule'
  · rcases hisolator with ⟨_, _, hdirty⟩
    rcases htri (hcarrier hdirty) with hsub | hcircuit | hmodule'
    · exact hproper hsub
    · exact hprimitive hcircuit
    · exact hmodule hmodule'

/-- The reduced two-chart boundary certificate directly routes the irreducible slip branch. -/
theorem q64_singleTurnCommonFrameGluing_of_twoChartSlipBoundaryCertificate
    {ConsecutiveDirtyAxes DirtyChartChangeEdge CompleteSharedSlackSide SmallerSquareTransverseBreaker
      FirstPackageChangeCompleteSmallerMarker LocalExit : Prop}
    (hdirty : ConsecutiveDirtyAxes → DirtyChartChangeEdge)
    (hcert :
      Q64TwoChartSlipBoundaryCertificate DirtyChartChangeEdge CompleteSharedSlackSide
        SmallerSquareTransverseBreaker)
    (hside : CompleteSharedSlackSide → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hbreaker : SmallerSquareTransverseBreaker → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hcert (hdirty haxes) with hshared | hsmall
  · exact hside hshared
  · exact hbreaker hsmall

/-- The commutator formulation also yields single-turn common-frame gluing once its branches route. -/
theorem q64_singleTurnCommonFrameGluing_of_successorCommutation
    {ConsecutiveDirtyAxes SuccessorPackageIdentificationsCommute NontrivialCommutator
      MixedNonOverlapPair0101_0011 Positive0001PackageLeak FirstPackageChangeCompleteSmallerMarker
      LocalExit : Prop}
    (hcomm :
      Q64CommonFrameSuccessorCommutation ConsecutiveDirtyAxes
        SuccessorPackageIdentificationsCommute NontrivialCommutator)
    (hnormal :
      Q64SuccessorPackageCommutatorNormalForm NontrivialCommutator
        MixedNonOverlapPair0101_0011 Positive0001PackageLeak)
    (hcommute :
      SuccessorPackageIdentificationsCommute → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hmixed :
      MixedNonOverlapPair0101_0011 → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hpositive : Positive0001PackageLeak → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hcomm haxes with hcommutes | hnontrivial
  · exact hcommute hcommutes
  rcases hnormal hnontrivial with hmixedPair | hpositiveLeak
  · exact hmixed hmixedPair
  · exact hpositive hpositiveLeak

/-- Pair-status constancy on the one-corner fiber is another route to single-turn common-frame gluing. -/
theorem q64_singleTurnCommonFrameGluing_of_oneCornerPairStatusConstancy
    {ConsecutiveDirtyAxes OneCornerMedianFiber PairStatusConstant
      SuccessorSide0001SharedSlackMarker FirstPackageChangeCompleteSmallerMarker LocalExit : Prop}
    (hconst :
      Q64OneCornerMedianPairStatusConstancy OneCornerMedianFiber PairStatusConstant
        SuccessorSide0001SharedSlackMarker)
    (hfiber : ConsecutiveDirtyAxes → OneCornerMedianFiber)
    (hconstant : PairStatusConstant → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hmarker :
      SuccessorSide0001SharedSlackMarker → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hconst (hfiber haxes) with hpair | hmarker'
  · exact hconstant hpair
  · exact hmarker hmarker'

/-- The two-fiber overlap lemma is an equivalent route to single-turn common-frame gluing once both
branches are routed to a smaller marker or local exit. -/
theorem q64_singleTurnCommonFrameGluing_of_twoFiberOverlap
    {ConsecutiveDirtyAxes Omega10Nonempty Omega01Nonempty Common0111Witness
      MixedNonOverlapPair0101_0011 FirstPackageChangeCompleteSmallerMarker LocalExit : Prop}
    (hoverlap :
      Q64TwoFiberSingleFlipOverlapLemma Omega10Nonempty Omega01Nonempty Common0111Witness
        MixedNonOverlapPair0101_0011)
    (hfibers : ConsecutiveDirtyAxes → Omega10Nonempty ∧ Omega01Nonempty)
    (hcommon : Common0111Witness → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit)
    (hmixed :
      MixedNonOverlapPair0101_0011 → FirstPackageChangeCompleteSmallerMarker ∨ LocalExit) :
    Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes FirstPackageChangeCompleteSmallerMarker
      LocalExit := by
  intro haxes
  rcases hfibers haxes with ⟨h10, h01⟩
  rcases hoverlap h10 h01 with hwitness | hmixedPair
  · exact hcommon hwitness
  · exact hmixed hmixedPair

/-- A defect-switching square closes once the two first-return promotion branches close and the reduced
trace self-loop model is ruled out in the realized graph. -/
theorem q64_defectSwitchingSquare_closed_of_promotionGap
    {DefectSwitchingFullySkewSquare IsolatedRowPromoted LargerSideCompleteTransportedBag
      ReducedTraceSelfLoopModel FirstReturnSide CompleteSmallerBag LocalExit : Prop}
    (hgap :
      Q64DefectSwitchingSelfLoopPromotionGap DefectSwitchingFullySkewSquare IsolatedRowPromoted
        LargerSideCompleteTransportedBag ReducedTraceSelfLoopModel)
    (hrow : IsolatedRowPromoted → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hside : LargerSideCompleteTransportedBag → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hnoModel : ¬ ReducedTraceSelfLoopModel) :
    DefectSwitchingFullySkewSquare → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit := by
  intro hsquare
  rcases hgap hsquare with hpromote | hbag | hmodel
  · exact hrow hpromote
  · exact hside hbag
  · exact False.elim (hnoModel hmodel)

/-- The sharpened axis-lock endpoint closes the defect-switching square branch. -/
theorem q64_defectSwitchingSquare_closed_of_commonFrameAxisLock
    {DefectSwitchingFullySkewSquare SingletonFirstAxisSeated TransportDriftsToIncomparableFirstAxis
      LocalExit PrimitiveCircuit FirstReturnSide CompleteSmallerBag : Prop}
    (hanalysis :
      Q64DefectSwitchingSquareAxisAnalysis DefectSwitchingFullySkewSquare
        SingletonFirstAxisSeated TransportDriftsToIncomparableFirstAxis)
    (hseated : SingletonFirstAxisSeated → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hlock :
      Q64CommonFrameOrderedAxisLock TransportDriftsToIncomparableFirstAxis LocalExit
        PrimitiveCircuit)
    (hprimitive : PrimitiveCircuit → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit) :
    DefectSwitchingFullySkewSquare → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit := by
  intro hsquare
  rcases hanalysis hsquare with hfirst | hdrift
  · exact hseated hfirst
  rcases hlock hdrift with hlocal | hprimitiveCircuit
  · exact Or.inr (Or.inr hlocal)
  · exact hprimitive hprimitiveCircuit

/--
The equivalent single-turn common-frame gluing endpoint also closes the defect-switching square branch:
the drift branch becomes consecutive dirty axes, whose first package-change edge is a complete smaller
bag or a local exit.
-/
theorem q64_defectSwitchingSquare_closed_of_singleTurnCommonFrameGluing
    {DefectSwitchingFullySkewSquare SingletonFirstAxisSeated TransportDriftsToIncomparableFirstAxis
      ConsecutiveDirtyAxes FirstReturnSide CompleteSmallerBag LocalExit : Prop}
    (hanalysis :
      Q64DefectSwitchingSquareAxisAnalysis DefectSwitchingFullySkewSquare
        SingletonFirstAxisSeated TransportDriftsToIncomparableFirstAxis)
    (hseated : SingletonFirstAxisSeated → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hdirty : TransportDriftsToIncomparableFirstAxis → ConsecutiveDirtyAxes)
    (hglue : Q64SingleTurnCommonFrameGluing ConsecutiveDirtyAxes CompleteSmallerBag LocalExit) :
    DefectSwitchingFullySkewSquare → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit := by
  intro hsquare
  rcases hanalysis hsquare with hfirst | hdrift
  · exact hseated hfirst
  rcases hglue (hdirty hdrift) with hsmall | hlocal
  · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr hlocal)

/--
Higher-rank package-coordinate monodromy is not a separate endpoint after quotienting fixed-trace,
unary, and false-clone kernels: its first moved coordinate is rank-one `0001`, or the reverse
orientation is represented by the `0111` compensator with unary leaks.
-/
def Q64HigherRankMonodromyReduction
    (HigherRankMonodromy RankOneSuccessor0001 Reverse0111WithUnaryLeaks : Prop) : Prop :=
  HigherRankMonodromy → RankOneSuccessor0001 ∨ Reverse0111WithUnaryLeaks

/-- If both rank-one exits are impossible, no higher-rank monodromy survivor remains. -/
theorem q64_no_higherRankMonodromy_of_reduction
    {HigherRankMonodromy RankOneSuccessor0001 Reverse0111WithUnaryLeaks : Prop}
    (hred :
      Q64HigherRankMonodromyReduction HigherRankMonodromy RankOneSuccessor0001
        Reverse0111WithUnaryLeaks)
    (hno0001 : ¬ RankOneSuccessor0001)
    (hnoReverse : ¬ Reverse0111WithUnaryLeaks) :
    ¬ HigherRankMonodromy := by
  intro hmono
  rcases hred hmono with h0001 | hreverse
  · exact hno0001 h0001
  · exact hnoReverse hreverse

/--
Directional sign coherence on a thickened bad hidden edge: a lower edge of type `10` cannot reverse
to `01` on the opposite side, and symmetrically after swapping the square directions.
-/
def Q64DirectionalSignCoherence (p : Bool → Bool → Prop) : Prop :=
  (p false false → ¬ p true false → p true true → p false true) ∧
    (p false false → ¬ p false true → p true true → p true false)

/--
First-return predecessor lemma: in the designated terminal square of a closest-return strip, the
near-side predecessor corner is back in the witness set.
-/
def Q64FirstReturnPredecessorLemma
    (CleanCorridor TerminalSquare NearSidePredecessorInWitness : Prop) : Prop :=
  CleanCorridor → TerminalSquare → NearSidePredecessorInWitness

/--
Successor-side first-switch normal form: after all shorter returns and predecessor-side suffixes are
removed, any hidden-edge counterexample exposes the successor-side `0001` square.
-/
def Q64SuccessorSideFirstSwitch0001Reduction
    (BadHiddenEdge SmallerBadEdge PredecessorSideDischarged SuccessorSide0001 : Prop) : Prop :=
  BadHiddenEdge → SmallerBadEdge ∨ PredecessorSideDischarged ∨ SuccessorSide0001

/-- The first-switch reduction excludes bad hidden edges when every resulting branch is impossible. -/
theorem q64_no_badHiddenEdge_of_firstSwitchReduction
    {BadHiddenEdge SmallerBadEdge PredecessorSideDischarged SuccessorSide0001 : Prop}
    (hred :
      Q64SuccessorSideFirstSwitch0001Reduction BadHiddenEdge SmallerBadEdge
        PredecessorSideDischarged SuccessorSide0001)
    (hnoSmall : ¬ SmallerBadEdge) (hnoPred : ¬ PredecessorSideDischarged)
    (hno0001 : ¬ SuccessorSide0001) :
    ¬ BadHiddenEdge := by
  intro hbad
  rcases hred hbad with hsmall | hpred | h0001
  · exact hnoSmall hsmall
  · exact hnoPred hpred
  · exact hno0001 h0001

/--
The explicit local common core after the first-switch reduction: fiber-constant pair status, defect
fiber identification, per-fiber persistence, and pair-chamber separation produce the degree-congruent
transversal.
-/
def Q64OneCornerLocalCommonCore
    (FiberConstantPairStatus DefectFiberIdentification PerFiberPersistence PairChamberSeparation
      DegreeCongruentTransversal : Prop) : Prop :=
  FiberConstantPairStatus →
    DefectFiberIdentification →
      PerFiberPersistence → PairChamberSeparation → DegreeCongruentTransversal

/--
One-corner package bridge: once ambient membership is lifted to the fixed shared slice and prescribed
entry holds, the local common core supplies the compatible degree-congruent transversal.
-/
def Q64OneCornerSharedSliceToTransversal
    (AmbientBinaryCylinder FixedFrameShadow SharedSliceEntry AdmissibleCylinderEntry
      LocalCommonCore CompatibleTransversal : Prop) : Prop :=
  Q64AmbientToFixedSharedSliceLift AmbientBinaryCylinder FixedFrameShadow SharedSliceEntry →
    Q64PrescribedSharedSliceEntry FixedFrameShadow SharedSliceEntry AdmissibleCylinderEntry →
      LocalCommonCore → AmbientBinaryCylinder → CompatibleTransversal

/--
Outgoing anti-Horn/no-split is formal once persistence, silent-edge exclusion, and componentwise
no-split are available.
-/
def Q64OutgoingAntiHornFormal
    (AnchoredPersistence SilentEdgeExclusion ComponentwiseNoSplit OutgoingAntiHorn : Prop) : Prop :=
  AnchoredPersistence → SilentEdgeExclusion → ComponentwiseNoSplit → OutgoingAntiHorn

/--
Failures of the outgoing no-split formulation reduce to repair-fiber cubicality or to the same
square-breaker routing package.
-/
def Q64OutgoingNoSplitFailureReduction
    (OutgoingNoSplitFailure RepairFiberCubicality SquareBreakerRouting : Prop) : Prop :=
  OutgoingNoSplitFailure → RepairFiberCubicality ∨ SquareBreakerRouting

/-- The formal outgoing anti-Horn surface projects the anti-Horn conclusion. -/
theorem q64_outgoingAntiHorn_of_formal
    {AnchoredPersistence SilentEdgeExclusion ComponentwiseNoSplit OutgoingAntiHorn : Prop}
    (h :
      Q64OutgoingAntiHornFormal AnchoredPersistence SilentEdgeExclusion ComponentwiseNoSplit
        OutgoingAntiHorn)
    (hpersist : AnchoredPersistence) (hsilent : SilentEdgeExclusion)
    (hnosplit : ComponentwiseNoSplit) :
    OutgoingAntiHorn :=
  h hpersist hsilent hnosplit

end OneCornerMedianFiber

section CommonEdgeRigidity

variable {State Chamber Packet : Type*}

/--
Common-edge pair-chamber cylinder rigidity: an elementary hidden step that preserves both side
chamber coordinates also preserves the repaired packet-state.
-/
def Q64CommonEdgePairChamberRigidity
    (Step : State → State → Prop) (chiMinus chiPlus : State → Chamber)
    (packet : State → Packet) : Prop :=
  ∀ ⦃s t : State⦄,
    Step s t → chiMinus s = chiMinus t → chiPlus s = chiPlus t → packet s = packet t

/-- The same statement in the silent-component language used by the notes. -/
def Q64TwoSidedSilentComponentInjectivity
    (Step : State → State → Prop) (sigmaMinus sigmaPlus : State → Chamber)
    (packet : State → Packet) : Prop :=
  ∀ ⦃s t : State⦄,
    Step s t → sigmaMinus s = sigmaMinus t → sigmaPlus s = sigmaPlus t → packet s = packet t

theorem q64_pairChamberRigidity_iff_silentComponentInjectivity
    {Step : State → State → Prop} {chiMinus chiPlus : State → Chamber}
    {packet : State → Packet} :
    Q64CommonEdgePairChamberRigidity Step chiMinus chiPlus packet ↔
      Q64TwoSidedSilentComponentInjectivity Step chiMinus chiPlus packet :=
  Iff.rfl

/--
Ordered-edge sign obstruction: if every oriented step inside one pair-chamber cylinder has a sign
depending only on that cylinder, while reversing the step negates the sign, then no same-cylinder
nontrivial step can exist.
-/
theorem q64_no_sameCylinder_step_of_orderedSign
    {Step : State → State → Prop} {pairChamber : State → Chamber}
    {sign : State → State → ℤ} {omega : Chamber → ℤ}
    (hsym : ∀ ⦃x y⦄, Step x y → Step y x)
    (hconst :
      ∀ ⦃x y⦄, Step x y → pairChamber x = pairChamber y →
        sign x y = omega (pairChamber x))
    (hanti : ∀ ⦃x y⦄, Step x y → sign y x = -sign x y)
    (hnonzero : ∀ C, omega C ≠ 0) :
    ∀ ⦃x y⦄, Step x y → pairChamber x = pairChamber y → False := by
  intro x y hstep hcyl
  have hrev : Step y x := hsym hstep
  have hxy : sign x y = omega (pairChamber x) := hconst hstep hcyl
  have hyx : sign y x = omega (pairChamber y) := hconst hrev hcyl.symm
  have hneg : sign y x = -sign x y := hanti hstep
  rw [hxy, hyx, ← hcyl] at hneg
  have hzero : omega (pairChamber x) = 0 := by omega
  exact hnonzero (pairChamber x) hzero

/--
Endpoint/chamber-only data are constant on a fixed pair-chamber cylinder.  This is the formal
content behind the note that chamberwise endpoint labels alone cannot orient a chamber-flat hidden
step.
-/
theorem q64_pairChamberFactoredStatistic_constant_on_cylinder
    {Value : Type*} {pairChamber : State → Chamber} {statistic : State → Value}
    {readout : Chamber → Value}
    (hfactor : ∀ x, statistic x = readout (pairChamber x)) :
    ∀ ⦃x y⦄, pairChamber x = pairChamber y → statistic x = statistic y := by
  intro x y hcyl
  rw [hfactor x, hfactor y, hcyl]

/--
An additive potential built from the two one-side chamber coordinates is also constant on each
pair-chamber cylinder.
-/
theorem q64_endpointChamberPotential_constant_on_pairCylinder
    {Value : Type*} [Add Value] {sigmaMinus sigmaPlus : State → Chamber}
    {potential : State → Value} {fMinus fPlus : Chamber → Value}
    (hpotential : ∀ x, potential x = fMinus (sigmaMinus x) + fPlus (sigmaPlus x)) :
    ∀ ⦃x y⦄,
      sigmaMinus x = sigmaMinus y → sigmaPlus x = sigmaPlus y → potential x = potential y := by
  intro x y hminus hplus
  rw [hpotential x, hpotential y, hminus, hplus]

/--
Latest pair-chamber blocker alternative: a chamber-flat hidden step either admits such a
cylinder-constant ordered sign, or it localizes to binary trace coalescence.
-/
def Q64PairChamberOrderedSignOrTraceCoalescence
    (ChamberFlatHiddenStep CylinderConstantOrderedSign BinaryTraceCoalescence : Prop) : Prop :=
  ChamberFlatHiddenStep → CylinderConstantOrderedSign ∨ BinaryTraceCoalescence

/--
Filled-overlap pair-injectivity, pair-chamber hidden-choice separation, and two-fiber overlap all
reduce to either a fixed-trace local exit or a square-transverse breaker.
-/
def Q64FilledOverlapPairInjectivityReduction
    (FilledOverlapFailure FixedTraceLocalExit SquareTransverseBreaker : Prop) : Prop :=
  FilledOverlapFailure → FixedTraceLocalExit ∨ SquareTransverseBreaker

/--
Binary skew-ladder endpoint: after common discrepancy packaging is missing, every dirty-row turn is
either a balanced flip, a same-side twin turn needing an outside boundary distinguisher, or the
successor-side `0001` square.
-/
def Q64BinarySkewLadderTurnDichotomy
    (DirtyRowTurn BalancedFlip SameSideTwinTurn BoundaryDistinguisher SuccessorSide0001 : Prop) :
    Prop :=
  DirtyRowTurn → BalancedFlip ∨ (SameSideTwinTurn ∧ BoundaryDistinguisher) ∨ SuccessorSide0001

/--
Fixed-square opposite-defect uniqueness is not a raw short-packet consequence; it reduces to a
same-trace/false-clone exit or to the square-transverse breaker theorem.
-/
def Q64FixedSquareOppositeDefectUniquenessReduction
    (TwoCompleters SameTraceOrFalseCloneExit SquareTransverseBreaker : Prop) : Prop :=
  TwoCompleters → SameTraceOrFalseCloneExit ∨ SquareTransverseBreaker

/--
Failed-row acyclicity closes only when the first dirty failed row strictly decreases the active side;
the nondecreasing survivor is exactly the skew binary ladder.
-/
def Q64FailedRowAcyclicityEndpointReduction
    (DirtyFailedRowCycle StrictActiveSideDecrease SkewBinaryLadder : Prop) : Prop :=
  DirtyFailedRowCycle → StrictActiveSideDecrease ∨ SkewBinaryLadder

end CommonEdgeRigidity

section IncidentSquareSilentGraph

variable {Defect Chamber : Type*}

/-- Silent-edge exclusion: every silent elementary hidden step is a loop. -/
def Q64SilentStepRigidity (SilentStep : Defect → Defect → Prop) : Prop :=
  ∀ ⦃x y : Defect⦄, SilentStep x y → x = y

/-- Silent-path singleton property: every silent path stays at its starting defect. -/
def Q64SilentPathRigidity (SilentStep : Defect → Defect → Prop) : Prop :=
  ∀ ⦃x y : Defect⦄, Relation.ReflTransGen SilentStep x y → x = y

theorem q64_silentStepRigidity_iff_silentPathRigidity
    {SilentStep : Defect → Defect → Prop} :
    Q64SilentStepRigidity SilentStep ↔ Q64SilentPathRigidity SilentStep := by
  constructor
  · intro hstep x y hpath
    induction hpath with
    | refl => rfl
    | tail _hxy hyz ih =>
        exact ih.trans (hstep hyz)
  · intro hpath x y hxy
    exact hpath (Relation.ReflTransGen.single hxy)

/--
Same-chamber silent-step defect rigidity: a silent elementary step inside one unary chamber cannot
change the repaired opposite defect.
-/
def Q64SameChamberSilentStepDefectRigidity
    (Step : Defect → Defect → Prop) (chamber : Defect → Chamber) : Prop :=
  ∀ ⦃x y : Defect⦄, Step x y → chamber x = chamber y → x = y

/--
One-step wall detection: any elementary step that changes the repaired opposite defect must cross a
unary chamber wall.
-/
def Q64OppositeDefectWallDetection
    (Step : Defect → Defect → Prop) (chamber : Defect → Chamber) : Prop :=
  ∀ ⦃x y : Defect⦄, Step x y → x ≠ y → chamber x ≠ chamber y

theorem q64_sameChamberRigidity_iff_wallDetection
    {Step : Defect → Defect → Prop} {chamber : Defect → Chamber} :
    Q64SameChamberSilentStepDefectRigidity Step chamber ↔
      Q64OppositeDefectWallDetection Step chamber := by
  constructor
  · intro hrigid x y hstep hxy hchamber
    exact hxy (hrigid hstep hchamber)
  · intro hwall x y hstep hchamber
    by_contra hxy
    exact hwall hstep hxy hchamber

end IncidentSquareSilentGraph

section InitialPacketBasin

variable {State Packet : Type*}

/--
The initial-packet basin of a base state: states reachable by a silent path along which every new
state still has the base packet.
-/
def q64InitialPacketBasin
    (base : State) (Step : State → State → Prop) (packet : State → Packet) : Set State :=
  {y | Relation.ReflTransGen (fun a b => Step a b ∧ packet b = packet base) base y}

theorem q64_initialPacketBasin_step_mem
    {base a b : State} {Step : State → State → Prop} {packet : State → Packet}
    (ha : a ∈ q64InitialPacketBasin base Step packet)
    (hstep : Step a b) (hpacket : packet b = packet base) :
    b ∈ q64InitialPacketBasin base Step packet := by
  exact Relation.ReflTransGen.tail ha ⟨hstep, hpacket⟩

/--
Boundary first-packet-change principle: if a one-step continuation leaves the initial-packet basin,
then that boundary step changes the packet.
-/
theorem q64_boundary_step_packet_changes
    {base a b : State} {Step : State → State → Prop} {packet : State → Packet}
    (ha : a ∈ q64InitialPacketBasin base Step packet)
    (hstep : Step a b) (hb : b ∉ q64InitialPacketBasin base Step packet) :
    packet b ≠ packet base := by
  intro hpacket
  exact hb (q64_initialPacketBasin_step_mem ha hstep hpacket)

end InitialPacketBasin

section OverlapStringCoboundary

/--
Edge drift on a finite overlap string is a coboundary when it is the consecutive difference of an
edge potential.
-/
def Q64OverlapStringCoboundary (drift potential : ℕ → ℤ) (length : ℕ) : Prop :=
  ∀ i, i < length → drift i = potential (i + 1) - potential i

theorem q64_sum_range_potential_diff (potential : ℕ → ℤ) :
    ∀ length : ℕ,
      (Finset.range length).sum (fun i => potential (i + 1) - potential i) =
        potential length - potential 0
  | 0 => by simp
  | length + 1 => by
      rw [Finset.sum_range_succ, q64_sum_range_potential_diff potential length]
      ring

/-- Telescoping for the witness-switch coboundary along a maximal overlap string. -/
theorem q64_sum_drift_of_overlapStringCoboundary
    {drift potential : ℕ → ℤ} {length : ℕ}
    (h : Q64OverlapStringCoboundary drift potential length) :
    (Finset.range length).sum drift = potential length - potential 0 := by
  calc
    (Finset.range length).sum drift =
        (Finset.range length).sum (fun i => potential (i + 1) - potential i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact h i (Finset.mem_range.mp hi)
    _ = potential length - potential 0 :=
      q64_sum_range_potential_diff potential length

/-- A closed potential string has zero total orthogonal drift. -/
theorem q64_zero_drift_of_overlapStringCoboundary_cycle
    {drift potential : ℕ → ℤ} {length : ℕ}
    (h : Q64OverlapStringCoboundary drift potential length)
    (hcycle : potential length = potential 0) :
    (Finset.range length).sum drift = 0 := by
  rw [q64_sum_drift_of_overlapStringCoboundary h, hcycle]
  ring

end OverlapStringCoboundary

section AdditiveInterval

variable {K : Type*}

lemma q64_sum_zero_one_eq_filter_card (S : Finset K) (coeff : K → ℕ)
    (hbit : ∀ k ∈ S, coeff k = 0 ∨ coeff k = 1) :
    S.sum coeff = (S.filter fun k => coeff k = 1).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rcases hbit k hk with h0 | h1
  · simp [h0]
  · simp [h1]

lemma q64_card_filter_one_le_one [DecidableEq K] (S : Finset K) (coeff : K → ℕ)
    (hpair : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → coeff k + coeff l ≤ 1) :
    (S.filter fun k => coeff k = 1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k hk l hl
  rcases Finset.mem_filter.mp hk with ⟨hkS, hk1⟩
  rcases Finset.mem_filter.mp hl with ⟨hlS, hl1⟩
  by_contra hne
  have hle := hpair k hkS l hlS hne
  omega

lemma q64_sum_zero_one_le_one [DecidableEq K] (S : Finset K) (coeff : K → ℕ)
    (hbit : ∀ k ∈ S, coeff k = 0 ∨ coeff k = 1)
    (hpair : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → coeff k + coeff l ≤ 1) :
    S.sum coeff ≤ 1 := by
  rw [q64_sum_zero_one_eq_filter_card S coeff hbit]
  exact q64_card_filter_one_le_one S coeff hpair

/--
The candidate-fixed additive interval lemma for the interval `{0,1}`: if every singleton coefficient
and every two-term partial sum stays in `{0,1}`, then the whole finite partial sum stays in `{0,1}`.
-/
theorem q64_int_sum_zero_one_interval [DecidableEq K] (S : Finset K) (coeff : K → ℤ)
    (hbit : ∀ k ∈ S, coeff k = 0 ∨ coeff k = 1)
    (hpair :
      ∀ k ∈ S, ∀ l ∈ S, k ≠ l → coeff k + coeff l = 0 ∨ coeff k + coeff l = 1) :
    S.sum coeff = 0 ∨ S.sum coeff = 1 := by
  let coeffNat : K → ℕ := fun k => if coeff k = 1 then 1 else 0
  let coeffInt : K → ℤ := fun k => (coeffNat k : ℤ)
  have hcoeffNat_bit : ∀ k ∈ S, coeffNat k = 0 ∨ coeffNat k = 1 := by
    intro k _hk
    unfold coeffNat
    by_cases h : coeff k = 1 <;> simp [h]
  have hcoeffNat_pair :
      ∀ k ∈ S, ∀ l ∈ S, k ≠ l → coeffNat k + coeffNat l ≤ 1 := by
    intro k hk l hl hne
    unfold coeffNat
    by_cases hk1 : coeff k = 1
    · by_cases hl1 : coeff l = 1
      · have hp := hpair k hk l hl hne
        rw [hk1, hl1] at hp
        omega
      · simp [hk1, hl1]
    · by_cases hl1 : coeff l = 1 <;> simp [hk1, hl1]
  have hsumNat : S.sum coeffNat ≤ 1 :=
    q64_sum_zero_one_le_one S coeffNat hcoeffNat_bit hcoeffNat_pair
  have hsum_eq : S.sum coeff = S.sum coeffInt := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold coeffInt coeffNat
    rcases hbit k hk with h0 | h1
    · simp [h0]
    · simp [h1]
  have hcast : S.sum coeffInt = ((S.sum coeffNat : ℕ) : ℤ) := by
    simp [coeffInt]
  have hsumNat_cases : S.sum coeffNat = 0 ∨ S.sum coeffNat = 1 := by
    omega
  rcases hsumNat_cases with h0 | h1
  · left
    rw [hsum_eq, hcast, h0]
    norm_num
  · right
    rw [hsum_eq, hcast, h1]
    norm_num

/--
The sign-reversed candidate-fixed additive interval lemma for `{-1,0}`.
-/
theorem q64_int_sum_negone_zero_interval [DecidableEq K] (S : Finset K) (coeff : K → ℤ)
    (hbit : ∀ k ∈ S, coeff k = -1 ∨ coeff k = 0)
    (hpair :
      ∀ k ∈ S, ∀ l ∈ S, k ≠ l → coeff k + coeff l = -1 ∨ coeff k + coeff l = 0) :
    S.sum coeff = -1 ∨ S.sum coeff = 0 := by
  have hpos := q64_int_sum_zero_one_interval S (fun k => -coeff k)
    (by
      intro k hk
      rcases hbit k hk with hneg | h0
      · right
        change -coeff k = 1
        rw [hneg]
        norm_num
      · left
        change -coeff k = 0
        rw [h0]
        norm_num)
    (by
      intro k hk l hl hne
      have hp := hpair k hk l hl hne
      have hneg : -coeff k + -coeff l = -(coeff k + coeff l) := by ring
      rw [hneg]
      rcases hp with hp | hp
      · right
        rw [hp]
        norm_num
      · left
        rw [hp]
        norm_num)
  have hneg_sum : S.sum (fun k => -coeff k) = -S.sum coeff := by
    simp
  rcases hpos with h0 | h1
  · right
    rw [hneg_sum] at h0
    linarith
  · left
    rw [hneg_sum] at h1
    linarith

/-- The degenerate interval `{0}` case of the candidate-fixed additive interval lemma. -/
theorem q64_int_sum_zero_interval (S : Finset K) (coeff : K → ℤ)
    (hzero : ∀ k ∈ S, coeff k = 0) :
    S.sum coeff = 0 := by
  exact Finset.sum_eq_zero hzero

end AdditiveInterval

section UpperFaceHelly

variable {X : Type*}

/--
Median-convexity in the abstract chamber graph form used by the upper-face Helly reduction:
if any two of the three inputs lie in the set, then their median lies in the set.
-/
def Q64MedianConvex (med : X → X → X → X) (A : Set X) : Prop :=
  ∀ ⦃x y z : X⦄,
    ((x ∈ A ∧ y ∈ A) ∨ (x ∈ A ∧ z ∈ A) ∨ (y ∈ A ∧ z ∈ A)) →
      med x y z ∈ A

/--
The formal Helly step for three upper-face witness packets: pairwise intersections plus
median-convexity produce a common witness.
-/
theorem q64_three_medianConvex_sets_helly
    {med : X → X → X → X} {A B C : Set X}
    (hA : Q64MedianConvex med A) (hB : Q64MedianConvex med B)
    (hC : Q64MedianConvex med C)
    (hBC : (B ∩ C).Nonempty) (hCA : (C ∩ A).Nonempty) (hAB : (A ∩ B).Nonempty) :
    (A ∩ B ∩ C).Nonempty := by
  rcases hBC with ⟨a, haB, haC⟩
  rcases hCA with ⟨b, hbC, hbA⟩
  rcases hAB with ⟨c, hcA, hcB⟩
  refine ⟨med a b c, ?_⟩
  exact ⟨⟨hA (Or.inr (Or.inr ⟨hbA, hcA⟩)),
    hB (Or.inr (Or.inl ⟨haB, hcB⟩))⟩,
    hC (Or.inl ⟨haC, hbC⟩)⟩

/-- First packet in the abstract candidate-switching Helly no-go. -/
def q64CandidateSwitchingNoGoA : Set (Fin 3) := fun x => x = 0 ∨ x = 1

/-- Second packet in the abstract candidate-switching Helly no-go. -/
def q64CandidateSwitchingNoGoB : Set (Fin 3) := fun x => x = 1 ∨ x = 2

/-- Third packet in the abstract candidate-switching Helly no-go. -/
def q64CandidateSwitchingNoGoC : Set (Fin 3) := fun x => x = 2 ∨ x = 0

/--
Pairwise packet overlaps do not imply a common witness without the graph-specific gatedness input.
-/
theorem q64_candidateSwitching_pairwise_not_triple_helly :
    (q64CandidateSwitchingNoGoA ∩ q64CandidateSwitchingNoGoB).Nonempty ∧
      (q64CandidateSwitchingNoGoB ∩ q64CandidateSwitchingNoGoC).Nonempty ∧
        (q64CandidateSwitchingNoGoC ∩ q64CandidateSwitchingNoGoA).Nonempty ∧
          ¬ (q64CandidateSwitchingNoGoA ∩ q64CandidateSwitchingNoGoB ∩
            q64CandidateSwitchingNoGoC).Nonempty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨(1 : Fin 3), ?_⟩
    constructor
    · unfold q64CandidateSwitchingNoGoA
      right
      rfl
    · unfold q64CandidateSwitchingNoGoB
      left
      rfl
  · refine ⟨(2 : Fin 3), ?_⟩
    constructor
    · unfold q64CandidateSwitchingNoGoB
      right
      rfl
    · unfold q64CandidateSwitchingNoGoC
      left
      rfl
  · refine ⟨(0 : Fin 3), ?_⟩
    constructor
    · unfold q64CandidateSwitchingNoGoC
      right
      rfl
    · unfold q64CandidateSwitchingNoGoA
      left
      rfl
  · rintro ⟨x, hx⟩
    rcases hx with ⟨⟨hA, hB⟩, hC⟩
    unfold q64CandidateSwitchingNoGoA at hA
    unfold q64CandidateSwitchingNoGoB at hB
    unfold q64CandidateSwitchingNoGoC at hC
    rcases hA with rfl | rfl
    · change (0 : Fin 3) = 1 ∨ (0 : Fin 3) = 2 at hB
      rcases hB with h | h
      · exact (by decide : (0 : Fin 3) ≠ 1) h
      · exact (by decide : (0 : Fin 3) ≠ 2) h
    · change (1 : Fin 3) = 2 ∨ (1 : Fin 3) = 0 at hC
      rcases hC with h | h
      · exact (by decide : (1 : Fin 3) ≠ 2) h
      · exact (by decide : (1 : Fin 3) ≠ 0) h

/--
Graph-specific candidate-switching gatedness: pairwise face overlaps must either produce a common
witness, give a transverse gate, or expose the shared-slack marker.
-/
def Q64CandidateSwitchingGatedness
    (PairwiseFaceOverlap CommonWitness TransverseGate SharedSlackMarker : Prop) : Prop :=
  PairwiseFaceOverlap → CommonWitness ∨ TransverseGate ∨ SharedSlackMarker

/--
If no transverse gate or marker remains, candidate-switching gatedness gives a common witness.
-/
theorem q64_commonWitness_of_candidateSwitchingGatedness
    {PairwiseFaceOverlap CommonWitness TransverseGate SharedSlackMarker : Prop}
    (hgated :
      Q64CandidateSwitchingGatedness PairwiseFaceOverlap CommonWitness TransverseGate
        SharedSlackMarker)
    (hnoGate : ¬ TransverseGate) (hnoMarker : ¬ SharedSlackMarker)
    (hoverlap : PairwiseFaceOverlap) :
    CommonWitness := by
  rcases hgated hoverlap with hcommon | hgate | hmarker
  · exact hcommon
  · exact False.elim (hnoGate hgate)
  · exact False.elim (hnoMarker hmarker)

end UpperFaceHelly

section LateHostReductions

variable {State Defect Index Chamber Component : Type*}

/-- A statistic preserved on silent elementary steps is constant along silent paths. -/
theorem q64_statistic_constant_on_silentPath
    {SilentStep : State → State → Prop} {stat : State → Defect}
    (hstep : ∀ ⦃x y : State⦄, SilentStep x y → stat x = stat y) :
    ∀ ⦃x y : State⦄, Relation.ReflTransGen SilentStep x y → stat x = stat y := by
  intro x y hpath
  induction hpath with
  | refl => rfl
  | tail _hxy hyz ih =>
      exact ih.trans (hstep hyz)

/--
Abstract form of `host-silentedge128`: if every nontrivial silent edge has a differing coordinate
but the anchored one-corner lift plus fixed-square rigidity forces that coordinate to agree, then
the silent graph is edgeless.
-/
theorem q64_silentedge128_no_nontrivial_step
    {SilentStep : State → State → Prop} {coord : State → Index → Defect}
    (hfirst :
      ∀ ⦃x y : State⦄, SilentStep x y → x ≠ y → ∃ j, coord x j ≠ coord y j)
    (hlift :
      ∀ ⦃x y : State⦄ (j : Index), SilentStep x y → coord x j ≠ coord y j →
        coord y j = coord x j) :
    Q64SilentStepRigidity SilentStep := by
  intro x y hstep
  by_contra hxy
  rcases hfirst hstep hxy with ⟨j, hj⟩
  exact hj (hlift j hstep hj).symm

/--
Abstract form of `host-opppair123`: anchored witness persistence puts all realized outgoing defects
in one silent component; componentwise singleton then forces the realized set to have size at most
one.
-/
theorem q64_realized_outgoing_singleton_of_componentwise
    [DecidableEq Defect] [DecidableEq Component]
    (R : Finset Defect) (component : Defect → Component)
    (honeComponent : ∃ C, ∀ ρ ∈ R, component ρ = C)
    (hcomponentSingleton : ∀ C, (R.filter fun ρ => component ρ = C).card ≤ 1) :
    R.card ≤ 1 := by
  rcases honeComponent with ⟨C, hC⟩
  have hfilter : R.filter (fun ρ => component ρ = C) = R := by
    apply Finset.ext
    intro ρ
    constructor
    · intro hρ
      exact (Finset.mem_filter.mp hρ).1
    · intro hρ
      exact Finset.mem_filter.mpr ⟨hρ, hC ρ hρ⟩
  rw [← hfilter]
  exact hcomponentSingleton C

/--
Pair-chamber separation of the hidden choice: no nontrivial elementary hidden step stays inside one
pair-chamber cylinder.
-/
def Q64PairChamberSeparatesHiddenChoice
    (Step : State → State → Prop) (sigmaMinus sigmaPlus : State → Chamber) : Prop :=
  ∀ ⦃x y : State⦄,
    Step x y → sigmaMinus x = sigmaMinus y → sigmaPlus x = sigmaPlus y → x = y

/--
Abstract form of `host-orient115`: if every hypothetical non-overlap table produces a nontrivial
pair-chamber-silent hidden step, pair-chamber separation forces the two-fiber overlap conclusion.
-/
theorem q64_twoFiberOverlap_of_pairChamberSeparation
    {K : Type*} [Fintype K] [DecidableEq K]
    {d10 d01 : K → ℕ} {Step : State → State → Prop}
    {sigmaMinus sigmaPlus : State → Chamber}
    (hsep : Q64PairChamberSeparatesHiddenChoice Step sigmaMinus sigmaPlus)
    (hnonOverlapProducesStep :
      (q64Omega10 d10).Nonempty → (q64Omega01 d01).Nonempty →
        q64Omega10 d10 ∩ q64Omega01 d01 = ∅ →
          ∃ x y, Step x y ∧ x ≠ y ∧ sigmaMinus x = sigmaMinus y ∧
            sigmaPlus x = sigmaPlus y) :
    Q64TwoFiberSingleFlipOverlap d10 d01 := by
  intro h10 h01
  by_contra hinterEmpty
  have hdisj : q64Omega10 d10 ∩ q64Omega01 d01 = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hinterEmpty
  rcases hnonOverlapProducesStep h10 h01 hdisj with
    ⟨x, y, hstep, hxy, hminus, hplus⟩
  exact hxy (hsep hstep hminus hplus)

end LateHostReductions

section SmallModulePackingFrontier

/--
For the `1+5` exposed-`K_5` split, unordered seed sizes across the two sides are represented by
the smaller side.
-/
def q64UnorderedFiveSplitType (r : ℕ) : ℕ :=
  min r (5 - r)

/--
The five seed sizes in the size-`5` completion collapse, up to swapping the two sides, to the three
types `(0,5)`, `(1,4)`, and `(2,3)`.
-/
theorem q64_unorderedFiveSplitType_cases {r : ℕ} (hr : r ≤ 5) :
    q64UnorderedFiveSplitType r = 0 ∨ q64UnorderedFiveSplitType r = 1 ∨
      q64UnorderedFiveSplitType r = 2 := by
  unfold q64UnorderedFiveSplitType
  interval_cases r <;> norm_num

/--
After the support-graph pruning that excludes all cycle-square skeletons of length at least `8`,
the residual `m ≥ 6` cycle-square frontier is finite.
-/
theorem q64_cycleSquare_frontier_cases {m : ℕ} (hm6 : 6 ≤ m) (hm8 : m < 8) :
    m = 6 ∨ m = 7 := by
  omega

/-- A directed walk in the ordered-triangle propagation digraph. -/
inductive Q64DirectedWalk {V : Type*} (Step : V → V → Prop) : List V → Prop
  | nil : Q64DirectedWalk Step []
  | singleton (v : V) : Q64DirectedWalk Step [v]
  | cons {v w : V} {tail : List V} :
      Step v w → Q64DirectedWalk Step (w :: tail) → Q64DirectedWalk Step (v :: w :: tail)

/--
The ordered-triangle propagation state graph packages supported ladders as directed walks.
-/
def Q64SupportedLadder {V : Type*} (Step : V → V → Prop) (vertices : List V) : Prop :=
  Q64DirectedWalk Step vertices

theorem q64_supportedLadder_iff_directedWalk
    {V : Type*} {Step : V → V → Prop} {vertices : List V} :
    Q64SupportedLadder Step vertices ↔ Q64DirectedWalk Step vertices :=
  Iff.rfl

/-- A cyclic supported ladder is a directed walk with a closing edge. -/
def Q64CyclicSupportedLadder {V : Type*} (Step : V → V → Prop) (start : V)
    (rest : List V) : Prop :=
  Q64DirectedWalk Step (start :: rest) ∧
    ∃ last ∈ (start :: rest).getLast?, Step last start

end SmallModulePackingFrontier

section DyadicTailOrbitFrontier

variable {U : Type*} [Fintype U] [DecidableEq U]

/--
If a proper nonempty terminal-tail cut is preserved up to complement by a transitive profile
symmetry family, then the cut is balanced.
-/
theorem q64_transitive_invariant_cut_balanced
    (S : Finset U) (hnon : S.Nonempty) (hproper : S ≠ Finset.univ)
    (htrans : ∀ u v : U, ∃ e : Equiv.Perm U,
      e u = v ∧ (S.image e = S ∨ S.image e = Finset.univ \ S)) :
    2 * S.card = Fintype.card U := by
  rcases hnon with ⟨u, huS⟩
  have hexistsOutside : ∃ v : U, v ∉ S := by
    by_contra hno
    apply hproper
    ext v
    constructor
    · intro _hv
      simp
    · intro _hv
      by_contra hvS
      exact hno ⟨v, hvS⟩
  rcases hexistsOutside with ⟨v, hvS⟩
  rcases htrans u v with ⟨e, heu, himg | himg⟩
  · have hvImage : v ∈ S.image e :=
      Finset.mem_image.mpr ⟨u, huS, heu⟩
    rw [himg] at hvImage
    exact False.elim (hvS hvImage)
  · have hcardImage : (S.image e).card = S.card :=
      Finset.card_image_of_injective S e.injective
    have hcardComp : (Finset.univ \ S).card = Fintype.card U - S.card :=
      Finset.card_sdiff_of_subset (by simp)
    rw [himg, hcardComp] at hcardImage
    omega

/-- The two-bit three-orbit residual code from the dyadic determinant package. -/
inductive Q64ThreeOrbitDyadicCode
  | vanishing
  | badOrbit₁
  | badOrbit₂
  | badOrbit₃
  deriving DecidableEq, Repr

/--
The normalized determinant parities `(L₁,L₂) ∈ F₂²` encode exactly the four residual classes:
vanishing, bad `O₁`, bad `O₂`, or bad `O₃`.
-/
def q64ThreeOrbitDyadicCodeOfBits (L₁ L₂ : Bool) : Q64ThreeOrbitDyadicCode :=
  match L₁, L₂ with
  | false, false => Q64ThreeOrbitDyadicCode.vanishing
  | true, false => Q64ThreeOrbitDyadicCode.badOrbit₁
  | false, true => Q64ThreeOrbitDyadicCode.badOrbit₂
  | true, true => Q64ThreeOrbitDyadicCode.badOrbit₃

theorem q64_threeOrbitDyadicCode_cases (L₁ L₂ : Bool) :
    q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.vanishing ∨
      q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₁ ∨
      q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₂ ∨
      q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₃ := by
  cases L₁ <;> cases L₂ <;> simp [q64ThreeOrbitDyadicCodeOfBits]

theorem q64_threeOrbitDyadicCode_minimalPair_iff (L₁ L₂ : Bool) :
    q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₁ ∨
      q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₂ ↔
        L₁.xor L₂ = true := by
  cases L₁ <;> cases L₂ <;> simp [q64ThreeOrbitDyadicCodeOfBits]

theorem q64_threeOrbitDyadicCode_largeOrbit_iff (L₁ L₂ : Bool) :
    q64ThreeOrbitDyadicCodeOfBits L₁ L₂ = Q64ThreeOrbitDyadicCode.badOrbit₃ ↔
      L₁ = true ∧ L₂ = true := by
  cases L₁ <;> cases L₂ <;> simp [q64ThreeOrbitDyadicCodeOfBits]

/-- Even singleton supports never have the new host-frontier size `5`. -/
theorem q64_even_support_ne_five {n : ℕ} (heven : 2 ∣ n) : n ≠ 5 := by
  intro hn
  rcases heven with ⟨k, hk⟩
  omega

/-- Supports divisible by `4` also never have the new host-frontier size `5`. -/
theorem q64_four_dvd_support_ne_five {n : ℕ} (hfour : 4 ∣ n) : n ≠ 5 := by
  intro hn
  rcases hfour with ⟨k, hk⟩
  omega

/-- The `F₂` characteristic vector of a finite orbit packet. -/
def q64F2Indicator (S : Finset U) (u : U) : ZMod 2 := if u ∈ S then 1 else 0

omit [Fintype U] in
/--
For disjoint packets, the aggregate characteristic vector is the sum of the two child
characteristic vectors.  This is the finite algebra behind the dyadic coarsening identity
`[1_B] = [1_{B₀}] + [1_{B₁}]`.
-/
theorem q64_f2Indicator_union_of_disjoint (A B : Finset U) (hdisj : Disjoint A B) :
    q64F2Indicator (A ∪ B) = fun u => q64F2Indicator A u + q64F2Indicator B u := by
  funext u
  by_cases hA : u ∈ A
  · have hB : u ∉ B := by
      intro hB
      exact (Finset.disjoint_left.mp hdisj) hA hB
    simp [q64F2Indicator, hA, hB]
  · by_cases hB : u ∈ B <;> simp [q64F2Indicator, hA, hB]

/-- Complementing a cut adds the all-ones vector in `F₂`. -/
theorem q64_f2Indicator_complement_eq_one_add (S : Finset U) :
    q64F2Indicator (Finset.univ \ S) = fun u => 1 + q64F2Indicator S u := by
  funext u
  by_cases hS : u ∈ S
  · simp [q64F2Indicator, hS]
    decide
  · simp [q64F2Indicator, hS]

omit [Fintype U] in
/-- The three-child version of the disjoint aggregate characteristic-vector identity. -/
theorem q64_f2Indicator_three_disjoint_union (A B C : Finset U)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    q64F2Indicator (A ∪ B ∪ C) =
      fun u => q64F2Indicator A u + q64F2Indicator B u + q64F2Indicator C u := by
  funext u
  by_cases hA : u ∈ A
  · have hB : u ∉ B := by
      intro hB
      exact (Finset.disjoint_left.mp hAB) hA hB
    have hC : u ∉ C := by
      intro hC
      exact (Finset.disjoint_left.mp hAC) hA hC
    simp [q64F2Indicator, hA, hB, hC]
  · by_cases hB : u ∈ B
    · have hC : u ∉ C := by
        intro hC
        exact (Finset.disjoint_left.mp hBC) hB hC
      simp [q64F2Indicator, hA, hB, hC]
    · by_cases hC : u ∈ C <;> simp [q64F2Indicator, hA, hB, hC]

/-- Aggregate complement-orbit obstruction coefficient for a packet. -/
def q64AggregateBeta (weight : U → ZMod 2) (S : Finset U) : ZMod 2 :=
  ∑ u ∈ S, weight u

omit [Fintype U] in
/-- The aggregate `β` obstruction is additive under disjoint coarsening. -/
theorem q64_aggregateBeta_union_of_disjoint
    (weight : U → ZMod 2) (A B : Finset U) (hdisj : Disjoint A B) :
    q64AggregateBeta weight (A ∪ B) =
      q64AggregateBeta weight A + q64AggregateBeta weight B := by
  unfold q64AggregateBeta
  rw [Finset.sum_union hdisj]

/--
Three-block singleton coarsening: the ambient orbit universe is split into two blocks on one
side and one distinguished block on the other side, and the bad cut is the distinguished block.
-/
def Q64ThreeBlockSingletonCoarsening (A₀ A₁ B S : Finset U) : Prop :=
  A₀.Nonempty ∧ A₁.Nonempty ∧ B.Nonempty ∧
    Disjoint A₀ A₁ ∧ Disjoint A₀ B ∧ Disjoint A₁ B ∧
      A₀ ∪ A₁ ∪ B = Finset.univ ∧ S = B

/-- In a three-block singleton coarsening, the cut vector is exactly the singleton block vector. -/
theorem q64_threeBlockSingletonCoarsening_cut_indicator
    {A₀ A₁ B S : Finset U} (h : Q64ThreeBlockSingletonCoarsening A₀ A₁ B S) :
    q64F2Indicator S = q64F2Indicator B := by
  rcases h with ⟨_, _, _, _, _, _, _, hS⟩
  ext u
  simp [q64F2Indicator, hS]

/--
In a three-block singleton coarsening, the complement of the singleton cut is the sum of the two
opposite-side blocks in `F₂`.
-/
theorem q64_threeBlockSingletonCoarsening_complement_indicator
    {A₀ A₁ B S : Finset U} (h : Q64ThreeBlockSingletonCoarsening A₀ A₁ B S) :
    q64F2Indicator (Finset.univ \ S) =
      fun u => q64F2Indicator A₀ u + q64F2Indicator A₁ u := by
  rcases h with ⟨_, _, _, hA₀A₁, hA₀B, hA₁B, hpart, hS⟩
  have hcomp : Finset.univ \ S = A₀ ∪ A₁ := by
    ext u
    constructor
    · intro hu
      have huB : u ∉ B := by
        rw [hS] at hu
        exact (Finset.mem_sdiff.mp hu).2
      have huPart : u ∈ A₀ ∪ A₁ ∪ B := by
        rw [hpart]
        simp
      rw [Finset.mem_union] at huPart
      rcases huPart with hu01 | huBmem
      · exact hu01
      · exact False.elim (huB huBmem)
    · intro hu
      have huB : u ∉ B := by
        rw [Finset.mem_union] at hu
        rcases hu with huA₀ | huA₁
        · intro huB
          exact (Finset.disjoint_left.mp hA₀B) huA₀ huB
        · intro huB
          exact (Finset.disjoint_left.mp hA₁B) huA₁ huB
      rw [Finset.mem_sdiff]
      exact ⟨by simp, by simpa [hS] using huB⟩
  rw [hcomp]
  exact q64_f2Indicator_union_of_disjoint A₀ A₁ hA₀A₁

/--
Abstract coarsening-stability target: whenever a bad aggregate cut is coarsened by the
profile-orbit projection relation, the coarser cut remains bad.
-/
def Q64CoarseningStability (Bad : Finset U → Prop)
    (Coarsens : Finset U → Finset U → Prop) : Prop :=
  ∀ ⦃S T⦄, Bad S → Coarsens S T → Bad T

/--
Abstract many-orbit projection target: any aggregate bad cut can be detected by a three-block
singleton coarsening.
-/
def Q64ManyOrbitProjection (Bad : Finset U → Prop) : Prop :=
  ∀ ⦃S⦄, Bad S →
    ∃ A₀ A₁ B : Finset U, Q64ThreeBlockSingletonCoarsening A₀ A₁ B S ∧ Bad B

/-- The weighted `H_min/H_big` closure target from the dyadic tail notes. -/
def Q64WeightedHMinHBigClosure (Bad Hmin Hbig : Finset U → Prop) : Prop :=
  ∀ ⦃S⦄, Bad S → Hmin S ∨ Hbig S

/--
Weighted mixed-trace splitting target: a bad mixed trace either already has a homogeneous
subobstruction or splits into two nonempty disjoint bad traces.
-/
def Q64WeightedMixedTraceSplitting
    (Bad Homogeneous : Finset U → Prop) : Prop :=
  ∀ ⦃S⦄, Bad S →
    (∃ T : Finset U, T ⊆ S ∧ T.Nonempty ∧ Homogeneous T) ∨
      ∃ A B : Finset U, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
        S = A ∪ B ∧ Bad A ∧ Bad B

/-- The child carry test below the dyadic modulus `2^m`. -/
def q64DyadicChildCarry (m a : ℕ) : ℕ := a / 2 ^ m

/-- The coarse carry test after merging two dyadic children. -/
def q64DyadicCoarseCarry (m a b : ℕ) : ℕ := (a + b) / 2 ^ m

/--
The minimal two-child carry endpoint: each child is below the modulus and has zero carry, but
their merge has coarse carry `1`.
-/
theorem q64_two_child_carry_endpoint {m : ℕ} (hm : 0 < m) :
    q64DyadicChildCarry m (2 ^ (m - 1)) = 0 ∧
      q64DyadicChildCarry m (2 ^ (m - 1)) = 0 ∧
        q64DyadicCoarseCarry m (2 ^ (m - 1)) (2 ^ (m - 1)) = 1 := by
  have hm' : m = (m - 1) + 1 := by omega
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [hm']
    simp [pow_succ]
    ring
  have hchild : q64DyadicChildCarry m (2 ^ (m - 1)) = 0 := by
    unfold q64DyadicChildCarry
    rw [hpow]
    exact Nat.div_eq_of_lt (by
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) (m - 1)])
  have hcoarse :
      q64DyadicCoarseCarry m (2 ^ (m - 1)) (2 ^ (m - 1)) = 1 := by
    unfold q64DyadicCoarseCarry
    rw [hpow]
    have h : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 * 2 ^ (m - 1) := by ring
    rw [h]
    exact Nat.div_self (by positivity)
  exact ⟨hchild, hchild, hcoarse⟩

/--
The two-child endpoint is genuinely non-additive at the carry layer: summing child carry tests
misses the coarse carry bit.
-/
theorem q64_two_child_carry_endpoint_not_additive {m : ℕ} (hm : 0 < m) :
    q64DyadicCoarseCarry m (2 ^ (m - 1)) (2 ^ (m - 1)) ≠
      q64DyadicChildCarry m (2 ^ (m - 1)) +
        q64DyadicChildCarry m (2 ^ (m - 1)) := by
  rcases q64_two_child_carry_endpoint hm with ⟨h0, _, h1⟩
  rw [h0, h1]
  norm_num

/--
The residue of `n` modulo `2*k` is determined by its residue modulo `k` and the parity of the
quotient `n/k`. This is the arithmetic row-divisibility step behind the dyadic tail lift.
-/
theorem q64_dyadic_modEq_bit_decomposition {k n : ℕ} :
    n ≡ n % k + k * ((n / k) % 2) [MOD 2 * k] := by
  have hquot : n / k ≡ (n / k) % 2 [MOD 2] := (Nat.mod_modEq (n / k) 2).symm
  have hmul : k * (n / k) ≡ k * ((n / k) % 2) [MOD k * 2] := hquot.mul_left' k
  have hmul' : k * (n / k) ≡ k * ((n / k) % 2) [MOD 2 * k] := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have hdecomp : n = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
  have hbase :
      n % k + k * (n / k) ≡ n % k + k * ((n / k) % 2) [MOD 2 * k] :=
    Nat.ModEq.rfl.add hmul'
  simpa [← hdecomp] using hbase

/--
If two row sums agree modulo `2^m` and their next quotient bit agrees, then they agree modulo
`2^(m+1)`.  This is the proof-carrying arithmetic version of one dyadic dropped-tail bit step.
-/
theorem q64_dyadic_next_mod_eq_of_low_mod_eq_and_quotient_parity_eq
    {m a b : ℕ}
    (hlow : a % 2 ^ m = b % 2 ^ m)
    (hbit : (a / 2 ^ m) % 2 = (b / 2 ^ m) % 2) :
    a % 2 ^ (m + 1) = b % 2 ^ (m + 1) := by
  have ha := q64_dyadic_modEq_bit_decomposition (k := 2 ^ m) (n := a)
  have hb := q64_dyadic_modEq_bit_decomposition (k := 2 ^ m) (n := b)
  have hrhs :
      a % 2 ^ m + 2 ^ m * ((a / 2 ^ m) % 2) =
        b % 2 ^ m + 2 ^ m * ((b / 2 ^ m) % 2) := by
    rw [hlow, hbit]
  have hmodeq : a ≡ b [MOD 2 * 2 ^ m] := by
    exact ha.trans (by simpa [hrhs] using hb.symm)
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  simpa [hpow] using hmodeq

/-- Natural row-sum residue constancy at a specified modulus. -/
def Q64NatResidueConstAtMod {Row : Type*} (modulus : ℕ) (rowSum : Row → ℕ) : Prop :=
  ∀ a b, rowSum a % modulus = rowSum b % modulus

/--
Row-wise dyadic bit step: if the dropped-tail row sums are constant modulo `2^m` and the next
quotient bit is constant, then the row sums are constant modulo `2^(m+1)`.
-/
theorem q64_natResidueConstAt_next_dyadic_of_low_and_quotientBit
    {Row : Type*} {m : ℕ} {rowSum : Row → ℕ}
    (hlow : Q64NatResidueConstAtMod (2 ^ m) rowSum)
    (hbit : ∀ a b, (rowSum a / 2 ^ m) % 2 = (rowSum b / 2 ^ m) % 2) :
    Q64NatResidueConstAtMod (2 ^ (m + 1)) rowSum := by
  intro a b
  exact q64_dyadic_next_mod_eq_of_low_mod_eq_and_quotient_parity_eq
    (hlow a b) (hbit a b)

/--
Iterated dyadic row-residue lift: freezing the quotient parity at each successive bit upgrades
constancy from modulus `2^m` to modulus `2^(m+n)`.
-/
theorem q64_natResidueConstAt_dyadic_iterate
    {Row : Type*} {m n : ℕ} {rowSum : Row → ℕ}
    (hstart : Q64NatResidueConstAtMod (2 ^ m) rowSum)
    (hbits :
      ∀ i, i < n →
        ∀ a b, (rowSum a / 2 ^ (m + i)) % 2 = (rowSum b / 2 ^ (m + i)) % 2) :
    Q64NatResidueConstAtMod (2 ^ (m + n)) rowSum := by
  revert hstart hbits
  induction n with
  | zero =>
      intro hstart _hbits
      simpa using hstart
  | succ n ih =>
      intro hstart hbits
      have hlow : Q64NatResidueConstAtMod (2 ^ (m + n)) rowSum :=
        ih hstart (fun i hi => hbits i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      have hbit :
          ∀ a b, (rowSum a / 2 ^ (m + n)) % 2 =
            (rowSum b / 2 ^ (m + n)) % 2 :=
        hbits n (Nat.lt_succ_self n)
      have hnext :=
        q64_natResidueConstAt_next_dyadic_of_low_and_quotientBit hlow hbit
      simpa [Nat.add_assoc] using hnext

/--
Starting from the trivial modulus `2^0=1`, freezing every dyadic quotient bit through `j` bits gives
row-residue constancy modulo `2^j`.
-/
theorem q64_natResidueConstAt_dyadic_from_all_quotientBits
    {Row : Type*} {j : ℕ} {rowSum : Row → ℕ}
    (hbits :
      ∀ i, i < j →
        ∀ a b, (rowSum a / 2 ^ i) % 2 = (rowSum b / 2 ^ i) % 2) :
    Q64NatResidueConstAtMod (2 ^ j) rowSum := by
  have hstart : Q64NatResidueConstAtMod (2 ^ 0) rowSum := by
    intro a b
    simp [Nat.mod_one]
  have hiter :=
    q64_natResidueConstAt_dyadic_iterate (m := 0) (n := j) hstart
      (fun i hi a b => by simpa using hbits i hi a b)
  simpa using hiter

/-- The `F₂` mixed second difference on a binary square. -/
def q64BoolMixedSecondDifference (f : Bool → Bool → ZMod 2) : ZMod 2 :=
  f true true + f true false + f false true + f false false

/--
The hidden successor-side `0001` square: both one-child tests vanish, but the double-successor
corner is positive.
-/
def Q64PositiveANDCarryAtom (f : Bool → Bool → ZMod 2) : Prop :=
  f false false = 0 ∧ f true false = 0 ∧ f false true = 0 ∧ f true true = 1

/-- Boolean form of the successor-side `0001` endpoint. -/
def Q64BoolPositiveANDAtom (p : Bool → Bool → Bool) : Prop :=
  p false false = false ∧ p true false = false ∧ p false true = false ∧ p true true = true

/-- Gated-Helly square implication for one localized candidate packet. -/
def Q64GatedHellySquareImplication (Omega : Bool → Bool → Bool) : Prop :=
  Omega false false = true → Omega true false = true → Omega false true = true →
    Omega true true = true

/--
The exact first failure of the gated-Helly square implication is a successor-side positive-AND row,
represented by the Boolean complement of the candidate-membership table.
-/
theorem q64_positiveAND_of_gatedHellySquare_failure
    {Omega : Bool → Bool → Bool}
    (h00 : Omega false false = true) (h10 : Omega true false = true)
    (h01 : Omega false true = true) (h11 : Omega true true = false) :
    Q64BoolPositiveANDAtom (fun x y => !Omega x y) := by
  simp [Q64BoolPositiveANDAtom, h00, h10, h01, h11]

/-- Coerce a Boolean endpoint table into its `F₂` characteristic table. -/
def q64BoolToF2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The concrete positive-AND square model. -/
def q64ANDCarryModel (x y : Bool) : ZMod 2 := if x && y then 1 else 0

/-- The Boolean AND square is the minimal positive carry atom. -/
theorem q64_positiveANDCarryAtom_model : Q64PositiveANDCarryAtom q64ANDCarryModel := by
  simp [Q64PositiveANDCarryAtom, q64ANDCarryModel]

/-- A Boolean `0001` endpoint is the same positive carry atom after passage to `F₂`. -/
theorem q64_boolPositiveANDAtom_to_f2
    {p : Bool → Bool → Bool} (h : Q64BoolPositiveANDAtom p) :
    Q64PositiveANDCarryAtom (fun x y => q64BoolToF2 (p x y)) := by
  rcases h with ⟨h00, h10, h01, h11⟩
  simp [Q64PositiveANDCarryAtom, q64BoolToF2, h00, h10, h01, h11]

/-- A positive carry atom has mixed second difference equal to `1`. -/
theorem q64_positiveANDCarryAtom_mixedSecondDifference
    {f : Bool → Bool → ZMod 2} (h : Q64PositiveANDCarryAtom f) :
    q64BoolMixedSecondDifference f = 1 := by
  rcases h with ⟨h00, h10, h01, h11⟩
  simp [q64BoolMixedSecondDifference, h00, h10, h01, h11]

/--
The positive-AND square is invisible to the two lower unary increments while its mixed second
difference is nonzero.
-/
theorem q64_positiveANDCarryAtom_unary_increments_zero
    {f : Bool → Bool → ZMod 2} (h : Q64PositiveANDCarryAtom f) :
    f true false - f false false = 0 ∧ f false true - f false false = 0 ∧
      q64BoolMixedSecondDifference f = 1 := by
  rcases h with ⟨h00, h10, h01, h11⟩
  simp [q64BoolMixedSecondDifference, h00, h10, h01, h11]

/--
First-return positive-AND carry atom: the algebraic square plus the corridor/minimality hypotheses
needed by the host-local endpoint.
-/
def Q64FirstReturnPositiveANDCarryAtom
    (f : Bool → Bool → ZMod 2) (CleanCorridor FirstReturn : Prop) : Prop :=
  Q64PositiveANDCarryAtom f ∧ CleanCorridor ∧ FirstReturn

/--
Successor-side `0001` exclusion for a pair-status witness on a hidden square.  This is the
Lean-facing form of the binary pair-status endpoint isolated by the corrected roadmap.
-/
def Q64SuccessorSide0001Exclusion (p : Bool → Bool → Bool) : Prop :=
  ¬ Q64BoolPositiveANDAtom p

/-- A two-fiber missing-corner theorem rules out the feasible `0001` counterexample. -/
theorem q64_successorSide0001_exclusion_of_missingCorner
    {Feasible : Bool → Bool → Prop} (hcorner : Q64TwoFiberMissingCorner Feasible) :
    ¬ (Feasible false false ∧ Feasible true false ∧ Feasible false true ∧
      ¬ Feasible true true) :=
  q64_no_three_corner_counterexample_of_missingCorner hcorner

/-- Pair-status constancy on a median fiber after unary chamber data are fixed. -/
def Q64BinaryPairStatusConstancy (M : Finset U) (status : U → Bool) : Prop :=
  ∀ ⦃u v : U⦄, u ∈ M → v ∈ M → status u = status v

/--
Reduction used by the median-fiber audit: failure of pair-status constancy produces a
successor-side `0001` table.
-/
def Q64PairStatusConstancyReducesTo0001 (M : Finset U) (status : U → Bool) : Prop :=
  ¬ Q64BinaryPairStatusConstancy M status →
    ∃ p : Bool → Bool → Bool, Q64BoolPositiveANDAtom p

omit [Fintype U] [DecidableEq U] in
/-- If every successor-side `0001` table is excluded, the reduction gives pair-status constancy. -/
theorem q64_pairStatusConstancy_of_reducesTo0001
    {M : Finset U} {status : U → Bool}
    (hred : Q64PairStatusConstancyReducesTo0001 M status)
    (hno0001 : ∀ p : Bool → Bool → Bool, ¬ Q64BoolPositiveANDAtom p) :
    Q64BinaryPairStatusConstancy M status := by
  by_contra hnot
  rcases hred hnot with ⟨p, hp⟩
  exact hno0001 p hp

/-- The two dyadic child shadows meet in one fixed peeled package. -/
def Q64TwoShadowIntersection (Sh_H Sh_J : Finset U) : Prop :=
  (Sh_H ∩ Sh_J).Nonempty

omit [Fintype U] in
/--
Failure of the two-shadow intersection splits into: a missing shadow, or two nonempty disjoint
shadows.  This is the finite set-theoretic part of the two-shadow endpoint.
-/
theorem q64_twoShadow_failure_cases (Sh_H Sh_J : Finset U)
    (hfail : ¬ Q64TwoShadowIntersection Sh_H Sh_J) :
    ¬ Sh_H.Nonempty ∨ ¬ Sh_J.Nonempty ∨
      (Sh_H.Nonempty ∧ Sh_J.Nonempty ∧ Disjoint Sh_H Sh_J) := by
  by_cases hH : Sh_H.Nonempty
  · by_cases hJ : Sh_J.Nonempty
    · right
      right
      refine ⟨hH, hJ, ?_⟩
      rw [Finset.disjoint_left]
      intro x hxH hxJ
      exact hfail ⟨x, by simp [hxH, hxJ]⟩
    · right
      left
      exact hJ
  · left
    exact hH

/--
A common shadow discharges the carry endpoint: once the two child shadows intersect, the carry
cannot remain as a separate obstruction.
-/
def Q64CarryDischargedByCommonShadow
    (Sh_H Sh_J : Finset U) (CarryEndpoint : Prop) : Prop :=
  Q64TwoShadowIntersection Sh_H Sh_J → ¬ CarryEndpoint

/--
Positive mixed carry rows are paired with negative overlap rows inside the same peeled package.
-/
def Q64MixedCompensatorRouting
    (Positive Negative : Finset U) (SamePackage : U → U → Prop) : Prop :=
  ∀ p ∈ Positive, ∃ n ∈ Negative, SamePackage p n

/--
The second routing layer for the dyadic endpoint: compensator routing handles the `0001/0111`
mixed term and unary-leak routing places the successor residuals in the same fixed package.
-/
def Q64TwoLayerCarryRouting
    (Positive Negative : Finset U) (SamePackage : U → U → Prop)
    (UnaryLeakRouted : Prop) : Prop :=
  Q64MixedCompensatorRouting Positive Negative SamePackage ∧ UnaryLeakRouted

/--
Dirty shared-slack absorption: the remaining budget-one boundary either preserves an active bad
pair on one side or localizes to the fixed-fiber endpoint catalogue.
-/
def Q64DirtySharedSlackAbsorption
    (Boundary PreservesActivePair LocalizesToCatalogue : Prop) : Prop :=
  Boundary → PreservesActivePair ∨ LocalizesToCatalogue

/--
Corrected q-marker endpoint from the current roadmap: in the fully skew splitter branch, the marker
must yield a proper first-return submarker, a prime-shell module exit, or an already closed local exit.
-/
def Q64QMarkerCarrierMarkerCoupling
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit : Prop) : Prop :=
  FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit

/--
`proof.md` four-exit form of q-marker carrier/marker coupling: a fully skew endpoint yields a
proper submarker, a prime-shell module exit, a closed local exit, or an explicit regular `q`-set.
-/
def Q64QMarkerCarrierMarkerCouplingWithRegularQSet
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop) :
    Prop :=
  FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet

/--
The four-exit `proof.md` q-marker theorem recovers the older three-exit API whenever a regular
`q`-set is treated as one of the already closed exits.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_regularQSetExit
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop}
    (h :
      Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet)
    (hregular : RegularQSet → ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  intro hskew
  rcases h hskew with hsub | hmodule | hlocal | hreg
  · exact Or.inl hsub
  · exact Or.inr (Or.inl hmodule)
  · exact Or.inr (Or.inr hlocal)
  · exact Or.inr (Or.inr (hregular hreg))

/-- The four-exit q-marker theorem gives the no-survivor statement when all exits are excluded. -/
theorem q64_no_fullySkewQMarkerSurvivor_of_regularQSetCoupling
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop}
    (h :
      Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet)
    (hskew : FullySkewSplitter) (hnoSub : ¬ ProperSubmarker)
    (hnoModule : ¬ PrimeModuleExit) (hnoLocal : ¬ ClosedLocalExit)
    (hnoRegular : ¬ RegularQSet) : False := by
  rcases h hskew with hsub | hmodule | hlocal | hreg
  · exact hnoSub hsub
  · exact hnoModule hmodule
  · exact hnoLocal hlocal
  · exact hnoRegular hreg

/--
Lean-facing data for `proof.md` Theorem 9.3.  A nonconstant terminal residue produces a fully skew
q-marker survivor; the four q-marker exits all close to a regular q-set; and if no residue is
nonconstant, the constant-residue lemma directly gives the regular q-set.
-/
structure Q64TerminalDyadicTheoremData
    (NonconstantResidue FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      RegularQSet : Prop) : Prop where
  constantResidueRegular : (¬ NonconstantResidue) → RegularQSet
  obstructionFullySkew : NonconstantResidue → FullySkewSplitter
  qMarkerCoupling :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet
  properSubmarkerCloses : ProperSubmarker → RegularQSet
  primeModuleCloses : PrimeModuleExit → RegularQSet
  closedLocalCloses : ClosedLocalExit → RegularQSet

/--
Abstract terminal dyadic theorem: the Section 9 contradiction proof is just case analysis once its
graph-specific ingredients are supplied.
-/
theorem q64_terminalDyadicTheorem_of_data
    {NonconstantResidue FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      RegularQSet : Prop}
    (hdata :
      Q64TerminalDyadicTheoremData NonconstantResidue FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet) :
    RegularQSet := by
  classical
  by_cases hnonconstant : NonconstantResidue
  · rcases hdata.qMarkerCoupling (hdata.obstructionFullySkew hnonconstant) with
      hsub | hmodule | hlocal | hregular
    · exact hdata.properSubmarkerCloses hsub
    · exact hdata.primeModuleCloses hmodule
    · exact hdata.closedLocalCloses hlocal
    · exact hregular
  · exact hdata.constantResidueRegular hnonconstant

/--
Static split-quotient exhaustion at the q-marker endpoint: every fully skew splitter survivor is
reduced to the marker-splitting zero-sum atom, the product-firewall frame, and its weighted quotient
packaging.
-/
def Q64StaticSplitQuotientExhaustion
    (FullySkewSplitter MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging : Prop) : Prop :=
  FullySkewSplitter → MarkerSplittingZeroSumAtom ∧ ProductFirewall ∧ WeightedQuotientPackaging

/--
Component form of the static split-quotient audit: finite packet arithmetic first reduces a fully
skew survivor to the marker-splitting zero-sum atom, then the product-firewall and weighted-quotient
packaging are constructed from that atom.
-/
structure Q64StaticSplitQuotientAudit
    (FullySkewSplitter MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging : Prop) : Prop where
  zeroSumAtom : FullySkewSplitter → MarkerSplittingZeroSumAtom
  productFirewall : MarkerSplittingZeroSumAtom → ProductFirewall
  weightedPackaging :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging

/-- The component static split-quotient audit assembles to the exhaustion statement. -/
theorem q64_staticSplitQuotientExhaustion_of_audit
    {FullySkewSplitter MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging : Prop}
    (haudit :
      Q64StaticSplitQuotientAudit FullySkewSplitter MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging) :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging := by
  intro hskew
  have hzero := haudit.zeroSumAtom hskew
  have hfirewall := haudit.productFirewall hzero
  exact ⟨hzero, hfirewall, haudit.weightedPackaging hzero hfirewall⟩

/--
Binary trace-coalescence / skew-ladder exclusion: the first failed row of a separating dirty row
coalesces with it in one residual fixed fiber.
-/
def Q64BinaryTraceCoalescence
    (Separates : U → Prop) (FirstFailed Coalesces : U → U → Prop) : Prop :=
  ∀ ⦃r s : U⦄, Separates r → FirstFailed r s → Coalesces r s

/--
Binary crossing endpoint: a minimal crossing carrier has either an admissible repair/reanchor row or
localizes the alternating failed-row ladder to the closed Section-40 catalogue.
-/
def Q64BinaryCrossingEndpoint
    (Separates AdmissibleRepair LocalizesLadder : U → Prop) : Prop :=
  (∃ r : U, Separates r) →
    ∃ r : U, Separates r ∧ (AdmissibleRepair r ∨ LocalizesLadder r)

/--
Common discrepancy packaging for the balanced-flip branch: the two opposite rows are represented in
one peeled raw-discrepancy space with opposite defects on the same active pair.
-/
def Q64CommonDiscrepancyPackaging
    (SamePackage OppositeRawDefects : U → U → Prop) : Prop :=
  ∀ ⦃r s : U⦄, SamePackage r s → OppositeRawDefects r s

/--
The audited equivalence package for the current binary endpoint: trace coalescence, common-shadow
synchronization, adjacent shared-slice admissibility, and two-fiber overlap are treated as the same
remaining theorem surface.
-/
def Q64BinaryEndpointEquivalence
    (TraceCoalescence CommonShadow SharedSliceAdmissible TwoFiberOverlap : Prop) : Prop :=
  (TraceCoalescence ↔ CommonShadow) ∧
    (CommonShadow ↔ SharedSliceAdmissible) ∧
      (SharedSliceAdmissible ↔ TwoFiberOverlap)

/-- Oriented two-row holonomy has been reduced to the successor-side `0001` atom. -/
def Q64OrientedHolonomyReducesTo0001 (Holonomy : Prop) : Prop :=
  Holonomy → ∃ p : Bool → Bool → Bool, Q64BoolPositiveANDAtom p

/-- Excluding `0001` excludes every holonomy instance covered by the reduction. -/
theorem q64_no_orientedHolonomy_of_reducesTo0001
    {Holonomy : Prop} (hred : Q64OrientedHolonomyReducesTo0001 Holonomy)
    (hno0001 : ∀ p : Bool → Bool → Bool, ¬ Q64BoolPositiveANDAtom p) :
    ¬ Holonomy := by
  intro hhol
  rcases hred hhol with ⟨p, hp⟩
  exact hno0001 p hp

/--
Balanced-flip / same-side-boundary dichotomy for the turn-parity normal form.
The same-side branch is represented by a boundary-routing obligation.
-/
def Q64BalancedFlipSameSideBoundaryDichotomy
    (Holonomy BalancedFlip SameSideBoundaryRouting : Prop) : Prop :=
  Holonomy → BalancedFlip ∨ SameSideBoundaryRouting

/--
A common peeled package turns pair-status constancy into the raw-discrepancy packaging needed for
the balanced-flip branch.
-/
def Q64CommonPeeledPackageFromPairStatus
    (PairStatusConstant CommonPackage : Prop) : Prop :=
  PairStatusConstant → CommonPackage

/-- The endpoint-mass audit leaves a pointwise sign law or paired-compensator routing. -/
def Q64EndpointMassAlternative
    (PointwiseSignLaw PairedCompensatorRouting : Prop) : Prop :=
  PointwiseSignLaw ∨ PairedCompensatorRouting

/--
No-shared-slack / sign-law endpoint: a double same-sign slack-row saturation must either coalesce,
fall to the clean marked-add catalogue, or enter the dirty budget-one absorption branch.
-/
def Q64NoSharedSlackReduction
    (DoubleSlackSaturation Coalesces CleanMarkedAdd DirtyAbs1 : Prop) : Prop :=
  DoubleSlackSaturation → Coalesces ∨ CleanMarkedAdd ∨ DirtyAbs1

/--
Final pair-status endpoint: a first-return `0001` coordinate must be killed either by the
history-sensitive anti-Horn/submodularity law or by support decrease of its shared-slack carrier.
-/
def Q64PairStatusAntiHornOrSharedSlackSupportDecrease
    (FirstReturn0001 PairStatusAntiHornSubmodularity SharedSlackSupportDecrease : Prop) : Prop :=
  FirstReturn0001 → PairStatusAntiHornSubmodularity ∨ SharedSlackSupportDecrease

/-- If both closing routes are impossible, no first-return `0001` coordinate survives. -/
theorem q64_no_firstReturn0001_of_pairStatusAntiHornOrSupportDecrease
    {FirstReturn0001 PairStatusAntiHornSubmodularity SharedSlackSupportDecrease : Prop}
    (h :
      Q64PairStatusAntiHornOrSharedSlackSupportDecrease FirstReturn0001
        PairStatusAntiHornSubmodularity SharedSlackSupportDecrease)
    (hnoHorn : ¬ PairStatusAntiHornSubmodularity)
    (hnoDecrease : ¬ SharedSlackSupportDecrease) :
    ¬ FirstReturn0001 := by
  intro h0001
  rcases h h0001 with hhorn | hdecrease
  · exact hnoHorn hhorn
  · exact hnoDecrease hdecrease

/-- Prime-shell budget-one cycle-breaker, isolated as a named endpoint. -/
def Q64PrimeShellBudgetOneCycleBreaker
    (BudgetOneCycle DefectSwitchingSquareExcluded : Prop) : Prop :=
  BudgetOneCycle → DefectSwitchingSquareExcluded

/--
Shortest irreducible budget-one cycles reduce to the first-return defect-switching square; no
separate long-cycle obstruction remains.
-/
def Q64ShortestCycleReducesToFirstReturnSquare
    (ShortestCycle FirstReturnDefectSwitchingSquare : Prop) : Prop :=
  ShortestCycle → FirstReturnDefectSwitchingSquare

/-- The finite seed shapes forced by a same-type defect-switching shared-slack square. -/
inductive Q64FiveVertexSeedShape
  | p4
  | house
  | p5
  | c5
  deriving DecidableEq, Repr

/--
In the `+` orientation of the defect-switching square, the inserted-root degree tests force the two
defect types to agree.
-/
theorem q64_defectTypes_equal_of_insertedRoot_tests
    {tau_d tau_e xy : Bool} (hx : xy = !tau_e) (hy : xy = !tau_d) :
    tau_d = tau_e := by
  cases tau_d <;> cases tau_e <;> cases xy <;> simp at hx hy ⊢

/--
The five-vertex seed table after the two defect types agree: miss/miss gives `P₄` or house; add/add
gives `P₅` or `C₅`, according to the internal edge `de`.
-/
def q64FiveVertexSeedShapeOfSameType (tau de : Bool) : Q64FiveVertexSeedShape :=
  match tau, de with
  | false, false => Q64FiveVertexSeedShape.p4
  | false, true => Q64FiveVertexSeedShape.house
  | true, false => Q64FiveVertexSeedShape.p5
  | true, true => Q64FiveVertexSeedShape.c5

/-- The defect-switching seed has exactly one of the four Section-40 seed shapes. -/
theorem q64_fiveVertexSeedShape_cases (tau de : Bool) :
    q64FiveVertexSeedShapeOfSameType tau de = Q64FiveVertexSeedShape.p4 ∨
      q64FiveVertexSeedShapeOfSameType tau de = Q64FiveVertexSeedShape.house ∨
        q64FiveVertexSeedShapeOfSameType tau de = Q64FiveVertexSeedShape.p5 ∨
          q64FiveVertexSeedShapeOfSameType tau de = Q64FiveVertexSeedShape.c5 := by
  cases tau <;> cases de <;> simp [q64FiveVertexSeedShapeOfSameType]

/--
Five-vertex seed packaging: the local `P₄`, house, `P₅`, or `C₅` seed lies in one fixed-fiber /
prime weighted-quotient attachment satisfying the Section-40 modular hypotheses.
-/
def Q64FiveVertexSeedPackaging
    (SeedPackaged : Q64FiveVertexSeedShape → Prop) : Prop :=
  ∀ shape : Q64FiveVertexSeedShape, SeedPackaged shape

/--
Local residue homogenization for the five-vertex seed: the low-set correction is internalized in the
same fixed-fiber / weighted-quotient closure, without assuming a global completer.
-/
def Q64LocalResidueHomogenizer
    (Seed : Finset U) (CorrectionInternalized : Prop) : Prop :=
  Seed.Nonempty → CorrectionInternalized

/--
Marked two-class quartet forced by the low-set update: two same-trace pairs are separated exactly by
the marked shared-slack set, with the balanced `C₄` / `2K₂` local shape.
-/
def Q64MarkedTwoClassQuartet
    (DeletedPairSameTrace InsertedPairSameTrace SeparatedOnlyByMarker BalancedLocalShape : Prop) :
    Prop :=
  DeletedPairSameTrace ∧ InsertedPairSameTrace ∧ SeparatedOnlyByMarker ∧ BalancedLocalShape

/--
The localization theorem still needed after the marked two-class reduction: the quartet enters one
Section-40 frame, gives a completer, or lands in a closed weighted quotient seed.
-/
def Q64MarkedTwoClassLocalization
    (QuartetLocalized Completer ClosedWeightedQuotientSeed : Prop) : Prop :=
  QuartetLocalized ∨ Completer ∨ ClosedWeightedQuotientSeed

/-- Minimality package for q-marker obstructions. -/
def Q64MinimalQMarker (Marker : ℕ → Prop) (R : ℕ) : Prop :=
  Marker R ∧ ∀ R' : ℕ, Marker R' → R' < R → False

/-- A concrete size-`4` marker used by the q-marker audit warning. -/
def q64StaticQ4Marker : Finset (Fin 4) := Finset.univ

/-- One binary active component inside the size-`4` marker. -/
def q64StaticQ4ActiveComponent : Finset (Fin 4) :=
  Finset.univ.image (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 4))

/-- The active component has size `2`. -/
theorem q64_staticQ4ActiveComponent_card : q64StaticQ4ActiveComponent.card = 2 := by
  unfold q64StaticQ4ActiveComponent
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) h

/-- The q-marker itself has size `4`. -/
theorem q64_staticQ4Marker_card : q64StaticQ4Marker.card = 4 := by
  unfold q64StaticQ4Marker
  simp

/--
Finite size witness for the audit warning: a binary active component can sit inside a marker of
size `q=4`, so binary carrier collapse alone does not force a sub-`q` marker.
-/
theorem q64_binaryCarrier_does_not_bound_q4_marker :
    ∃ R C : Finset (Fin 4), C ⊆ R ∧ C.card = 2 ∧ R.card = 4 := by
  refine ⟨q64StaticQ4Marker, q64StaticQ4ActiveComponent, ?_, ?_, ?_⟩
  · intro x hx
    unfold q64StaticQ4Marker
    simp
  · exact q64_staticQ4ActiveComponent_card
  · exact q64_staticQ4Marker_card

/--
Two static outside rows from the `proof.md` binary-carrier warning: each row sees exactly one endpoint
of each active binary component while the whole marker still has size `q=4`.
-/
def q64StaticQ4SkewRow (row : Fin 2) (p : Fin 4) : Bool :=
  if row = 0 then decide (p = 0 ∨ p = 2) else decide (p = 0 ∨ p = 3)

/-- The two q=4 static rows are fully skew on both binary components. -/
theorem q64_staticQ4SkewRows_split_both_binary_components :
    q64StaticQ4SkewRow 0 0 ≠ q64StaticQ4SkewRow 0 1 ∧
      q64StaticQ4SkewRow 0 2 ≠ q64StaticQ4SkewRow 0 3 ∧
        q64StaticQ4SkewRow 1 0 ≠ q64StaticQ4SkewRow 1 1 ∧
          q64StaticQ4SkewRow 1 2 ≠ q64StaticQ4SkewRow 1 3 := by
  decide

/--
Binary carrier collapse plus ambient separation is still compatible with an exact size-`q` marker in
the concrete `q=4` model.
-/
theorem q64_binaryCarrier_staticRows_do_not_shrink_q4_marker :
    (∃ row : Fin 2, q64StaticQ4SkewRow row 0 ≠ q64StaticQ4SkewRow row 1) ∧
      (∃ row : Fin 2, q64StaticQ4SkewRow row 2 ≠ q64StaticQ4SkewRow row 3) ∧
        q64StaticQ4Marker.card = 4 := by
  refine ⟨⟨0, ?_⟩, ⟨⟨0, ?_⟩, q64_staticQ4Marker_card⟩⟩ <;> decide

/-- A preserved-side proper submarker contradicts q-marker minimality. -/
theorem q64_no_preservedSide_submarker_of_minimalQMarker
    {Marker : ℕ → Prop} {R R' : ℕ} (hmin : Q64MinimalQMarker Marker R)
    (hsub : Marker R') (hlt : R' < R) : False :=
  hmin.2 R' hsub hlt

/--
The sharpened final q-marker atom: a provenance splitter is admissible, or its first failed row
carries a complete smaller first-return shared-slack marker.
-/
def Q64QMarkerProvenanceSupportDecrease
    (ProvenanceSplitterAdmissible SmallerCompleteMarker LocalNonMarkerExit : Prop) : Prop :=
  ProvenanceSplitterAdmissible ∨ SmallerCompleteMarker ∨ LocalNonMarkerExit

/-- The flat-connection trichotomy gives a Theorem-G branch once its three identified endpoints route. -/
theorem q64_theoremG_of_flatConnectionFailureTrichotomy
    {AmbientHighErrorSplitter FlatConnectionFailure NonfilledRepairFace CurvedFilledFace
      FlatNontrivialMonodromyLoop SquareTransverseBreaker SharedSlackQMarker
      AdmissibleModulePrimenessAgain OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hfailure : AmbientHighErrorSplitter → FlatConnectionFailure)
    (htri :
      Q64FlatConnectionFailureTrichotomy FlatConnectionFailure NonfilledRepairFace CurvedFilledFace
        FlatNontrivialMonodromyLoop)
    (hid :
      Q64FlatConnectionFailureEndpointIdentification NonfilledRepairFace CurvedFilledFace
        FlatNontrivialMonodromyLoop SquareTransverseBreaker SharedSlackQMarker
        AdmissibleModulePrimenessAgain)
    (hrepair :
      SquareTransverseBreaker →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hcurved :
      SharedSlackQMarker →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hflat :
      AdmissibleModulePrimenessAgain →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases htri (hfailure hsplit) with hnonfilled | hcurvedFace | hflatLoop
  · exact hrepair (hid.1 hnonfilled)
  · exact hcurved (hid.2.1 hcurvedFace)
  · exact hflat (hid.2.2 hflatLoop)

/--
The ordered-boundary certificate closes the transported branch; the only non-formal branch left by
ambient-to-boundary transport is the one-state bounce.
-/
theorem q64_theoremG_of_ambientToBoundaryTransportWithBounce
    {AmbientHighErrorSplitter OrderedBoundaryRow InternalFailureWholeSplitterSide
      CompleteSmallerQMarker LocalRegularizingExit OneStateHighErrorBounceSameSlippedSide
      OrderedBoundaryAdmissible : Prop}
    (htransport :
      Q64AmbientToBoundaryTransportWithBounce AmbientHighErrorSplitter OrderedBoundaryRow
        LocalRegularizingExit OneStateHighErrorBounceSameSlippedSide)
    (hcert :
      Q64OrderedBoundarySlipCertificate OrderedBoundaryRow InternalFailureWholeSplitterSide
        CompleteSmallerQMarker)
    (hbounce :
      OneStateHighErrorBounceSameSlippedSide →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases htransport hsplit with hboundary | hlocal | hbounce'
  · exact Or.inr (Or.inl (hcert hboundary).2)
  · exact Or.inr (Or.inr hlocal)
  · exact hbounce hbounce'

/-- The three host-frontier closures reduce the one-state bounce to the missing-`0111` table branch. -/
theorem q64_oneStateBounce_closed_of_hostFrontierShadow
    {OneStateHighErrorBounce PairChamberHiddenChoiceSeparation AnchoredPersistenceNoSplitQPlus
      AnchoredOneCornerLiftQj Missing0111Table OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hshadow :
      Q64OneStateBounceHostFrontierShadow OneStateHighErrorBounce
        PairChamberHiddenChoiceSeparation AnchoredPersistenceNoSplitQPlus
        AnchoredOneCornerLiftQj Missing0111Table)
    (hpair :
      PairChamberHiddenChoiceSeparation →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hpersist :
      AnchoredPersistenceNoSplitQPlus →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hlift :
      AnchoredOneCornerLiftQj →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hmissing :
      Missing0111Table →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    OneStateHighErrorBounce →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hbounce
  rcases hshadow hbounce with hpair' | hpersist' | hlift' | hmissing'
  · exact hpair hpair'
  · exact hpersist hpersist'
  · exact hlift hlift'
  · exact hmissing hmissing'

/--
The clone-packet loop analysis closes the one-state bounce only through a boundary provenance
certificate or by returning to the two-packet non-overlap atom.
-/
theorem q64_oneStateBounce_closed_of_clonePacketCycle
    {OneStateHighErrorBounce PrimeShellBreakerOfBouncedRows SameCutHighErrorClonePacket
      AdmissibleModuleWithUnpromotedAmbientBreaker BoundaryProvenanceCertificate
      TwoPacketNonOverlapAtom0101_0011 OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hbreaker : OneStateHighErrorBounce → PrimeShellBreakerOfBouncedRows)
    (hclone :
      Q64SameCutHighErrorClonePacketReduction PrimeShellBreakerOfBouncedRows
        SameCutHighErrorClonePacket AdmissibleModuleWithUnpromotedAmbientBreaker)
    (hcycle :
      Q64ClonePacketCycleReduction SameCutHighErrorClonePacket BoundaryProvenanceCertificate
        TwoPacketNonOverlapAtom0101_0011)
    (hcert :
      BoundaryProvenanceCertificate →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hatom :
      TwoPacketNonOverlapAtom0101_0011 →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    OneStateHighErrorBounce →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hbounce
  rcases hclone (hbreaker hbounce) with ⟨hpacket, _⟩
  rcases hcycle hpacket with hboundary | htwoPacket
  · exact hcert hboundary
  · exact hatom htwoPacket

/-- Clone-package graph reduction closes after routing the acyclic and transposition branches. -/
theorem q64_clonePackageGraph_closed_of_transpositionReduction
    {ClonePackageGraph AcyclicClonePackageGraph TwoStatePackageTransposition AnchoredSubcaseClosed
      IrreducibleMovesAnchor AnchoredFrameSlipEndpoint OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hgraph :
      Q64ClonePackageGraphReduction ClonePackageGraph AcyclicClonePackageGraph
        TwoStatePackageTransposition)
    (htransposition :
      Q64TwoStateTranspositionFrameSlip TwoStatePackageTransposition AnchoredSubcaseClosed
        IrreducibleMovesAnchor AnchoredFrameSlipEndpoint)
    (hacyclic :
      AcyclicClonePackageGraph →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hanchored :
      AnchoredSubcaseClosed →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hslip :
      AnchoredFrameSlipEndpoint →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    ClonePackageGraph →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hcloneGraph
  rcases hgraph hcloneGraph with hacyclicGraph | htwoState
  · exact hacyclic hacyclicGraph
  rcases htransposition htwoState with hclosed | hmove
  · exact hanchored hclosed
  · exact hslip hmove.2

/-- The anchored frame-slip endpoint closes through the single-chamber lift dichotomy once both branches
route. -/
theorem q64_anchoredFrameSlip_closed_of_singleChamberLift
    {AnchoredFrameSlipEndpoint SingleChamberFlatAnchoredSlipEdge OneCornerLiftClosed
      OneCornerLiftFailure0001Square OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hpath :
      Q64ShortestFlatAnchorPathReduction AnchoredFrameSlipEndpoint
        SingleChamberFlatAnchoredSlipEdge)
    (hlift :
      Q64SingleChamberFlatSlipLiftDichotomy SingleChamberFlatAnchoredSlipEdge
        OneCornerLiftClosed OneCornerLiftFailure0001Square)
    (hclosed :
      OneCornerLiftClosed →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hfailure :
      OneCornerLiftFailure0001Square →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    AnchoredFrameSlipEndpoint →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hslip
  rcases hlift (hpath hslip) with hliftClosed | h0001
  · exact hclosed hliftClosed
  · exact hfailure h0001

/-- Hidden-package cover classification closes once the cover branch and odd-face branches route. -/
theorem q64_hiddenCover_closed_of_branchPointClassification
    {HiddenPackageCoverBranchPoint OneCornerLiftFailure SquareTransverseBreaker OddFilledFace
      Marker0001 OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hclass :
      Q64HiddenCoverBranchPointClassification HiddenPackageCoverBranchPoint OneCornerLiftFailure
        SquareTransverseBreaker OddFilledFace Marker0001)
    (hlift :
      OneCornerLiftFailure →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hbreaker :
      SquareTransverseBreaker →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hmarker :
      Marker0001 →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    (HiddenPackageCoverBranchPoint ∨ OddFilledFace) →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hbranch
  rcases hbranch with hcover | hodd
  · rcases hclass.1 hcover with hfail | hsq
    · exact hlift hfail
    · exact hbreaker hsq
  · exact hmarker (hclass.2 hodd)

/--
The latest two-sheeted-cover endpoint gives Theorem G once mixed edge tables, base-boundary cuts, and
sheet-character discontinuities are routed to the already named exits.
-/
theorem q64_theoremG_of_twoPrimarySheetCharacterProvenance
    {FullySkewSplitter NonlocalAmbientSeparator MixedEdgeBranchPoint BaseBoundaryCut
      GlobalSheetCharacterSeparator FirstReturnBoundarySide BranchPoint0001OrSquareTransverse
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hseparator : FullySkewSplitter → NonlocalAmbientSeparator)
    (hpurify :
      Q64HiddenPackageCoverEdgeTablePurification NonlocalAmbientSeparator MixedEdgeBranchPoint
        BaseBoundaryCut GlobalSheetCharacterSeparator)
    (hsheet :
      Q64TwoPrimarySheetCharacterProvenance GlobalSheetCharacterSeparator FirstReturnBoundarySide
        BranchPoint0001OrSquareTransverse)
    (hmixed :
      MixedEdgeBranchPoint →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hbase :
      BaseBoundaryCut →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hside : FirstReturnBoundarySide → OrderedBoundaryAdmissible)
    (hbranch :
      BranchPoint0001OrSquareTransverse →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hpurify (hseparator hskew) with hmixed' | hbase' | hsheet'
  · exact hmixed hmixed'
  · exact hbase hbase'
  · rcases hsheet hsheet' with hfirst | hbranch'
    · exact Or.inl (hside hfirst)
    · exact hbranch hbranch'

/-- Star-flat slip-edge provenance supplies the single-slip child-realization endpoint. -/
theorem q64_singleSlipChildRealization_of_starFlatSlipEdgeProvenance
    {AnchoredRankOneSlipEdge PrimitiveAnchoredSlipEdge EveryAnchoredStarFaceFilledFlat
      OrderedFirstReturnBoundaryEdge QHalfChildCarrier BranchSquare
      BranchPoint0001OrSquareTransverse : Prop}
    (hstar :
      Q64StarFlatSlipEdgeProvenance PrimitiveAnchoredSlipEdge EveryAnchoredStarFaceFilledFlat
        OrderedFirstReturnBoundaryEdge BranchSquare)
    (hprimitive : AnchoredRankOneSlipEdge → PrimitiveAnchoredSlipEdge)
    (hfaces : AnchoredRankOneSlipEdge → EveryAnchoredStarFaceFilledFlat)
    (hchild : OrderedFirstReturnBoundaryEdge → QHalfChildCarrier)
    (hbranch : BranchSquare → BranchPoint0001OrSquareTransverse) :
    Q64SingleSlipChildRealization AnchoredRankOneSlipEdge OrderedFirstReturnBoundaryEdge
      QHalfChildCarrier BranchPoint0001OrSquareTransverse := by
  intro hslip
  rcases hstar (hprimitive hslip) (hfaces hslip) with hordered | hbranch'
  · exact Or.inl ⟨hordered, hchild hordered⟩
  · exact Or.inr (hbranch hbranch')

/--
The single-slip child-realization endpoint gives Theorem G once the ordered-child branch and branch-point
branch are routed to the existing provenance/support-decrease exits.
-/
theorem q64_theoremG_of_singleSlipChildRealization
    {FullySkewSplitter DistributedMonodromy PrimitiveHalfCarrierCarry AnchoredRankOneSlipEdge
      OrderedFirstReturnBoundaryEdge QHalfChildCarrier BranchPoint0001OrSquareTransverse
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hmonodromy : FullySkewSplitter → DistributedMonodromy)
    (hcarry : FullySkewSplitter → PrimitiveHalfCarrierCarry)
    (htree :
      Q64TreeGaugeSingleSlipReduction DistributedMonodromy PrimitiveHalfCarrierCarry
        AnchoredRankOneSlipEdge)
    (hchild :
      Q64SingleSlipChildRealization AnchoredRankOneSlipEdge OrderedFirstReturnBoundaryEdge
        QHalfChildCarrier BranchPoint0001OrSquareTransverse)
    (hordered :
      OrderedFirstReturnBoundaryEdge → QHalfChildCarrier →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hbranch :
      BranchPoint0001OrSquareTransverse →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hchild (htree (hmonodromy hskew) (hcarry hskew)) with horderedChild | hbranch'
  · exact hordered horderedChild.1 horderedChild.2
  · exact hbranch hbranch'

/--
Star-to-boundary normality is a still sharper Theorem-G route: the normal branch is admissible, and the
first static-but-not-first-return square is precisely the remaining provenance/cubicality branch.
-/
theorem q64_theoremG_of_starToBoundaryNormality
    {FullySkewSplitter LocallyStarFlatSheetCharacterSeparator BoundaryHistoryCommutation
      OrderedFirstReturnBoundaryEdge StaticNotFirstReturnSquare OrderedBoundaryAdmissible
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hlocalStar : FullySkewSplitter → LocallyStarFlatSheetCharacterSeparator)
    (hcommutes : FullySkewSplitter → BoundaryHistoryCommutation)
    (hnormal :
      Q64StarToBoundaryNormality LocallyStarFlatSheetCharacterSeparator
        BoundaryHistoryCommutation OrderedFirstReturnBoundaryEdge StaticNotFirstReturnSquare)
    (hordered : OrderedFirstReturnBoundaryEdge → OrderedBoundaryAdmissible)
    (hstatic :
      StaticNotFirstReturnSquare →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hnormal (hlocalStar hskew) (hcommutes hskew) with hordered' | hstatic'
  · exact Or.inl (hordered hordered')
  · exact hstatic hstatic'

/--
The boundary-exchange gate analysis routes a static-but-not-first-return square to the already named
local/proper/circuit/branch exits, except for the idempotent boundary-normality atom kept explicit.
-/
theorem q64_staticNotFirstReturnSquare_closed_of_exchangeGate
    {StaticNotFirstReturnSquare ExchangeGateEdge FixedTraceCleanLocal MinimalSquareTransverseBreaker
      ProperChildCarrier PrimitiveCircuit BranchSquare GateParallelSheetCharacterBounce
      IdempotentOneEdgeBoundaryNormalityFailure OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hexpose :
      Q64StaticNotFirstReturnExchangeGate StaticNotFirstReturnSquare ExchangeGateEdge)
    (hprime :
      Q64ExchangeGatePrimeBreakerReduction ExchangeGateEdge FixedTraceCleanLocal
        MinimalSquareTransverseBreaker)
    (hdirty :
      Q64BoundaryExchangeDirtyRowReduction MinimalSquareTransverseBreaker ProperChildCarrier
        PrimitiveCircuit BranchSquare GateParallelSheetCharacterBounce)
    (hbounce :
      Q64GateParallelBounceNormalForm GateParallelSheetCharacterBounce
        IdempotentOneEdgeBoundaryNormalityFailure)
    (hfixed :
      FixedTraceCleanLocal →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hchild :
      ProperChildCarrier →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hcircuit :
      PrimitiveCircuit →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hbranch :
      BranchSquare →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hidempotent :
      IdempotentOneEdgeBoundaryNormalityFailure →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    StaticNotFirstReturnSquare →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hstatic
  rcases hprime (hexpose hstatic) with hclean | hbreaker
  · exact hfixed hclean
  rcases hdirty hbreaker with hproper | hcircuit' | hbranch' | hbounce'
  · exact hchild hproper
  · exact hcircuit hcircuit'
  · exact hbranch hbranch'
  · exact hidempotent (hbounce hbounce')

/--
Star-to-boundary normality plus the exchange-gate reduction gives the q-marker provenance/support
decrease endpoint; the idempotent one-edge atom is the only explicit unresolved branch.
-/
theorem q64_theoremG_of_starToBoundaryNormality_and_exchangeGate
    {FullySkewSplitter LocallyStarFlatSheetCharacterSeparator BoundaryHistoryCommutation
      OrderedFirstReturnBoundaryEdge StaticNotFirstReturnSquare ExchangeGateEdge
      FixedTraceCleanLocal MinimalSquareTransverseBreaker ProperChildCarrier PrimitiveCircuit
      BranchSquare GateParallelSheetCharacterBounce IdempotentOneEdgeBoundaryNormalityFailure
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hlocalStar : FullySkewSplitter → LocallyStarFlatSheetCharacterSeparator)
    (hcommutes : FullySkewSplitter → BoundaryHistoryCommutation)
    (hnormal :
      Q64StarToBoundaryNormality LocallyStarFlatSheetCharacterSeparator
        BoundaryHistoryCommutation OrderedFirstReturnBoundaryEdge StaticNotFirstReturnSquare)
    (hordered : OrderedFirstReturnBoundaryEdge → OrderedBoundaryAdmissible)
    (hexpose :
      Q64StaticNotFirstReturnExchangeGate StaticNotFirstReturnSquare ExchangeGateEdge)
    (hprime :
      Q64ExchangeGatePrimeBreakerReduction ExchangeGateEdge FixedTraceCleanLocal
        MinimalSquareTransverseBreaker)
    (hdirty :
      Q64BoundaryExchangeDirtyRowReduction MinimalSquareTransverseBreaker ProperChildCarrier
        PrimitiveCircuit BranchSquare GateParallelSheetCharacterBounce)
    (hbounce :
      Q64GateParallelBounceNormalForm GateParallelSheetCharacterBounce
        IdempotentOneEdgeBoundaryNormalityFailure)
    (hfixed :
      FixedTraceCleanLocal →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hchild :
      ProperChildCarrier →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hcircuit :
      PrimitiveCircuit →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hbranch :
      BranchSquare →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hidempotent :
      IdempotentOneEdgeBoundaryNormalityFailure →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit :=
  q64_theoremG_of_starToBoundaryNormality hlocalStar hcommutes hnormal hordered
    (q64_staticNotFirstReturnSquare_closed_of_exchangeGate hexpose hprime hdirty hbounce hfixed
      hchild hcircuit hbranch hidempotent)
    hskew

/--
Rank-one boundary-category fullness closes the idempotent one-edge failure once prefix-insertion
fullness is routed; local category axioms alone are not assumed to supply this.
-/
theorem q64_idempotentBoundaryNormality_closed_of_rankOneBoundaryCategoryFullness
    {IdempotentOneEdgeBoundaryNormalityFailure UniqueCentralDeckInvolution
      FirstReturnCategoryMembership PrefixInsertionFullness OrderedBoundaryAdmissible
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hdeck : IdempotentOneEdgeBoundaryNormalityFailure → UniqueCentralDeckInvolution)
    (hfull :
      Q64RankOneBoundaryCategoryFullness UniqueCentralDeckInvolution
        FirstReturnCategoryMembership PrefixInsertionFullness)
    (hfirst : FirstReturnCategoryMembership → OrderedBoundaryAdmissible)
    (hprefix :
      PrefixInsertionFullness →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit) :
    IdempotentOneEdgeBoundaryNormalityFailure →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit := by
  intro hidem
  rcases hfull (hdeck hidem) with hmember | hprefix'
  · exact Or.inl (hfirst hmember)
  · exact hprefix hprefix'

/--
The rank-one boundary-category fullness formulation itself is a Theorem-G endpoint: the first-return
membership branch is admissible and the prefix-insertion branch is kept explicit.
-/
theorem q64_theoremG_of_rankOneBoundaryCategoryFullness
    {FullySkewSplitter UniqueCentralDeckInvolution FirstReturnCategoryMembership
      PrefixInsertionFullness OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hdeck : FullySkewSplitter → UniqueCentralDeckInvolution)
    (hfull :
      Q64RankOneBoundaryCategoryFullness UniqueCentralDeckInvolution
        FirstReturnCategoryMembership PrefixInsertionFullness)
    (hfirst : FirstReturnCategoryMembership → OrderedBoundaryAdmissible)
    (hprefix :
      PrefixInsertionFullness →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hfull (hdeck hskew) with hmember | hprefix'
  · exact Or.inl (hfirst hmember)
  · exact hprefix hprefix'

/--
Root selector fullness gives the q-marker provenance/support-decrease atom directly: initial
first-return boundaries are admissible, and the local/branch alternatives are routed explicitly.
-/
theorem q64_theoremG_of_rootSelectorFullness
    {FullySkewSplitter RealizedAmbientChildCutRow InitialFirstReturnBoundary LocalExit BranchExit
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hrow : FullySkewSplitter → RealizedAmbientChildCutRow)
    (hselector :
      Q64RootSelectorFullness RealizedAmbientChildCutRow InitialFirstReturnBoundary LocalExit
        BranchExit)
    (hboundary : InitialFirstReturnBoundary → OrderedBoundaryAdmissible)
    (hlocal : LocalExit → LocalRegularizingExit)
    (hbranch :
      BranchExit →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hselector (hrow hskew) with hfirst | hlocal' | hbranch'
  · exact Or.inl (hboundary hfirst)
  · exact Or.inr (Or.inr (hlocal hlocal'))
  · exact hbranch hbranch'

/--
Root-edge fullness is the same endpoint after identifying the primitive child-carrier separator with a
realized ambient child-cut row.
-/
theorem q64_rootSelectorFullness_of_rootEdgeFullness
    {RealizedAmbientChildCutRow AmbientSeparatorPrimitiveChildCarrier InitialFirstReturnBoundary
      FirstReturnChildEdge LocalExit BranchExit : Prop}
    (hedge :
      Q64RootEdgeFullness AmbientSeparatorPrimitiveChildCarrier FirstReturnChildEdge LocalExit
        BranchExit)
    (htoCarrier : RealizedAmbientChildCutRow → AmbientSeparatorPrimitiveChildCarrier)
    (hfirst : FirstReturnChildEdge → InitialFirstReturnBoundary) :
    Q64RootSelectorFullness RealizedAmbientChildCutRow InitialFirstReturnBoundary LocalExit
      BranchExit := by
  intro hrow
  rcases hedge (htoCarrier hrow) with hedgeFirst | hlocal | hbranch
  · exact Or.inl (hfirst hedgeFirst)
  · exact Or.inr (Or.inl hlocal)
  · exact Or.inr (Or.inr hbranch)

/--
The memory-free/restart-residue chain reduces anchored prefix eligibility to admitted prefix-local
support, classified local/branch exchange failures, or the residue-zero non-square provenance atom.
-/
theorem q64_rootSelectorFullness_of_memoryFree_restartSaturation
    {RealizedAmbientChildCutRow AnchoredPrefixEligibility PrefixLocalAdmitted HiddenSelectorMemory
      RestartAdmissibility LocalBranchExchangeFailure NonzeroRestartResidueVector
      ClosedFirstNonzeroCoordinate HiddenRestartResidue ResidueZeroPrefixLocalSaturation
      ResidueZeroNonSquareRow InitialFirstReturnBoundary LocalExit BranchExit : Prop}
    (heligible : RealizedAmbientChildCutRow → AnchoredPrefixEligibility)
    (hmemory :
      Q64MemoryFreeSelectorTheorem AnchoredPrefixEligibility PrefixLocalAdmitted
        HiddenSelectorMemory)
    (hrestart :
      Q64RestartMinimalityKillsHiddenMemory HiddenSelectorMemory RestartAdmissibility
        LocalBranchExchangeFailure)
    (hresidue :
      Q64RestartResidueVectorDichotomy RestartAdmissibility NonzeroRestartResidueVector
        ClosedFirstNonzeroCoordinate HiddenRestartResidue)
    (hsaturate :
      Q64AnchoredPrefixProvenanceSaturation HiddenRestartResidue
        ResidueZeroPrefixLocalSaturation ResidueZeroNonSquareRow)
    (hprefix : PrefixLocalAdmitted → InitialFirstReturnBoundary)
    (hlocalBranch : LocalBranchExchangeFailure → LocalExit ∨ BranchExit)
    (hnonzero : NonzeroRestartResidueVector → ClosedFirstNonzeroCoordinate → LocalExit ∨ BranchExit)
    (hresidueZero : ResidueZeroPrefixLocalSaturation → InitialFirstReturnBoundary)
    (hnonsquare : ResidueZeroNonSquareRow → BranchExit) :
    Q64RootSelectorFullness RealizedAmbientChildCutRow InitialFirstReturnBoundary LocalExit
      BranchExit := by
  intro hrow
  rcases hmemory (heligible hrow) with hprefixLocal | hhidden
  · exact Or.inl (hprefix hprefixLocal)
  rcases hrestart hhidden with hadm | hlocalBranch'
  · rcases hresidue hadm with hnonzero' | hhiddenResidue
    · rcases hnonzero hnonzero'.1 hnonzero'.2 with hlocal | hbranch
      · exact Or.inr (Or.inl hlocal)
      · exact Or.inr (Or.inr hbranch)
    · rcases hsaturate hhiddenResidue with hsat | hnonsq
      · exact Or.inl (hresidueZero hsat)
      · exact Or.inr (Or.inr (hnonsquare hnonsq))
  · rcases hlocalBranch hlocalBranch' with hlocal | hbranch
    · exact Or.inr (Or.inl hlocal)
    · exact Or.inr (Or.inr hbranch)

/--
If first-return completeness in `FR^sat` is compatible with the original first-return family, then the
residue-zero non-square row is routed back to the original ordered-boundary support.
-/
theorem q64_theoremG_of_frsatSaturationCompatibility
    {FullySkewSplitter FRSatFirstReturnCompleteSupport OriginalFirstReturnCompleteSupport
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hsupport : FullySkewSplitter → FRSatFirstReturnCompleteSupport)
    (hcompat :
      Q64FRSatSaturationCompatibility FRSatFirstReturnCompleteSupport
        OriginalFirstReturnCompleteSupport)
    (horiginal : OriginalFirstReturnCompleteSupport → OrderedBoundaryAdmissible)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit :=
  Or.inl (horiginal (hcompat (hsupport hskew)))

/-- Intrinsic exchange-completeness supplies the `FR^sat` saturation-compatibility map. -/
theorem q64_frsatSaturationCompatibility_of_intrinsicExchangeCompleteness
    {FourGraphCorners TerminalResidueVector FRSatFirstReturnCompleteSupport
      OriginalFirstReturnCompleteSupport : Prop}
    (haudit :
      Q64IntrinsicExchangeCompletenessAudit FourGraphCorners TerminalResidueVector
        FRSatFirstReturnCompleteSupport OriginalFirstReturnCompleteSupport)
    (hcorners : FourGraphCorners) (hresidue : TerminalResidueVector) :
    Q64FRSatSaturationCompatibility FRSatFirstReturnCompleteSupport
      OriginalFirstReturnCompleteSupport := by
  intro hsat
  exact haudit hcorners hresidue hsat

/-- The saturated `FR^sat` provenance theorem routes immediately to the Theorem-G endpoint. -/
theorem q64_theoremG_of_saturatedProvenanceSupportDecrease
    {FullySkewSplitter PrefixLocalFailure NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary
      ExchangeCompleteSmallerQMarker OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hsat :
      Q64SaturatedProvenanceSupportDecrease FullySkewSplitter PrefixLocalFailure
        NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker)
    (hprefix : PrefixLocalFailure → LocalRegularizingExit)
    (hnonzero : NonzeroFirstTerminalResidue → LocalRegularizingExit)
    (hsmall : ExchangeCompleteSmallerQMarker → CompleteSmallerQMarker)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hsat hskew with hprefix' | hnonzero' | hzero
  · exact Or.inr (Or.inr (hprefix hprefix'))
  · exact Or.inr (Or.inr (hnonzero hnonzero'))
  · exact Or.inr (Or.inl (hsmall hzero.2))

/--
In the canonical saturated convention, the saturated provenance theorem is the Theorem-G atom once the
three saturated branches are routed.
-/
theorem q64_theoremG_in_canonicalSaturatedFirstReturnConvention
    {CanonicalSaturatedConvention FullySkewSplitter PrefixLocalFailure NonzeroFirstTerminalResidue
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker OrderedBoundaryAdmissible
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hcanon :
      Q64CanonicalSaturatedProvenanceTheorem CanonicalSaturatedConvention FullySkewSplitter
        PrefixLocalFailure NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary
        ExchangeCompleteSmallerQMarker)
    (hcanonical : CanonicalSaturatedConvention)
    (hprefix : PrefixLocalFailure → LocalRegularizingExit)
    (hnonzero : NonzeroFirstTerminalResidue → LocalRegularizingExit)
    (hsmall : ExchangeCompleteSmallerQMarker → CompleteSmallerQMarker)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit :=
  q64_theoremG_of_saturatedProvenanceSupportDecrease (hcanon hcanonical) hprefix hnonzero hsmall
    hskew

/--
With the canonical saturated convention already in force, the named canonical-provenance surface is
exactly the saturated provenance/support-decrease statement.  Thus the remaining Lean content at this
endpoint is the support-decrease theorem itself, not another bookkeeping implication.
-/
theorem q64_canonicalSaturatedProvenanceTheorem_iff_saturatedProvenanceSupportDecrease
    {CanonicalSaturatedConvention FullySkewSplitter PrefixLocalFailure NonzeroFirstTerminalResidue
      ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker : Prop}
    (hcanonical : CanonicalSaturatedConvention) :
    Q64CanonicalSaturatedProvenanceTheorem CanonicalSaturatedConvention FullySkewSplitter
        PrefixLocalFailure NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary
        ExchangeCompleteSmallerQMarker ↔
      Q64SaturatedProvenanceSupportDecrease FullySkewSplitter PrefixLocalFailure
        NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker := by
  unfold Q64CanonicalSaturatedProvenanceTheorem
  constructor
  · intro h
    exact h hcanonical
  · intro h _
    exact h

/--
The three conjuncts in `Q64CanonicalSaturatedFirstReturnConvention` do not, by themselves, imply the
saturated support-decrease theorem in the abstract `Prop` interface.  This small countermodel keeps
the missing mathematical input explicit.
-/
theorem q64_canonicalSaturatedFirstReturnConvention_alone_does_not_imply_saturatedProvenanceSupportDecrease :
    ∃ BoundariesChosenInFRSat SupportMinimized LexicographicTieBreak FullySkewSplitter
        PrefixLocalFailure NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary
        ExchangeCompleteSmallerQMarker : Prop,
      Q64CanonicalSaturatedFirstReturnConvention BoundariesChosenInFRSat SupportMinimized
          LexicographicTieBreak ∧
        FullySkewSplitter ∧
          ¬ Q64SaturatedProvenanceSupportDecrease FullySkewSplitter PrefixLocalFailure
            NonzeroFirstTerminalResidue ZeroResidueFRSatBoundary ExchangeCompleteSmallerQMarker := by
  refine ⟨True, True, True, True, False, False, False, False, ?_, trivial, ?_⟩
  · exact ⟨trivial, trivial, trivial⟩
  · intro h
    rcases h trivial with hprefix | hnonzero | hzero
    · exact hprefix
    · exact hnonzero
    · exact hzero.1

/--
The historical and canonical path conventions alone do not imply path-saturation equivalence in the
abstract interface.  The missing mathematical input is the comparison/homotopy theorem, not merely the
choice of two conventions.
-/
theorem q64_pathConventions_alone_do_not_imply_pathSaturationEquivalence :
    ∃ HistoricalPathConvention CanonicalSaturatedConvention TerminalHostDescentUnchanged
        LocalBranchExit : Prop,
      HistoricalPathConvention ∧ CanonicalSaturatedConvention ∧
        ¬ Q64PathSaturationEquivalence HistoricalPathConvention CanonicalSaturatedConvention
          TerminalHostDescentUnchanged LocalBranchExit := by
  refine ⟨True, True, False, False, trivial, trivial, ?_⟩
  intro hequiv
  rcases hequiv trivial trivial with hdescent | hexit
  · exact hdescent
  · exact hexit

/--
Path-saturation equivalence transports the saturated support-decrease proof back to the original
unsaturated Theorem-G statement, with local/branch exits kept explicit.
-/
theorem q64_theoremG_of_pathSaturationEquivalence
    {FullySkewSplitter HistoricalPathConvention CanonicalSaturatedConvention
      TerminalHostDescentUnchanged LocalBranchExit OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hhistorical : FullySkewSplitter → HistoricalPathConvention)
    (hcanonical : FullySkewSplitter → CanonicalSaturatedConvention)
    (hequiv :
      Q64PathSaturationEquivalence HistoricalPathConvention CanonicalSaturatedConvention
        TerminalHostDescentUnchanged LocalBranchExit)
    (hdescent :
      TerminalHostDescentUnchanged →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hexit : LocalBranchExit → LocalRegularizingExit)
    (hskew : FullySkewSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hequiv (hhistorical hskew) (hcanonical hskew) with hsame | hexit'
  · exact hdescent hsame
  · exact Or.inr (Or.inr (hexit hexit'))

/--
The three explicit subclaims in the final q-marker atom: provenance selection, local non-marker exit,
and marker-complete descent.
-/
def Q64QMarkerSupportDecreaseSubclaims
    (ProvenanceSelection LocalNonMarkerExit MarkerCompleteDescent : Prop) : Prop :=
  ProvenanceSelection ∧ LocalNonMarkerExit ∧ MarkerCompleteDescent

/--
The ambient-to-provenance routing gap isolated by the re-audit: an arbitrary prime-shell splitter of
the marker must either route to an ordered first-return/provenance row, or already give a local exit.
-/
def Q64AmbientToProvenanceRouting
    (AmbientSplitter ProvenanceSelection LocalNonMarkerExit : Prop) : Prop :=
  AmbientSplitter → ProvenanceSelection ∨ LocalNonMarkerExit

/--
The ordered first-return choice: provenance selection supplies a row with the repair-path order data
needed by the support-decrease argument.
-/
def Q64OrderedFirstReturnChoice (ProvenanceSelection OrderedFirstReturnRow : Prop) : Prop :=
  ProvenanceSelection → OrderedFirstReturnRow

/--
Row-to-breaker transport: an ordered failed interval row must become a valid breaker/candidate in the
same first-return frame, unless it has already produced a local non-marker exit.
-/
def Q64RowToBreakerTransport
    (OrderedFirstReturnRow ValidBreaker LocalNonMarkerExit : Prop) : Prop :=
  OrderedFirstReturnRow → ValidBreaker ∨ LocalNonMarkerExit

/--
The interval test dichotomy for a valid provenance breaker: it is admissible, or it has a first
failed row that has to be classified.
-/
def Q64IntervalAdmissibilityDichotomy
    (ValidBreaker ProvenanceSplitterAdmissible FirstFailedRow : Prop) : Prop :=
  ValidBreaker → ProvenanceSplitterAdmissible ∨ FirstFailedRow

/--
First-failure classification: after a valid breaker fails an interval test, the first failure is
either marker-internal or belongs to one of the local non-marker catalogues.
-/
def Q64FirstFailureClassification
    (FirstFailedRow MarkerInternalFailure NonMarkerFailure : Prop) : Prop :=
  FirstFailedRow → MarkerInternalFailure ∨ NonMarkerFailure

/-- Non-marker first failures are routed to the closed local catalogues. -/
def Q64LocalNonMarkerExitTheorem (NonMarkerFailure LocalNonMarkerExit : Prop) : Prop :=
  NonMarkerFailure → LocalNonMarkerExit

/--
Marker-complete descent for square-provenance: a marker-internal first failure carries the whole
smaller shared-slack marker of the transported quartet, not just a failed prefix.
-/
def Q64MarkerCompleteDescentTheorem
    (MarkerInternalFailure SmallerCompleteMarker : Prop) : Prop :=
  MarkerInternalFailure → SmallerCompleteMarker

/-- A complete smaller marker package, including strict support decrease. -/
def Q64CompleteSmallerMarker (Marker : ℕ → Prop) (R R' : ℕ) : Prop :=
  Marker R' ∧ 0 < R' ∧ R' < R

/-- A complete smaller q-marker contradicts minimality of the original q-marker. -/
theorem q64_no_completeSmallerMarker_of_minimalQMarker
    {Marker : ℕ → Prop} {R R' : ℕ} (hmin : Q64MinimalQMarker Marker R)
    (hsmall : Q64CompleteSmallerMarker Marker R R') : False :=
  hmin.2 R' hsmall.1 hsmall.2.2

/--
Square-provenance is the strengthened provenance promised in the hard attack on Theorem G: a
selected splitter carries the whole ordered first-return square, so marker-internal failure can be
read as the complete shared-slack marker of the transported quartet.
-/
def Q64SquareProvenanceMarkerCompleteDescent
    (SquareProvenance MarkerInternalFailure CompleteSmallerQMarker : Prop) : Prop :=
  SquareProvenance → MarkerInternalFailure → CompleteSmallerQMarker

/--
Once square-provenance for the selected row is available, the marker-complete descent clause in
Theorem G is exactly the transported low-set update.
-/
theorem q64_markerCompleteDescentTheorem_of_squareProvenance
    {SquareProvenance MarkerInternalFailure CompleteSmallerQMarker : Prop}
    (hsquare : SquareProvenance)
    (hdescent :
      Q64SquareProvenanceMarkerCompleteDescent SquareProvenance MarkerInternalFailure
        CompleteSmallerQMarker) :
    Q64MarkerCompleteDescentTheorem MarkerInternalFailure CompleteSmallerQMarker := by
  intro hinternal
  exact hdescent hsquare hinternal

/--
Wall-order is enough only after marker-completeness has been supplied: then the low-set residue
calculation can be applied to a complete first-return side.
-/
def Q64FirstReturnWallOrderSupportDecrease
    (FirstReturnWallOrder MarkerComplete LowSetResidue ProperFirstReturnSide SupportDecrease : Prop) :
    Prop :=
  FirstReturnWallOrder → MarkerComplete → LowSetResidue → ProperFirstReturnSide → SupportDecrease

/-- The conditional wall-order route exposes marker-completeness as the missing support-decrease input. -/
theorem q64_supportDecrease_of_wallOrder_markerComplete
    {FirstReturnWallOrder MarkerComplete LowSetResidue ProperFirstReturnSide SupportDecrease : Prop}
    (h :
      Q64FirstReturnWallOrderSupportDecrease FirstReturnWallOrder MarkerComplete LowSetResidue
        ProperFirstReturnSide SupportDecrease)
    (horder : FirstReturnWallOrder) (hcomplete : MarkerComplete) (hresidue : LowSetResidue)
    (hproper : ProperFirstReturnSide) :
    SupportDecrease :=
  h horder hcomplete hresidue hproper

/--
Dirty shared-slack absorption, in the form identified by the hard attack: a budget-one reanchor cycle
must either give a completer, coalesce into a local same-trace/false-clone exit, or expose a
square-provenance smaller marker.
-/
def Q64DirtySharedSlackAbsorptionTheorem
    (BudgetOneReanchorCycle Completer SameTraceOrFalseCloneExit
      SquareProvenanceSmallerMarker : Prop) : Prop :=
  BudgetOneReanchorCycle →
    Completer ∨ SameTraceOrFalseCloneExit ∨ SquareProvenanceSmallerMarker

/-- The current hard attack records dirty shared-slack absorption as equivalent to Theorem G. -/
def Q64DirtySharedSlackAbsorptionEquivTheoremG
    (TheoremG DirtySharedSlackAbsorption : Prop) : Prop :=
  TheoremG ↔ DirtySharedSlackAbsorption

/-- Dirty shared-slack absorption closes Theorem G when the audited equivalence is supplied. -/
theorem q64_theoremG_of_dirtySharedSlackAbsorption
    {TheoremG DirtySharedSlackAbsorption : Prop}
    (hequiv : Q64DirtySharedSlackAbsorptionEquivTheoremG TheoremG DirtySharedSlackAbsorption)
    (hdirty : DirtySharedSlackAbsorption) :
    TheoremG :=
  hequiv.mpr hdirty

/-- Theorem G gives dirty shared-slack absorption under the same audited equivalence. -/
theorem q64_dirtySharedSlackAbsorption_of_theoremG
    {TheoremG DirtySharedSlackAbsorption : Prop}
    (hequiv : Q64DirtySharedSlackAbsorptionEquivTheoremG TheoremG DirtySharedSlackAbsorption)
    (hG : TheoremG) :
    DirtySharedSlackAbsorption :=
  hequiv.mp hG

/-- Two-point incidence model used by the audit no-go for provenance selection. -/
def q64NoGoAmbientTrace (_row : Unit) (p : Fin 2) : Bool :=
  decide (p = 0)

/-- In the no-go model, the designated provenance family is constant on the marker. -/
def q64NoGoProvenanceTrace (_row : Unit) (_p : Fin 2) : Bool :=
  false

/-- The ambient family separates the two marker points in the no-go model. -/
theorem q64_noGo_ambientSeparates :
    ∃ row : Unit,
      q64NoGoAmbientTrace row 0 ≠ q64NoGoAmbientTrace row 1 := by
  refine ⟨(), ?_⟩
  decide

/-- No designated provenance row separates any two marker points in the no-go model. -/
theorem q64_noGo_noProvenanceSplitter :
    ¬ ∃ row : Unit, ∃ a b : Fin 2,
      q64NoGoProvenanceTrace row a ≠ q64NoGoProvenanceTrace row b := by
  rintro ⟨row, a, b, hsplit⟩
  simp [q64NoGoProvenanceTrace] at hsplit

/--
Concrete formal version of the proof.md no-go: ambient separation of a marker does not by itself
imply the existence of a provenance splitter.
-/
theorem q64_ambientSeparation_does_not_force_provenanceSelection :
    (∃ row : Unit, q64NoGoAmbientTrace row 0 ≠ q64NoGoAmbientTrace row 1) ∧
      ¬ ∃ row : Unit, ∃ a b : Fin 2,
        q64NoGoProvenanceTrace row a ≠ q64NoGoProvenanceTrace row b := by
  exact ⟨q64_noGo_ambientSeparates, q64_noGo_noProvenanceSplitter⟩

/--
Static residue data are compatible with an exact q-marker: residue coupling can certify
`|R| = 0 mod q`, but it does not make the marker a proper sub-`q` side.
-/
def Q64StaticResidueExactMarkerProfile (q lowDegree highDegree marker : ℕ) : Prop :=
  1 < q ∧ 0 < marker ∧ marker = q ∧ marker % q = 0 ∧
    highDegree % q = (lowDegree + 1) % q

/-- The `q=4` exact-marker profile realizes the static residue no-go from `proof.md`. -/
theorem q64_staticResidue_exactMarkerProfile_q4 :
    Q64StaticResidueExactMarkerProfile 4 1 2 4 ∧ ¬ 4 < 4 := by
  simp [Q64StaticResidueExactMarkerProfile]

/--
The detailed provenance-routing chain implies the sharpened q-marker support-decrease atom.
This is the Lean-facing dependency skeleton of provenance selection, ordered first-return choice,
row-to-breaker transport, non-marker local exits, and marker-complete descent.
-/
theorem q64_provenanceSupportDecrease_of_routing
    {AmbientSplitter ProvenanceSelection OrderedFirstReturnRow ValidBreaker
      ProvenanceSplitterAdmissible FirstFailedRow MarkerInternalFailure NonMarkerFailure
      SmallerCompleteMarker LocalNonMarkerExit : Prop}
    (hroute :
      Q64AmbientToProvenanceRouting AmbientSplitter ProvenanceSelection LocalNonMarkerExit)
    (hchoice : Q64OrderedFirstReturnChoice ProvenanceSelection OrderedFirstReturnRow)
    (htransport :
      Q64RowToBreakerTransport OrderedFirstReturnRow ValidBreaker LocalNonMarkerExit)
    (hadm :
      Q64IntervalAdmissibilityDichotomy ValidBreaker ProvenanceSplitterAdmissible FirstFailedRow)
    (hclass :
      Q64FirstFailureClassification FirstFailedRow MarkerInternalFailure NonMarkerFailure)
    (hnonmarker : Q64LocalNonMarkerExitTheorem NonMarkerFailure LocalNonMarkerExit)
    (hdescent : Q64MarkerCompleteDescentTheorem MarkerInternalFailure SmallerCompleteMarker)
    (hsplit : AmbientSplitter) :
    Q64QMarkerProvenanceSupportDecrease
      ProvenanceSplitterAdmissible SmallerCompleteMarker LocalNonMarkerExit := by
  rcases hroute hsplit with hsel | hlocal
  · rcases htransport (hchoice hsel) with hbreaker | hlocal
    · rcases hadm hbreaker with hadmissible | hfailed
      · exact Or.inl hadmissible
      · rcases hclass hfailed with hinternal | hnon
        · exact Or.inr (Or.inl (hdescent hinternal))
        · exact Or.inr (Or.inr (hnonmarker hnon))
    · exact Or.inr (Or.inr hlocal)
  · exact Or.inr (Or.inr hlocal)

/--
`proof.md` Theorem G as a one-splitter implication: an ambient high-error splitter, routed through
the provenance/first-return chain, yields an ordered-boundary admissible splitter, a complete smaller
marker, or a local non-marker exit.
-/
theorem q64_theoremG_of_provenanceRouting
    {AmbientHighErrorSplitter ProvenanceSelection OrderedFirstReturnRow ValidBreaker
      OrderedBoundaryAdmissible FirstFailedRow MarkerInternalFailure NonMarkerFailure
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hroute :
      Q64AmbientToProvenanceRouting AmbientHighErrorSplitter ProvenanceSelection
        LocalRegularizingExit)
    (hchoice : Q64OrderedFirstReturnChoice ProvenanceSelection OrderedFirstReturnRow)
    (htransport :
      Q64RowToBreakerTransport OrderedFirstReturnRow ValidBreaker LocalRegularizingExit)
    (hadm :
      Q64IntervalAdmissibilityDichotomy ValidBreaker OrderedBoundaryAdmissible
        FirstFailedRow)
    (hclass :
      Q64FirstFailureClassification FirstFailedRow MarkerInternalFailure NonMarkerFailure)
    (hnonmarker : Q64LocalNonMarkerExitTheorem NonMarkerFailure LocalRegularizingExit)
    (hdescent : Q64MarkerCompleteDescentTheorem MarkerInternalFailure CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  exact
    q64_provenanceSupportDecrease_of_routing hroute hchoice htransport hadm hclass
      hnonmarker hdescent hsplit

/--
Theorem G after the product-firewall transport trap has reached square-provenance: the ordinary
marker-complete descent premise is supplied by the square-provenance low-set update.
-/
theorem q64_theoremG_of_squareProvenanceRouting
    {AmbientHighErrorSplitter ProvenanceSelection OrderedFirstReturnRow ValidBreaker
      OrderedBoundaryAdmissible FirstFailedRow MarkerInternalFailure NonMarkerFailure
      SquareProvenance CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hroute :
      Q64AmbientToProvenanceRouting AmbientHighErrorSplitter ProvenanceSelection
        LocalRegularizingExit)
    (hchoice : Q64OrderedFirstReturnChoice ProvenanceSelection OrderedFirstReturnRow)
    (htransport :
      Q64RowToBreakerTransport OrderedFirstReturnRow ValidBreaker LocalRegularizingExit)
    (hadm :
      Q64IntervalAdmissibilityDichotomy ValidBreaker OrderedBoundaryAdmissible
        FirstFailedRow)
    (hclass :
      Q64FirstFailureClassification FirstFailedRow MarkerInternalFailure NonMarkerFailure)
    (hnonmarker : Q64LocalNonMarkerExitTheorem NonMarkerFailure LocalRegularizingExit)
    (hsquare : SquareProvenance)
    (hsquareDescent :
      Q64SquareProvenanceMarkerCompleteDescent SquareProvenance MarkerInternalFailure
        CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  exact
    q64_theoremG_of_provenanceRouting hroute hchoice htransport hadm hclass hnonmarker
      (q64_markerCompleteDescentTheorem_of_squareProvenance hsquare hsquareDescent)
      hsplit

/--
Final proof.md normal form for Gap Theorem G: after fixed-trace and clean exits are removed, a minimal
transverse breaker must pass the interval tests, coalesce into a fixed frame, strictly reduce support,
or already be a local regularizing exit.
-/
def Q64MinimalTransverseBreakerAdmissibility
    (MinimalTransverseBreaker OrderedBoundaryAdmissible FixedFrameCoalescence
      StrictSupportDecrease LocalRegularizingExit : Prop) : Prop :=
  MinimalTransverseBreaker →
    OrderedBoundaryAdmissible ∨ FixedFrameCoalescence ∨ StrictSupportDecrease ∨
      LocalRegularizingExit

/--
The minimal transverse-breaker normal form is exactly strong enough to supply Theorem G's
support-decrease alternative.
-/
theorem q64_theoremG_of_minimalTransverseBreakerAdmissibility
    {AmbientHighErrorSplitter MinimalTransverseBreaker OrderedBoundaryAdmissible
      FixedFrameCoalescence StrictSupportDecrease CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hminimal : AmbientHighErrorSplitter → MinimalTransverseBreaker)
    (hadm :
      Q64MinimalTransverseBreakerAdmissibility MinimalTransverseBreaker
        OrderedBoundaryAdmissible FixedFrameCoalescence StrictSupportDecrease
        LocalRegularizingExit)
    (hcoalesce : FixedFrameCoalescence → LocalRegularizingExit)
    (hdecrease : StrictSupportDecrease → CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hadm (hminimal hsplit) with hboundary | hcoal | hdecrease' | hlocal
  · exact Or.inl hboundary
  · exact Or.inr (Or.inr (hcoalesce hcoal))
  · exact Or.inr (Or.inl (hdecrease hdecrease'))
  · exact Or.inr (Or.inr hlocal)

/--
Admissible-module primeness form of the same gap: an ambient splitter of an admissible module must
become admissible after local marking, strictly reduce the admissible module, or exit locally.
-/
def Q64AdmissibleModulePrimeness
    (AmbientSplitter AdmissibleAfterMarking StrictSmallerAdmissibleModule LocalExit : Prop) :
    Prop :=
  AmbientSplitter → AdmissibleAfterMarking ∨ StrictSmallerAdmissibleModule ∨ LocalExit

/--
Primitive antichain realization is the large-marker form of Theorem G: a primitive first-wall
zero-sum antichain must realize a proper zero-sum subcarrier, produce a binary-circuit-elimination
row, or exit locally.
-/
def Q64PrimitiveAntichainRealization
    (PrimitiveAntichain ProperRealizedZeroSumSubcarrier BinaryCircuitEliminationRow LocalExit : Prop) :
    Prop :=
  PrimitiveAntichain →
    ProperRealizedZeroSumSubcarrier ∨ BinaryCircuitEliminationRow ∨ LocalExit

/--
Final saturated separator-bag endpoint: over one active pair, an ambient breaker of the sign-coherent
q-divisible separator bag must promote to a first-return side, give a complete smaller bag, or exit
locally.
-/
def Q64SignCoherentSeparatorBagEndpoint
    (SeparatorBag AmbientBreaker FirstReturnSide CompleteSmallerBag LocalExit : Prop) : Prop :=
  SeparatorBag → AmbientBreaker → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit

/--
Exact-marker packet-firewall normal form: every finite packet-quotient selection reduces to a protected
clique module, a compensator-packet module, or the ambient high-error breaker whose promotion is exactly
Theorem G.
-/
def Q64ExactMarkerPacketFirewallNormalForm
    (FinitePacketQuotientSelection ProtectedCliqueModule CompensatorPacketModule
      AmbientHighErrorBreaker : Prop) : Prop :=
  FinitePacketQuotientSelection →
    ProtectedCliqueModule ∨ CompensatorPacketModule ∨ AmbientHighErrorBreaker

/--
Full propositional wiring of the latest separator-bag normal-form analysis.  Once every earlier branch
is routed to a first-return side, a complete smaller bag, or a local exit, it remains only to close the
defect-switching fully skew square.
-/
theorem q64_signCoherentSeparatorBagEndpoint_of_defectSwitchingClosure
    {SeparatorBag AmbientBreaker ConstantOnPair OppositeSign LocalOrCommonPackage
      SameSignSeparatorOutsidePackage MinimumSideBreaker SingletonSidePromotionGap
      CrossingPrimitiveCircuit LocalDeparture MinimumSideContradiction PrimitiveCircuit
      HighErrorSameSignIsolatorLoop SameTraceTwinCoalescence SquareTransverseBreaker
      SingleHighErrorIsolatorSelfLoop PureSameDefectTokenLoopClosed DefectSwitchingFullySkewSquare
      FirstReturnSide CompleteSmallerBag LocalExit : Prop}
    (hnorm :
      Q64BreakerSignNormalization AmbientBreaker ConstantOnPair OppositeSign LocalOrCommonPackage
        SameSignSeparatorOutsidePackage)
    (hconst : ConstantOnPair → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hopp : OppositeSign → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hlocalCommon : LocalOrCommonPackage → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hsameToMin : SameSignSeparatorOutsidePackage → MinimumSideBreaker)
    (hmin :
      Q64MinimumSideBreakerNormalForm MinimumSideBreaker SingletonSidePromotionGap
        CrossingPrimitiveCircuit)
    (hcross : CrossingPrimitiveCircuit → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hsingle :
      Q64SingletonSideIterationNormalForm SingletonSidePromotionGap LocalDeparture
        MinimumSideContradiction PrimitiveCircuit HighErrorSameSignIsolatorLoop)
    (hdepart : LocalDeparture → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hcontradict : MinimumSideContradiction → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hprimitive : PrimitiveCircuit → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hiso :
      Q64IsolatorLoopQuotientNormalForm HighErrorSameSignIsolatorLoop SameTraceTwinCoalescence
        SquareTransverseBreaker SingleHighErrorIsolatorSelfLoop)
    (hcoalesce : SameTraceTwinCoalescence → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hsquare : SquareTransverseBreaker → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hself :
      Q64IsolatorSelfLoopToDefectSwitchingSquare SingleHighErrorIsolatorSelfLoop
        PureSameDefectTokenLoopClosed DefectSwitchingFullySkewSquare)
    (hpure : PureSameDefectTokenLoopClosed → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit)
    (hdefect :
      DefectSwitchingFullySkewSquare → FirstReturnSide ∨ CompleteSmallerBag ∨ LocalExit) :
    Q64SignCoherentSeparatorBagEndpoint SeparatorBag AmbientBreaker FirstReturnSide
      CompleteSmallerBag LocalExit := by
  intro _ hbreaker
  rcases hnorm hbreaker with hconstant | hopposite | hlocal | hsame
  · exact hconst hconstant
  · exact hopp hopposite
  · exact hlocalCommon hlocal
  rcases hmin (hsameToMin hsame) with hsingleton | hcrossing
  · rcases hsingle hsingleton with hdeparture | hminimum | hprim | hisolator
    · exact hdepart hdeparture
    · exact hcontradict hminimum
    · exact hprimitive hprim
    rcases hiso hisolator with htwin | hsq | hselfloop
    · exact hcoalesce htwin
    · exact hsquare hsq
    rcases hself hselfloop with hpureLoop | hskew
    · exact hpure hpureLoop
    · exact hdefect hskew
  · exact hcross hcrossing

/-- Admissible-module primeness supplies the q-marker support-decrease alternatives. -/
theorem q64_theoremG_of_admissibleModulePrimeness
    {AmbientHighErrorSplitter OrderedBoundaryAdmissible StrictSmallerAdmissibleModule
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hprime :
      Q64AdmissibleModulePrimeness AmbientHighErrorSplitter OrderedBoundaryAdmissible
        StrictSmallerAdmissibleModule LocalRegularizingExit)
    (hsmaller : StrictSmallerAdmissibleModule → CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hprime hsplit with hadm | hsmall | hlocal
  · exact Or.inl hadm
  · exact Or.inr (Or.inl (hsmaller hsmall))
  · exact Or.inr (Or.inr hlocal)

/-- Primitive antichain realization is another direct route to Theorem G's three alternatives. -/
theorem q64_theoremG_of_primitiveAntichainRealization
    {AmbientHighErrorSplitter PrimitiveAntichain ProperRealizedZeroSumSubcarrier
      BinaryCircuitEliminationRow OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hrealize :
      Q64PrimitiveAntichainRealization PrimitiveAntichain ProperRealizedZeroSumSubcarrier
        BinaryCircuitEliminationRow LocalRegularizingExit)
    (hskewToAntichain : AmbientHighErrorSplitter → PrimitiveAntichain)
    (hproper : ProperRealizedZeroSumSubcarrier → CompleteSmallerQMarker)
    (hbinary : BinaryCircuitEliminationRow → OrderedBoundaryAdmissible)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hrealize (hskewToAntichain hsplit) with hsub | hbin | hlocal
  · exact Or.inr (Or.inl (hproper hsub))
  · exact Or.inl (hbinary hbin)
  · exact Or.inr (Or.inr hlocal)

/-- The sign-coherent separator-bag endpoint is exactly a Theorem-G support-decrease route. -/
theorem q64_theoremG_of_signCoherentSeparatorBagEndpoint
    {AmbientHighErrorSplitter SeparatorBag AmbientBreaker FirstReturnSide CompleteSmallerBag
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hendpoint :
      Q64SignCoherentSeparatorBagEndpoint SeparatorBag AmbientBreaker FirstReturnSide
        CompleteSmallerBag LocalRegularizingExit)
    (hbag : AmbientHighErrorSplitter → SeparatorBag)
    (hbreaker : AmbientHighErrorSplitter → AmbientBreaker)
    (hside : FirstReturnSide → OrderedBoundaryAdmissible)
    (hsmall : CompleteSmallerBag → CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hendpoint (hbag hsplit) (hbreaker hsplit) with hfirst | hsmaller | hlocal
  · exact Or.inl (hside hfirst)
  · exact Or.inr (Or.inl (hsmall hsmaller))
  · exact Or.inr (Or.inr hlocal)

/--
The exact-marker packet-firewall normal form is not a new unconditional proof: the module branches must
close, and the ambient-breaker branch is precisely the Theorem-G promotion step.
-/
theorem q64_theoremG_of_exactMarkerPacketFirewallNormalForm
    {AmbientHighErrorSplitter FinitePacketQuotientSelection ProtectedCliqueModule
      CompensatorPacketModule AmbientHighErrorBreaker OrderedBoundaryAdmissible
      CompleteSmallerQMarker LocalRegularizingExit : Prop}
    (hnormal :
      Q64ExactMarkerPacketFirewallNormalForm FinitePacketQuotientSelection ProtectedCliqueModule
        CompensatorPacketModule AmbientHighErrorBreaker)
    (hselect : AmbientHighErrorSplitter → FinitePacketQuotientSelection)
    (hclique : ProtectedCliqueModule → CompleteSmallerQMarker ∨ LocalRegularizingExit)
    (hcompensator : CompensatorPacketModule → CompleteSmallerQMarker ∨ LocalRegularizingExit)
    (hbreaker :
      AmbientHighErrorBreaker →
        Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
          LocalRegularizingExit)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hnormal (hselect hsplit) with hprotected | hcomp | hambient
  · rcases hclique hprotected with hsmall | hlocal
    · exact Or.inr (Or.inl hsmall)
    · exact Or.inr (Or.inr hlocal)
  · rcases hcompensator hcomp with hsmall | hlocal
    · exact Or.inr (Or.inl hsmall)
    · exact Or.inr (Or.inr hlocal)
  · exact hbreaker hambient

/--
Once admissible provenance splitters and local non-marker exits are closed, and complete smaller
markers give proper submarkers, provenance/support-decrease yields carrier/marker coupling.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_provenanceSupportDecrease
    {FullySkewSplitter ProvenanceSplitterAdmissible SmallerCompleteMarker LocalNonMarkerExit
      ProperSubmarker PrimeModuleExit ClosedLocalExit : Prop}
    (hprov :
      FullySkewSplitter →
        Q64QMarkerProvenanceSupportDecrease
          ProvenanceSplitterAdmissible SmallerCompleteMarker LocalNonMarkerExit)
    (hadmissible : ProvenanceSplitterAdmissible → ClosedLocalExit)
    (hsmaller : SmallerCompleteMarker → ProperSubmarker)
    (hlocal : LocalNonMarkerExit → ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  intro hskew
  rcases hprov hskew with hadm | hsmall | hloc
  · exact Or.inr (Or.inr (hadmissible hadm))
  · exact Or.inl (hsmaller hsmall)
  · exact Or.inr (Or.inr (hlocal hloc))

/--
Compact package for the six completed `FR^sat` proof-md branch/closure maps: prefix and nonzero
branches close locally, completed support gives a smaller q-marker, and admissible/smaller/local exits
route to the final closed endpoint.
-/
structure Q64CompletedFRSatBranchClosureMaps {Row Packet : Type*}
    (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    (OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit ProperSubmarker
      ClosedLocalExit : Prop) : Prop where
  hprefix : Q64FRSatPrefixLocalFailure C.completeSupports.saturate r → LocalRegularizingExit
  hnonzero :
    Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r → LocalRegularizingExit
  hsmall : Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r →
    CompleteSmallerQMarker
  hadmissible : OrderedBoundaryAdmissible → ClosedLocalExit
  hsmaller : CompleteSmallerQMarker → ProperSubmarker
  hlocal : LocalRegularizingExit → ClosedLocalExit

/--
Structural instance of the completed `FR^sat` branch/closure maps.  It names the three routed
outcomes by the actual completed branch events: prefix/nonzero rows are local exits, and
exchange-complete support is the smaller-marker branch.  This removes any extra routing input when the
final audit is stated directly over the completed saturated branch predicates.
-/
theorem q64_completedFRSatBranchClosureMaps_structural {Row Packet : Type*}
    (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row) :
    Q64CompletedFRSatBranchClosureMaps C r False
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
        Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
        Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r) where
  hprefix := Or.inl
  hnonzero := Or.inr
  hsmall := id
  hadmissible := False.elim
  hsmaller := id
  hlocal := id

/--
The six branch/closure maps for completed `FR^sat` are the only external routing input needed to
promote the structural saturated provenance theorem to q-marker carrier/marker coupling.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_completedRawFRSatSaturation
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    {OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit ProperSubmarker
      PrimeModuleExit ClosedLocalExit : Prop}
    (hprefix : Q64FRSatPrefixLocalFailure C.completeSupports.saturate r → LocalRegularizingExit)
    (hnonzero : Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r →
      LocalRegularizingExit)
    (hsmall : Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r →
      CompleteSmallerQMarker)
    (hadmissible : OrderedBoundaryAdmissible → ClosedLocalExit)
    (hsmaller : CompleteSmallerQMarker → ProperSubmarker)
    (hlocal : LocalRegularizingExit → ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling (C.completeSupports.saturate.splitter r) ProperSubmarker
      PrimeModuleExit ClosedLocalExit := by
  exact
    q64_qMarkerCarrierMarkerCoupling_of_provenanceSupportDecrease
      (fun hskew =>
        q64_theoremG_of_saturatedProvenanceSupportDecrease
           (q64_saturatedProvenanceSupportDecrease_of_completedRawFRSatSaturation C r)
           hprefix hnonzero hsmall hskew)
      hadmissible hsmaller hlocal

/--
Packaged form of `q64_qMarkerCarrierMarkerCoupling_of_completedRawFRSatSaturation`: all six
remaining proof-md saturated branch/closure maps are carried by one compact certificate.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_completedRawFRSatSaturation_maps
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    {OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit ProperSubmarker
      PrimeModuleExit ClosedLocalExit : Prop}
    (hmaps :
      Q64CompletedFRSatBranchClosureMaps C r OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit ProperSubmarker ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling (C.completeSupports.saturate.splitter r) ProperSubmarker
      PrimeModuleExit ClosedLocalExit := by
  exact
    q64_qMarkerCarrierMarkerCoupling_of_completedRawFRSatSaturation C r
      hmaps.hprefix hmaps.hnonzero hmaps.hsmall hmaps.hadmissible hmaps.hsmaller
      hmaps.hlocal

/--
Proof-md-facing q-marker exclusion data for the saturated `FR^sat` route.  A q-marker first exits by
one of the proved local closures, or it reaches the fully-skew endpoint; in that endpoint the completed
`FR^sat` branch maps route prefix/nonzero/complete-smaller cases to the three terminal exits.
-/
structure Q64SaturatedQMarkerExclusionData {Row Packet : Type*}
    (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    (QMarker FullySkewSplitter OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop) :
    Prop where
  qMarkerLocalClosuresOrFullySkew :
    QMarker → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ FullySkewSplitter
  fullySkewToCompletedFRSatSplitter :
    FullySkewSplitter → C.completeSupports.saturate.splitter r
  completedBranchClosureMaps :
    Q64CompletedFRSatBranchClosureMaps C r OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit ProperSubmarker ClosedLocalExit

/-- Package saturated q-marker exclusion data from its local/skew dichotomy, the fully-skew
transport into the completed `FR^sat` splitter, and a bundled branch-closure map certificate. -/
theorem q64_saturatedQMarkerExclusionData_of_completedBranchClosureMaps
    {Row Packet : Type*} {C : Q64FRSatRawExchangeComplex Row Packet} {r : Row}
    {QMarker FullySkewSplitter OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop}
    (hlocalOrSkew :
      QMarker → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ FullySkewSplitter)
    (hskew : FullySkewSplitter → C.completeSupports.saturate.splitter r)
    (hmaps :
      Q64CompletedFRSatBranchClosureMaps C r OrderedBoundaryAdmissible CompleteSmallerQMarker
        LocalRegularizingExit ProperSubmarker ClosedLocalExit) :
    Q64SaturatedQMarkerExclusionData C r QMarker FullySkewSplitter
      OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet where
  qMarkerLocalClosuresOrFullySkew := hlocalOrSkew
  fullySkewToCompletedFRSatSplitter := hskew
  completedBranchClosureMaps := hmaps

/-- Structural saturated q-marker exclusion data: the completed branch maps are the canonical
`FR^sat` prefix/nonzero and exchange-complete exits, so no external branch-map certificate remains. -/
theorem q64_saturatedQMarkerExclusionData_structural
    {Row Packet : Type*} (C : Q64FRSatRawExchangeComplex Row Packet) (r : Row)
    {QMarker FullySkewSplitter PrimeModuleExit RegularQSet : Prop}
    (hlocalOrSkew :
      QMarker →
        Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r ∨
        PrimeModuleExit ∨
        (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
          Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r) ∨
        FullySkewSplitter)
    (hskew : FullySkewSplitter → C.completeSupports.saturate.splitter r) :
    Q64SaturatedQMarkerExclusionData C r QMarker FullySkewSplitter False
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
        Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      PrimeModuleExit
      (Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
        Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      RegularQSet := by
  exact
    q64_saturatedQMarkerExclusionData_of_completedBranchClosureMaps
      (C := C) (r := r)
      (OrderedBoundaryAdmissible := False)
      (CompleteSmallerQMarker :=
        Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      (LocalRegularizingExit :=
        Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
          Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (ProperSubmarker :=
        Q64FRSatExchangeCompleteSmallerQMarker C.completeSupports.saturate r)
      (PrimeModuleExit := PrimeModuleExit)
      (ClosedLocalExit :=
        Q64FRSatPrefixLocalFailure C.completeSupports.saturate r ∨
          Q64FRSatNonzeroFirstTerminalResidue C.completeSupports.saturate r)
      (RegularQSet := RegularQSet)
      hlocalOrSkew hskew (q64_completedFRSatBranchClosureMaps_structural C r)

/--
The saturated q-marker exclusion package supplies the four-exit carrier/marker coupling used by the
terminal dyadic theorem.  The `RegularQSet` exit remains available for compatibility with the Section 9
API, but the saturated `FR^sat` branch maps already route fully-skew survivors to the other exits.
-/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_saturatedQMarkerExclusionData
    {Row Packet : Type*} {C : Q64FRSatRawExchangeComplex Row Packet} {r : Row}
    {QMarker FullySkewSplitter OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet : Prop}
    (hdata :
      Q64SaturatedQMarkerExclusionData C r QMarker FullySkewSplitter
        OrderedBoundaryAdmissible CompleteSmallerQMarker LocalRegularizingExit ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet QMarker ProperSubmarker PrimeModuleExit
      ClosedLocalExit RegularQSet := by
  intro hmarker
  rcases hdata.qMarkerLocalClosuresOrFullySkew hmarker with hsub | hmodule | hlocal | hskew
  · exact Or.inl hsub
  · exact Or.inr (Or.inl hmodule)
  · exact Or.inr (Or.inr (Or.inl hlocal))
  ·
    have hcoupling :
        Q64QMarkerCarrierMarkerCoupling (C.completeSupports.saturate.splitter r)
          ProperSubmarker PrimeModuleExit ClosedLocalExit :=
      q64_qMarkerCarrierMarkerCoupling_of_completedRawFRSatSaturation_maps C r
        hdata.completedBranchClosureMaps
    rcases hcoupling (hdata.fullySkewToCompletedFRSatSplitter hskew) with
      hsub' | hmodule' | hlocal'
    · exact Or.inl hsub'
    · exact Or.inr (Or.inl hmodule')
    · exact Or.inr (Or.inr (Or.inl hlocal'))

/--
If the detailed routing chain is available in the fully skew branch, then the older carrier/marker
coupling endpoint follows from the three closure maps.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_routing
    {FullySkewSplitter ProvenanceSelection OrderedFirstReturnRow ValidBreaker
      ProvenanceSplitterAdmissible FirstFailedRow MarkerInternalFailure NonMarkerFailure
      SmallerCompleteMarker LocalNonMarkerExit ProperSubmarker PrimeModuleExit
      ClosedLocalExit : Prop}
    (hroute :
      Q64AmbientToProvenanceRouting FullySkewSplitter ProvenanceSelection LocalNonMarkerExit)
    (hchoice : Q64OrderedFirstReturnChoice ProvenanceSelection OrderedFirstReturnRow)
    (htransport :
      Q64RowToBreakerTransport OrderedFirstReturnRow ValidBreaker LocalNonMarkerExit)
    (hadm :
      Q64IntervalAdmissibilityDichotomy ValidBreaker ProvenanceSplitterAdmissible FirstFailedRow)
    (hclass :
      Q64FirstFailureClassification FirstFailedRow MarkerInternalFailure NonMarkerFailure)
    (hnonmarker : Q64LocalNonMarkerExitTheorem NonMarkerFailure LocalNonMarkerExit)
    (hdescent : Q64MarkerCompleteDescentTheorem MarkerInternalFailure SmallerCompleteMarker)
    (hadmissible : ProvenanceSplitterAdmissible → ClosedLocalExit)
    (hsmaller : SmallerCompleteMarker → ProperSubmarker)
    (hlocal : LocalNonMarkerExit → ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  refine
    q64_qMarkerCarrierMarkerCoupling_of_provenanceSupportDecrease
      (hadmissible := hadmissible) (hsmaller := hsmaller) (hlocal := hlocal) ?_
  intro hskew
  exact
    q64_provenanceSupportDecrease_of_routing hroute hchoice htransport hadm hclass
      hnonmarker hdescent hskew

/--
The ordered-prefix arithmetic promised by the large-marker audit: a positive marker whose size is
divisible by `q` and strictly below `2q` has exact size `q`.
-/
theorem q64_positive_divisible_marker_lt_two_mul_eq
    {q marker : ℕ} (_hq : 0 < q) (hpos : 0 < marker)
    (hmod : marker % q = 0) (hlt : marker < 2 * q) : marker = q := by
  rcases (Nat.dvd_iff_mod_eq_zero.mpr hmod) with ⟨m, rfl⟩
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    simp [hm0] at hpos
  have hmlt : m < 2 := by
    by_contra hm2not
    have hm2 : 2 ≤ m := le_of_not_gt hm2not
    have hge : 2 * q ≤ m * q := Nat.mul_le_mul_right q hm2
    have hlt' : m * q < 2 * q := by simpa [Nat.mul_comm] using hlt
    exact not_lt_of_ge hge hlt'
  have hm : m = 1 := by omega
  simp [hm]

/-- If two internal degrees are both below `q`, congruence modulo `q` is actual equality. -/
theorem q64_degree_eq_of_mod_eq_of_lt_q
    {q a b : ℕ} (ha : a < q) (hb : b < q) (hmod : a % q = b % q) : a = b := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  exact hmod

/--
Exact-size marker regularity layer: once every internal marker degree is below `q` and congruent
modulo `q`, the marker is internally regular.
-/
def Q64ExactMarkerInternalDegreeCongruence
    (q : ℕ) (R : Finset U) (degree : U → ℕ) : Prop :=
  R.card = q ∧ (∀ r ∈ R, degree r < q) ∧
    ∀ r ∈ R, ∀ s ∈ R, degree r % q = degree s % q

omit [Fintype U] [DecidableEq U] in
/-- The exact-size state-internal splitter argument may use residues only after exact size is known. -/
theorem q64_exactMarker_internalRegular_of_degreeCongruence
    {q : ℕ} {R : Finset U} {degree : U → ℕ}
    (h : Q64ExactMarkerInternalDegreeCongruence q R degree) :
    ∀ ⦃r s : U⦄, r ∈ R → s ∈ R → degree r = degree s := by
  intro r s hr hs
  exact q64_degree_eq_of_mod_eq_of_lt_q (h.2.1 r hr) (h.2.1 s hs) (h.2.2 r hr s hs)

/--
Frozen large-marker closure: a same-trace marker whose outside rows are constant is closed by a
same-trace `P₃`/roof template, by cluster extraction, or by an induced regular `q`-set.
-/
def Q64FrozenLargeMarkerClosure
    (FrozenSameTraceMarker SameTraceP3Template ClusterExtraction RegularQSet : Prop) : Prop :=
  FrozenSameTraceMarker → SameTraceP3Template ∨ ClusterExtraction ∨ RegularQSet

/--
The simultaneous-wall no-q-jump theorem isolated by the audit: a wall block jumping across `q`
either already contains a regular `q`-set, exits locally, exposes a smaller complete marker, or leaves
the explicit zero-sum packet atom.
-/
def Q64LargeMarkerNoQJumpTheorem
    (SimultaneousWallBlock RegularQSet LocalExit SmallerCompleteMarker ZeroSumPacketAtom : Prop) :
    Prop :=
  SimultaneousWallBlock →
    RegularQSet ∨ LocalExit ∨ SmallerCompleteMarker ∨ ZeroSumPacketAtom

/--
First-return packet-primality packaging: a packet quotient from a genuine q-marker atom is prime
inside the first-return package, or every ambient quotient-module breaker transports to a
packet-refining admissible row or a local exit.
-/
def Q64FirstReturnPacketPrimality
    (GenuineQMarkerPacketAtom FirstReturnPackagePrime PacketRefiningAdmissibleRow LocalExit : Prop) :
    Prop :=
  GenuineQMarkerPacketAtom →
    FirstReturnPackagePrime ∨ PacketRefiningAdmissibleRow ∨ LocalExit

/--
First-return packet-primality supplies the q-marker support-decrease atom once the three packet exits
are identified with the Theorem-G exits.
-/
theorem q64_theoremG_of_firstReturnPacketPrimality
    {AmbientHighErrorSplitter GenuineQMarkerPacketAtom FirstReturnPackagePrime
      PacketRefiningAdmissibleRow OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit : Prop}
    (hpacket :
      Q64FirstReturnPacketPrimality GenuineQMarkerPacketAtom FirstReturnPackagePrime
        PacketRefiningAdmissibleRow LocalRegularizingExit)
    (hskewToPacket : AmbientHighErrorSplitter → GenuineQMarkerPacketAtom)
    (hprime : FirstReturnPackagePrime → OrderedBoundaryAdmissible)
    (hrefine : PacketRefiningAdmissibleRow → CompleteSmallerQMarker)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryAdmissible CompleteSmallerQMarker
      LocalRegularizingExit := by
  rcases hpacket (hskewToPacket hsplit) with hpkg | href | hlocal
  · exact Or.inl (hprime hpkg)
  · exact Or.inr (Or.inl (hrefine href))
  · exact Or.inr (Or.inr hlocal)

/-- Admissible-module primeness and first-return packet-primality are interchangeable endpoint forms. -/
def Q64AdmissibleModulePacketPrimalityEquivalence
    (AdmissibleModulePrimeness FirstReturnPacketPrimality : Prop) : Prop :=
  AdmissibleModulePrimeness ↔ FirstReturnPacketPrimality

/--
Minimal failure of admissible-module primeness has the two-splitter crossing normal form: the ambient
split and the first failed ordered row cross both sides, and no quadrant is first-return complete.
-/
def Q64TwoSplitterCrossingNormalForm
    (MinimalPrimenessFailure AmbientCrossesOrdered OrderedCrossesAmbient NoCompleteQuadrant : Prop) :
    Prop :=
  MinimalPrimenessFailure →
    AmbientCrossesOrdered ∧ OrderedCrossesAmbient ∧ NoCompleteQuadrant

/--
Binary circuit elimination is the graph-specific theorem missing from the primitive `2×2` carrier:
a realized admissible boundary trace must supply a diagonal/quadrant, or the omitted diagonal is the
same first-return `0001` corner.
-/
def Q64BinaryCircuitElimination
    (PrimitiveCircuit RealizedDiagonalOrQuadrant FirstReturn0001 : Prop) : Prop :=
  PrimitiveCircuit → RealizedDiagonalOrQuadrant ∨ FirstReturn0001

/--
The row/column/diagonal pairings of a primitive carrier form a three-pairing triality.  Its
irreducible branch is package-coordinate monodromy rather than residue arithmetic.
-/
def Q64ThreePairingTriality
    (RowPairing ColumnPairing DiagonalPairing RealizedDiagonal PackageMonodromy : Prop) : Prop :=
  RowPairing → ColumnPairing → DiagonalPairing → RealizedDiagonal ∨ PackageMonodromy

/-- Project packet-primality from the equivalence package. -/
theorem q64_packetPrimality_of_admissibleModulePrimeness
    {AdmissibleModulePrimeness FirstReturnPacketPrimality : Prop}
    (heq :
      Q64AdmissibleModulePacketPrimalityEquivalence AdmissibleModulePrimeness
        FirstReturnPacketPrimality)
    (h : AdmissibleModulePrimeness) :
    FirstReturnPacketPrimality :=
  heq.mp h

/-- Project admissible-module primeness from the equivalence package. -/
theorem q64_admissibleModulePrimeness_of_packetPrimality
    {AdmissibleModulePrimeness FirstReturnPacketPrimality : Prop}
    (heq :
      Q64AdmissibleModulePacketPrimalityEquivalence AdmissibleModulePrimeness
        FirstReturnPacketPrimality)
    (h : FirstReturnPacketPrimality) :
    AdmissibleModulePrimeness :=
  heq.mpr h

/-- First-return packet-primality directly supplies the older carrier/marker coupling API. -/
theorem q64_qMarkerCarrierMarkerCoupling_of_firstReturnPacketPrimality
    {FullySkewSplitter GenuineQMarkerPacketAtom FirstReturnPackagePrime
      PacketRefiningAdmissibleRow LocalExit ProperSubmarker PrimeModuleExit ClosedLocalExit : Prop}
    (hpacket :
      Q64FirstReturnPacketPrimality GenuineQMarkerPacketAtom FirstReturnPackagePrime
        PacketRefiningAdmissibleRow LocalExit)
    (hskewToPacket : FullySkewSplitter → GenuineQMarkerPacketAtom)
    (hprime : FirstReturnPackagePrime → PrimeModuleExit)
    (hrefine : PacketRefiningAdmissibleRow → ProperSubmarker)
    (hlocal : LocalExit → ClosedLocalExit) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  intro hskew
  rcases hpacket (hskewToPacket hskew) with hpkg | href | hloc
  · exact Or.inr (Or.inl (hprime hpkg))
  · exact Or.inl (hrefine href)
  · exact Or.inr (Or.inr (hlocal hloc))

/--
Side-replacement normal form: after side homogeneity, any residual replacement atom either closes
locally, freezes a packet, exposes a proper first-return-complete arc, or becomes a directed
replacement cycle.
-/
def Q64SideReplacementCycleNormalForm
    (SideReplacementAtom LocalExit FrozenPacket ProperFirstReturnCompleteArc
      DirectedReplacementCycle : Prop) : Prop :=
  SideReplacementAtom →
    LocalExit ∨ FrozenPacket ∨ ProperFirstReturnCompleteArc ∨ DirectedReplacementCycle

/--
The ordered-cycle shortcut is valid only after all replacement-cycle edges have been packaged in one
peeled first-return space: then the earliest edge distinguishes a proper arc or one of the closed
local/weighted quotient exits applies.
-/
def Q64ReplacementCycleCommonPackageReduction
    (DirectedReplacementCycle CommonPeeledPackage ProperFirstReturnArc CompleterExit
      ProperMarkerExit LocalCoalescence CommonPackageFailure : Prop) : Prop :=
  DirectedReplacementCycle →
    (CommonPeeledPackage →
      ProperFirstReturnArc ∨ CompleterExit ∨ ProperMarkerExit ∨ LocalCoalescence) ∧
    (¬ CommonPeeledPackage → CommonPackageFailure)

/--
Two-cycle replacement normal form: if both arcs are in one package the cycle is just the balanced
`0101/0011` flip; otherwise the first failed common-space edge is again `0001`.
-/
def Q64ReplacementTwoCycleNormalForm
    (ReplacementTwoCycle SamePackageBalancedFlip FirstFailedCommonSpace0001 : Prop) : Prop :=
  ReplacementTwoCycle → SamePackageBalancedFlip ∨ FirstFailedCommonSpace0001

/--
Irreducible directed replacement cycles carry no first-return-complete arc, frozen packet, local exit,
or complete quadrant.
-/
def Q64IrreducibleReplacementCycle
    (DirectedReplacementCycle NoProperFirstReturnArc NoFrozenPacket NoLocalExit NoCompleteQuadrant :
      Prop) : Prop :=
  DirectedReplacementCycle ∧ NoProperFirstReturnArc ∧ NoFrozenPacket ∧ NoLocalExit ∧
    NoCompleteQuadrant

/-- In the irreducible side-replacement atom, the normal form leaves only a directed cycle. -/
theorem q64_directedReplacementCycle_of_irreducible_sideReplacement
    {SideReplacementAtom LocalExit FrozenPacket ProperFirstReturnCompleteArc
      DirectedReplacementCycle : Prop}
    (hnf :
      Q64SideReplacementCycleNormalForm SideReplacementAtom LocalExit FrozenPacket
        ProperFirstReturnCompleteArc DirectedReplacementCycle)
    (hnoLocal : ¬ LocalExit) (hnoFrozen : ¬ FrozenPacket)
    (hnoArc : ¬ ProperFirstReturnCompleteArc) (hatom : SideReplacementAtom) :
    DirectedReplacementCycle := by
  rcases hnf hatom with hlocal | hfrozen | harc | hcycle
  · exact False.elim (hnoLocal hlocal)
  · exact False.elim (hnoFrozen hfrozen)
  · exact False.elim (hnoArc harc)
  · exact hcycle

/-- Natural packet weight used in the clique-quotient audit. -/
def q64PacketWeight (cliqueSize cliqueCount : ℕ) : ℕ := cliqueCount * cliqueSize

/-- Total weight of a primitive `2×2` carrier. -/
def q64TwoByTwoTotal (w : Bool → Bool → ℕ) : ℕ :=
  w false false + w true false + w false true + w true true

/-- Row-pair weight of a primitive `2×2` carrier. -/
def q64TwoByTwoRow (w : Bool → Bool → ℕ) (x : Bool) : ℕ :=
  w x false + w x true

/-- Column-pair weight of a primitive `2×2` carrier. -/
def q64TwoByTwoColumn (w : Bool → Bool → ℕ) (y : Bool) : ℕ :=
  w false y + w true y

/-- Main-diagonal pair weight of a primitive `2×2` carrier. -/
def q64TwoByTwoMainDiagonal (w : Bool → Bool → ℕ) : ℕ :=
  w false false + w true true

/-- Off-diagonal pair weight of a primitive `2×2` carrier. -/
def q64TwoByTwoOffDiagonal (w : Bool → Bool → ℕ) : ℕ :=
  w true false + w false true

/--
Primitive `2×2` residue circuit: the total carrier has zero residue, while every row, column,
quadrant, and packaged diagonal has nonzero residue.
-/
def Q64PrimitiveTwoByTwoResidueCircuit (q : ℕ) (w : Bool → Bool → ℕ) : Prop :=
  q64TwoByTwoTotal w % q = 0 ∧
    (∀ x, q64TwoByTwoRow w x % q ≠ 0) ∧
      (∀ y, q64TwoByTwoColumn w y % q ≠ 0) ∧
        (∀ x y, w x y % q ≠ 0) ∧
          q64TwoByTwoMainDiagonal w % q ≠ 0 ∧
            q64TwoByTwoOffDiagonal w % q ≠ 0

/-- Constant positive quadrant weights form a primitive `2×2` circuit at modulus `4k`. -/
theorem q64_primitiveTwoByTwoResidueCircuit_const_quadrants
    {q k : ℕ} (hq : q = 4 * k) (hk : 0 < k) :
    Q64PrimitiveTwoByTwoResidueCircuit q (fun _ _ => k) := by
  subst q
  have htotal : (k + k + k + k) % (4 * k) = 0 := by
    have hsum : k + k + k + k = 4 * k := by omega
    rw [hsum, Nat.mod_self]
  have hkmod : k % (4 * k) ≠ 0 := by
    have hlt : k < 4 * k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.ne_of_gt hk
  have h2mod : (k + k) % (4 * k) ≠ 0 := by
    have hpos : 0 < k + k := by omega
    have hlt : k + k < 4 * k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.ne_of_gt hpos
  unfold Q64PrimitiveTwoByTwoResidueCircuit q64TwoByTwoTotal q64TwoByTwoRow
    q64TwoByTwoColumn q64TwoByTwoMainDiagonal q64TwoByTwoOffDiagonal
  simp [htotal, hkmod, h2mod]

/--
Primitive simultaneous-wall antichain: the whole antichain is zero-sum, all packet pieces survive the
common-divisor residue-shadow removal, and no proper first-return-complete subcarrier is zero-sum.
-/
def Q64PrimitiveFirstWallAntichain
    (q : ℕ) (P : Finset U) (weight : U → ℕ) (FirstReturnComplete : Finset U → Prop) :
    Prop :=
  P.Nonempty ∧ (∑ p ∈ P, weight p) % q = 0 ∧
    (∀ p ∈ P, Nat.Coprime q (weight p)) ∧
      ∀ T : Finset U, T ⊂ P → T.Nonempty → FirstReturnComplete T →
        (∑ p ∈ T, weight p) % q ≠ 0

/--
Product-firewall containment closes when the dirty shared-slack set lies in one proper breaker side;
otherwise the survivor is the simultaneous-wall antichain.
-/
def Q64ProductFirewallContainmentOrAntichain
    (DirtySharedSlackSet ProperBreakerSide SimultaneousWallAntichain : Prop) : Prop :=
  DirtySharedSlackSet → ProperBreakerSide ∨ SimultaneousWallAntichain

/-- The primitive antichain residue pattern `(1,1,1,q-3)` is arithmetically viable for `q ≥ 4`. -/
theorem q64_primitiveAntichain_one_one_one_qMinusThree
    {q : ℕ} (hq : 4 ≤ q) :
    (1 + 1 + 1 + (q - 3)) % q = 0 ∧ 1 % q ≠ 0 ∧ (q - 3) % q ≠ 0 := by
  have hsum : 1 + 1 + 1 + (q - 3) = q := by omega
  have h1lt : 1 < q := by omega
  have hq3pos : 0 < q - 3 := by omega
  have hq3lt : q - 3 < q := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt h1lt]
    norm_num
  · rw [Nat.mod_eq_of_lt hq3lt]
    exact Nat.ne_of_gt hq3pos

/--
Dyadic odd-layer endpoint: a survivor with no realized first-return-complete odd-pair carrier closes
only by crossing odd-cut elimination, laminar even-interval realization, or the first adjacent laminar
common-package failure.
-/
def Q64DyadicOddLayerEndpoint
    (DyadicOddLayerSurvivor CrossingOddCutElimination LaminarEvenIntervalRealization
      AdjacentLaminarPackageChange0001 : Prop) : Prop :=
  DyadicOddLayerSurvivor →
    CrossingOddCutElimination ∨ LaminarEvenIntervalRealization ∨
      AdjacentLaminarPackageChange0001

/--
Maximal length-`q` zero-sum atoms have no remaining residue heterogeneity after unit scaling: all
packet residues are one generator.  This is bookkeeping only; it still does not realize a subcarrier.
-/
def Q64MaximalZeroSumAtomUnitGenerator
    (MaximalLengthQAtom UnitScaledGeneratorResidues : Prop) : Prop :=
  MaximalLengthQAtom → UnitScaledGeneratorResidues

/--
Binary skew-ladder adjacent-turn test: opposite-side turns in one package are zero raw packets, and
same-side turns in one fixed frame are local same-trace/twin exits; any surviving edge is an adjacent
package-change `0001`.
-/
def Q64BinarySkewLadderAdjacentTurnTest
    (LadderEdge OppositeSideOnePackageZeroRaw SameSideFixedFrameTwinExit
      AdjacentPackageChange0001 : Prop) : Prop :=
  LadderEdge →
    OppositeSideOnePackageZeroRaw ∨ SameSideFixedFrameTwinExit ∨ AdjacentPackageChange0001

/-- A packet quotient has total marker weight zero modulo `q`. -/
def Q64ZeroResiduePacketQuotient
    (q : ℕ) (P : Finset U) (weight : U → ℕ) : Prop :=
  (∑ p ∈ P, weight p) % q = 0

/--
Minimal zero-sum packet atom: the whole packet quotient has zero residue, but no proper nonempty
first-return-complete subquotient has zero residue.
-/
def Q64MinimalZeroSumPacketAtom
    (q : ℕ) (P : Finset U) (weight : U → ℕ)
    (FirstReturnComplete : Finset U → Prop) : Prop :=
  P.Nonempty ∧ Q64ZeroResiduePacketQuotient q P weight ∧
    ∀ T : Finset U, T ⊂ P → T.Nonempty → FirstReturnComplete T →
      (∑ p ∈ T, weight p) % q ≠ 0

/--
Divisor-sparse clique quotient: for each divisor `h` of `q`, there are too few cliques of size at
least `h` to select `h` vertices from each and immediately obtain a regular induced `q`-set.
-/
def Q64DivisorSparseCliqueQuotient
    (q : ℕ) (P : Finset U) (cliqueSize : U → ℕ) : Prop :=
  ∀ h : ℕ, h ∣ q → 0 < h → (P.filter fun p => h ≤ cliqueSize p).card < q / h

/--
Packet-quotient regular-selection endpoint: the exact atom either has a regular `q`-selection,
packages into Section 40, or exposes a smaller first-return-complete zero-sum marker.
-/
def Q64PacketQuotientRegularSelection
    (RegularQSelection Section40Package ProperZeroSumMarker : Prop) : Prop :=
  RegularQSelection ∨ Section40Package ∨ ProperZeroSumMarker

/--
Exact-marker selection reduction from the latest proof.md status: all one-splitter exact branches are
closed, and the residual survivor is the two-splitter / zero-sum packet atom.
-/
def Q64ExactMarkerSelectionReduction
    (ExactMarkerSurvivor NoSplitClosed LowUniversalClosed HighNullClosed SingletonLiftClosed
      TwoSplitterZeroSumPacketAtom : Prop) : Prop :=
  ExactMarkerSurvivor →
    NoSplitClosed ∨ LowUniversalClosed ∨ HighNullClosed ∨ SingletonLiftClosed ∨
      TwoSplitterZeroSumPacketAtom

/-- If every closed exact-marker branch is ruled out, the residual is the two-splitter packet atom. -/
theorem q64_twoSplitterZeroSumPacketAtom_of_exactMarkerSelectionReduction
    {ExactMarkerSurvivor NoSplitClosed LowUniversalClosed HighNullClosed SingletonLiftClosed
      TwoSplitterZeroSumPacketAtom : Prop}
    (hred :
      Q64ExactMarkerSelectionReduction ExactMarkerSurvivor NoSplitClosed LowUniversalClosed
        HighNullClosed SingletonLiftClosed TwoSplitterZeroSumPacketAtom)
    (hnoSplit : ¬ NoSplitClosed) (hnoLow : ¬ LowUniversalClosed)
    (hnoHigh : ¬ HighNullClosed) (hnoLift : ¬ SingletonLiftClosed)
    (hsurvivor : ExactMarkerSurvivor) :
    TwoSplitterZeroSumPacketAtom := by
  rcases hred hsurvivor with hsplit | hlow | hhigh | hlift | hatom
  · exact False.elim (hnoSplit hsplit)
  · exact False.elim (hnoLow hlow)
  · exact False.elim (hnoHigh hhigh)
  · exact False.elim (hnoLift hlift)
  · exact hatom

/--
Product-firewall routing target from the latest zero-sum audit: provenance rows and ambient high-error
rows must be transported into one fixed first-return frame.
-/
def Q64LastObstructionProductFirewall
    (ProvenanceCutsCompensator AmbientCutsMarker SharedFirstReturnFrame : Prop) : Prop :=
  ProvenanceCutsCompensator → AmbientCutsMarker → SharedFirstReturnFrame

/--
Weighted-quotient packaging target for the marker-splitting zero-sum atom: once the atom is packaged
in the prime weighted quotient frame, it either has a regular `q`-selection, falls to Section 40, or
exposes a proper first-return-complete zero-sum marker.
-/
def Q64ZeroSumAtomWeightedQuotientPackaging
    (ZeroSumPacketAtom WeightedQuotientFrame RegularQSelection Section40Package
      ProperZeroSumMarker : Prop) : Prop :=
  ZeroSumPacketAtom → WeightedQuotientFrame →
    Q64PacketQuotientRegularSelection RegularQSelection Section40Package ProperZeroSumMarker

/--
Landing surface for the incoming final obstruction proof: the marker-splitting zero-sum atom,
product-firewall routing, and weighted-quotient packaging together produce carrier/marker coupling.
-/
def Q64LastObstructionLandingSurface
    (MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      CarrierMarkerCoupling : Prop) : Prop :=
  MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
    CarrierMarkerCoupling

/-- A positive integer below `q` has nonzero residue modulo `q`. -/
theorem q64_positive_subq_residue_ne_zero {q n : ℕ} (hpos : 0 < n) (hlt : n < q) :
    n % q ≠ 0 := by
  rw [Nat.mod_eq_of_lt hlt]
  exact Nat.ne_of_gt hpos

omit [Fintype U] in
/--
Ordered boundary completeness only needs side provenance after this point: any failed set contained
in a proper protected packet has cardinality below `q`.
-/
theorem q64_orderedBoundary_failedSet_card_lt_q
    {q : ℕ} {P F : Finset U} (hsub : F ⊆ P) (hpacket : P.card < q) : F.card < q :=
  lt_of_le_of_lt (Finset.card_le_card hsub) hpacket

/-- A nonempty failed side below `q` cannot be a q-marker by residue alone. -/
theorem q64_nonempty_subq_failedSide_not_qMarker
    {q : ℕ} {F : Finset U} (hF : F.Nonempty) (hlt : F.card < q) : F.card % q ≠ 0 :=
  q64_positive_subq_residue_ne_zero hF.card_pos hlt

/-- In an exact two-packet marker, the whole pair has zero residue and neither packet does. -/
theorem q64_two_packet_exact_minimal_zero_sum {q a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hsum : a + b = q) :
    (a + b) % q = 0 ∧ a % q ≠ 0 ∧ b % q ≠ 0 := by
  have ha_lt : a < q := by omega
  have hb_lt : b < q := by omega
  refine ⟨?_, q64_positive_subq_residue_ne_zero ha ha_lt,
    q64_positive_subq_residue_ne_zero hb hb_lt⟩
  rw [hsum]
  exact Nat.mod_self q

/--
Two-packet half-excess arithmetic: in the one-sided compensator quotient, degree equality and total
size force the combined smaller-clique/compensator mass to be exactly `b+t`.
-/
theorem q64_twoPacket_halfExcess_sum
    {a b t q alpha beta gamma : ℕ}
    (ha : a = b + 2 * t) (hq : q = a + b)
    (hdegree : alpha = beta + gamma) (hsize : alpha + beta + gamma = q) :
    beta + gamma = b + t := by
  omega

/--
Consequently, if at most all `b` vertices of the smaller marker clique are selected, the compensator
part contains at least the half-excess `t`.
-/
theorem q64_twoPacket_compensator_at_least_halfExcess
    {a b t q alpha beta gamma : ℕ}
    (ha : a = b + 2 * t) (hq : q = a + b)
    (hdegree : alpha = beta + gamma) (hsize : alpha + beta + gamma = q)
    (hbeta : beta ≤ b) :
    t ≤ gamma := by
  have hsum := q64_twoPacket_halfExcess_sum ha hq hdegree hsize
  omega

/--
The static `K_(q-2) ∪ K_2` independent-compensator shortcut cannot produce the claimed mixed regular
selection under its forced equations when `q ≥ 8`.
-/
theorem q64_qMinusTwo_independentCompensator_no_mixed_selection
    {q x y z : ℕ} (hq : 8 ≤ q) (hy : y ≤ 2) (hz : z = 1)
    (hx : x = y + 1) (hsize : x + y + z = q) :
    False := by
  omega

/--
Exact packet partitions are automatically minimal at the bare residue level: a proper positive
subsum with a positive complementary packet cannot have zero residue modulo the total `q`.
-/
theorem q64_exact_positive_proper_subsum_residue_ne_zero {q sub comp : ℕ}
    (hsub : 0 < sub) (hcomp : 0 < comp) (htotal : sub + comp = q) :
    sub % q ≠ 0 := by
  have hlt : sub < q := by omega
  rw [Nat.mod_eq_of_lt hlt]
  exact Nat.ne_of_gt hsub

omit [Fintype U] in
/--
Exact packet atoms of total integer weight `q` are automatically minimal at the bare residue level:
every proper nonempty packet union has positive weight strictly below `q`, hence nonzero residue.
-/
theorem q64_exact_packet_proper_union_residue_ne_zero
    {q : ℕ} {P T : Finset U} {weight : U → ℕ}
    (hTP : T ⊂ P) (hTnon : T.Nonempty)
    (hpos : ∀ p ∈ P, 0 < weight p)
    (htotal : (∑ p ∈ P, weight p) = q) :
    (∑ p ∈ T, weight p) % q ≠ 0 := by
  have hsub : T ⊆ P := hTP.1
  have hTpos : 0 < ∑ p ∈ T, weight p := by
    apply Finset.sum_pos
    · intro p hpT
      exact hpos p (hsub hpT)
    · exact hTnon
  have hextra : ∃ p, p ∈ P ∧ p ∉ T := by
    by_contra hnone
    have hPsubT : P ⊆ T := by
      intro p hpP
      by_contra hpT
      exact hnone ⟨p, hpP, hpT⟩
    exact hTP.2 hPsubT
  rcases hextra with ⟨p, hpP, hpT⟩
  have hsum_lt : (∑ x ∈ T, weight x) < ∑ x ∈ P, weight x := by
    exact Finset.sum_lt_sum_of_subset hsub hpP hpT (hpos p hpP)
      (fun x _ _ => Nat.zero_le (weight x))
  have hlt : (∑ p ∈ T, weight p) < q := by
    simpa [htotal] using hsum_lt
  exact q64_positive_subq_residue_ne_zero hTpos hlt

omit [Fintype U] in
/--
When the exact packet quotient has total positive packet weights summing to the integer `q`, the
minimal zero-sum condition follows without any first-return input.
-/
theorem q64_minimalZeroSumPacketAtom_of_exact_total_weight
    {q : ℕ} {P : Finset U} {weight : U → ℕ} {FirstReturnComplete : Finset U → Prop}
    (hPnon : P.Nonempty) (hpos : ∀ p ∈ P, 0 < weight p)
    (htotal : (∑ p ∈ P, weight p) = q) :
    Q64MinimalZeroSumPacketAtom q P weight FirstReturnComplete := by
  refine ⟨hPnon, ?_, ?_⟩
  · unfold Q64ZeroResiduePacketQuotient
    rw [htotal]
    exact Nat.mod_self q
  · intro T hTP hTnon _hcomplete
    exact q64_exact_packet_proper_union_residue_ne_zero hTP hTnon hpos htotal

/--
If weighted-quotient packaging has been proved and each of its three exits is ruled out, the explicit
zero-sum packet atom cannot survive.
-/
theorem q64_no_zeroSumPacketAtom_of_weightedQuotientPackaging
    {ZeroSumPacketAtom WeightedQuotientFrame RegularQSelection Section40Package
      ProperZeroSumMarker : Prop}
    (hpack :
      Q64ZeroSumAtomWeightedQuotientPackaging ZeroSumPacketAtom WeightedQuotientFrame
        RegularQSelection Section40Package ProperZeroSumMarker)
    (hframe : ZeroSumPacketAtom → WeightedQuotientFrame)
    (hnoReg : ¬ RegularQSelection) (hnoSection : ¬ Section40Package)
    (hnoProper : ¬ ProperZeroSumMarker) :
    ¬ ZeroSumPacketAtom := by
  intro hzero
  rcases hpack hzero (hframe hzero) with hreg | hsection | hproper
  · exact hnoReg hreg
  · exact hnoSection hsection
  · exact hnoProper hproper

/--
The no-q-jump theorem plus the last-obstruction weighted packaging closes a simultaneous wall block
once the regular/local/smaller exits are known impossible.
-/
theorem q64_no_simultaneousWallBlock_of_noQJump_and_weightedPackaging
    {SimultaneousWallBlock RegularQSet LocalExit SmallerCompleteMarker ZeroSumPacketAtom
      WeightedQuotientFrame RegularQSelection Section40Package ProperZeroSumMarker : Prop}
    (hjump :
      Q64LargeMarkerNoQJumpTheorem SimultaneousWallBlock RegularQSet LocalExit
        SmallerCompleteMarker ZeroSumPacketAtom)
    (hpack :
      Q64ZeroSumAtomWeightedQuotientPackaging ZeroSumPacketAtom WeightedQuotientFrame
        RegularQSelection Section40Package ProperZeroSumMarker)
    (hframe : ZeroSumPacketAtom → WeightedQuotientFrame)
    (hselection : RegularQSelection → RegularQSet)
    (hsection : Section40Package → LocalExit)
    (hproper : ProperZeroSumMarker → SmallerCompleteMarker)
    (hnoReg : ¬ RegularQSet) (hnoLocal : ¬ LocalExit)
    (hnoSmall : ¬ SmallerCompleteMarker) :
    ¬ SimultaneousWallBlock := by
  intro hwall
  rcases hjump hwall with hreg | hlocal | hsmall | hzero
  · exact hnoReg hreg
  · exact hnoLocal hlocal
  · exact hnoSmall hsmall
  · rcases hpack hzero (hframe hzero) with hsel | hsec | hprop
    · exact hnoReg (hselection hsel)
    · exact hnoLocal (hsection hsec)
    · exact hnoSmall (hproper hprop)

/--
Product-firewall transport trap from the final split-quotient audit: a failed high-error ambient
packet breaker produces a nonempty shared-slack marker strictly smaller than `q`, while the low-set
update says that marker size is `0 [MOD q]`.
-/
def Q64ProductFirewallTransportTrap
    (q : ℕ) (TransportFailure : Prop) (markerSize : TransportFailure → ℕ) : Prop :=
  ∀ hfail : TransportFailure, 0 < markerSize hfail ∧ markerSize hfail < q ∧
    markerSize hfail % q = 0

/--
Concrete sub-`q` marker data produced by a failed product-firewall transport in the notes: the
square-breaker reduction gives a nonempty dirty shared-slack marker contained in one side of a proper
packet, and that packet has size `< q`; the low-set update gives residue `0 [MOD q]`.
-/
structure Q64FailedTransportSubqMarkerData
    (q : ℕ) (TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  marker_pos : ∀ hfail : TransportFailure, 0 < markerSize hfail
  marker_le_packet : ∀ hfail : TransportFailure, markerSize hfail ≤ packetSize hfail
  packet_lt_q : ∀ hfail : TransportFailure, packetSize hfail < q
  marker_mod_zero : ∀ hfail : TransportFailure, markerSize hfail % q = 0

/--
The square-breaker reduction part of a failed transport: the failed boundary transport produces a
nonempty dirty shared-slack marker contained in the packet side selected by the failure.
-/
def Q64TransportFailureProducesDirtySubmarker
    (TransportFailure : Prop) (markerSize packetSize : TransportFailure → ℕ) : Prop :=
  ∀ hfail : TransportFailure, 0 < markerSize hfail ∧ markerSize hfail ≤ packetSize hfail

/-- The packet side selected by a failed transport is proper, hence has size `< q`. -/
def Q64TransportFailureProperPacketBound
    (q : ℕ) (TransportFailure : Prop) (packetSize : TransportFailure → ℕ) : Prop :=
  ∀ hfail : TransportFailure, packetSize hfail < q

/--
Low-set congruence for the transported marker: every surviving first-return shared-slack marker has
size `0 [MOD q]`.
-/
def Q64TransportFailureLowSetCongruence
    (q : ℕ) (TransportFailure : Prop) (markerSize : TransportFailure → ℕ) : Prop :=
  ∀ hfail : TransportFailure, markerSize hfail % q = 0

/--
The three note-level subclaims -- dirty submarker production, proper-packet size, and low-set
congruence -- assemble into the failed-transport sub-`q` marker data.
-/
theorem q64_failedTransportSubqMarkerData_of_components
    {q : ℕ} {TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hsubmarker :
      Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize)
    (hpacket :
      Q64TransportFailureProperPacketBound q TransportFailure packetSize)
    (hcongr :
      Q64TransportFailureLowSetCongruence q TransportFailure markerSize) :
    Q64FailedTransportSubqMarkerData q TransportFailure markerSize packetSize where
  marker_pos := fun hfail => (hsubmarker hfail).1
  marker_le_packet := fun hfail => (hsubmarker hfail).2
  packet_lt_q := hpacket
  marker_mod_zero := hcongr

/--
The component form directly gives the product-firewall transport trap, so the impossible branch is
eliminated without assuming the packed trap itself.
-/
theorem q64_productFirewallTransportTrap_of_failedTransportComponents
    {q : ℕ} {TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hsubmarker :
      Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize)
    (hpacket :
      Q64TransportFailureProperPacketBound q TransportFailure packetSize)
    (hcongr :
      Q64TransportFailureLowSetCongruence q TransportFailure markerSize) :
    Q64ProductFirewallTransportTrap q TransportFailure markerSize := by
  intro hfail
  exact ⟨(hsubmarker hfail).1,
    lt_of_le_of_lt (hsubmarker hfail).2 (hpacket hfail),
    hcongr hfail⟩

/--
The explicit failed-transport marker data is exactly the product-firewall sub-`q` transport trap.
-/
theorem q64_productFirewallTransportTrap_of_failedTransportSubqMarkerData
    {q : ℕ} {TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hdata :
      Q64FailedTransportSubqMarkerData q TransportFailure markerSize packetSize) :
    Q64ProductFirewallTransportTrap q TransportFailure markerSize := by
  intro hfail
  exact ⟨hdata.marker_pos hfail,
    lt_of_le_of_lt (hdata.marker_le_packet hfail) (hdata.packet_lt_q hfail),
    hdata.marker_mod_zero hfail⟩

/--
The sub-`q` transport trap is contradictory: no nonempty marker of size `< q` can have residue
`0 [MOD q]`.
-/
theorem q64_no_productFirewall_transportFailure_of_subqTrap
    {q : ℕ} {TransportFailure : Prop} {markerSize : TransportFailure → ℕ}
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize) :
    ¬ TransportFailure := by
  intro hfail
  exact q64_positive_subq_residue_ne_zero (htrap hfail).1 (htrap hfail).2.1
    (htrap hfail).2.2

/--
Row-to-boundary transport closure for the product-firewall endpoint: each live ambient packet breaker
either becomes an ordered first-return boundary row or has already exited locally.
-/
def Q64ProductFirewallTransportClosure
    (AmbientPacketBreaker OrderedBoundaryRow LocalExit : Prop) : Prop :=
  AmbientPacketBreaker → OrderedBoundaryRow ∨ LocalExit

/--
The pre-trap transport reduction in the product-firewall proof: an ambient packet breaker either
already reaches an ordered first-return boundary row, exits locally, or is a transport failure.
-/
def Q64ProductFirewallTransportReduction
    (AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop) : Prop :=
  AmbientPacketBreaker → OrderedBoundaryRow ∨ LocalExit ∨ TransportFailure

/--
The two non-failure transport exits both supply carrier/marker coupling.
-/
def Q64BoundaryExitCarrierMarkerCoupling
    (OrderedBoundaryRow LocalExit CarrierMarkerCoupling : Prop) : Prop :=
  (OrderedBoundaryRow → CarrierMarkerCoupling) ∧ (LocalExit → CarrierMarkerCoupling)

/--
Product-firewall proof certificate, matching the note proof: the zero-sum atom, product firewall, and
weighted quotient package produce an ambient breaker; product-firewall transport routes any such
breaker to an ordered boundary row, local exit, or transport failure; the sub-`q` trap eliminates
transport failures; and the two non-failure exits give carrier/marker coupling.
-/
structure Q64ProductFirewallProofCertificate
    (q : ℕ)
    (MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize : TransportFailure → ℕ) : Prop where
  zero : MarkerSplittingZeroSumAtom
  firewall : ProductFirewall
  packaging : WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  trap : Q64ProductFirewallTransportTrap q TransportFailure markerSize
  exits : Q64BoundaryExitCarrierMarkerCoupling OrderedBoundaryRow LocalExit CarrierMarkerCoupling

/--
More explicit product-firewall certificate using the note's failed-transport marker data rather than
the already-compressed trap: failed transport produces a positive low-set marker contained in a
proper packet of size `< q`.
-/
structure Q64ProductFirewallProofDataCertificate
    (q : ℕ)
    (MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  zero : MarkerSplittingZeroSumAtom
  firewall : ProductFirewall
  packaging : WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  subqMarkerData :
    Q64FailedTransportSubqMarkerData q TransportFailure markerSize packetSize
  exits : Q64BoundaryExitCarrierMarkerCoupling OrderedBoundaryRow LocalExit CarrierMarkerCoupling

/--
The fully expanded q-marker product-firewall route claimed by the notes.  It starts from the fully
skew branch, applies static split-quotient exhaustion to reach the product firewall, transports the
ambient packet breaker to an ordered boundary row or local exit, and kills every transport failure by
the explicit sub-`q` marker data.
-/
structure Q64ProductFirewallQMarkerCouplingData
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  subqMarkerData :
    Q64FailedTransportSubqMarkerData q TransportFailure markerSize packetSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit
  localExit :
    LocalExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit

/--
Four-exit version of the product-firewall q-marker route from `proof.md`: the surviving
ordered-boundary/local branches may close by producing an explicit regular `q`-set.
-/
structure Q64ProductFirewallQMarkerCouplingDataWithRegularQSet
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  subqMarkerData :
    Q64FailedTransportSubqMarkerData q TransportFailure markerSize packetSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  localExit :
    LocalExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet

/--
Product-firewall q-marker route conditional on Gap Theorem G.  Static split-quotient exhaustion
produces the product-firewall frame and an ambient high-error splitter; Theorem G routes that splitter
to one of the three proof.md outcomes, each of which lands in the carrier/marker coupling exits.
-/
structure Q64ProductFirewallTheoremGQMarkerCouplingDataWithRegularQSet
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientHighErrorSplitter OrderedBoundaryRow LocalRegularizingExit
      CompleteSmallerQMarker : Prop) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  splitter :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientHighErrorSplitter
  theoremG :
    AmbientHighErrorSplitter →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryRow CompleteSmallerQMarker
        LocalRegularizingExit
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  localExit :
    LocalRegularizingExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  smallerMarker : CompleteSmallerQMarker → ProperSubmarker

/--
Component-level product-firewall q-marker route.  This version keeps the failed-transport
contradiction split into the three subclaims named in the notes instead of preassembling
`Q64FailedTransportSubqMarkerData`.
-/
structure Q64ProductFirewallQMarkerCouplingComponents
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  submarker :
    Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize
  packetBound :
    Q64TransportFailureProperPacketBound q TransportFailure packetSize
  lowSetCongruence :
    Q64TransportFailureLowSetCongruence q TransportFailure markerSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit
  localExit :
    LocalExit → FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit

/--
Four-exit component-level product-firewall route.  This keeps the failed-transport contradiction
split into the three note-level subclaims and keeps the explicit regular-`q`-set exit.
-/
structure Q64ProductFirewallQMarkerCouplingComponentsWithRegularQSet
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientExhaustion FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  submarker :
    Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize
  packetBound :
    Q64TransportFailureProperPacketBound q TransportFailure packetSize
  lowSetCongruence :
    Q64TransportFailureLowSetCongruence q TransportFailure markerSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  localExit :
    LocalExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet

/--
Fully componentized product-firewall q-marker route: the static split-quotient input is also split
into its zero-sum, firewall, and weighted-packaging constructors.
-/
structure Q64ProductFirewallQMarkerCouplingAudit
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientAudit FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  submarker :
    Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize
  packetBound :
    Q64TransportFailureProperPacketBound q TransportFailure packetSize
  lowSetCongruence :
    Q64TransportFailureLowSetCongruence q TransportFailure markerSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit
  localExit :
    LocalExit → FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit

/--
Four-exit fully componentized product-firewall q-marker route: the split-quotient audit and the
failed-transport trap are both split, and the regular-`q`-set exit is kept explicit.
-/
structure Q64ProductFirewallQMarkerCouplingAuditWithRegularQSet
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop)
    (markerSize packetSize : TransportFailure → ℕ) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientAudit FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  breaker :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientPacketBreaker
  transport :
    ProductFirewall →
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure
  submarker :
    Q64TransportFailureProducesDirtySubmarker TransportFailure markerSize packetSize
  packetBound :
    Q64TransportFailureProperPacketBound q TransportFailure packetSize
  lowSetCongruence :
    Q64TransportFailureLowSetCongruence q TransportFailure markerSize
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  localExit :
    LocalExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet

/--
Audit-level version of the Theorem-G q-marker route: the static split quotient is supplied by its
component audit, while the only unclosed q-marker ingredient is the explicit support-decrease theorem.
-/
structure Q64ProductFirewallTheoremGQMarkerCouplingAuditWithRegularQSet
    (q : ℕ)
    (FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientHighErrorSplitter OrderedBoundaryRow LocalRegularizingExit
      CompleteSmallerQMarker : Prop) : Prop where
  splitQuotient :
    Q64StaticSplitQuotientAudit FullySkewSplitter MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging
  splitter :
    MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
      AmbientHighErrorSplitter
  theoremG :
    AmbientHighErrorSplitter →
      Q64QMarkerProvenanceSupportDecrease OrderedBoundaryRow CompleteSmallerQMarker
        LocalRegularizingExit
  boundary :
    OrderedBoundaryRow →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  localExit :
    LocalRegularizingExit →
      FullySkewSplitter → ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨ RegularQSet
  smallerMarker : CompleteSmallerQMarker → ProperSubmarker

/-- The fully componentized q-marker audit assembles to the component route. -/
theorem q64_productFirewallQMarkerCouplingComponents_of_audit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingAudit q FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
        AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize) :
    Q64ProductFirewallQMarkerCouplingComponents q FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure
      markerSize packetSize where
  splitQuotient := q64_staticSplitQuotientExhaustion_of_audit h.splitQuotient
  breaker := h.breaker
  transport := h.transport
  submarker := h.submarker
  packetBound := h.packetBound
  lowSetCongruence := h.lowSetCongruence
  boundary := h.boundary
  localExit := h.localExit

/-- The four-exit fully componentized q-marker audit assembles to the four-exit component route. -/
theorem q64_productFirewallQMarkerCouplingComponentsWithRegularQSet_of_audit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingAuditWithRegularQSet q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64ProductFirewallQMarkerCouplingComponentsWithRegularQSet q FullySkewSplitter
      ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
      TransportFailure markerSize packetSize where
  splitQuotient := q64_staticSplitQuotientExhaustion_of_audit h.splitQuotient
  breaker := h.breaker
  transport := h.transport
  submarker := h.submarker
  packetBound := h.packetBound
  lowSetCongruence := h.lowSetCongruence
  boundary := h.boundary
  localExit := h.localExit

/-- The audit-level Theorem-G q-marker route assembles to the exhaustion-level route. -/
theorem q64_productFirewallTheoremGQMarkerCouplingDataWithRegularQSet_of_audit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientHighErrorSplitter OrderedBoundaryRow LocalRegularizingExit
      CompleteSmallerQMarker : Prop}
    (h :
      Q64ProductFirewallTheoremGQMarkerCouplingAuditWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientHighErrorSplitter OrderedBoundaryRow
        LocalRegularizingExit CompleteSmallerQMarker) :
    Q64ProductFirewallTheoremGQMarkerCouplingDataWithRegularQSet q FullySkewSplitter
      ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging AmbientHighErrorSplitter OrderedBoundaryRow
      LocalRegularizingExit CompleteSmallerQMarker where
  splitQuotient := q64_staticSplitQuotientExhaustion_of_audit h.splitQuotient
  splitter := h.splitter
  theoremG := h.theoremG
  boundary := h.boundary
  localExit := h.localExit
  smallerMarker := h.smallerMarker

/-- The component-level product-firewall route assembles to the marker-data route. -/
theorem q64_productFirewallQMarkerCouplingData_of_components
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingComponents q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64ProductFirewallQMarkerCouplingData q FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize where
  splitQuotient := h.splitQuotient
  breaker := h.breaker
  transport := h.transport
  subqMarkerData :=
    q64_failedTransportSubqMarkerData_of_components h.submarker h.packetBound
      h.lowSetCongruence
  boundary := h.boundary
  localExit := h.localExit

/-- Four-exit componentized q-marker route assembles to the packed four-exit marker-data route. -/
theorem q64_productFirewallQMarkerCouplingDataWithRegularQSet_of_components
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingComponentsWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64ProductFirewallQMarkerCouplingDataWithRegularQSet q FullySkewSplitter
      ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
      ProductFirewall WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
      TransportFailure markerSize packetSize where
  splitQuotient := h.splitQuotient
  breaker := h.breaker
  transport := h.transport
  subqMarkerData :=
    q64_failedTransportSubqMarkerData_of_components h.submarker h.packetBound
      h.lowSetCongruence
  boundary := h.boundary
  localExit := h.localExit

/-- The explicit product-firewall data certificate compresses to the trap-based certificate. -/
theorem q64_productFirewallProofCertificate_of_dataCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hcert :
      Q64ProductFirewallProofDataCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize packetSize) :
    Q64ProductFirewallProofCertificate q MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
      LocalExit TransportFailure markerSize where
  zero := hcert.zero
  firewall := hcert.firewall
  packaging := hcert.packaging
  breaker := hcert.breaker
  transport := hcert.transport
  trap := q64_productFirewallTransportTrap_of_failedTransportSubqMarkerData hcert.subqMarkerData
  exits := hcert.exits

/--
If every unresolved transport failure falls into the sub-`q` low-set trap, then the product firewall
has no transport survivor.
-/
theorem q64_productFirewallTransportClosure_of_subqTrap
    {q : ℕ} {AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize : TransportFailure → ℕ}
    (hreduce : AmbientPacketBreaker → OrderedBoundaryRow ∨ LocalExit ∨ TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize) :
    Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow LocalExit := by
  intro hbreaker
  rcases hreduce hbreaker with hboundary | hlocal | hfail
  · exact Or.inl hboundary
  · exact Or.inr hlocal
  · exact False.elim ((q64_no_productFirewall_transportFailure_of_subqTrap htrap) hfail)

/-- Named wrapper for the product-firewall transport reduction plus the sub-`q` trap. -/
theorem q64_productFirewallTransportClosure_of_transportReduction_and_subqTrap
    {q : ℕ} {AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize : TransportFailure → ℕ}
    (hreduce :
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize) :
    Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow LocalExit :=
  q64_productFirewallTransportClosure_of_subqTrap hreduce htrap

/--
Product-firewall transport closure is a direct Theorem-G support-decrease route: after failed
transports are killed by the sub-`q` trap, the ambient splitter reaches an ordered row or a local exit.
-/
theorem q64_theoremG_of_productFirewallTransportReduction_and_subqTrap
    {q : ℕ}
    {AmbientHighErrorSplitter AmbientPacketBreaker OrderedBoundaryRow CompleteSmallerQMarker
      LocalRegularizingExit TransportFailure : Prop}
    {markerSize : TransportFailure → ℕ}
    (hbreaker : AmbientHighErrorSplitter → AmbientPacketBreaker)
    (hreduce :
      Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow
        LocalRegularizingExit TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize)
    (hsplit : AmbientHighErrorSplitter) :
    Q64QMarkerProvenanceSupportDecrease OrderedBoundaryRow CompleteSmallerQMarker
      LocalRegularizingExit := by
  have hclosure :
      Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow
        LocalRegularizingExit :=
    q64_productFirewallTransportClosure_of_transportReduction_and_subqTrap hreduce htrap
  rcases hclosure (hbreaker hsplit) with hboundary | hlocal
  · exact Or.inl hboundary
  · exact Or.inr (Or.inr hlocal)

/--
Once the product-firewall transport closure has been proved, the last-obstruction landing surface is
just the bookkeeping that turns the ordered-boundary or local-exit branch into carrier/marker
coupling.
-/
theorem q64_lastObstructionLanding_of_productFirewallTransportClosure
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit : Prop}
    (hbreaker :
      MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
        AmbientPacketBreaker)
    (htransport :
      ProductFirewall →
        Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow LocalExit)
    (hboundary : OrderedBoundaryRow → CarrierMarkerCoupling)
    (hlocal : LocalExit → CarrierMarkerCoupling) :
    Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling := by
  intro hzero hfirewall hpack
  rcases htransport hfirewall (hbreaker hzero hfirewall hpack) with hordered | hexit
  · exact hboundary hordered
  · exact hlocal hexit

/--
Direct product-firewall landing theorem: transport reduction plus the sub-`q` trap removes the
failure branch, and the two remaining exits both yield carrier/marker coupling.
-/
theorem q64_lastObstructionLanding_of_transportReduction_and_subqTrap
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize : TransportFailure → ℕ}
    (hbreaker :
      MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
        AmbientPacketBreaker)
    (htransport :
      ProductFirewall →
        Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
          TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize)
    (hexits :
      Q64BoundaryExitCarrierMarkerCoupling OrderedBoundaryRow LocalExit CarrierMarkerCoupling) :
    Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling := by
  exact q64_lastObstructionLanding_of_productFirewallTransportClosure hbreaker
    (fun hfirewall =>
      q64_productFirewallTransportClosure_of_transportReduction_and_subqTrap
        (htransport hfirewall) htrap)
    hexits.1 hexits.2

/--
The product-firewall proof certificate supplies the last-obstruction landing surface.
-/
theorem q64_lastObstructionLanding_of_productFirewallProofCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize : TransportFailure → ℕ}
    (hcert :
      Q64ProductFirewallProofCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize) :
    Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling := by
  exact q64_lastObstructionLanding_of_transportReduction_and_subqTrap hcert.breaker hcert.transport
    hcert.trap hcert.exits

/--
The failed-transport marker-data version of the product-firewall certificate supplies the
last-obstruction landing surface.
-/
theorem q64_lastObstructionLanding_of_productFirewallProofDataCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hcert :
      Q64ProductFirewallProofDataCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize packetSize) :
    Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling := by
  exact q64_lastObstructionLanding_of_productFirewallProofCertificate
    (q64_productFirewallProofCertificate_of_dataCertificate hcert)

/--
Product-firewall closure of q-marker carrier/marker coupling, in the exact form stated in the notes:
static split-quotient exhaustion leaves only the product firewall; a failed transport would create a
nonempty marker inside a proper packet of size `< q`, while the low-set congruence makes that marker
`0 [MOD q]`; hence failure is impossible and the remaining ordered-boundary/local-exit branches give
the required q-marker outcome.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingData
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hdata :
      Q64ProductFirewallQMarkerCouplingData q FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
        AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  intro hskew
  rcases hdata.splitQuotient hskew with ⟨hzero, hfirewall, hpack⟩
  have htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize :=
    q64_productFirewallTransportTrap_of_failedTransportSubqMarkerData hdata.subqMarkerData
  have hclosure :
      Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow LocalExit :=
    q64_productFirewallTransportClosure_of_transportReduction_and_subqTrap
      (hdata.transport hfirewall) htrap
  rcases hclosure (hdata.breaker hzero hfirewall hpack) with hboundary | hlocal
  · exact hdata.boundary hboundary hskew
  · exact hdata.localExit hlocal hskew

/--
Four-exit product-firewall closure of q-marker carrier/marker coupling, matching Theorem 2.1 in
`proof.md` with the regular-`q`-set branch kept explicit.
-/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallQMarkerCouplingData
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hdata :
      Q64ProductFirewallQMarkerCouplingDataWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet := by
  intro hskew
  rcases hdata.splitQuotient hskew with ⟨hzero, hfirewall, hpack⟩
  have htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize :=
    q64_productFirewallTransportTrap_of_failedTransportSubqMarkerData hdata.subqMarkerData
  have hclosure :
      Q64ProductFirewallTransportClosure AmbientPacketBreaker OrderedBoundaryRow LocalExit :=
    q64_productFirewallTransportClosure_of_transportReduction_and_subqTrap
      (hdata.transport hfirewall) htrap
  rcases hclosure (hdata.breaker hzero hfirewall hpack) with hboundary | hlocal
  · exact hdata.boundary hboundary hskew
  · exact hdata.localExit hlocal hskew

/--
Theorem-G product-firewall closure of q-marker carrier/marker coupling.  The complete-smaller-marker
branch is exactly the proper-submarker exit in the older carrier/marker API.
-/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallTheoremGQMarkerCouplingData
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientHighErrorSplitter OrderedBoundaryRow LocalRegularizingExit
      CompleteSmallerQMarker : Prop}
    (hdata :
      Q64ProductFirewallTheoremGQMarkerCouplingDataWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientHighErrorSplitter OrderedBoundaryRow
        LocalRegularizingExit CompleteSmallerQMarker) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet := by
  intro hskew
  rcases hdata.splitQuotient hskew with ⟨hzero, hfirewall, hpack⟩
  rcases hdata.theoremG (hdata.splitter hzero hfirewall hpack) with
    hboundary | hsmall | hlocal
  · exact hdata.boundary hboundary hskew
  · exact Or.inl (hdata.smallerMarker hsmall)
  · exact hdata.localExit hlocal hskew

/-- Audit-level Theorem-G product-firewall closure of q-marker carrier/marker coupling. -/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallTheoremGQMarkerCouplingAudit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientHighErrorSplitter OrderedBoundaryRow LocalRegularizingExit
      CompleteSmallerQMarker : Prop}
    (h :
      Q64ProductFirewallTheoremGQMarkerCouplingAuditWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientHighErrorSplitter OrderedBoundaryRow
        LocalRegularizingExit CompleteSmallerQMarker) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet := by
  exact
    q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallTheoremGQMarkerCouplingData
      (q64_productFirewallTheoremGQMarkerCouplingDataWithRegularQSet_of_audit h)

/--
Component-level product-firewall closure of q-marker carrier/marker coupling.  This is the same
claim as `q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingData`, but its hypotheses
are exactly the three failed-transport subclaims rather than the packed sub-`q` marker-data field.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingComponents
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingComponents q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  exact q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingData
    (q64_productFirewallQMarkerCouplingData_of_components h)

/-- Four-exit component-level product-firewall closure of q-marker carrier/marker coupling. -/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallQMarkerCouplingComponents
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingComponentsWithRegularQSet q FullySkewSplitter
        ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom
        ProductFirewall WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet := by
  exact q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallQMarkerCouplingData
    (q64_productFirewallQMarkerCouplingDataWithRegularQSet_of_components h)

/--
Fully componentized product-firewall closure of q-marker carrier/marker coupling.  This exposes both
the static split-quotient audit components and the failed-transport trap components.
-/
theorem q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingAudit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingAudit q FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
        AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit := by
  exact q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingComponents
    (q64_productFirewallQMarkerCouplingComponents_of_audit h)

/-- Four-exit fully componentized product-firewall closure of q-marker carrier/marker coupling. -/
theorem q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallQMarkerCouplingAudit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit RegularQSet
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingAuditWithRegularQSet q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit RegularQSet MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize) :
    Q64QMarkerCarrierMarkerCouplingWithRegularQSet FullySkewSplitter ProperSubmarker
      PrimeModuleExit ClosedLocalExit RegularQSet := by
  exact q64_qMarkerCarrierMarkerCouplingWithRegularQSet_of_productFirewallQMarkerCouplingComponents
    (q64_productFirewallQMarkerCouplingComponentsWithRegularQSet_of_audit h)

/-- The final obstruction landing surface directly supplies the older carrier/marker coupling API. -/
theorem q64_qMarkerCarrierMarkerCoupling_of_lastObstructionLanding
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit : Prop}
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit))
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
      ClosedLocalExit :=
  hlanding hzero hfirewall hpack

/-- Divisor-selection arithmetic: choosing `h` vertices from each of `q / h` cliques gives `q`. -/
theorem q64_divisor_selection_total {q h : ℕ} (hdvd : h ∣ q) : h * (q / h) = q := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel hdvd

/--
The frozen-cluster extraction count from the large-marker audit: choosing `gcd(s,q)` vertices from
each of `q/gcd(s,q)` equal-size cliques gives exactly `q` vertices.
-/
theorem q64_gcd_cluster_selection_total (q s : ℕ) :
    Nat.gcd s q * (q / Nat.gcd s q) = q :=
  q64_divisor_selection_total (Nat.gcd_dvd_right s q)

/-- The selected slice size `gcd(s,q)` is positive whenever the clique size is positive. -/
theorem q64_gcd_cluster_slice_pos {q s : ℕ} (hs : 0 < s) :
    0 < Nat.gcd s q :=
  Nat.gcd_pos_of_pos_left q hs

/--
Two-packet compensator arithmetic.  If `a>b`, `a+b=q`, and the compensator size is half the gap,
then the selected larger-clique slice and the smaller-plus-compensator slice have the same size and
the total selected size is `q`.
-/
theorem q64_twoPacket_compensator_arithmetic {q a b t : ℕ}
    (hsum : a + b = q) (hgap : a = b + 2 * t) :
    a - t = b + t ∧ (a - t) + b + t = q ∧ (a - t) - 1 = (b + t) - 1 := by
  omega

/--
The one-sided two-clique quotient has the advertised necessary arithmetic: if a regular selection
uses `alpha,beta,gamma` vertices from the large clique, small clique, and one-sided compensator
packet, then the selection equations force `beta+gamma=b+t`; if at most all `b` small-clique vertices
are selected, the compensator packet must have size at least the half-excess `t`.
-/
theorem q64_twoPacket_compensator_necessary_arithmetic {q a b t alpha beta gamma : ℕ}
    (hsum : a + b = q) (hgap : a = b + 2 * t)
    (hdegree : alpha = beta + gamma) (htotal : alpha + beta + gamma = q)
    (hbeta : beta ≤ b) :
    beta + gamma = b + t ∧ t ≤ gamma := by
  omega

/--
The `q=8`, `K₅ ⊔ K₃` audit warning: it is a genuine exact zero-sum two-packet pattern, and the
one-vertex compensator is exactly half the size gap.
-/
theorem q64_q8_K5_K3_zero_sum_and_compensator_arithmetic :
    (5 + 3) % 8 = 0 ∧ 5 % 8 ≠ 0 ∧ 3 % 8 ≠ 0 ∧
      5 = 3 + 2 * 1 ∧ 5 - 1 = 3 + 1 ∧ (5 - 1) + 3 + 1 = 8 := by
  norm_num

/--
The static `K_{q-2} ⊔ K₂` plus independent compensators pattern cannot be closed by the same
one-sided regular-selection arithmetic for even `q ≥ 8`: the required equation would force
`q = 2y+2` with `y ≤ 2`.
-/
theorem q64_KqMinus2_K2_independent_compensator_selection_impossible
    {q x y z : ℕ} (hq : 8 ≤ q) (hy : y ≤ 2)
    (hz : z = 1) (hx : x = y + 1) (htotal : x + y + z = q) : False := by
  omega

/--
The no-q-jump endpoint closes a simultaneous wall block once the four listed alternatives are known
impossible.
-/
theorem q64_no_simultaneousWallBlock_of_noQJump
    {SimultaneousWallBlock RegularQSet LocalExit SmallerCompleteMarker ZeroSumPacketAtom : Prop}
    (hjump :
      Q64LargeMarkerNoQJumpTheorem SimultaneousWallBlock RegularQSet LocalExit
        SmallerCompleteMarker ZeroSumPacketAtom)
    (hnoReg : ¬ RegularQSet) (hnoLocal : ¬ LocalExit)
    (hnoSmall : ¬ SmallerCompleteMarker) (hnoZero : ¬ ZeroSumPacketAtom) :
    ¬ SimultaneousWallBlock := by
  intro hwall
  rcases hjump hwall with hreg | hlocal | hsmall | hzero
  · exact hnoReg hreg
  · exact hnoLocal hlocal
  · exact hnoSmall hsmall
  · exact hnoZero hzero

/--
Pointwise weighted carry reduction: a weighted primitive boundary contributes no new local geometry;
some support representative hits the same marked two-class / q-marker endpoint.
-/
def Q64WeightedCarryPointwiseReduction
    (WeightedBoundary RepresentativeHostBoundary : Prop) : Prop :=
  WeightedBoundary → RepresentativeHostBoundary

/--
Final audited dependency chain: everything after the low-set update remains conditional on
carrier/marker coupling.
-/
def Q64FinalAuditConditionalChain
    (CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      BetaVanishes GlobalBridge : Prop) : Prop :=
  CarrierMarkerCoupling →
    PrimeCycleBreaker ∧ SignLaw ∧ OneCornerLift ∧ CompensatorRouting ∧ BetaVanishes ∧ GlobalBridge

/--
Component form of the final audit chain: each post-coupling theorem is provided as its own
constructor, rather than hidden inside one large conjunction-valued function.
-/
structure Q64FinalAuditComponentChain
    (CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      BetaVanishes GlobalBridge : Prop) : Prop where
  primeCycleBreaker : CarrierMarkerCoupling → PrimeCycleBreaker
  signLaw : CarrierMarkerCoupling → SignLaw
  oneCornerLift : CarrierMarkerCoupling → OneCornerLift
  compensatorRouting : CarrierMarkerCoupling → CompensatorRouting
  betaVanishes : CarrierMarkerCoupling → BetaVanishes
  globalBridge : CarrierMarkerCoupling → GlobalBridge

/-- The component final-audit chain assembles to the conjunction-valued final audit chain. -/
theorem q64_finalAuditConditionalChain_of_components
    {CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      BetaVanishes GlobalBridge : Prop}
    (h :
      Q64FinalAuditComponentChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw
        OneCornerLift CompensatorRouting BetaVanishes GlobalBridge) :
    Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge := by
  intro hcouple
  exact ⟨h.primeCycleBreaker hcouple, h.signLaw hcouple, h.oneCornerLift hcouple,
    h.compensatorRouting hcouple, h.betaVanishes hcouple, h.globalBridge hcouple⟩

/--
Once the last obstruction landing proof supplies carrier/marker coupling, the already-audited final
chain gives all downstream endgame outputs.
-/
theorem q64_finalAudit_of_lastObstructionLanding
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge)
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    PrimeCycleBreaker ∧ SignLaw ∧ OneCornerLift ∧ CompensatorRouting ∧ BetaVanishes ∧
      GlobalBridge :=
  hchain (hlanding hzero hfirewall hpack)

/--
One Lean-facing certificate for the strongest claimed final-proof route in the notes: the zero-sum
atom is present, the product-firewall and weighted-quotient packages are present, the landing proof
turns them into carrier/marker coupling, and the final audit chain turns that coupling into the
global bridge.
-/
def Q64ClaimedFinalProofCertificate
    (MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop) :
    Prop :=
  MarkerSplittingZeroSumAtom ∧ ProductFirewall ∧ WeightedQuotientPackaging ∧
    Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling ∧
    Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge

/-- The claimed final-proof certificate extracts the exact global bridge needed downstream. -/
theorem q64_globalBridge_of_claimedFinalProofCertificate
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    GlobalBridge := by
  rcases hcert with ⟨hzero, hfirewall, hpack, hlanding, hchain⟩
  exact (hchain (hlanding hzero hfirewall hpack)).2.2.2.2.2

/-- The claimed final-proof certificate also extracts the dyadic beta-vanishing component. -/
theorem q64_betaVanishes_of_claimedFinalProofCertificate
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    BetaVanishes := by
  rcases hcert with ⟨hzero, hfirewall, hpack, hlanding, hchain⟩
  exact (hchain (hlanding hzero hfirewall hpack)).2.2.2.2.1

/--
The product-firewall sub-`q` transport trap supplies the landing component of the claimed
final-proof certificate, once the ordered-boundary and local-exit branches are known to imply
carrier/marker coupling.
-/
theorem q64_claimedFinalProofCertificate_of_productFirewallTransportTrap
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging)
    (hbreaker :
      MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
        AmbientPacketBreaker)
    (hreduce : AmbientPacketBreaker → OrderedBoundaryRow ∨ LocalExit ∨ TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize)
    (hboundary : OrderedBoundaryRow → CarrierMarkerCoupling)
    (hlocal : LocalExit → CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge := by
  refine ⟨hzero, hfirewall, hpack, ?_, hchain⟩
  exact q64_lastObstructionLanding_of_productFirewallTransportClosure hbreaker
    (fun _ => q64_productFirewallTransportClosure_of_subqTrap hreduce htrap)
    hboundary hlocal

/--
Named transport-reduction version of the final-proof certificate constructor.  This is the
product-firewall certificate surface closest to the notes: pre-trap transport gives
ordered-boundary, local-exit, or failure; the sub-`q` trap kills failure; both exits feed
carrier/marker coupling.
-/
theorem q64_claimedFinalProofCertificate_of_transportReduction_and_subqTrap
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging)
    (hbreaker :
      MarkerSplittingZeroSumAtom → ProductFirewall → WeightedQuotientPackaging →
        AmbientPacketBreaker)
    (htransport :
      ProductFirewall →
        Q64ProductFirewallTransportReduction AmbientPacketBreaker OrderedBoundaryRow LocalExit
          TransportFailure)
    (htrap : Q64ProductFirewallTransportTrap q TransportFailure markerSize)
    (hexits :
      Q64BoundaryExitCarrierMarkerCoupling OrderedBoundaryRow LocalExit CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge := by
  refine ⟨hzero, hfirewall, hpack, ?_, hchain⟩
  exact q64_lastObstructionLanding_of_transportReduction_and_subqTrap hbreaker htransport htrap
    hexits

/--
The named product-firewall proof certificate is a direct constructor for the claimed final-proof
certificate once the final audit chain is available.
-/
theorem q64_claimedFinalProofCertificate_of_productFirewallProofCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hcert :
      Q64ProductFirewallProofCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge := by
  refine ⟨hcert.zero, hcert.firewall, hcert.packaging, ?_, hchain⟩
  exact q64_lastObstructionLanding_of_productFirewallProofCertificate hcert

/--
The failed-transport marker-data product-firewall certificate is a direct constructor for the
claimed final-proof certificate once the final audit chain is available.
-/
theorem q64_claimedFinalProofCertificate_of_productFirewallProofDataCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes GlobalBridge : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hcert :
      Q64ProductFirewallProofDataCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes GlobalBridge) :
    Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
      WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
      CompensatorRouting BetaVanishes GlobalBridge := by
  exact q64_claimedFinalProofCertificate_of_productFirewallProofCertificate
    (q64_productFirewallProofCertificate_of_dataCertificate hcert) hchain

/--
The fixed peeled-package theorem: the two successor transports induce the same anchored package,
unless one successor edge has already coalesced to the Section-40 catalogue.
-/
def Q64FirstReturnFixedPeeledPackageTheorem
    (CommonPackage SuccessorCoalesced : Prop) : Prop :=
  CommonPackage ∨ SuccessorCoalesced

/--
Active-packet preservation for the same-side holonomy branch: the first boundary of a
prime-shell distinguisher must keep the active packet, or it already localizes to Section 40 /
the balanced flip.
-/
def Q64ActivePacketPreservation
    (BoundaryDistinguisher PreservesActivePacket Section40Exit BalancedFlipQuartet : Prop) : Prop :=
  BoundaryDistinguisher → PreservesActivePacket ∨ Section40Exit ∨ BalancedFlipQuartet

/--
First-return two-shadow theorem surface: ambient binary-cylinder membership produces the two fixed
successor shadows, and the nonempty shadow case either intersects or is exactly the fully skew
successor-side positive-AND atom.
-/
def Q64FirstReturnTwoShadowTheorem
    (AmbientCylinderMembership ShadowHLift ShadowJLift ShadowsIntersect
      FullySkewPositiveAND : Prop) : Prop :=
  AmbientCylinderMembership →
    ShadowHLift ∧ ShadowJLift ∧ (ShadowsIntersect ∨ FullySkewPositiveAND)

/--
If positive-AND squares are excluded, first-return two-shadow production gives a common shadow.
-/
theorem q64_commonShadow_of_firstReturnTwoShadow
    {AmbientCylinderMembership ShadowHLift ShadowJLift ShadowsIntersect FullySkewPositiveAND : Prop}
    (htwo :
      Q64FirstReturnTwoShadowTheorem AmbientCylinderMembership ShadowHLift ShadowJLift
        ShadowsIntersect FullySkewPositiveAND)
    (hnoAND : ¬ FullySkewPositiveAND) (hamb : AmbientCylinderMembership) :
    ShadowsIntersect := by
  rcases htwo hamb with ⟨_, _, hinter | hand⟩
  · exact hinter
  · exact False.elim (hnoAND hand)

/--
The reduction circle from `proof.md`: excluding the fully skew positive-AND square, proving common
fixed-package shadow routing, proving dirty shared-slack absorption, and proving Theorem G are
treated as equivalent theorem surfaces.
-/
def Q64PositiveANDTransportGapEquivalence
    (NoPositiveAND CommonShadowRouting DirtySharedSlackAbsorption TheoremG : Prop) : Prop :=
  (NoPositiveAND ↔ CommonShadowRouting) ∧
    (CommonShadowRouting ↔ DirtySharedSlackAbsorption) ∧
      (DirtySharedSlackAbsorption ↔ TheoremG)

/-- Common-shadow routing closes Theorem G through the audited positive-AND reduction circle. -/
theorem q64_theoremG_of_commonShadowRouting
    {NoPositiveAND CommonShadowRouting DirtySharedSlackAbsorption TheoremG : Prop}
    (heq :
      Q64PositiveANDTransportGapEquivalence NoPositiveAND CommonShadowRouting
        DirtySharedSlackAbsorption TheoremG)
    (hshadow : CommonShadowRouting) :
    TheoremG :=
  heq.2.2.mp (heq.2.1.mp hshadow)

/-- Excluding positive-AND also closes Theorem G through the same reduction circle. -/
theorem q64_theoremG_of_noPositiveAND
    {NoPositiveAND CommonShadowRouting DirtySharedSlackAbsorption TheoremG : Prop}
    (heq :
      Q64PositiveANDTransportGapEquivalence NoPositiveAND CommonShadowRouting
        DirtySharedSlackAbsorption TheoremG)
    (hno : NoPositiveAND) :
    TheoremG :=
  q64_theoremG_of_commonShadowRouting heq (heq.1.mp hno)

/--
The conditional host route from proof.md: failed-row acyclicity plus transverse-breaker routing
fills the support-local fourth corner and yields the three downstream host-frontier consequences.
-/
def Q64SupportLocalFourthCornerRoute
    (FailedRowAcyclicity TransverseBreakerRouting FourthCornerFilling SilentEdgeExclusion
      OutgoingNoSplit PairChamberSeparation : Prop) : Prop :=
  FailedRowAcyclicity → TransverseBreakerRouting →
    FourthCornerFilling ∧ SilentEdgeExclusion ∧ OutgoingNoSplit ∧ PairChamberSeparation

/-- Pair-chamber separation is downstream of the conditional support-local fourth-corner route. -/
theorem q64_pairChamberSeparation_of_supportLocalFourthCornerRoute
    {FailedRowAcyclicity TransverseBreakerRouting FourthCornerFilling SilentEdgeExclusion
      OutgoingNoSplit PairChamberSeparation : Prop}
    (hroute :
      Q64SupportLocalFourthCornerRoute FailedRowAcyclicity TransverseBreakerRouting
        FourthCornerFilling SilentEdgeExclusion OutgoingNoSplit PairChamberSeparation)
    (hacyclic : FailedRowAcyclicity) (htransverse : TransverseBreakerRouting) :
    PairChamberSeparation :=
  (hroute hacyclic htransverse).2.2.2

/--
Dyadic two-child carry reduction: a primitive mixed carry must be localized to a common package,
become a successor-side `0001` endpoint, expose a one-corner lift failure, or produce a
homogeneous child obstruction.
-/
def Q64DyadicTwoChildCarryReduction
    (PrimitiveCarry CommonShadowPackage SuccessorSide0001 OneCornerLiftFailure
      HomogeneousChildObstruction : Prop) : Prop :=
  PrimitiveCarry →
    CommonShadowPackage ∨ SuccessorSide0001 ∨ OneCornerLiftFailure ∨ HomogeneousChildObstruction

/--
If every non-common-package branch is excluded, the two-child carry reduction gives package equality.
-/
theorem q64_commonPackage_of_dyadicTwoChildCarryReduction
    {PrimitiveCarry CommonShadowPackage SuccessorSide0001 OneCornerLiftFailure
      HomogeneousChildObstruction : Prop}
    (hred :
      Q64DyadicTwoChildCarryReduction PrimitiveCarry CommonShadowPackage SuccessorSide0001
        OneCornerLiftFailure HomogeneousChildObstruction)
    (hno0001 : ¬ SuccessorSide0001) (hnoLift : ¬ OneCornerLiftFailure)
    (hnoChild : ¬ HomogeneousChildObstruction) (hcarry : PrimitiveCarry) :
    CommonShadowPackage := by
  rcases hred hcarry with hcommon | h0001 | hlift | hchild
  · exact hcommon
  · exact False.elim (hno0001 h0001)
  · exact False.elim (hnoLift hlift)
  · exact False.elim (hnoChild hchild)

/--
Endpoint mass has only the two noncircular closing routes identified in proof.md: a pointwise sign
law or paired-compensator routing with unary leaks absorbed in the same package.
-/
def Q64EndpointMassClosingRoutes
    (EndpointMass PointwiseSignLaw PairedCompensatorWithUnaryLeaks : Prop) : Prop :=
  EndpointMass → PointwiseSignLaw ∨ PairedCompensatorWithUnaryLeaks

/--
Full residual compensator routing: a first-return `0001` row either coalesces into Section 40, or
has a routed `0111` compensator in the same peeled package with unary residuals absorbed.
-/
def Q64PairedCompensatorFullResidualRouting
    (Positive0001 Coalesces Has0111Compensator SamePeeledPackage UnaryResidualAbsorbed : Prop) :
    Prop :=
  Positive0001 →
    Coalesces ∨ (Has0111Compensator ∧ SamePeeledPackage ∧ UnaryResidualAbsorbed)

/-- Full residual compensator routing implies the older endpoint-mass alternative. -/
theorem q64_endpointMassAlternative_of_fullResidualCompensator
    {Positive0001 Coalesces Has0111Compensator SamePeeledPackage UnaryResidualAbsorbed
      PointwiseSignLaw PairedCompensatorRouting : Prop}
    (hfull :
      Q64PairedCompensatorFullResidualRouting Positive0001 Coalesces Has0111Compensator
        SamePeeledPackage UnaryResidualAbsorbed)
    (hcoalesced : Coalesces → PointwiseSignLaw)
    (hpaired :
      Has0111Compensator → SamePeeledPackage → UnaryResidualAbsorbed →
        PairedCompensatorRouting)
    (hpos : Positive0001) :
    Q64EndpointMassAlternative PointwiseSignLaw PairedCompensatorRouting := by
  rcases hfull hpos with hcoal | hcomp
  · exact Or.inl (hcoalesced hcoal)
  · exact Or.inr (hpaired hcomp.1 hcomp.2.1 hcomp.2.2)

omit [Fintype U] in
/--
If the first-return fixed-package theorem supplies a common package and the ambient-to-fixed lift
gives one successor shadow, then the two shadow predicates are equal and hence intersect.
-/
theorem q64_twoShadow_intersection_of_nonempty_of_eq
    {Sh_H Sh_J : Finset U} (hH : Sh_H.Nonempty) (heq : Sh_H = Sh_J) :
    Q64TwoShadowIntersection Sh_H Sh_J := by
  rcases hH with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [Finset.mem_inter]
  exact ⟨hx, by simpa [← heq] using hx⟩

/-- The equivalence package projects trace coalescence to two-fiber overlap. -/
theorem q64_twoFiberOverlap_of_binaryEndpointEquivalence
    {TraceCoalescence CommonShadow SharedSliceAdmissible TwoFiberOverlap : Prop}
    (heq :
      Q64BinaryEndpointEquivalence TraceCoalescence CommonShadow SharedSliceAdmissible
        TwoFiberOverlap)
    (htrace : TraceCoalescence) :
    TwoFiberOverlap := by
  exact heq.2.2.mp (heq.2.1.mp (heq.1.mp htrace))

/-- The equivalence package also transports two-fiber overlap back to trace coalescence. -/
theorem q64_traceCoalescence_of_binaryEndpointEquivalence
    {TraceCoalescence CommonShadow SharedSliceAdmissible TwoFiberOverlap : Prop}
    (heq :
      Q64BinaryEndpointEquivalence TraceCoalescence CommonShadow SharedSliceAdmissible
        TwoFiberOverlap)
    (hoverlap : TwoFiberOverlap) :
    TraceCoalescence := by
  exact heq.1.mpr (heq.2.1.mpr (heq.2.2.mpr hoverlap))

/--
If the corrected q-marker coupling is available and neither a proper submarker nor a module/closed
exit is possible, then the fully skew splitter branch is impossible.
-/
theorem q64_no_fullySkewSplitter_of_qMarkerCoupling
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit : Prop}
    (hcouple :
      Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit)
    (hnoSub : ¬ ProperSubmarker) (hnoModule : ¬ PrimeModuleExit)
    (hnoClosed : ¬ ClosedLocalExit) :
    ¬ FullySkewSplitter := by
  intro hskew
  rcases hcouple hskew with hsub | hmodule | hclosed
  · exact hnoSub hsub
  · exact hnoModule hmodule
  · exact hnoClosed hclosed

/--
If a low-set update changes `|L|` by `|R|` but preserves the residue modulo `q`, then the marker
size `|R|` is divisible by `q`.
-/
theorem q64_marker_mod_eq_zero_of_lowSet_update
    {q low marker : ℕ} (hmarker : marker ≤ low)
    (hmod : (low - marker) % q = low % q) :
    marker % q = 0 := by
  have hmodeq : (low - marker) ≡ low [MOD q] := hmod
  have hsuble : low - marker ≤ low := Nat.sub_le low marker
  have hdiv : q ∣ low - (low - marker) := (Nat.modEq_iff_dvd' hsuble).mp hmodeq
  have hdiff : low - (low - marker) = marker := by omega
  rw [hdiff] at hdiv
  exact Nat.dvd_iff_mod_eq_zero.mp hdiv

/-- A nonzero marker of size below `q` cannot have residue `0` modulo `q`. -/
theorem q64_subq_marker_eq_zero_of_mod_eq_zero
    {q marker : ℕ} (hlt : marker < q) (hmod : marker % q = 0) : marker = 0 := by
  rw [Nat.mod_eq_of_lt hlt] at hmod
  exact hmod

/-- A positive marker below `q` cannot have marker size congruent to `0` modulo `q`. -/
theorem q64_no_positive_subq_marker
    {q marker : ℕ} (hpos : 0 < marker) (hlt : marker < q) (hmod : marker % q = 0) :
    False := by
  have hzero : marker = 0 := q64_subq_marker_eq_zero_of_mod_eq_zero hlt hmod
  omega

/--
Budget-one absorption normal form from the dirty shared-slack audit: after coalesced and clean
marked-add exits, every surviving successor-side `0001` square is the dirty `Abs(1)` boundary.
-/
def Q64BudgetOneAbsorptionNormalForm
    (Positive0001 CoalescedSuccessor CleanMarkedAdd DirtyAbs1Boundary : Prop) : Prop :=
  Positive0001 → CoalescedSuccessor ∨ CleanMarkedAdd ∨ DirtyAbs1Boundary

/--
Same-defect singleton reanchor turns are closed by the shifted same-trace / false-clone endpoint, by
a completer, or by the already recorded Section-40 catalogue.
-/
def Q64SameDefectReanchorClosure
    (SameDefectTurn SameTraceClone Completer Section40Exit : Prop) : Prop :=
  SameDefectTurn → SameTraceClone ∨ Completer ∨ Section40Exit

/--
Shortest long reanchor cycles have no independent holonomy: after same-defect turns are removed, the
first-return deletion produces a defect-switching shared-slack square.
-/
def Q64LongReanchorCycleReduction
    (ShortestIrreducibleCycle SameDefectTurnClosed DefectSwitchingSharedSlackSquare : Prop) : Prop :=
  ShortestIrreducibleCycle → SameDefectTurnClosed ∨ DefectSwitchingSharedSlackSquare

/--
The local five-vertex audit for a defect-switching square: mixed defect types are local failures, and
same-type squares expose one of the four seed templates before residue packaging.
-/
def Q64DefectSwitchingFiveVertexSeedTable
    (DefectSwitchingSquare MixedLocalFailure P4Seed P5Seed C5Seed HouseSeed : Prop) : Prop :=
  DefectSwitchingSquare → MixedLocalFailure ∨ P4Seed ∨ P5Seed ∨ C5Seed ∨ HouseSeed

/--
Marked two-class localization after the exact low-set update: a shared-slack square either closes
locally, gives a sub-`q` marker, produces an already smaller/closed q-marker exit, or reaches the
fully skew carrier branch.
-/
def Q64MarkedTwoClassQMarkerLocalization
    (SharedSlackSquare LocalClosedExit SubQMarker ProperSubmarker PrimeModuleExit ClosedLocalExit
      FullySkewSplitter : Prop) : Prop :=
  SharedSlackSquare →
    LocalClosedExit ∨ SubQMarker ∨ ProperSubmarker ∨ PrimeModuleExit ∨ ClosedLocalExit ∨
      FullySkewSplitter

/--
The marked localization theorem, together with corrected carrier/marker coupling, excludes a
shared-slack square once every smaller or local exit is ruled out.
-/
theorem q64_no_sharedSlackSquare_of_markedLocalization_and_qMarkerCoupling
    {SharedSlackSquare LocalClosedExit SubQMarker ProperSubmarker PrimeModuleExit ClosedLocalExit
      FullySkewSplitter : Prop}
    (hloc :
      Q64MarkedTwoClassQMarkerLocalization SharedSlackSquare LocalClosedExit SubQMarker
        ProperSubmarker PrimeModuleExit ClosedLocalExit FullySkewSplitter)
    (hcouple :
      Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit)
    (hnoLocal : ¬ LocalClosedExit) (hnoSubQ : ¬ SubQMarker)
    (hnoProper : ¬ ProperSubmarker) (hnoModule : ¬ PrimeModuleExit)
    (hnoClosed : ¬ ClosedLocalExit) :
    ¬ SharedSlackSquare := by
  intro hsquare
  rcases hloc hsquare with hlocal | hsubq | hproper | hmodule | hclosed | hskew
  · exact hnoLocal hlocal
  · exact hnoSubQ hsubq
  · exact hnoProper hproper
  · exact hnoModule hmodule
  · exact hnoClosed hclosed
  · rcases hcouple hskew with hproper' | hmodule' | hclosed'
    · exact hnoProper hproper'
    · exact hnoModule hmodule'
    · exact hnoClosed hclosed'

/--
Omni-saturated dirty splits repair the side-selection flaw: a dirty split preserves an active side,
falls into the fixed-fiber/Section-40 kernel, or is exactly the fully skew positive-AND square.
-/
def Q64OmniSaturatedDirtySplitPreservation
    (DirtySplit PreservedActiveSide Section40Kernel FullySkewPositiveAND : Prop) : Prop :=
  DirtySplit → PreservedActiveSide ∨ Section40Kernel ∨ FullySkewPositiveAND

/--
Prime no-holonomy is now equivalent to closing the fully skew atom: same-defect and long-cycle turns
reduce every budget-one cycle to the defect-switching shared-slack square.
-/
def Q64PrimeNoHolonomyReduction
    (BudgetOneCycle SameDefectClosed LongCycleReduced DefectSwitchingSharedSlackSquare : Prop) :
    Prop :=
  BudgetOneCycle → SameDefectClosed ∨ LongCycleReduced ∨ DefectSwitchingSharedSlackSquare

/-- The host-side edge-bias functional in the exact one-defect frontier. -/
def q64HostPhi (epsilon : U → ℕ) (W : Finset U) : ℤ :=
  W.sum fun x => (1 : ℤ) - (epsilon x : ℤ)

omit [Fintype U] [DecidableEq U] in
/-- A zero-defect outside vertex gives positive host bias on the singleton subset. -/
theorem q64_hostPhi_singleton_pos_of_zeroEpsilon
    {epsilon : U → ℕ} {x : U} (hzero : epsilon x = 0) :
    0 < q64HostPhi epsilon {x} := by
  simp [q64HostPhi, hzero]

omit [Fintype U] [DecidableEq U] in
/-- Positive host bias on an arbitrary outside subset forces a genuine zero-defect witness. -/
theorem q64_exists_zeroEpsilon_of_positive_hostPhi
    {epsilon : U → ℕ} {W : Finset U} (hphi : 0 < q64HostPhi epsilon W) :
    ∃ x ∈ W, epsilon x = 0 := by
  by_contra hnone
  have hnonpos : q64HostPhi epsilon W ≤ 0 := by
    unfold q64HostPhi
    apply Finset.sum_nonpos
    intro x hx
    have hxne : epsilon x ≠ 0 := by
      intro hzero
      exact hnone ⟨x, hx, hzero⟩
    have hge : 1 ≤ epsilon x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hxne)
    have hge_int : (1 : ℤ) ≤ (epsilon x : ℤ) := by exact_mod_cast hge
    linarith
  exact not_lt_of_ge hnonpos hphi

omit [Fintype U] [DecidableEq U] in
/-- Completer positivity is equivalent to a positive-bias subset in the epsilon normal form. -/
theorem q64_positive_hostPhi_iff_exists_zeroEpsilon
    {epsilon : U → ℕ} :
    (∃ W : Finset U, 0 < q64HostPhi epsilon W) ↔ ∃ x : U, epsilon x = 0 := by
  constructor
  · rintro ⟨W, hW⟩
    rcases q64_exists_zeroEpsilon_of_positive_hostPhi hW with ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨{x}, q64_hostPhi_singleton_pos_of_zeroEpsilon hx⟩

/-- Multiplicity of a unique defect fiber inside a finite outside one-defect set. -/
def q64DefectMultiplicity (O1 : Finset U) (defect : U → U) (u : U) : ℕ :=
  (O1.filter fun x => defect x = u).card

/-- Integer Hall excess for an anchor-supported unique-defect family. -/
def q64AnchorHallExcess (q : ℕ) (mu : U → ℕ) (Y : Finset U) : ℤ :=
  Y.sum fun u => (mu u : ℤ) - ((q - 1 : ℕ) : ℤ)

omit [Fintype U] [DecidableEq U] in
/-- Pointwise fiber bounds imply every anchor-supported Hall excess is nonpositive. -/
theorem q64_anchorHallExcess_nonpos_of_fiber_bounds
    {q : ℕ} {anchor Y : Finset U} {mu : U → ℕ}
    (hY : Y ⊆ anchor) (hbound : ∀ u ∈ anchor, mu u ≤ q - 1) :
    q64AnchorHallExcess q mu Y ≤ 0 := by
  unfold q64AnchorHallExcess
  apply Finset.sum_nonpos
  intro u hu
  have hb : mu u ≤ q - 1 := hbound u (hY hu)
  have hb_int : (mu u : ℤ) ≤ ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hb
  linarith

omit [Fintype U] [DecidableEq U] in
/-- The Hall inequalities collapse back to the pointwise anchor-fiber bounds. -/
theorem q64_fiber_bounds_of_anchorHallExcess_nonpos
    {q : ℕ} {anchor : Finset U} {mu : U → ℕ}
    (hhall : ∀ Y : Finset U, Y ⊆ anchor → q64AnchorHallExcess q mu Y ≤ 0) :
    ∀ u ∈ anchor, mu u ≤ q - 1 := by
  intro u hu
  have hsubset : ({u} : Finset U) ⊆ anchor := by
    intro v hv
    simpa [Finset.mem_singleton.mp hv] using hu
  have hsingle := hhall {u} hsubset
  have hterm : (mu u : ℤ) - ((q - 1 : ℕ) : ℤ) ≤ 0 := by
    simpa [q64AnchorHallExcess] using hsingle
  have hle_int : (mu u : ℤ) ≤ ((q - 1 : ℕ) : ℤ) := by linarith
  exact_mod_cast hle_int

omit [Fintype U] [DecidableEq U] in
/-- Anchor-supported Hall capacity is exactly the family of pointwise multiplicity bounds. -/
theorem q64_anchorHallExcess_nonpos_iff_fiber_bounds
    {q : ℕ} {anchor : Finset U} {mu : U → ℕ} :
    (∀ Y : Finset U, Y ⊆ anchor → q64AnchorHallExcess q mu Y ≤ 0) ↔
      ∀ u ∈ anchor, mu u ≤ q - 1 := by
  constructor
  · exact q64_fiber_bounds_of_anchorHallExcess_nonpos
  · intro hbound Y hY
    exact q64_anchorHallExcess_nonpos_of_fiber_bounds hY hbound

omit [Fintype U] [DecidableEq U] in
/--
If the total anchor-fiber multiplicity exceeds `(q-1)|anchor|`, then some anchor fiber is
overloaded.
-/
theorem q64_exists_overloaded_anchor_fiber_of_sum_gt
    {q : ℕ} {anchor : Finset U} {mu : U → ℕ}
    (hsum : (q - 1) * anchor.card < anchor.sum mu) :
    ∃ u ∈ anchor, q ≤ mu u := by
  by_contra hnone
  have hbound : ∀ u ∈ anchor, mu u ≤ q - 1 := by
    intro u hu
    by_contra hnot
    have hover : q ≤ mu u := by omega
    exact hnone ⟨u, hu, hover⟩
  have hle : anchor.sum mu ≤ anchor.sum (fun _u => q - 1) := by
    apply Finset.sum_le_sum
    intro u hu
    exact hbound u hu
  have hconst : anchor.sum (fun _u => q - 1) = anchor.card * (q - 1) := by
    simp
  rw [hconst, Nat.mul_comm] at hle
  exact not_lt_of_ge hle hsum

/--
One-defect escape surface: if a unique defect is off the anchor, swapping that defect for the
outside vertex preserves the anchored near-regular shell.
-/
def Q64AnchoredOneDefectEscape
    (OneDefectWitness DefectOffAnchor AnchoredNearRegularSwap : Prop) : Prop :=
  OneDefectWitness → DefectOffAnchor → AnchoredNearRegularSwap

/--
Injective multi-swap compatibility is the exact residual host-side bridge once Hall capacity has
collapsed to pointwise anchor-fiber bounds.
-/
def Q64AnchorInjectiveMultiSwapCompatibility
    (InjectiveDefectSubfamily CompatibleTransversal AnchoredNearRegularMultiSwap : Prop) : Prop :=
  InjectiveDefectSubfamily → CompatibleTransversal → AnchoredNearRegularMultiSwap

/--
Residual host absorption after Hall capacity collapses: anchor-supported one-defect fibers require
compatible-transversal positivity, or else the same candidate-switching fourth-corner obstruction
appears.
-/
def Q64CompatibleTransversalPositivityReduction
    (AnchorSupportedOneDefect CompatibleTransversalPositive CandidateSwitchingFourthCorner : Prop) :
    Prop :=
  AnchorSupportedOneDefect → CompatibleTransversalPositive ∨ CandidateSwitchingFourthCorner

/-- Host absorption reaches compatible-transversal positivity unless candidate switching fires. -/
theorem q64_compatibleTransversalPositive_of_no_candidateSwitching
    {AnchorSupportedOneDefect CompatibleTransversalPositive CandidateSwitchingFourthCorner : Prop}
    (hred :
      Q64CompatibleTransversalPositivityReduction AnchorSupportedOneDefect
        CompatibleTransversalPositive CandidateSwitchingFourthCorner)
    (hnoSwitch : ¬ CandidateSwitchingFourthCorner) (hanchor : AnchorSupportedOneDefect) :
    CompatibleTransversalPositive := by
  rcases hred hanchor with hpos | hswitch
  · exact hpos
  · exact False.elim (hnoSwitch hswitch)

/--
Exact host-side frontier after the one-error strip: either completer positivity holds, or all
remaining one-defect witnesses are anchor-supported, pointwise under capacity, and require the
injective multi-swap compatibility theorem.
-/
def Q64ExactHostSideOneDefectFrontier
    (CompleterPositive AnchorSupportedUniqueDefects PointwiseFiberBounds
      InjectiveMultiSwapCompatibility : Prop) : Prop :=
  CompleterPositive ∨
    (AnchorSupportedUniqueDefects ∧ PointwiseFiberBounds ∧ InjectiveMultiSwapCompatibility)

/--
Weighted first-return seed packaging: the dyadic primitive-carry endpoint requires the same
five-vertex seed to be packaged with orbit-size weights, not merely an aggregate cut identity.
-/
def Q64WeightedFiveVertexSeedPackaging
    (WeightedSeed Section40WeightedFrame MarkedTwoClassKernel : Prop) : Prop :=
  WeightedSeed → Section40WeightedFrame ∨ MarkedTwoClassKernel

/--
Primitive-carry splitting after dividing by the common 2-adic factor: an admissible primitive
boundary either preserves the bad cut for descent, exposes a homogeneous suborbit, or lands in the
weighted five-vertex seed kernel.
-/
def Q64PrimitiveCarryBoundarySplitting
    (PrimitiveBoundary PreservesBadCut HomogeneousSuborbit WeightedSeedKernel : Prop) : Prop :=
  PrimitiveBoundary → PreservesBadCut ∨ HomogeneousSuborbit ∨ WeightedSeedKernel

/--
Weighted mixed-trace admissibility is the dyadic avatar of the host breaker theorem: every weighted
mixed-trace breaker either splits while preserving the bad cut, localizes to a closed template, or
returns to the marked q-marker kernel.
-/
def Q64WeightedMixedTraceAdmissibility
    (WeightedMixedTraceBreaker PreservesBadCut ClosedWeightedTemplate MarkedQMarkerKernel : Prop) :
    Prop :=
  WeightedMixedTraceBreaker →
    PreservesBadCut ∨ ClosedWeightedTemplate ∨ MarkedQMarkerKernel

/--
Trace-refinement failed-row acyclicity: the first dirty failed row of a minimal mixed-trace
breaker is admissible, strictly decreases the active support, or reaches terminal outside-row
constancy.
-/
def Q64TraceRefinementFailedRowAcyclicity
    (MixedTraceBreaker AdmissibleBreaker StrictSupportDecrease TerminalConstancy : Prop) : Prop :=
  MixedTraceBreaker → AdmissibleBreaker ∨ StrictSupportDecrease ∨ TerminalConstancy

/--
Transverse-breaker admissibility: a minimal square-transverse breaker either passes the
one-coordinate interval tests, localizes to Section 40, produces a local completer, or its first
failed row gives a smaller square-transverse breaker.
-/
def Q64TransverseBreakerAdmissibility
    (MinimalTransverseBreaker IntervalTestsPass Section40Localization LocalCompleter
      SmallerTransverseBreaker : Prop) : Prop :=
  MinimalTransverseBreaker →
    IntervalTestsPass ∨ Section40Localization ∨ LocalCompleter ∨ SmallerTransverseBreaker

/--
Support-local fourth-corner gate theorem: after transverse-square gate compatibility, the localized
upper-face witness packets are gated/convex and Helly supplies one common witness for the cube face.
-/
def Q64SupportLocalFourthCornerGateTheorem
    (TransverseSquareGateCompatibility GatedPackets CommonWitness FourthCornerFilled : Prop) :
    Prop :=
  TransverseSquareGateCompatibility →
    GatedPackets ∧ CommonWitness ∧ FourthCornerFilled

/--
The three named host atoms are downstream bookkeeping once trace-refinement acyclicity and the
square-breaker routing package are supplied.
-/
def Q64HostAtomsFromSquareBreakerRouting
    (TraceRefinementAcyclicity SquareBreakerRouting HostSilentEdge128 HostOppPair123
      HostOrient115 : Prop) : Prop :=
  TraceRefinementAcyclicity →
    SquareBreakerRouting → HostSilentEdge128 ∧ HostOppPair123 ∧ HostOrient115

/-- Projection of the three original host-frontier atoms from the square-breaker routing package. -/
theorem q64_hostAtoms_of_squareBreakerRouting
    {TraceRefinementAcyclicity SquareBreakerRouting HostSilentEdge128 HostOppPair123
      HostOrient115 : Prop}
    (h :
      Q64HostAtomsFromSquareBreakerRouting TraceRefinementAcyclicity SquareBreakerRouting
        HostSilentEdge128 HostOppPair123 HostOrient115)
    (htrace : TraceRefinementAcyclicity) (hsquare : SquareBreakerRouting) :
    HostSilentEdge128 ∧ HostOppPair123 ∧ HostOrient115 :=
  h htrace hsquare

/--
Bit-by-bit dyadic tail propagation: vanishing of the aggregate `beta_m` class advances dropped-tail
residue constancy from modulus `2^m` to modulus `2^(m+1)`.
-/
def Q64DyadicBetaBitStep
    (BetaVanishesAtBit ResidueConstAtBit ResidueConstAtNextBit : Prop) : Prop :=
  BetaVanishesAtBit → ResidueConstAtBit → ResidueConstAtNextBit

/-- Beta vanishes at every bit below the terminal dyadic height `j`. -/
def Q64AllBetaBitsVanishUpTo (j : ℕ) (BetaVanishesAtBit : ℕ → Prop) : Prop :=
  ∀ m, m < j → BetaVanishesAtBit m

/-- Each beta-vanishing bit step advances residue constancy from `2^m` to `2^(m+1)`. -/
def Q64DyadicBetaBitStepsUpTo
    (j : ℕ) (BetaVanishesAtBit ResidueConstAtBit : ℕ → Prop) : Prop :=
  ∀ m, m < j →
    Q64DyadicBetaBitStep
      (BetaVanishesAtBit m) (ResidueConstAtBit m) (ResidueConstAtBit (m + 1))

/--
Corollary 3.2 in bit-step form: starting from residue constancy modulo `1`, beta-vanishing at
all bits below `j` iterates the one-bit propagation step to residue constancy modulo `2^j`.
-/
theorem q64_dyadicResidueConstAt_of_betaBitStepsUpTo
    {BetaVanishesAtBit ResidueConstAtBit : ℕ → Prop} :
    ∀ {j : ℕ},
      Q64DyadicBetaBitStepsUpTo j BetaVanishesAtBit ResidueConstAtBit →
      Q64AllBetaBitsVanishUpTo j BetaVanishesAtBit →
      ResidueConstAtBit 0 →
      ResidueConstAtBit j
  | 0, _hsteps, _hbeta, hinit => hinit
  | Nat.succ j, hsteps, hbeta, hinit => by
      have hsteps' :
          Q64DyadicBetaBitStepsUpTo j BetaVanishesAtBit ResidueConstAtBit := by
        intro m hm
        exact hsteps m (Nat.lt_trans hm (Nat.lt_succ_self j))
      have hbeta' : Q64AllBetaBitsVanishUpTo j BetaVanishesAtBit := by
        intro m hm
        exact hbeta m (Nat.lt_trans hm (Nat.lt_succ_self j))
      have hresJ : ResidueConstAtBit j :=
        q64_dyadicResidueConstAt_of_betaBitStepsUpTo hsteps' hbeta' hinit
      simpa [Nat.succ_eq_add_one] using
        hsteps j (Nat.lt_succ_self j) (hbeta j (Nat.lt_succ_self j)) hresJ

/--
Dyadic dropped-tail residue propagation packages the iteration of the bit step through all bits of
`q=2^j`.
-/
def Q64DyadicDroppedTailResiduePropagation
    (AllBetaBitsVanish InitialResidueConst FinalDroppedTailResidueConst : Prop) : Prop :=
  AllBetaBitsVanish → InitialResidueConst → FinalDroppedTailResidueConst

/--
The abstract dropped-tail propagation certificate follows from the concrete bit-step induction data
of Corollary 3.2.
-/
theorem q64_dyadicDroppedTailResiduePropagation_of_betaBitStepsUpTo
    {BetaVanishesAtBit ResidueConstAtBit : ℕ → Prop} {j : ℕ}
    (hsteps : Q64DyadicBetaBitStepsUpTo j BetaVanishesAtBit ResidueConstAtBit) :
    Q64DyadicDroppedTailResiduePropagation
      (Q64AllBetaBitsVanishUpTo j BetaVanishesAtBit)
      (ResidueConstAtBit 0) (ResidueConstAtBit j) := by
  intro hbeta hinit
  exact q64_dyadicResidueConstAt_of_betaBitStepsUpTo hsteps hbeta hinit

/-- Constancy of a residue-valued row statistic on the terminal bucket. -/
def Q64ResidueConst {Row : Type*} {q : ℕ} (residue : Row → ZMod q) : Prop :=
  ∀ a b, residue a = residue b

/-- Adding the same exact control-block residue to every row does not change constancy. -/
theorem q64_residueConst_add_const_iff
    {Row : Type*} {q : ℕ} (residue : Row → ZMod q) (c : ZMod q) :
    Q64ResidueConst (fun r => residue r + c) ↔ Q64ResidueConst residue := by
  constructor
  · intro h a b
    have hshift := h a b
    exact add_right_cancel hshift
  · intro h a b
    change residue a + c = residue b + c
    rw [h a b]

/-- The tail-free/small-ambient sanity check: the zero tail has constant residue. -/
theorem q64_residueConst_zero_tail {Row : Type*} {q : ℕ} :
    Q64ResidueConst (fun _ : Row => (0 : ZMod q)) := by
  intro _ _
  rfl

/--
If the internal bucket residue plus the dropped-tail residue is a constant host residue, then
regularity/residue-constancy of the bucket is equivalent to dropped-tail residue constancy.
-/
def Q64DroppedTailFiniteCore {Row : Type*} {q : ℕ}
    (internalResidue tailResidue : Row → ZMod q) (hostResidue : ZMod q) : Prop :=
  ∀ r, internalResidue r + tailResidue r = hostResidue

theorem q64_internalResidueConst_iff_tailResidueConst_of_finiteCore
    {Row : Type*} {q : ℕ} {internalResidue tailResidue : Row → ZMod q}
    {hostResidue : ZMod q}
    (hcore : Q64DroppedTailFiniteCore internalResidue tailResidue hostResidue) :
    Q64ResidueConst internalResidue ↔ Q64ResidueConst tailResidue := by
  constructor
  · intro hint a b
    have hsum : internalResidue a + tailResidue a =
        internalResidue b + tailResidue b := by rw [hcore a, hcore b]
    rw [hint a b] at hsum
    exact add_left_cancel hsum
  · intro htail a b
    have hsum : internalResidue a + tailResidue a =
        internalResidue b + tailResidue b := by rw [hcore a, hcore b]
    rw [htail a b] at hsum
    exact add_right_cancel hsum

/--
For natural degrees below `q`, constancy modulo `q` is exact constancy.  This is the finite bucket
step turning residue constancy of `G[w]` into ordinary regularity.
-/
theorem q64_natConst_of_modConst_of_lt
    {Row : Type*} {q : ℕ} {degree : Row → ℕ}
    (hmod : ∀ a b, degree a % q = degree b % q) (hlt : ∀ a, degree a < q) :
    ∀ a b, degree a = degree b := by
  intro a b
  have ha : degree a % q = degree a := Nat.mod_eq_of_lt (hlt a)
  have hb : degree b % q = degree b := Nat.mod_eq_of_lt (hlt b)
  have hmodab := hmod a b
  rw [ha, hb] at hmodab
  exact hmodab

/--
The `q+1` trap used in the exact-marker audit: if all degrees lie in `[0,q]`, are congruent
modulo `q`, and no `0/q` mixed pair occurs, then they are equal.
-/
theorem q64_natConst_of_modConst_of_le_and_no_zero_top_pair
    {Row : Type*} {q : ℕ} {degree : Row → ℕ}
    (hmod : ∀ a b, degree a % q = degree b % q)
    (hle : ∀ a, degree a ≤ q)
    (hnoMixed : ∀ a b, degree a = 0 → degree b = q → False) :
    ∀ a b, degree a = degree b := by
  intro a b
  by_cases haTop : degree a = q
  · by_cases hbTop : degree b = q
    · rw [haTop, hbTop]
    · have hbLt : degree b < q := lt_of_le_of_ne (hle b) hbTop
      have hmodab := hmod a b
      rw [haTop, Nat.mod_self, Nat.mod_eq_of_lt hbLt] at hmodab
      exact False.elim (hnoMixed b a hmodab.symm haTop)
  · have haLt : degree a < q := lt_of_le_of_ne (hle a) haTop
    by_cases hbTop : degree b = q
    · have hmodab := hmod a b
      rw [Nat.mod_eq_of_lt haLt, hbTop, Nat.mod_self] at hmodab
      exact False.elim (hnoMixed a b hmodab hbTop)
    · have hbLt : degree b < q := lt_of_le_of_ne (hle b) hbTop
      have hmodab := hmod a b
      rw [Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] at hmodab
      exact hmodab

/-- Exact regularity of the internal bucket, represented by its row degrees. -/
def Q64BucketRegularDegree {Row : Type*} (insideDegree : Row → ℕ) : Prop :=
  ∀ a b, insideDegree a = insideDegree b

/-- The chosen control block has one exact row degree on the bucket. -/
def Q64ConstantControlDegree {Row : Type*} (controlDegree : Row → ℕ) : Prop :=
  ∀ a b, controlDegree a = controlDegree b

/-- Exact regularity of the small ambient graph formed from the bucket plus the control block. -/
def Q64ExactSingleControlDegree {Row : Type*}
    (insideDegree controlDegree : Row → ℕ) : Prop :=
  ∀ a b, insideDegree a + controlDegree a = insideDegree b + controlDegree b

/--
Proposition 2.1 in finite arithmetic form: with an exact constant control block, the final
single-control witness condition is equivalent to regularity of the bucket itself.
-/
theorem q64_exactSingleControlDegree_iff_bucketRegular_of_constantControl
    {Row : Type*} {insideDegree controlDegree : Row → ℕ}
    (hcontrol : Q64ConstantControlDegree controlDegree) :
    Q64ExactSingleControlDegree insideDegree controlDegree ↔
      Q64BucketRegularDegree insideDegree := by
  constructor
  · intro hamb a b
    have hsum := hamb a b
    rw [hcontrol a b] at hsum
    exact Nat.add_right_cancel hsum
  · intro hregular a b
    rw [hregular a b, hcontrol a b]

/-- The small-ambient residue is the bucket residue plus the total control-block residue. -/
def Q64SmallAmbientResidueConst {Row : Type*} {q : ℕ}
    (insideResidue blockResidue : Row → ZMod q) : Prop :=
  Q64ResidueConst (fun r => insideResidue r + blockResidue r)

/--
Proposition 4.1 in residue form: if the outside/control blocks have constant residue contribution,
then small-ambient modular regularity is exactly internal modular regularity.
-/
theorem q64_smallAmbientResidueConst_iff_internalResidueConst_of_blockResidueConst
    {Row : Type*} {q : ℕ} {insideResidue blockResidue : Row → ZMod q}
    (hblock : Q64ResidueConst blockResidue) :
    Q64SmallAmbientResidueConst insideResidue blockResidue ↔
      Q64ResidueConst insideResidue := by
  constructor
  · intro hamb a b
    have hsum := hamb a b
    change insideResidue a + blockResidue a = insideResidue b + blockResidue b at hsum
    rw [hblock a b] at hsum
    exact add_right_cancel hsum
  · intro hinside a b
    change insideResidue a + blockResidue a = insideResidue b + blockResidue b
    rw [hinside a b, hblock a b]

/--
Residue-controlled proof-blocks for a partition of the dropped tail: each block contributes a
constant row residue on the terminal bucket.
-/
def Q64TailProofBlockResidueData {Row Block : Type*} [DecidableEq Block] {q : ℕ}
    (blocks : Finset Block) (contribution : Row → Block → ZMod q) : Prop :=
  ∀ B ∈ blocks, Q64ResidueConst (fun r => contribution r B)

/-- Summing residue-controlled proof-blocks gives a constant total dropped-tail residue. -/
theorem q64_tailResidueConst_of_proofBlockResidueData
    {Row Block : Type*} [DecidableEq Block] {q : ℕ}
    {blocks : Finset Block} {contribution : Row → Block → ZMod q}
    (hblocks : Q64TailProofBlockResidueData blocks contribution) :
    Q64ResidueConst (fun r => blocks.sum (fun B => contribution r B)) := by
  intro a b
  apply Finset.sum_congr rfl
  intro B hB
  exact hblocks B hB a b

/--
Finite-core exact-upgrade surface: dropped-tail residue constancy gives bucket regularity, and the
already exact control block then yields the final exact witness.
-/
def Q64FiniteCoreExactUpgrade
    (DroppedTailResidueConst BucketRegular ExactControlBlock FinalExactWitness : Prop) : Prop :=
  DroppedTailResidueConst → BucketRegular → ExactControlBlock → FinalExactWitness

/--
Proof-block residue data is exactly strong enough to feed the finite-core exact-upgrade surface.
-/
theorem q64_finiteCoreExactUpgrade_of_proofBlockResidueData
    {Row Block : Type*} [DecidableEq Block] {q : ℕ}
    {blocks : Finset Block} {contribution : Row → Block → ZMod q}
    {BucketRegular ExactControlBlock FinalExactWitness : Prop}
    (hupgrade :
      Q64FiniteCoreExactUpgrade
        (Q64ResidueConst (fun r => blocks.sum (fun B => contribution r B)))
        BucketRegular ExactControlBlock FinalExactWitness)
    (hblocks : Q64TailProofBlockResidueData blocks contribution)
    (hregular : BucketRegular) (hcontrol : ExactControlBlock) :
    FinalExactWitness :=
  hupgrade (q64_tailResidueConst_of_proofBlockResidueData hblocks) hregular hcontrol

/--
Once the dropped-tail residue is constant, the positive-cost successor external-block bridge is just
the existing terminal regularity/control-block bookkeeping.
-/
def Q64PositiveCostExternalBlockBridgeFromTailResidue
    (DroppedTailResidueConst TerminalRegularQBucket ControlBlockBookkeeping
      PositiveCostExternalBlockBridge : Prop) : Prop :=
  DroppedTailResidueConst →
    TerminalRegularQBucket → ControlBlockBookkeeping → PositiveCostExternalBlockBridge

/--
Propositional wrapper for the latest audit: dyadic beta vanishing plus the terminal bookkeeping
yields the positive-cost external-block bridge.
-/
theorem q64_positiveCostExternalBlockBridge_of_dyadicTail
    {AllBetaBitsVanish InitialResidueConst FinalDroppedTailResidueConst TerminalRegularQBucket
      ControlBlockBookkeeping PositiveCostExternalBlockBridge : Prop}
    (hprop :
      Q64DyadicDroppedTailResiduePropagation AllBetaBitsVanish InitialResidueConst
        FinalDroppedTailResidueConst)
    (hbridge :
      Q64PositiveCostExternalBlockBridgeFromTailResidue FinalDroppedTailResidueConst
        TerminalRegularQBucket ControlBlockBookkeeping PositiveCostExternalBlockBridge)
    (hbeta : AllBetaBitsVanish) (hinit : InitialResidueConst)
    (hterminal : TerminalRegularQBucket) (hbook : ControlBlockBookkeeping) :
    PositiveCostExternalBlockBridge :=
  hbridge (hprop hbeta hinit) hterminal hbook

/--
The dyadic weighted mixed-trace endpoint after the carry audit: weighted splitting plus dirty
shared-slack absorption forces the aggregate `β` obstruction to vanish.
-/
def Q64WeightedMixedTraceCarryAudit
    (Bad Homogeneous : Finset U → Prop) (Boundary PreservesActivePair Localizes : Prop)
    (BetaVanishes : Prop) : Prop :=
  Q64WeightedMixedTraceSplitting Bad Homogeneous →
    Q64DirtySharedSlackAbsorption Boundary PreservesActivePair Localizes →
      BetaVanishes

end DyadicTailOrbitFrontier

end Q64PromotionEndpoint

end RegularInducedSubgraph
