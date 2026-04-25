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

theorem q64_twoFiberSingleFlipOverlap_inter_ne_empty
    {d10 d01 : K → ℕ}
    (hoverlap : Q64TwoFiberSingleFlipOverlap d10 d01)
    (h10 : (q64Omega10 d10).Nonempty) (h01 : (q64Omega01 d01).Nonempty) :
    (q64Omega10 d10 ∩ q64Omega01 d01) ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (hoverlap h10 h01)

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

/-- Natural packet weight used in the clique-quotient audit. -/
def q64PacketWeight (cliqueSize cliqueCount : ℕ) : ℕ := cliqueCount * cliqueSize

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
turns them into carrier/marker coupling, and the final audit chain turns carrier/marker coupling into
the global bridge.
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
The product-firewall sub-`q` transport trap supplies the landing component of the claimed final-proof
certificate, once the ordered-boundary and local-exit branches are known to imply carrier/marker
coupling.
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
product-firewall certificate surface closest to the notes: pre-trap transport gives ordered-boundary,
local-exit, or failure; the sub-`q` trap kills failure; both exits feed carrier/marker coupling.
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
The failed-transport marker-data product-firewall certificate is a direct constructor for the claimed
final-proof certificate once the final audit chain is available.
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
Active-packet preservation for the same-side holonomy branch: the first boundary of a prime-shell
distinguisher must keep the active packet, or it already localizes to Section 40 / the balanced flip.
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
    (AmbientCylinderMembership ShadowHLift ShadowJLift ShadowsIntersect FullySkewPositiveAND : Prop) :
    Prop :=
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
If the total anchor-fiber multiplicity exceeds `(q-1)|anchor|`, then some anchor fiber is overloaded.
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
One-defect escape surface: if a unique defect is off the anchor, swapping that defect for the outside
vertex preserves the anchored near-regular shell.
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
Trace-refinement failed-row acyclicity: the first dirty failed row of a minimal mixed-trace breaker is
admissible, strictly decreases the active support, or reaches terminal outside-row constancy.
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

/-- Proof-block residue data is exactly strong enough to feed the finite-core exact-upgrade surface. -/
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
Propositional wrapper for the latest audit: dyadic beta vanishing plus the terminal bookkeeping yields
the positive-cost external-block bridge.
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
