import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Rank
import RegularInducedSubgraph.Threshold

namespace RegularInducedSubgraph

section FiniteGraph

open Matrix
open Finset
open scoped BigOperators

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
A fixed-modulus witness of size at least `k`: an induced subgraph on at least `k` vertices whose
degrees are all congruent modulo the specific modulus `q`.
-/
def HasFixedModulusWitnessOfCard (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, k ≤ s.card ∧ InducesModEqDegree G s q

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

lemma hasFixedModulusWitnessOfCard_mono
    (G : SimpleGraph V) {k ℓ q : ℕ} (hkℓ : k ≤ ℓ)
    (hwitness : HasFixedModulusWitnessOfCard G ℓ q) :
    HasFixedModulusWitnessOfCard G k q := by
  rcases hwitness with ⟨s, hℓ, hs⟩
  exact ⟨s, le_trans hkℓ hℓ, hs⟩

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

private def degreeParityVec (G : SimpleGraph V) [DecidableRel G.Adj] : V → ZMod 2 :=
  fun v => (G.degree v : ZMod 2)

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha : a.val < 2 := a.val_lt
  have ha' : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha' with h0 | h1
  · exact Or.inl (a.val_eq_zero.mp h0)
  · exact Or.inr ((ZMod.val_eq_one (by decide) a).mp h1)

private lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · intro ha
    rcases zmod2_eq_zero_or_one a with h0 | h1
    · exact False.elim (ha h0)
    · exact h1
  · rintro rfl h
    exact zero_ne_one h.symm

private lemma zmod2_mul_self_eq (a : ZMod 2) : a * a = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

private lemma sum_zmod2_eq_card_filter_eq_one
    (s : Finset V) (x : V → ZMod 2) :
    ∑ u ∈ s, x u = ↑((s.filter fun u => x u = 1).card) := by
  classical
  rw [← Finset.sum_filter_ne_zero (s := s) (f := fun u => x u)]
  have hfilter : s.filter (fun u => x u ≠ 0) = s.filter (fun u => x u = 1) := by
    ext u
    simp [zmod2_ne_zero_iff_eq_one]
  rw [hfilter]
  calc
    Finset.sum (s.filter fun u => x u = 1) x
        = Finset.sum (s.filter fun u => x u = 1) (fun _ => (1 : ZMod 2)) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp only [Finset.mem_filter] at hu
            simp [hu.2]
    _ = ↑((s.filter fun u => x u = 1).card) := by
          simp

private lemma sum_darts_eq_dotProduct_adj
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    (∑ d : G.Dart, x d.fst * x d.snd) = x ⬝ᵥ (G.adjMatrix (ZMod 2) *ᵥ x) := by
  classical
  calc
    ∑ d : G.Dart, x d.fst * x d.snd
        = ∑ v : V,
            ((Finset.univ.filter fun d : G.Dart => d.fst = v).sum fun d => x d.fst * x d.snd) := by
            symm
            simpa using (Finset.sum_fiberwise_of_maps_to
              (s := (Finset.univ : Finset G.Dart)) (t := (Finset.univ : Finset V))
              (g := fun d : G.Dart => d.fst) (by intro d hd; simp) (fun d => x d.fst * x d.snd))
    _ = ∑ v : V, x v * ∑ u ∈ G.neighborFinset v, x u := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [G.dart_fst_fiber v]
          rw [Finset.sum_image]
          · simpa [SimpleGraph.neighborSet, SimpleGraph.neighborFinset, Finset.mul_sum] using
              (Finset.sum_toFinset_eq_subtype (fun u : V => G.Adj v u) (fun u => x v * x u)).symm
          · intro a _ b _ hab
            exact G.dartOfNeighborSet_injective v hab
    _ = x ⬝ᵥ (G.adjMatrix (ZMod 2) *ᵥ x) := by
          simp [dotProduct, G.adjMatrix_mulVec_apply, Finset.mul_sum]

private lemma sum_darts_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    (∑ d : G.Dart, x d.fst * x d.snd) = 0 := by
  classical
  simpa using
    (Finset.sum_involution
      (s := (Finset.univ : Finset G.Dart))
      (f := fun d : G.Dart => x d.fst * x d.snd)
      (g := fun d _ => d.symm)
      (by
        intro d hd
        simp [SimpleGraph.Dart.symm, mul_comm]
        rw [← two_mul]
        have h2 : (2 : ZMod 2) = 0 := by decide
        rw [h2, zero_mul])
      (by
        intro d hd hne
        exact d.symm_ne)
      (by
        intro d hd
        simp)
      (by
        intro d hd
        simp))

private lemma dotProduct_adj_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    x ⬝ᵥ (G.adjMatrix (ZMod 2) *ᵥ x) = 0 := by
  rw [← sum_darts_eq_dotProduct_adj (G := G) x, sum_darts_eq_zero (G := G) x]

private lemma dotProduct_lap_eq_degreeParity
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    x ⬝ᵥ (G.lapMatrix (ZMod 2) *ᵥ x) = degreeParityVec G ⬝ᵥ x := by
  rw [SimpleGraph.lapMatrix, sub_mulVec, dotProduct_sub, G.dotProduct_mulVec_degMatrix,
    dotProduct_adj_eq_zero (G := G) x, sub_zero, dotProduct]
  apply Finset.sum_congr rfl
  intro v hv
  rcases zmod2_eq_zero_or_one (x v) with h0 | h1
  · rw [h0]
    simp [degreeParityVec]
  · rw [h1]
    simp [degreeParityVec]

private lemma degreeParity_annihilates_ker
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V → ZMod 2}
    (hx : G.lapMatrix (ZMod 2) *ᵥ x = 0) :
    degreeParityVec G ⬝ᵥ x = 0 := by
  rw [← dotProduct_lap_eq_degreeParity (G := G) x, hx, dotProduct_zero]

private lemma symm_dotProduct_col
    (M : Matrix V V (ZMod 2)) (hM : M.IsSymm) (x : V → ZMod 2) (i : V) :
    x ⬝ᵥ M.col i = (M *ᵥ x) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.col, hM.apply, mul_comm]

private lemma exists_lap_solution
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : V → ZMod 2, G.lapMatrix (ZMod 2) *ᵥ x = degreeParityVec G := by
  let L : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := Matrix.toLin' (G.lapMatrix (ZMod 2))
  have hann : dotProductEquiv (ZMod 2) V (degreeParityVec G) ∈ L.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact degreeParity_annihilates_ker (G := G) (by simpa [L, LinearMap.mem_ker] using hz)
  have hrangeEq : L.dualMap.range = L.ker.dualAnnihilator :=
    LinearMap.range_dualMap_eq_dualAnnihilator_ker L
  have hrange : dotProductEquiv (ZMod 2) V (degreeParityVec G) ∈ L.dualMap.range := by
    rw [hrangeEq]
    exact hann
  rcases LinearMap.mem_range.mp hrange with ⟨ψ, hψ⟩
  let x : V → ZMod 2 := (dotProductEquiv (ZMod 2) V).symm ψ
  have hxpsi : dotProductEquiv (ZMod 2) V x = ψ := by simp [x]
  refine ⟨x, ?_⟩
  ext i
  have hsingle := LinearMap.congr_fun hψ (Pi.single i 1)
  calc
    (G.lapMatrix (ZMod 2) *ᵥ x) i = x ⬝ᵥ (G.lapMatrix (ZMod 2)).col i := by
      exact (symm_dotProduct_col (M := G.lapMatrix (ZMod 2)) (G.isSymm_lapMatrix (ZMod 2)) x i).symm
    _ = ψ (L (Pi.single i 1)) := by
      rw [← hxpsi]
      simp [L]
    _ = degreeParityVec G i := by
      simpa [dotProductEquiv, degreeParityVec] using hsingle

private lemma even_induced_degree_zero_side
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V → ZMod 2}
    (hx : G.lapMatrix (ZMod 2) *ᵥ x = degreeParityVec G)
    (s0 s1 : Finset V)
    (hs0 : s0 = Finset.univ.filter fun v => x v = 0)
    (hs1 : s1 = Finset.univ.filter fun v => x v = 1) :
    ∀ v : ↑(s0 : Set V), Even ((inducedOn G s0).degree v) := by
  intro v
  have hvx : x v = 0 := by simpa [hs0] using v.2
  have hdisj : Disjoint s0 s1 := by
    rw [hs0, hs1]
    refine Finset.disjoint_left.mpr ?_
    intro w hw0 hw1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw0 hw1
    have : False := by simpa [hw0] using hw1
    exact this.elim
  have hunion : s0 ∪ s1 = Finset.univ := by
    rw [hs0, hs1]
    ext w
    constructor
    · intro _
      simp
    · intro _
      simp [zmod2_eq_zero_or_one (x w)]
  have hxv : ∑ u ∈ G.neighborFinset v, x u = degreeParityVec G v := by
    have hxv' := congrFun hx v
    rw [SimpleGraph.lapMatrix_mulVec_apply] at hxv'
    simpa [degreeParityVec, hvx] using hxv'
  have hcard1 : (((G.neighborFinset v ∩ s1).card : ℕ) : ZMod 2) = degreeParityVec G v := by
    have hs1filter :
        G.neighborFinset v ∩ s1 = (G.neighborFinset v).filter fun u => x u = 1 := by
      ext u
      simp [hs1, and_left_comm, and_assoc]
    calc
      (((G.neighborFinset v ∩ s1).card : ℕ) : ZMod 2)
          = ↑(((G.neighborFinset v).filter fun u => x u = 1).card) := by
              simpa [hs1filter]
      _ = ∑ u ∈ G.neighborFinset v, x u := by
            symm
            exact sum_zmod2_eq_card_filter_eq_one (s := G.neighborFinset v) (x := x)
      _ = degreeParityVec G v := hxv
  have hdeg :
      G.degree v = (inducedOn G s0).degree v + (G.neighborFinset v ∩ s1).card := by
    calc
      G.degree v = (G.neighborFinset v ∩ Finset.univ).card := by simp
      _ = (G.neighborFinset v ∩ (s0 ∪ s1)).card := by simpa [hunion]
      _ = (G.neighborFinset v ∩ s0).card + (G.neighborFinset v ∩ s1).card := by
            exact card_neighborFinset_inter_union (G := G) hdisj v
      _ = (inducedOn G s0).degree v + (G.neighborFinset v ∩ s1).card := by
            rw [← degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s0)
              (v := v)]
  have hcast : (((inducedOn G s0).degree v : ℕ) : ZMod 2) = 0 := by
    have hcast' := congrArg (fun n : ℕ => (n : ZMod 2)) hdeg
    have hcancel :
        degreeParityVec G v =
          (((inducedOn G s0).degree v : ℕ) : ZMod 2) + degreeParityVec G v := by
      simpa [degreeParityVec, Nat.cast_add, hcard1, add_comm, add_left_comm, add_assoc] using hcast'
    have hcancel' :
        (((inducedOn G s0).degree v : ℕ) : ZMod 2) + degreeParityVec G v =
          0 + degreeParityVec G v := by
      simpa using hcancel.symm
    exact add_right_cancel hcancel'
  rwa [ZMod.natCast_eq_zero_iff_even] at hcast

private lemma even_induced_degree_one_side
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V → ZMod 2}
    (hx : G.lapMatrix (ZMod 2) *ᵥ x = degreeParityVec G)
    (s1 : Finset V)
    (hs1 : s1 = Finset.univ.filter fun v => x v = 1) :
    ∀ v : ↑(s1 : Set V), Even ((inducedOn G s1).degree v) := by
  intro v
  have hvx : x v = 1 := by simpa [hs1] using v.2
  have hxv : ∑ u ∈ G.neighborFinset v, x u = 0 := by
    have hxv' := congrFun hx v
    rw [SimpleGraph.lapMatrix_mulVec_apply] at hxv'
    have hxv'' : (degreeParityVec G v : ZMod 2) = degreeParityVec G v +
        ∑ u ∈ G.neighborFinset v, x u := by
      simpa [degreeParityVec, hvx, sub_eq_iff_eq_add] using hxv'
    have hcancel :
        degreeParityVec G v + ∑ u ∈ G.neighborFinset v, x u = degreeParityVec G v + 0 := by
      simpa using hxv''.symm
    exact add_left_cancel hcancel
  have hcast : (((inducedOn G s1).degree v : ℕ) : ZMod 2) = 0 := by
    have hs1filter :
        G.neighborFinset v ∩ s1 = (G.neighborFinset v).filter fun u => x u = 1 := by
      ext u
      simp [hs1, and_left_comm, and_assoc]
    rw [degree_inducedOn_eq_card_neighborFinset_inter_modular (G := G) (s := s1) (v := v)]
    calc
      (((G.neighborFinset v ∩ s1).card : ℕ) : ZMod 2)
          = ↑(((G.neighborFinset v).filter fun u => x u = 1).card) := by
              simpa [hs1filter]
      _ = ∑ u ∈ G.neighborFinset v, x u := by
            symm
            exact sum_zmod2_eq_card_filter_eq_one (s := G.neighborFinset v) (x := x)
      _ = 0 := hxv
  rwa [ZMod.natCast_eq_zero_iff_even] at hcast

/--
Gallai's parity theorem: every finite graph contains an induced subgraph on at least half of its
vertices whose degrees are all even.
-/
lemma exists_large_even_induced_subgraph (G : SimpleGraph V) :
    ∃ s : Finset V, Fintype.card V ≤ 2 * s.card ∧
      (by
        classical
        exact ∀ v : ↑(s : Set V), Even ((inducedOn G s).degree v)) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨x, hx⟩ := exists_lap_solution (G := G)
  let s0 : Finset V := Finset.univ.filter fun v => x v = 0
  let s1 : Finset V := Finset.univ.filter fun v => x v = 1
  have hdeg0 :
      ∀ v : ↑(s0 : Set V), Even ((inducedOn G s0).degree v) :=
    even_induced_degree_zero_side (G := G) hx s0 s1 rfl rfl
  have hdeg1 :
      ∀ v : ↑(s1 : Set V), Even ((inducedOn G s1).degree v) :=
    even_induced_degree_one_side (G := G) hx s1 rfl
  have hdisj : Disjoint s0 s1 := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv0 hv1
    simp only [s0, s1, Finset.mem_filter, Finset.mem_univ, true_and] at hv0 hv1
    have : False := by simpa [hv0] using hv1
    exact this.elim
  have hcard : s0.card + s1.card = Fintype.card V := by
    have hunion : s0 ∪ s1 = Finset.univ := by
      ext v
      constructor
      · intro _
        simp
      · intro _
        simp [s0, s1, zmod2_eq_zero_or_one (x v)]
    calc
      s0.card + s1.card = (s0 ∪ s1).card := by
        symm
        exact Finset.card_union_of_disjoint hdisj
      _ = Fintype.card V := by simpa [hunion]
  by_cases hle : s0.card ≤ s1.card
  · refine ⟨s1, ?_, hdeg1⟩
    omega
  · have hle' : s1.card ≤ s0.card := le_of_not_ge hle
    refine ⟨s0, ?_, hdeg0⟩
    omega

/--
The parity base case in fixed-modulus form: every finite graph has an induced subgraph on at least
`|V| / 2` vertices whose degrees are all congruent modulo `2`.
-/
lemma hasFixedModulusWitnessOfCard_two (G : SimpleGraph V) :
    HasFixedModulusWitnessOfCard G (Fintype.card V / 2) 2 := by
  rcases exists_large_even_induced_subgraph (G := G) with ⟨s, hsize, heven⟩
  refine ⟨s, ?_, ?_⟩
  · omega
  · intro v w
    rcases heven v with ⟨a, ha⟩
    rcases heven w with ⟨b, hb⟩
    rw [ha, hb]
    have h0a : a + a ≡ 0 [MOD 2] := by
      simpa [two_mul] using (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 2 a))
    have h0b : b + b ≡ 0 [MOD 2] := by
      simpa [two_mul] using (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 2 b))
    exact h0a.trans h0b.symm

/--
A binary column over a row type `W`. In the dyadic-tail analysis, these model adjacency columns from
the dropped part into the current bucket.
-/
abbrev BinaryColumn (W : Type*) := W → Bool

private abbrev binaryColumnBit (b : Bool) : ℕ := cond b 1 0

/--
The row sum determined by a list of binary columns.
-/
def binaryColumnRowSum {W : Type*} : List (BinaryColumn W) → W → ℕ
  | [], _ => 0
  | c :: cs, w => binaryColumnBit (c w) + binaryColumnRowSum cs w

lemma binaryColumnRowSum_append {W : Type*} (cols₁ cols₂ : List (BinaryColumn W)) :
    ∀ w, binaryColumnRowSum (cols₁ ++ cols₂) w =
      binaryColumnRowSum cols₁ w + binaryColumnRowSum cols₂ w := by
  induction cols₁ with
  | nil =>
      intro w
      simp [binaryColumnRowSum]
  | cons c cs ih =>
      intro w
      simp [binaryColumnRowSum, ih, Nat.add_assoc]

/--
Row-sum version of a binary zero-sum packet: modulo `2`, the packet contributes the same value on
every row.
-/
def IsBinaryZeroSumPacket {W : Type*} (packet : List (BinaryColumn W)) : Prop :=
  ∀ v w, binaryColumnRowSum packet v ≡ binaryColumnRowSum packet w [MOD 2]

/--
A partition of columns into binary zero-sum packets.
-/
def HasBinaryZeroSumPacketPartition {W : Type*} (packets : List (List (BinaryColumn W))) : Prop :=
  ∀ packet ∈ packets, IsBinaryZeroSumPacket packet

/--
Flatten a list of binary packets into a single column list.
-/
def flattenBinaryPackets {W : Type*} (packets : List (List (BinaryColumn W))) :
    List (BinaryColumn W) :=
  packets.foldr List.append []

lemma modEq_rowSum_two_of_hasBinaryZeroSumPacketPartition
    {W : Type*} {packets : List (List (BinaryColumn W))}
    (hpackets : HasBinaryZeroSumPacketPartition packets) :
    ∀ v w, binaryColumnRowSum (flattenBinaryPackets packets) v ≡
      binaryColumnRowSum (flattenBinaryPackets packets) w [MOD 2] := by
  induction packets with
  | nil =>
      intro v w
      simpa [binaryColumnRowSum] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD 2])
  | cons packet packets ih =>
      intro v w
      have hpacket : IsBinaryZeroSumPacket packet := hpackets packet (by simp)
      have hrest : HasBinaryZeroSumPacketPartition packets := by
        intro packet' hmem
        exact hpackets packet' (by simp [hmem])
      have hpacketsMod :
          binaryColumnRowSum (flattenBinaryPackets packets) v ≡
            binaryColumnRowSum (flattenBinaryPackets packets) w [MOD 2] :=
        ih hrest v w
      have hadd :
          binaryColumnRowSum packet v + binaryColumnRowSum (flattenBinaryPackets packets) v ≡
            binaryColumnRowSum packet w + binaryColumnRowSum (flattenBinaryPackets packets) w [MOD 2] := by
        exact Nat.ModEq.add (hpacket v w) hpacketsMod
      simpa [flattenBinaryPackets, binaryColumnRowSum_append] using hadd

/--
Two binary columns are complementary if their pointwise sum is the all-ones column.
-/
def ComplementaryBinaryColumns {W : Type*} (a b : BinaryColumn W) : Prop :=
  ∀ w, a w = !(b w)

/--
One binary compression step: an equal pair compresses to itself, and a complementary pair compresses
to the zero column after removing the constant parity bit.
-/
def DyadicPairCompression {W : Type*} (a b d : BinaryColumn W) : Prop :=
  (a = b ∧ d = a) ∨ (ComplementaryBinaryColumns a b ∧ d = fun _ => false)

/--
One level of dyadic pairing on a list of binary columns.
-/
inductive DyadicPairingStep {W : Type*} :
    List (BinaryColumn W) → List (BinaryColumn W) → Prop
  | nil : DyadicPairingStep [] []
  | cons {a b d cols next} :
      DyadicPairCompression a b d →
      DyadicPairingStep cols next →
      DyadicPairingStep (a :: b :: cols) (d :: next)

/--
A dyadic pairing tree of depth `j`: after `j` successive pairing/compression levels, no columns
remain.
-/
inductive HasDyadicPairingTree {W : Type*} : ℕ → List (BinaryColumn W) → Prop
  | zero : HasDyadicPairingTree 0 []
  | succ {j cols next} :
      DyadicPairingStep cols next →
      HasDyadicPairingTree j next →
      HasDyadicPairingTree (j + 1) cols

private lemma exists_constant_bit_decomposition_of_dyadicPairCompression
    {W : Type*} {a b d : BinaryColumn W} (h : DyadicPairCompression a b d) :
    ∃ ε : ℕ, ∀ w, binaryColumnBit (a w) + binaryColumnBit (b w) = ε + 2 * binaryColumnBit (d w) := by
  rcases h with ⟨hab, hd⟩ | ⟨hcomp, hd⟩
  · refine ⟨0, ?_⟩
    intro w
    rw [hd, ← hab]
    cases hbw : a w <;> simp [binaryColumnBit, hbw]
  · refine ⟨1, ?_⟩
    intro w
    rw [hd]
    cases hbw : b w <;> simp [ComplementaryBinaryColumns, binaryColumnBit, hbw, hcomp w]

private lemma exists_constant_rowSum_decomposition_of_dyadicPairingStep
    {W : Type*} {cols next : List (BinaryColumn W)}
    (h : DyadicPairingStep cols next) :
    ∃ K : ℕ, ∀ w, binaryColumnRowSum cols w = K + 2 * binaryColumnRowSum next w := by
  induction h with
  | nil =>
      refine ⟨0, ?_⟩
      intro w
      simp [binaryColumnRowSum]
  | @cons a b d cols next hpair hstep ih =>
      rcases exists_constant_bit_decomposition_of_dyadicPairCompression hpair with ⟨ε, hε⟩
      rcases ih with ⟨K, hK⟩
      refine ⟨ε + K, ?_⟩
      intro w
      calc
        binaryColumnRowSum (a :: b :: cols) w
            = (binaryColumnBit (a w) + binaryColumnBit (b w)) + binaryColumnRowSum cols w := by
                simp [binaryColumnRowSum, Nat.add_assoc]
        _ = (ε + 2 * binaryColumnBit (d w)) + (K + 2 * binaryColumnRowSum next w) := by
              rw [hε w, hK w]
        _ = (ε + K) + 2 * (binaryColumnBit (d w) + binaryColumnRowSum next w) := by
              omega
        _ = (ε + K) + 2 * binaryColumnRowSum (d :: next) w := by
              rfl

/--
If a list of binary columns admits a dyadic pairing tree of depth `j`, then every row sum is
constant modulo `2^j`.
-/
lemma modEq_rowSum_of_hasDyadicPairingTree
    {W : Type*} {j : ℕ} {cols : List (BinaryColumn W)}
    (h : HasDyadicPairingTree j cols) :
    ∀ v w, binaryColumnRowSum cols v ≡ binaryColumnRowSum cols w [MOD 2 ^ j] := by
  induction h with
  | zero =>
      intro v w
      simpa [binaryColumnRowSum] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD 2 ^ 0])
  | @succ j cols next hstep htree ih =>
      rcases exists_constant_rowSum_decomposition_of_dyadicPairingStep hstep with ⟨K, hK⟩
      intro v w
      have hnext : binaryColumnRowSum next v ≡ binaryColumnRowSum next w [MOD 2 ^ j] := ih v w
      have hdouble :
          2 * binaryColumnRowSum next v ≡
            2 * binaryColumnRowSum next w [MOD 2 ^ (j + 1)] := by
        simpa [Nat.pow_succ, Nat.mul_comm] using Nat.ModEq.mul_left' 2 hnext
      have hadd :
          K + 2 * binaryColumnRowSum next v ≡
            K + 2 * binaryColumnRowSum next w [MOD 2 ^ (j + 1)] := by
        exact Nat.ModEq.add (Nat.ModEq.refl K) hdouble
      simpa [hK v, hK w] using hadd

/--
A dyadic divisibility chain of depth `j` for a natural-valued row function.

At each stage one removes a constant term and halves the remainder. This is the row-function analogue
of successive divisibility of the tail obstruction class.
-/
inductive HasDyadicRowDivisibilityChain {W : Type*} : ℕ → (W → ℕ) → Prop
  | zero (row : W → ℕ) : HasDyadicRowDivisibilityChain 0 row
  | succ {j : ℕ} {row next : W → ℕ} (K : ℕ)
      (hdecomp : ∀ w, row w = K + 2 * next w)
      (hnext : HasDyadicRowDivisibilityChain j next) :
      HasDyadicRowDivisibilityChain (j + 1) row

lemma hasDyadicRowDivisibilityChain_one_of_modEq_two
    {W : Type*} {row : W → ℕ} (hrow : ∀ v w, row v ≡ row w [MOD 2]) :
    HasDyadicRowDivisibilityChain 1 row := by
  by_cases hW : Nonempty W
  · classical
    let w₀ : W := Classical.choice hW
    let ε := row w₀ % 2
    refine
      HasDyadicRowDivisibilityChain.succ ε
        (next := fun w => row w / 2) ?_
        (HasDyadicRowDivisibilityChain.zero (fun w => row w / 2))
    intro w
    have hmod : row w % 2 = ε := by
      simpa [ε] using (hrow w w₀)
    calc
      row w = row w % 2 + 2 * (row w / 2) := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div (row w) 2).symm
      _ = ε + 2 * (row w / 2) := by rw [hmod]
  · refine
      HasDyadicRowDivisibilityChain.succ 0
        (next := fun _ => 0) ?_
        (HasDyadicRowDivisibilityChain.zero (fun _ => 0))
    intro w
    exact (hW ⟨w⟩).elim

lemma HasDyadicRowDivisibilityChain.congr
    {W : Type*} {j : ℕ} {row row' : W → ℕ}
    (h : HasDyadicRowDivisibilityChain j row)
    (hrow : ∀ w, row w = row' w) :
    HasDyadicRowDivisibilityChain j row' := by
  induction h generalizing row' with
  | zero row =>
      exact HasDyadicRowDivisibilityChain.zero row'
  | succ K hdecomp hnext _ih =>
      exact HasDyadicRowDivisibilityChain.succ K (fun w => by rw [← hrow w, hdecomp w]) hnext

/--
A dyadic divisibility chain together with an explicit terminal residual row after `j` stages.
-/
inductive HasDyadicRowDivisibilityChainTo {W : Type*} : ℕ → (W → ℕ) → (W → ℕ) → Prop
  | zero (row : W → ℕ) : HasDyadicRowDivisibilityChainTo 0 row row
  | succ {j : ℕ} {row next tail : W → ℕ} (K : ℕ)
      (hdecomp : ∀ w, row w = K + 2 * next w)
      (hnext : HasDyadicRowDivisibilityChainTo j next tail) :
      HasDyadicRowDivisibilityChainTo (j + 1) row tail

lemma HasDyadicRowDivisibilityChainTo.forget
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (h : HasDyadicRowDivisibilityChainTo j row tail) :
    HasDyadicRowDivisibilityChain j row := by
  induction h with
  | zero row =>
      exact HasDyadicRowDivisibilityChain.zero row
  | succ K hdecomp hnext ih =>
      exact HasDyadicRowDivisibilityChain.succ K hdecomp ih

lemma exists_hasDyadicRowDivisibilityChainTo_of_hasDyadicRowDivisibilityChain
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (h : HasDyadicRowDivisibilityChain j row) :
    ∃ tail : W → ℕ, HasDyadicRowDivisibilityChainTo j row tail := by
  induction h with
  | zero row =>
      exact ⟨row, HasDyadicRowDivisibilityChainTo.zero row⟩
  | @succ j row next K hdecomp hnext ih =>
      rcases ih with ⟨tail, htail⟩
      exact ⟨tail, HasDyadicRowDivisibilityChainTo.succ K hdecomp htail⟩

lemma HasDyadicRowDivisibilityChainTo.succ_of_terminalModEq_two
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChainTo j row tail)
    (hterm : ∀ v w, tail v ≡ tail w [MOD 2]) :
    HasDyadicRowDivisibilityChain (j + 1) row := by
  induction hchain with
  | zero row =>
      simpa using hasDyadicRowDivisibilityChain_one_of_modEq_two hterm
  | @succ j row next tail K hdecomp hnext ih =>
      exact HasDyadicRowDivisibilityChain.succ K hdecomp (ih hterm)

lemma HasDyadicRowDivisibilityChainTo.tail_modEq_two_iff_row_modEq_pow_succ
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChainTo j row tail) {v w : W} :
    tail v ≡ tail w [MOD 2] ↔ row v ≡ row w [MOD 2 ^ (j + 1)] := by
  induction hchain generalizing v w with
  | zero row =>
      simpa
  | @succ j row next tail K hdecomp hnext ih =>
      constructor
      · intro htail
        have hnextMod : next v ≡ next w [MOD 2 ^ (j + 1)] := (ih).1 htail
        have hdouble :
            2 * next v ≡ 2 * next w [MOD 2 * 2 ^ (j + 1)] := by
          simpa [Nat.mul_comm] using Nat.ModEq.mul_left' 2 hnextMod
        have hadd :
            K + 2 * next v ≡ K + 2 * next w [MOD 2 * 2 ^ (j + 1)] := by
          exact Nat.ModEq.add (Nat.ModEq.refl K) hdouble
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, hdecomp v, hdecomp w]
          using hadd
      · intro hrow
        have hdouble :
            2 * next v ≡ 2 * next w [MOD 2 * 2 ^ (j + 1)] := by
          have hadd :
              K + 2 * next v ≡ K + 2 * next w [MOD 2 * 2 ^ (j + 1)] := by
            simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, hdecomp v, hdecomp w]
              using hrow
          exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl K) hadd
        have hnextMod : next v ≡ next w [MOD 2 ^ (j + 1)] := by
          exact
            Nat.ModEq.mul_left_cancel' (a := next v) (b := next w) (c := 2)
              (m := 2 ^ (j + 1)) (by decide : 2 ≠ 0) hdouble
        exact (ih).2 hnextMod

lemma HasDyadicRowDivisibilityChainTo.tail_modEq_two_iff_row_modEq_pow_succ_basepoint
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChainTo j row tail) (w₀ : W) :
    (∀ w, tail w ≡ tail w₀ [MOD 2]) ↔
      (∀ w, row w ≡ row w₀ [MOD 2 ^ (j + 1)]) := by
  constructor
  · intro htail w
    exact (hchain.tail_modEq_two_iff_row_modEq_pow_succ (v := w) (w := w₀)).1 (htail w)
  · intro hrow w
    exact (hchain.tail_modEq_two_iff_row_modEq_pow_succ (v := w) (w := w₀)).2 (hrow w)

/--
Lean-facing form of the note's terminal beta-vanishing claim at bit `j`: every residual tail
obtained after `j` dyadic row-divisibility steps has constant parity.
-/
def DyadicTailBetaVanishesAt {W : Type*} (j : ℕ) (row : W → ℕ) : Prop :=
  ∀ tail : W → ℕ, HasDyadicRowDivisibilityChainTo j row tail →
    ∀ v w, tail v ≡ tail w [MOD 2]

/-- Beta-vanishing for every dyadic level strictly below `j`. -/
def DyadicTailBetaVanishesUpTo {W : Type*} (j : ℕ) (row : W → ℕ) : Prop :=
  ∀ m, m < j → DyadicTailBetaVanishesAt m row

lemma HasDyadicRowDivisibilityChainTo.succ_of_dyadicTailBetaVanishesAt
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChainTo j row tail)
    (hbeta : DyadicTailBetaVanishesAt j row) :
    HasDyadicRowDivisibilityChain (j + 1) row :=
  hchain.succ_of_terminalModEq_two (hbeta tail hchain)

/--
Successive dyadic divisibility of a row function forces constancy modulo `2^j`.
-/
lemma modEq_of_hasDyadicRowDivisibilityChain
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (h : HasDyadicRowDivisibilityChain j row) :
    ∀ v w, row v ≡ row w [MOD 2 ^ j] := by
  induction h with
  | zero row =>
      intro v w
      change row v % (2 ^ 0) = row w % (2 ^ 0)
      rw [pow_zero, Nat.mod_one, Nat.mod_one]
  | @succ j row next K hdecomp hnext ih =>
      intro v w
      have hnextMod : next v ≡ next w [MOD 2 ^ j] := ih v w
      have hdouble :
          2 * next v ≡ 2 * next w [MOD 2 ^ (j + 1)] := by
        simpa [Nat.pow_succ, Nat.mul_comm] using Nat.ModEq.mul_left' 2 hnextMod
      have hadd :
          K + 2 * next v ≡ K + 2 * next w [MOD 2 ^ (j + 1)] := by
        exact Nat.ModEq.add (Nat.ModEq.refl K) hdouble
      simpa [hdecomp v, hdecomp w] using hadd

/--
The bit-by-bit dyadic-tail step from the notes: beta-vanishing for the terminal residual tail
upgrades row constancy from the first `j` dyadic quotients to modulo `2^(j+1)`.
-/
lemma row_modEq_pow_succ_of_dyadicTailBetaVanishesAt
    {W : Type*} {j : ℕ} {row tail : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChainTo j row tail)
    (hbeta : DyadicTailBetaVanishesAt j row) :
    ∀ v w, row v ≡ row w [MOD 2 ^ (j + 1)] :=
  modEq_of_hasDyadicRowDivisibilityChain
    (hchain.succ_of_dyadicTailBetaVanishesAt hbeta)

/--
Full bit-by-bit dyadic-tail iteration: if the beta class vanishes at every level below `j`, then
the dropped-tail row admits a dyadic divisibility chain of depth `j`.
-/
lemma hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (hbeta : DyadicTailBetaVanishesUpTo j row) :
    HasDyadicRowDivisibilityChain j row := by
  induction j with
  | zero =>
      exact HasDyadicRowDivisibilityChain.zero row
  | succ j ih =>
      have hprev :
          HasDyadicRowDivisibilityChain j row := by
        exact ih (fun m hm => hbeta m (Nat.lt_trans hm (Nat.lt_succ_self j)))
      rcases exists_hasDyadicRowDivisibilityChainTo_of_hasDyadicRowDivisibilityChain hprev with
        ⟨tail, htail⟩
      exact htail.succ_of_dyadicTailBetaVanishesAt (hbeta j (Nat.lt_succ_self j))

/-- The iterated beta-vanishing theorem as a row congruence modulo `2^j`. -/
lemma row_modEq_pow_of_dyadicTailBetaVanishesUpTo
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (hbeta : DyadicTailBetaVanishesUpTo j row) :
    ∀ v w, row v ≡ row w [MOD 2 ^ j] :=
  modEq_of_hasDyadicRowDivisibilityChain
    (hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo hbeta)

/--
Conversely, a full dyadic divisibility chain makes every lower terminal beta class vanish.
-/
lemma dyadicTailBetaVanishesUpTo_of_hasDyadicRowDivisibilityChain
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (hchain : HasDyadicRowDivisibilityChain j row) :
    DyadicTailBetaVanishesUpTo j row := by
  intro m hm tail htail v w
  have hrowJ : row v ≡ row w [MOD 2 ^ j] :=
    modEq_of_hasDyadicRowDivisibilityChain hchain v w
  have hpowdvd : 2 ^ (m + 1) ∣ 2 ^ j :=
    Nat.pow_dvd_pow 2 (Nat.succ_le_of_lt hm)
  exact (htail.tail_modEq_two_iff_row_modEq_pow_succ (v := v) (w := w)).2
    (Nat.ModEq.of_dvd hpowdvd hrowJ)

/--
The note's all-bits beta-vanishing package is exactly the row-divisibility chain, at the
row-function level.
-/
theorem dyadicTailBetaVanishesUpTo_iff_hasDyadicRowDivisibilityChain
    {W : Type*} {j : ℕ} {row : W → ℕ} :
    DyadicTailBetaVanishesUpTo j row ↔ HasDyadicRowDivisibilityChain j row :=
  ⟨hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo,
    dyadicTailBetaVanishesUpTo_of_hasDyadicRowDivisibilityChain⟩

lemma hasDyadicRowDivisibilityChain_binaryColumnRowSum_of_hasDyadicPairingTree
    {W : Type*} {j : ℕ} {cols : List (BinaryColumn W)}
    (h : HasDyadicPairingTree j cols) :
    HasDyadicRowDivisibilityChain j (binaryColumnRowSum cols) := by
  induction h with
  | zero =>
      simpa [binaryColumnRowSum] using
        (HasDyadicRowDivisibilityChain.zero (fun _ : W => 0))
  | @succ j cols next hstep htree ih =>
      rcases exists_constant_rowSum_decomposition_of_dyadicPairingStep hstep with ⟨K, hK⟩
      exact HasDyadicRowDivisibilityChain.succ K hK ih

lemma hasDyadicRowDivisibilityChain_one_of_hasBinaryZeroSumPacketPartition
    {W : Type*} {packets : List (List (BinaryColumn W))}
    (hpackets : HasBinaryZeroSumPacketPartition packets) :
    HasDyadicRowDivisibilityChain 1 (binaryColumnRowSum (flattenBinaryPackets packets)) := by
  exact
    hasDyadicRowDivisibilityChain_one_of_modEq_two
      (modEq_rowSum_two_of_hasBinaryZeroSumPacketPartition hpackets)

lemma hasDyadicRowDivisibilityChain_succ_of_modEq_two_and_halved
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (hrow : ∀ v w, row v ≡ row w [MOD 2])
    (hnext : HasDyadicRowDivisibilityChain j (fun w => row w / 2)) :
    HasDyadicRowDivisibilityChain (j + 1) row := by
  by_cases hW : Nonempty W
  · classical
    let w₀ : W := Classical.choice hW
    let ε := row w₀ % 2
    refine
      HasDyadicRowDivisibilityChain.succ ε
        (next := fun w => row w / 2) ?_ hnext
    intro w
    have hmod : row w % 2 = ε := by
      simpa [ε] using (hrow w w₀)
    calc
      row w = row w % 2 + 2 * (row w / 2) := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div (row w) 2).symm
      _ = ε + 2 * (row w / 2) := by rw [hmod]
  · refine
      HasDyadicRowDivisibilityChain.succ 0
        (next := fun w => row w / 2) ?_ hnext
    intro w
    exact (hW ⟨w⟩).elim

lemma hasDyadicRowDivisibilityChain_succ_of_hasBinaryZeroSumPacketPartition_and_halved
    {W : Type*} {j : ℕ} {packets : List (List (BinaryColumn W))}
    (hpackets : HasBinaryZeroSumPacketPartition packets)
    (hnext :
      HasDyadicRowDivisibilityChain j
        (fun w => binaryColumnRowSum (flattenBinaryPackets packets) w / 2)) :
    HasDyadicRowDivisibilityChain (j + 1)
      (binaryColumnRowSum (flattenBinaryPackets packets)) := by
  exact
    hasDyadicRowDivisibilityChain_succ_of_modEq_two_and_halved
      (modEq_rowSum_two_of_hasBinaryZeroSumPacketPartition hpackets)
      hnext

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
If the ambient degrees on `s ∪ t₁ ∪ t₂ ∪ u` are constant modulo `q` on `s`, and the external
degrees into each disjoint block `t₁, t₂` are constant modulo `q` on `s`, then the ambient degrees
on `s ∪ u` are constant modulo `q` on `s`.
-/
lemma modEq_unionDegree_of_modEq_extendedUnionDegree_and_two_externalDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t₁ t₂ u : Finset V}
    (hst : Disjoint s (t₁ ∪ t₂)) (htu : Disjoint (t₁ ∪ t₂) u) (ht : Disjoint t₁ t₂) {q : ℕ}
    (hdeg :
      ∀ v w : ↑(s : Set V),
        (inducedOn G (s ∪ ((t₁ ∪ t₂) ∪ u))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (s ∪ ((t₁ ∪ t₂) ∪ u))).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext₁ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₁).card ≡ (G.neighborFinset w ∩ t₁).card [MOD q])
    (hext₂ :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t₂).card ≡ (G.neighborFinset w ∩ t₂).card [MOD q]) :
    ∀ v w : ↑(s : Set V),
      (inducedOn G (s ∪ u)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (s ∪ u)).degree ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
  have hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ (t₁ ∪ t₂)).card ≡
          (G.neighborFinset w ∩ (t₁ ∪ t₂)).card [MOD q] := by
    intro v w
    have hv :
        (G.neighborFinset v ∩ (t₁ ∪ t₂)).card =
          (G.neighborFinset v ∩ t₁).card + (G.neighborFinset v ∩ t₂).card := by
      simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
        (card_neighborFinset_inter_union (G := G) (s := t₁) (t := t₂) ht v)
    have hw :
        (G.neighborFinset w ∩ (t₁ ∪ t₂)).card =
          (G.neighborFinset w ∩ t₁).card + (G.neighborFinset w ∩ t₂).card := by
      simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
        (card_neighborFinset_inter_union (G := G) (s := t₁) (t := t₂) ht w)
    simpa [hv, hw] using Nat.ModEq.add (hext₁ v w) (hext₂ v w)
  exact
    modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
      (G := G) (s := s) (t := t₁ ∪ t₂) (u := u) hst htu
      (hdeg := by
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hdeg)
      (hext := hext)

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
If the dropped tail `s \ u` is partitioned into separated control blocks whose external degrees are
constant modulo `q` on `u`, then host-degree congruence on `G[s]` already forces modular regularity
on `u`.
-/
lemma inducesModEqDegree_of_modEq_hostDegree_and_internalTailBlocks
    (G : SimpleGraph V) [DecidableRel G.Adj] {u s : Finset V} (hu : u ⊆ s) {q : ℕ}
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    {blocks : List (Finset V × ℕ)} (hcover : controlBlockUnion blocks = s \ u)
    (hsep : ControlBlocksSeparated u blocks)
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    InducesModEqDegree G u q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hdeg :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hAmbientEq : u ∪ controlBlockUnion blocks = s := by
      ext x
      by_cases hxu : x ∈ u
      · have hxs : x ∈ s := hu hxu
        simp [hcover, hxu, hxs, or_assoc, or_left_comm, or_comm]
      · simp [hcover, hxu, or_assoc, or_left_comm, or_comm]
    have hcastv :
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G s).degree ⟨v.1, hu v.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ controlBlockUnion blocks)
          (t := s)
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := hu v.2))
    have hcastw :
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ controlBlockUnion blocks)
          (t := s)
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := hu w.2))
    simpa [hcastv, hcastw] using hhost v w
  exact
    inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees G hsep hdeg hext

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
`HasFixedModulusCascadeFrom G q s chain` records a multistage refinement from a host `s` down a
chain of smaller buckets without any auxiliary control family. At each proper step the ambient
degree in `G[s]` and the degree into the dropped part `s \ u` are frozen modulo `q`; at the
terminal bucket, the ambient degree in `G[s]` is constant modulo `q`.
-/
def HasFixedModulusCascadeFrom (G : SimpleGraph V) (q : ℕ) :
    Finset V → List (Finset V) → Prop := by
  classical
  exact fun s chain =>
    match chain with
    | [] =>
        ∀ v w : ↑(s : Set V), (inducedOn G s).degree v ≡ (inducedOn G s).degree w [MOD q]
    | u :: chain =>
        ∃ hu : u ⊆ s, ∃ eDrop : ℕ,
          (∀ v w : ↑(u : Set V),
            (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
              (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
          (∀ v : ↑(u : Set V), (G.neighborFinset v ∩ (s \ u)).card ≡ eDrop [MOD q]) ∧
          HasFixedModulusCascadeFrom G q u chain

/--
A fixed-modulus cascade witness of size at least `k`: a host `s`, a fixed modulus `q`, and a chain
of bucket refinements whose terminal bucket has size at least `k`.
-/
def HasFixedModulusCascadeWitnessOfCard (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    HasFixedModulusCascadeFrom G q s chain

lemma hasFixedModulusCascadeWitnessOfCard_mono
    (G : SimpleGraph V) {k ℓ q : ℕ} (hkℓ : k ≤ ℓ)
    (hcascade : HasFixedModulusCascadeWitnessOfCard G ℓ q) :
    HasFixedModulusCascadeWitnessOfCard G k q := by
  rcases hcascade with ⟨s, chain, hℓ, hfrom⟩
  exact ⟨s, chain, le_trans hkℓ hℓ, hfrom⟩

lemma hasFixedModulusCascadeWitnessOfCard_of_hasFixedModulusWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ} (hfixed : HasFixedModulusWitnessOfCard G k q) :
    HasFixedModulusCascadeWitnessOfCard G k q := by
  rcases hfixed with ⟨s, hks, hmod⟩
  exact ⟨s, [], by simpa [cascadeTerminal] using hks, hmod⟩

/--
The terminal bucket of a fixed-modulus cascade is itself a fixed-modulus witness with the same
modulus.
-/
lemma inducesModEqDegree_cascadeTerminal_of_hasFixedModulusCascadeFrom
    (G : SimpleGraph V) {q : ℕ} {s : Finset V} {chain : List (Finset V)}
    (hcascade : HasFixedModulusCascadeFrom G q s chain) :
    InducesModEqDegree G (cascadeTerminal s chain) q := by
  classical
  induction chain generalizing s with
  | nil =>
      simpa [InducesModEqDegree, HasFixedModulusCascadeFrom, cascadeTerminal] using hcascade
  | cons u chain ih =>
      rcases hcascade with ⟨hu, eDrop, hdeg, hdrop, hrest⟩
      simpa [cascadeTerminal] using ih hrest

lemma hasFixedModulusWitnessOfCard_of_hasFixedModulusCascadeWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ} (hcascade : HasFixedModulusCascadeWitnessOfCard G k q) :
    HasFixedModulusWitnessOfCard G k q := by
  rcases hcascade with ⟨s, chain, hk, hfrom⟩
  exact
    ⟨cascadeTerminal s chain, hk,
      inducesModEqDegree_cascadeTerminal_of_hasFixedModulusCascadeFrom G hfrom⟩

/--
Gallai's parity theorem, repackaged in the empty-control fixed-modulus cascade language suggested by
the dyadic-lift note.
-/
lemma hasFixedModulusCascadeWitnessOfCard_two (G : SimpleGraph V) :
    HasFixedModulusCascadeWitnessOfCard G (Fintype.card V / 2) 2 := by
  exact hasFixedModulusCascadeWitnessOfCard_of_hasFixedModulusWitnessOfCard G
    (hasFixedModulusWitnessOfCard_two G)

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
A fixed-modulus single-control modular host witness of size at least `k`: a bucket `u` inside a
host set `s`, together with one nonempty disjoint control set `t`, such that the host degrees in
`G[s]` are constant modulo `q` on `u` and the external degrees into `t` share a common residue
modulo `q` on `u`.
-/
def HasFixedModulusSingleControlModularHostWitnessOfCard
    (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, k ≤ u.card ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card ≡ e [MOD q]

/--
Exact-cardinality version of the fixed-modulus single-control modular host witness package.
-/
def HasExactCardFixedModulusSingleControlModularHostWitnessOfCard
    (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, u.card = k ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card ≡ e [MOD q]

/--
Exact-cardinality fixed-modulus single-control modular host witness with prescribed control-set size
`r`.
-/
def HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, u.card = k ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ t.card = r ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card ≡ e [MOD q]

/--
Literal host-side frontier package from Corollary 10.2: a completed host set `s` of size `q^2`
whose internal degrees are constant modulo `q`, together with one disjoint control set `t` on which
the external degree is already frozen exactly.
-/
def HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard
    (G : SimpleGraph V) (q : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, s.card = q * q ∧ 0 < t.card ∧ Disjoint s t ∧
    InducesModEqDegree G s q ∧
    ∃ e : ℕ, ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e

/--
Completed-host version of the exact single-control package with prescribed inherited control size
`r`.
-/
def HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) (q r : ℕ) : Prop := by
  classical
  exact ∃ s t : Finset V, s.card = q * q ∧ 0 < t.card ∧ t.card = r ∧ Disjoint s t ∧
    InducesModEqDegree G s q ∧
    ∃ e : ℕ, ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e

/--
Inside a peeled host set `T` with chosen low set `L ⊆ T`, the vertex `x` has the exact low
neighborhood if it sees precisely `L` inside `T`.
-/
def HasExactLowNeighborhoodOnFinset
    (G : SimpleGraph V) (x : V) (T L : Finset V) : Prop := by
  classical
  exact G.neighborFinset x ∩ T = L

/--
Number of defects of the neighborhood of `x` inside `T` relative to the target low set `L`.

This counts both extra neighbors in `T \\ L` and missing neighbors in `L`.
-/
noncomputable def lowNeighborhoodError
    (G : SimpleGraph V) (x : V) (T L : Finset V) : ℕ := by
  classical
  exact (G.neighborFinset x ∩ (T \ L)).card + (L \ G.neighborFinset x).card

lemma hasExactLowNeighborhoodOnFinset_iff_lowNeighborhoodError_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T) :
    HasExactLowNeighborhoodOnFinset G x T L ↔
      lowNeighborhoodError G x T L = 0 := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  unfold HasExactLowNeighborhoodOnFinset lowNeighborhoodError
  constructor
  · intro hExact
    have hextra : G.neighborFinset x ∩ (T \ L) = ∅ := by
      apply Finset.ext
      intro y
      constructor
      · intro hy
        rcases Finset.mem_inter.mp hy with ⟨hyN, hyTL⟩
        rcases Finset.mem_sdiff.mp hyTL with ⟨hyT, hyNotL⟩
        have hyInL : y ∈ L := by
          have hyIn : y ∈ G.neighborFinset x ∩ T := Finset.mem_inter.mpr ⟨hyN, hyT⟩
          rw [hExact] at hyIn
          exact hyIn
        exact (hyNotL hyInL).elim
      · intro hy
        simpa using hy
    have hmiss : L \ G.neighborFinset x = ∅ := by
      apply Finset.ext
      intro y
      constructor
      · intro hy
        rcases Finset.mem_sdiff.mp hy with ⟨hyL, hyNotN⟩
        have hyInN : y ∈ G.neighborFinset x := by
          have hyIn : y ∈ G.neighborFinset x ∩ T := by
            have hyInL : y ∈ L := hyL
            rw [← hExact] at hyInL
            exact hyInL
          exact (Finset.mem_inter.mp hyIn).1
        exact (hyNotN hyInN).elim
      · intro hy
        simpa using hy
    have hextraCard : (G.neighborFinset x ∩ (T \ L)).card = 0 := by
      simp [hextra]
    have hmissCard : (L \ G.neighborFinset x).card = 0 := by
      simp [hmiss]
    rw [hextraCard, hmissCard]
  · intro herr
    have ⟨hextra0, hmiss0⟩ := Nat.add_eq_zero_iff.mp herr
    have hextra : G.neighborFinset x ∩ (T \ L) = ∅ := Finset.card_eq_zero.mp hextra0
    have hmiss : L \ G.neighborFinset x = ∅ := Finset.card_eq_zero.mp hmiss0
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyN, hyT⟩
      by_contra hyNotL
      have hyExtra : y ∈ G.neighborFinset x ∩ (T \ L) := by
        exact Finset.mem_inter.mpr ⟨hyN, Finset.mem_sdiff.mpr ⟨hyT, hyNotL⟩⟩
      have : y ∈ (∅ : Finset V) := by simpa [hextra] using hyExtra
      simpa using this
    · intro hyL
      have hyN : y ∈ G.neighborFinset x := by
        by_contra hyNotN
        have hyMiss : y ∈ L \ G.neighborFinset x := Finset.mem_sdiff.mpr ⟨hyL, hyNotN⟩
        have : y ∈ (∅ : Finset V) := by simpa [hmiss] using hyMiss
        simpa using this
      exact Finset.mem_inter.mpr ⟨hyN, hLT hyL⟩

lemma hasExactLowNeighborhoodOnFinset_of_card_lt_and_coordinate_balance
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V} {q : ℕ}
    (hLT : L ⊆ T) (hPq : P.card < q)
    (hOut : ∀ y ∈ T \ L, (P.filter fun x => y ∈ G.neighborFinset x).card ≡ 0 [MOD q])
    (hIn : ∀ y ∈ L, (P.filter fun x => y ∈ G.neighborFinset x).card ≡ P.card [MOD q]) :
    ∀ x ∈ P, HasExactLowNeighborhoodOnFinset G x T L := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hq0 : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hPq
  intro x hxP
  unfold HasExactLowNeighborhoodOnFinset
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rcases Finset.mem_inter.mp hy with ⟨hyN, hyT⟩
    by_contra hyNotL
    have hyTL : y ∈ T \ L := Finset.mem_sdiff.mpr ⟨hyT, hyNotL⟩
    have hmod : (P.filter fun z => y ∈ G.neighborFinset z).card % q = 0 := by
      simpa [Nat.mod_eq_of_lt hq0] using hOut y hyTL
    have hcountLt : (P.filter fun z => y ∈ G.neighborFinset z).card < q := by
      exact lt_of_le_of_lt (Finset.card_filter_le _ _) hPq
    have hcount0 : (P.filter fun z => y ∈ G.neighborFinset z).card = 0 := by
      rw [Nat.mod_eq_of_lt hcountLt] at hmod
      exact hmod
    have hempty : (P.filter fun z => y ∈ G.neighborFinset z) = ∅ := Finset.card_eq_zero.mp hcount0
    have hxFilter : x ∈ P.filter fun z => y ∈ G.neighborFinset z := by
      exact Finset.mem_filter.mpr ⟨hxP, hyN⟩
    rw [hempty] at hxFilter
    have : False := by simpa using hxFilter
    simpa using this
  · intro hyL
    have hmod :
        (P.filter fun z => y ∈ G.neighborFinset z).card % q = P.card % q := by
      simpa using hIn y hyL
    have hcountLt : (P.filter fun z => y ∈ G.neighborFinset z).card < q := by
      exact lt_of_le_of_lt (Finset.card_filter_le _ _) hPq
    have hcountFull : (P.filter fun z => y ∈ G.neighborFinset z).card = P.card := by
      rw [Nat.mod_eq_of_lt hcountLt, Nat.mod_eq_of_lt hPq] at hmod
      exact hmod
    have hfilterEq : (P.filter fun z => y ∈ G.neighborFinset z) = P := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hcountFull]
    have hxFilter : x ∈ P.filter fun z => y ∈ G.neighborFinset z := by
      rw [hfilterEq]
      exact hxP
    have hyN : y ∈ G.neighborFinset x := by
      simpa using (Finset.mem_filter.mp hxFilter).2
    exact Finset.mem_inter.mpr ⟨hyN, hLT hyL⟩

lemma hasExactLowNeighborhoodOnFinset_of_weighted_sum_lt_and_coordinate_balance
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V} {q : ℕ} {m : V → ℕ}
    (hLT : L ⊆ T) (hMq : P.sum m < q)
    (hOut :
      ∀ y ∈ T \ L, (P.filter fun z => y ∈ G.neighborFinset z).sum m ≡ 0 [MOD q])
    (hIn :
      ∀ y ∈ L,
        (P.filter fun z => y ∈ G.neighborFinset z).sum m ≡ P.sum m [MOD q]) :
    ∀ x ∈ P, 0 < m x → HasExactLowNeighborhoodOnFinset G x T L := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  intro x hxP hxPos
  unfold HasExactLowNeighborhoodOnFinset
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rcases Finset.mem_inter.mp hy with ⟨hyN, hyT⟩
    by_contra hyNotL
    have hyTL : y ∈ T \ L := Finset.mem_sdiff.mpr ⟨hyT, hyNotL⟩
    have hsumLe :
        (P.filter fun z => y ∈ G.neighborFinset z).sum m ≤ P.sum m := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsumLtq : (P.filter fun z => y ∈ G.neighborFinset z).sum m < q := by
      exact lt_of_le_of_lt hsumLe hMq
    have hsum0 : (P.filter fun z => y ∈ G.neighborFinset z).sum m = 0 := by
      have hmod :
          ((P.filter fun z => y ∈ G.neighborFinset z).sum m) % q = 0 := by
        simpa [Nat.mod_eq_of_lt hsumLtq] using hOut y hyTL
      rw [Nat.mod_eq_of_lt hsumLtq] at hmod
      exact hmod
    have hxFilter : x ∈ P.filter (fun z => y ∈ G.neighborFinset z) := by
      exact Finset.mem_filter.mpr ⟨hxP, hyN⟩
    have hxLe :
        m x ≤ (P.filter fun z => y ∈ G.neighborFinset z).sum m := by
      exact Finset.single_le_sum (fun z hz => Nat.zero_le _) hxFilter
    have hxLe0 : m x ≤ 0 := by
      rw [hsum0] at hxLe
      exact hxLe
    have hxZero : m x = 0 := by
      exact Nat.le_zero.mp hxLe0
    exact (Nat.ne_of_gt hxPos) hxZero
  · intro hyL
    have hsumLe :
        (P.filter fun z => y ∈ G.neighborFinset z).sum m ≤ P.sum m := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsumLtq : (P.filter fun z => y ∈ G.neighborFinset z).sum m < q := by
      exact lt_of_le_of_lt hsumLe hMq
    have hsumFull :
        (P.filter fun z => y ∈ G.neighborFinset z).sum m = P.sum m := by
      have hmod : ((P.filter fun z => y ∈ G.neighborFinset z).sum m) % q = (P.sum m) % q := by
        exact hIn y hyL
      rw [Nat.mod_eq_of_lt hsumLtq, Nat.mod_eq_of_lt hMq] at hmod
      exact hmod
    have hyN : y ∈ G.neighborFinset x := by
      by_contra hyNotN
      have hxComp : x ∈ P.filter (fun z => y ∉ G.neighborFinset z) := by
        exact Finset.mem_filter.mpr ⟨hxP, hyNotN⟩
      have hcompLe :
          m x ≤ (P.filter fun z => y ∉ G.neighborFinset z).sum m := by
        exact Finset.single_le_sum (fun z hz => Nat.zero_le _) hxComp
      have hcompPos : 0 < (P.filter fun z => y ∉ G.neighborFinset z).sum m := by
        exact lt_of_lt_of_le hxPos hcompLe
      have hlt :
          (P.filter fun z => y ∈ G.neighborFinset z).sum m < P.sum m := by
        rw [← Finset.sum_filter_add_sum_filter_not P (fun z => y ∈ G.neighborFinset z) m]
        exact Nat.lt_add_of_pos_right hcompPos
      exact (Nat.ne_of_lt hlt) hsumFull
    exact Finset.mem_inter.mpr ⟨hyN, hLT hyL⟩

lemma sum_card_neighborFinset_inter_eq_sum_card_filter_mem_neighborFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P S : Finset V) :
    P.sum (fun x => (G.neighborFinset x ∩ S).card) =
      S.sum (fun y => (P.filter fun x => y ∈ G.neighborFinset x).card) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  simpa [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.filter_mem_eq_inter, Finset.inter_comm,
    ← SimpleGraph.mem_neighborFinset] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := P) (t := S) (r := G.Adj))

lemma sum_card_sdiff_neighborFinset_eq_sum_card_filter_not_mem_neighborFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P S : Finset V) :
    P.sum (fun x => (S \ G.neighborFinset x).card) =
      S.sum (fun y => (P.filter fun x => y ∉ G.neighborFinset x).card) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  simpa [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.sdiff_eq_filter] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := P) (t := S) (r := fun x y => y ∉ G.neighborFinset x))

lemma sum_lowNeighborhoodError_eq_sum_card_filter_mem_neighborFinset_add_sum_card_filter_not_mem_neighborFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V) :
    P.sum (fun x => lowNeighborhoodError G x T L) =
      (T \ L).sum (fun y => (P.filter fun x => y ∈ G.neighborFinset x).card) +
        L.sum (fun y => (P.filter fun x => y ∉ G.neighborFinset x).card) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  unfold lowNeighborhoodError
  rw [sum_add_distrib]
  rw [sum_card_neighborFinset_inter_eq_sum_card_filter_mem_neighborFinset (G := G) (P := P)
      (S := T \ L)]
  rw [sum_card_sdiff_neighborFinset_eq_sum_card_filter_not_mem_neighborFinset (G := G) (P := P)
      (S := L)]

lemma exists_hasExactLowNeighborhoodOnFinset_of_sum_lowNeighborhoodError_lt_card
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V}
    (hLT : L ⊆ T)
    (herr : P.sum (fun x => lowNeighborhoodError G x T L) < P.card) :
    ∃ x ∈ P, HasExactLowNeighborhoodOnFinset G x T L := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  by_contra hnone
  have hnone' : ∀ x, x ∈ P → ¬ HasExactLowNeighborhoodOnFinset G x T L := by
    intro x hxP hxExact
    exact hnone ⟨x, hxP, hxExact⟩
  have hpos : ∀ x ∈ P, 1 ≤ lowNeighborhoodError G x T L := by
    intro x hxP
    have hne : lowNeighborhoodError G x T L ≠ 0 := by
      intro hzero
      exact
        hnone' x hxP
          ((hasExactLowNeighborhoodOnFinset_iff_lowNeighborhoodError_eq_zero (G := G) hLT).2 hzero)
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
  have hcardLe : P.card ≤ P.sum (fun x => lowNeighborhoodError G x T L) := by
    simpa using Finset.card_nsmul_le_sum P (fun x => lowNeighborhoodError G x T L) 1 hpos
  exact (Nat.not_le_of_lt herr) hcardLe

lemma card_filter_hasExactLowNeighborhoodOnFinset_ge_card_sub_sum_lowNeighborhoodError
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V}
    (hLT : L ⊆ T) : by
      classical
      exact
        P.card - P.sum (fun x => lowNeighborhoodError G x T L) ≤
          (P.filter fun x => HasExactLowNeighborhoodOnFinset G x T L).card := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  let good := P.filter fun x => HasExactLowNeighborhoodOnFinset G x T L
  have hgoodSub : good ⊆ P := Finset.filter_subset _ _
  have hbadLe :
      (P \ good).card ≤ P.sum (fun x => lowNeighborhoodError G x T L) := by
    have hbadPos : ∀ x ∈ P \ good, 1 ≤ lowNeighborhoodError G x T L := by
      intro x hxBad
      rcases Finset.mem_sdiff.mp hxBad with ⟨hxP, hxNotGood⟩
      have hxNot : ¬ HasExactLowNeighborhoodOnFinset G x T L := by
        exact fun hxExact => hxNotGood (by simp [good, hxP, hxExact])
      have hne : lowNeighborhoodError G x T L ≠ 0 := by
        intro hzero
        exact
          hxNot
            ((hasExactLowNeighborhoodOnFinset_iff_lowNeighborhoodError_eq_zero (G := G) hLT).2 hzero)
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    have hbadCardLeBadSum :
        (P \ good).card ≤ (P \ good).sum (fun x => lowNeighborhoodError G x T L) := by
      simpa using
        Finset.card_nsmul_le_sum (P \ good) (fun x => lowNeighborhoodError G x T L) 1 hbadPos
    have hbadSumLe :
        (P \ good).sum (fun x => lowNeighborhoodError G x T L) ≤
          P.sum (fun x => lowNeighborhoodError G x T L) := by
      exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
    exact le_trans hbadCardLeBadSum hbadSumLe
  have hsplit : (P \ good).card + good.card = P.card := by
    calc
      (P \ good).card + good.card = (P \ good).card + (P ∩ good).card := by
        rw [Finset.inter_eq_right.mpr hgoodSub]
      _ = P.card := Finset.card_sdiff_add_card_inter P good
  have hle : P.card ≤ good.card + P.sum (fun x => lowNeighborhoodError G x T L) := by
    rw [← hsplit]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add_left hbadLe good.card
  have hresult :
      P.card - P.sum (fun x => lowNeighborhoodError G x T L) ≤ good.card := by
    exact Nat.sub_le_iff_le_add.mpr hle
  simpa [good] using hresult

lemma exists_lowNeighborhoodError_le_one_of_sum_lowNeighborhoodError_lt_two_mul_card
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V}
    (herr : P.sum (fun x => lowNeighborhoodError G x T L) < 2 * P.card) :
    ∃ x ∈ P, lowNeighborhoodError G x T L ≤ 1 := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  by_contra hnone
  have hnone' : ∀ x, x ∈ P → ¬ lowNeighborhoodError G x T L ≤ 1 := by
    intro x hxP hxle
    exact hnone ⟨x, hxP, hxle⟩
  have htwoLe : P.card + P.card ≤ P.sum (fun x => lowNeighborhoodError G x T L) := by
    have hge : ∀ x ∈ P, 2 ≤ lowNeighborhoodError G x T L := by
      intro x hxP
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge (hnone' x hxP))
    have htwoMul : P.card * 2 ≤ P.sum (fun x => lowNeighborhoodError G x T L) := by
      simpa using
        Finset.card_nsmul_le_sum P (fun x => lowNeighborhoodError G x T L) 2 hge
    calc
      P.card + P.card = P.card * 2 := by rw [← two_mul, Nat.mul_comm]
      _ ≤ P.sum (fun x => lowNeighborhoodError G x T L) := htwoMul
  have herr' : P.sum (fun x => lowNeighborhoodError G x T L) < P.card + P.card := by
    simpa [two_mul] using herr
  exact (Nat.not_le_of_lt herr') htwoLe

/--
One-defect miss type inside a peeled host set `T`: the low neighborhood is exactly `L \ {z}` for some
unique missing low vertex `z ∈ L`.
-/
def HasLowNeighborhoodMissTypeOnFinset
    (G : SimpleGraph V) (x : V) (T L : Finset V) (z : V) : Prop := by
  classical
  exact z ∈ L ∧ HasExactLowNeighborhoodOnFinset G x T (L \ {z})

/--
One-defect add type inside a peeled host set `T`: the low neighborhood is exactly `insert y L` for some
unique added high vertex `y ∈ T \ L`.
-/
def HasLowNeighborhoodAddTypeOnFinset
    (G : SimpleGraph V) (x : V) (T L : Finset V) (y : V) : Prop := by
  classical
  exact y ∈ T \ L ∧ HasExactLowNeighborhoodOnFinset G x T (insert y L)

lemma hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    (∃ z, HasLowNeighborhoodMissTypeOnFinset G x T L z) ∨
      (∃ y, HasLowNeighborhoodAddTypeOnFinset G x T L y) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  let extra := G.neighborFinset x ∩ (T \ L)
  let miss := L \ G.neighborFinset x
  have hsum : extra.card + miss.card = 1 := by
    simpa [lowNeighborhoodError, extra, miss] using herr
  by_cases hextra0 : extra.card = 0
  · have hmiss1 : miss.card = 1 := by
      simpa [hextra0] using hsum
    have hextraEmpty : extra = ∅ := Finset.card_eq_zero.mp hextra0
    obtain ⟨z, hzmiss⟩ := Finset.card_eq_one.mp hmiss1
    have hzInMiss : z ∈ miss := by
      rw [hzmiss]
      simp
    have hzL : z ∈ L := (Finset.mem_sdiff.mp hzInMiss).1
    have hzNotN : z ∉ G.neighborFinset x := (Finset.mem_sdiff.mp hzInMiss).2
    left
    refine ⟨z, ?_⟩
    unfold HasLowNeighborhoodMissTypeOnFinset
    refine ⟨hzL, ?_⟩
    unfold HasExactLowNeighborhoodOnFinset
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyN, hyT⟩
      have hyL : y ∈ L := by
        by_contra hyNotL
        have hyExtra : y ∈ extra := by
          exact Finset.mem_inter.mpr ⟨hyN, Finset.mem_sdiff.mpr ⟨hyT, hyNotL⟩⟩
        have : y ∈ (∅ : Finset V) := by
          simpa [hextraEmpty] using hyExtra
        simpa using this
      have hyNeZ : y ≠ z := by
        intro hyEq
        subst hyEq
        exact hzNotN hyN
      exact Finset.mem_sdiff.mpr ⟨hyL, by simpa [Finset.mem_singleton] using hyNeZ⟩
    · intro hy
      rcases Finset.mem_sdiff.mp hy with ⟨hyL, hyNotZ⟩
      have hyT : y ∈ T := hLT hyL
      have hyN : y ∈ G.neighborFinset x := by
        by_contra hyNotN
        have hyMiss : y ∈ miss := Finset.mem_sdiff.mpr ⟨hyL, hyNotN⟩
        rw [hzmiss] at hyMiss
        exact hyNotZ (by simpa using hyMiss)
      exact Finset.mem_inter.mpr ⟨hyN, hyT⟩
  · have hextraLe : extra.card ≤ 1 := by
      calc
        extra.card ≤ extra.card + miss.card := Nat.le_add_right _ _
        _ = 1 := hsum
    have hextraOneLe : 1 ≤ extra.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hextra0)
    have hextra1 : extra.card = 1 := le_antisymm hextraLe hextraOneLe
    have hmiss0 : miss.card = 0 := by
      simpa [hextra1] using hsum
    have hmissEmpty : miss = ∅ := Finset.card_eq_zero.mp hmiss0
    obtain ⟨y, hyextra⟩ := Finset.card_eq_one.mp hextra1
    have hyInExtra : y ∈ extra := by
      rw [hyextra]
      simp
    have hyN : y ∈ G.neighborFinset x := (Finset.mem_inter.mp hyInExtra).1
    have hyTL : y ∈ T \ L := (Finset.mem_inter.mp hyInExtra).2
    right
    refine ⟨y, ?_⟩
    unfold HasLowNeighborhoodAddTypeOnFinset
    refine ⟨hyTL, ?_⟩
    unfold HasExactLowNeighborhoodOnFinset
    apply Finset.ext
    intro v
    constructor
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hvN, hvT⟩
      by_cases hvL : v ∈ L
      · exact Finset.mem_insert.mpr (Or.inr hvL)
      · have hvExtra : v ∈ extra := by
          exact Finset.mem_inter.mpr ⟨hvN, Finset.mem_sdiff.mpr ⟨hvT, hvL⟩⟩
        rw [hyextra] at hvExtra
        exact Finset.mem_insert.mpr (Or.inl (by simpa using hvExtra))
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hvL
      · exact Finset.mem_inter.mpr ⟨hyN, (Finset.mem_sdiff.mp hyTL).1⟩
      · have hvT : v ∈ T := hLT hvL
        have hvN : v ∈ G.neighborFinset x := by
          by_contra hvNotN
          have hvMiss : v ∈ miss := Finset.mem_sdiff.mpr ⟨hvL, hvNotN⟩
          have : v ∈ (∅ : Finset V) := by
            simpa [hmissEmpty] using hvMiss
          simpa using this
        exact Finset.mem_inter.mpr ⟨hvN, hvT⟩

/--
Existence of a chosen defect site in `T` for a one-defect low neighborhood.
-/
lemma exists_lowNeighborhoodDefectSite
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    ∃ u, u ∈ T ∧
      (HasLowNeighborhoodMissTypeOnFinset G x T L u ∨
        HasLowNeighborhoodAddTypeOnFinset G x T L u) := by
  classical
  rcases
      hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_of_lowNeighborhoodError_eq_one
        (G := G) (x := x) (T := T) (L := L) hLT herr with
    hmiss | hadd
  · refine ⟨Classical.choose hmiss, hLT (Classical.choose_spec hmiss).1, ?_⟩
    exact Or.inl (Classical.choose_spec hmiss)
  · refine ⟨Classical.choose hadd, (Finset.mem_sdiff.mp (Classical.choose_spec hadd).1).1, ?_⟩
    exact Or.inr (Classical.choose_spec hadd)

/--
Chosen defect site in `T` for a one-defect low neighborhood. This is the finite peeled-set version of the
defect map on the one-defect strip.
-/
noncomputable def lowNeighborhoodDefectSite
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (T L : Finset V)
    (hLT : L ⊆ T) (herr : lowNeighborhoodError G x T L = 1) : ↑(T : Set V) := by
  classical
  refine ⟨Classical.choose (exists_lowNeighborhoodDefectSite (G := G) (x := x) (T := T) (L := L) hLT herr), ?_⟩
  exact
    (Classical.choose_spec
      (exists_lowNeighborhoodDefectSite (G := G) (x := x) (T := T) (L := L) hLT herr)).1

lemma hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_at_lowNeighborhoodDefectSite
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    HasLowNeighborhoodMissTypeOnFinset G x T L (lowNeighborhoodDefectSite G x T L hLT herr).1 ∨
      HasLowNeighborhoodAddTypeOnFinset G x T L (lowNeighborhoodDefectSite G x T L hLT herr).1 := by
  classical
  exact
    (Classical.choose_spec
      (exists_lowNeighborhoodDefectSite (G := G) (x := x) (T := T) (L := L) hLT herr)).2

lemma hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodMissTypeOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {x z : V} {T L : Finset V}
    (hmiss : HasLowNeighborhoodMissTypeOnFinset G x T L z) :
    HasExactLowNeighborhoodOnFinset G x (T.erase z) (L.erase z) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hmiss with ⟨_, hExact⟩
  unfold HasExactLowNeighborhoodOnFinset at hExact ⊢
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rcases Finset.mem_inter.mp hy with ⟨hyN, hyTerase⟩
    have hyT : y ∈ T := (Finset.mem_erase.mp hyTerase).2
    have hyNeZ : y ≠ z := (Finset.mem_erase.mp hyTerase).1
    have hyIn : y ∈ L \ ({z} : Finset V) := by
      rw [← hExact]
      exact Finset.mem_inter.mpr ⟨hyN, hyT⟩
    rcases Finset.mem_sdiff.mp hyIn with ⟨hyL, hyNotSingleton⟩
    exact Finset.mem_erase.mpr ⟨by simpa [Finset.mem_singleton] using hyNotSingleton, hyL⟩
  · intro hy
    rcases Finset.mem_erase.mp hy with ⟨hyNeZ, hyL⟩
    have hyIn : y ∈ L \ ({z} : Finset V) := by
      exact Finset.mem_sdiff.mpr ⟨hyL, by simpa [Finset.mem_singleton] using hyNeZ⟩
    have hyNT : y ∈ G.neighborFinset x ∩ T := hExact.symm ▸ hyIn
    rcases Finset.mem_inter.mp hyNT with ⟨hyN, hyT⟩
    exact Finset.mem_inter.mpr ⟨hyN, Finset.mem_erase.mpr ⟨hyNeZ, hyT⟩⟩

lemma hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodAddTypeOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} {T L : Finset V}
    (hadd : HasLowNeighborhoodAddTypeOnFinset G x T L y) :
    HasExactLowNeighborhoodOnFinset G x (T.erase y) L := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hadd with ⟨hyTL, hExact⟩
  have hyNotL : y ∉ L := (Finset.mem_sdiff.mp hyTL).2
  unfold HasExactLowNeighborhoodOnFinset at hExact ⊢
  apply Finset.ext
  intro v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvN, hvTerase⟩
    have hvIn : v ∈ insert y L := by
      rw [← hExact]
      exact Finset.mem_inter.mpr ⟨hvN, (Finset.mem_erase.mp hvTerase).2⟩
    rcases Finset.mem_insert.mp hvIn with hEq | hvL
    · subst hEq
      exact False.elim <| (Finset.mem_erase.mp hvTerase).1 rfl
    · exact hvL
  · intro hvL
    have hvIn : v ∈ insert y L := Finset.mem_insert.mpr (Or.inr hvL)
    have hvNT : v ∈ G.neighborFinset x ∩ T := hExact.symm ▸ hvIn
    have hvNeY : v ≠ y := by
      intro hEq
      subst hEq
      exact hyNotL hvL
    rcases Finset.mem_inter.mp hvNT with ⟨hvN, hvT⟩
    exact Finset.mem_inter.mpr ⟨hvN, Finset.mem_erase.mpr ⟨hvNeY, hvT⟩⟩

lemma hasExactLowNeighborhoodOnFinset_on_erase
    (G : SimpleGraph V) [DecidableRel G.Adj] {x z : V} {T L : Finset V}
    (hExact : HasExactLowNeighborhoodOnFinset G x T L) :
    HasExactLowNeighborhoodOnFinset G x (T.erase z) (L.erase z) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  unfold HasExactLowNeighborhoodOnFinset at hExact ⊢
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rcases Finset.mem_inter.mp hy with ⟨hyN, hyTerase⟩
    have hyT : y ∈ T := (Finset.mem_erase.mp hyTerase).2
    have hyNeZ : y ≠ z := (Finset.mem_erase.mp hyTerase).1
    have hyNT : y ∈ G.neighborFinset x ∩ T := Finset.mem_inter.mpr ⟨hyN, hyT⟩
    rw [hExact] at hyNT
    exact Finset.mem_erase.mpr ⟨hyNeZ, hyNT⟩
  · intro hy
    rcases Finset.mem_erase.mp hy with ⟨hyNeZ, hyL⟩
    have hyNT : y ∈ G.neighborFinset x ∩ T := by
      rw [hExact]
      exact hyL
    rcases Finset.mem_inter.mp hyNT with ⟨hyN, hyT⟩
    exact Finset.mem_inter.mpr ⟨hyN, Finset.mem_erase.mpr ⟨hyNeZ, hyT⟩⟩

/--
Delete the chosen defect site from `T` for a one-defect outside vertex.
-/
noncomputable def lowNeighborhoodDeletedDefectHostOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (T L : Finset V)
    (hLT : L ⊆ T) (herr : lowNeighborhoodError G x T L = 1) : Finset V := by
  exact T.erase (lowNeighborhoodDefectSite G x T L hLT herr).1

/--
Canonical low set on the deleted-defect host: delete the defect vertex from `L` in the miss case,
and keep `L` unchanged in the add case.
-/
noncomputable def lowNeighborhoodDeletedDefectLowSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (T L : Finset V)
    (hLT : L ⊆ T) (herr : lowNeighborhoodError G x T L = 1) : Finset V := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  exact if HasLowNeighborhoodMissTypeOnFinset G x T L u then L.erase u else L

lemma hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectData
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    HasExactLowNeighborhoodOnFinset G x
      (lowNeighborhoodDeletedDefectHostOnFinset G x T L hLT herr)
      (lowNeighborhoodDeletedDefectLowSetOnFinset G x T L hLT herr) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  have hsite :
      HasLowNeighborhoodMissTypeOnFinset G x T L u ∨
        HasLowNeighborhoodAddTypeOnFinset G x T L u := by
    simpa [u] using
      hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_at_lowNeighborhoodDefectSite
        (G := G) (x := x) (T := T) (L := L) hLT herr
  by_cases hmiss : HasLowNeighborhoodMissTypeOnFinset G x T L u
  · simp [lowNeighborhoodDeletedDefectHostOnFinset, lowNeighborhoodDeletedDefectLowSetOnFinset, u, hmiss]
    exact hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodMissTypeOnFinset (G := G) hmiss
  · have hadd : HasLowNeighborhoodAddTypeOnFinset G x T L u := by
      rcases hsite with hmiss' | hadd
      · exact (hmiss hmiss').elim
      · exact hadd
    simp [lowNeighborhoodDeletedDefectHostOnFinset, lowNeighborhoodDeletedDefectLowSetOnFinset, u, hmiss]
    exact hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodAddTypeOnFinset (G := G) hadd

lemma lowNeighborhoodDeletedDefectLowSetOnFinset_subset_deletedDefectHostOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    lowNeighborhoodDeletedDefectLowSetOnFinset G x T L hLT herr ⊆
      lowNeighborhoodDeletedDefectHostOnFinset G x T L hLT herr := by
  classical
  intro y hy
  have hExact :=
    hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectData
      (G := G) (x := x) (T := T) (L := L) hLT herr
  unfold HasExactLowNeighborhoodOnFinset at hExact
  rw [← hExact] at hy
  exact (Finset.mem_inter.mp hy).2

lemma exists_erase_vertex_hasExactLowNeighborhoodOnFinset_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    ∃ u ∈ T, ∃ L',
      L' ⊆ T.erase u ∧
      HasExactLowNeighborhoodOnFinset G x (T.erase u) L' ∧
      (L' = L.erase u ∨ L' = L) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  let L' := lowNeighborhoodDeletedDefectLowSetOnFinset G x T L hLT herr
  refine ⟨u, ?_, L', ?_, ?_, ?_⟩
  · simpa [u] using (lowNeighborhoodDefectSite G x T L hLT herr).2
  · simpa [L'] using
      lowNeighborhoodDeletedDefectLowSetOnFinset_subset_deletedDefectHostOnFinset
        (G := G) (x := x) (T := T) (L := L) hLT herr
  · simpa [u, L'] using
      hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectData
        (G := G) (x := x) (T := T) (L := L) hLT herr
  · by_cases hmiss : HasLowNeighborhoodMissTypeOnFinset G x T L u
    · left
      simp [u, L', lowNeighborhoodDeletedDefectLowSetOnFinset, hmiss]
    · right
      simp [u, L', lowNeighborhoodDeletedDefectLowSetOnFinset, hmiss]

lemma hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one_of_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1)
    (hmem :
      (lowNeighborhoodDefectSite G x T L hLT herr).1 ∈ L) :
    HasExactLowNeighborhoodOnFinset G x
      (T.erase (lowNeighborhoodDefectSite G x T L hLT herr).1)
      (L.erase (lowNeighborhoodDefectSite G x T L hLT herr).1) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  have hsite :
      HasLowNeighborhoodMissTypeOnFinset G x T L u ∨
        HasLowNeighborhoodAddTypeOnFinset G x T L u := by
    simpa [u] using
      hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_at_lowNeighborhoodDefectSite
        (G := G) (x := x) (T := T) (L := L) hLT herr
  have hmiss : HasLowNeighborhoodMissTypeOnFinset G x T L u := by
    rcases hsite with hmiss | hadd
    · exact hmiss
    · exact ((Finset.mem_sdiff.mp hadd.1).2 (by simpa [u] using hmem)).elim
  simpa [u] using
    hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodMissTypeOnFinset
      (G := G) hmiss

lemma hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one_of_not_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1)
    (hnotmem :
      (lowNeighborhoodDefectSite G x T L hLT herr).1 ∉ L) :
    HasExactLowNeighborhoodOnFinset G x
      (T.erase (lowNeighborhoodDefectSite G x T L hLT herr).1)
      L := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  have hsite :
      HasLowNeighborhoodMissTypeOnFinset G x T L u ∨
        HasLowNeighborhoodAddTypeOnFinset G x T L u := by
    simpa [u] using
      hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_at_lowNeighborhoodDefectSite
        (G := G) (x := x) (T := T) (L := L) hLT herr
  have hadd : HasLowNeighborhoodAddTypeOnFinset G x T L u := by
    rcases hsite with hmiss | hadd
    · exact (hnotmem (by simpa [u] using hmiss.1)).elim
    · exact hadd
  simpa [u] using
    hasExactLowNeighborhoodOnFinset_on_erase_of_hasLowNeighborhoodAddTypeOnFinset
      (G := G) hadd

lemma hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    HasExactLowNeighborhoodOnFinset G x
      (T.erase (lowNeighborhoodDefectSite G x T L hLT herr).1)
      (L.erase (lowNeighborhoodDefectSite G x T L hLT herr).1) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  by_cases hmem : u ∈ L
  · simpa [u] using
      hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one_of_mem
        (G := G) (x := x) (T := T) (L := L) hLT herr hmem
  · have h :=
      hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one_of_not_mem
        (G := G) (x := x) (T := T) (L := L) hLT herr hmem
    have hErase : L.erase u = L := (Finset.erase_eq_self).2 hmem
    simpa [u, hErase] using h

lemma lowNeighborhoodDeletedDefectLowSetOnFinset_eq_erase_defectSite
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herr : lowNeighborhoodError G x T L = 1) :
    lowNeighborhoodDeletedDefectLowSetOnFinset G x T L hLT herr =
      L.erase (lowNeighborhoodDefectSite G x T L hLT herr).1 := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herr).1
  have hsite :
      HasLowNeighborhoodMissTypeOnFinset G x T L u ∨
        HasLowNeighborhoodAddTypeOnFinset G x T L u := by
    simpa [u] using
      hasLowNeighborhoodMissTypeOnFinset_or_hasLowNeighborhoodAddTypeOnFinset_at_lowNeighborhoodDefectSite
        (G := G) (x := x) (T := T) (L := L) hLT herr
  by_cases hmiss : HasLowNeighborhoodMissTypeOnFinset G x T L u
  · simp [lowNeighborhoodDeletedDefectLowSetOnFinset, u, hmiss]
  · rcases hsite with hmiss' | hadd
    · exact (hmiss hmiss').elim
    · have huNotL : u ∉ L := (Finset.mem_sdiff.mp hadd.1).2
      have hErase : L.erase u = L := (Finset.erase_eq_self).2 huNotL
      simpa [lowNeighborhoodDeletedDefectLowSetOnFinset, u, hmiss, hErase]

lemma erase_comm_finset (s : Finset V) (u v : V) :
    (s.erase u).erase v = (s.erase v).erase u := by
  ext x
  simp [and_left_comm, and_assoc]

/--
Delete the two chosen defect sites from `T`.
-/
noncomputable def lowNeighborhoodDeletedDefectPairHostOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (T L : Finset V)
    (hLT : L ⊆ T)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) : Finset V := by
  exact
    (T.erase (lowNeighborhoodDefectSite G x T L hLT herrx).1).erase
      (lowNeighborhoodDefectSite G y T L hLT herry).1

/--
Canonical low set on the common two-defect deleted host.
-/
noncomputable def lowNeighborhoodDeletedDefectPairLowSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (T L : Finset V)
    (hLT : L ⊆ T)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) : Finset V := by
  exact
    (L.erase (lowNeighborhoodDefectSite G x T L hLT herrx).1).erase
      (lowNeighborhoodDefectSite G y T L hLT herry).1

lemma hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData_left
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    HasExactLowNeighborhoodOnFinset G x
      (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
      (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herrx).1
  let v := (lowNeighborhoodDefectSite G y T L hLT herry).1
  have hx :
      HasExactLowNeighborhoodOnFinset G x (T.erase u) (L.erase u) := by
    simpa [u] using
      hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one
        (G := G) (x := x) (T := T) (L := L) hLT herrx
  have hx' :
      HasExactLowNeighborhoodOnFinset G x ((T.erase u).erase v) ((L.erase u).erase v) :=
    hasExactLowNeighborhoodOnFinset_on_erase (G := G) (x := x) (z := v) hx
  simpa [lowNeighborhoodDeletedDefectPairHostOnFinset, lowNeighborhoodDeletedDefectPairLowSetOnFinset, u, v] using hx'

lemma hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData_right
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    HasExactLowNeighborhoodOnFinset G y
      (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
      (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) := by
  classical
  let u := (lowNeighborhoodDefectSite G x T L hLT herrx).1
  let v := (lowNeighborhoodDefectSite G y T L hLT herry).1
  have hy :
      HasExactLowNeighborhoodOnFinset G y (T.erase v) (L.erase v) := by
    simpa [v] using
      hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one
        (G := G) (x := y) (T := T) (L := L) hLT herry
  have hy' :
      HasExactLowNeighborhoodOnFinset G y ((T.erase v).erase u) ((L.erase v).erase u) :=
    hasExactLowNeighborhoodOnFinset_on_erase (G := G) (x := y) (z := u) hy
  simpa [lowNeighborhoodDeletedDefectPairHostOnFinset, lowNeighborhoodDeletedDefectPairLowSetOnFinset,
    u, v, erase_comm_finset] using hy'

lemma hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} {T L : Finset V}
    (hLT : L ⊆ T)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    HasExactLowNeighborhoodOnFinset G x
        (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
        (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) ∧
      HasExactLowNeighborhoodOnFinset G y
        (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
        (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) := by
  exact ⟨
    hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData_left
      (G := G) (x := x) (y := y) (T := T) (L := L) hLT herrx herry,
    hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData_right
      (G := G) (x := x) (y := y) (T := T) (L := L) hLT herrx herry
  ⟩

/--
Finite candidate set for a deleted defect site `u`: vertices of `P` that complete `T \ {u}`.
-/
noncomputable def lowNeighborhoodDeletedDefectCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u : V) : Finset V := by
  classical
  exact P.filter fun x => HasExactLowNeighborhoodOnFinset G x (T.erase u) (L.erase u)

lemma mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u : V) {x : V} :
    x ∈ lowNeighborhoodDeletedDefectCandidateSetOnFinset G P T L u ↔
      x ∈ P ∧ HasExactLowNeighborhoodOnFinset G x (T.erase u) (L.erase u) := by
  classical
  unfold lowNeighborhoodDeletedDefectCandidateSetOnFinset
  simp

/--
Finite candidate set for a deleted defect pair `{u,v}`: vertices of `P` that complete the
common deleted host.
-/
noncomputable def lowNeighborhoodDeletedDefectPairCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v : V) : Finset V := by
  classical
  exact P.filter fun x => HasExactLowNeighborhoodOnFinset G x ((T.erase u).erase v) ((L.erase u).erase v)

lemma mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v : V) {x : V} :
    x ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ↔
      x ∈ P ∧ HasExactLowNeighborhoodOnFinset G x ((T.erase u).erase v) ((L.erase u).erase v) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairCandidateSetOnFinset
  simp

/--
Adjacency trace of a root `z` on a swap pair `{x,y}`.
-/
noncomputable def lowNeighborhoodDeletedDefectPairRootTraceOnFinset
    (G : SimpleGraph V) (x y z : V) : Finset V := by
  classical
  exact ({x, y} : Finset V).filter fun w => w ∈ G.neighborFinset z

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
    (G : SimpleGraph V) [DecidableRel G.Adj] {P T L : Finset V} {u v x y z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hExact :
      HasExactLowNeighborhoodOnFinset G z ((T.erase u).erase v) ((L.erase u).erase v) :=
    (mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      u v (x := z)).1 hz |>.2
  unfold HasExactLowNeighborhoodOnFinset at hExact
  have hMemEq {w : V} :
      w ∈ G.neighborFinset z ∩ ((T.erase u).erase v) ↔ w ∈ ((L.erase u).erase v) := by
    simpa using congrArg (fun s : Finset V => w ∈ s) hExact
  apply Finset.ext
  intro w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hwN, hwBig⟩
    rcases Finset.mem_insert.mp hwBig with rfl | hwBig
    · exact Finset.mem_union.mpr <| Or.inr <| by
        unfold lowNeighborhoodDeletedDefectPairRootTraceOnFinset
        exact Finset.mem_filter.mpr ⟨by simp, hwN⟩
    · rcases Finset.mem_insert.mp hwBig with rfl | hwHost
      · exact Finset.mem_union.mpr <| Or.inr <| by
          unfold lowNeighborhoodDeletedDefectPairRootTraceOnFinset
          exact Finset.mem_filter.mpr ⟨by simp, hwN⟩
      · have hwBase : w ∈ ((L.erase u).erase v) := by
          exact hMemEq.mp (Finset.mem_inter.mpr ⟨hwN, hwHost⟩)
        exact Finset.mem_union.mpr <| Or.inl hwBase
  · intro hw
    rcases Finset.mem_union.mp hw with hwBase | hwRoot
    · have hwPair : w ∈ G.neighborFinset z ∩ ((T.erase u).erase v) := by
        exact hMemEq.mpr hwBase
      rcases Finset.mem_inter.mp hwPair with ⟨hwN, hwHost⟩
      exact Finset.mem_inter.mpr ⟨hwN, by
        exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr hwHost⟩
    · have hwPair : w ∈ ({x, y} : Finset V) := (Finset.mem_filter.mp hwRoot).1
      have hwN : w ∈ G.neighborFinset z := (Finset.mem_filter.mp hwRoot).2
      have hwBig : w ∈ insert x (insert y ((T.erase u).erase v)) := by
        rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl <;> simp
      exact Finset.mem_inter.mpr ⟨hwN, hwBig⟩

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_self_left
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y x =
      if G.Adj x y then ({y} : Finset V) else ∅ := by
  classical
  by_cases hxy : G.Adj x y
  · ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact False.elim (by simpa using hwAdj)
      · simpa [hxy]
    · intro hw
      have hwY : w ∈ ({y} : Finset V) := by
        simpa [hxy] using hw
      have hw' : w = y := by simpa using hwY
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hxy⟩
  · ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact False.elim (by simpa using hwAdj)
      · exact (hxy (by simpa using hwAdj)).elim
    · intro hw
      exact False.elim (by simpa [hxy] using hw)

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_self_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y y =
      if G.Adj x y then ({x} : Finset V) else ∅ := by
  classical
  by_cases hxy : G.Adj x y
  · have hyx : G.Adj y x := hxy.symm
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · simpa [hxy]
      · exact False.elim (by simpa using hwAdj)
    · intro hw
      have hwX : w ∈ ({x} : Finset V) := by
        simpa [hxy] using hw
      have hw' : w = x := by simpa using hwX
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hyx⟩
  · have hyx : ¬ G.Adj y x := by
      intro hyx
      exact hxy hyx.symm
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact (hyx (by simpa using hwAdj)).elim
      · exact False.elim (by simpa using hwAdj)
    · intro hw
      exact False.elim (by simpa [hxy] using hw)

def lowNeighborhoodDeletedDefectPairLeftStatusBit
    (G : SimpleGraph V) (x y z : V) : Prop :=
  y ∈ lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z

def lowNeighborhoodDeletedDefectPairRightStatusBit
    (G : SimpleGraph V) (x y z : V) : Prop :=
  x ∈ lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z

lemma lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V) :
    lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ G.Adj z y := by
  classical
  unfold lowNeighborhoodDeletedDefectPairLeftStatusBit lowNeighborhoodDeletedDefectPairRootTraceOnFinset
  simp

lemma lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V) :
    lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ G.Adj z x := by
  classical
  unfold lowNeighborhoodDeletedDefectPairRightStatusBit lowNeighborhoodDeletedDefectPairRootTraceOnFinset
  simp

noncomputable def lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    (lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v).filter
      fun z => lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ G.Adj x y

noncomputable def lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    (lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v).filter
      fun z => lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ G.Adj x y

noncomputable def lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    (lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v).filter
      fun z => lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ ¬ G.Adj x y

noncomputable def lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    (lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v).filter
      fun z => lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ ¬ G.Adj x y

lemma mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
  simp

lemma mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
  simp

lemma mem_lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ ¬ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
  simp

lemma mem_lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ ¬ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
  simp

noncomputable def lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset G P T L u v x y ∩
      lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset G P T L u v x y

noncomputable def lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset G P T L u v x y ∩
      lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset G P T L u v x y

noncomputable def lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset G P T L u v x y ∩
      lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset G P T L u v x y

noncomputable def lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset G P T L u v x y ∩
      lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset G P T L u v x y

lemma mem_lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ G.Adj x y) ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hzLeft, hzRight⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzLeft with
      ⟨hzCand, hzLeftBit⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzRight with
      ⟨_, hzRightBit⟩
    exact ⟨hzCand, hzLeftBit, hzRightBit⟩
  · rintro ⟨hzCand, hzLeftBit, hzRightBit⟩
    exact ⟨
      (mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzLeftBit⟩,
      (mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzRightBit⟩
    ⟩

lemma mem_lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
        G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ G.Adj x y) ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ ¬ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hzLeft, hzRight⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzLeft with
      ⟨hzCand, hzLeftBit⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzRight with
      ⟨_, hzRightBit⟩
    exact ⟨hzCand, hzLeftBit, hzRightBit⟩
  · rintro ⟨hzCand, hzLeftBit, hzRightBit⟩
    exact ⟨
      (mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzLeftBit⟩,
      (mem_lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzRightBit⟩
    ⟩

lemma mem_lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
        G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ ¬ G.Adj x y) ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hzLeft, hzRight⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzLeft with
      ⟨hzCand, hzLeftBit⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzRight with
      ⟨_, hzRightBit⟩
    exact ⟨hzCand, hzLeftBit, hzRightBit⟩
  · rintro ⟨hzCand, hzLeftBit, hzRightBit⟩
    exact ⟨
      (mem_lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzLeftBit⟩,
      (mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzRightBit⟩
    ⟩

lemma mem_lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset G P T L u v x y ↔
      z ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
        (lowNeighborhoodDeletedDefectPairLeftStatusBit G x y z ↔ ¬ G.Adj x y) ∧
        (lowNeighborhoodDeletedDefectPairRightStatusBit G x y z ↔ ¬ G.Adj x y) := by
  classical
  unfold lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hzLeft, hzRight⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzLeft with
      ⟨hzCand, hzLeftBit⟩
    rcases
      (mem_lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hzRight with
      ⟨_, hzRightBit⟩
    exact ⟨hzCand, hzLeftBit, hzRightBit⟩
  · rintro ⟨hzCand, hzLeftBit, hzRightBit⟩
    exact ⟨
      (mem_lowNeighborhoodDeletedDefectPairLeftFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzLeftBit⟩,
      (mem_lowNeighborhoodDeletedDefectPairRightFlippedStatusCandidateSetOnFinset
        (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).2 ⟨hzCand, hzRightBit⟩
    ⟩

inductive DeletedDefectPairChamberKind
  | fixed
  | leftFixedRightFlipped
  | leftFlippedRightFixed
  | flipped
  deriving DecidableEq

noncomputable def lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset
    (kind : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) (P T L : Finset V) (u v x y : V) : Finset V := by
  classical
  exact
    match kind with
    | .fixed =>
        lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset G P T L u v x y
    | .leftFixedRightFlipped =>
        lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
          G P T L u v x y
    | .leftFlippedRightFixed =>
        lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
          G P T L u v x y
    | .flipped =>
        lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset G P T L u v x y

noncomputable def lowNeighborhoodDeletedDefectPairChamberTraceOnFinset
    (kind : DeletedDefectPairChamberKind) (G : SimpleGraph V) (x y : V) : Finset V := by
  classical
  exact
    match kind with
    | .fixed => if G.Adj x y then ({x, y} : Finset V) else ∅
    | .leftFixedRightFlipped => if G.Adj x y then ({y} : Finset V) else ({x} : Finset V)
    | .leftFlippedRightFixed => if G.Adj x y then ({x} : Finset V) else ({y} : Finset V)
    | .flipped => if G.Adj x y then ∅ else ({x, y} : Finset V)

noncomputable def lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) (P T L : Finset V) (u v : V)
    (x₁ y₁ x₂ y₂ : V) : Finset V := by
  classical
  exact
    lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind₁ G P T L u v x₁ y₁ ∩
      lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind₂ G P T L u v x₂ y₂

lemma mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) (P T L : Finset V) (u v : V)
    (x₁ y₁ x₂ y₂ : V) {z : V} :
    z ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
        kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂ ↔
      z ∈ lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind₁ G P T L u v x₁ y₁ ∧
        z ∈ lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind₂ G P T L u v x₂ y₂ := by
  classical
  unfold lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
  rw [Finset.mem_inter]

/--
One-defect strip inside a packet `P`: the vertices whose low-neighborhood error relative to `(T, L)`
is exactly `1`.
-/
noncomputable def lowNeighborhoodOneDefectSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) : Finset V := by
  classical
  exact P.filter fun x => lowNeighborhoodError G x T L = 1

lemma mem_lowNeighborhoodOneDefectSetOnFinset
    (G : SimpleGraph V) (P T L : Finset V) {x : V} :
    x ∈ lowNeighborhoodOneDefectSetOnFinset G P T L ↔
      x ∈ P ∧ lowNeighborhoodError G x T L = 1 := by
  classical
  unfold lowNeighborhoodOneDefectSetOnFinset
  simp

noncomputable def lowNeighborhoodDefectSiteOfMem
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x : V}
    (hx : x ∈ lowNeighborhoodOneDefectSetOnFinset G P T L) : ↑(T : Set V) := by
  classical
  exact
    lowNeighborhoodDefectSite G x T L hLT
      ((mem_lowNeighborhoodOneDefectSetOnFinset
        (G := G) (P := P) (T := T) (L := L) (x := x)).1 hx).2

/--
Defect fiber `d⁻¹(u)` inside the one-defect strip over `P`.
-/
noncomputable def lowNeighborhoodDefectFiberOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u : V) :
    Finset ↑(lowNeighborhoodOneDefectSetOnFinset G P T L) := by
  classical
  exact
    (lowNeighborhoodOneDefectSetOnFinset G P T L).attach.filter fun x =>
      (lowNeighborhoodDefectSiteOfMem G P T L hLT x.2).1 = u

lemma mem_lowNeighborhoodDefectFiberOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u : V) {x : ↑(lowNeighborhoodOneDefectSetOnFinset G P T L)} :
    x ∈ lowNeighborhoodDefectFiberOnFinset G P T L hLT u ↔
      (lowNeighborhoodDefectSiteOfMem G P T L hLT x.2).1 = u := by
  classical
  unfold lowNeighborhoodDefectFiberOnFinset
  simp

lemma val_mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFiberOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u : V) {x : ↑(lowNeighborhoodOneDefectSetOnFinset G P T L)}
    (hx : x ∈ lowNeighborhoodDefectFiberOnFinset G P T L hLT u) :
    x.1 ∈ lowNeighborhoodDeletedDefectCandidateSetOnFinset G P T L u := by
  classical
  have hxP : x.1 ∈ P :=
    (mem_lowNeighborhoodOneDefectSetOnFinset (G := G) (P := P) (T := T) (L := L) (x := x.1)).1 x.2 |>.1
  have herr :
      lowNeighborhoodError G x.1 T L = 1 :=
    (mem_lowNeighborhoodOneDefectSetOnFinset (G := G) (P := P) (T := T) (L := L) (x := x.1)).1 x.2 |>.2
  have hsite :
      (lowNeighborhoodDefectSite G x.1 T L hLT herr).1 = u := by
    simpa using (mem_lowNeighborhoodDefectFiberOnFinset (G := G) (P := P) (T := T) (L := L)
      hLT u (x := x)).1 hx
  have hExact :
      HasExactLowNeighborhoodOnFinset G x.1 (T.erase u) (L.erase u) := by
    simpa [hsite] using
      hasExactLowNeighborhoodOnFinset_on_erase_defectSite_of_lowNeighborhoodError_eq_one
        (G := G) (x := x.1) (T := T) (L := L) hLT herr
  exact (mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
    u (x := x.1)).2 ⟨hxP, hExact⟩

lemma val_mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFiberOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u v : V) {x : ↑(lowNeighborhoodOneDefectSetOnFinset G P T L)}
    (hx : x ∈ lowNeighborhoodDefectFiberOnFinset G P T L hLT u) :
    x.1 ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v := by
  classical
  have hxP : x.1 ∈ P :=
    (mem_lowNeighborhoodOneDefectSetOnFinset (G := G) (P := P) (T := T) (L := L) (x := x.1)).1 x.2 |>.1
  have hxSingle :
      x.1 ∈ lowNeighborhoodDeletedDefectCandidateSetOnFinset G P T L u :=
    val_mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFiberOnFinset
      (G := G) (P := P) (T := T) (L := L) hLT u hx
  have hExactSingle :
      HasExactLowNeighborhoodOnFinset G x.1 (T.erase u) (L.erase u) :=
    (mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      u (x := x.1)).1 hxSingle |>.2
  have hExactPair :
      HasExactLowNeighborhoodOnFinset G x.1 ((T.erase u).erase v) ((L.erase u).erase v) :=
    hasExactLowNeighborhoodOnFinset_on_erase (G := G) (x := x.1) (z := v) hExactSingle
  exact
    (mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      u v (x := x.1)).2 ⟨hxP, hExactPair⟩

lemma val_mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFibers
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u v : V)
    {x : ↑(lowNeighborhoodOneDefectSetOnFinset G P T L)}
    {y : ↑(lowNeighborhoodOneDefectSetOnFinset G P T L)}
    (hx : x ∈ lowNeighborhoodDefectFiberOnFinset G P T L hLT u)
    (hy : y ∈ lowNeighborhoodDefectFiberOnFinset G P T L hLT v) :
    x.1 ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v ∧
      y.1 ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L u v := by
  classical
  refine ⟨
    val_mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFiberOnFinset
      (G := G) (P := P) (T := T) (L := L) hLT u v hx,
    ?_⟩
  have hyP : y.1 ∈ P :=
    (mem_lowNeighborhoodOneDefectSetOnFinset (G := G) (P := P) (T := T) (L := L) (x := y.1)).1 y.2 |>.1
  have hySingle :
      y.1 ∈ lowNeighborhoodDeletedDefectCandidateSetOnFinset G P T L v :=
    val_mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset_of_mem_lowNeighborhoodDefectFiberOnFinset
      (G := G) (P := P) (T := T) (L := L) hLT v hy
  have hExactSingle :
      HasExactLowNeighborhoodOnFinset G y.1 (T.erase v) (L.erase v) :=
    (mem_lowNeighborhoodDeletedDefectCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      v (x := y.1)).1 hySingle |>.2
  have hExactPair :
      HasExactLowNeighborhoodOnFinset G y.1 ((T.erase v).erase u) ((L.erase v).erase u) :=
    hasExactLowNeighborhoodOnFinset_on_erase (G := G) (x := y.1) (z := u) hExactSingle
  have hExactPair' :
      HasExactLowNeighborhoodOnFinset G y.1 ((T.erase u).erase v) ((L.erase u).erase v) := by
    simpa [erase_comm_finset] using hExactPair
  exact
    (mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      u v (x := y.1)).2 ⟨hyP, hExactPair'⟩

lemma mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_left_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hxP : x ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    x ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1 := by
  classical
  have hExact :
      HasExactLowNeighborhoodOnFinset G x
        (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
        (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) :=
    (hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData
      (G := G) (x := x) (y := y) (T := T) (L := L) hLT herrx herry).1
  exact
    (mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      (x := x)).2 ⟨by simpa using hxP, by simpa [lowNeighborhoodDeletedDefectPairHostOnFinset,
        lowNeighborhoodDeletedDefectPairLowSetOnFinset] using hExact⟩

lemma mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_right_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hyP : y ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    y ∈ lowNeighborhoodDeletedDefectPairCandidateSetOnFinset G P T L
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1 := by
  classical
  have hExact :
      HasExactLowNeighborhoodOnFinset G y
        (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)
        (lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry) :=
    (hasExactLowNeighborhoodOnFinset_on_lowNeighborhoodDeletedDefectPairData
      (G := G) (x := x) (y := y) (T := T) (L := L) hLT herrx herry).2
  exact
    (mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset (G := G) (P := P) (T := T) (L := L)
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      (x := y)).2 ⟨by simpa using hyP, by simpa [lowNeighborhoodDeletedDefectPairHostOnFinset,
        lowNeighborhoodDeletedDefectPairLowSetOnFinset] using hExact⟩

lemma mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset_left_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hxP : x ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    x ∈ lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset G P T L
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      x y := by
  classical
  have hxCand :=
    mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_left_of_lowNeighborhoodError_eq_one
      (G := G) (P := P) (T := T) (L := L) hLT hxP herrx herry
  exact
    (mem_lowNeighborhoodDeletedDefectPairLeftFixedStatusCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L)
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      x y (z := x)).2
      ⟨hxCand, by simpa [lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj]⟩

lemma mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset_right_of_lowNeighborhoodError_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hyP : y ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    y ∈ lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset G P T L
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      x y := by
  classical
  have hyCand :=
    mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_right_of_lowNeighborhoodError_eq_one
      (G := G) (P := P) (T := T) (L := L) hLT hyP herrx herry
  have hstatus : lowNeighborhoodDeletedDefectPairRightStatusBit G x y y ↔ G.Adj x y := by
    rw [lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj]
    constructor <;> intro h <;> exact h.symm
  exact
    (mem_lowNeighborhoodDeletedDefectPairRightFixedStatusCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L)
      (lowNeighborhoodDefectSite G x T L hLT herrx).1
      (lowNeighborhoodDefectSite G y T L hLT herry).1
      x y (z := y)).2
      ⟨hyCand, hstatus⟩

lemma neighborFinset_inter_insert_insert_lowNeighborhoodDeletedDefectPairHostOnFinset_eq_pairLow_union_if_adj_left
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hxP : x ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    G.neighborFinset x ∩
        insert x
          (insert y (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)) =
      lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry ∪
        (if G.Adj x y then ({y} : Finset V) else ∅) := by
  classical
  have hxCand :=
    mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_left_of_lowNeighborhoodError_eq_one
      (G := G) (P := P) (T := T) (L := L) hLT hxP herrx herry
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L)
      (u := (lowNeighborhoodDefectSite G x T L hLT herrx).1)
      (v := (lowNeighborhoodDefectSite G y T L hLT herry).1)
      (x := x) (y := y) (z := x) hxCand
  simpa [lowNeighborhoodDeletedDefectPairHostOnFinset, lowNeighborhoodDeletedDefectPairLowSetOnFinset,
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset_self_left] using h

lemma neighborFinset_inter_insert_insert_lowNeighborhoodDeletedDefectPairHostOnFinset_eq_pairLow_union_if_adj_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) {x y : V}
    (hyP : y ∈ P)
    (herrx : lowNeighborhoodError G x T L = 1)
    (herry : lowNeighborhoodError G y T L = 1) :
    G.neighborFinset y ∩
        insert x
          (insert y (lowNeighborhoodDeletedDefectPairHostOnFinset G x y T L hLT herrx herry)) =
      lowNeighborhoodDeletedDefectPairLowSetOnFinset G x y T L hLT herrx herry ∪
        (if G.Adj x y then ({x} : Finset V) else ∅) := by
  classical
  have hyCand :=
    mem_lowNeighborhoodDeletedDefectPairCandidateSetOnFinset_right_of_lowNeighborhoodError_eq_one
      (G := G) (P := P) (T := T) (L := L) hLT hyP herrx herry
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L)
      (u := (lowNeighborhoodDefectSite G x T L hLT herrx).1)
      (v := (lowNeighborhoodDefectSite G y T L hLT herry).1)
      (x := x) (y := y) (z := y) hyCand
  simpa [lowNeighborhoodDeletedDefectPairHostOnFinset, lowNeighborhoodDeletedDefectPairLowSetOnFinset,
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset_self_right] using h

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_fixedStatusChamber
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z =
      if G.Adj x y then ({x, y} : Finset V) else ∅ := by
  classical
  rcases
    (mem_lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz with
    ⟨_, hzLeft, hzRight⟩
  rw [lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj] at hzLeft
  rw [lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj] at hzRight
  by_cases hxy : G.Adj x y
  · have hzx : G.Adj z x := hzRight.mpr hxy
    have hzy : G.Adj z y := hzLeft.mpr hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, _⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl <;> simp [hxy]
    · intro hw
      have hwXY : w = x ∨ w = y := by simpa [hxy] using hw
      rcases hwXY with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzx⟩
      · exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzy⟩
  · have hzx : ¬ G.Adj z x := by
      intro hzx
      exact hxy (hzRight.mp hzx)
    have hzy : ¬ G.Adj z y := by
      intro hzy
      exact hxy (hzLeft.mp hzy)
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact (hzx (by simpa using hwAdj)).elim
      · exact (hzy (by simpa using hwAdj)).elim
    · intro hw
      exact False.elim (by simpa [hxy] using hw)

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_leftFixedRightFlippedStatusChamber
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z =
      if G.Adj x y then ({y} : Finset V) else ({x} : Finset V) := by
  classical
  rcases
    (mem_lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz with
    ⟨_, hzLeft, hzRight⟩
  rw [lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj] at hzLeft
  rw [lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj] at hzRight
  by_cases hxy : G.Adj x y
  · have hzy : G.Adj z y := hzLeft.mpr hxy
    have hzx : ¬ G.Adj z x := by
      intro hzx
      exact (hzRight.mp hzx) hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact (hzx (by simpa using hwAdj)).elim
      · simpa [hxy]
    · intro hw
      have hwY : w ∈ ({y} : Finset V) := by simpa [hxy] using hw
      have hw' : w = y := by simpa using hwY
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzy⟩
  · have hzy : ¬ G.Adj z y := by
      intro hzy
      exact hxy (hzLeft.mp hzy)
    have hzx : G.Adj z x := hzRight.mpr hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · simpa [hxy]
      · exact (hzy (by simpa using hwAdj)).elim
    · intro hw
      have hwX : w ∈ ({x} : Finset V) := by simpa [hxy] using hw
      have hw' : w = x := by simpa using hwX
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzx⟩

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_leftFlippedRightFixedStatusChamber
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z =
      if G.Adj x y then ({x} : Finset V) else ({y} : Finset V) := by
  classical
  rcases
    (mem_lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz with
    ⟨_, hzLeft, hzRight⟩
  rw [lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj] at hzLeft
  rw [lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj] at hzRight
  by_cases hxy : G.Adj x y
  · have hzy : ¬ G.Adj z y := by
      intro hzy
      exact (hzLeft.mp hzy) hxy
    have hzx : G.Adj z x := hzRight.mpr hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · simpa [hxy]
      · exact (hzy (by simpa using hwAdj)).elim
    · intro hw
      have hwX : w ∈ ({x} : Finset V) := by simpa [hxy] using hw
      have hw' : w = x := by simpa using hwX
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzx⟩
  · have hzy : G.Adj z y := hzLeft.mpr hxy
    have hzx : ¬ G.Adj z x := by
      intro hzx
      exact hxy (hzRight.mp hzx)
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact (hzx (by simpa using hwAdj)).elim
      · simpa [hxy]
    · intro hw
      have hwY : w ∈ ({y} : Finset V) := by simpa [hxy] using hw
      have hw' : w = y := by simpa using hwY
      subst hw'
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzy⟩

lemma lowNeighborhoodDeletedDefectPairRootTraceOnFinset_flippedStatusChamber
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    lowNeighborhoodDeletedDefectPairRootTraceOnFinset G x y z =
      if G.Adj x y then ∅ else ({x, y} : Finset V) := by
  classical
  rcases
    (mem_lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz with
    ⟨_, hzLeft, hzRight⟩
  rw [lowNeighborhoodDeletedDefectPairLeftStatusBit_iff_adj] at hzLeft
  rw [lowNeighborhoodDeletedDefectPairRightStatusBit_iff_adj] at hzRight
  by_cases hxy : G.Adj x y
  · have hzx : ¬ G.Adj z x := by
      intro hzx
      exact (hzRight.mp hzx) hxy
    have hzy : ¬ G.Adj z y := by
      intro hzy
      exact (hzLeft.mp hzy) hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, hwAdj⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl
      · exact (hzx (by simpa using hwAdj)).elim
      · exact (hzy (by simpa using hwAdj)).elim
    · intro hw
      exact False.elim (by simpa [hxy] using hw)
  · have hzx : G.Adj z x := hzRight.mpr hxy
    have hzy : G.Adj z y := hzLeft.mpr hxy
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwPair, _⟩
      rcases (by simpa using hwPair : w = x ∨ w = y) with rfl | rfl <;> simp [hxy]
    · intro hw
      have hwXY : w = x ∨ w = y := by simpa [hxy] using hw
      rcases hwXY with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzx⟩
      · exact Finset.mem_filter.mpr ⟨by simp, by simpa using hzy⟩

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_fixedStatusChamberTrace
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ if G.Adj x y then ({x, y} : Finset V) else ∅ := by
  have hzCand :=
    (mem_lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz |>.1
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y)
      (z := z) hzCand
  simpa [lowNeighborhoodDeletedDefectPairRootTraceOnFinset_fixedStatusChamber
    (G := G) (P := P) (T := T) (L := L) u v x y hz] using h

lemma
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFixedRightFlippedStatusChamberTrace
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ if G.Adj x y then ({y} : Finset V) else ({x} : Finset V) := by
  have hzCand :=
    (mem_lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz |>.1
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y)
      (z := z) hzCand
  simpa [lowNeighborhoodDeletedDefectPairRootTraceOnFinset_leftFixedRightFlippedStatusChamber
    (G := G) (P := P) (T := T) (L := L) u v x y hz] using h

lemma
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFlippedRightFixedStatusChamberTrace
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ if G.Adj x y then ({x} : Finset V) else ({y} : Finset V) := by
  have hzCand :=
    (mem_lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz |>.1
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y)
      (z := z) hzCand
  simpa [lowNeighborhoodDeletedDefectPairRootTraceOnFinset_leftFlippedRightFixedStatusChamber
    (G := G) (P := P) (T := T) (L := L) u v x y hz] using h

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_flippedStatusChamberTrace
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ if G.Adj x y then ∅ else ({x, y} : Finset V) := by
  have hzCand :=
    (mem_lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      (G := G) (P := P) (T := T) (L := L) u v x y (z := z)).1 hz |>.1
  have h :=
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_rootTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y)
      (z := z) hzCand
  simpa [lowNeighborhoodDeletedDefectPairRootTraceOnFinset_flippedStatusChamber
    (G := G) (P := P) (T := T) (L := L) u v x y hz] using h

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_fixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x (insert y ((T.erase u).erase v)) := by
  rw [neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_fixedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz,
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_fixedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz']

lemma
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_leftFixedRightFlippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairLeftFixedRightFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x (insert y ((T.erase u).erase v)) := by
  rw [neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFixedRightFlippedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz,
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFixedRightFlippedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz']

lemma
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_leftFlippedRightFixedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairLeftFlippedRightFixedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x (insert y ((T.erase u).erase v)) := by
  rw [neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFlippedRightFixedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz,
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFlippedRightFixedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz']

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_flippedStatusChamberCandidateSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairFlippedStatusChamberCandidateSetOnFinset
      G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x (insert y ((T.erase u).erase v)) := by
  rw [neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_flippedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz,
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_flippedStatusChamberTrace
      (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz']

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_chamberTrace
    (kind : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      ((L.erase u).erase v) ∪ lowNeighborhoodDeletedDefectPairChamberTraceOnFinset kind G x y := by
  classical
  cases kind with
  | fixed =>
      cases
        Subsingleton.elim (‹DecidableRel G.Adj›)
          (fun a b => Classical.propDecidable (G.Adj a b))
      simpa [lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset,
        lowNeighborhoodDeletedDefectPairChamberTraceOnFinset] using
        neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_fixedStatusChamberTrace
          (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz
  | leftFixedRightFlipped =>
      cases
        Subsingleton.elim (‹DecidableRel G.Adj›)
          (fun a b => Classical.propDecidable (G.Adj a b))
      simpa [lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset,
        lowNeighborhoodDeletedDefectPairChamberTraceOnFinset] using
        neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFixedRightFlippedStatusChamberTrace
          (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz
  | leftFlippedRightFixed =>
      cases
        Subsingleton.elim (‹DecidableRel G.Adj›)
          (fun a b => Classical.propDecidable (G.Adj a b))
      simpa [lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset,
        lowNeighborhoodDeletedDefectPairChamberTraceOnFinset] using
        neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_leftFlippedRightFixedStatusChamberTrace
          (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz
  | flipped =>
      cases
        Subsingleton.elim (‹DecidableRel G.Adj›)
          (fun a b => Classical.propDecidable (G.Adj a b))
      simpa [lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset,
        lowNeighborhoodDeletedDefectPairChamberTraceOnFinset] using
        neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_flippedStatusChamberTrace
          (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCandidateSetOnFinset
    (kind : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v x y : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind G P T L u v x y)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairChamberCandidateSetOnFinset kind G P T L u v x y) :
    G.neighborFinset z ∩ insert x (insert y ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x (insert y ((T.erase u).erase v)) := by
  rw [neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_chamberTrace
      (kind := kind) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz,
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_chamberTrace
      (kind := kind) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x) (y := y) hz']

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCylinderCandidateSetOnFinset_left
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v : V) (x₁ y₁ x₂ y₂ : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂) :
    G.neighborFinset z ∩ insert x₁ (insert y₁ ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x₁ (insert y₁ ((T.erase u).erase v)) := by
  have hz₁ :=
    (mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z)).1 hz |>.1
  have hz₁' :=
    (mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z')).1 hz' |>.1
  exact
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCandidateSetOnFinset
      (kind := kind₁) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x₁) (y := y₁)
      hz₁ hz₁'

lemma neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCylinderCandidateSetOnFinset_right
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v : V) (x₁ y₁ x₂ y₂ : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂) :
    G.neighborFinset z ∩ insert x₂ (insert y₂ ((T.erase u).erase v)) =
      G.neighborFinset z' ∩ insert x₂ (insert y₂ ((T.erase u).erase v)) := by
  have hz₂ :=
    (mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z)).1 hz |>.2
  have hz₂' :=
    (mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z')).1 hz' |>.2
  exact
    neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCandidateSetOnFinset
      (kind := kind₂) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) (x := x₂) (y := y₂)
      hz₂ hz₂'

/--
The repaired packet-state on a common edge, read through the two incident repaired pair hosts.
-/
noncomputable def lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (T L : Finset V)
    (u v x₁ y₁ x₂ y₂ z : V) : Finset V × Finset V := by
  exact
    ( G.neighborFinset z ∩ insert x₁ (insert y₁ ((T.erase u).erase v)),
      G.neighborFinset z ∩ insert x₂ (insert y₂ ((T.erase u).erase v)) )

/--
Packet-state profile forced by a fixed pair-chamber cylinder.
-/
noncomputable def lowNeighborhoodDeletedDefectPairChamberCylinderPacketStateProfileOnFinset
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : Finset V)
    (u v x₁ y₁ x₂ y₂ : V) : Finset V × Finset V := by
  classical
  exact
    ( ((L.erase u).erase v) ∪ lowNeighborhoodDeletedDefectPairChamberTraceOnFinset kind₁ G x₁ y₁,
      ((L.erase u).erase v) ∪ lowNeighborhoodDeletedDefectPairChamberTraceOnFinset kind₂ G x₂ y₂ )

lemma
    lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset_eq_profile_of_mem_chamberCylinderCandidateSetOnFinset
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v : V) (x₁ y₁ x₂ y₂ : V) {z : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂) :
    lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset
        G T L u v x₁ y₁ x₂ y₂ z =
      lowNeighborhoodDeletedDefectPairChamberCylinderPacketStateProfileOnFinset
        kind₁ kind₂ G L u v x₁ y₁ x₂ y₂ := by
  apply Prod.ext
  · simpa [lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset,
      lowNeighborhoodDeletedDefectPairChamberCylinderPacketStateProfileOnFinset] using
      neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_chamberTrace
        (kind := kind₁) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v)
        (x := x₁) (y := y₁)
        ((mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
          kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z)).1 hz).1
  · simpa [lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset,
      lowNeighborhoodDeletedDefectPairChamberCylinderPacketStateProfileOnFinset] using
      neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_deletedDefectPairLowSet_union_chamberTrace
        (kind := kind₂) (G := G) (P := P) (T := T) (L := L) (u := u) (v := v)
        (x := x₂) (y := y₂)
        ((mem_lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
          kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) u v x₁ y₁ x₂ y₂ (z := z)).1 hz).2

lemma lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset_eq_of_mem_chamberCylinderCandidateSetOnFinset
    (kind₁ kind₂ : DeletedDefectPairChamberKind)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (u v : V) (x₁ y₁ x₂ y₂ : V) {z z' : V}
    (hz : z ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂)
    (hz' : z' ∈ lowNeighborhoodDeletedDefectPairChamberCylinderCandidateSetOnFinset
      kind₁ kind₂ G P T L u v x₁ y₁ x₂ y₂) :
    lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset
        G T L u v x₁ y₁ x₂ y₂ z =
      lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset
        G T L u v x₁ y₁ x₂ y₂ z' := by
  apply Prod.ext
  · simpa [lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset] using
      neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCylinderCandidateSetOnFinset_left
        kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) x₁ y₁ x₂ y₂ hz hz'
  · simpa [lowNeighborhoodDeletedDefectPairCommonEdgePacketStateOnFinset] using
      neighborFinset_inter_insert_insert_deletedDefectPairHost_eq_of_mem_chamberCylinderCandidateSetOnFinset_right
        kind₁ kind₂ (G := G) (P := P) (T := T) (L := L) (u := u) (v := v) x₁ y₁ x₂ y₂ hz hz'

/--
Multiplicity of a defect site `u ∈ T` inside the one-defect strip over `P`.
-/
noncomputable def lowNeighborhoodDefectMultiplicityOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u : V) : ℕ := by
  classical
  exact
    ((lowNeighborhoodOneDefectSetOnFinset G P T L).attach.filter fun x =>
      (lowNeighborhoodDefectSiteOfMem G P T L hLT x.2).1 = u).card

lemma lowNeighborhoodDefectMultiplicityOnFinset_eq_card_lowNeighborhoodDefectFiberOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (u : V) :
    lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u =
      (lowNeighborhoodDefectFiberOnFinset G P T L hLT u).card := by
  unfold lowNeighborhoodDefectMultiplicityOnFinset lowNeighborhoodDefectFiberOnFinset
  rfl

/--
Number of one-defect vertices in `P` whose chosen defect site lies in `Y ⊆ T`.
-/
noncomputable def lowNeighborhoodDefectCountOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (Y : Finset V) : ℕ := by
  classical
  exact
    ((lowNeighborhoodOneDefectSetOnFinset G P T L).attach.filter fun x =>
      (lowNeighborhoodDefectSiteOfMem G P T L hLT x.2).1 ∈ Y).card

lemma lowNeighborhoodDefectCountOnFinset_eq_sum_lowNeighborhoodDefectMultiplicityOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (Y : Finset V) :
    lowNeighborhoodDefectCountOnFinset G P T L hLT Y =
      Y.sum (fun u => lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u) := by
  classical
  unfold lowNeighborhoodDefectCountOnFinset lowNeighborhoodDefectMultiplicityOnFinset
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp

lemma lowNeighborhoodDefectCountOnFinset_le_capacity_of_forall_lowNeighborhoodDefectMultiplicityOnFinset_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (Y : Finset V) (q : ℕ)
    (hmu : ∀ u ∈ Y, lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u ≤ q - 1) :
    lowNeighborhoodDefectCountOnFinset G P T L hLT Y ≤ (q - 1) * Y.card := by
  rw [lowNeighborhoodDefectCountOnFinset_eq_sum_lowNeighborhoodDefectMultiplicityOnFinset]
  calc
    Y.sum (fun u => lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u) ≤
        Y.sum (fun _ => q - 1) := by
      exact Finset.sum_le_sum fun u hu => hmu u hu
    _ = (q - 1) * Y.card := by
      simp [Nat.mul_comm]

lemma lowNeighborhoodDefectCountOnFinset_le_capacity_iff_forall_lowNeighborhoodDefectMultiplicityOnFinset_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L w : Finset V)
    (hLT : L ⊆ T) (q : ℕ) :
    (∀ Y, Y ⊆ w →
      lowNeighborhoodDefectCountOnFinset G P T L hLT Y ≤ (q - 1) * Y.card) ↔
      ∀ u ∈ w, lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u ≤ q - 1 := by
  constructor
  · intro hY u hu
    have hsingle :
        lowNeighborhoodDefectCountOnFinset G P T L hLT ({u} : Finset V) ≤
          (q - 1) * ({u} : Finset V).card := by
      exact hY {u} (by
        intro v hv
        have hv' : v = u := by simpa using hv
        simpa [hv'] using hu)
    rw [lowNeighborhoodDefectCountOnFinset_eq_sum_lowNeighborhoodDefectMultiplicityOnFinset] at hsingle
    simpa [Nat.mul_comm] using hsingle
  · intro hmu Y hY
    exact
      lowNeighborhoodDefectCountOnFinset_le_capacity_of_forall_lowNeighborhoodDefectMultiplicityOnFinset_le
        (G := G) (P := P) (T := T) (L := L) (hLT := hLT) (Y := Y) (q := q)
        (fun u hu => hmu u (hY hu))

lemma lowNeighborhoodDefectCountOnFinset_eq_card_lowNeighborhoodOneDefectSetOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L w : Finset V)
    (hLT : L ⊆ T)
    (hsupport :
      ∀ x (hx : x ∈ lowNeighborhoodOneDefectSetOnFinset G P T L),
        (lowNeighborhoodDefectSiteOfMem G P T L hLT hx).1 ∈ w) :
    lowNeighborhoodDefectCountOnFinset G P T L hLT w =
      (lowNeighborhoodOneDefectSetOnFinset G P T L).card := by
  classical
  set O₁ := lowNeighborhoodOneDefectSetOnFinset G P T L
  unfold lowNeighborhoodDefectCountOnFinset
  have hfilterEq :
      (O₁.attach.filter fun x => (lowNeighborhoodDefectSiteOfMem G P T L hLT x.2).1 ∈ w) =
        O₁.attach := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, hsupport x.1 (by simpa [O₁] using x.2)⟩
  rw [hfilterEq]
  simp [O₁]

lemma exists_lowNeighborhoodDefectMultiplicityOnFinset_ge_q_of_card_lowNeighborhoodOneDefectSetOnFinset_gt_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L w : Finset V)
    (hLT : L ⊆ T) {q : ℕ} (hq : 0 < q)
    (hsupport :
      ∀ x (hx : x ∈ lowNeighborhoodOneDefectSetOnFinset G P T L),
        (lowNeighborhoodDefectSiteOfMem G P T L hLT hx).1 ∈ w)
    (hover :
      (lowNeighborhoodOneDefectSetOnFinset G P T L).card > (q - 1) * w.card) :
    ∃ u ∈ w, q ≤ lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u := by
  classical
  by_contra hnone
  have hmu : ∀ u ∈ w, lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u ≤ q - 1 := by
    intro u hu
    have hnot : ¬ q ≤ lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u := by
      intro hqu
      exact hnone ⟨u, hu, hqu⟩
    exact Nat.le_pred_of_lt (Nat.lt_of_not_ge hnot)
  have hcap :
      lowNeighborhoodDefectCountOnFinset G P T L hLT w ≤ (q - 1) * w.card := by
    exact
      lowNeighborhoodDefectCountOnFinset_le_capacity_of_forall_lowNeighborhoodDefectMultiplicityOnFinset_le
        (G := G) (P := P) (T := T) (L := L) (hLT := hLT) (Y := w) (q := q) hmu
  rw [lowNeighborhoodDefectCountOnFinset_eq_card_lowNeighborhoodOneDefectSetOnFinset
      (G := G) (P := P) (T := T) (L := L) (w := w) hLT hsupport] at hcap
  exact (Nat.not_le_of_lt hover) hcap

/--
Hall quantity on the one-defect strip over `P`, measured against anchor capacity `q - 1` on a test
set `Y ⊆ T`.
-/
noncomputable def lowNeighborhoodHallQuantityOnFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (q : ℕ) (Y : Finset V) : Int := by
  exact
    (lowNeighborhoodDefectCountOnFinset G P T L hLT Y : Int) -
      ((((q - 1) * Y.card : ℕ) : Int))

lemma lowNeighborhoodHallQuantityOnFinset_eq_sum_lowNeighborhoodDefectMultiplicityOnFinset_sub_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P T L : Finset V)
    (hLT : L ⊆ T) (q : ℕ) (Y : Finset V) :
    lowNeighborhoodHallQuantityOnFinset G P T L hLT q Y =
      Y.sum (fun u =>
        ((lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u : Int) -
          (((q - 1 : ℕ) : Int)))) := by
  classical
  unfold lowNeighborhoodHallQuantityOnFinset
  rw [lowNeighborhoodDefectCountOnFinset_eq_sum_lowNeighborhoodDefectMultiplicityOnFinset]
  have hsumCast :
      ((Y.sum fun u => lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u : ℕ) : Int) =
        Y.sum (fun u => (lowNeighborhoodDefectMultiplicityOnFinset G P T L hLT u : Int)) := by
    simp
  have hconst :
      ((((q - 1) * Y.card : ℕ) : Int)) = Y.sum (fun _ => (((q - 1 : ℕ) : Int))) := by
    simp [Finset.sum_const, Nat.mul_comm]
  rw [hsumCast, hconst, ← Finset.sum_sub_distrib]

/--
Exact-cardinality fixed-modulus single-control modular host witness with prescribed control-set size
`r`, together with the missing dropped-part residue on `s \ u`.

This is the honest extra finite datum behind the stripped direct exact-upgrade route: once `r < q`,
the modular control-degree data below collapse automatically to exact equality.
-/
def HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, u.card = k ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ t.card = r ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    (∀ v w : ↑(u : Set V),
      (G.neighborFinset v ∩ (s \ u)).card ≡
        (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card ≡ e [MOD q]

/--
Exact-cardinality terminal bridge package for the one-control host problem.

Besides the host residue in `G[s]`, this packages the dropped-part residue on `s \ u` and freezes the
control degree into `t` exactly. This is the literal finite input used by the exact host-to-regular
collapse theorem below.
-/
def HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, u.card = k ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    (∀ v w : ↑(u : Set V),
      (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e

/--
Exact-cardinality fixed-modulus single-control residue host witness with prescribed control-set size
`r`.
-/
def HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ u s t : Finset V, u.card = k ∧ ∃ hu : u ⊆ s, 0 < t.card ∧ t.card = r ∧ Disjoint s t ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
        (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
    (∀ v w : ↑(u : Set V),
      (G.neighborFinset v ∩ (s \ u)).card ≡
        (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
    ∃ e : ℕ, ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e

/--
A composable fixed-modulus control-block modular host witness of size at least `k`: a bucket `u`
inside a larger host `s`, together with a fixed modulus `q` and a nonempty separated control-block
family, such that the degrees in `G[s]` are constant modulo `q` on `u` and each control block
contributes a separately constant residue modulo `q` on `u`.

Unlike `HasControlBlockModularBucketingWitnessOfCard`, this package does not try to record the
dropped-part residue from `s` down to `u`; it is the smaller fixed-modulus object suggested by the
dyadic-lift note for composable restriction arguments.
-/
def HasFixedModulusControlBlockModularHostWitnessOfCard
    (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ ∃ hu : u ⊆ s,
    ∃ blocks : List (Finset V × ℕ),
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      (∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G u q blocks

/--
A bounded composable fixed-modulus control-block modular host witness using at most `r` control
blocks.
-/
def HasBoundedFixedModulusControlBlockModularHostWitnessOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ u s : Finset V, k ≤ u.card ∧ ∃ hu : u ⊆ s,
    ∃ blocks : List (Finset V × ℕ),
      blocks.length ≤ r ∧
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated s blocks ∧
      (∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G u q blocks

/--
Refined host-step data produced from a bounded fixed-modulus control-block modular host witness after
splitting off an exact control block of size `q - 1`.

This packages the full output currently exposed by the main host-step refinement theorem in
`Modular/Cascade.lean`: a surviving bucket `w` inside a host `s`, one distinguished exact control
block `t`, the remaining separated control blocks, ambient modular degree data on
`s ∪ controlBlockUnion ((t, e) :: blocks)`, exact degree into `t`, modular host degree on `s`, and
the residual external-block congruence data.
-/
def HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, ∃ hw : w ⊆ s, ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ,
    k ≤ w.card ∧
    t.card = q - 1 ∧
    blocks.length ≤ r ∧
    ControlBlocksSeparated s ((t, e) :: blocks) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
    (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
        (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
    HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)

/--
Exact-cardinality version of the refinement-data package produced by the current host-step theorem.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s, ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ,
    t.card = q - 1 ∧
    blocks.length ≤ r ∧
    ControlBlocksSeparated s ((t, e) :: blocks) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
    (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
        (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
    HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)

/--
Exact-cardinality refinement-data package together with a residue-controlled partition of the
internal tail `s \ w`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks tailBlocks : List (Finset V × ℕ), ∃ e : ℕ,
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      controlBlockUnion tailBlocks = s \ w ∧
      ControlBlocksSeparated w tailBlocks ∧
      HasConstantModExternalBlockDegrees G w q tailBlocks

/--
Exact-cardinality refinement-data package together with a dyadic pairing tree for the dropped-part
columns of `s \ w` relative to the current bucket `w`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ, ∃ j : ℕ,
      q = 2 ^ j ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      ∃ cols : List (BinaryColumn ↑(w : Set V)),
        (∀ v : ↑(w : Set V),
          binaryColumnRowSum cols v = (G.neighborFinset v.1 ∩ (s \ w)).card) ∧
        HasDyadicPairingTree j cols

/--
Exact-cardinality refinement-data package together with a first-bit binary packet decomposition of the
dropped-part columns and a recursive dyadic divisibility chain on the halved dropped-part degree
function.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ, ∃ j : ℕ,
      q = 2 ^ (j + 1) ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      ∃ packets : List (List (BinaryColumn ↑(w : Set V))),
        (∀ v : ↑(w : Set V),
          binaryColumnRowSum (flattenBinaryPackets packets) v =
            (G.neighborFinset v.1 ∩ (s \ w)).card) ∧
        HasBinaryZeroSumPacketPartition packets ∧
        HasDyadicRowDivisibilityChain j
          (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card / 2)

/--
Exact-cardinality refinement-data package together with a dyadic divisibility chain for the dropped
part degree function on the current bucket `w`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ, ∃ j : ℕ,
      q = 2 ^ j ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      HasDyadicRowDivisibilityChain j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card)

/--
Exact-cardinality refinement-data package together with an explicit terminal dyadic tail after `j`
halving steps on the dropped-part degree function, plus mod-2 constancy of that terminal tail.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ, ∃ j : ℕ,
      q = 2 ^ (j + 1) ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      ∃ tail : ↑(w : Set V) → ℕ,
        HasDyadicRowDivisibilityChainTo j
          (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail ∧
        (∀ v w' : ↑(w : Set V), tail v ≡ tail w' [MOD 2])

/--
Exact-cardinality refinement-data package with the dyadic tail expressed in the note's beta
language.  After `j` halving steps, beta-vanishing says every residual terminal tail has constant
parity; the concrete row is the dropped-part degree `|N(v) ∩ (s \ w)|`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ, ∃ j : ℕ,
      ∃ row tail : ↑(w : Set V) → ℕ,
      q = 2 ^ (j + 1) ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      (∀ v, row v = (G.neighborFinset v.1 ∩ (s \ w)).card) ∧
      HasDyadicRowDivisibilityChainTo j row tail ∧
      DyadicTailBetaVanishesAt j row

/--
Exact-cardinality refinement-data package with beta-vanishing at every dyadic level below `j`.
Unlike `HasExact...DyadicBetaDataOfCard`, this package does not assume a pre-existing terminal
chain: the chain is constructed by `hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s,
    ∃ blocks : List (Finset V × ℕ), ∃ e j : ℕ, ∃ row : ↑(w : Set V) → ℕ,
      q = 2 ^ j ∧
      t.card = q - 1 ∧
      blocks.length ≤ r ∧
      ControlBlocksSeparated s ((t, e) :: blocks) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
      (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
      (∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
      HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks) ∧
      (∀ v, row v = (G.neighborFinset v.1 ∩ (s \ w)).card) ∧
      DyadicTailBetaVanishesUpTo j row

/--
Exact-cardinality refinement-data package together with the smaller ambient congruence on
`w ∪ controlBlockUnion ((t, e) :: blocks)` that is sufficient to recover the dropped-part residue
on `s \ w`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s, ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ,
    t.card = q - 1 ∧
    blocks.length ≤ r ∧
    ControlBlocksSeparated s ((t, e) :: blocks) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G (w ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (w ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨w', Finset.mem_union.mpr (Or.inl w'.2)⟩ [MOD q]) ∧
    (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
        (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
    HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)

/--
Exact-cardinality refinement-data package together with the missing dropped-part residue on `s \ w`.
-/
def HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
    (G : SimpleGraph V) (k q r : ℕ) : Prop := by
  classical
  exact ∃ w s t : Finset V, w.card = k ∧ ∃ hw : w ⊆ s, ∃ blocks : List (Finset V × ℕ), ∃ e : ℕ,
    t.card = q - 1 ∧
    blocks.length ≤ r ∧
    ControlBlocksSeparated s ((t, e) :: blocks) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
          ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q]) ∧
    (∀ v w' : ↑(w : Set V),
      (G.neighborFinset v ∩ (s \ w)).card ≡
        (G.neighborFinset w' ∩ (s \ w)).card [MOD q]) ∧
    (∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e) ∧
    (∀ v w' : ↑(w : Set V),
      (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
        (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q]) ∧
    HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (href : HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases href with ⟨w, s, t, hw, blocks, e, hwk, htcard, hlen, hsep, hdegAmbient, hctrl, hdegHost, hext⟩
  rcases exists_subset_card_eq_of_le_card (s := w) hwk with ⟨u, huW, huk⟩
  refine ⟨u, s, t, huk, ?_, blocks, e, htcard, hlen, hsep, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hw (huW hx)
  · intro v w'
    exact hdegAmbient ⟨v.1, huW v.2⟩ ⟨w'.1, huW w'.2⟩
  · intro v
    exact hctrl ⟨v.1, huW v.2⟩
  · intro v w'
    exact hdegHost ⟨v.1, huW v.2⟩ ⟨w'.1, huW w'.2⟩
  · exact hasConstantModExternalBlockDegrees_mono (G := G) huW hext

lemma
    hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hq : 1 < q)
    (href : HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard G k q r) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard G k q (q - 1) := by
  rcases href with ⟨w, s, t, hwk, hw, blocks, e, htcard, _hlen, hsep, _hdegAmbient, hctrl, hdegHost, _hext⟩
  rcases hsep with ⟨hst, _htail, _hsepTail⟩
  have htpos : 0 < t.card := by
    rw [htcard]
    exact Nat.sub_pos_of_lt hq
  refine ⟨w, s, t, hwk, hw, htpos, htcard, hst, hdegHost, e, ?_⟩
  intro v
  simpa [hctrl v] using (Nat.ModEq.refl e : e ≡ e [MOD q])

lemma
    hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hq : 1 < q)
    (href : HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G k q r) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard G k q (q - 1) := by
  exact
    hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
      (G := G) hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
        (G := G) href)

lemma hasFixedModulusSingleControlModularHostWitnessOfCard_mono
    (G : SimpleGraph V) {k ℓ q : ℕ} (hkℓ : k ≤ ℓ)
    (hhost : HasFixedModulusSingleControlModularHostWitnessOfCard G ℓ q) :
    HasFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, t, hℓ, hu, ht, hst, hdeg, e, hext⟩
  exact ⟨u, s, t, le_trans hkℓ hℓ, hu, ht, hst, hdeg, e, hext⟩

lemma hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlModularHostWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G k q) :
    HasFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, hst, hdeg, e, hext⟩
  exact ⟨u, s, t, by simpa [hku], hu, ht, hst, hdeg, e, hext⟩

lemma hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) {k q r : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard G k q r) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, _htr, hst, hdeg, e, hext⟩
  exact ⟨u, s, t, hku, hu, ht, hst, hdeg, e, hext⟩

lemma
    hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) {q r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard G q r) :
    HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard G q := by
  rcases hhost with ⟨s, t, hsq, ht, _htr, hst, hdeg, e, hext⟩
  exact ⟨s, t, hsq, ht, hst, hdeg, e, hext⟩

lemma
    hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
    (G : SimpleGraph V) {k q r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard G k q r) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard G k q r := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, _hdrop, e, hext⟩
  exact ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, e, hext⟩

lemma
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) {k q r : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r) :
    HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, _htr, hst, hdeg, hdrop, e, hext⟩
  exact ⟨u, s, t, hku, hu, ht, hst, hdeg, hdrop, e, hext⟩

lemma
    hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) {k q r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r) :
    HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard G k q r := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, hdrop, e, hext⟩
  refine ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, hdrop, e, ?_⟩
  intro v
  simpa [hext v] using (Nat.ModEq.refl e : e ≡ e [MOD q])

lemma hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasFixedModulusSingleControlModularHostWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ}
    (hhost : HasFixedModulusSingleControlModularHostWitnessOfCard G k q) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  classical
  rcases hhost with ⟨u, s, t, hku, hu, ht, hst, hdeg, e, hext⟩
  rcases exists_subset_card_eq_of_le_card hku with ⟨w, hwu, hwk⟩
  refine ⟨w, s, t, hwk, ?_, ht, hst, ?_, e, ?_⟩
  · intro x hx
    exact hu (hwu hx)
  · intro v w'
    exact hdeg ⟨v.1, hwu v.2⟩ ⟨w'.1, hwu w'.2⟩
  · intro v
    exact hext ⟨v.1, hwu v.2⟩

lemma
    hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k q) :
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, t, hku, hu, ht, hst, hdeg, _hdrop, e, hext⟩
  refine ⟨u, s, t, hku, hu, ht, hst, hdeg, e, ?_⟩
  intro v
  simpa [hext v] using (Nat.ModEq.refl e : e ≡ e [MOD q])

lemma
    hasFixedModulusControlBlockModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
    (G : SimpleGraph V) {k q r : ℕ}
    (hbounded : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q r) :
    HasFixedModulusControlBlockModularHostWitnessOfCard G k q := by
  rcases hbounded with ⟨u, s, hku, hu, blocks, _hlen, hnonempty, hsep, hdeg, hext⟩
  exact ⟨u, s, hku, hu, blocks, hnonempty, hsep, hdeg, hext⟩

private noncomputable def finsetSubtypeMapEquiv_host {W : Type*} [DecidableEq W]
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

private noncomputable def inducedOnIsoMap_host {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ↪g G') (s : Finset V) :
    inducedOn G s ≃g inducedOn G' (s.map e.toEmbedding) where
  toEquiv := finsetSubtypeMapEquiv_host e.toEmbedding
  map_rel_iff' := by
    intro a b
    simpa [finsetSubtypeMapEquiv_host, inducedOn] using (e.map_adj_iff (v := a) (w := b))

private def mapControlBlocks {W : Type*} [DecidableEq W] (e : V ↪ W) :
    List (Finset V × ℕ) → List (Finset W × ℕ)
  | [] => []
  | (t, r) :: blocks => (t.map e, r) :: mapControlBlocks e blocks

private lemma controlBlockUnion_mapControlBlocks {W : Type*} [DecidableEq W] (e : V ↪ W) :
    ∀ blocks : List (Finset V × ℕ),
      controlBlockUnion (mapControlBlocks e blocks) = (controlBlockUnion blocks).map e
  | [] => by simp [mapControlBlocks, controlBlockUnion]
  | (t, r) :: blocks => by
      simp [mapControlBlocks, controlBlockUnion, controlBlockUnion_mapControlBlocks,
        Finset.map_union]

private lemma length_mapControlBlocks {W : Type*} [DecidableEq W] (e : V ↪ W) :
    ∀ blocks : List (Finset V × ℕ), (mapControlBlocks e blocks).length = blocks.length
  | [] => by simp [mapControlBlocks]
  | (_t, _r) :: blocks => by simp [mapControlBlocks, length_mapControlBlocks]

private lemma nonemptyControlBlockUnion_mapControlBlocks {W : Type*} [DecidableEq W] (e : V ↪ W)
    {blocks : List (Finset V × ℕ)} (hnonempty : NonemptyControlBlockUnion blocks) :
    NonemptyControlBlockUnion (mapControlBlocks e blocks) := by
  unfold NonemptyControlBlockUnion at hnonempty ⊢
  rw [controlBlockUnion_mapControlBlocks, Finset.card_map]
  exact hnonempty

private lemma disjoint_map_of_disjoint {W : Type*} [DecidableEq W] (e : V ↪ W) {s t : Finset V}
    (hdisj : Disjoint s t) : Disjoint (s.map e) (t.map e) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxS hxT
  rcases Finset.mem_map.mp hxS with ⟨y, hy, hxy⟩
  rcases Finset.mem_map.mp hxT with ⟨z, hz, hxz⟩
  exact (Finset.disjoint_left.mp hdisj) hy (e.injective (hxy.trans hxz.symm) ▸ hz)

private lemma controlBlocksSeparated_mapControlBlocks {W : Type*} [DecidableEq W]
    (e : V ↪ W) {s : Finset V} :
    ∀ {blocks : List (Finset V × ℕ)},
      ControlBlocksSeparated s blocks →
        ControlBlocksSeparated (s.map e) (mapControlBlocks e blocks)
  | [], _ => by simp [ControlBlocksSeparated, mapControlBlocks]
  | (t, r) :: blocks, hsep => by
      rcases hsep with ⟨hst, htail, hrest⟩
      refine ⟨disjoint_map_of_disjoint e hst, ?_, controlBlocksSeparated_mapControlBlocks e hrest⟩
      rw [controlBlockUnion_mapControlBlocks]
      exact disjoint_map_of_disjoint e htail

private lemma card_neighborFinset_inter_map_eq {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ↪g G') (v : V) (t : Finset V) :
    (G'.neighborFinset (e v) ∩ t.map e.toEmbedding).card = (G.neighborFinset v ∩ t).card := by
  classical
  have hmap :
      (G'.neighborFinset (e v) ∩ t.map e.toEmbedding) =
        (G.neighborFinset v ∩ t).map e.toEmbedding := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxAdj, hxT⟩
      rcases Finset.mem_map.mp hxT with ⟨y, hy, rfl⟩
      refine Finset.mem_map.mpr ⟨y, ?_, rfl⟩
      have hyAdj : G.Adj v y := by
        exact (e.map_adj_iff (v := v) (w := y)).mp (by simpa using hxAdj)
      exact Finset.mem_inter.mpr ⟨by simpa using hyAdj, hy⟩
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_inter.mp hy with ⟨hyAdj, hyT⟩
      have hyAdj' : G'.Adj (e v) (e y) := by
        exact (e.map_adj_iff (v := v) (w := y)).mpr (by simpa using hyAdj)
      exact Finset.mem_inter.mpr ⟨by simpa using hyAdj', Finset.mem_map.mpr ⟨y, hyT, rfl⟩⟩
  rw [hmap, Finset.card_map]

private lemma hasConstantModExternalBlockDegrees_mapControlBlocks
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ↪g G') {s : Finset V} {q : ℕ} :
    ∀ {blocks : List (Finset V × ℕ)},
      HasConstantModExternalBlockDegrees G s q blocks →
        HasConstantModExternalBlockDegrees G' (s.map e.toEmbedding) q
          (mapControlBlocks e.toEmbedding blocks)
  | [], hext => by
      simpa [HasConstantModExternalBlockDegrees, mapControlBlocks] using hext
  | (t, r) :: blocks, hext => by
      rcases hext with ⟨hhead, htail⟩
      refine ⟨?_, hasConstantModExternalBlockDegrees_mapControlBlocks e htail⟩
      intro v
      rcases Finset.mem_map.mp v.2 with ⟨x, hx, hxEq⟩
      have hcard :
          (G'.neighborFinset v ∩ t.map e.toEmbedding).card = (G.neighborFinset x ∩ t).card := by
        change (G'.neighborFinset v.1 ∩ t.map e.toEmbedding).card = (G.neighborFinset x ∩ t).card
        have hvx : v.1 = e x := by simpa using hxEq.symm
        rw [hvx]
        exact card_neighborFinset_inter_map_eq e x t
      simpa [hcard] using hhead ⟨x, hx⟩

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_embedding
    {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ↪g G') {k q r : ℕ}
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q r) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G' k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  cases
    Subsingleton.elim (‹DecidableRel G'.Adj›)
      (fun a b => Classical.propDecidable (G'.Adj a b))
  rcases hhost with ⟨u, s, hku, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  let u' : Finset W := u.map e.toEmbedding
  let s' : Finset W := s.map e.toEmbedding
  let blocks' := mapControlBlocks e.toEmbedding blocks
  have hu' : u' ⊆ s' := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact Finset.mem_map.mpr ⟨v, hu hv, rfl⟩
  have hdeg' :
      ∀ v w : ↑(u' : Set W),
        (inducedOn G' s').degree ⟨v.1, hu' v.2⟩ ≡
          (inducedOn G' s').degree ⟨w.1, hu' w.2⟩ [MOD q] := by
    let hIso := inducedOnIsoMap_host e s
    intro v w
    rcases Finset.mem_map.mp v.2 with ⟨v0, hv0, hvEq⟩
    rcases Finset.mem_map.mp w.2 with ⟨w0, hw0, hwEq⟩
    have hIso_v :
        hIso ⟨v0, hu hv0⟩ = ⟨v.1, hu' v.2⟩ := by
      apply Subtype.ext
      exact hvEq
    have hIso_w :
        hIso ⟨w0, hu hw0⟩ = ⟨w.1, hu' w.2⟩ := by
      apply Subtype.ext
      exact hwEq
    have hcastv :
        (inducedOn G' s').degree ⟨v.1, hu' v.2⟩ =
          (inducedOn G s).degree ⟨v0, hu hv0⟩ := by
      have hcastv' := SimpleGraph.Iso.degree_eq hIso ⟨v0, hu hv0⟩
      rw [hIso_v] at hcastv'
      exact hcastv'
    have hcastw :
        (inducedOn G' s').degree ⟨w.1, hu' w.2⟩ =
          (inducedOn G s).degree ⟨w0, hu hw0⟩ := by
      have hcastw' := SimpleGraph.Iso.degree_eq hIso ⟨w0, hu hw0⟩
      rw [hIso_w] at hcastw'
      exact hcastw'
    rw [hcastv, hcastw]
    exact hdeg ⟨v0, hv0⟩ ⟨w0, hw0⟩
  have hlen' : blocks'.length ≤ r := by
    simpa [blocks', length_mapControlBlocks] using hlen
  refine ⟨u', s', ?_, hu', blocks', ?_⟩
  · simpa [u'] using hku
  · refine ⟨hlen', ?_⟩
    refine ⟨nonemptyControlBlockUnion_mapControlBlocks e.toEmbedding hnonempty, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [s', blocks'] using controlBlocksSeparated_mapControlBlocks e.toEmbedding hsep
    · refine ⟨?_, ?_⟩
      · intro v w
        exact hdeg' v w
      simpa [u', blocks'] using
        (hasConstantModExternalBlockDegrees_mapControlBlocks (G := G) (G' := G') e hext)

lemma hasFixedModulusControlBlockModularHostWitnessOfCard_of_embedding
    {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ↪g G') {k q : ℕ}
    (hhost : HasFixedModulusControlBlockModularHostWitnessOfCard G k q) :
    HasFixedModulusControlBlockModularHostWitnessOfCard G' k q := by
  rcases hhost with ⟨u, s, hku, hu, blocks, hnonempty, hsep, hdeg, hext⟩
  exact
    hasFixedModulusControlBlockModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
      G'
      (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_embedding
        e
        ⟨u, s, hku, hu, blocks, le_rfl, hnonempty, hsep, hdeg, hext⟩)

lemma hasFixedModulusControlBlockModularHostWitnessOfCard_mono
    (G : SimpleGraph V) {k ℓ q : ℕ} (hkℓ : k ≤ ℓ)
    (hhost : HasFixedModulusControlBlockModularHostWitnessOfCard G ℓ q) :
    HasFixedModulusControlBlockModularHostWitnessOfCard G k q := by
  rcases hhost with ⟨u, s, hℓ, hu, blocks, hnonempty, hsep, hdeg, hext⟩
  exact ⟨u, s, le_trans hkℓ hℓ, hu, blocks, hnonempty, hsep, hdeg, hext⟩

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_mono
    (G : SimpleGraph V) {k ℓ q r : ℕ} (hkℓ : k ≤ ℓ)
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ℓ q r) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q r := by
  rcases hhost with ⟨u, s, hℓ, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  exact ⟨u, s, le_trans hkℓ hℓ, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_le
    (G : SimpleGraph V) {k q r r' : ℕ} (hrr' : r ≤ r')
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q r) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q r' := by
  rcases hhost with ⟨u, s, hk, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  exact ⟨u, s, hk, hu, blocks, le_trans hlen hrr', hnonempty, hsep, hdeg, hext⟩

lemma hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusSingleControlModularHostWitnessOfCard
    (G : SimpleGraph V) {k q : ℕ}
    (hhost : HasFixedModulusSingleControlModularHostWitnessOfCard G k q) :
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q 1 := by
  classical
  rcases hhost with ⟨u, s, t, hku, hu, ht, hst, hdeg, e, hext⟩
  refine ⟨u, s, hku, hu, [(t, e)], by simp, ?_, ?_, hdeg, ?_⟩
  · unfold NonemptyControlBlockUnion
    simpa [controlBlockUnion] using ht
  · refine ⟨hst, ?_, trivial⟩
    simp [controlBlockUnion]
  · simpa [HasConstantModExternalBlockDegrees] using And.intro hext True.intro

lemma hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_one
    (G : SimpleGraph V) {k q : ℕ}
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q 1) :
    HasFixedModulusSingleControlModularHostWitnessOfCard G k q := by
  classical
  rcases hhost with ⟨u, s, hku, hu, blocks, hlen, hnonempty, hsep, hdeg, hext⟩
  cases blocks with
  | nil =>
      exfalso
      unfold NonemptyControlBlockUnion at hnonempty
      simp [controlBlockUnion] at hnonempty
  | cons b bs =>
      cases bs with
      | nil =>
          rcases b with ⟨t, e⟩
          refine ⟨u, s, t, hku, hu, ?_, ?_, hdeg, e, ?_⟩
          · unfold NonemptyControlBlockUnion at hnonempty
            simpa [controlBlockUnion] using hnonempty
          · rcases hsep with ⟨hst, _htail, _⟩
            exact hst
          · rcases hext with ⟨hextHead, _⟩
            exact hextHead
      | cons b' bs' =>
          have hlen' : bs'.length + 2 ≤ 1 := by simpa using hlen
          omega

theorem hasFixedModulusSingleControlModularHostWitnessOfCard_iff_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_one
    (G : SimpleGraph V) {k q : ℕ} :
    HasFixedModulusSingleControlModularHostWitnessOfCard G k q ↔
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G k q 1 := by
  constructor
  · exact
      hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusSingleControlModularHostWitnessOfCard
        G
  · exact
      hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_one
        G

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

lemma inducesModEqDegree_of_inducesRegularOfDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} {d q : ℕ}
    (hreg : InducesRegularOfDegree G s d) :
    InducesModEqDegree G s q := by
  classical
  unfold InducesModEqDegree
  rw [InducesRegularOfDegree] at hreg
  intro v w
  simpa [hreg v, hreg w] using (Nat.ModEq.refl d : d ≡ d [MOD q])

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

lemma exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Finset V} {q : ℕ}
    (htq : t.card < q)
    (hext :
      ∀ v w : ↑(s : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    ∃ e : ℕ, ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨v0, hv0⟩ := hs
    refine ⟨(G.neighborFinset v0 ∩ t).card, ?_⟩
    intro v
    have hv_lt : (G.neighborFinset v ∩ t).card < q := by
      exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
    have h0_lt : (G.neighborFinset v0 ∩ t).card < q := by
      exact lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_right)) htq
    have hmod :
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset v0 ∩ t).card [MOD q] := by
      exact hext v ⟨v0, hv0⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hv_lt, Nat.mod_eq_of_lt h0_lt] at hmod
    exact hmod
  · refine ⟨0, ?_⟩
    have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    intro v
    exact False.elim (by simpa using v.2)

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
  rcases
      exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
        (G := G) (s := s) (t := t) htq hext with
    ⟨e, hext_exact⟩
  refine hasBoundedSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
    (G := G) (hks := hks) (ht := ht) (htr := htr) (hst := hst) (D := d + e) (e := e) ?_
    hext_exact
  intro v
  calc
    (inducedOn G (s ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G s).degree v + (G.neighborFinset v ∩ t).card := by
          exact degree_union_eq_degree_add_external (G := G) (s := s) (t := t) hst v
    _ = d + e := by simp [hd v, hext_exact v]

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
  rcases
      exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
        (G := G) (s := u) (t := t) htq hctrl with
    ⟨e, hext⟩
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
      (G := G) hku hu ht htr hst hq hdeg hdrop hext

lemma hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {q e : ℕ} (hq : u.card ≤ q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
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
  have huMod : InducesModEqDegree G u q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' hdrop
  rcases inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hq huMod with ⟨d, hd⟩
  rw [InducesRegularOfDegree] at hd
  refine
    hasSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
      (G := G) (hks := hku) (ht := ht) (hst := huT) (D := d + e) (e := e) ?_ hext
  intro v
  have hvd : (inducedOn G u).degree v = d := by
    convert hd v
  calc
    (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G u).degree v + (G.neighborFinset v ∩ t).card := by
          exact degree_union_eq_degree_add_external (G := G) (s := u) (t := t) huT v
    _ = d + e := by rw [hvd, hext v]

lemma hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {q e : ℕ} (hq : u.card ≤ q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
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
  have huMod : InducesModEqDegree G u q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' hdrop
  rcases inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hq huMod with ⟨d, hd⟩
  rw [InducesRegularOfDegree] at hd
  refine
    hasBoundedSingleControlExactWitnessOfCard_of_constant_unionDegree_and_externalDegree
      (G := G) (hks := hku) (ht := ht) (htr := htr) (hst := huT) (D := d + e) (e := e) ?_ hext
  intro v
  have hvd : (inducedOn G u).degree v = d := by
    convert hd v
  calc
    (inducedOn G (u ∪ t)).degree ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ =
        (inducedOn G u).degree v + (G.neighborFinset v ∩ t).card := by
          exact degree_union_eq_degree_add_external (G := G) (s := u) (t := t) huT v
    _ = d + e := by rw [hvd, hext v]

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_pow_two_and_dyadicRowDivisibilityChain_of_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r j e : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hcard : u.card = 2 ^ j)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD 2 ^ j])
    {row : ↑(u : Set V) → ℕ}
    (hrow :
      ∀ v : ↑(u : Set V),
        row v = (G.neighborFinset v.1 ∩ (s \ u)).card)
    (hchain : HasDyadicRowDivisibilityChain j row)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  have hq : u.card ≤ 2 ^ j := by
    simpa [hcard]
  have hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v.1 ∩ (s \ u)).card ≡
          (G.neighborFinset w.1 ∩ (s \ u)).card [MOD 2 ^ j] := by
    intro v w
    simpa [hrow v, hrow w] using modEq_of_hasDyadicRowDivisibilityChain hchain v w
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) hku hu ht htr hst hq hhost hdrop hext

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_pow_two_and_dyadicPairingTree_of_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r j e : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    (hcard : u.card = 2 ^ j)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD 2 ^ j])
    {cols : List (BinaryColumn ↑(u : Set V))}
    (hrow :
      ∀ v : ↑(u : Set V),
        binaryColumnRowSum cols v = (G.neighborFinset v.1 ∩ (s \ u)).card)
    (htree : HasDyadicPairingTree j cols)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  have hchain :
      HasDyadicRowDivisibilityChain j (binaryColumnRowSum cols) :=
    hasDyadicRowDivisibilityChain_binaryColumnRowSum_of_hasDyadicPairingTree htree
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_pow_two_and_dyadicRowDivisibilityChain_of_modEq_hostDegree_and_externalDegree
      (G := G) (u := u) (s := s) (t := t) (k := k) (r := r) hku hu ht htr hst hcard hhost
      (row := binaryColumnRowSum cols) hrow hchain hext

lemma hasSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q) (htq : t.card < q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  rcases
      exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
        (G := G) (s := u) (t := t) htq hctrl with
    ⟨e, hext⟩
  exact
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) hku hu ht hst hq hhost hdrop hext

lemma hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q) (htq : t.card < q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  rcases
      exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
        (G := G) (s := u) (t := t) htq hctrl with
    ⟨e, hext⟩
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) hku hu ht htr hst hq hhost hdrop hext

lemma
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_control_card_lt_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} {u s t : Finset V}
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card = r) (hst : Disjoint s t)
    (htq : t.card < q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hctrl :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ t).card ≡ (G.neighborFinset w ∩ t).card [MOD q]) :
    HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases
      exists_constant_externalDegree_of_card_lt_modulus_of_modEq_externalDegree
        (G := G) (s := u) (t := t) htq hctrl with
    ⟨e, hext⟩
  let hres :
      ∃ u' s' t' : Finset V,
        u'.card = k ∧ ∃ hu' : u' ⊆ s',
          0 < t'.card ∧
          t'.card = r ∧
          Disjoint s' t' ∧
          (∀ v w : ↑(u' : Set V),
            (inducedOn G s').degree ⟨v.1, hu' v.2⟩ ≡
              (inducedOn G s').degree ⟨w.1, hu' w.2⟩ [MOD q]) ∧
          (∀ v w : ↑(u' : Set V),
            (G.neighborFinset v ∩ (s' \ u')).card ≡
              (G.neighborFinset w ∩ (s' \ u')).card [MOD q]) ∧
          ∃ e' : ℕ, ∀ v : ↑(u' : Set V), (G.neighborFinset v ∩ t').card = e' :=
      ⟨u, s, t, hku, hu, ht, htr, hst, hhost, hdrop, e, hext⟩
  simpa [HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard] using hres

lemma
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_lt_of_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hrq : r < q)
    (hhost :
      HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard G k q r) :
    HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, hdrop, e, hext⟩
  have htq : t.card < q := by
    simpa [htr] using hrq
  exact
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_control_card_lt_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (k := k) (q := q) (r := r) (u := u) (s := s) (t := t)
      (hku := hku) (hu := hu) (ht := ht) (htr := htr) (hst := hst) (htq := htq)
      (hhost := hdeg) (hdrop := hdrop) (hctrl := by
        intro v w
        exact (hext v).trans (hext w).symm)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_lt_and_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hkq : k ≤ q) (hrq : r < q)
    (hhost :
      HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases
      hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_lt_of_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
        (G := G) hrq hhost with
    ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, hdrop, e, hext⟩
  have hku' : k ≤ u.card := by simpa [hku]
  have huq : u.card ≤ q := by simpa [hku] using hkq
  have htr' : t.card ≤ r := by simpa [htr]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (k := k) (r := r) (u := u) (s := s) (t := t) (q := q) (e := e)
      (hku := hku') (hu := hu) (ht := ht) (htr := htr') (hst := hst) (hq := huq)
      (hhost := hdeg) (hdrop := hdrop) (hext := hext)

/--
If an exact-card fixed-modulus single-control host witness already occupies all available vertices
outside its control set, then there is no dropped part `s \ u`: the host set must equal the bucket
`u`, so the modular host data collapse directly to a bounded exact witness.

Concretely, this happens whenever the ambient graph has at most `k + r` vertices, where `k = |u|`
and `r = |t|`.
-/
lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_add_of_lt_and_hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hkq : k ≤ q) (hV : Fintype.card V ≤ k + r) (hrq : r < q)
    (hhost : HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, e, hext⟩
  have hsum : s.card + t.card ≤ Fintype.card V := by
    have hunion :
        (s ∪ t).card ≤ (Finset.univ : Finset V).card := by
      exact Finset.card_le_card (by
        intro x hx
        simp)
    rw [Finset.card_union_of_disjoint hst] at hunion
    simpa using hunion
  have hsCard : s.card ≤ k := by
    omega
  have husEq : u = s := by
    exact Finset.eq_of_subset_of_card_le hu (by simpa [hku] using hsCard)
  subst s
  have htr' : t.card ≤ r := by
    simpa [htr]
  have huq : u.card ≤ q := by
    simpa [hku] using hkq
  have htq : t.card < q := by
    simpa [htr] using hrq
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (k := k) (r := r) (u := u) (s := u) (t := t)
      (hku := by simpa [hku])
      (hu := subset_rfl)
      (ht := ht) (htr := htr') (hst := hst) (hq := huq) (htq := htq)
      (hhost := by
        intro v w
        convert hdeg v w using 1 <;> rfl)
      (hdrop := by
        intro v w
        simpa using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD q]))
      (hctrl := by
        intro v w
        simpa using (hext v).trans (hext w).symm)

/--
Small-ambient collapse for the live refinement-data package: when `|V| ≤ 2q - 1`, a refinement
datum at bucket size `q` already leaves no room for a dropped part, so it yields a bounded exact
single-control witness of size `q`.
-/
lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_two_mul_sub_one_of_hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {q r : ℕ}
    (hq : 1 < q) (hV : Fintype.card V ≤ 2 * q - 1)
    (href : HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard G q q r) :
    HasBoundedSingleControlExactWitnessOfCard G q (q - 1) := by
  have hrq : q - 1 < q := by
    omega
  have hV' : Fintype.card V ≤ q + (q - 1) := by
    omega
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_add_of_lt_and_hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
      (G := G) (k := q) (q := q) (r := q - 1) le_rfl hV' hrq
      (hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
        (G := G) hq href)

/--
If the host degrees on `u` are constant modulo `q` inside `G[s]`, and the induced degrees on the
bucket `u` are themselves constant modulo `q`, then the dropped-part degrees into `s \ u` are
constant modulo `q` on `u`.
-/
lemma modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {u s : Finset V} (hu : u ⊆ s) {q : ℕ}
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hmod : InducesModEqDegree G u q) :
    ∀ v w : ↑(u : Set V),
      (G.neighborFinset v ∩ (s \ u)).card ≡
        (G.neighborFinset w ∩ (s \ u)).card [MOD q] := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
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
  exact
    modEq_externalDegree_of_modEq_unionDegree_and_inducesModEqDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' hmod

lemma inducesModEqDegree_of_modEq_hostDegree_and_dropDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {u s : Finset V} (hu : u ⊆ s) {q : ℕ}
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q]) :
    InducesModEqDegree G u q := by
  have huDrop : Disjoint u (s \ u) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxU
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
  exact
    inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) (s := u) (t := s \ u) huDrop hhost' hdrop

lemma exists_inducesRegularOfDegree_iff_modEq_dropDegree_of_card_le_modulus_and_modEq_hostDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {u s : Finset V} (hu : u ⊆ s) {q : ℕ}
    (hq : u.card ≤ q)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q]) :
    (∃ d : ℕ, InducesRegularOfDegree G u d) ↔
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q] := by
  constructor
  · rintro ⟨d, hreg⟩
    exact
      modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree
        (G := G) hu hhost
        (inducesModEqDegree_of_inducesRegularOfDegree (G := G) (q := q) hreg)
  · intro hdrop
    exact
      inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hq
        (inducesModEqDegree_of_modEq_hostDegree_and_dropDegree (G := G) hu hhost hdrop)

lemma
    hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d e : ℕ} {u s t : Finset V}
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card = r) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have hmod : InducesModEqDegree G u q :=
    inducesModEqDegree_of_inducesRegularOfDegree (G := G) (q := q) hreg
  refine ⟨u, s, t, hku, hu, ht, htr, hst, hhost, ?_, e, ?_⟩
  · exact modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree (G := G) hu hhost hmod
  · intro v
    simpa [hext v] using (Nat.ModEq.refl e : e ≡ e [MOD q])

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_lt_and_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d e : ℕ} {u s t : Finset V}
    (hkq : k ≤ q) (hrq : r < q)
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card = r) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_lt_and_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
      (G := G) hkq hrq
      (hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
        (G := G) hku hu ht htr hst hhost hreg hext)

lemma
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d e : ℕ} {u s t : Finset V}
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card = r) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨u, s, t, hku, hu, ht, htr, hst, hhost, ?_, e, hext⟩
  exact
    modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree
      (G := G) hu hhost
      (inducesModEqDegree_of_inducesRegularOfDegree (G := G) (q := q) hreg)

lemma hasBoundedSingleControlExactWitnessOfCard_of_lt_of_modEq_hostDegree_and_modEq_unionDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s t : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card ≤ r) (hst : Disjoint s t)
    {q : ℕ} (hq : u.card ≤ q) (hkr : r < k)
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
  have huMod : InducesModEqDegree G u q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalDegree
      (G := G) huT hsmall hctrl
  have hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q] := by
    exact modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree (G := G) hu hhost huMod
  have hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ t))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalDegree
        (G := G) (s := u) (t := s \ u) (u := t) huDrop hdropT hsmall hdrop
  have htq : t.card < q := by
    exact lt_of_le_of_lt htr (lt_of_lt_of_le hkr (le_trans hku hq))
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_control_card_lt_modulus_of_modEq_extendedUnionDegree_and_dropDegree_and_externalDegree
      (G := G) (u := u) (s := s) (t := t) hku hu ht htr hst hq htq hbig hdrop hctrl

lemma
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q : ℕ} (hq : k ≤ q)
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k q) :
    HasSingleControlExactWitnessOfCard G k := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨u, s, t, hku, hu, ht, hst, hdeg, hdrop, e, hext⟩
  have hcard : k ≤ u.card := by
    simpa [hku]
  have huq : u.card ≤ q := by
    simpa [hku] using hq
  exact
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (u := u) (s := s) (t := t) hcard hu ht hst huq hdeg hdrop hext

lemma hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k k) :
    HasSingleControlExactWitnessOfCard G k := by
  exact
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G) (q := k) le_rfl hhost

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hq : k ≤ q)
    (hhost :
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨u, s, t, hku, hu, ht, htr, hst, hdeg, hdrop, e, hext⟩
  have hcard : k ≤ u.card := by
    simpa [hku]
  have huq : u.card ≤ q := by
    simpa [hku] using hq
  have htr' : t.card ≤ r := by
    simpa [htr]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (u := u) (s := s) (t := t) hcard hu ht htr' hst huq hdeg hdrop hext

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G k k r) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
      (G := G) (q := k) le_rfl hhost

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d e : ℕ} {u s t : Finset V}
    (hkq : k ≤ q)
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (htr : t.card = r) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasBoundedSingleControlExactWitnessOfCard G k r := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
      (G := G) hkq
      (hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
        (G := G) hku hu ht htr hst hhost hreg hext)

lemma
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q d e : ℕ} {u s t : Finset V}
    (hkq : k ≤ q)
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  exact
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G) hkq
      (hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
        (G := G)
        (hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
          (G := G) (r := t.card) hku hu ht rfl hst hhost hreg hext))

lemma
    hasSingleControlExactWitnessOfCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k d e : ℕ} {u s t : Finset V}
    (hku : u.card = k) (hu : u ⊆ s) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD k])
    (hreg : InducesRegularOfDegree G u d)
    (hext : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e) :
    HasSingleControlExactWitnessOfCard G k := by
  exact
    hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
      (G := G) (q := k) le_rfl hku hu ht hst hhost hreg hext

lemma
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q : ℕ} (hq : k ≤ q)
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k q) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
        (G := G) hq hhost)

lemma hasRegularInducedSubgraphOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G k k) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G) (q := k) le_rfl hhost

/--
Named graph-level form of the surviving host frontier: every `q^2`-vertex induced subgraph whose
degrees are constant modulo `q` contains a regular induced subgraph on `q` vertices.
-/
def HasModulusSquareRegularSelection (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ ⦃s : Finset V⦄, s.card = q * q → InducesModEqDegree G s q →
    ∃ u : Finset V, u ⊆ s ∧ u.card = q ∧ ∃ d : ℕ, InducesRegularOfDegree G u d

/--
Host-local form of Corollary 10.2: whenever a completed host set `s` of size `q^2` carries one
disjoint control set `t` with exact external degree on all of `s`, some `q`-subset of `s` is
already regular.
-/
def HasCompletedHostRegularSelection (G : SimpleGraph V) (q : ℕ) : Prop := by
  classical
  exact
    ∀ ⦃s t : Finset V⦄, s.card = q * q → 0 < t.card → Disjoint s t →
      InducesModEqDegree G s q →
      (∃ e : ℕ, ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e) →
        ∃ u : Finset V, u ⊆ s ∧ u.card = q ∧ ∃ d : ℕ, InducesRegularOfDegree G u d

lemma hasCompletedHostRegularSelection_of_hasModulusSquareRegularSelection
    (G : SimpleGraph V) {q : ℕ}
    (hselect : HasModulusSquareRegularSelection G q) :
    HasCompletedHostRegularSelection G q := by
  intro s t hsq _ht _hst hhost _hext
  exact hselect hsq hhost

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_regularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect :
      ∀ ⦃s' : Finset V⦄, s'.card = q * q → InducesModEqDegree G s' q →
        ∃ u : Finset V, u ⊆ s' ∧ u.card = q ∧ ∃ d : ℕ, InducesRegularOfDegree G u d) :
    HasBoundedSingleControlExactWitnessOfCard G q t.card := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hselect hsq hhost with ⟨u, hu, huq, d, hreg⟩
  have hhostU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    exact hhost ⟨v.1, hu v.2⟩ ⟨w.1, hu w.2⟩
  have hextU : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext ⟨v.1, hu v.2⟩
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
      (G := G) (k := q) (q := q) (r := t.card) le_rfl huq hu ht rfl hst hhostU hreg hextU

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasBoundedSingleControlExactWitnessOfCard G q t.card := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_regularSelection
      (G := G) hsq ht hst hhost hext hselect

lemma
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_regularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect :
      ∀ ⦃s' : Finset V⦄, s'.card = q * q → InducesModEqDegree G s' q →
        ∃ u : Finset V, u ⊆ s' ∧ u.card = q ∧ ∃ d : ℕ, InducesRegularOfDegree G u d) :
    HasSingleControlExactWitnessOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hselect hsq hhost with ⟨u, hu, huq, d, hreg⟩
  have hhostU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    exact hhost ⟨v.1, hu v.2⟩ ⟨w.1, hu w.2⟩
  have hextU : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext ⟨v.1, hu v.2⟩
  have hres :
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G q q t.card := by
    exact
      hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
        (G := G) (u := u) (s := s) (t := t) huq hu ht rfl hst hhostU hreg hextU
  exact
    hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G)
      (hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
        (G := G) hres)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasCompletedHostRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect : HasCompletedHostRegularSelection G q) :
    HasBoundedSingleControlExactWitnessOfCard G q t.card := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hselect hsq ht hst hhost ⟨e, hext⟩ with ⟨u, hu, huq, d, hreg⟩
  have hhostU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    exact hhost ⟨v.1, hu v.2⟩ ⟨w.1, hu w.2⟩
  have hextU : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext ⟨v.1, hu v.2⟩
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
      (G := G) (k := q) (q := q) (r := t.card) le_rfl huq hu ht rfl hst hhostU hreg hextU

lemma
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasCompletedHostRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect : HasCompletedHostRegularSelection G q) :
    HasSingleControlExactWitnessOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hselect hsq ht hst hhost ⟨e, hext⟩ with ⟨u, hu, huq, d, hreg⟩
  have hhostU :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q] := by
    intro v w
    exact hhost ⟨v.1, hu v.2⟩ ⟨w.1, hu w.2⟩
  have hextU : ∀ v : ↑(u : Set V), (G.neighborFinset v ∩ t).card = e := by
    intro v
    exact hext ⟨v.1, hu v.2⟩
  have hres :
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard G q q t.card := by
    exact
      hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_inducesRegularOfDegree_and_modEq_hostDegree_and_externalDegree
        (G := G) (u := u) (s := s) (t := t) huq hu ht rfl hst hhostU hreg hextU
  exact
    hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G)
      (hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
        (G := G) hres)

lemma
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasSingleControlExactWitnessOfCard G q := by
  exact
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_regularSelection
      (G := G) hsq ht hst hhost hext hselect

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard G q r)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasBoundedSingleControlExactWitnessOfCard G q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨s, t, hsq, ht, htr, hst, hdeg, e, hext⟩
  simpa [htr] using
    (hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
      (G := G) (s := s) (t := t) hsq ht hst hdeg hext hselect)

lemma
    hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard G q)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasSingleControlExactWitnessOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨s, t, hsq, ht, hst, hdeg, e, hext⟩
  exact
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
      (G := G) (s := s) (t := t) hsq ht hst hdeg hext hselect

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard_and_hasCompletedHostRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q r : ℕ}
    (hhost :
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard G q r)
    (hselect : HasCompletedHostRegularSelection G q) :
    HasBoundedSingleControlExactWitnessOfCard G q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨s, t, hsq, ht, htr, hst, hdeg, e, hext⟩
  simpa [htr] using
    (hasBoundedSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasCompletedHostRegularSelection
      (G := G) (s := s) (t := t) hsq ht hst hdeg hext hselect)

lemma
    hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasCompletedHostRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard G q)
    (hselect : HasCompletedHostRegularSelection G q) :
    HasSingleControlExactWitnessOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hhost with ⟨s, t, hsq, ht, hst, hdeg, e, hext⟩
  exact
    hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasCompletedHostRegularSelection
      (G := G) (s := s) (t := t) hsq ht hst hdeg hext hselect

lemma
    hasRegularInducedSubgraphOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasCompletedHostRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard G q)
    (hselect : HasCompletedHostRegularSelection G q) :
    HasRegularInducedSubgraphOfCard G q := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasCompletedHostRegularSelection
        (G := G) hhost hselect)

lemma
    hasRegularInducedSubgraphOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q e : ℕ} {s t : Finset V}
    (hsq : s.card = q * q) (ht : 0 < t.card) (hst : Disjoint s t)
    (hhost : InducesModEqDegree G s q)
    (hext : ∀ v : ↑(s : Set V), (G.neighborFinset v ∩ t).card = e)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasRegularInducedSubgraphOfCard G q := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_card_eq_sq_of_inducesModEqDegree_and_externalDegree_and_hasModulusSquareRegularSelection
        (G := G) hsq ht hst hhost hext hselect)

lemma
    hasRegularInducedSubgraphOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasModulusSquareRegularSelection
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hhost : HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard G q)
    (hselect : HasModulusSquareRegularSelection G q) :
    HasRegularInducedSubgraphOfCard G q := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G
      (hasSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCard_and_hasModulusSquareRegularSelection
        (G := G) hhost hselect)

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

private lemma modEq_dropDegree_and_extendedUnionDegree_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {u s : Finset V} (hu : u ⊆ s)
    {q : ℕ} {blocks : List (Finset V × ℕ)} (hsep : ControlBlocksSeparated s blocks)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    (∀ v w : ↑(u : Set V),
      (G.neighborFinset v ∩ (s \ u)).card ≡
        (G.neighborFinset w ∩ (s \ u)).card [MOD q]) ∧
    (∀ v w : ↑(u : Set V),
      (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
          ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
          ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q]) := by
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
  have hsepU : ControlBlocksSeparated u blocks := controlBlocksSeparated_mono hu hsep
  have huMod : InducesModEqDegree G u q := by
    exact
      inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
        (G := G) (s := u) (q := q) (blocks := blocks) hsepU hsmall hext
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
    exact
      modEq_externalDegree_of_modEq_unionDegree_and_inducesModEqDegree
        (G := G) (s := u) (t := s \ u) huDrop hhost' huMod
  have hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    have hbigRaw :
        ∀ v w : ↑(u : Set V),
          (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
              ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
            (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
              ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
      exact
        modEq_extendedUnionDegree_of_modEq_unionDegree_and_externalBlockDegrees
          (G := G) (s := u) (tail := s \ u) (q := q) (blocks := blocks) hsepU hdropBlocks.symm
          hhost' hext
    have hAmbientEq :
        u ∪ (controlBlockUnion blocks ∪ (s \ u)) =
          u ∪ ((s \ u) ∪ controlBlockUnion blocks) := by
      simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
    intro v w
    have hcastv :
        (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (controlBlockUnion blocks ∪ (s \ u)))
          (t := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl v.2)))
    have hcastw :
        (inducedOn G (u ∪ (controlBlockUnion blocks ∪ (s \ u)))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ (controlBlockUnion blocks ∪ (s \ u)))
          (t := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl w.2)))
    simpa [hcastv, hcastw] using hbigRaw v w
  exact ⟨hdrop, hbig⟩

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases href with ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hsmall, hctrl, hhost, hext⟩
  rcases
      modEq_dropDegree_and_extendedUnionDegree_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
        (G := G) (u := w) (s := s) hw (blocks := ((t, e) :: blocks)) hsep hhost hsmall hext with
    ⟨hdrop, hbigRaw⟩
  have hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q] := by
    intro v w'
    have hAmbientEq :
        w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)) =
          s ∪ controlBlockUnion ((t, e) :: blocks) := by
      ext x
      by_cases hxw : x ∈ w
      · simp [hxw, hw hxw, or_assoc, or_left_comm, or_comm]
      · simp [hxw, or_assoc, or_left_comm, or_comm]
    have hcastv :
        (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))
          (t := s ∪ controlBlockUnion ((t, e) :: blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl (hw v.2))))
    have hcastw :
        (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))
          (t := s ∪ controlBlockUnion ((t, e) :: blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl w'.2))
          (ht := Finset.mem_union.mpr (Or.inl (hw w'.2))))
    simpa [hcastv, hcastw] using hbigRaw v w'
  exact ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hbig, hdrop, hctrl, hhost, hext⟩

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases href with ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hbig, hdrop, hctrl, hhost, hext⟩
  have hwDrop : Disjoint w (s \ w) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxW
  have hdropBlocks : Disjoint (s \ w) (controlBlockUnion ((t, e) :: blocks)) := by
    have hsBlocks : Disjoint s (controlBlockUnion ((t, e) :: blocks)) :=
      disjoint_controlBlockUnion_of_controlBlocksSeparated hsep
    refine Finset.disjoint_left.mpr ?_
    intro x hxDrop hxBlock
    exact (Finset.disjoint_left.mp hsBlocks) (Finset.mem_sdiff.mp hxDrop).1 hxBlock
  have hbigAmbient :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ [MOD q] := by
    intro v w'
    have hAmbientEq :
        w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)) =
          s ∪ controlBlockUnion ((t, e) :: blocks) := by
      rw [← Finset.union_assoc, Finset.union_comm w (s \ w), Finset.sdiff_union_of_subset hw]
    have hcastv :
        (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))
          (t := s ∪ controlBlockUnion ((t, e) :: blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl (hw v.2))))
    have hcastw :
        (inducedOn G (w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ ((s \ w) ∪ controlBlockUnion ((t, e) :: blocks)))
          (t := s ∪ controlBlockUnion ((t, e) :: blocks))
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl w'.2))
          (ht := Finset.mem_union.mpr (Or.inl (hw w'.2))))
    simpa [hcastv, hcastw] using hbig v w'
  have hsmall :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (w ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (w ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w'.1, Finset.mem_union.mpr (Or.inl w'.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
        (G := G) (s := w) (t := s \ w) (u := controlBlockUnion ((t, e) :: blocks))
        hwDrop hdropBlocks hbigAmbient hdrop
  exact ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hsmall, hctrl, hhost, hext⟩

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_inducesModEqDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s) {blocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hmod : InducesModEqDegree G w q)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hbig, ?_, hctrl, hhost, hext⟩
  exact modEq_dropDegree_of_modEq_hostDegree_and_inducesModEqDegree (G := G) hw hhost hmod

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_inducesRegularOfDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s) {blocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hreg : InducesRegularOfDegree G w d)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r := by
  rw [InducesRegularOfDegree] at hreg
  apply
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_inducesModEqDegree
      (G := G) hwk hw htcard hlen hsep hbig ?_ hctrl hhost hext
  intro v w'
  simpa [hreg v, hreg w'] using (Nat.ModEq.refl d : d ≡ d [MOD q])

lemma hasBoundedControlBlockModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks) (hsep : ControlBlocksSeparated s blocks)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
  rcases
      modEq_dropDegree_and_extendedUnionDegree_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
        (G := G) (u := u) (s := s) hu (q := q) (blocks := blocks) hsep hhost hsmall hext with
    ⟨hdrop, hbig⟩
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  exact ⟨u, s, hku, hu, q, hq, blocks, hlen, hnonempty, hsep, hbig, hdrop, hext⟩

lemma
    hasBoundedControlBlockModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks) (hsep : ControlBlocksSeparated s blocks)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    HasBoundedControlBlockModularBucketingWitnessOfCard G k r := by
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
  have hbigAmbient :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    intro v w
    have hAmbientEq :
        u ∪ ((s \ u) ∪ controlBlockUnion blocks) = s ∪ controlBlockUnion blocks := by
      rw [← Finset.union_assoc, Finset.union_comm u (s \ u), Finset.sdiff_union_of_subset hu]
    have hcastv :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl v.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu v.2))))
    have hcastw :
        (inducedOn G (u ∪ ((s \ u) ∪ controlBlockUnion blocks))).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ =
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := u ∪ ((s \ u) ∪ controlBlockUnion blocks))
          (t := s ∪ controlBlockUnion blocks)
          (h := hAmbientEq)
          (hs := Finset.mem_union.mpr (Or.inl w.2))
          (ht := Finset.mem_union.mpr (Or.inl (hu w.2))))
    simpa [hcastv, hcastw] using hbig v w
  have hsmall :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩ ≡
          (inducedOn G (u ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl w.2)⟩ [MOD q] := by
    exact
      modEq_unionDegree_of_modEq_extendedUnionDegree_and_externalDegree
        (G := G) (s := u) (t := s \ u) (u := controlBlockUnion blocks) huDrop hdropBlocks
        hbigAmbient hdrop
  exact
    hasBoundedControlBlockModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_unionDegree_and_externalBlockDegrees
      (G := G) hku hu hq hlen hnonempty hsep hhost hsmall hext

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

lemma
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_modEq_hostDegree_and_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
    (G : SimpleGraph V) [DecidableRel G.Adj] {k r : ℕ} {u s : Finset V}
    (hku : k ≤ u.card) (hu : u ⊆ s) {q : ℕ} (hq : u.card ≤ q)
    {blocks : List (Finset V × ℕ)} (hlen : blocks.length ≤ r)
    (hnonempty : NonemptyControlBlockUnion blocks) (hsep : ControlBlocksSeparated s blocks)
    (hhost :
      ∀ v w : ↑(u : Set V),
        (inducedOn G s).degree ⟨v.1, hu v.2⟩ ≡
          (inducedOn G s).degree ⟨w.1, hu w.2⟩ [MOD q])
    (hbig :
      ∀ v w : ↑(u : Set V),
        (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨v.1, Finset.mem_union.mpr (Or.inl (hu v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion blocks)).degree
            ⟨w.1, Finset.mem_union.mpr (Or.inl (hu w.2))⟩ [MOD q])
    (hdrop :
      ∀ v w : ↑(u : Set V),
        (G.neighborFinset v ∩ (s \ u)).card ≡
          (G.neighborFinset w ∩ (s \ u)).card [MOD q])
    (hext : HasConstantModExternalBlockDegrees G u q blocks) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard G
      (hasBoundedControlBlockModularBucketingWitnessOfCard_of_modEq_hostDegree_and_modEq_extendedUnionDegree_and_dropDegree_and_externalBlockDegrees
        (G := G) hku hu hq hlen hnonempty hsep hhost hbig hdrop hext)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href : HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases href with ⟨w, s, t, hwk, hw, _blocks, e, htcard, _hlen, hsep, _hbig, hdrop, hctrl, hhost, _hext⟩
  rcases hsep with ⟨hst, _htail, _hsepTail⟩
  have hwq : w.card ≤ q := by
    rw [hwk]
    exact hkq
  have htpos : 0 < t.card := by
    rw [htcard]
    exact Nat.sub_pos_of_lt hq
  have htr : t.card ≤ q - 1 := by
    rw [htcard]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_modEq_hostDegree_and_dropDegree_and_externalDegree
      (G := G) (u := w) (s := s) (t := t) (k := k) (r := q - 1)
      (hku := by simpa [hwk]) hw htpos htr hst hwq hhost hdrop hctrl

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesModEqDegree_and_exactCardFixedModulusControlBlockModularHostRefinementData
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s) {blocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hmod : InducesModEqDegree G w q)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_inducesModEqDegree
        (G := G) hwk hw htcard hlen hsep hbig hmod hctrl hhost hext)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesRegularOfDegree_and_exactCardFixedModulusControlBlockModularHostRefinementData
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r d : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s) {blocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hreg : InducesRegularOfDegree G w d)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_inducesModEqDegree_and_exactCardFixedModulusControlBlockModularHostRefinementData
      (G := G) hkq hq hwk hw htcard hlen hsep hbig
      (by
        rw [InducesRegularOfDegree] at hreg
        intro v w'
        simpa [hreg v, hreg w'] using (Nat.ModEq.refl d : d ≡ d [MOD q]))
      hctrl hhost hext

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_internalTailBlocks_and_exactCardFixedModulusControlBlockModularHostRefinementData
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks tailBlocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (htailUnion : controlBlockUnion tailBlocks = s \ w)
    (htailSep : ControlBlocksSeparated w tailBlocks)
    (htailExt : HasConstantModExternalBlockDegrees G w q tailBlocks)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r := by
  have hmod : InducesModEqDegree G w q := by
    exact
      inducesModEqDegree_of_modEq_hostDegree_and_internalTailBlocks
        (G := G) hw hhost htailUnion htailSep htailExt
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_inducesModEqDegree
      (G := G) hwk hw htcard hlen hsep hbig hmod hctrl hhost hext

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_internalTailBlocks_and_exactCardFixedModulusControlBlockModularHostRefinementData
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks tailBlocks : List (Finset V × ℕ)} {e : ℕ}
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (htailUnion : controlBlockUnion tailBlocks = s \ w)
    (htailSep : ControlBlocksSeparated w tailBlocks)
    (htailExt : HasConstantModExternalBlockDegrees G w q tailBlocks)
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks)) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_internalTailBlocks_and_exactCardFixedModulusControlBlockModularHostRefinementData
        (G := G) hwk hw htcard hlen hsep hbig htailUnion htailSep htailExt hctrl hhost hext)

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (htail :
      HasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases htail with
    ⟨w, s, t, hwk, hw, blocks, tailBlocks, e, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
      htailUnion, htailSep, htailExt⟩
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_internalTailBlocks_and_exactCardFixedModulusControlBlockModularHostRefinementData
      (G := G) hwk hw htcard hlen hsep hbig htailUnion htailSep htailExt hctrl hhost hext

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (htail :
      HasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
        (G := G) htail)

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard_of_rowModEq_pow_succ
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (hrow :
      ∀ v w' : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w'.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
    tail, hchain, ?_⟩
  intro v w'
  exact (hchain.tail_modEq_two_iff_row_modEq_pow_succ (v := v) (w := w')).2 (hrow v w')

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard_of_rowModEq_pow_succ_basepoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (w₀ : ↑(w : Set V))
    (hrow :
      ∀ v : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w₀.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard G k q r := by
  refine
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard_of_rowModEq_pow_succ
      (G := G) hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hchain ?_
  intro v w'
  exact (hrow v).trans (hrow w').symm

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_terminalModEq_two
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {row tail : ↑(w : Set V) → ℕ}
    (hrow : ∀ v, row v = (G.neighborFinset v.1 ∩ (s \ w)).card)
    (hchain : HasDyadicRowDivisibilityChainTo j row tail)
    (hterm : ∀ v w' : ↑(w : Set V), tail v ≡ tail w' [MOD 2]) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨w, s, t, hwk, hw, blocks, e, j + 1, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost,
    hext, ?_⟩
  exact
    HasDyadicRowDivisibilityChain.congr
      (hchain.succ_of_terminalModEq_two hterm)
      hrow

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_dyadicTailBetaVanishesAt
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {row tail : ↑(w : Set V) → ℕ}
    (hrow : ∀ v, row v = (G.neighborFinset v.1 ∩ (s \ w)).card)
    (hchain : HasDyadicRowDivisibilityChainTo j row tail)
    (hbeta : DyadicTailBetaVanishesAt j row) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_terminalModEq_two
      (G := G) (w := w) (s := s) (t := t) hwk hw (blocks := blocks) (e := e)
      (j := j) hqpow htcard hlen hsep hbig hctrl hhost hext hrow hchain
      (hbeta tail hchain)

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hbeta :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hbeta with
    ⟨w, s, t, hwk, hw, blocks, e, j, row, tail, hqpow, htcard, hlen, hsep, hbig, hctrl,
      hhost, hext, hrow, hchain, hbetaVanishes⟩
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_dyadicTailBetaVanishesAt
      (G := G) (w := w) (s := s) (t := t) hwk hw (blocks := blocks) (e := e)
      (j := j) hqpow htcard hlen hsep hbig hctrl hhost hext
      (row := row) (tail := tail) hrow hchain hbetaVanishes

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hbeta :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hbeta with
    ⟨w, s, t, hwk, hw, blocks, e, j, row, hqpow, htcard, hlen, hsep, hbig, hctrl,
      hhost, hext, hrow, hbetaUpTo⟩
  refine ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost,
    hext, ?_⟩
  exact
    HasDyadicRowDivisibilityChain.congr
      (hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo hbetaUpTo)
      hrow

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hdiv :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hdiv with
    ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
      hchain⟩
  refine ⟨w, s, t, hwk, hw, blocks, e, j,
    (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card),
    hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext, ?_, ?_⟩
  · intro v
    rfl
  · exact dyadicTailBetaVanishesUpTo_of_hasDyadicRowDivisibilityChain hchain

theorem
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard_iff_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard G k q r ↔
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
        G k q r :=
  ⟨hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
      G,
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      G⟩

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_modEq_two_and_halved
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {row : ↑(w : Set V) → ℕ}
    (hrow : ∀ v, row v = (G.neighborFinset v.1 ∩ (s \ w)).card)
    (hmodTwo : ∀ v w' : ↑(w : Set V), row v ≡ row w' [MOD 2])
    (hhalf : HasDyadicRowDivisibilityChain j (fun v : ↑(w : Set V) => row v / 2)) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨w, s, t, hwk, hw, blocks, e, j + 1, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost,
    hext, ?_⟩
  exact
    HasDyadicRowDivisibilityChain.congr
      (hasDyadicRowDivisibilityChain_succ_of_modEq_two_and_halved hmodTwo hhalf)
      hrow

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hterm :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hterm with
    ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
      tail, hchain, hmodTwo⟩
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_terminalModEq_two
      (G := G) (w := w) (s := s) (t := t) hwk hw (blocks := blocks) (e := e) (j := j)
      hqpow htcard hlen hsep hbig hctrl hhost hext
      (row := fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card)
      (tail := tail) (hrow := by intro v; rfl) hchain hmodTwo

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hpacket :
      HasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hpacket with
    ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
      packets, hrow, hpackets, hhalf⟩
  have hhalfPackets :
      HasDyadicRowDivisibilityChain j
        (fun v : ↑(w : Set V) =>
          binaryColumnRowSum (flattenBinaryPackets packets) v / 2) := by
    exact
      HasDyadicRowDivisibilityChain.congr hhalf
        (fun v => by rw [← hrow v])
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_modEq_two_and_halved
      (G := G) hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hrow
      (modEq_rowSum_two_of_hasBinaryZeroSumPacketPartition hpackets) hhalfPackets

lemma
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ}
    (hpair :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard G k q r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hpair with
    ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext,
      cols, hrow, htree⟩
  refine ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, hbig, hctrl, hhost, hext, ?_⟩
  exact
    HasDyadicRowDivisibilityChain.congr
      (hasDyadicRowDivisibilityChain_binaryColumnRowSum_of_hasDyadicPairingTree htree)
      hrow

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hdiv :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hdiv with
    ⟨w, s, t, hwk, hw, blocks, e, j, hqpow, htcard, hlen, hsep, _hbig, hctrl, hhost, _hext,
      hchain⟩
  have hst : Disjoint s t := by
    rcases hsep with ⟨hst, _htail, _hsepTail⟩
    exact hst
  have htpos : 0 < t.card := by
    rw [htcard]
    exact Nat.sub_pos_of_lt hq
  have htr : t.card ≤ q - 1 := by
    rw [htcard]
  have hwpow : w.card = 2 ^ j := by
    calc
      w.card = k := hwk
      _ = q := hkq
      _ = 2 ^ j := hqpow
  have hhostPow :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD 2 ^ j] := by
    simpa [hqpow] using hhost
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_pow_two_and_dyadicRowDivisibilityChain_of_modEq_hostDegree_and_externalDegree
      (G := G) (u := w) (s := s) (t := t) (k := k) (r := q - 1)
      (hku := by simpa [hwk]) hw htpos htr hst hwpow hhostPow
      (row := fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card)
      (hrow := by intro v; rfl) hchain hctrl

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hbeta :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
        (G := G) hbeta)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hbeta :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
        (G := G) hbeta)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hterm :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
        (G := G) hterm)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (hrow :
      ∀ v w' : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w'.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard_of_rowModEq_pow_succ
        (G := G) hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hchain hrow)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ_basepoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (w₀ : ↑(w : Set V))
    (hrow :
      ∀ v : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w₀.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard_of_rowModEq_pow_succ_basepoint
        (G := G) hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hchain w₀ hrow)

lemma
    hasRegularInducedSubgraphOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (hrow :
      ∀ v w' : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w'.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
      (hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ
        (G := G) hkq hq hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hchain hrow)

lemma
    hasRegularInducedSubgraphOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ_basepoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    {w s t : Finset V} (hwk : w.card = k) (hw : w ⊆ s)
    {blocks : List (Finset V × ℕ)} {e j : ℕ}
    (hqpow : q = 2 ^ (j + 1))
    (htcard : t.card = q - 1) (hlen : blocks.length ≤ r)
    (hsep : ControlBlocksSeparated s ((t, e) :: blocks))
    (hbig :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨v, Finset.mem_union.mpr (Or.inl (hw v.2))⟩ ≡
          (inducedOn G (s ∪ controlBlockUnion ((t, e) :: blocks))).degree
            ⟨w', Finset.mem_union.mpr (Or.inl (hw w'.2))⟩ [MOD q])
    (hctrl : ∀ v : ↑(w : Set V), (G.neighborFinset v.1 ∩ t).card = e)
    (hhost :
      ∀ v w' : ↑(w : Set V),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD q])
    (hext : HasConstantModExternalBlockDegrees G w q ((t, e) :: blocks))
    {tail : ↑(w : Set V) → ℕ}
    (hchain :
      HasDyadicRowDivisibilityChainTo j
        (fun v : ↑(w : Set V) => (G.neighborFinset v.1 ∩ (s \ w)).card) tail)
    (w₀ : ↑(w : Set V))
    (hrow :
      ∀ v : ↑(w : Set V),
        (G.neighborFinset v.1 ∩ (s \ w)).card ≡
          (G.neighborFinset w₀.1 ∩ (s \ w)).card [MOD 2 ^ (j + 1)]) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
      (hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_rowModEq_pow_succ_basepoint
        (G := G) hkq hq hwk hw hqpow htcard hlen hsep hbig hctrl hhost hext hchain w₀ hrow)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hpacket :
      HasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
        (G := G) hpacket)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k = q) (hq : 1 < q)
    (hpair :
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
        (G := G) hpair)

lemma
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href : HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
      (hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
        (G := G) hkq hq href)

lemma
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard G k q r) :
    HasBoundedSingleControlExactWitnessOfCard G k (q - 1) := by
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
        (G := G) href)

lemma
    hasRegularInducedSubgraphOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard G k q r) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
      (hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
        (G := G) hkq hq href)

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
