import RegularInducedSubgraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Universal profiles for the q = 8 quotient CSP

Section 26 of `notes/remaining-gap-obstruction-module.md` replaces the exact
profile set of a regular bag by a **universal profile**:

* `(s, δ) ∈ U(n, ρ)` means that **every** `n`-vertex `ρ`-regular graph contains
  an induced `s`-vertex regular subgraph of degree `δ`.

This file introduces that predicate and proves the two extremal exact families
needed repeatedly later:

* `U(n, 0) = {(s, 0) : s ≤ n}`
* `U(n, n - 1) = {(s, s - 1) : s ≤ n}`
* the complement transfer `(s, δ) ↦ (s, s - 1 - δ)`

 This file now also records the exact `ρ = 2` universal-profile table for
 `3 ≤ n < 8`, which is already sufficient for the current `q = 8` program.
-/

namespace RegularInducedSubgraph

open Finset
open SimpleGraph

section UniversalProfiles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Regularity packaged without exposing local-finiteness instance arguments. -/
def RegularOfDegree (G : SimpleGraph V) (d : ℕ) : Prop := by
  classical
  exact ∀ v : V, G.degree v = d

/-- A *canonical exact witness* for the pair `(s, δ)`.

The extra clause `t.Nonempty ∨ δ = 0` removes the vacuous ambiguity of the empty
induced subgraph, so `(0, 0)` is the only empty witness that contributes to a
universal profile. -/
def HasCanonicalRegularInducedSubgraphOfCardAndDegree
    (G : SimpleGraph V) (s δ : ℕ) : Prop := by
  classical
  exact ∃ t : Finset V, t.card = s ∧ InducesRegularOfDegree G t δ ∧ (t.Nonempty ∨ δ = 0)

/-- The universal profile `U(n, ρ)` of `n`-vertex `ρ`-regular graphs. -/
def UniversalProfile (n ρ : ℕ) : Set (ℕ × ℕ) := by
  classical
  exact {p | ∀ G : SimpleGraph (Fin n), RegularOfDegree G ρ →
    HasCanonicalRegularInducedSubgraphOfCardAndDegree G p.1 p.2}

private lemma zero_regular_isIndepSet_univ {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : RegularOfDegree G 0) :
    G.IsIndepSet (Set.univ : Set (Fin n)) := by
  classical
  intro v _ w _ hne hadj
  have hpos : 0 < G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨w, by simpa [SimpleGraph.mem_neighborFinset] using hadj⟩
  exact (Nat.lt_irrefl 0) <| by simpa [hG v] using hpos

private lemma full_regular_isClique_univ {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : RegularOfDegree G (n - 1)) :
    G.IsClique (Set.univ : Set (Fin n)) := by
  classical
  intro v _ w _ hne
  by_contra hnot
  have hsubset : G.neighborFinset v ⊆ (Finset.univ.erase w) := by
    intro x hx
    have hxne : x ≠ w := by
      intro hxw
      subst hxw
      exact hnot (by simpa [SimpleGraph.mem_neighborFinset] using hx)
    simp [hxne]
  have hssubset : G.neighborFinset v ⊂ Finset.univ.erase w := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨v, ?_, ?_⟩
    · simp [hne]
    · simp [SimpleGraph.mem_neighborFinset]
  have hlt : G.degree v < n - 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    simpa using Finset.card_lt_card hssubset
  exact (Nat.lt_irrefl (n - 1)) <| by simpa [hG v] using hlt

private lemma regular_one_existsUnique_adj {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (v : Fin (2 * m)) :
    ∃! w : Fin (2 * m), G.Adj v w := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp (hG v)

private noncomputable def mate {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (v : Fin (2 * m)) : Fin (2 * m) :=
  (regular_one_existsUnique_adj hG v).choose

private lemma adj_mate {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (v : Fin (2 * m)) :
    G.Adj v (mate hG v) :=
  (regular_one_existsUnique_adj hG v).choose_spec.1

private lemma mate_eq_of_adj {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) {v w : Fin (2 * m)} (hvw : G.Adj v w) :
    mate hG v = w := by
  exact ((regular_one_existsUnique_adj hG v).choose_spec.2 w hvw).symm

private lemma mate_mate {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (v : Fin (2 * m)) :
    mate hG (mate hG v) = v :=
  mate_eq_of_adj (hG := hG) ((adj_mate hG v).symm)

private lemma mate_ne_self {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (v : Fin (2 * m)) :
    mate hG v ≠ v := by
  exact (G.ne_of_adj (adj_mate hG v)).symm

private lemma mate_injective {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) :
    Function.Injective (mate hG) :=
  (Function.Involutive.injective (mate_mate hG))

private noncomputable def mateLeftFinset {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun v => v < mate hG v

private noncomputable def mateLeftRightEquiv {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) :
    {v : Fin (2 * m) // v < mate hG v} ≃ {v : Fin (2 * m) // mate hG v < v} where
  toFun v := ⟨mate hG v, by simpa [mate_mate hG v] using v.property⟩
  invFun v := ⟨mate hG v, by simpa [mate_mate hG v] using v.property⟩
  left_inv v := by
    apply Subtype.ext
    simp [mate_mate hG v]
  right_inv v := by
    apply Subtype.ext
    simp [mate_mate hG v]

private lemma mateLeftFinset_card {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) :
    (mateLeftFinset hG).card = m := by
  classical
  let p : Fin (2 * m) → Prop := fun v => v < mate hG v
  let q : Fin (2 * m) → Prop := fun v => mate hG v < v
  have hpq_disj : Disjoint p q := by
    rw [disjoint_iff_inf_le]
    intro v hv
    exact (lt_asymm hv.1 hv.2).elim
  have hallmem : ∀ v : Fin (2 * m), p v ∨ q v := by
    intro v
    exact lt_or_gt_of_ne (mate_ne_self hG v).symm
  have hall : Fintype.card {v : Fin (2 * m) // p v ∨ q v} = 2 * m := by
    simpa using
      (Fintype.card_of_subtype (s := (Finset.univ : Finset (Fin (2 * m))))
        (p := fun v => p v ∨ q v) (by
          intro v
          simp [hallmem v]))
  have hsum :
      Fintype.card {v : Fin (2 * m) // p v} + Fintype.card {v : Fin (2 * m) // q v} = 2 * m := by
    calc
      Fintype.card {v : Fin (2 * m) // p v} + Fintype.card {v : Fin (2 * m) // q v}
          = Fintype.card {v : Fin (2 * m) // p v ∨ q v} := by
              symm
              exact Fintype.card_subtype_or_disjoint p q hpq_disj
      _ = 2 * m := hall
  have hEq :
      Fintype.card {v : Fin (2 * m) // p v} = Fintype.card {v : Fin (2 * m) // q v} := by
    simpa [p, q] using Fintype.card_congr (mateLeftRightEquiv hG)
  have hcard : Fintype.card {v : Fin (2 * m) // p v} = m := by
    omega
  rw [Fintype.card_subtype p] at hcard
  simpa [mateLeftFinset, p] using hcard

private lemma mateLeftFinset_isIndepSet {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) :
    G.IsIndepSet ((mateLeftFinset hG : Finset (Fin (2 * m))) : Set (Fin (2 * m))) := by
  intro v hv w hw hne hadj
  have hv' : v ∈ mateLeftFinset hG := hv
  have hw' : w ∈ mateLeftFinset hG := hw
  have hvlt : v < mate hG v := (Finset.mem_filter.mp hv').2
  have hwlt : w < mate hG w := (Finset.mem_filter.mp hw').2
  have hmw : mate hG v = w := mate_eq_of_adj hG hadj
  have hmv : mate hG w = v := mate_eq_of_adj hG hadj.symm
  rw [hmw] at hvlt
  rw [hmv] at hwlt
  exact (lt_asymm hvlt hwlt).elim

private noncomputable def pairUnion {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (a : Finset (Fin (2 * m))) : Finset (Fin (2 * m)) := by
  let mateEmb : Fin (2 * m) ↪ Fin (2 * m) :=
    ⟨mate hG, mate_injective hG⟩
  exact a ∪ a.map mateEmb

private lemma mate_mem_pairUnion {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) {a : Finset (Fin (2 * m))} {v : Fin (2 * m)}
    (hv : v ∈ pairUnion hG a) :
    mate hG v ∈ pairUnion hG a := by
  classical
  let mateEmb : Fin (2 * m) ↪ Fin (2 * m) :=
    ⟨mate hG, mate_injective hG⟩
  dsimp [pairUnion] at hv ⊢
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_map.mpr ⟨v, hv, rfl⟩
  · rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact Finset.mem_union.mpr <| Or.inl (by simpa [mate_mate hG w] using hw)

private lemma pairUnion_card {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) {a : Finset (Fin (2 * m))}
    (ha : a ⊆ mateLeftFinset hG) :
    (pairUnion hG a).card = 2 * a.card := by
  classical
  let mateEmb : Fin (2 * m) ↪ Fin (2 * m) :=
    ⟨mate hG, mate_injective hG⟩
  have hdisj : Disjoint a (a.map mateEmb) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvA hvMap
    rcases Finset.mem_map.mp hvMap with ⟨w, hwA, hwv⟩
    have hvLeft : v < mate hG v := by
      exact (Finset.mem_filter.mp (ha hvA)).2
    have hwLeft : w < mate hG w := by
      exact (Finset.mem_filter.mp (ha hwA)).2
    have hwv' : mate hG w = v := by simpa [mateEmb] using hwv
    rw [← hwv', mate_mate hG w] at hvLeft
    exact (lt_asymm hwLeft hvLeft).elim
  dsimp [pairUnion]
  calc
    (a ∪ a.map mateEmb).card = a.card + (a.map mateEmb).card := Finset.card_union_of_disjoint hdisj
    _ = a.card + a.card := by rw [Finset.card_map]
    _ = 2 * a.card := by omega

private lemma inducesRegularOfDegree_pairUnion_one {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) (a : Finset (Fin (2 * m))) :
    InducesRegularOfDegree G (pairUnion hG a) 1 := by
  classical
  rw [InducesRegularOfDegree]
  intro x
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨⟨mate hG x, mate_mem_pairUnion hG x.property⟩, ?_, ?_⟩
  · simpa [inducedOn] using adj_mate hG x
  · intro y hy
    apply Subtype.ext
    exact (mate_eq_of_adj hG (by simpa [inducedOn] using hy)).symm

private lemma isIndepSet_of_inducesRegularOfDegree_zero {m : ℕ}
    {G : SimpleGraph (Fin (2 * m))} {t : Finset (Fin (2 * m))}
    (hreg : InducesRegularOfDegree G t 0) :
    G.IsIndepSet ((t : Finset (Fin (2 * m))) : Set (Fin (2 * m))) := by
  classical
  rw [InducesRegularOfDegree] at hreg
  intro v hv w hw hne hadj
  have hpos : 0 < (inducedOn G t).degree ⟨v, hv⟩ := by
    exact ((inducedOn G t).degree_pos_iff_exists_adj ⟨v, hv⟩).2
      ⟨⟨w, hw⟩, by simpa [inducedOn] using hadj⟩
  exact (Nat.lt_irrefl 0) <| by simpa [hreg ⟨v, hv⟩] using hpos

private lemma indepSet_card_le_of_regularOne {m : ℕ} {G : SimpleGraph (Fin (2 * m))}
    (hG : RegularOfDegree G 1) {t : Finset (Fin (2 * m))}
    (hI : G.IsIndepSet ((t : Finset (Fin (2 * m))) : Set (Fin (2 * m)))) :
    t.card ≤ m := by
  classical
  let mateEmb : Fin (2 * m) ↪ Fin (2 * m) :=
    ⟨mate hG, mate_injective hG⟩
  have hdisj : Disjoint t (t.map mateEmb) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvT hvMap
    rcases Finset.mem_map.mp hvMap with ⟨w, hwT, hwv⟩
    have hvT' : mate hG w ∈ t := by
      rw [← hwv] at hvT
      simpa [mateEmb] using hvT
    exact hI (show w ∈ ((t : Finset (Fin (2 * m))) : Set (Fin (2 * m))) from hwT)
      (show mate hG w ∈ ((t : Finset (Fin (2 * m))) : Set (Fin (2 * m))) from hvT')
      (mate_ne_self hG w).symm (adj_mate hG w)
  have hcard :
      t.card + t.card ≤ 2 * m := by
    calc
      t.card + t.card = (t ∪ t.map mateEmb).card := by
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_map]
      _ ≤ (Finset.univ : Finset (Fin (2 * m))).card := Finset.card_le_univ _
      _ = 2 * m := by simp
  omega

private lemma induced_regular_degree_eq_zero_or_one_of_nonempty {m : ℕ}
    {G : SimpleGraph (Fin (2 * m))} (hG : RegularOfDegree G 1)
    {t : Finset (Fin (2 * m))} {δ : ℕ}
    (htne : t.Nonempty) (hreg : InducesRegularOfDegree G t δ) :
    δ = 0 ∨ δ = 1 := by
  classical
  obtain ⟨v, hv⟩ := htne
  rw [InducesRegularOfDegree] at hreg
  by_cases hneigh : ∃ w : ↑(t : Set (Fin (2 * m))), (inducedOn G t).Adj ⟨v, hv⟩ w
  · rcases hneigh with ⟨w, hw⟩
    have hmate : mate hG v ∈ t := by
      simpa [mate_eq_of_adj hG (by simpa [inducedOn] using hw)] using w.property
    let u : ↑(t : Set (Fin (2 * m))) := ⟨mate hG v, hmate⟩
    have hu : (inducedOn G t).Adj ⟨v, hv⟩ u := by
      simpa [u, inducedOn] using adj_mate hG v
    have huniq : ∃! w : ↑(t : Set (Fin (2 * m))), (inducedOn G t).Adj ⟨v, hv⟩ w := by
      refine ⟨u, hu, ?_⟩
      intro y hy
      apply Subtype.ext
      exact (mate_eq_of_adj hG (by simpa [inducedOn] using hy)).symm
    have hdeg1 : (inducedOn G t).degree ⟨v, hv⟩ = 1 := by
      exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).2 huniq
    exact Or.inr ((hreg ⟨v, hv⟩).symm.trans hdeg1)
  · have hdeg0 : (inducedOn G t).degree ⟨v, hv⟩ = 0 := by
      by_contra hzero
      have hpos : 0 < (inducedOn G t).degree ⟨v, hv⟩ := Nat.pos_of_ne_zero hzero
      exact hneigh (((inducedOn G t).degree_pos_iff_exists_adj ⟨v, hv⟩).1 hpos)
    exact Or.inl ((hreg ⟨v, hv⟩).symm.trans hdeg0)

private lemma inducesRegularOfDegree_one_even_card {m : ℕ}
    {G : SimpleGraph (Fin (2 * m))} {t : Finset (Fin (2 * m))}
    (hreg : InducesRegularOfDegree G t 1) :
    Even t.card := by
  classical
  rw [InducesRegularOfDegree] at hreg
  have hperfect : (⊤ : Subgraph (inducedOn G t)).IsPerfectMatching := by
    rw [Subgraph.isPerfectMatching_iff]
    intro v
    exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp (hreg v)
  simpa [Fintype.card_coe] using hperfect.even_card

private lemma exists_regularOfDegree_one_fin_even (m : ℕ) :
    ∃ G : SimpleGraph (Fin (2 * m)), RegularOfDegree G 1 := by
  classical
  let s : Set (Fin (2 * m)) := {v | (v : ℕ) < m}
  let t : Set (Fin (2 * m)) := {v | m ≤ (v : ℕ)}
  have hst : Disjoint s t := by
    rw [Set.disjoint_iff]
    intro v hvst
    simp [s, t] at hvst
    omega
  let f : s ≃ t :=
    { toFun := fun v => by
        refine ⟨⟨(v : ℕ) + m, ?_⟩, ?_⟩
        · have hv : (v : ℕ) < m := by
            have hv' := v.property
            change (((v : s) : Fin (2 * m)) : ℕ) < m at hv'
            exact hv'
          omega
        · change m ≤ (v : ℕ) + m
          omega
      invFun := fun v => by
        refine ⟨⟨(v : ℕ) - m, ?_⟩, ?_⟩
        · exact lt_of_le_of_lt (Nat.sub_le _ _) v.1.isLt
        · have hv : m ≤ (v : ℕ) := by
            have hv' := v.property
            change m ≤ (((v : t) : Fin (2 * m)) : ℕ) at hv'
            exact hv'
          have hb : (v : ℕ) < 2 * m := v.1.isLt
          refine lt_of_add_lt_add_right (a := m) ?_
          rw [Nat.sub_add_cancel hv]
          simpa [two_mul] using hb
      left_inv := by
        intro v
        apply Subtype.ext
        apply Fin.ext
        change (((v : ℕ) + m) - m) = (v : ℕ)
        rw [Nat.add_sub_cancel]
      right_inv := by
        intro v
        apply Subtype.ext
        apply Fin.ext
        have hv : m ≤ (v : ℕ) := by
          have hv' := v.property
          change m ≤ (((v : t) : Fin (2 * m)) : ℕ) at hv'
          exact hv'
        change (((v : ℕ) - m) + m) = (v : ℕ)
        rw [Nat.sub_add_cancel hv] }
  obtain ⟨M, hverts, hmatch⟩ :=
    Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv (G := (⊤ : SimpleGraph (Fin (2 * m))))
      hst f (by
        intro v
        simp [SimpleGraph.top_adj]
        have hv : (v : ℕ) < m := by
          have hv' := v.property
          change (((v : s) : Fin (2 * m)) : ℕ) < m at hv'
          exact hv'
        have hfv : m ≤ ((f v : Fin (2 * m)) : ℕ) := by
          have hfv' := (f v).property
          change m ≤ (((f v : t) : Fin (2 * m)) : ℕ) at hfv'
          exact hfv'
        intro hEq
        have hEq' : (v : ℕ) = ((f v : Fin (2 * m)) : ℕ) := by
          exact congrArg (fun x : Fin (2 * m) => (x : ℕ)) hEq
        omega)
  have hspan : M.IsSpanning := by
    intro v
    rw [hverts]
    by_cases hv : (v : ℕ) < m
    · exact Or.inl (by simpa [s] using hv)
    · have hvt : m ≤ (v : ℕ) := by omega
      exact Or.inr (by simpa [t] using hvt)
  have hperfect : M.IsPerfectMatching := ⟨hmatch, hspan⟩
  refine ⟨M.spanningCoe, ?_⟩
  intro v
  calc
    M.spanningCoe.degree v = M.degree v := Subgraph.degree_spanningCoe (G' := M) v
    _ = 1 := (Subgraph.isPerfectMatching_iff_forall_degree.mp hperfect) v

private lemma classify_canonical_witness_in_regularOne {m : ℕ}
    {G : SimpleGraph (Fin (2 * m))} (hG : RegularOfDegree G 1)
    {s δ : ℕ} {t : Finset (Fin (2 * m))}
    (htcard : t.card = s) (hreg : InducesRegularOfDegree G t δ)
    (hcanon : t.Nonempty ∨ δ = 0) :
    (s ≤ m ∧ δ = 0) ∨ ∃ k, 1 ≤ k ∧ k ≤ m ∧ s = 2 * k ∧ δ = 1 := by
  by_cases htne : t.Nonempty
  · rcases induced_regular_degree_eq_zero_or_one_of_nonempty hG htne hreg with hδ | hδ
    · left
      constructor
      · have hI : G.IsIndepSet ((t : Finset (Fin (2 * m))) : Set (Fin (2 * m))) := by
          exact isIndepSet_of_inducesRegularOfDegree_zero (by simpa [hδ] using hreg)
        have hsle : t.card ≤ m := indepSet_card_le_of_regularOne hG hI
        simpa [htcard] using hsle
      · exact hδ
    · right
      have hsEven : Even s := by
        have hEven : Even t.card := by
          exact inducesRegularOfDegree_one_even_card (by simpa [hδ] using hreg)
        simpa [htcard] using hEven
      have hspos : 0 < s := by
        simpa [htcard] using Finset.card_pos.mpr htne
      have hsle : s ≤ 2 * m := by
        simpa [htcard] using t.card_le_univ
      obtain ⟨k, hk⟩ := hsEven
      refine ⟨k, ?_, ?_, ?_, hδ⟩ <;> omega
  · have hδ : δ = 0 := hcanon.resolve_left htne
    left
    constructor
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
      have hs0 : s = 0 := by simpa [ht0] using htcard.symm
      omega
    · exact hδ

/-- Exact description of `U(n, 0)`: only independent witnesses occur. -/
theorem mem_universalProfile_zero_iff {n s δ : ℕ} :
    (s, δ) ∈ UniversalProfile n 0 ↔ s ≤ n ∧ δ = 0 := by
  classical
  constructor
  · intro h
    have hbot : RegularOfDegree (⊥ : SimpleGraph (Fin n)) 0 := by
      intro v
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      simp [SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
    rcases h (⊥ : SimpleGraph (Fin n)) hbot with ⟨t, htcard, hreg, hcanon⟩
    have htcard' : t.card = s := by simpa using htcard
    have hs : s ≤ n := by
      rw [← htcard']
      simpa using t.card_le_univ
    have hδ : δ = 0 := by
      by_cases htne : t.Nonempty
      · obtain ⟨v, hv⟩ := htne
        have hzero : InducesRegularOfDegree (⊥ : SimpleGraph (Fin n)) t 0 :=
          inducesRegularOfDegree_of_induce_eq_bot _ _ (by
            ext x y
            simp)
        letI : DecidableRel (⊥ : SimpleGraph (Fin n)).Adj :=
          fun a b => Classical.propDecidable ((⊥ : SimpleGraph (Fin n)).Adj a b)
        rw [InducesRegularOfDegree] at hzero hreg
        exact ((hzero ⟨v, hv⟩).symm.trans (hreg ⟨v, hv⟩)).symm
      · exact hcanon.resolve_left htne
    exact ⟨hs, hδ⟩
  · rintro ⟨hs, rfl⟩ G hG
    have hI : G.IsIndepSet (Set.univ : Set (Fin n)) :=
      zero_regular_isIndepSet_univ hG
    have hs' : s ≤ (Finset.univ : Finset (Fin n)).card := by
      simpa using hs
    obtain ⟨t, htsub, htcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := s) hs'
    refine ⟨t, htcard, ?_, Or.inr rfl⟩
    refine inducesRegularOfDegree_of_isIndepSet G t ?_
    intro v hv w hw hne hadj
    exact hI (by simp) (by simp) hne hadj

/-- Exact description of `U(n, n - 1)`: only clique witnesses occur. -/
theorem mem_universalProfile_full_iff {n s δ : ℕ} :
    (s, δ) ∈ UniversalProfile n (n - 1) ↔ s ≤ n ∧ δ = s - 1 := by
  classical
  constructor
  · intro h
    have htop : RegularOfDegree (⊤ : SimpleGraph (Fin n)) (n - 1) := by
      intro v
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      have hcard : ({w : Fin n | ¬ v = w} : Finset (Fin n)).card = n - 1 := by
        have hfilter : ({w : Fin n | ¬ v = w} : Finset (Fin n)) = Finset.univ.erase v := by
          ext w
          simp [eq_comm]
        rw [hfilter]
        simpa using
          Finset.card_erase_of_mem (s := (Finset.univ : Finset (Fin n))) (a := v)
            (by simp : v ∈ (Finset.univ : Finset (Fin n)))
      simpa [SimpleGraph.top_adj, eq_comm] using hcard.symm
    rcases h (⊤ : SimpleGraph (Fin n)) htop with ⟨t, htcard, hreg, hcanon⟩
    have htcard' : t.card = s := by simpa using htcard
    have hs : s ≤ n := by
      rw [← htcard']
      simpa using t.card_le_univ
    have hδ : δ = s - 1 := by
      by_cases htne : t.Nonempty
      · obtain ⟨v, hv⟩ := htne
        have hclique : (⊤ : SimpleGraph (Fin n)).IsClique ((t : Finset (Fin n)) : Set (Fin n)) := by
          intro x hx y hy hxy
          simp [hxy]
        have htopreg : InducesRegularOfDegree (⊤ : SimpleGraph (Fin n)) t (t.card - 1) :=
          inducesRegularOfDegree_of_isClique _ _ hclique
        letI : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj :=
          fun a b => Classical.propDecidable ((⊤ : SimpleGraph (Fin n)).Adj a b)
        rw [InducesRegularOfDegree] at hreg htopreg
        have : δ = t.card - 1 := (hreg ⟨v, hv⟩).symm.trans (htopreg ⟨v, hv⟩)
        simpa [htcard'] using this
      · have hδ0 : δ = 0 := hcanon.resolve_left htne
        have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
        have hs0 : s = 0 := by simpa [ht0] using htcard'.symm
        subst hs0
        simpa using hδ0
    exact ⟨hs, hδ⟩
  · rintro ⟨hs, rfl⟩ G hG
    have hC : G.IsClique (Set.univ : Set (Fin n)) :=
      full_regular_isClique_univ hG
    have hs' : s ≤ (Finset.univ : Finset (Fin n)).card := by
      simpa using hs
    obtain ⟨t, htsub, htcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := s) hs'
    refine ⟨t, htcard, ?_, ?_⟩
    · have hCt : G.IsClique ((t : Finset (Fin n)) : Set (Fin n)) :=
        hC.subset (by intro x hx; simp)
      simpa [htcard] using inducesRegularOfDegree_of_isClique G t hCt
    · by_cases htne : t.Nonempty
      · exact Or.inl htne
      · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
        have hs0 : s = 0 := by simpa [ht0] using htcard.symm
        subst hs0
        exact Or.inr rfl

private lemma inducedOn_compl_eq_compl_inducedOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : Finset V) :
    inducedOn Gᶜ t = (inducedOn G t)ᶜ := by
  ext x y
  simp [inducedOn, SimpleGraph.compl_adj]

private lemma regularOfEq {V : Type*} [Fintype V] {G H : SimpleGraph V}
    [hdecG : DecidableRel G.Adj] [hdecH : DecidableRel H.Adj]
    {d : ℕ} (hGH : G = H) (hreg : G.IsRegularOfDegree d) :
    H.IsRegularOfDegree d := by
  subst hGH
  cases Subsingleton.elim hdecG hdecH
  exact hreg

private lemma inducesRegularOfDegree_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V} {d : ℕ}
    (h : InducesRegularOfDegree G t d) :
    InducesRegularOfDegree Gᶜ t (t.card - 1 - d) := by
  classical
  letI : DecidableRel (inducedOn G t).Adj :=
    fun a b => Classical.propDecidable ((inducedOn G t).Adj a b)
  letI : DecidableRel (inducedOn Gᶜ t).Adj :=
    fun a b => Classical.propDecidable ((inducedOn Gᶜ t).Adj a b)
  rw [InducesRegularOfDegree] at h ⊢
  have hcompl : ((inducedOn G t)ᶜ).IsRegularOfDegree (t.card - 1 - d) := by
    simpa [Fintype.card_coe] using h.compl
  exact regularOfEq (inducedOn_compl_eq_compl_inducedOn G t).symm hcompl

/-- One direction of the universal-profile complement symmetry from Section 26. -/
theorem mem_universalProfile_compl {n ρ s δ : ℕ}
    (hρ : ρ ≤ n - 1)
    (h : (s, δ) ∈ UniversalProfile n ρ) :
    (s, s - 1 - δ) ∈ UniversalProfile n (n - 1 - ρ) := by
  intro G hG
  letI : DecidableRel G.Adj := fun a b => Classical.propDecidable (G.Adj a b)
  have hGcompl : RegularOfDegree Gᶜ ρ := by
    intro v
    rw [SimpleGraph.degree_compl]
    rw [hG v, Fintype.card_fin, Nat.sub_sub_self hρ]
  rcases h Gᶜ hGcompl with ⟨t, htcard, hreg, hcanon⟩
  refine ⟨t, htcard, ?_, ?_⟩
  · simpa [htcard] using inducesRegularOfDegree_compl Gᶜ hreg
  · by_cases htne : t.Nonempty
    · exact Or.inl htne
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
      have hs0 : s = 0 := by simpa [ht0] using htcard.symm
      subst hs0
      exact Or.inr (by simp)

/-- The packaged complement symmetry from Section 26. -/
theorem mem_universalProfile_compl_iff {n ρ s δ : ℕ}
    (hρ : ρ ≤ n - 1) (hδ : δ ≤ s - 1) :
    (s, δ) ∈ UniversalProfile n ρ ↔
      (s, s - 1 - δ) ∈ UniversalProfile n (n - 1 - ρ) := by
  constructor
  · exact mem_universalProfile_compl hρ
  · intro h
    have h' :
        (s, s - 1 - (s - 1 - δ)) ∈ UniversalProfile n (n - 1 - (n - 1 - ρ)) :=
      mem_universalProfile_compl (n := n) (ρ := n - 1 - ρ) (s := s) (δ := s - 1 - δ)
        (Nat.sub_le _ _) h
    have hδ' : s - 1 - (s - 1 - δ) = δ := by omega
    have hρ' : n - 1 - (n - 1 - ρ) = ρ := by omega
    simpa [hδ', hρ'] using h'

/-- Exact description of `U(2m, 1)`: independent subsets of a matching, or unions of `t` edges. -/
theorem mem_universalProfile_one_even_iff {m s δ : ℕ} :
    (s, δ) ∈ UniversalProfile (2 * m) 1 ↔
      (s ≤ m ∧ δ = 0) ∨ ∃ t, 1 ≤ t ∧ t ≤ m ∧ s = 2 * t ∧ δ = 1 := by
  constructor
  · intro h
    obtain ⟨G, hG⟩ := exists_regularOfDegree_one_fin_even m
    rcases h G hG with ⟨t, htcard, hreg, hcanon⟩
    exact classify_canonical_witness_in_regularOne hG htcard hreg hcanon
  · intro h
    rcases h with h | ⟨t, htpos, htm, hs, hδ⟩
    · rcases h with ⟨hs, hδ0⟩
      subst hδ0
      intro G hG
      have hcard : (mateLeftFinset hG).card = m := mateLeftFinset_card hG
      have hs' : s ≤ (mateLeftFinset hG).card := by simpa [hcard] using hs
      obtain ⟨a, ha, hcardA⟩ :=
        Finset.exists_subset_card_eq (s := mateLeftFinset hG) (n := s) hs'
      refine ⟨a, hcardA, ?_, Or.inr rfl⟩
      have hI : G.IsIndepSet ((a : Finset (Fin (2 * m))) : Set (Fin (2 * m))) :=
        by
          intro x hx y hy hxy hadj
          exact mateLeftFinset_isIndepSet hG (ha hx) (ha hy) hxy hadj
      exact inducesRegularOfDegree_of_isIndepSet G a hI
    · subst hs
      subst hδ
      intro G hG
      have hcard : (mateLeftFinset hG).card = m := mateLeftFinset_card hG
      have ht' : t ≤ (mateLeftFinset hG).card := by simpa [hcard] using htm
      obtain ⟨a, ha, hcardA⟩ :=
        Finset.exists_subset_card_eq (s := mateLeftFinset hG) (n := t) ht'
      have hpair : (pairUnion hG a).card = 2 * t := by
        simpa [hcardA] using pairUnion_card hG ha
      have hreg : InducesRegularOfDegree G (pairUnion hG a) 1 :=
        inducesRegularOfDegree_pairUnion_one hG a
      have hne : (pairUnion hG a).Nonempty := by
        have hapos : 0 < a.card := by omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hapos
        exact ⟨v, by
          dsimp [pairUnion]
          exact Finset.mem_union.mpr (Or.inl hv)⟩
      exact ⟨pairUnion hG a, hpair, hreg, Or.inl hne⟩

end UniversalProfiles

section UniversalProfilesRhoTwo

/-- The exact small-order `ρ = 2` profile table needed for the `q = 8` program. -/
abbrev UniversalProfileTwoLt8Formula (n s δ : ℕ) : Prop :=
  match n with
  | 3 => (s ≤ 1 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 3 ∧ δ = 2)
  | 4 => (s ≤ 2 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 4 ∧ δ = 2)
  | 5 => (s ≤ 2 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 5 ∧ δ = 2)
  | 6 => (s ≤ 2 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 4 ∧ δ = 1) ∨ (s = 6 ∧ δ = 2)
  | 7 => (s ≤ 3 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 4 ∧ δ = 1) ∨ (s = 7 ∧ δ = 2)
  | _ => False

private lemma degree_inducedOn_eq_card_neighborFinset_inter
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (t : Finset W) (v : ↑(t : Set W)) :
    (inducedOn G t).degree v = (G.neighborFinset v ∩ t).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G t).neighborFinset v).map (Function.Embedding.subtype (· ∈ (t : Set W))) =
        G.neighborFinset v ∩ t := by
    ext x
    simp [inducedOn, and_assoc]
  calc
    ((inducedOn G t).neighborFinset v).card =
        (((inducedOn G t).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ (t : Set W)))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset v ∩ t).card := by rw [hmap]

private lemma inducedOn_degree_le_degree
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {t : Finset W} (v : ↑(t : Set W)) :
    (inducedOn G t).degree v ≤ G.degree v := by
  rw [degree_inducedOn_eq_card_neighborFinset_inter (G := G) (t := t) (v := v)]
  calc
    (G.neighborFinset v ∩ t).card ≤ (G.neighborFinset v).card := by
      exact Finset.card_le_card (by
        intro x hx
        exact (Finset.mem_inter.mp hx).1)
    _ = G.degree v := by
      exact SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := (v : W))

private abbrev RegularOfDegreeDec {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : W, G.degree v = d

private abbrev InducesRegularOfDegreeDec {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (t : Finset W) (d : ℕ) : Prop :=
  ∀ v : ↑(t : Set W), (inducedOn G t).degree v = d

private abbrev HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (s δ : ℕ) : Prop :=
  ∃ t : Finset W, t.card = s ∧ InducesRegularOfDegreeDec G t δ ∧ (t.Nonempty ∨ δ = 0)

private lemma regularOfDegreeDec_iff {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {d : ℕ} :
    RegularOfDegreeDec G d ↔ RegularOfDegree G d := by
  classical
  unfold RegularOfDegreeDec RegularOfDegree
  have hinst : (inferInstance : DecidableRel G.Adj) = Classical.decRel G.Adj :=
    Subsingleton.elim _ _
  cases hinst
  rfl

private lemma inducesRegularOfDegreeDec_iff {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {t : Finset W} {d : ℕ} :
    InducesRegularOfDegreeDec G t d ↔ InducesRegularOfDegree G t d := by
  classical
  unfold InducesRegularOfDegreeDec InducesRegularOfDegree
  have hinst : (inferInstance : DecidableRel G.Adj) = Classical.decRel G.Adj :=
    Subsingleton.elim _ _
  cases hinst
  rfl

private lemma hasCanonicalRegularInducedSubgraphOfCardAndDegreeDec_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec G s δ ↔
      HasCanonicalRegularInducedSubgraphOfCardAndDegree G s δ := by
  constructor
  · rintro ⟨t, htcard, hreg, hcanon⟩
    exact ⟨t, htcard, (inducesRegularOfDegreeDec_iff G).mp hreg, hcanon⟩
  · rintro ⟨t, htcard, hreg, hcanon⟩
    exact ⟨t, htcard, (inducesRegularOfDegreeDec_iff G).mpr hreg, hcanon⟩

private lemma regularOfDegreeDec_two_cycleGraph {n : ℕ}
    (hn : 3 ≤ n) :
    RegularOfDegreeDec (SimpleGraph.cycleGraph n) 2 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = m + 3 := by omega
  subst hn'
  intro v
  simpa using (SimpleGraph.cycleGraph_degree_three_le (n := m) (v := v))

private def twoTrianglesSix : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(3, 4), s(4, 5), s(3, 5)} : Finset (Sym2 (Fin 6)))

private def trianglePlusSquareSeven : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(3, 4), s(4, 5), s(5, 6), s(3, 6)} :
      Finset (Sym2 (Fin 7)))

instance : DecidableRel twoTrianglesSix.Adj := by
  unfold twoTrianglesSix
  infer_instance

instance : DecidableRel trianglePlusSquareSeven.Adj := by
  unfold trianglePlusSquareSeven
  infer_instance

private theorem regularOfDegreeDec_twoTrianglesSix : RegularOfDegreeDec twoTrianglesSix 2 := by
  native_decide

private theorem regularOfDegreeDec_trianglePlusSquareSeven :
    RegularOfDegreeDec trianglePlusSquareSeven 2 := by
  native_decide

private abbrev CycleSixFormula (s δ : ℕ) : Prop :=
  (s ≤ 3 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 4 ∧ δ = 1) ∨ (s = 6 ∧ δ = 2)

private abbrev TwoTrianglesSixFormula (s δ : ℕ) : Prop :=
  (s ≤ 2 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 3 ∧ δ = 2) ∨ (s = 4 ∧ δ = 1) ∨ (s = 6 ∧ δ = 2)

private abbrev CycleSevenFormula (s δ : ℕ) : Prop :=
  (s ≤ 3 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 4 ∧ δ = 1) ∨ (s = 7 ∧ δ = 2)

private abbrev TrianglePlusSquareSevenFormula (s δ : ℕ) : Prop :=
  (s ≤ 3 ∧ δ = 0) ∨ (s = 2 ∧ δ = 1) ∨ (s = 3 ∧ δ = 2) ∨
    (s = 4 ∧ δ = 1) ∨ (s = 4 ∧ δ = 2) ∨ (s = 7 ∧ δ = 2)

private lemma canonical_card_le {n s δ : ℕ} {G : SimpleGraph (Fin n)}
    (h : HasCanonicalRegularInducedSubgraphOfCardAndDegree G s δ) :
    s ≤ n := by
  rcases h with ⟨t, htcard, _hreg, _hcanon⟩
  have htcard' : t.card = s := by simpa using htcard
  rw [← htcard']
  simpa using t.card_le_univ

private lemma canonical_degree_le_of_regular_two {n s δ : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hG : RegularOfDegreeDec G 2)
    (h : HasCanonicalRegularInducedSubgraphOfCardAndDegree G s δ) :
    δ ≤ 2 := by
  rcases h with ⟨t, _htcard, hreg, hcanon⟩
  by_cases htne : t.Nonempty
  · obtain ⟨v, hv⟩ := htne
    have hreg' : InducesRegularOfDegreeDec G t δ := by
      have hreg'' : InducesRegularOfDegree G t δ := by simpa using hreg
      exact (inducesRegularOfDegreeDec_iff G).mpr hreg''
    have hle : (inducedOn G t).degree ⟨v, hv⟩ ≤ G.degree v :=
      inducedOn_degree_le_degree (G := G) ⟨v, hv⟩
    calc
      δ = (inducedOn G t).degree ⟨v, hv⟩ := by symm; exact hreg' ⟨v, hv⟩
      _ ≤ G.degree v := hle
      _ = 2 := hG v
  · have hδ0 : δ = 0 := hcanon.resolve_left htne
    omega

private lemma canonical_formula_of_table {n s δ : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {P : ℕ → ℕ → Prop}
    (hG : RegularOfDegreeDec G 2)
    (htable : ∀ s' : Fin (n + 1), ∀ δ' : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec G s'.1 δ'.1 ↔ P s'.1 δ'.1)
    (h : HasCanonicalRegularInducedSubgraphOfCardAndDegree G s δ) :
    P s δ := by
  have hs : s ≤ n := canonical_card_le h
  have hδ : δ ≤ 2 := canonical_degree_le_of_regular_two hG h
  have hDec : HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec G s δ :=
    (hasCanonicalRegularInducedSubgraphOfCardAndDegreeDec_iff G).mpr h
  let s' : Fin (n + 1) := ⟨s, by omega⟩
  let δ' : Fin 3 := ⟨δ, by omega⟩
  simpa [s', δ'] using (htable s' δ').mp hDec

private lemma canonical_of_formula_of_table {n s δ : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {P : ℕ → ℕ → Prop}
    (hs : s ≤ n) (hδ : δ ≤ 2)
    (htable : ∀ s' : Fin (n + 1), ∀ δ' : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec G s'.1 δ'.1 ↔ P s'.1 δ'.1)
    (h : P s δ) :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree G s δ := by
  let s' : Fin (n + 1) := ⟨s, by omega⟩
  let δ' : Fin 3 := ⟨δ, by omega⟩
  have hDec : HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec G s δ := by
    simpa [s', δ'] using (htable s' δ').mpr h
  exact (hasCanonicalRegularInducedSubgraphOfCardAndDegreeDec_iff G).mp hDec

private theorem cycleThreeCanonicalTable :
    ∀ s : Fin 4, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (SimpleGraph.cycleGraph 3) s.1 δ.1 ↔
        UniversalProfileTwoLt8Formula 3 s.1 δ.1 := by
  native_decide

private theorem cycleFourCanonicalTable :
    ∀ s : Fin 5, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (SimpleGraph.cycleGraph 4) s.1 δ.1 ↔
        UniversalProfileTwoLt8Formula 4 s.1 δ.1 := by
  native_decide

private theorem cycleFiveCanonicalTable :
    ∀ s : Fin 6, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (SimpleGraph.cycleGraph 5) s.1 δ.1 ↔
        UniversalProfileTwoLt8Formula 5 s.1 δ.1 := by
  native_decide

private theorem cycleSixCanonicalTable :
    ∀ s : Fin 7, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (SimpleGraph.cycleGraph 6) s.1 δ.1 ↔
        CycleSixFormula s.1 δ.1 := by
  native_decide

private theorem twoTrianglesSixCanonicalTable :
    ∀ s : Fin 7, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec twoTrianglesSix s.1 δ.1 ↔
        TwoTrianglesSixFormula s.1 δ.1 := by
  native_decide

private theorem cycleSevenCanonicalTable :
    ∀ s : Fin 8, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (SimpleGraph.cycleGraph 7) s.1 δ.1 ↔
        CycleSevenFormula s.1 δ.1 := by
  native_decide

private theorem trianglePlusSquareSevenCanonicalTable :
    ∀ s : Fin 8, ∀ δ : Fin 3,
      HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec trianglePlusSquareSeven s.1 δ.1 ↔
        TrianglePlusSquareSevenFormula s.1 δ.1 := by
  native_decide

/-- Exact induced-regular profile of the unique `2`-regular graph on `3` vertices. -/
theorem cycleThree_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree (SimpleGraph.cycleGraph 3) s δ ↔
      UniversalProfileTwoLt8Formula 3 s δ := by
  constructor
  · exact canonical_formula_of_table (G := SimpleGraph.cycleGraph 3)
      (regularOfDegreeDec_two_cycleGraph (n := 3) (by omega)) cycleThreeCanonicalTable
  · intro h
    have hs : s ≤ 3 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact canonical_of_formula_of_table (G := SimpleGraph.cycleGraph 3) hs hδ
      cycleThreeCanonicalTable h

/-- Exact induced-regular profile of the unique `2`-regular graph on `4` vertices. -/
theorem cycleFour_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree (SimpleGraph.cycleGraph 4) s δ ↔
      UniversalProfileTwoLt8Formula 4 s δ := by
  constructor
  · exact canonical_formula_of_table (G := SimpleGraph.cycleGraph 4)
      (regularOfDegreeDec_two_cycleGraph (n := 4) (by omega)) cycleFourCanonicalTable
  · intro h
    have hs : s ≤ 4 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact canonical_of_formula_of_table (G := SimpleGraph.cycleGraph 4) hs hδ
      cycleFourCanonicalTable h

/-- Exact induced-regular profile of the unique `2`-regular graph on `5` vertices. -/
theorem cycleFive_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree (SimpleGraph.cycleGraph 5) s δ ↔
      UniversalProfileTwoLt8Formula 5 s δ := by
  constructor
  · exact canonical_formula_of_table (G := SimpleGraph.cycleGraph 5)
      (regularOfDegreeDec_two_cycleGraph (n := 5) (by omega)) cycleFiveCanonicalTable
  · intro h
    have hs : s ≤ 5 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact canonical_of_formula_of_table (G := SimpleGraph.cycleGraph 5) hs hδ
      cycleFiveCanonicalTable h

/-- Exact induced-regular profile of the `6`-cycle. -/
theorem cycleSix_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree (SimpleGraph.cycleGraph 6) s δ ↔
      CycleSixFormula s δ := by
  constructor
  · exact canonical_formula_of_table (G := SimpleGraph.cycleGraph 6)
      (regularOfDegreeDec_two_cycleGraph (n := 6) (by omega)) cycleSixCanonicalTable
  · intro h
    have hs : s ≤ 6 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    exact canonical_of_formula_of_table (G := SimpleGraph.cycleGraph 6) hs hδ
      cycleSixCanonicalTable h

/-- Exact induced-regular profile of `C₃ ⊔ C₃`. -/
theorem twoTrianglesSix_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree twoTrianglesSix s δ ↔
      TwoTrianglesSixFormula s δ := by
  constructor
  · exact canonical_formula_of_table (G := twoTrianglesSix)
      regularOfDegreeDec_twoTrianglesSix twoTrianglesSixCanonicalTable
  · intro h
    have hs : s ≤ 6 := by
      rcases h with h0 | h1 | h2 | h3 | h4 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 | h4 <;> omega
    exact canonical_of_formula_of_table (G := twoTrianglesSix) hs hδ
      twoTrianglesSixCanonicalTable h

/-- Exact induced-regular profile of the `7`-cycle. -/
theorem cycleSeven_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree (SimpleGraph.cycleGraph 7) s δ ↔
      CycleSevenFormula s δ := by
  constructor
  · exact canonical_formula_of_table (G := SimpleGraph.cycleGraph 7)
      (regularOfDegreeDec_two_cycleGraph (n := 7) (by omega)) cycleSevenCanonicalTable
  · intro h
    have hs : s ≤ 7 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    exact canonical_of_formula_of_table (G := SimpleGraph.cycleGraph 7) hs hδ
      cycleSevenCanonicalTable h

/-- Exact induced-regular profile of `C₃ ⊔ C₄`. -/
theorem trianglePlusSquareSeven_hasCanonicalRegularSubgraph_iff {s δ : ℕ} :
    HasCanonicalRegularInducedSubgraphOfCardAndDegree trianglePlusSquareSeven s δ ↔
      TrianglePlusSquareSevenFormula s δ := by
  constructor
  · exact canonical_formula_of_table (G := trianglePlusSquareSeven)
      regularOfDegreeDec_trianglePlusSquareSeven trianglePlusSquareSevenCanonicalTable
  · intro h
    have hs : s ≤ 7 := by
      rcases h with h0 | h1 | h2 | h3 | h4 | h5 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 | h4 | h5 <;> omega
    exact canonical_of_formula_of_table (G := trianglePlusSquareSeven) hs hδ
      trianglePlusSquareSevenCanonicalTable h

private abbrev GraphCode (n : ℕ) :=
  { adj : Fin n → Fin n → Bool // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x) }

private def graphOfCode {n : ℕ} (c : GraphCode n) : SimpleGraph (Fin n) :=
  SimpleGraph.mk' c

private instance {n : ℕ} (c : GraphCode n) : DecidableRel (graphOfCode c).Adj := by
  dsimp [graphOfCode, SimpleGraph.mk']
  infer_instance

private lemma graphOfCode_surjective {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ c : GraphCode n, graphOfCode c = G := by
  classical
  refine ⟨⟨fun v w => decide (G.Adj v w), ?_, ?_⟩, ?_⟩
  · intro x y
    by_cases h : G.Adj x y
    · have h' : G.Adj y x := G.symm h
      simp [h, h']
    · have h' : ¬ G.Adj y x := by
        intro hyx
        exact h (G.symm hyx)
      simp [h, h']
  · intro x
    have h : ¬ G.Adj x x := G.loopless.irrefl x
    simp
  · ext v w
    by_cases h : G.Adj v w
    · simp [graphOfCode, SimpleGraph.mk', h]
    · simp [graphOfCode, SimpleGraph.mk', h]

private abbrev UniversalProfileDec (n ρ s δ : ℕ) : Prop :=
  ∀ c : GraphCode n, RegularOfDegreeDec (graphOfCode c) ρ →
    HasCanonicalRegularInducedSubgraphOfCardAndDegreeDec (graphOfCode c) s δ

private instance (n ρ s δ : ℕ) : Decidable (UniversalProfileDec n ρ s δ) := by
  unfold UniversalProfileDec
  infer_instance

private lemma universalProfileDec_iff {n ρ s δ : ℕ} :
    UniversalProfileDec n ρ s δ ↔ (s, δ) ∈ UniversalProfile n ρ := by
  classical
  constructor
  · intro h G hG
    rcases graphOfCode_surjective G with ⟨c, rfl⟩
    exact (hasCanonicalRegularInducedSubgraphOfCardAndDegreeDec_iff (graphOfCode c)).mp
      (h c ((regularOfDegreeDec_iff (graphOfCode c)).mpr hG))
  · intro h G hG
    exact (hasCanonicalRegularInducedSubgraphOfCardAndDegreeDec_iff (graphOfCode G)).mpr
      (h (graphOfCode G) ((regularOfDegreeDec_iff (graphOfCode G)).mp hG))

private lemma universalProfile_formula_of_table {n s δ : ℕ} {P : ℕ → ℕ → Prop}
    (hcycle : RegularOfDegreeDec (SimpleGraph.cycleGraph n) 2)
    (htable : ∀ s' : Fin (n + 1), ∀ δ' : Fin 3,
      UniversalProfileDec n 2 s'.1 δ'.1 ↔ P s'.1 δ'.1)
    (h : (s, δ) ∈ UniversalProfile n 2) :
    P s δ := by
  have hCanonCycle : HasCanonicalRegularInducedSubgraphOfCardAndDegree
      (SimpleGraph.cycleGraph n) s δ :=
    h _ ((regularOfDegreeDec_iff _).mp hcycle)
  have hs : s ≤ n := canonical_card_le hCanonCycle
  have hδ : δ ≤ 2 := canonical_degree_le_of_regular_two hcycle hCanonCycle
  have hDec : UniversalProfileDec n 2 s δ := (universalProfileDec_iff).mpr h
  let s' : Fin (n + 1) := ⟨s, by omega⟩
  let δ' : Fin 3 := ⟨δ, by omega⟩
  simpa [s', δ'] using (htable s' δ').mp hDec

private lemma universalProfile_of_formula_of_table {n s δ : ℕ} {P : ℕ → ℕ → Prop}
    (hs : s ≤ n) (hδ : δ ≤ 2)
    (htable : ∀ s' : Fin (n + 1), ∀ δ' : Fin 3,
      UniversalProfileDec n 2 s'.1 δ'.1 ↔ P s'.1 δ'.1)
    (h : P s δ) :
    (s, δ) ∈ UniversalProfile n 2 := by
  let s' : Fin (n + 1) := ⟨s, by omega⟩
  let δ' : Fin 3 := ⟨δ, by omega⟩
  have hDec : UniversalProfileDec n 2 s δ := by
    simpa [s', δ'] using (htable s' δ').mpr h
  exact (universalProfileDec_iff).mp hDec

private theorem universalProfileTwoThreeTable :
    ∀ s : Fin 4, ∀ δ : Fin 3,
      UniversalProfileDec 3 2 s.1 δ.1 ↔ UniversalProfileTwoLt8Formula 3 s.1 δ.1 := by
  native_decide

private theorem universalProfileTwoFourTable :
    ∀ s : Fin 5, ∀ δ : Fin 3,
      UniversalProfileDec 4 2 s.1 δ.1 ↔ UniversalProfileTwoLt8Formula 4 s.1 δ.1 := by
  native_decide

private theorem universalProfileTwoFiveTable :
    ∀ s : Fin 6, ∀ δ : Fin 3,
      UniversalProfileDec 5 2 s.1 δ.1 ↔ UniversalProfileTwoLt8Formula 5 s.1 δ.1 := by
  native_decide

private theorem universalProfileTwoSixTable :
    ∀ s : Fin 7, ∀ δ : Fin 3,
      UniversalProfileDec 6 2 s.1 δ.1 ↔ UniversalProfileTwoLt8Formula 6 s.1 δ.1 := by
  native_decide

private theorem universalProfileTwoSevenTable :
    ∀ s : Fin 8, ∀ δ : Fin 3,
      UniversalProfileDec 7 2 s.1 δ.1 ↔ UniversalProfileTwoLt8Formula 7 s.1 δ.1 := by
  native_decide

/-- Exact description of `U(3, 2)`. -/
theorem mem_universalProfile_two_three_iff {s δ : ℕ} :
    (s, δ) ∈ UniversalProfile 3 2 ↔ UniversalProfileTwoLt8Formula 3 s δ := by
  constructor
  · exact universalProfile_formula_of_table
      (hcycle := regularOfDegreeDec_two_cycleGraph (n := 3) (by omega))
      universalProfileTwoThreeTable
  · intro h
    have hs : s ≤ 3 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact universalProfile_of_formula_of_table hs hδ universalProfileTwoThreeTable h

/-- Exact description of `U(4, 2)`. -/
theorem mem_universalProfile_two_four_iff {s δ : ℕ} :
    (s, δ) ∈ UniversalProfile 4 2 ↔ UniversalProfileTwoLt8Formula 4 s δ := by
  constructor
  · exact universalProfile_formula_of_table
      (hcycle := regularOfDegreeDec_two_cycleGraph (n := 4) (by omega))
      universalProfileTwoFourTable
  · intro h
    have hs : s ≤ 4 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact universalProfile_of_formula_of_table hs hδ universalProfileTwoFourTable h

/-- Exact description of `U(5, 2)`. -/
theorem mem_universalProfile_two_five_iff {s δ : ℕ} :
    (s, δ) ∈ UniversalProfile 5 2 ↔ UniversalProfileTwoLt8Formula 5 s δ := by
  constructor
  · exact universalProfile_formula_of_table
      (hcycle := regularOfDegreeDec_two_cycleGraph (n := 5) (by omega))
      universalProfileTwoFiveTable
  · intro h
    have hs : s ≤ 5 := by
      rcases h with h0 | h1 | h2 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 <;> omega
    exact universalProfile_of_formula_of_table hs hδ universalProfileTwoFiveTable h

/-- Exact description of `U(6, 2)`. -/
theorem mem_universalProfile_two_six_iff {s δ : ℕ} :
    (s, δ) ∈ UniversalProfile 6 2 ↔ UniversalProfileTwoLt8Formula 6 s δ := by
  constructor
  · exact universalProfile_formula_of_table
      (hcycle := regularOfDegreeDec_two_cycleGraph (n := 6) (by omega))
      universalProfileTwoSixTable
  · intro h
    have hs : s ≤ 6 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    exact universalProfile_of_formula_of_table hs hδ universalProfileTwoSixTable h

/-- Exact description of `U(7, 2)`. -/
theorem mem_universalProfile_two_seven_iff {s δ : ℕ} :
    (s, δ) ∈ UniversalProfile 7 2 ↔ UniversalProfileTwoLt8Formula 7 s δ := by
  constructor
  · exact universalProfile_formula_of_table
      (hcycle := regularOfDegreeDec_two_cycleGraph (n := 7) (by omega))
      universalProfileTwoSevenTable
  · intro h
    have hs : s ≤ 7 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    have hδ : δ ≤ 2 := by
      rcases h with h0 | h1 | h2 | h3 <;> omega
    exact universalProfile_of_formula_of_table hs hδ universalProfileTwoSevenTable h

/-- Exact description of `U(n, 2)` in the small range needed for the `q = 8` program. -/
theorem mem_universalProfile_two_lt8_iff {n s δ : ℕ} (hn3 : 3 ≤ n) (hn8 : n < 8) :
    (s, δ) ∈ UniversalProfile n 2 ↔ UniversalProfileTwoLt8Formula n s δ := by
  have hn : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact mem_universalProfile_two_three_iff
  · exact mem_universalProfile_two_four_iff
  · exact mem_universalProfile_two_five_iff
  · exact mem_universalProfile_two_six_iff
  · exact mem_universalProfile_two_seven_iff

end UniversalProfilesRhoTwo

end RegularInducedSubgraph
