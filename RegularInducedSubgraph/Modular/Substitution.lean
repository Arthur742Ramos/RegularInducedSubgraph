import RegularInducedSubgraph.Basic

/-!
# Same-type heavy pair lemma (Lemma 16.1)

This file formalises Lemma 16.1 of `notes/remaining-gap-obstruction-module.md`.

In a homogeneous substitution graph, a *bag* is a vertex set that is either a clique or an
independent set, and any two distinct bags are connected by either a complete or empty bipartite
graph.  Lemma 16.1 says:

> If two bags `A` and `B` have the **same type** (both clique-bags or both independent-bags) and
> each has size at least `q / 2`, then `G` already contains a regular induced `q`-subgraph.

Concretely, take `A' ⊆ A` and `B' ⊆ B` with `|A'| = |B'| = q/2` and set `U := A' ∪ B'`.  We split
into the four sign cases of (bag type, cross type):

| case | A type | B type | cross  | structure of `G[U]`        | degree     |
|------|--------|--------|--------|----------------------------|------------|
| 1    | clique | clique | full   | `K_q`                      | `q-1`      |
| 2    | indep. | indep. | empty  | empty `q`-vertex graph     | `0`        |
| 3    | clique | clique | empty  | `K_{q/2} ⊔ K_{q/2}`        | `q/2-1`    |
| 4    | indep. | indep. | full   | `K_{q/2,q/2}`              | `q/2`      |

Each case is exposed as its own theorem; the four are then bundled into the same-type heavy pair
lemma `hasRegularInducedSubgraphOfCard_of_same_type_heavy_pair`.
-/

namespace RegularInducedSubgraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Local helpers -/

private lemma degree_inducedOn_eq_card_inter_substitution
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : ↑(s : Set V)) :
    (inducedOn G s).degree v = (G.neighborFinset (v : V) ∩ s).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G s).neighborFinset v).map (Function.Embedding.subtype (· ∈ (s : Set V))) =
        G.neighborFinset (v : V) ∩ s := by
    ext x
    simp [inducedOn, and_assoc]
  calc
    ((inducedOn G s).neighborFinset v).card =
        (((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ (s : Set V)))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset (v : V) ∩ s).card := by rw [hmap]

private lemma exists_disjoint_subsets_of_card_eq_half
    {q : ℕ} {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      A'.card = q / 2 ∧ B'.card = q / 2 ∧ Disjoint A' B' := by
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hB
  refine ⟨A', B', hA'sub, hB'sub, hA'card, hB'card, ?_⟩
  exact hAB.mono hA'sub hB'sub

private lemma card_union_eq_q_of_halves
    {q : ℕ} (hq2 : 2 ∣ q) {A' B' : Finset V}
    (hA' : A'.card = q / 2) (hB' : B'.card = q / 2)
    (hdisj : Disjoint A' B') :
    (A' ∪ B').card = q := by
  rw [Finset.card_union_of_disjoint hdisj, hA', hB']
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma neighborFinset_inter_eq_erase_of_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : Finset V} (hs : G.IsClique (s : Set V)) {v : V} (hv : v ∈ s) :
    G.neighborFinset v ∩ s = s.erase v := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  refine ⟨fun ⟨hadj, hw⟩ => ⟨?_, hw⟩, ?_⟩
  · intro hwv; subst hwv; exact (hadj.ne rfl).elim
  rintro ⟨hne, hw⟩
  refine ⟨?_, hw⟩
  exact hs hv hw (fun h => hne h.symm)

private lemma neighborFinset_inter_eq_empty_of_isIndepSet
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : Finset V} (hs : G.IsIndepSet (s : Set V)) {v : V} (hv : v ∈ s) :
    G.neighborFinset v ∩ s = ∅ := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.notMem_empty,
    iff_false, not_and]
  intro hadj hw
  by_cases hvw : v = w
  · subst hvw; exact (hadj.ne rfl).elim
  · exact hs hv hw hvw hadj

private lemma neighborFinset_inter_eq_self_of_complete_cross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : Finset V} (hcross : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) {v : V} (hv : v ∈ s) :
    G.neighborFinset v ∩ t = t := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun ⟨_, hw⟩ => hw, fun hw => ⟨hcross v hv w hw, hw⟩⟩

private lemma neighborFinset_inter_eq_empty_of_anticomplete_cross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : Finset V} (hcross : ∀ x ∈ s, ∀ y ∈ t, ¬ G.Adj x y) {v : V} (hv : v ∈ s) :
    G.neighborFinset v ∩ t = ∅ := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.notMem_empty,
    iff_false, not_and]
  intro hadj hw
  exact hcross v hv w hw hadj

private lemma card_neighborFinset_inter_union_disjoint
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

/-! ## Case 1 — clique-clique with complete cross -/

theorem hasRegularInducedSubgraphOfCard_of_clique_clique_complete
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq2 : 2 ∣ q)
    {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card)
    (hAclique : G.IsClique (A : Set V)) (hBclique : G.IsClique (B : Set V))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y) :
    HasRegularInducedSubgraphOfCard G q := by
  obtain ⟨A', B', hA'sub, hB'sub, hA'card, hB'card, hdisj⟩ :=
    exists_disjoint_subsets_of_card_eq_half hAB hA hB
  have hUcard : (A' ∪ B').card = q :=
    card_union_eq_q_of_halves hq2 hA'card hB'card hdisj
  have hUclique : G.IsClique ((A' ∪ B' : Finset V) : Set V) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hxA | hxB
    · rcases hy with hyA | hyB
      · exact hAclique (hA'sub hxA) (hA'sub hyA) hxy
      · exact hcross x (hA'sub hxA) y (hB'sub hyB)
    · rcases hy with hyA | hyB
      · exact (hcross y (hA'sub hyA) x (hB'sub hxB)).symm
      · exact hBclique (hB'sub hxB) (hB'sub hyB) hxy
  exact ⟨A' ∪ B', hUcard.ge, (A' ∪ B').card - 1,
    inducesRegularOfDegree_of_isClique G (A' ∪ B') hUclique⟩

/-! ## Case 2 — indep-indep with empty cross -/

theorem hasRegularInducedSubgraphOfCard_of_indep_indep_empty
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq2 : 2 ∣ q)
    {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card)
    (hAindep : G.IsIndepSet (A : Set V)) (hBindep : G.IsIndepSet (B : Set V))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    HasRegularInducedSubgraphOfCard G q := by
  obtain ⟨A', B', hA'sub, hB'sub, hA'card, hB'card, hdisj⟩ :=
    exists_disjoint_subsets_of_card_eq_half hAB hA hB
  have hUcard : (A' ∪ B').card = q :=
    card_union_eq_q_of_halves hq2 hA'card hB'card hdisj
  have hUindep : G.IsIndepSet ((A' ∪ B' : Finset V) : Set V) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hxA | hxB
    · rcases hy with hyA | hyB
      · exact hAindep (hA'sub hxA) (hA'sub hyA) hxy
      · exact hcross x (hA'sub hxA) y (hB'sub hyB)
    · rcases hy with hyA | hyB
      · intro hadj
        exact hcross y (hA'sub hyA) x (hB'sub hxB) hadj.symm
      · exact hBindep (hB'sub hxB) (hB'sub hyB) hxy
  exact ⟨A' ∪ B', hUcard.ge, 0,
    inducesRegularOfDegree_of_isIndepSet G (A' ∪ B') hUindep⟩

/-! ## Cases 3 and 4 — explicit degree computation -/

/-- Case 3: clique-clique anticomplete on subsets of size `q / 2` gives a `(q/2 - 1)`-regular
induced subgraph on `q` vertices. -/
theorem hasRegularInducedSubgraphOfCard_of_clique_clique_empty
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq2 : 2 ∣ q)
    {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card)
    (hAclique : G.IsClique (A : Set V)) (hBclique : G.IsClique (B : Set V))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    HasRegularInducedSubgraphOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  obtain ⟨A', B', hA'sub, hB'sub, hA'card, hB'card, hdisj⟩ :=
    exists_disjoint_subsets_of_card_eq_half hAB hA hB
  have hUcard : (A' ∪ B').card = q :=
    card_union_eq_q_of_halves hq2 hA'card hB'card hdisj
  have hA'clique : G.IsClique (A' : Set V) := hAclique.subset (Finset.coe_subset.mpr hA'sub)
  have hB'clique : G.IsClique (B' : Set V) := hBclique.subset (Finset.coe_subset.mpr hB'sub)
  have hcross' : ∀ x ∈ A', ∀ y ∈ B', ¬ G.Adj x y := by
    intro x hx y hy
    exact hcross x (hA'sub hx) y (hB'sub hy)
  have hcross_sym : ∀ x ∈ B', ∀ y ∈ A', ¬ G.Adj x y := by
    intro x hx y hy hadj
    exact hcross' y hy x hx hadj.symm
  refine ⟨A' ∪ B', hUcard.ge, q / 2 - 1, ?_⟩
  show (inducedOn G (A' ∪ B')).IsRegularOfDegree (q / 2 - 1)
  intro v
  have hvU : (v : V) ∈ A' ∪ B' := v.2
  rw [degree_inducedOn_eq_card_inter_substitution G (A' ∪ B') v,
      card_neighborFinset_inter_union_disjoint G hdisj]
  rcases Finset.mem_union.mp hvU with hvA | hvB
  · rw [neighborFinset_inter_eq_erase_of_isClique G hA'clique hvA,
        neighborFinset_inter_eq_empty_of_anticomplete_cross G hcross' hvA,
        Finset.card_erase_of_mem hvA, hA'card, Finset.card_empty]
    simp
  · rw [neighborFinset_inter_eq_empty_of_anticomplete_cross G hcross_sym hvB,
        neighborFinset_inter_eq_erase_of_isClique G hB'clique hvB,
        Finset.card_erase_of_mem hvB, hB'card, Finset.card_empty]
    simp

/-- Case 4: indep-indep complete cross on subsets of size `q / 2` gives a `(q/2)`-regular induced
subgraph on `q` vertices (the bipartite graph `K_{q/2,q/2}`). -/
theorem hasRegularInducedSubgraphOfCard_of_indep_indep_complete
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq2 : 2 ∣ q)
    {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card)
    (hAindep : G.IsIndepSet (A : Set V)) (hBindep : G.IsIndepSet (B : Set V))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y) :
    HasRegularInducedSubgraphOfCard G q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  obtain ⟨A', B', hA'sub, hB'sub, hA'card, hB'card, hdisj⟩ :=
    exists_disjoint_subsets_of_card_eq_half hAB hA hB
  have hUcard : (A' ∪ B').card = q :=
    card_union_eq_q_of_halves hq2 hA'card hB'card hdisj
  have hA'indep : G.IsIndepSet (A' : Set V) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hA'sub) hAindep
  have hB'indep : G.IsIndepSet (B' : Set V) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hB'sub) hBindep
  have hcross' : ∀ x ∈ A', ∀ y ∈ B', G.Adj x y := by
    intro x hx y hy
    exact hcross x (hA'sub hx) y (hB'sub hy)
  have hcross_sym : ∀ x ∈ B', ∀ y ∈ A', G.Adj x y := by
    intro x hx y hy
    exact (hcross' y hy x hx).symm
  refine ⟨A' ∪ B', hUcard.ge, q / 2, ?_⟩
  show (inducedOn G (A' ∪ B')).IsRegularOfDegree (q / 2)
  intro v
  have hvU : (v : V) ∈ A' ∪ B' := v.2
  rw [degree_inducedOn_eq_card_inter_substitution G (A' ∪ B') v,
      card_neighborFinset_inter_union_disjoint G hdisj]
  rcases Finset.mem_union.mp hvU with hvA | hvB
  · rw [neighborFinset_inter_eq_empty_of_isIndepSet G hA'indep hvA,
        neighborFinset_inter_eq_self_of_complete_cross G hcross' hvA,
        Finset.card_empty, hB'card]
    simp
  · rw [neighborFinset_inter_eq_self_of_complete_cross G hcross_sym hvB,
        neighborFinset_inter_eq_empty_of_isIndepSet G hB'indep hvB,
        Finset.card_empty, hA'card]
    simp

/-! ## Lemma 16.1 — same-type heavy pair -/

/--
**Lemma 16.1** (`notes/remaining-gap-obstruction-module.md`).

Suppose `A`, `B` are disjoint vertex sets in `G`, each of size at least `q / 2`, both
homogeneous (clique or independent), and **of the same type** (both clique-bags or both
independent-bags).  Suppose the cross between `A` and `B` is itself homogeneous (complete or
empty).  Then `G` already contains a regular induced `q`-subgraph.
-/
theorem hasRegularInducedSubgraphOfCard_of_same_type_heavy_pair
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq2 : 2 ∣ q)
    {A B : Finset V} (hAB : Disjoint A B)
    (hA : q / 2 ≤ A.card) (hB : q / 2 ≤ B.card)
    (hsame :
      (G.IsClique (A : Set V) ∧ G.IsClique (B : Set V)) ∨
      (G.IsIndepSet (A : Set V) ∧ G.IsIndepSet (B : Set V)))
    (hcross : (∀ x ∈ A, ∀ y ∈ B, G.Adj x y) ∨ (∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)) :
    HasRegularInducedSubgraphOfCard G q := by
  rcases hsame with ⟨hAcl, hBcl⟩ | ⟨hAin, hBin⟩
  · rcases hcross with hC | hC
    · exact hasRegularInducedSubgraphOfCard_of_clique_clique_complete G hq2 hAB hA hB
        hAcl hBcl hC
    · exact hasRegularInducedSubgraphOfCard_of_clique_clique_empty G hq2 hAB hA hB
        hAcl hBcl hC
  · rcases hcross with hC | hC
    · exact hasRegularInducedSubgraphOfCard_of_indep_indep_complete G hq2 hAB hA hB
        hAin hBin hC
    · exact hasRegularInducedSubgraphOfCard_of_indep_indep_empty G hq2 hAB hA hB
        hAin hBin hC

end RegularInducedSubgraph
