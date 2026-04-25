import Mathlib

/-!
# Split graphs and the Földes–Hammer characterization

A graph is a *split graph* when its vertex set partitions into a clique `K`
and an independent set `I`. The Földes–Hammer theorem states that this is
equivalent to forbidding the three induced subgraphs `2K₂`, `C₄`, `C₅`.

This file develops the definitions and the easy direction (split ⇒
{2K₂,C₄,C₅}-free). The hard direction lives in
`RegularInducedSubgraph.Combinatorics.FoldesHammer`.

## Main definitions

* `SimpleGraph.IsSplitGraph G` — `G` admits a partition into a clique and an
  independent set.
* `RegularInducedSubgraph.twoK₂` — the disjoint union of two edges, as a
  `SimpleGraph (Fin 4)`.
* `RegularInducedSubgraph.cycleFour`, `cycleFive` — the cycles `C₄`, `C₅`
  (using `cycleGraph`).
* `SimpleGraph.IsInducedCopyFree G H` — there is no induced copy of `H` in `G`,
  i.e. no `SimpleGraph.Embedding` from `H` into `G`. Because
  `SimpleGraph.Embedding` is a `RelEmbedding`, this reflects non-adjacency
  automatically, so it is the correct notion of *induced* copy.
-/

namespace SimpleGraph

universe u

variable {V : Type u}

/-- A graph `G` is a split graph if its vertex set partitions into a clique
and an independent set. -/
def IsSplitGraph (G : SimpleGraph V) : Prop :=
  ∃ K I : Set V, K ∪ I = Set.univ ∧ Disjoint K I ∧ G.IsClique K ∧ G.IsIndepSet I

/-- `G` contains no induced copy of `H`: there is no graph embedding from `H`
into `G`. (`SimpleGraph.Embedding` is a `RelEmbedding`, so it both preserves
and reflects adjacency, making this the *induced* copy-free notion.) -/
def IsInducedCopyFree (G : SimpleGraph V) {W : Type*} (H : SimpleGraph W) : Prop :=
  IsEmpty (H ↪g G)

end SimpleGraph

namespace RegularInducedSubgraph

open SimpleGraph

/-- The graph `2K₂` on four vertices: two disjoint edges. -/
def twoK₂ : SimpleGraph (Fin 4) := fromEdgeSet {s(0, 1), s(2, 3)}

/-- The 4-cycle, as a `SimpleGraph (Fin 4)`. -/
def cycleFour : SimpleGraph (Fin 4) := cycleGraph 4

/-- The 5-cycle, as a `SimpleGraph (Fin 5)`. -/
def cycleFive : SimpleGraph (Fin 5) := cycleGraph 5

instance : DecidableRel twoK₂.Adj := by
  unfold twoK₂; infer_instance

instance : DecidableRel cycleFour.Adj := by
  unfold cycleFour; infer_instance

instance : DecidableRel cycleFive.Adj := by
  unfold cycleFive; infer_instance

end RegularInducedSubgraph

/-! ## Easy direction lemmas -/

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- In a split graph with parts `K` (clique) and `I` (independent set), every
vertex lies in `K` or in `I`. -/
lemma mem_clique_or_indep_of_partition
    {K I : Set V} (hKI : K ∪ I = Set.univ) (v : V) : v ∈ K ∨ v ∈ I := by
  have hv : v ∈ (Set.univ : Set V) := Set.mem_univ v
  rw [← hKI] at hv
  exact hv

/-- Within an independent part, an `H`-embedding cannot place two adjacent
vertices of `H`. -/
lemma not_adj_image_of_both_in_indep
    {W : Type*} {H : SimpleGraph W}
    {I : Set V} (hI : G.IsIndepSet I)
    (φ : H ↪g G) {x y : W}
    (hx : φ x ∈ I) (hy : φ y ∈ I) (hxy : H.Adj x y) : False := by
  have hG : G.Adj (φ x) (φ y) := φ.map_rel_iff.mpr hxy
  exact hI hx hy (G.ne_of_adj hG) hG

/-- Within a clique part, an `H`-embedding's images of distinct vertices are
adjacent in `H`. -/
lemma adj_of_both_image_in_clique
    {W : Type*} {H : SimpleGraph W}
    {K : Set V} (hK : G.IsClique K)
    (φ : H ↪g G) {x y : W}
    (hx : φ x ∈ K) (hy : φ y ∈ K) (hne : x ≠ y) : H.Adj x y := by
  have hneφ : φ x ≠ φ y := fun h => hne (φ.injective h)
  exact φ.map_rel_iff.mp (hK hx hy hneφ)

end SimpleGraph

/-! ## Easy direction proper -/

namespace RegularInducedSubgraph

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A split-graph embedding of `H`: each `H`-vertex is colored by which part of
the partition its image lies in (`true` = clique, `false` = independent),
and the colours satisfy the split-graph constraints. -/
private lemma splitGraph_embedding_colour
    {W : Type*} {H : SimpleGraph W} (hG : G.IsSplitGraph) (φ : H ↪g G) :
    ∃ f : W → Bool,
      (∀ x y, f x = true → f y = true → x ≠ y → H.Adj x y) ∧
      (∀ x y, f x = false → f y = false → ¬ H.Adj x y) := by
  classical
  obtain ⟨K, I, hKI, _hdisj, hK, hI⟩ := hG
  refine ⟨fun w => decide (φ w ∈ K), ?_, ?_⟩
  · intro x y hx hy hne
    have hxK : φ x ∈ K := by simpa using hx
    have hyK : φ y ∈ K := by simpa using hy
    exact adj_of_both_image_in_clique hK φ hxK hyK hne
  · intro x y hx hy hadj
    have hxK : φ x ∉ K := by simpa using hx
    have hyK : φ y ∉ K := by simpa using hy
    have hxI : φ x ∈ I := (mem_clique_or_indep_of_partition hKI _).resolve_left hxK
    have hyI : φ y ∈ I := (mem_clique_or_indep_of_partition hKI _).resolve_left hyK
    exact not_adj_image_of_both_in_indep hI φ hxI hyI hadj

/-! ### Adjacency facts for `2K₂`, `C₄`, `C₅` -/

@[simp] lemma twoK₂_adj_iff {u v : Fin 4} :
    twoK₂.Adj u v ↔ (s(u, v) = s(0, 1) ∨ s(u, v) = s(2, 3)) ∧ u ≠ v := by
  unfold twoK₂; rw [fromEdgeSet_adj]; simp

lemma twoK₂_adj_01 : twoK₂.Adj (0 : Fin 4) 1 := by decide
lemma twoK₂_adj_23 : twoK₂.Adj (2 : Fin 4) 3 := by decide
lemma twoK₂_not_adj_02 : ¬ twoK₂.Adj (0 : Fin 4) 2 := by decide
lemma twoK₂_not_adj_03 : ¬ twoK₂.Adj (0 : Fin 4) 3 := by decide
lemma twoK₂_not_adj_12 : ¬ twoK₂.Adj (1 : Fin 4) 2 := by decide
lemma twoK₂_not_adj_13 : ¬ twoK₂.Adj (1 : Fin 4) 3 := by decide

/-- A split graph contains no induced `2K₂`.

The two edges `0–1` and `2–3` of `2K₂` each have at least one endpoint in the
clique part `K` (otherwise both endpoints would lie in the independent part,
forcing them not to be adjacent in `G`, contradicting that `H`-adjacency lifts
to `G`-adjacency). Picking such a `K`-endpoint from each edge gives two
distinct vertices in `K` whose `2K₂`-adjacency is forced — but no cross-pair
`{0,1} × {2,3}` is `2K₂`-adjacent. Contradiction. -/
theorem IsSplitGraph.no_induced_twoK₂ (hG : G.IsSplitGraph) :
    G.IsInducedCopyFree twoK₂ := by
  classical
  refine ⟨fun φ => ?_⟩
  obtain ⟨f, hKclique, hIindep⟩ := splitGraph_embedding_colour hG φ
  have edge_has_K : ∀ {a b : Fin 4}, twoK₂.Adj a b → f a = true ∨ f b = true := by
    intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨ha, hb⟩ := h
    have ha' : f a = false := by cases hf : f a <;> simp_all
    have hb' : f b = false := by cases hf : f b <;> simp_all
    exact hIindep a b ha' hb' hab
  have h01 := edge_has_K twoK₂_adj_01
  have h23 := edge_has_K twoK₂_adj_23
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
  · exact twoK₂_not_adj_02 (hKclique 0 2 h0 h2 (by decide))
  · exact twoK₂_not_adj_03 (hKclique 0 3 h0 h3 (by decide))
  · exact twoK₂_not_adj_12 (hKclique 1 2 h1 h2 (by decide))
  · exact twoK₂_not_adj_13 (hKclique 1 3 h1 h3 (by decide))

/-! ### Key enumeration lemmas (closed by `native_decide`) -/

private lemma cycleFour_split_colouring_impossible :
    ∀ g : Fin 4 → Bool,
      (∀ x y : Fin 4, g x = true → g y = true → x ≠ y → cycleFour.Adj x y) →
      (∀ x y : Fin 4, g x = false → g y = false → ¬ cycleFour.Adj x y) → False := by
  native_decide

private lemma cycleFive_split_colouring_impossible :
    ∀ g : Fin 5 → Bool,
      (∀ x y : Fin 5, g x = true → g y = true → x ≠ y → cycleFive.Adj x y) →
      (∀ x y : Fin 5, g x = false → g y = false → ¬ cycleFive.Adj x y) → False := by
  native_decide

/-- A split graph contains no induced `C₄`. The split partition gives a
2-colouring of `Fin 4` with the constraint that within colour `true` (clique
side) distinct vertices are `cycleFour`-adjacent, and within colour `false`
(independent side) vertices are non-adjacent. We discharge by exhausting all
`2^4 = 16` colourings. -/
theorem IsSplitGraph.no_induced_cycleFour (hG : G.IsSplitGraph) :
    G.IsInducedCopyFree cycleFour := by
  classical
  refine ⟨fun φ => ?_⟩
  obtain ⟨f, hKclique, hIindep⟩ := splitGraph_embedding_colour hG φ
  exact cycleFour_split_colouring_impossible f hKclique hIindep

/-- A split graph contains no induced `C₅`. Same enumeration strategy as C₄,
across all `2^5 = 32` colourings of `Fin 5`. -/
theorem IsSplitGraph.no_induced_cycleFive (hG : G.IsSplitGraph) :
    G.IsInducedCopyFree cycleFive := by
  classical
  refine ⟨fun φ => ?_⟩
  obtain ⟨f, hKclique, hIindep⟩ := splitGraph_embedding_colour hG φ
  exact cycleFive_split_colouring_impossible f hKclique hIindep

/-- **Easy direction of Földes–Hammer.** A split graph admits no induced copy
of any of `2K₂`, `C₄`, `C₅`. -/
theorem IsSplitGraph.no_induced_forbidden (hG : G.IsSplitGraph) :
    G.IsInducedCopyFree twoK₂ ∧
    G.IsInducedCopyFree cycleFour ∧
    G.IsInducedCopyFree cycleFive :=
  ⟨IsSplitGraph.no_induced_twoK₂ hG,
   IsSplitGraph.no_induced_cycleFour hG,
   IsSplitGraph.no_induced_cycleFive hG⟩

end RegularInducedSubgraph
