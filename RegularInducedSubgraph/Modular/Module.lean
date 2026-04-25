import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import RegularInducedSubgraph.Modular.Finite

/-!
# Graph modules and the small-module regular subgraph criterion

This file formalises the substitution / module machinery from §17 of
`notes/remaining-gap-obstruction-module.md`.

A finite vertex set `M` is a *graph module* of `G` when every vertex outside `M` is adjacent to
either all or none of `M` — equivalently, vertices in `V \ M` cannot distinguish vertices of `M`
through the adjacency relation.

The two main results formalised here are:

* `IsGraphModule.inducesModEqDegree_of_modEq_degree_on` (Proposition 17.1):
  if `M` is a module of `G` and the ambient degrees of `G` are all congruent modulo `q` on `M`,
  then the induced subgraph `G[M]` is `q`-modular.

* `IsGraphModule.hasRegularInducedSubgraphOfCard_of_card_le_modulus_of_modEq_degree_on`
  (Corollary 17.2): if in addition `M.card ≤ q`, then `G[M]` is regular.  Together with
  `M.card = k`, this provides a `HasRegularInducedSubgraphOfCard G k` witness.

These are the substitution-side ingredients of the surviving Modular q² → q Regular Selection
problem (cf. `notes/remaining-gap-math-memo.md` §10 and `notes/last-gap-proof-roadmap.md`).
-/

namespace RegularInducedSubgraph

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A finite vertex set `M` is a **graph module** of `G` when every outside vertex is adjacent to
either all or none of `M`.  Formally: for every `w ∉ M` and every pair `v, v' ∈ M`,
`G.Adj w v ↔ G.Adj w v'`.

This is the standard substitution / homogeneous-set notion, recorded in §17 of
`notes/remaining-gap-obstruction-module.md`.
-/
def IsGraphModule (G : SimpleGraph V) (M : Finset V) : Prop :=
  ∀ ⦃w : V⦄, w ∉ M → ∀ ⦃v v' : V⦄, v ∈ M → v' ∈ M → (G.Adj w v ↔ G.Adj w v')

/-- Open-neighbourhood partition along a finset (as a cardinality equality). -/
private lemma card_neighborFinset_partition_module
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) (v : V) :
    (G.neighborFinset v).card =
      (G.neighborFinset v ∩ M).card + (G.neighborFinset v \ M).card := by
  classical
  have hdisj :
      Disjoint (G.neighborFinset v ∩ M) (G.neighborFinset v \ M) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  have hunion :
      (G.neighborFinset v ∩ M) ∪ (G.neighborFinset v \ M) = G.neighborFinset v := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hxM : x ∈ M
      · exact Or.inl ⟨h, hxM⟩
      · exact Or.inr ⟨h, hxM⟩
  calc
    (G.neighborFinset v).card
        = ((G.neighborFinset v ∩ M) ∪ (G.neighborFinset v \ M)).card := by rw [hunion]
    _ = (G.neighborFinset v ∩ M).card + (G.neighborFinset v \ M).card :=
          Finset.card_union_of_disjoint hdisj

/-- Local copy of the standard induced-degree formula:
inside `inducedOn G s`, the degree of a vertex equals the cardinality of its ambient
neighbourhood intersected with `s`. -/
private lemma degree_inducedOn_eq_card_neighborFinset_inter_module
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

namespace IsGraphModule

variable {G : SimpleGraph V} [DecidableRel G.Adj] {M : Finset V}

/-- Outside the module, the open neighbourhood is the *same set* for every member of `M`. -/
lemma neighborFinset_sdiff_eq
    (hM : IsGraphModule G M) {v v' : V} (hv : v ∈ M) (hv' : v' ∈ M) :
    G.neighborFinset v \ M = G.neighborFinset v' \ M := by
  classical
  ext w
  simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
  refine ⟨?_, ?_⟩
  · rintro ⟨hadj, hwM⟩
    refine ⟨?_, hwM⟩
    have hwv : G.Adj w v := G.symm hadj
    exact G.symm ((hM hwM hv hv').mp hwv)
  · rintro ⟨hadj, hwM⟩
    refine ⟨?_, hwM⟩
    have hwv' : G.Adj w v' := G.symm hadj
    exact G.symm ((hM hwM hv hv').mpr hwv')

/-- The "outside degree" (number of ambient neighbours that lie outside `M`) is constant on `M`. -/
lemma sdiff_card_eq
    (hM : IsGraphModule G M) {v v' : V} (hv : v ∈ M) (hv' : v' ∈ M) :
    (G.neighborFinset v \ M).card = (G.neighborFinset v' \ M).card := by
  rw [hM.neighborFinset_sdiff_eq hv hv']

/--
Decomposition of the **ambient** degree of a module member into its **internal** induced degree
plus the (constant on `M`) **outside** degree.
-/
lemma degree_eq_inducedOn_add_sdiff
    (hM : IsGraphModule G M) {v : V} (hv : v ∈ M) :
    G.degree v =
      (inducedOn G M).degree ⟨v, hv⟩ + (G.neighborFinset v \ M).card := by
  classical
  have hcard :
      (G.neighborFinset v).card =
        (G.neighborFinset v ∩ M).card + (G.neighborFinset v \ M).card :=
    card_neighborFinset_partition_module (G := G) (M := M) (v := v)
  have hdeg : G.degree v = (G.neighborFinset v).card :=
    (G.card_neighborFinset_eq_degree (v := v)).symm
  have hind : (inducedOn G M).degree ⟨v, hv⟩ = (G.neighborFinset v ∩ M).card :=
    degree_inducedOn_eq_card_neighborFinset_inter_module (G := G) (s := M) ⟨v, hv⟩
  rw [hdeg, hcard, hind]

/--
**Proposition 17.1** (`notes/remaining-gap-obstruction-module.md`).
If `M` is a graph module of `G` and the ambient degrees of `G` are congruent modulo `q` on `M`,
then the induced subgraph `G[M]` is `q`-modular.
-/
theorem inducesModEqDegree_of_modEq_degree_on
    {q : ℕ} (hM : IsGraphModule G M)
    (hdeg : ∀ ⦃v w : V⦄, v ∈ M → w ∈ M → G.degree v ≡ G.degree w [MOD q]) :
    InducesModEqDegree G M q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesModEqDegree]
  rintro ⟨v, hv⟩ ⟨w, hw⟩
  have h1 :
      G.degree v =
        (inducedOn G M).degree (⟨v, hv⟩ : ↑(M : Set V)) +
          (G.neighborFinset v \ M).card :=
    hM.degree_eq_inducedOn_add_sdiff hv
  have h2 :
      G.degree w =
        (inducedOn G M).degree (⟨w, hw⟩ : ↑(M : Set V)) +
          (G.neighborFinset w \ M).card :=
    hM.degree_eq_inducedOn_add_sdiff hw
  have hsame :
      (G.neighborFinset v \ M).card = (G.neighborFinset w \ M).card :=
    hM.sdiff_card_eq hv hw
  have hdvw : G.degree v ≡ G.degree w [MOD q] := hdeg hv hw
  rw [h1, h2, hsame] at hdvw
  exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl _) hdvw

/--
**Proposition 17.1, global version**.  Same statement but with the global hypothesis
`∀ v w, G.degree v ≡ G.degree w [MOD q]` (the ambient graph is `q`-regular *modulo* `q`).
-/
theorem inducesModEqDegree_of_modEq_degree
    {q : ℕ} (hM : IsGraphModule G M)
    (hdeg : ∀ v w : V, G.degree v ≡ G.degree w [MOD q]) :
    InducesModEqDegree G M q :=
  hM.inducesModEqDegree_of_modEq_degree_on (fun v w _ _ => hdeg v w)

/--
**Corollary 17.2**.  A module of size at most the modulus collapses to a regular induced
subgraph: if `M.card ≤ q`, the ambient `q`-modularity hypothesis on `M` already forces
`G[M]` to be regular.
-/
theorem exists_inducesRegularOfDegree_of_card_le_modulus_of_modEq_degree_on
    {q : ℕ} (hM : IsGraphModule G M) (hcard : M.card ≤ q)
    (hdeg : ∀ ⦃v w : V⦄, v ∈ M → w ∈ M → G.degree v ≡ G.degree w [MOD q]) :
    ∃ d : ℕ, InducesRegularOfDegree G M d :=
  inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree
    G hcard (hM.inducesModEqDegree_of_modEq_degree_on hdeg)

/-- Global-degree version of Corollary 17.2. -/
theorem exists_inducesRegularOfDegree_of_card_le_modulus_of_modEq_degree
    {q : ℕ} (hM : IsGraphModule G M) (hcard : M.card ≤ q)
    (hdeg : ∀ v w : V, G.degree v ≡ G.degree w [MOD q]) :
    ∃ d : ℕ, InducesRegularOfDegree G M d :=
  hM.exists_inducesRegularOfDegree_of_card_le_modulus_of_modEq_degree_on
    hcard (fun _ _ _ _ => hdeg _ _)

/--
Packaged form of Corollary 17.2.1: a graph module of size **exactly** `k` (with `k ≤ q`) and
`q`-modular ambient degrees on `M` provides a regular induced subgraph of cardinality `k`.
In particular, taking `k = q` yields the canonical "size-`q` regular induced subgraph from a
size-`q` module" packaging used by the Modular q² → q Regular Selection program.
-/
theorem hasRegularInducedSubgraphOfCard_of_card_eq_of_modEq_degree_on
    {k q : ℕ} (hM : IsGraphModule G M) (hk : M.card = k) (hkq : k ≤ q)
    (hdeg : ∀ ⦃v w : V⦄, v ∈ M → w ∈ M → G.degree v ≡ G.degree w [MOD q]) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  have hMq : M.card ≤ q := hk ▸ hkq
  obtain ⟨d, hd⟩ :=
    hM.exists_inducesRegularOfDegree_of_card_le_modulus_of_modEq_degree_on hMq hdeg
  exact ⟨M, hk.ge, d, hd⟩

/--
No-split q-marker module branch.  If the surviving marker is a genuine graph module of size `q`
and the ambient degrees on the marker are congruent modulo `q`, then the marker itself is the
regular induced `q`-set promised by the q-marker audit.
-/
theorem hasRegularInducedSubgraphOfCard_modulus_of_card_eq_modulus_of_modEq_degree_on
    {q : ℕ} (hM : IsGraphModule G M) (hcard : M.card = q)
    (hdeg : ∀ ⦃v w : V⦄, v ∈ M → w ∈ M → G.degree v ≡ G.degree w [MOD q]) :
    HasRegularInducedSubgraphOfCard G q := by
  exact hM.hasRegularInducedSubgraphOfCard_of_card_eq_of_modEq_degree_on hcard le_rfl hdeg

/--
Global-degree version of the no-split q-marker module branch.
-/
theorem hasRegularInducedSubgraphOfCard_modulus_of_card_eq_modulus_of_modEq_degree
    {q : ℕ} (hM : IsGraphModule G M) (hcard : M.card = q)
    (hdeg : ∀ v w : V, G.degree v ≡ G.degree w [MOD q]) :
    HasRegularInducedSubgraphOfCard G q := by
  exact
    hM.hasRegularInducedSubgraphOfCard_modulus_of_card_eq_modulus_of_modEq_degree_on
      hcard (fun {v} {w} _ _ => hdeg v w)

end IsGraphModule

/-! ## §10 host-internal exactness criterion

This section formalises the host-internal equivalence of §10 of
`notes/remaining-gap-obstruction-module.md`: inside a `q`-modular induced subgraph on `S`, a
sub-finset `U ⊆ S` is *itself* `q`-modular iff the **complement degrees**
`|N(v) ∩ (S \ U)|` are constant modulo `q` on `U`.  When `U.card ≤ q` this collapses to the
"regular induced ↔ modular complement degree" criterion that powers the host-internal exactness
arm of the Modular `q² → q` Regular Selection program.
-/

/-- Auxiliary decomposition: for `U ⊆ S` and `v ∈ U`, the induced degree of `v` inside `G[S]`
splits as the induced degree of `v` inside `G[U]` plus the **complement degree**
`|N(v) ∩ (S \ U)|`. -/
private lemma degree_inducedOn_subset_decompose
    {G : SimpleGraph V} [DecidableRel G.Adj] {S U : Finset V} (hUS : U ⊆ S)
    {v : V} (hv : v ∈ U) :
    (inducedOn G S).degree ⟨v, hUS hv⟩ =
      (inducedOn G U).degree ⟨v, hv⟩ + (G.neighborFinset v ∩ (S \ U)).card := by
  classical
  have hSdecomp :
      G.neighborFinset v ∩ S =
        (G.neighborFinset v ∩ U) ∪ (G.neighborFinset v ∩ (S \ U)) := by
    rw [← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hUS]
  have hdisj :
      Disjoint (G.neighborFinset v ∩ U) (G.neighborFinset v ∩ (S \ U)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    rcases Finset.mem_inter.mp hx1 with ⟨_, hxU⟩
    rcases Finset.mem_inter.mp hx2 with ⟨_, hxSU⟩
    exact (Finset.mem_sdiff.mp hxSU).2 hxU
  have h1 :
      (inducedOn G S).degree ⟨v, hUS hv⟩ = (G.neighborFinset v ∩ S).card :=
    degree_inducedOn_eq_card_neighborFinset_inter_module (G := G) (s := S) ⟨v, hUS hv⟩
  have h2 :
      (inducedOn G U).degree ⟨v, hv⟩ = (G.neighborFinset v ∩ U).card :=
    degree_inducedOn_eq_card_neighborFinset_inter_module (G := G) (s := U) ⟨v, hv⟩
  rw [h1, h2, hSdecomp, Finset.card_union_of_disjoint hdisj]

/--
**Proposition 10.1** (host-internal exactness criterion;
`notes/remaining-gap-obstruction-module.md` §10).

Inside a `q`-modular induced subgraph on `S`, a subset `U ⊆ S` is itself `q`-modular iff the
**complement degrees** `|N(v) ∩ (S \ U)|` are constant modulo `q` on `U`.

This is the (2) ↔ (3) equivalence of §10: the global ambient `q`-modularity of `G[S]` translates
the modular regularity of `G[U]` directly into modular constancy of the host-internal complement
degrees, which is the formalisation target of the §10 host-internal exactness program.
-/
theorem inducesModEqDegree_iff_modEq_complementDegree_of_inducesModEqDegree_subset
    {G : SimpleGraph V} [DecidableRel G.Adj] {S U : Finset V} {q : ℕ}
    (hUS : U ⊆ S) (hS : InducesModEqDegree G S q) :
    InducesModEqDegree G U q ↔
      ∀ v w : ↑(U : Set V),
        (G.neighborFinset (v : V) ∩ (S \ U)).card ≡
          (G.neighborFinset (w : V) ∩ (S \ U)).card [MOD q] := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rw [InducesModEqDegree] at hS
  rw [InducesModEqDegree]
  refine ⟨?_, ?_⟩
  · -- `InducesModEqDegree G U q` ⇒ complement degrees are mod-`q` constant.
    intro hU v w
    have hSvw := hS ⟨(v : V), hUS v.2⟩ ⟨(w : V), hUS w.2⟩
    have hUvw := hU v w
    have h1 := degree_inducedOn_subset_decompose (G := G) hUS v.2
    have h2 := degree_inducedOn_subset_decompose (G := G) hUS w.2
    rw [h1, h2] at hSvw
    -- `(deg U v) + comp v ≡ (deg U w) + comp w` and `(deg U v) ≡ (deg U w)` ⇒ `comp v ≡ comp w`.
    exact Nat.ModEq.add_left_cancel hUvw hSvw
  · -- Complement degrees mod-`q` constant ⇒ `InducesModEqDegree G U q`.
    intro hExt v w
    have hSvw := hS ⟨(v : V), hUS v.2⟩ ⟨(w : V), hUS w.2⟩
    have hExtvw := hExt v w
    have h1 := degree_inducedOn_subset_decompose (G := G) hUS v.2
    have h2 := degree_inducedOn_subset_decompose (G := G) hUS w.2
    rw [h1, h2] at hSvw
    -- `(deg U v) + comp v ≡ (deg U w) + comp w` and `comp v ≡ comp w` ⇒ `(deg U v) ≡ (deg U w)`.
    exact Nat.ModEq.add_right_cancel hExtvw hSvw

/--
**Corollary 10.2** (host-internal regularity criterion).

Inside a `q`-modular induced subgraph on `S`, any subset `U ⊆ S` of cardinality at most `q`
admits a regular induced subgraph structure iff the **complement degrees**
`|N(v) ∩ (S \ U)|` are constant modulo `q` on `U`.

In the canonical application `S.card = q^2`, `U.card = q` this is exactly the host-internal
exactness criterion for a single-control `(U, S \ U)` witness: the condition `Ω_{S \ U}(U) = 0`
of §10 collapses to the existence of a regular induced subgraph on `U`.
-/
theorem exists_inducesRegularOfDegree_iff_modEq_complementDegree_of_card_le_modulus
    {G : SimpleGraph V} [DecidableRel G.Adj] {S U : Finset V} {q : ℕ}
    (hUS : U ⊆ S) (hUq : U.card ≤ q) (hS : InducesModEqDegree G S q) :
    (∃ d : ℕ, InducesRegularOfDegree G U d) ↔
      ∀ v w : ↑(U : Set V),
        (G.neighborFinset (v : V) ∩ (S \ U)).card ≡
          (G.neighborFinset (w : V) ∩ (S \ U)).card [MOD q] := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  refine ⟨?_, ?_⟩
  · rintro ⟨d, hd⟩
    refine
      (inducesModEqDegree_iff_modEq_complementDegree_of_inducesModEqDegree_subset
          (G := G) hUS hS).mp ?_
    -- A regular induced subgraph trivially has all induced degrees equal.
    rw [InducesModEqDegree]
    intro v w
    have hv : (inducedOn G U).degree v = d := hd v
    have hw : (inducedOn G U).degree w = d := hd w
    rw [hv, hw]
  · intro hExt
    exact
      inducesRegularOfDegree_of_card_le_modulus_of_inducesModEqDegree G hUq <|
        (inducesModEqDegree_iff_modEq_complementDegree_of_inducesModEqDegree_subset
            (G := G) hUS hS).mpr hExt

/-- Packaged version of Corollary 10.2: any subset `U ⊆ S` of size exactly `k ≤ q` whose
complement degrees are mod-`q` constant inside a `q`-modular host produces a
`HasRegularInducedSubgraphOfCard G k` witness. -/
theorem hasRegularInducedSubgraphOfCard_of_card_eq_of_modEq_complementDegree
    {G : SimpleGraph V} [DecidableRel G.Adj] {S U : Finset V} {k q : ℕ}
    (hUS : U ⊆ S) (hUk : U.card = k) (hkq : k ≤ q) (hS : InducesModEqDegree G S q)
    (hExt :
      ∀ v w : ↑(U : Set V),
        (G.neighborFinset (v : V) ∩ (S \ U)).card ≡
          (G.neighborFinset (w : V) ∩ (S \ U)).card [MOD q]) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  have hUq : U.card ≤ q := hUk ▸ hkq
  obtain ⟨d, hd⟩ :=
    (exists_inducesRegularOfDegree_iff_modEq_complementDegree_of_card_le_modulus
        hUS hUq hS).mpr hExt
  exact ⟨U, hUk.ge, d, hd⟩

/--
Terminal host exactness in the `proof.md` form.  If the terminal bucket `U` has size `q`, the host
`S` is fixed-modulus modulo `q`, and the dropped-tail/complement degrees are constant modulo `q` on
`U`, then `U` itself supplies a regular induced `q`-set.
-/
theorem hasRegularInducedSubgraphOfCard_modulus_of_terminal_complementDegree
    {G : SimpleGraph V} [DecidableRel G.Adj] {S U : Finset V} {q : ℕ}
    (hUS : U ⊆ S) (hUq : U.card = q) (hS : InducesModEqDegree G S q)
    (hExt :
      ∀ v w : ↑(U : Set V),
        (G.neighborFinset (v : V) ∩ (S \ U)).card ≡
          (G.neighborFinset (w : V) ∩ (S \ U)).card [MOD q]) :
    HasRegularInducedSubgraphOfCard G q := by
  exact hasRegularInducedSubgraphOfCard_of_card_eq_of_modEq_complementDegree
    hUS hUq le_rfl hS hExt

end RegularInducedSubgraph
