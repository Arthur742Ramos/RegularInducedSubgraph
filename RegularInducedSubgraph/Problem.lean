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

/--
Finite base case used by the q = 4 shortcut.

The script

`python search_structured_q4.py --min-n 7 --max-n 7 --progress-step 500000`

exhaustively checks all `2^21` labelled graphs on `7` vertices and reports that
`regular-induced-4-free graphs: 0`, so every graph on `7` vertices contains a regular induced
subgraph on at least `4` vertices.  The lemmas below give a formal Lean reduction from this
semantic statement to a small labelled-edge Boolean certificate.  The full checked certificate lives
in `RegularInducedSubgraph.SevenVertexCertificate`, where it is isolated from these lightweight
definitions because the table proof is large.
-/
def SevenVertexFourRegularBaseCase : Prop :=
  4 ∈ admissibleBounds 7

/-- The `21` unordered edges of the complete graph on seven labelled vertices. -/
abbrev SevenVertexEdge := ((⊤ : SimpleGraph (Fin 7)).edgeSet)

/-- A Boolean-labelled graph on seven vertices, encoded by its unordered edge labels. -/
abbrev SevenVertexEdgeCode := SevenVertexEdge → Bool

def sevenVertexEdgeOfNe {v w : Fin 7} (h : v ≠ w) : SevenVertexEdge := by
  refine ⟨s(v, w), ?_⟩
  change (⊤ : SimpleGraph (Fin 7)).Adj v w
  simpa using h

/-- Adjacency decoded from a seven-vertex edge code. -/
def sevenVertexCodeAdj (x : SevenVertexEdgeCode) (v w : Fin 7) : Bool :=
  if h : v = w then false else x (sevenVertexEdgeOfNe h)

/-- Internal degree inside a finite vertex set, computed from an edge code. -/
def sevenVertexCodeDegree (x : SevenVertexEdgeCode) (s : Finset (Fin 7)) (v : Fin 7) : ℕ :=
  (s.filter fun w => sevenVertexCodeAdj x v w).card

/--
The executable seven-vertex version of `HasRegularInducedSubgraphOfCard`.

The regularity degree is stored as `Fin (s.card + 1)` because every decoded internal degree is at
most `s.card`; this keeps the finite search space small for external `native_decide` certificates.
-/
def SevenVertexCodeHasRegularInducedSubgraphOfCard (x : SevenVertexEdgeCode) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin 7), k ≤ s.card ∧
    ∃ d : Fin (s.card + 1), ∀ v ∈ s, sevenVertexCodeDegree x s v = d.1

instance sevenVertexCodeHasRegularDecidable (x : SevenVertexEdgeCode) (k : ℕ) :
    Decidable (SevenVertexCodeHasRegularInducedSubgraphOfCard x k) := by
  unfold SevenVertexCodeHasRegularInducedSubgraphOfCard sevenVertexCodeDegree
    sevenVertexCodeAdj
  infer_instance

def sevenVertexGraphCode (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] :
    SevenVertexEdgeCode :=
  fun e => decide (e.1 ∈ G.edgeSet)

lemma sevenVertexCodeAdj_graphCode (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (v w : Fin 7) :
    sevenVertexCodeAdj (sevenVertexGraphCode G) v w = decide (G.Adj v w) := by
  unfold sevenVertexCodeAdj sevenVertexGraphCode
  by_cases h : v = w
  · subst w
    simp
  · simp [h]
    convert (SimpleGraph.mem_edgeSet (G := G) (v := v) (w := w)) using 1

private lemma degree_inducedOn_eq_sevenVertexCodeDegree_graphCode
    (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (s : Finset (Fin 7))
    (v : ↑(s : Set (Fin 7))) :
    (inducedOn G s).degree v = sevenVertexCodeDegree (sevenVertexGraphCode G) s v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (fun x => x ∈ (s : Set (Fin 7)))) =
        s.filter (fun w => sevenVertexCodeAdj (sevenVertexGraphCode G) v w) := by
    ext x
    simp [inducedOn, sevenVertexCodeAdj_graphCode, and_comm]
  calc
    ((inducedOn G s).neighborFinset v).card =
        (((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (fun x => x ∈ (s : Set (Fin 7))))).card := by
            rw [Finset.card_map]
    _ = (s.filter fun w => sevenVertexCodeAdj (sevenVertexGraphCode G) v w).card := by
          rw [hmap]
    _ = sevenVertexCodeDegree (sevenVertexGraphCode G) s v := rfl

/--
Soundness of the labelled-edge certificate route: a proof of the executable certificate for every
edge labelling yields the semantic seven-vertex base case.
-/
theorem sevenVertexFourRegularBaseCase_of_codeCertificate
    (hcode : ∀ x : SevenVertexEdgeCode,
      SevenVertexCodeHasRegularInducedSubgraphOfCard x 4) :
    SevenVertexFourRegularBaseCase := by
  intro G
  classical
  rcases hcode (sevenVertexGraphCode G) with ⟨s, hks, d, hd⟩
  refine ⟨s, hks, d.1, ?_⟩
  rw [InducesRegularOfDegree]
  intro v
  rw [degree_inducedOn_eq_sevenVertexCodeDegree_graphCode]
  exact hd v v.2

private def sevenVertexBit (m i : ℕ) : Bool :=
  decide ((m / 2 ^ i) % 2 = 1)

/-- The vertex set encoded by a seven-bit mask. -/
def sevenVertexFinsetOfMask (m : Fin 128) : Finset (Fin 7) :=
  (Finset.univ : Finset (Fin 7)).filter fun v => sevenVertexBit m.1 v.1

lemma sevenVertexCodeDegree_le_card
    (x : SevenVertexEdgeCode) (s : Finset (Fin 7)) (v : Fin 7) :
    sevenVertexCodeDegree x s v ≤ s.card := by
  unfold sevenVertexCodeDegree
  exact Finset.card_filter_le _ _

/-- Boolean regularity test for a decoded set of vertices. -/
def sevenVertexCodeRegular (x : SevenVertexEdgeCode) (s : Finset (Fin 7)) : Bool :=
  (List.finRange 7).all fun v =>
    (List.finRange 7).all fun w =>
      decide (v ∈ s → w ∈ s →
        sevenVertexCodeDegree x s v = sevenVertexCodeDegree x s w)

lemma sevenVertexCodeRegular_sound {x : SevenVertexEdgeCode} {s : Finset (Fin 7)}
    (hreg : sevenVertexCodeRegular x s = true) :
    ∃ d : Fin (s.card + 1), ∀ v ∈ s, sevenVertexCodeDegree x s v = d.1 := by
  by_cases hs : s.Nonempty
  · rcases hs with ⟨v₀, hv₀⟩
    refine ⟨⟨sevenVertexCodeDegree x s v₀,
      Nat.lt_succ_of_le (sevenVertexCodeDegree_le_card x s v₀)⟩, ?_⟩
    intro v hv
    have hforall : ∀ v w : Fin 7,
        v ∉ s ∨ w ∉ s ∨
          sevenVertexCodeDegree x s v = sevenVertexCodeDegree x s w := by
      simpa [sevenVertexCodeRegular, List.all_iff_forall_prop] using hreg
    rcases hforall v v₀ with hvnot | hv₀not | heq
    · exact False.elim (hvnot hv)
    · exact False.elim (hv₀not hv₀)
    · exact heq
  · refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
    intro v hv
    exact False.elim (hs ⟨v, hv⟩)

/--
A compact Boolean checker for the remaining finite certificate.  It searches the `128` vertex
masks and accepts a regular induced set of size exactly `4` or `5` (the exhaustive search shows the
`5`-vertex alternative is enough when no `4`-vertex regular set exists).
-/
def sevenVertexCodeHasRegularFourOrFiveBool (x : SevenVertexEdgeCode) : Bool :=
  (List.finRange 128).any fun m =>
    let s := sevenVertexFinsetOfMask m
    let c := s.card
    decide (c = 4 ∨ c = 5) && sevenVertexCodeRegular x s

lemma sevenVertexCodeHasRegularFourOrFiveBool_sound {x : SevenVertexEdgeCode}
    (h : sevenVertexCodeHasRegularFourOrFiveBool x = true) :
    SevenVertexCodeHasRegularInducedSubgraphOfCard x 4 := by
  unfold sevenVertexCodeHasRegularFourOrFiveBool at h
  rw [List.any_eq_true] at h
  rcases h with ⟨m, _hm, hm⟩
  let s := sevenVertexFinsetOfMask m
  have hcard : 4 ≤ s.card := by
    have hm' := hm
    simp at hm'
    have hsize : s.card = 4 ∨ s.card = 5 := hm'.1
    omega
  have hreg : sevenVertexCodeRegular x s = true := by
    have hm' := hm
    simp at hm'
    exact hm'.2
  exact ⟨s, hcard, sevenVertexCodeRegular_sound hreg⟩

/--
Soundness of the compact Boolean finite-search route.  Proving the Boolean premise by an external
or build-isolated `native_decide` certificate is enough to discharge
`SevenVertexFourRegularBaseCase`.
-/
theorem sevenVertexFourRegularBaseCase_of_boolCertificate
    (hcert : ∀ x : SevenVertexEdgeCode,
      sevenVertexCodeHasRegularFourOrFiveBool x = true) :
    SevenVertexFourRegularBaseCase :=
  sevenVertexFourRegularBaseCase_of_codeCertificate fun x =>
    sevenVertexCodeHasRegularFourOrFiveBool_sound (hcert x)

theorem four_le_F_seven (hbase : SevenVertexFourRegularBaseCase) : 4 ≤ F 7 := by
  exact le_F_iff.mpr hbase

theorem four_le_F_of_seven_le (hbase : SevenVertexFourRegularBaseCase)
    {n : ℕ} (hn : 7 ≤ n) : 4 ≤ F n := by
  exact le_trans (four_le_F_seven hbase) (F_monotone hn)

lemma hasRegularInducedSubgraphOfCard_of_le_F_fintypeCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ}
    (hk : k ≤ F (Fintype.card V)) :
    HasRegularInducedSubgraphOfCard G k := by
  classical
  let H : SimpleGraph (Fin (Fintype.card V)) :=
    G.comap (Fintype.equivFin V).symm.toEmbedding
  exact
    hasRegularInducedSubgraphOfCard_of_embedding
      (SimpleGraph.Embedding.comap (Fintype.equivFin V).symm.toEmbedding G)
      ((le_F_iff.mp hk) H)

lemma hasRegularInducedSubgraphOfCard_of_card_eq_and_le_F
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n k : ℕ}
    (hcard : Fintype.card V = n) (hk : k ≤ F n) :
    HasRegularInducedSubgraphOfCard G k := by
  have hk' : k ≤ F (Fintype.card V) := by
    simpa [hcard] using hk
  exact hasRegularInducedSubgraphOfCard_of_le_F_fintypeCard G hk'

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
