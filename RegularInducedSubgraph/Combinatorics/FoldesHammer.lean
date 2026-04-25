import RegularInducedSubgraph.Combinatorics.SplitGraph

/-!
# The Földes-Hammer interface

This file records the proved Lean-facing half of the classical split-graph characterization:

* a split graph contains no induced `2K₂`, `C₄`, or `C₅`.

The hard Földes-Hammer converse is not formalized here.  In particular, this file exposes no
trusted converse theorem.
-/

namespace RegularInducedSubgraph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Proved Földes-Hammer easy direction: split graphs avoid the three forbidden induced subgraphs. -/
theorem forbidden_of_isSplitGraph (hG : G.IsSplitGraph) :
    G.IsInducedCopyFree twoK₂ ∧
      G.IsInducedCopyFree cycleFour ∧
        G.IsInducedCopyFree cycleFive :=
  IsSplitGraph.no_induced_forbidden hG

end RegularInducedSubgraph
