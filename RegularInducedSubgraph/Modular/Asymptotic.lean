import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt
import RegularInducedSubgraph.Modular.Cascade
import RegularInducedSubgraph.Modular.Frontier

open Filter

namespace RegularInducedSubgraph

section Threshold

/--
Discrete modular form of the power-sequence target: on the subsequence `b^k`, every linear-size
target `M * k` should eventually admit a modular witness.
-/
def EventualNatPowerModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasModularWitnessOfCard G (M * k)

/--
Stronger exact control-block target: on the subsequence `b^k`, every linear-size demand eventually
admits a nonempty exact control-block witness.
-/
def EventualNatPowerExactControlBlockDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasExactControlBlockWitnessOfCard G (M * k)

/--
Bounded exact control-block target: the same nonempty exact witness exists using at most `r`
control blocks.
-/
def EventualNatPowerBoundedExactControlBlockDomination (b r : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedExactControlBlockWitnessOfCard G (M * k) r

/--
Single-control exact target: on graphs with `b^k` vertices, every linear-size demand eventually
admits one nonempty control set that freezes both ambient and external degrees.
-/
def EventualNatPowerSingleControlExactDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlExactWitnessOfCard G (M * k)

/--
Single-control exact target with an explicit control-size budget `u k` at scale `k`.
-/
def EventualNatPowerBoundedSingleControlExactDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlExactWitnessOfCard G (M * k) (u k)

/--
Single-control modular target: on graphs with `b^k` vertices, every linear-size demand eventually
admits one nonempty control set that freezes both ambient and external degrees modulo a modulus at
least the bucket size.
-/
def EventualNatPowerSingleControlModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlModularWitnessOfCard G (M * k)

/--
Single-control modular target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlModularDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlModularWitnessOfCard G (M * k) (u k)

/--
Single-control modular bucketing target: a large bucket survives inside a host set while the ambient
degree and both relevant external residues are frozen modulo a modulus at least the bucket size.
-/
def EventualNatPowerSingleControlModularBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlModularBucketingWitnessOfCard G (M * k)

/--
Single-control modular bucketing target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlModularBucketingDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedSingleControlModularBucketingWitnessOfCard G (M * k) (u k)

/--
Single-control bucketing target: a large bucket survives inside a host set while the host ambient
degree and both relevant external degrees are frozen.
-/
def EventualNatPowerSingleControlBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlBucketingWitnessOfCard G (M * k)

/--
Single-control bucketing target with an explicit control-size budget `u k`.
-/
def EventualNatPowerBoundedSingleControlBucketingDomination (b : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlBucketingWitnessOfCard G (M * k) (u k)

/--
Multiblock bucketing target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a large bucket together with a nonempty separated control-block family whose ambient and
external degree data are frozen on that bucket.
-/
def EventualNatPowerControlBlockBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockBucketingWitnessOfCard G (M * k)

/--
Bounded multiblock bucketing target: the final exact control-block witness extracted from the
bucketing data uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockBucketingDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedControlBlockBucketingWitnessOfCard G (M * k) (r k)

/--
Multiblock modular bucketing target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a large bucket together with a nonempty separated control-block family whose
ambient degree, dropped-part residue, and control-block residues are all frozen modulo a modulus at
least the bucket size.
-/
def EventualNatPowerControlBlockModularBucketingDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockModularBucketingWitnessOfCard G (M * k)

/--
Bounded multiblock modular bucketing target: the modular bucketing data uses at most `r k`
control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockModularBucketingDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedControlBlockModularBucketingWitnessOfCard G (M * k) (r k)

/--
Single-control cascade target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a fixed-control cascade whose terminal bucket has the required size.
-/
def EventualNatPowerSingleControlCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasSingleControlCascadeWitnessOfCard G (M * k)

/--
Bounded single-control cascade target: the final exact control-block witness extracted from the
cascade uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedSingleControlCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedSingleControlCascadeWitnessOfCard G (M * k) (r k)

/--
Multiblock cascade target: on graphs with `b^k` vertices, every linear-size demand eventually
admits a fixed separated control-block family together with a cascade whose terminal bucket has the
required size.
-/
def EventualNatPowerControlBlockCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockCascadeWitnessOfCard G (M * k)

/--
Bounded multiblock cascade target: the final exact control-block witness extracted from the cascade
uses at most `r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedControlBlockCascadeWitnessOfCard G (M * k) (r k)

/--
Modular multiblock cascade target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a fixed-modulus separated control-block cascade whose terminal bucket already fits
under that modulus.
-/
def EventualNatPowerControlBlockModularCascadeDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockModularCascadeWitnessOfCard G (M * k)

/--
Bounded modular multiblock cascade target: after all drops are packaged, the cascade uses at most
`r k` control blocks at scale `k`.
-/
def EventualNatPowerBoundedControlBlockModularCascadeDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasBoundedControlBlockModularCascadeWitnessOfCard G (M * k) (r k)

/--
Sharper power-sequence target: on the subsequence `b^k`, every linear-size demand eventually admits
a modular witness whose modulus already beats the maximum induced degree.
-/
def EventualNatPowerLowDegreeModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasLowDegreeModularWitnessOfCard G (M * k)

/--
Power-sequence control-block target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a control-block witness.
-/
def EventualNatPowerControlBlockDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasControlBlockWitnessOfCard G (M * k)

/--
Power-sequence genuine control-block target: on graphs with `b^k` vertices, every linear-size demand
eventually admits a modular control-block witness with a genuinely present separated control-block
family.
-/
def EventualNatPowerNonemptyControlBlockModularDomination (b : ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)), HasNonemptyControlBlockModularWitnessOfCard G (M * k)

/--
Bounded genuine control-block target with an explicit control-block budget `r k`.
-/
def EventualNatPowerBoundedNonemptyControlBlockModularDomination (b : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k →
    ∀ G : SimpleGraph (Fin (b ^ k)),
      HasBoundedNonemptyControlBlockModularWitnessOfCard G (M * k) (r k)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerExactControlBlockDomination
    {b r : ℕ}
    (hctrl : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerBoundedExactControlBlockDomination
    {b r : ℕ} (hr : 0 < r)
    (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerBoundedExactControlBlockDomination b r := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedExactControlBlockWitnessOfCard_of_hasSingleControlExactWitnessOfCard G hr
    (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ}
    (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ}
    (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
    (eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerControlBlockBucketingDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ}
    (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerControlBlockBucketingDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockBucketingDomination

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerControlBlockBucketingDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockBucketingWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} :
    EventualNatPowerControlBlockBucketingDomination b ↔
      EventualNatPowerControlBlockCascadeDomination b := by
  constructor
  · exact eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockCascadeDomination
  · exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockBucketingDomination

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerBoundedControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockModularCascadeDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockModularCascadeDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockModularCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularCascadeWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerControlBlockModularCascadeDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularCascadeWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedControlBlockModularCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockModularCascadeDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularCascadeWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerControlBlockModularBucketingDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  constructor
  · exact eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
  · exact eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination

theorem eventualNatPowerControlBlockDomination_implies_eventualNatPowerModularDomination {b : ℕ}
    (hctrl : EventualNatPowerControlBlockDomination b) :
    EventualNatPowerModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasModularWitnessOfCard_of_hasControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerControlBlockDomination b) : TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hctrl M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasControlBlockWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerExactControlBlockDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hexact : EventualNatPowerExactControlBlockDomination b) : TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockDomination
      hexact)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_targetStatement
    {b r : ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerBoundedExactControlBlockDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerExactControlBlockDomination
      hctrl)

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasSingleControlCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  have := hK hk G
  exact hasExactControlBlockWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hasBoundedExactControlBlockWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard G this)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerBoundedControlBlockBucketingDomination_succ
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockBucketingDomination b (fun k => r k + 1) := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockBucketingWitnessOfCard_of_hasBoundedControlBlockCascadeWitnessOfCard_succ
    G
    (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    EventualNatPowerExactControlBlockDomination b := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasExactControlBlockWitnessOfCard_of_hasControlBlockCascadeWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) :
    EventualNatPowerExactControlBlockDomination b := by
  exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
    (eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
      hcascade)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockCascadeWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerControlBlockCascadeDomination_iff_eventualNatPowerExactControlBlockDomination
    {b : ℕ} :
    EventualNatPowerControlBlockCascadeDomination b ↔
      EventualNatPowerExactControlBlockDomination b := by
  constructor
  · exact eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
  · exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerControlBlockBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerControlBlockBucketingDomination b := by
  rw [eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination,
    eventualNatPowerControlBlockBucketingDomination_iff_eventualNatPowerExactControlBlockDomination]

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerControlBlockCascadeDomination b := by
  rw [eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerExactControlBlockDomination,
    eventualNatPowerControlBlockCascadeDomination_iff_eventualNatPowerExactControlBlockDomination]

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerControlBlockCascadeDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerControlBlockCascadeDomination b := by
  exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockCascadeDomination
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerBoundedControlBlockCascadeDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) :
    EventualNatPowerBoundedControlBlockCascadeDomination b r := by
  intro M
  rcases hcascade M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockCascadeWitnessOfCard_of_hasBoundedSingleControlCascadeWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedSingleControlCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerControlBlockCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerControlBlockCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedControlBlockCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasControlBlockBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedControlBlockBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hexact : EventualNatPowerExactControlBlockDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasExactControlBlockWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ}
    (hexact : EventualNatPowerBoundedExactControlBlockDomination b r) :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b (fun _ => r) := by
  intro M
  rcases hexact M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedExactControlBlockWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b r := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedNonemptyControlBlockModularWitnessOfCard_of_hasBoundedControlBlockModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerControlBlockModularBucketingDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockModularBucketingWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ}
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) :
    EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedControlBlockModularBucketingWitnessOfCard_of_hasBoundedNonemptyControlBlockModularWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerNonemptyControlBlockModularDomination b ↔
      EventualNatPowerControlBlockModularBucketingDomination b := by
  constructor
  · exact eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
  · exact eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination

theorem eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerNonemptyControlBlockModularDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  rw [eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination,
    eventualNatPowerControlBlockModularBucketingDomination_iff_eventualNatPowerControlBlockModularCascadeDomination]

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_iff_eventualNatPowerBoundedControlBlockModularBucketingDomination
    {b : ℕ} {r : ℕ → ℕ} :
    EventualNatPowerBoundedNonemptyControlBlockModularDomination b r ↔
      EventualNatPowerBoundedControlBlockModularBucketingDomination b r := by
  constructor
  · exact eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerBoundedControlBlockModularBucketingDomination
  · exact eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerBoundedNonemptyControlBlockModularDomination

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerModularDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hmod : EventualNatPowerModularDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hmod M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockDomination_iff_eventualNatPowerModularDomination
    {b : ℕ} :
    EventualNatPowerControlBlockDomination b ↔ EventualNatPowerModularDomination b := by
  constructor
  · exact eventualNatPowerControlBlockDomination_implies_eventualNatPowerModularDomination
  · exact eventualNatPowerModularDomination_implies_eventualNatPowerControlBlockDomination

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockDomination
    {b : ℕ} (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    EventualNatPowerControlBlockDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasControlBlockWitnessOfCard_of_hasControlBlockModularBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerControlBlockModularBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedControlBlockModularBucketingDomination b r) : TargetStatement := by
  exact eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockModularBucketingDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
      hbuck)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerControlBlockDomination
      hctrl)

theorem eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hctrl : EventualNatPowerBoundedNonemptyControlBlockModularDomination b r) : TargetStatement := by
  exact eventualNatPowerNonemptyControlBlockModularDomination_implies_targetStatement hb
    (eventualNatPowerBoundedNonemptyControlBlockModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
      hctrl)

theorem eventualNatPowerControlBlockModularCascadeDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hcascade : EventualNatPowerControlBlockModularCascadeDomination b) :
    TargetStatement := by
  exact eventualNatPowerControlBlockModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularBucketingDomination
      hcascade)

theorem eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hcascade : EventualNatPowerBoundedControlBlockModularCascadeDomination b r) : TargetStatement := by
  exact eventualNatPowerControlBlockModularCascadeDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockModularCascadeDomination_implies_eventualNatPowerControlBlockModularCascadeDomination
      hcascade)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  rw [le_F_iff]
  intro G
  exact hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerDomination b := by
  exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerDomination
    (eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
      hsingle)

theorem eventualNatPowerBoundedSingleControlExactDomination_mono_budget
    {b : ℕ} {u v : ℕ → ℕ}
    (huv : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k ≤ v k)
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerBoundedSingleControlExactDomination b v := by
  intro M
  rcases huv with ⟨K1, hK1⟩
  rcases hsingle M with ⟨K2, hK2⟩
  refine ⟨max K1 K2, ?_⟩
  intro k hk G
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_max_right _ _) hk
  rcases hK2 hk2 G with ⟨s, t, hks, ht, htu, hst, D, e, hdeg, hext⟩
  exact ⟨s, t, hks, ht, le_trans htu (hK1 hk1), hst, D, e, hdeg, hext⟩

theorem
    eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_one_lt
    {b : ℕ} (hb : 1 < b) (hpow : EventualNatPowerDomination b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) := by
  intro M
  rcases hpow (M + 1) with ⟨K, hK⟩
  refine ⟨max (K + 1) (M + 1), ?_⟩
  intro k hk G
  classical
  have hb0 : 0 < b := Nat.zero_lt_of_lt hb
  have hkK1 : K + 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkM1 : M + 1 ≤ k := le_trans (le_max_right _ _) hk
  have hk1 : 1 ≤ k := by
    exact le_trans (Nat.succ_le_succ (Nat.zero_le K)) hkK1
  let v : Fin (b ^ k) := ⟨0, pow_pos hb0 _⟩
  let s : Finset (Fin (b ^ k)) := Finset.univ.erase v
  let t : Finset (Fin (b ^ k)) := {v}
  have hsCard : s.card = b ^ k - 1 := by
    simp [s, v]
  have hsize' : 2 * (b ^ (k - 1) - 1) < b ^ k - 1 := by
    have h2b : 2 ≤ b := Nat.succ_le_of_lt hb
    have hpowpos : 0 < b ^ (k - 1) := pow_pos hb0 _
    have hmul : 2 * b ^ (k - 1) ≤ b * b ^ (k - 1) := by
      exact Nat.mul_le_mul_right (b ^ (k - 1)) h2b
    have hpow : b ^ k = b * b ^ (k - 1) := by
      rw [← pow_succ']
      simpa [Nat.sub_add_cancel hk1]
    rw [hpow]
    omega
  have hsize : (t.card + 1) * (b ^ (k - 1) - 1) < s.card := by
    simpa [t, hsCard] using hsize'
  have ht : 0 < t.card := by
    simp [t]
  have htr : t.card ≤ 1 := by
    simp [t]
  have hst : Disjoint s t := by
    simp [s, t]
  have hkprev : K ≤ k - 1 := by
    omega
  have hneed : M * k ≤ F (b ^ (k - 1)) := by
    have hkM : M ≤ k - 1 := by
      omega
    have hshift : M * k ≤ (M + 1) * (k - 1) := by
      calc
        M * k = M * ((k - 1) + 1) := by
          rw [Nat.sub_add_cancel hk1]
        _ = M * (k - 1) + M := by
          rw [Nat.mul_add, Nat.mul_one]
        _ ≤ M * (k - 1) + (k - 1) := by
          gcongr
        _ = (M + 1) * (k - 1) := by
          rw [Nat.add_mul, Nat.one_mul]
    exact le_trans hshift (hK hkprev)
  refine
    hasBoundedSingleControlExactWitnessOfCard_of_large_constant_externalDegree_and_recursive_strict
      (G := G) (s := s) (t := t) (n := b ^ (k - 1)) (k := M * k) (r := 1)
      hsize ht htr hst ?_
  intro u _hu hcardu
  exact
    hasRegularInducedSubgraphOfCard_of_card_eq_and_le_F
      (G := inducedOn G u)
      (n := b ^ (k - 1))
      (by simpa [hcardu] using (Fintype.card_coe u))
      hneed

theorem
    eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_two_lt
    {b : ℕ} (hb : 2 < b) (hpow : EventualNatPowerDomination b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) := by
  exact
    eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_one_lt
      (lt_trans (by decide : 1 < 2) hb) hpow

theorem eventualNatPowerBoundedSingleControlExactDomination_one_iff_eventualNatPowerDomination_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) ↔
      EventualNatPowerDomination b := by
  constructor
  · exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerDomination
  · exact eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_one_lt hb

theorem eventualNatPowerBoundedSingleControlExactDomination_one_iff_eventualNatPowerDomination_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) ↔
      EventualNatPowerDomination b := by
  exact
    eventualNatPowerBoundedSingleControlExactDomination_one_iff_eventualNatPowerDomination_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem
    eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k)
    (hpow : EventualNatPowerDomination b) :
    EventualNatPowerBoundedSingleControlExactDomination b u := by
  have hone :
      EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) :=
    eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_one_lt
      hb hpow
  apply
    eventualNatPowerBoundedSingleControlExactDomination_mono_budget (u := fun _ => 1) (v := u)
  · rcases hpos with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    simpa using Nat.succ_le_of_lt (hK hk)
  · exact hone

theorem eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerDomination_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlExactDomination b u ↔ EventualNatPowerDomination b := by
  constructor
  · exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerDomination
  · exact
      eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_pos
        hb hpos

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerSingleControlExactDomination b ↔ EventualNatPowerDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerDomination
  · intro hpow
    exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
      (eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_one_of_one_lt
        hb hpow)

theorem eventualNatPowerDomination_implies_eventualNatPowerBoundedExactControlBlockDomination_of_one_lt
    {b r : ℕ} (hb : 1 < b) (hr : 0 < r) (hpow : EventualNatPowerDomination b) :
    EventualNatPowerBoundedExactControlBlockDomination b r := by
  exact
    eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerBoundedExactControlBlockDomination
      hr
      ((eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_one_lt hb).2
        hpow)

theorem eventualNatPowerBoundedExactControlBlockDomination_iff_eventualNatPowerDomination_of_one_lt
    {b r : ℕ} (hb : 1 < b) (hr : 0 < r) :
    EventualNatPowerBoundedExactControlBlockDomination b r ↔
      EventualNatPowerDomination b := by
  constructor
  · intro hctrl
    exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerDomination
      (eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination
        (eventualNatPowerBoundedExactControlBlockDomination_implies_eventualNatPowerExactControlBlockDomination
          hctrl))
  · exact
      eventualNatPowerDomination_implies_eventualNatPowerBoundedExactControlBlockDomination_of_one_lt
        hb hr

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerSingleControlExactDomination b ↔ EventualNatPowerDomination b := by
  exact
    eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) ↔ TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlExactDomination_one_iff_eventualNatPowerDomination_of_one_lt
      hb,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerBoundedSingleControlExactDomination b (fun _ => 1) ↔ TargetStatement := by
  exact
    eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem eventualNatPowerBoundedSingleControlExactDomination_iff_targetStatement_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlExactDomination b u ↔ TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerDomination_of_eventually_pos
      hb hpos,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerBoundedExactControlBlockDomination_iff_targetStatement_of_one_lt
    {b r : ℕ} (hb : 1 < b) (hr : 0 < r) :
    EventualNatPowerBoundedExactControlBlockDomination b r ↔ TargetStatement := by
  rw [eventualNatPowerBoundedExactControlBlockDomination_iff_eventualNatPowerDomination_of_one_lt
      hb hr,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerSingleControlExactDomination_iff_targetStatement_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerSingleControlExactDomination b ↔ TargetStatement := by
  rw [eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerDomination_of_one_lt hb,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerSingleControlExactDomination_iff_targetStatement_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerSingleControlExactDomination b ↔ TargetStatement := by
  exact
    eventualNatPowerSingleControlExactDomination_iff_targetStatement_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem eventualNatPowerBoundedSingleControlExactDomination_one_two_iff_targetStatement :
    EventualNatPowerBoundedSingleControlExactDomination 2 (fun _ => 1) ↔ TargetStatement := by
  simpa using
    eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt
      (b := 2) (by decide : 1 < 2)

theorem eventualNatPowerSingleControlExactDomination_two_iff_targetStatement :
    EventualNatPowerSingleControlExactDomination 2 ↔ TargetStatement := by
  simpa using
    eventualNatPowerSingleControlExactDomination_iff_targetStatement_of_one_lt
      (b := 2) (by decide : 1 < 2)

theorem eventualNatPowerBoundedSingleControlExactDomination_one_four_iff_targetStatement :
    EventualNatPowerBoundedSingleControlExactDomination 4 (fun _ => 1) ↔ TargetStatement := by
  simpa using
    eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt
      (b := 4) (by decide : 1 < 4)

theorem eventualNatPowerSingleControlExactDomination_four_iff_targetStatement :
    EventualNatPowerSingleControlExactDomination 4 ↔ TargetStatement := by
  simpa using eventualNatPowerSingleControlExactDomination_iff_targetStatement_of_one_lt
    (b := 4) (by decide : 1 < 4)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) :
    EventualNatPowerBoundedSingleControlModularDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem
    eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u)
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlExactDomination b u := by
  intro M
  rcases hsingle (M + 1) with ⟨K1, hK1⟩
  rcases hsmall M with ⟨K2, hK2⟩
  refine ⟨max K1 K2, ?_⟩
  intro k hk G
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_max_right _ _) hk
  have hbig :
      HasBoundedSingleControlExactWitnessOfCard G ((M + 1) * k) (u k) := by
    exact
      hasBoundedSingleControlExactWitnessOfCard_of_lt_of_hasBoundedSingleControlModularWitnessOfCard
        G (hK2 hk2) (hK1 hk1 G)
  exact hasBoundedSingleControlExactWitnessOfCard_mono G
    (Nat.mul_le_mul_right k (Nat.le_succ M)) hbig

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlModularBucketingDomination b u)
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlExactDomination b u := by
  apply
    eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
  · intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard G
      (hK hk G)
  · exact hsmall

theorem
    eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔
      EventualNatPowerBoundedSingleControlExactDomination b u := by
  constructor
  · intro hmod
    exact
      eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
        hmod hsmall
  · exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlModularDomination

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u ↔
      EventualNatPowerBoundedSingleControlExactDomination b u := by
  constructor
  · intro hbuck
    exact
      eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
        hbuck hsmall
  · intro hsingle
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard G
      (hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
        (hK hk G))

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerNonemptyControlBlockModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasNonemptyControlBlockModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hctrl : EventualNatPowerNonemptyControlBlockModularDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hctrl M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasNonemptyControlBlockModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerNonemptyControlBlockModularDomination b := by
  constructor
  · exact eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerNonemptyControlBlockModularDomination
  · exact eventualNatPowerNonemptyControlBlockModularDomination_implies_eventualNatPowerSingleControlModularDomination

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerControlBlockModularBucketingDomination b := by
  rw [eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination,
    eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularBucketingDomination]

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerControlBlockModularCascadeDomination b := by
  rw [eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerNonemptyControlBlockModularDomination,
    eventualNatPowerNonemptyControlBlockModularDomination_iff_eventualNatPowerControlBlockModularCascadeDomination]

theorem eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlModularBucketingDomination b u) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlModularWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ} :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔
      EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  constructor
  · exact eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
  · intro hbuck
    intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard G
      (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_iff_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlModularDomination b ↔
      EventualNatPowerSingleControlModularBucketingDomination b := by
  constructor
  · exact eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
  · intro hbuck
    intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G
      (hK hk G)

theorem eventualNatPowerSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlModularBucketingDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlModularBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlModularDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlModularBucketingDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlModularBucketingWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlExactWitnessOfCard_of_hasSingleControlBucketingWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlBucketingDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlBucketingWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlExactDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlExactWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard G
    (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerSingleControlBucketingDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerSingleControlBucketingDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
  · exact eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination
    {b : ℕ} {u : ℕ → ℕ} :
    EventualNatPowerBoundedSingleControlExactDomination b u ↔
      EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  constructor
  · exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlBucketingDomination
  · exact eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination

theorem
    eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔
      EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  rw [eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
      hsmall,
    eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination]

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination_of_eventually_lt
    {b : ℕ} {u : ℕ → ℕ}
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → u k < (M + 1) * k) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u ↔
      EventualNatPowerBoundedSingleControlBucketingDomination b u := by
  rw [eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
      hsmall,
    eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination]

private theorem singletonControlBudget_eventually_lt :
    ∀ M : ℕ, ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → (1 : ℕ) < (M + 1) * k := by
  intro M
  refine ⟨2, ?_⟩
  intro k hk
  have h2 : 2 ≤ (M + 1) * k := by
    calc
      2 ≤ k := hk
      _ ≤ (M + 1) * k := by
        simpa [one_mul] using Nat.mul_le_mul_right k (Nat.succ_le_succ (Nat.zero_le M))
  exact lt_of_lt_of_le (by decide : 1 < 2) h2

theorem eventualNatPowerBoundedSingleControlBucketingDomination_one_iff_targetStatement_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerBoundedSingleControlBucketingDomination b (fun _ => 1) ↔
      TargetStatement := by
  rw [← eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination]
  exact eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_two_lt hb

theorem eventualNatPowerBoundedSingleControlBucketingDomination_one_iff_targetStatement_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerBoundedSingleControlBucketingDomination b (fun _ => 1) ↔
      TargetStatement := by
  rw [← eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination]
  exact eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt hb

theorem eventualNatPowerBoundedSingleControlModularDomination_one_iff_targetStatement_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerBoundedSingleControlModularDomination b (fun _ => 1) ↔ TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
      singletonControlBudget_eventually_lt]
  exact eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt hb

theorem eventualNatPowerBoundedSingleControlModularDomination_one_iff_targetStatement_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerBoundedSingleControlModularDomination b (fun _ => 1) ↔ TargetStatement := by
  exact
    eventualNatPowerBoundedSingleControlModularDomination_one_iff_targetStatement_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_one_iff_targetStatement_of_one_lt
    {b : ℕ} (hb : 1 < b) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b (fun _ => 1) ↔
      TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_lt
      singletonControlBudget_eventually_lt]
  exact eventualNatPowerBoundedSingleControlExactDomination_one_iff_targetStatement_of_one_lt hb

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_one_iff_targetStatement_of_two_lt
    {b : ℕ} (hb : 2 < b) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b (fun _ => 1) ↔
      TargetStatement := by
  exact
    eventualNatPowerBoundedSingleControlModularBucketingDomination_one_iff_targetStatement_of_one_lt
      (lt_trans (by decide : 1 < 2) hb)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_iff_eventualNatPowerDomination_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlBucketingDomination b u ↔ EventualNatPowerDomination b := by
  rw [← eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerBoundedSingleControlBucketingDomination]
  exact eventualNatPowerBoundedSingleControlExactDomination_iff_eventualNatPowerDomination_of_eventually_pos
    hb hpos

theorem eventualNatPowerBoundedSingleControlBucketingDomination_iff_targetStatement_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlBucketingDomination b u ↔ TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlBucketingDomination_iff_eventualNatPowerDomination_of_eventually_pos
      hb hpos,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerDomination_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔ EventualNatPowerDomination b := by
  constructor
  · intro hsingle
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularWitnessOfCard G
      (hK hk G)
  · intro hpow
    exact eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerBoundedSingleControlModularDomination
      (eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_pos
        hb hpos hpow)

theorem eventualNatPowerBoundedSingleControlModularDomination_iff_targetStatement_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlModularDomination b u ↔ TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlModularDomination_iff_eventualNatPowerDomination_of_eventually_pos
      hb hpos,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerDomination_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u ↔
      EventualNatPowerDomination b := by
  constructor
  · intro hbuck
    intro M
    rcases hbuck M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlModularBucketingWitnessOfCard G
      (hK hk G)
  · intro hpow
    intro M
    rcases
      (eventualNatPowerDomination_implies_eventualNatPowerBoundedSingleControlExactDomination_of_eventually_pos
        hb hpos hpow) M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact
      hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard G
        (hasBoundedSingleControlBucketingWitnessOfCard_of_hasBoundedSingleControlExactWitnessOfCard G
          (hK hk G))

theorem
    eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_targetStatement_of_eventually_pos
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hpos : ∃ K : ℕ, ∀ ⦃k : ℕ⦄, K ≤ k → 0 < u k) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u ↔
      TargetStatement := by
  rw [eventualNatPowerBoundedSingleControlModularBucketingDomination_iff_eventualNatPowerDomination_of_eventually_pos
      hb hpos,
    eventualNatPowerDomination_iff_targetStatement hb]

theorem eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlExactDomination b) :
    EventualNatPowerSingleControlCascadeDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasSingleControlCascadeWitnessOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination
    {b : ℕ} (hcascade : EventualNatPowerSingleControlCascadeDomination b) :
    EventualNatPowerSingleControlExactDomination b := by
  exact eventualNatPowerExactControlBlockDomination_implies_eventualNatPowerSingleControlExactDomination
    (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerExactControlBlockDomination
      hcascade)

theorem eventualNatPowerSingleControlExactDomination_iff_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlExactDomination b ↔
      EventualNatPowerSingleControlCascadeDomination b := by
  constructor
  · exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
  · exact eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination

theorem eventualNatPowerSingleControlBucketingDomination_iff_eventualNatPowerSingleControlCascadeDomination
    {b : ℕ} :
    EventualNatPowerSingleControlBucketingDomination b ↔
      EventualNatPowerSingleControlCascadeDomination b := by
  constructor
  · intro hbuck
    exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlCascadeDomination
      (eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
        hbuck)
  · intro hcascade
    exact eventualNatPowerSingleControlExactDomination_implies_eventualNatPowerSingleControlBucketingDomination
      (eventualNatPowerSingleControlCascadeDomination_implies_eventualNatPowerSingleControlExactDomination
        hcascade)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlModularDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlModularDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlModularBucketingDomination
    {b : ℕ} {u : ℕ → ℕ}
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) :
    EventualNatPowerBoundedSingleControlModularBucketingDomination b u := by
  intro M
  rcases hbuck M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasBoundedSingleControlModularBucketingWitnessOfCard_of_hasBoundedSingleControlBucketingWitnessOfCard
    G (hK hk G)

theorem eventualNatPowerSingleControlExactDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hsingle : EventualNatPowerSingleControlExactDomination b) :
    TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasSingleControlExactWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerSingleControlModularDomination_implies_eventualNatPowerModularDomination
    {b : ℕ} (hsingle : EventualNatPowerSingleControlModularDomination b) :
    EventualNatPowerModularDomination b := by
  intro M
  rcases hsingle M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk G
  exact hasModularWitnessOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerSingleControlModularDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hsingle : EventualNatPowerSingleControlModularDomination b) :
    TargetStatement := by
  have hpow : EventualNatPowerDomination b := by
    intro M
    rcases hsingle M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact hasRegularInducedSubgraphOfCard_of_hasSingleControlModularWitnessOfCard G (hK hk G)
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1 hpow

theorem eventualNatPowerBoundedSingleControlModularDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hsingle : EventualNatPowerBoundedSingleControlModularDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlModularDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlModularDomination_implies_eventualNatPowerSingleControlModularDomination
      hsingle)

theorem eventualNatPowerSingleControlModularBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerSingleControlModularBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerSingleControlModularDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedSingleControlModularBucketingDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlModularBucketingDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlModularBucketingDomination_implies_eventualNatPowerSingleControlModularBucketingDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlExactDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hsingle : EventualNatPowerBoundedSingleControlExactDomination b u) : TargetStatement := by
  exact eventualNatPowerSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlExactDomination_implies_eventualNatPowerSingleControlExactDomination
      hsingle)

theorem eventualNatPowerSingleControlBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerSingleControlBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerSingleControlBucketingDomination_implies_eventualNatPowerSingleControlExactDomination
      hbuck)

theorem eventualNatPowerBoundedSingleControlBucketingDomination_implies_targetStatement
    {b : ℕ} {u : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedSingleControlBucketingDomination b u) : TargetStatement := by
  exact eventualNatPowerBoundedSingleControlExactDomination_implies_targetStatement hb
    (eventualNatPowerBoundedSingleControlBucketingDomination_implies_eventualNatPowerBoundedSingleControlExactDomination
      hbuck)

theorem eventualNatPowerControlBlockBucketingDomination_implies_targetStatement
    {b : ℕ} (hb : 1 < b) (hbuck : EventualNatPowerControlBlockBucketingDomination b) :
    TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
      hbuck)

theorem eventualNatPowerBoundedControlBlockBucketingDomination_implies_targetStatement
    {b : ℕ} {r : ℕ → ℕ} (hb : 1 < b)
    (hbuck : EventualNatPowerBoundedControlBlockBucketingDomination b r) : TargetStatement := by
  exact eventualNatPowerExactControlBlockDomination_implies_targetStatement hb
    (eventualNatPowerBoundedControlBlockBucketingDomination_implies_eventualNatPowerExactControlBlockDomination
      hbuck)

theorem eventualNatPowerLowDegreeModularDomination_implies_eventualNatPowerDomination {b : ℕ}
    (hmod : EventualNatPowerLowDegreeModularDomination b) :
    EventualNatPowerDomination b := by
  intro M
  rcases hmod M with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  rw [le_F_iff]
  intro G
  exact hasRegularInducedSubgraphOfCard_of_hasLowDegreeModularWitnessOfCard G (hK hk G)

theorem eventualNatPowerLowDegreeModularDomination_implies_targetStatement {b : ℕ} (hb : 1 < b)
    (hmod : EventualNatPowerLowDegreeModularDomination b) : TargetStatement := by
  exact (eventualNatPowerDomination_iff_targetStatement (b := b) hb).1
    (eventualNatPowerLowDegreeModularDomination_implies_eventualNatPowerDomination hmod)

theorem eventualNatPowerModularDomination_iff_eventualNatPowerDomination {b : ℕ} :
    EventualNatPowerModularDomination b ↔ EventualNatPowerDomination b := by
  constructor
  · intro hmod
    intro M
    rcases hmod M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    exact (hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard G (M * k)).mp (hK hk G)
  · intro hpow
    intro M
    rcases hpow M with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk G
    exact (hasModularWitnessOfCard_iff_hasRegularInducedSubgraphOfCard G (M * k)).mpr
      ((le_F_iff.mp (hK hk)) G)

theorem eventualNatPowerControlBlockDomination_iff_eventualNatPowerDomination {b : ℕ} :
    EventualNatPowerControlBlockDomination b ↔ EventualNatPowerDomination b := by
  rw [eventualNatPowerControlBlockDomination_iff_eventualNatPowerModularDomination,
    eventualNatPowerModularDomination_iff_eventualNatPowerDomination]

theorem eventualNatPowerControlBlockDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualNatPowerControlBlockDomination b ↔ TargetStatement := by
  rw [eventualNatPowerControlBlockDomination_iff_eventualNatPowerDomination]
  exact eventualNatPowerDomination_iff_targetStatement hb

theorem eventualNatPowerModularDomination_iff_targetStatement {b : ℕ} (hb : 1 < b) :
    EventualNatPowerModularDomination b ↔ TargetStatement := by
  rw [eventualNatPowerModularDomination_iff_eventualNatPowerDomination]
  exact eventualNatPowerDomination_iff_targetStatement hb

theorem eventualNatPowerModularDomination_four_iff_targetStatement :
    EventualNatPowerModularDomination 4 ↔ TargetStatement := by
  simpa using eventualNatPowerModularDomination_iff_targetStatement (b := 4) (by decide : 1 < 4)

section DyadicLift

/--
A terminal-bounded fixed-modulus modular cascade witness of size at least `k`: this is the same data
as `HasControlBlockModularCascadeWitnessOfCard`, but with the modulus exposed as an argument so a
dyadic lift hypothesis can refer to it directly.

This is stronger than the composable fixed-modulus host package introduced in `Modular.Finite`,
because it still requires the terminal bucket size to be at most the modulus.
-/
def HasFixedModulusControlBlockModularCascadeWitnessOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k q : ℕ) : Prop := by
  classical
  exact ∃ s : Finset V, ∃ blocks : List (Finset V × ℕ), ∃ chain : List (Finset V),
    k ≤ (cascadeTerminal s chain).card ∧
    (cascadeTerminal s chain).card ≤ q ∧
    NonemptyControlBlockUnion blocks ∧
    ControlBlocksSeparated s blocks ∧
    HasControlBlockModularCascadeFrom G q blocks s chain

lemma hasControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k q : ℕ}
    (hfixed : HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q) :
    HasControlBlockModularCascadeWitnessOfCard G k := by
  rcases hfixed with ⟨s, blocks, chain, hk, hq, hnonempty, hsep, hcascade⟩
  exact ⟨s, q, blocks, chain, hk, hq, hnonempty, hsep, hcascade⟩

lemma hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k q : ℕ}
    (hfixed : HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q) :
    HasRegularInducedSubgraphOfCard G k := by
  exact
    hasRegularInducedSubgraphOfCard_of_hasControlBlockModularCascadeWitnessOfCard G
      (hasControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
        G hfixed)

lemma hasFixedModulusControlBlockModularCascadeWitnessOfCard_mono
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k ℓ q : ℕ} (hkℓ : k ≤ ℓ)
    (hfixed : HasFixedModulusControlBlockModularCascadeWitnessOfCard G ℓ q) :
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q := by
  rcases hfixed with ⟨s, blocks, chain, hℓ, hq, hnonempty, hsep, hcascade⟩
  exact ⟨s, blocks, chain, le_trans hkℓ hℓ, hq, hnonempty, hsep, hcascade⟩

lemma exists_terminal_externalBlockData_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k q : ℕ} (hfixed : HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q) :
    ∃ u : Finset V, ∃ blocks : List (Finset V × ℕ),
      k ≤ u.card ∧
      u.card ≤ q ∧
      NonemptyControlBlockUnion blocks ∧
      ControlBlocksSeparated u blocks ∧
      InducesModEqDegree G u q ∧
      HasConstantModExternalBlockDegrees G u q blocks := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases hfixed with ⟨s, baseBlocks, chain, hk, hq, hnonempty, hsep, hmod⟩
  rcases
      exists_controlBlockCascadeModularData_of_hasControlBlockModularCascadeFrom
        G hnonempty hsep hmod with
    ⟨u, blocks, huTerm, _hlen, _huSub, hnonemptyU, hsepU, _hunion, hdegU, hextU⟩
  refine ⟨u, blocks, ?_, ?_, hnonemptyU, hsepU, ?_, hextU⟩
  · simpa [huTerm, cascadeTerminal] using hk
  · simpa [huTerm, cascadeTerminal] using hq
  · exact
      inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees
        G hsepU hdegU hextU

lemma hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k q : ℕ} {s : Finset V} {blocks : List (Finset V × ℕ)} {chain : List (Finset V)}
    (hku : k ≤ (cascadeTerminal s chain).card) (hq : (cascadeTerminal s chain).card ≤ q)
    (hnonempty : NonemptyControlBlockUnion blocks) (hsep : ControlBlocksSeparated s blocks)
    (hcascade : HasFixedModulusCascadeFrom G q s chain)
    (hext : HasConstantModExternalBlockDegrees G s q blocks) :
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q := by
  exact
    ⟨s, blocks, chain, hku, hq, hnonempty, hsep,
      hasControlBlockModularCascadeFrom_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
        G hsep hcascade hext⟩

/--
Small-ambient refinement data already suffice for the fixed-modulus control-block modular cascade
package: take the selected bucket `w` as the terminal host and keep the inherited control blocks.
-/
lemma
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard G k q r) :
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  rcases href with ⟨w, s, t, hwk, hw, blocks, e, htcard, _hlen, hsep, hsmall, _hctrl, _hhost, hext⟩
  have htpos : 0 < t.card := by
    rw [htcard]
    exact Nat.sub_pos_of_lt hq
  have hnonempty : NonemptyControlBlockUnion ((t, e) :: blocks) := by
    rcases Finset.card_pos.mp htpos with ⟨x, hx⟩
    refine Finset.card_pos.mpr ?_
    refine ⟨x, ?_⟩
    simp [controlBlockUnion, hx]
  have hsepW : ControlBlocksSeparated w ((t, e) :: blocks) := controlBlocksSeparated_mono hw hsep
  have hwMod : InducesModEqDegree G w q := by
    exact inducesModEqDegree_of_modEq_unionDegree_and_externalBlockDegrees G hsepW hsmall hext
  have hfrom : HasFixedModulusCascadeFrom G q w [] := by
    simpa [HasFixedModulusCascadeFrom, InducesModEqDegree] using hwMod
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
      (G := G) (s := w) (blocks := ((t, e) :: blocks)) (chain := [])
      (by simpa [cascadeTerminal, hwk] using (le_rfl : k ≤ k))
      (by simpa [cascadeTerminal, hwk] using hkq)
      hnonempty hsepW hfrom hext

lemma
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k q r : ℕ} (hkq : k ≤ q) (hq : 1 < q)
    (href :
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G k q r) :
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q := by
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
      (G := G) hkq hq
      (hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
        (G := G) href)

/--
Gallai's theorem in the empty-control fixed-modulus cascade package suggested by the dyadic note.
Unlike `DyadicParityBaseCase`, this package keeps the modulus fixed but does not require a nonempty
control family or the terminal cap `|u| ≤ q`.
-/
def EmptyControlDyadicParityBaseCase : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    HasFixedModulusCascadeWitnessOfCard G (n / 2) 2

/--
Polynomial-cost dyadic lift hypothesis in the empty-control fixed-modulus cascade package.
-/
def HasPolynomialCostEmptyControlDyadicLift (C : ℕ) : Prop :=
  ∀ {n j m : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusCascadeWitnessOfCard G ((2 ^ j) ^ C * m) (2 ^ j) →
      HasFixedModulusCascadeWitnessOfCard G m (2 ^ (j + 1))

/--
Precise missing package behind the empty-control terminal bridge: starting from a large fixed-modulus
cascade witness, produce a genuinely nonempty separated control-block family whose external degrees
are already constant modulo `2^j` on the same cascade host. The existing finite bridge then turns
this data into the terminal-capped control-block modular cascade package without further work.
-/
def HasPolynomialCostEmptyControlExternalBlockBridge (D : ℕ) : Prop := by
  classical
  exact
    ∀ {n j m : ℕ} (G : SimpleGraph (Fin n)),
      HasFixedModulusCascadeWitnessOfCard G ((2 ^ j) ^ D * m) (2 ^ j) →
        ∃ s : Finset (Fin n), ∃ chain : List (Finset (Fin n)),
          ∃ blocks : List (Finset (Fin n) × ℕ),
            m ≤ (cascadeTerminal s chain).card ∧
            (cascadeTerminal s chain).card ≤ 2 ^ j ∧
            NonemptyControlBlockUnion blocks ∧
            ControlBlocksSeparated s blocks ∧
            HasFixedModulusCascadeFrom G (2 ^ j) s chain ∧
            HasConstantModExternalBlockDegrees G s (2 ^ j) blocks

/--
Polynomial-cost bridge from the empty-control fixed-modulus cascade package to the terminal-capped
control-block modular cascade package. The modulus stays fixed; only the witness order pays a
polynomial loss.
-/
def HasPolynomialCostEmptyControlTerminalBridge (D : ℕ) : Prop :=
  ∀ {n j m : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusCascadeWitnessOfCard G ((2 ^ j) ^ D * m) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G m (2 ^ j)

/--
Special-case version of the empty-control terminal bridge actually used in the dyadic forcing
argument: only the self-target `m = q = 2^j` is requested.
-/
def HasPolynomialCostEmptyControlTerminalSelfBridge (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusCascadeWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Even more reduced self-bridge: after descending to the terminal bucket, it is enough to bridge from
an ordinary fixed-modulus witness rather than from a full empty-control cascade.
-/
def HasPolynomialCostFixedWitnessTerminalSelfBridge (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Honest self-target version of the external-block bridge: at positive dyadic moduli, a large
fixed-modulus witness should already supply the separated control-block data needed by the finite
cascade bridge, but only for the terminal target `m = q = 2^j`.
-/
def HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge (D : ℕ) : Prop := by
  classical
  exact
    ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
      HasFixedModulusWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
        ∃ s : Finset (Fin n), ∃ chain : List (Finset (Fin n)),
          ∃ blocks : List (Finset (Fin n) × ℕ),
            2 ^ j ≤ (cascadeTerminal s chain).card ∧
            (cascadeTerminal s chain).card ≤ 2 ^ j ∧
            NonemptyControlBlockUnion blocks ∧
            ControlBlocksSeparated s blocks ∧
            HasFixedModulusCascadeFrom G (2 ^ j) s chain ∧
            HasConstantModExternalBlockDegrees G s (2 ^ j) blocks

/--
Viable dyadic self-bridge after the `q = 8` obstruction: only positive dyadic moduli `2^j` with
`j > 0` are requested, so the impossible `q = 1` control-block terminal case is excluded.
-/
def HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasFixedModulusWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Weakest fixed-witness self-target needed for the dyadic forcing argument: a large fixed-modulus
witness already collapses directly to a regular induced subgraph on `q = 2^j` vertices.
-/
def HasPolynomialCostFixedWitnessTerminalRegularization (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
      HasRegularInducedSubgraphOfCard G (2 ^ j)

/--
Further reduction of the terminal regularization problem: after deleting one nonempty control block,
it is enough to regularize a fixed-modulus host witness on the surviving bucket.
-/
def HasPolynomialCostFixedOneControlHostTerminalRegularization (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) 1 →
      HasRegularInducedSubgraphOfCard G (2 ^ j)

/--
The same bottleneck, repackaged using one explicit control set instead of a length-`1` control-block
list.
-/
def HasPolynomialCostFixedSingleControlHostTerminalRegularization (D : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusSingleControlModularHostWitnessOfCard G ((2 ^ j) ^ D * 2 ^ j) (2 ^ j) →
      HasRegularInducedSubgraphOfCard G (2 ^ j)

/--
Literal terminal-case obstruction in the single-control host language: the surviving bucket already
has exact cardinality `q = 2^j`.
-/
def HasExactCardFixedSingleControlHostTerminalRegularization : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G (2 ^ j) (2 ^ j) →
      HasRegularInducedSubgraphOfCard G (2 ^ j)

/--
Precise terminal upgrade singled out by the dropped-part roadmap: every exact-card fixed-modulus
single-control host witness can be strengthened so that the dropped-part residue on `s \ u` is also
frozen modulo `2^j`, while the control scalar into `t` is fixed exactly.
-/
def HasExactCardFixedSingleControlHostDroppedPartUpgrade : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G (2 ^ j) (2 ^ j) →
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Terminal-size bounded host regularization: once a bounded fixed-modulus control-block modular host
witness already lives on `q = 2^j` vertices, it collapses directly to a regular induced subgraph on
`q` vertices.
-/
def HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (2 ^ j) (2 ^ j) r →
      HasRegularInducedSubgraphOfCard G (2 ^ j)

/--
Positive-dyadic graph-local form of Corollary 10.2: every completed host/control pair at size
`q = 2^j` with `j > 0` contains a regular `q`-subset of the completed host.
-/
def HasPositiveDyadicCompletedHostRegularSelection : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasCompletedHostRegularSelection G (2 ^ j)

/--
Stronger graph-only sufficient theorem from the notes: every `q^2`-vertex induced subgraph with
degrees constant modulo `q` already contains a regular induced `q`-subgraph.
-/
def HasPositiveDyadicModulusSquareRegularSelection : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasModulusSquareRegularSelection G (2 ^ j)

theorem hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    HasPositiveDyadicCompletedHostRegularSelection := by
  intro n j hj G
  exact hasCompletedHostRegularSelection_of_hasModulusSquareRegularSelection G (hselect hj G)

/--
Weaker positive-dyadic terminal target for the bounded host package: at terminal size `q = 2^j`
with `j > 0`, it is enough to produce a control-block modular cascade witness rather than a regular
induced subgraph.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    (r : ℕ) : Prop := by
  classical
  exact
    ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (2 ^ j) (2 ^ j) r →
        ∃ s : Finset (Fin n), ∃ chain : List (Finset (Fin n)),
          ∃ blocks : List (Finset (Fin n) × ℕ),
            2 ^ j ≤ (cascadeTerminal s chain).card ∧
            (cascadeTerminal s chain).card ≤ 2 ^ j ∧
            NonemptyControlBlockUnion blocks ∧
            ControlBlocksSeparated s blocks ∧
            HasFixedModulusCascadeFrom G (2 ^ j) s chain ∧
            HasConstantModExternalBlockDegrees G s (2 ^ j) blocks

/--
Weaker positive-dyadic terminal target for the bounded host package: at terminal size `q = 2^j`
with `j > 0`, it is enough to produce the explicit external-block data needed by the finite cascade
bridge.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (2 ^ j) (2 ^ j) r →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Weaker positive-dyadic one-step self-target: at positive dyadic modulus `q = 2^j`, every bounded
host witness of size `q * q` already collapses to the fixed-modulus control-block modular cascade
package on `q` vertices.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ((2 ^ j) * 2 ^ j) (2 ^ j) r →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ j) (2 ^ j)

/--
Honest one-step finite Branch B self-target: at positive dyadic modulus `q = 2^j`, every bounded
host witness of size `q * q` should already collapse to a bounded exact single-control witness of
size `q` with control budget `q - 1`.

This packages exactly the output that the strengthened host-step theorem would deliver once the
missing dropped-part residue on the reduced host is recovered.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ((2 ^ j) * 2 ^ j) (2 ^ j) r →
      HasBoundedSingleControlExactWitnessOfCard G (2 ^ j) (2 ^ j - 1)

/--
Surviving direct exact upgrade singled out by the current `q * q -> q` self-step: only exact-card
fixed-modulus single-control modular host witnesses whose control set already has size `q - 1` need
to be upgraded, and only to some bounded exact single-control witness.
-/
def HasExactCardFixedSingleControlHostMaximalControlUpgrade : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
        G (2 ^ j) (2 ^ j) (2 ^ j - 1) →
      HasBoundedSingleControlExactWitnessOfCard G (2 ^ j) (2 ^ j - 1)

/--
Exact missing finite datum in the stripped `q - 1`-control route: keep the same structured modular
host witness, but adjoin only the dropped-part residue on `s \ u`.

At control size `q - 1`, the modular control-degree data already collapse automatically to exact
equality, so this is the honest missing ingredient beneath the direct exact-upgrade target.
-/
def HasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
        G (2 ^ j) (2 ^ j) (2 ^ j - 1) →
      HasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
        G (2 ^ j) (2 ^ j) (2 ^ j - 1)

/--
Stronger local residue-host route behind the structured self-step: the `q - 1`-control exact-card
host output should upgrade to the corresponding dropped-part residue package before the existing
exactness collapse is applied.

This is stronger than `HasExactCardFixedSingleControlHostMaximalControlUpgrade`; the script
`verify_q4_structured_residue_upgrade_counterexample.py` shows that this stronger residue route is
already false at `q = 4`, so the direct exact-upgrade target above is the honest live frontier.
-/
def HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
        G (2 ^ j) (2 ^ j) (2 ^ j - 1) →
      HasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
        G (2 ^ j) (2 ^ j) (2 ^ j - 1)

/--
Exact finite obstruction inside the current refinement-data package: recover the smaller ambient
congruence on `w ∪ controlBlockUnion ((t, e) :: blocks)`. Once this is available, the dropped-part
residue on `s \ w` follows algebraically.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: recover a dyadic pairing tree
for the dropped-part columns of `s \ w` relative to the current bucket `w`.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: recover a first-bit packet
decomposition for the dropped-part columns together with recursive divisibility data on the halved
dropped-part degree function.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: recover a dyadic divisibility
chain for the dropped-part degree function on the current bucket.

This packages the obstruction-module viewpoint without insisting on literal equal/complementary
column pairings.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: once a full dyadic
divisibility chain is available, isolate the terminal tail on which the last mod-2 step lives.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      G (2 ^ j) (2 ^ j) r →
    HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
      G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: recover an explicit terminal
dyadic tail after the frozen lower bits, together with the mod-2 constancy of that terminal tail.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Beta-vanishing version of the dyadic refinement bridge.  This is the note-level bit-by-bit
formulation: the refinement package supplies a dropped-tail row together with the terminal beta
vanishing needed to promote it to a full dyadic divisibility chain.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
All-bits beta version of the dyadic refinement bridge.  This is closest to the note phrase
"beta vanishes at every bit": Lean constructs the full dyadic divisibility chain from that package.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction inside the current refinement-data package: recover the smaller ambient
congruence on `w ∪ controlBlockUnion ((t, e) :: blocks)`. Once this is available, the dropped-part
residue on `s \ w` follows algebraically.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Exact finite obstruction singled out by the current host notes: from the refinement-data package,
recover a genuine completed host of size `q^2` carrying the inherited exact control block.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard
        G (2 ^ j) (2 ^ j - 1)

/--
Honest live finite bridge above the current `Cascade.lean` host-step theorem: instead of forgetting
the extra ambient/control-block data down to a bare structured modular-host witness, ask directly
that the full refined host-step package already collapses to a bounded exact single-control witness.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
        G (2 ^ j) (2 ^ j) r

/--
Honest live finite bridge above the current `Cascade.lean` host-step theorem: instead of forgetting
the extra ambient/control-block data down to a bare structured modular-host witness, ask directly
that the full refined host-step package already collapses to a bounded exact single-control witness.
-/
def HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    (r : ℕ) : Prop :=
  ∀ {n j : ℕ} (hj : 0 < j) (G : SimpleGraph (Fin n)),
    HasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard G (2 ^ j) (2 ^ j) r →
      HasBoundedSingleControlExactWitnessOfCard G (2 ^ j) (2 ^ j - 1)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementTailDataOfCard
      (G := G) le_rfl hq (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTailSelfBridge
      (r := r) hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementFirstBitPacketDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTailDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicTerminalDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDyadicBetaUpToDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge_iff_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
    {r : ℕ} :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge r ↔
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r :=
  ⟨hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge,
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge⟩

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {r : ℕ}
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        r)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge r := by
  intro n j hj G href
  exact hbridge hj G (hdiv hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_eq_modulus_and_one_lt_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDyadicDivisibilityDataOfCard
      (G := G) rfl hq (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {r : ℕ}
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        r)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
      (r := r)
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := r) hdiv hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
      (r := r) hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementTerminalSelfBridge
      (r := r) hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementFirstBitPacketSelfBridge
      (r := r) hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementPairingSelfBridge
      (r := r) hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
      (G := G)
      (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) le_rfl hq (hbridge hj G href)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {r : ℕ}
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r := by
  intro n j hj G href
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hupgrade hj G
      (hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
        (G := G) hq href)

theorem
    hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    HasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard
      (G := G)
      (hupgrade hj G hhost)

theorem
    hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade) :
    HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasExactCardFixedModulusSingleControlResidueHostWitnessOfCardWithControlCard_of_lt_of_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
      (G := G) (by simpa using Nat.sub_lt hq (by decide : 0 < 1))
      (hupgrade hj G hhost)

theorem
    hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade_iff_hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade :
    HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade ↔
      HasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade := by
  constructor
  · exact
      hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
  · exact
      hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade

theorem
    hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade) :
    HasExactCardFixedSingleControlHostMaximalControlUpgrade := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_of_lt_and_hasExactCardFixedModulusSingleControlModularHostDropDataOfCardWithControlCard
      (G := G) le_rfl
      (by simpa using Nat.sub_lt hq (by decide : 0 < 1))
      (hupgrade hj G hhost)

theorem
    hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    HasExactCardFixedSingleControlHostMaximalControlUpgrade := by
  exact
    hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade
      (hasExactCardFixedSingleControlHostMaximalControlDropResidueUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {r : ℕ}
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hupgrade hj G
      (hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_self_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) hq hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    {r : ℕ}
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      (hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hbridge hj G
      (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
        hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge_and_hasPositiveDyadicCompletedHostRegularSelection
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge
        r)
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard_and_hasCompletedHostRegularSelection
      (G := G)
      (hbridge hj G
        (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
          (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost))
      (hselect hj G)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge_and_hasPositiveDyadicModulusSquareRegularSelection
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge
        r)
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementCompletedHostSelfBridge_and_hasPositiveDyadicCompletedHostRegularSelection
      (r := r) hbridge
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {r : ℕ}
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        r)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := r) hdiv hbridge)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard
      (G := G) le_rfl hq
      (hbridge hj G
        (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
          (G := G) (q := 2 ^ j) (k := 2 ^ j) hq (Nat.pow_pos (by decide : 0 < 2)) hhost))

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
      (fun hj G href => by
        classical
        letI : DecidableRel G.Adj := Classical.decRel G.Adj
        exact
          hasExactCardFixedModulusControlBlockModularHostRefinementSmallAmbientDataOfCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
            (G := G) (hbridge hj G href))

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {r : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

/--
Weaker host-side frontier singled out by Corollary 10.2: from a bounded host witness at bucket
`q * q`, first recover a completed host of size `q^2` together with the inherited exact control
block of size `q - 1`.

Once this completed-host package is available, the remaining graph-theoretic task is exactly the
local regular-selection problem formalized by `HasCompletedHostRegularSelection`.
-/
def HasCompletedHostExtractionFromHostWitness (r : ℕ) : Prop :=
  ∀ {n : ℕ} {q : ℕ} (_hq : 1 < q) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q r →
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard G q (q - 1)

/--
Per-modulus slice of the completed-host extraction problem behind Corollary 10.2.
-/
def HasCompletedHostExtractionAtModulus (q r : ℕ) : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q r →
      HasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard G q (q - 1)

/--
The full completed-host extraction problem is exactly the conjunction of its per-modulus slices.
-/
theorem hasCompletedHostExtractionFromHostWitness_of_forall_modulus
    {r : ℕ} (hmod : ∀ q : ℕ, 1 < q → HasCompletedHostExtractionAtModulus q r) :
    HasCompletedHostExtractionFromHostWitness r := by
  intro n q hq G _ hhost
  exact hmod q hq G hhost

/--
Finite combinatorial obstruction isolated empirically in the throwaway investigation
(`check_step_drop_residue.py`, `verify_reduction.py`): every bounded fixed-modulus control-block
modular host witness at bucket `q * q` admits the missing dropped-part residue at bucket `q`.

The reduction behind this target is:
`drop(v) mod q` on a bucket subset `u*` of size `q` equals
`D - deg_G[u*](v) mod q`, where `D` is the bucket-constant host degree modulo `q`.
Since `|u*| = q`, `mod q` constancy of `deg_G[u*]` on `u*` is exact constancy, i.e. `G[u*]` is a
regular induced subgraph of size `q`.  So the claim further reduces to

  *every graph on `q * q` vertices contains a size-`q` induced regular subgraph*,

an instance of the Erdős–Faudree–Sós regular induced subgraph conjecture at `n = q^2`,
`size = q = √n`.  This is trivial for `q = 2`, follows from Ramsey `R(3, 3) = 6 ≤ 9` for `q = 3`,
and was verified empirically for `q = 4` (0/500 random graphs on 16 vertices without a size-4 regular
induced subgraph across a range of edge probabilities).
-/
def HasDropResidueExtractionFromHostWitness (r : ℕ) : Prop :=
  ∀ {n : ℕ} {q : ℕ} (_hq : 1 < q) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G q q r

/--
Per-modulus slice of the dropped-part extraction problem behind the positive-dyadic step-exact bridge.
-/
def HasDropResidueExtractionAtModulus (q r : ℕ) : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q r →
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G q q r

/--
The full obstruction `HasDropResidueExtractionFromHostWitness` is exactly the conjunction of its
per-modulus slices.
-/
theorem hasDropResidueExtractionFromHostWitness_of_forall_modulus
    {r : ℕ} (hmod : ∀ q : ℕ, 1 < q → HasDropResidueExtractionAtModulus q r) :
    HasDropResidueExtractionFromHostWitness r := by
  intro n q hq G _ hhost
  exact hmod q hq G hhost

/--
Local induced-degree formula used below: inside an induced subgraph on `s`, the degree of `v` is the
number of ambient neighbors of `v` that also lie in `s`.
-/
private lemma degree_inducedOn_eq_card_neighborFinset_inter_asymptotic
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) (v : ↑(s : Set (Fin n))) :
    (inducedOn G s).degree v = (G.neighborFinset v ∩ s).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((inducedOn G s).neighborFinset v).map (Function.Embedding.subtype (· ∈ (s : Set (Fin n)))) =
        G.neighborFinset v ∩ s := by
    ext x
    simp [inducedOn, and_assoc]
  calc
    ((inducedOn G s).neighborFinset v).card =
        (((inducedOn G s).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ (s : Set (Fin n))))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset v ∩ s).card := by rw [hmap]

/--
On a 2-vertex induced subgraph, the two degrees are equal: either the edge is present and both
degrees are `1`, or it is absent and both are `0`.
-/
private lemma induced_pair_degree_eq
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b : Fin n} (hab : a ≠ b) :
    (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨a, by simp [hab]⟩ =
      (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨b, by simp [hab]⟩ := by
  have haa : a ∉ G.neighborFinset a := by
    simpa [SimpleGraph.mem_neighborFinset] using (G.irrefl a)
  have hbb : b ∉ G.neighborFinset b := by
    simpa [SimpleGraph.mem_neighborFinset] using (G.irrefl b)
  have hsingle :
      (G.neighborFinset a ∩ ({b} : Finset (Fin n))).card =
        (G.neighborFinset b ∩ ({a} : Finset (Fin n))).card := by
    by_cases habAdj : G.Adj a b
    · have hbaAdj : G.Adj b a := G.symm habAdj
      simp [SimpleGraph.mem_neighborFinset, habAdj, hbaAdj]
    · have hbaAdj : ¬ G.Adj b a := by
        intro h
        exact habAdj (G.symm h)
      simp [SimpleGraph.mem_neighborFinset, habAdj, hbaAdj]
  calc
    (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨a, by simp [hab]⟩ =
        (G.neighborFinset a ∩ ({a, b} : Finset (Fin n))).card := by
          exact
            degree_inducedOn_eq_card_neighborFinset_inter_asymptotic
              (G := G) ({a, b} : Finset (Fin n)) ⟨a, by simp [hab]⟩
    _ = (G.neighborFinset a ∩ ({b} : Finset (Fin n))).card := by
          simp [Finset.inter_insert, haa, hab]
    _ = (G.neighborFinset b ∩ ({a} : Finset (Fin n))).card := hsingle
    _ = (G.neighborFinset b ∩ ({a, b} : Finset (Fin n))).card := by
          simpa [Finset.pair_comm, Finset.inter_insert, hbb]
    _ = (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨b, by simp [hab]⟩ := by
          symm
          exact
            degree_inducedOn_eq_card_neighborFinset_inter_asymptotic
              (G := G) ({a, b} : Finset (Fin n)) ⟨b, by simp [hab]⟩

/--
At modulus `2`, the missing dropped-part residue can be recovered directly from the exact-card
refinement data: on a 2-vertex bucket, the induced degrees inside the bucket are automatically equal.
-/
private lemma modEq_dropDegree_of_card_two
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {w s : Finset (Fin n)} (hwk : w.card = 2) (hw : w ⊆ s)
    (hhost :
      ∀ v w' : ↑(w : Set (Fin n)),
        (inducedOn G s).degree ⟨v.1, hw v.2⟩ ≡
          (inducedOn G s).degree ⟨w'.1, hw w'.2⟩ [MOD 2]) :
    ∀ v w' : ↑(w : Set (Fin n)),
      (G.neighborFinset v ∩ (s \ w)).card ≡
        (G.neighborFinset w' ∩ (s \ w)).card [MOD 2] := by
  rcases Finset.card_eq_two.mp hwk with ⟨a, b, hab, hwab⟩
  have hwa : a ∈ w := by simpa [hwab, hab]
  have hwb : b ∈ w := by simpa [hwab, hab]
  let va : ↑(w : Set (Fin n)) := ⟨a, hwa⟩
  let vb : ↑(w : Set (Fin n)) := ⟨b, hwb⟩
  have hdisj : Disjoint w (s \ w) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxW hxDrop
    exact (Finset.mem_sdiff.mp hxDrop).2 hxW
  have hdegwEq :
      (inducedOn G w).degree va = (inducedOn G w).degree vb := by
    have hcastA :
        (inducedOn G w).degree va =
          (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨a, by simp [hab]⟩ := by
      simpa [va, hwab] using
        (inducedOn_degree_congr (G := G)
          (s := w) (t := ({a, b} : Finset (Fin n)))
          (h := hwab)
          (hs := va.2)
          (ht := by
            have haPair : a ∈ ({a, b} : Finset (Fin n)) := by simp [hab]
            simpa [va] using haPair))
    have hcastB :
        (inducedOn G w).degree vb =
          (inducedOn G ({a, b} : Finset (Fin n))).degree ⟨b, by simp [hab]⟩ := by
      simpa [vb, hwab] using
        (inducedOn_degree_congr (G := G)
          (s := w) (t := ({a, b} : Finset (Fin n)))
          (h := hwab)
          (hs := vb.2)
          (ht := by
            have hbPair : b ∈ ({a, b} : Finset (Fin n)) := by simp [hab]
            simpa [vb] using hbPair))
    simpa [hcastA, hcastB] using induced_pair_degree_eq (G := G) hab
  have hbigAB :
      (inducedOn G (w ∪ (s \ w))).degree
          ⟨va.1, Finset.mem_union.mpr (Or.inl va.2)⟩ ≡
        (inducedOn G (w ∪ (s \ w))).degree
          ⟨vb.1, Finset.mem_union.mpr (Or.inl vb.2)⟩ [MOD 2] := by
    have hcastA :
        (inducedOn G (w ∪ (s \ w))).degree
            ⟨va.1, Finset.mem_union.mpr (Or.inl va.2)⟩ =
          (inducedOn G s).degree ⟨va.1, hw va.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (s \ w)) (t := s)
          (h := by rw [Finset.union_comm w, Finset.sdiff_union_of_subset hw])
          (hs := Finset.mem_union.mpr (Or.inl va.2))
          (ht := hw va.2))
    have hcastB :
        (inducedOn G (w ∪ (s \ w))).degree
            ⟨vb.1, Finset.mem_union.mpr (Or.inl vb.2)⟩ =
          (inducedOn G s).degree ⟨vb.1, hw vb.2⟩ := by
      simpa using
        (inducedOn_degree_congr (G := G)
          (s := w ∪ (s \ w)) (t := s)
          (h := by rw [Finset.union_comm w, Finset.sdiff_union_of_subset hw])
          (hs := Finset.mem_union.mpr (Or.inl vb.2))
          (ht := hw vb.2))
    simpa [hcastA, hcastB] using hhost va vb
  have hsplitA :
      (inducedOn G (w ∪ (s \ w))).degree
          ⟨va.1, Finset.mem_union.mpr (Or.inl va.2)⟩ =
        (inducedOn G w).degree va + (G.neighborFinset va ∩ (s \ w)).card := by
    exact degree_union_eq_degree_add_external (G := G) (s := w) (t := s \ w) hdisj va
  have hsplitB :
      (inducedOn G (w ∪ (s \ w))).degree
          ⟨vb.1, Finset.mem_union.mpr (Or.inl vb.2)⟩ =
        (inducedOn G w).degree vb + (G.neighborFinset vb ∩ (s \ w)).card := by
    exact degree_union_eq_degree_add_external (G := G) (s := w) (t := s \ w) hdisj vb
  have hdropAB :
      (G.neighborFinset va ∩ (s \ w)).card ≡
        (G.neighborFinset vb ∩ (s \ w)).card [MOD 2] := by
    have hsum :
        (inducedOn G w).degree va + (G.neighborFinset va ∩ (s \ w)).card ≡
          (inducedOn G w).degree vb + (G.neighborFinset vb ∩ (s \ w)).card [MOD 2] := by
      simpa [hsplitA, hsplitB] using hbigAB
    exact
      Nat.ModEq.add_left_cancel' ((inducedOn G w).degree va) (by simpa [hdegwEq] using hsum)
  intro v w'
  by_cases hvw : v.1 = w'.1
  · have hvw' : v = w' := Subtype.ext hvw
    subst w'
    exact Nat.ModEq.refl ((G.neighborFinset v ∩ (s \ w)).card)
  · have hvCases : v.1 = a ∨ v.1 = b := by
      have hvMem : v.1 ∈ ({a, b} : Finset (Fin n)) := by simpa [hwab] using v.2
      simpa [Finset.mem_insert, Finset.mem_singleton] using hvMem
    have hwCases : w'.1 = a ∨ w'.1 = b := by
      have hwMem : w'.1 ∈ ({a, b} : Finset (Fin n)) := by simpa [hwab] using w'.2
      simpa [Finset.mem_insert, Finset.mem_singleton] using hwMem
    rcases hvCases with hva | hvb
    · rcases hwCases with hwa' | hwb'
      · exact False.elim (hvw (hva.trans hwa'.symm))
      · have hvEq : v = va := Subtype.ext hva
        have hwEq : w' = vb := Subtype.ext hwb'
        subst v
        subst w'
        simpa [va, vb] using hdropAB
    · rcases hwCases with hwa' | hwb'
      · have hvEq : v = vb := Subtype.ext hvb
        have hwEq : w' = va := Subtype.ext hwa'
        subst v
        subst w'
        simpa [va, vb] using hdropAB.symm
      · exact False.elim (hvw (hvb.trans hwb'.symm))

/--
The first dyadic obstruction slice (`q = 2`) is unconditional: any bounded fixed-modulus host witness
at bucket `4` already yields the required dropped-part residue data at bucket `2`.
-/
theorem
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_two_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
    {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G 4 2 r) :
    HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard G 2 2 r := by
  classical
  cases
    Subsingleton.elim (‹DecidableRel G.Adj›)
      (fun a b => Classical.propDecidable (G.Adj a b))
  have href :
      HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard G 2 2 r := by
    exact
      hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard
        (G := G)
        (hasBoundedFixedModulusControlBlockModularHostRefinementDataOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
          (G := G) (q := 2) (k := 2) (by decide) (by decide) hhost)
  rcases href with ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hbig, hctrl, hhost', hext⟩
  refine ⟨w, s, t, hwk, hw, blocks, e, htcard, hlen, hsep, hbig, ?_, hctrl, hhost', hext⟩
  exact modEq_dropDegree_of_card_two (G := G) hwk hw hhost'

/--
The q = 2 dropped-part extraction theorem packaged as a per-modulus slice.
-/
theorem hasDropResidueExtractionAtModulusTwo (r : ℕ) :
    HasDropResidueExtractionAtModulus 2 r := by
  intro n G _ hhost
  exact
    hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_two_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
      (G := G) hhost

/--
The step-self-bridge at positive dyadic modulus reduces to the single combinatorial obstruction
`HasDropResidueExtractionFromHostWitness`.

Proof: given a host witness at bucket `q * q` with `q = 2 ^ j`, apply the obstruction to extract
the drop-data package at bucket `q`, then close with the existing
`hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard`
bridge at `k = q = q` (so `k ≤ q` holds by `le_rfl`), yielding the bounded exact single-control
witness of size `q` with control budget `q - 1`.
-/
theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasDropResidueExtractionFromHostWitness
    {r : ℕ}
    (hext : HasDropResidueExtractionFromHostWitness r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  have hdrop :
      HasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
        G (2 ^ j) (2 ^ j) r :=
    hext (q := 2 ^ j) hq G hhost
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) (k := 2 ^ j) (q := 2 ^ j) (r := r) le_rfl hq hdrop

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
    {r : ℕ}
    (hextract : HasCompletedHostExtractionFromHostWitness r)
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_hasExactCardFixedModulusSingleControlCompletedHostWitnessOfCardWithControlCard_and_hasCompletedHostRegularSelection
      (G := G)
      (hextract (q := 2 ^ j) hq G hhost)
      (hselect hj G)

theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicModulusSquareRegularSelection
    {r : ℕ}
    (hextract : HasCompletedHostExtractionFromHostWitness r)
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge r := by
  exact
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
      (r := r) hextract
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

/--
First dyadic step-exact bridge (`q = 2`): any bounded host witness at bucket `4` already collapses
to a bounded exact single-control witness of size `2`.
-/
theorem hasBoundedFixedModulusControlBlockModularHostStepExactSelfBridge_two
    {n r : ℕ} (G : SimpleGraph (Fin n))
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G 4 2 r) :
    HasBoundedSingleControlExactWitnessOfCard G 2 (2 - 1) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasBoundedSingleControlExactWitnessOfCard_of_card_le_modulus_and_hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard
      (G := G) (k := 2) (q := 2) (r := r) le_rfl (by decide)
      (hasExactCardFixedModulusControlBlockModularHostRefinementDropDataOfCard_two_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard
        (G := G) hhost)

/--
First nontrivial positive-dyadic step slice (`q = 4`): any bounded host witness at bucket `16`
already forces the required exact single-control witness of size `4`.

This uses the finite theorem `hasBoundedSingleControlExactWitnessOfCard_four_of_sixteen_le_card`,
which in turn combines the exact-control recursion with the exhaustive base fact
`4 ∈ admissibleBounds 7`.
-/
theorem hasBoundedFixedModulusControlBlockModularHostStepExactSelfBridge_four
    (hbase : SevenVertexFourRegularBaseCase)
    {n r : ℕ} (G : SimpleGraph (Fin n))
    (hhost : HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G 16 4 r) :
    HasBoundedSingleControlExactWitnessOfCard G 4 (4 - 1) := by
  have hn : 16 ≤ n := by
    rcases hhost with ⟨u, s, h16, hu, _blocks, _hlen, _hnonempty, _hsep, _hdeg, _hext⟩
    exact
      le_trans h16 <|
        le_trans (Finset.card_le_card hu) <|
          by simpa using (Finset.card_le_univ s)
  simpa using
    (hasBoundedSingleControlExactWitnessOfCard_four_of_sixteen_le_card
      hbase (G := G) (r := 4 - 1) (by decide : 1 ≤ 4 - 1) hn)

/--
At `q = 4`, the stripped maximal-control exact-upgrade target is already settled outside the
intermediate range `8 <= n <= 13`: the small-ambient collapse handles `n <= 7`, while the finite
q = 4 exact-witness theorem handles `n >= 14`.
-/
theorem hasExactCardFixedSingleControlHostMaximalControlUpgrade_four_of_card_le_seven_or_fourteen_le
    (hbase : SevenVertexFourRegularBaseCase)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hhost : HasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
      G 4 4 (4 - 1))
    (hcard : n ≤ 7 ∨ 14 ≤ n) :
    HasBoundedSingleControlExactWitnessOfCard G 4 (4 - 1) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hcard with hsmall | hlarge
  · exact
      hasBoundedSingleControlExactWitnessOfCard_of_card_le_add_of_lt_and_hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard
        (G := G) (k := 4) (q := 4) (r := 4 - 1)
        le_rfl (by simpa using hsmall) (by decide) hhost
  · simpa using
      (hasBoundedSingleControlExactWitnessOfCard_four_of_fourteen_le_card
        hbase (G := G) (r := 4 - 1) (by decide : 1 ≤ 4 - 1) hlarge)

/--
The corresponding q = 4 refinement-data exact self-bridge also reduces to the remaining orders
`8 <= n <= 13`.
-/
theorem
    hasBoundedFixedModulusControlBlockModularHostRefinementExactSelfBridge_four_of_card_le_seven_or_fourteen_le
    (hbase : SevenVertexFourRegularBaseCase)
    {n r : ℕ} (G : SimpleGraph (Fin n))
    (href : HasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard G 4 4 r)
    (hcard : n ≤ 7 ∨ 14 ≤ n) :
    HasBoundedSingleControlExactWitnessOfCard G 4 (4 - 1) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasExactCardFixedSingleControlHostMaximalControlUpgrade_four_of_card_le_seven_or_fourteen_le
      hbase
      (G := G)
      (hasExactCardFixedModulusSingleControlModularHostWitnessOfCardWithControlCard_of_hasExactCardFixedModulusControlBlockModularHostRefinementDataOfCard
        (G := G) (by decide) href)
      hcard

theorem
    hasPolynomialCostFixedOneControlHostTerminalRegularization_iff_hasPolynomialCostFixedSingleControlHostTerminalRegularization
    {D : ℕ} :
    HasPolynomialCostFixedOneControlHostTerminalRegularization D ↔
      HasPolynomialCostFixedSingleControlHostTerminalRegularization D := by
  constructor
  · intro h n j G hsingle
    exact
      h G
        (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusSingleControlModularHostWitnessOfCard
          G hsingle)
  · intro h n j G hhost
    exact
      h G
        (hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_one
          G hhost)

theorem hasPolynomialCostFixedSingleControlHostTerminalRegularization_of_zero
    {D : ℕ} (hzero : HasPolynomialCostFixedSingleControlHostTerminalRegularization 0) :
    HasPolynomialCostFixedSingleControlHostTerminalRegularization D := by
  intro n j G hhost
  have hsmall :
      HasFixedModulusSingleControlModularHostWitnessOfCard G (2 ^ j) (2 ^ j) := by
    refine
      hasFixedModulusSingleControlModularHostWitnessOfCard_mono
        (G := G) ?_ hhost
    have hqpos : 0 < 2 ^ j := Nat.pow_pos (by decide : 0 < 2)
    have hpow1 : 1 ≤ (2 ^ j) ^ D := Nat.succ_le_of_lt (Nat.pow_pos hqpos)
    calc
      2 ^ j = 1 * 2 ^ j := by simp
      _ ≤ (2 ^ j) ^ D * 2 ^ j := by
        exact Nat.mul_le_mul_right (2 ^ j) hpow1
  have hsmall' :
      HasFixedModulusSingleControlModularHostWitnessOfCard G ((2 ^ j) ^ 0 * 2 ^ j) (2 ^ j) := by
    simpa using hsmall
  simpa using hzero G hsmall'

/--
The previously stated full bridge immediately implies the weaker self-target version.
-/
theorem hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    HasPolynomialCostEmptyControlTerminalBridge D := by
  classical
  intro n j m G hcascade
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hbridge G hcascade with
    ⟨s, chain, blocks, hkm, hq, hnonempty, hsep, hfrom, hext⟩
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
      G hkm hq hnonempty hsep hfrom hext

/--
Conversely, any terminal control-block modular cascade witness can be shrunk to its terminal bucket,
where the external-block data become explicit.
-/
theorem hasPolynomialCostEmptyControlExternalBlockBridge_of_hasPolynomialCostEmptyControlTerminalBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlTerminalBridge D) :
    HasPolynomialCostEmptyControlExternalBlockBridge D := by
  classical
  intro n j m G hcascade
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases
      exists_terminal_externalBlockData_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
        (G := G) (hbridge G hcascade) with
    ⟨u, blocks, hkm, hq, hnonemptyU, hsepU, huMod, hextU⟩
  refine ⟨u, [], blocks, hkm, hq, hnonemptyU, hsepU, ?_, hextU⟩
  simpa [HasFixedModulusCascadeFrom, InducesModEqDegree] using huMod

/--
So the two empty-control bridge presentations are equivalent.
-/
theorem hasPolynomialCostEmptyControlTerminalBridge_iff_hasPolynomialCostEmptyControlExternalBlockBridge
    {D : ℕ} :
    HasPolynomialCostEmptyControlTerminalBridge D ↔
      HasPolynomialCostEmptyControlExternalBlockBridge D := by
  constructor
  · exact hasPolynomialCostEmptyControlExternalBlockBridge_of_hasPolynomialCostEmptyControlTerminalBridge
  · exact hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge

/--
The previously stated full bridge immediately implies the weaker self-target version.
-/
theorem hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostEmptyControlTerminalBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlTerminalBridge D) :
    HasPolynomialCostEmptyControlTerminalSelfBridge D := by
  intro n j G hcascade
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbridge G hcascade

/--
An empty-control self-bridge is stronger than the fixed-witness self-bridge, since every fixed-modulus
witness is already an empty-control cascade.
-/
theorem hasPolynomialCostFixedWitnessTerminalSelfBridge_of_hasPolynomialCostEmptyControlTerminalSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlTerminalSelfBridge D) :
    HasPolynomialCostFixedWitnessTerminalSelfBridge D := by
  intro n j G hfixed
  exact hbridge G (hasFixedModulusCascadeWitnessOfCard_of_hasFixedModulusWitnessOfCard G hfixed)

/--
The external-block bridge feeds directly into the fixed-witness self-bridge pipeline.
-/
theorem hasPolynomialCostFixedWitnessTerminalSelfBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    HasPolynomialCostFixedWitnessTerminalSelfBridge D := by
  exact
    hasPolynomialCostFixedWitnessTerminalSelfBridge_of_hasPolynomialCostEmptyControlTerminalSelfBridge
      (hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostEmptyControlTerminalBridge
        (hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
          hbridge))

/--
The full empty-control external-block bridge implies the weaker positive-dyadic self-target version.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D := by
  intro n j hj G hfixed
  exact
    hbridge G
      (hasFixedModulusCascadeWitnessOfCard_of_hasFixedModulusWitnessOfCard G hfixed)

/--
The positive-dyadic external-block self-target already yields the positive-dyadic terminal
control-block cascade witness.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D) :
    HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D := by
  intro n j hj G hfixed
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hbridge hj G hfixed with
    ⟨s, chain, blocks, hkm, hq, hnonempty, hsep, hfrom, hext⟩
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
      G hkm hq hnonempty hsep hfrom hext

/--
Conversely, a positive-dyadic terminal cascade self-witness can be shrunk to its terminal bucket,
recovering the external-block self-bridge presentation there.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D := by
  intro n j hj G hfixed
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases
      exists_terminal_externalBlockData_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
        (G := G) (hbridge hj G hfixed) with
    ⟨u, blocks, hkm, hq, hnonemptyU, hsepU, huMod, hextU⟩
  refine ⟨u, [], blocks, hkm, hq, hnonemptyU, hsepU, ?_, hextU⟩
  simpa [HasFixedModulusCascadeFrom, InducesModEqDegree] using huMod

/--
So the two positive-dyadic self-target bridge presentations are equivalent.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_iff_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
    {D : ℕ} :
    HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D ↔
      HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D := by
  constructor
  · exact
      hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
  · exact
      hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge

/--
Because the terminal bucket of an empty-control cascade is already a fixed-modulus witness, a
bridge from fixed witnesses is enough for the dyadic argument.
-/
theorem hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostFixedWitnessTerminalSelfBridge D) :
    HasPolynomialCostEmptyControlTerminalSelfBridge D := by
  intro n j G hcascade
  exact hbridge G (hasFixedModulusWitnessOfCard_of_hasFixedModulusCascadeWitnessOfCard G hcascade)

/--
Any fixed-witness self-bridge immediately yields the corresponding direct regularization statement.
-/
theorem hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostFixedWitnessTerminalSelfBridge D) :
    HasPolynomialCostFixedWitnessTerminalRegularization D := by
  intro n j G hfixed
  exact
    hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
      (hbridge G hfixed)

/--
So the external-block bridge also yields direct terminal regularization in the fixed-witness package.
-/
theorem hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostEmptyControlExternalBlockBridge
    {D : ℕ} (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    HasPolynomialCostFixedWitnessTerminalRegularization D := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
      (hasPolynomialCostFixedWitnessTerminalSelfBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
        hbridge)

/--
So the positive-dyadic external-block self-target also suffices for the full regularization pipeline.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge D) :
    HasPolynomialCostFixedWitnessTerminalRegularization D := by
  intro n j G hfixed
  by_cases hj : j = 0
  · have hfixedOne : HasFixedModulusWitnessOfCard G 1 1 := by
      simpa [hj] using hfixed
    rcases hfixedOne with ⟨s, hs, _hmod⟩
    have hsPos : 0 < s.card := lt_of_lt_of_le (by decide : 0 < 1) hs
    rcases Finset.card_pos.mp hsPos with ⟨v, _hv⟩
    letI : Nonempty (Fin n) := ⟨v⟩
    simpa [hj] using hasRegularInducedSubgraphOfCard_one G
  · exact
      hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
        (hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
          hbridge (Nat.pos_of_ne_zero hj) G hfixed)

/--
The corrected positive-dyadic self-bridge is already enough for full terminal regularization: the
only omitted case is `j = 0`, where the target is the trivial one-vertex regular induced subgraph.
-/
theorem hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
    {D : ℕ} (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D) :
    HasPolynomialCostFixedWitnessTerminalRegularization D := by
  intro n j G hfixed
  by_cases hj : j = 0
  · have hfixedOne : HasFixedModulusWitnessOfCard G 1 1 := by
      simpa [hj] using hfixed
    rcases hfixedOne with ⟨s, hs, _hmod⟩
    have hsPos : 0 < s.card := lt_of_lt_of_le (by decide : 0 < 1) hs
    rcases Finset.card_pos.mp hsPos with ⟨v, _hv⟩
    letI : Nonempty (Fin n) := ⟨v⟩
    simpa [hj] using hasRegularInducedSubgraphOfCard_one G
  · exact
      hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
        (hbridge (Nat.pos_of_ne_zero hj) G hfixed)

/--
A fixed-modulus witness of size `q * ((q^D) * q)` can first be converted to a one-control host
witness of size `(q^D) * q`, so a host-regularization theorem with exponent `D` yields the plain
fixed-witness regularization theorem with exponent `D + 1`.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasPolynomialCostFixedOneControlHostTerminalRegularization
    {D : ℕ} (hhost : HasPolynomialCostFixedOneControlHostTerminalRegularization D) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 1) := by
  intro n j G hfixed
  by_cases hj : j = 0
  · subst hj
    rcases hfixed with ⟨s, hs, _hmod⟩
    have hs' : 1 ≤ s.card := by simpa using hs
    have hspos : 0 < s.card := Nat.succ_le_iff.mp hs'
    have hn : 0 < n := by
      exact lt_of_lt_of_le hspos (by simpa using (Finset.card_le_univ s))
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    simpa using hasRegularInducedSubgraphOfCard_one G
  · rcases Nat.exists_eq_succ_of_ne_zero hj with ⟨r, rfl⟩
    let q : ℕ := 2 ^ (r + 1)
    let m : ℕ := q ^ D * q
    have hq : 1 < q := by
      have hpow1 : 1 ≤ 2 ^ r := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      calc
        1 < 2 := by decide
        _ ≤ 2 ^ r * 2 := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hpow1
        _ = q := by
          simp [q, pow_succ, Nat.mul_comm]
    have hm : 0 < m := by
      exact Nat.mul_pos (Nat.pow_pos (lt_trans (by decide : 0 < 1) hq))
        (lt_trans (by decide : 0 < 1) hq)
    have hfixed' : HasFixedModulusWitnessOfCard G (q * m) q := by
      simpa [q, m, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfixed
    exact
      hhost G
        (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard
          (G := G) hq hm hfixed')

/--
The finite host-iteration lemmas show that the one-control host regularization problem is already
reduced to terminal-size host witnesses, at the cost of growing the control-block budget from `1`
to `D + 1`.
-/
theorem
    hasPolynomialCostFixedOneControlHostTerminalRegularization_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
    {D : ℕ}
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (D + 1)) :
    HasPolynomialCostFixedOneControlHostTerminalRegularization D := by
  intro n j G hhost
  by_cases hj : j = 0
  · subst hj
    have hhost' :
        HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G 1 1 (D + 1) := by
      refine
        hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_le
          (G := G) (r := 1) (r' := D + 1) ?_ ?_
      · omega
      · simpa using hhost
    simpa using (hterm (j := 0) G hhost')
  · rcases Nat.exists_eq_succ_of_ne_zero hj with ⟨r, rfl⟩
    let q : ℕ := 2 ^ (r + 1)
    have hq : 1 < q := by
      have hpow1 : 1 ≤ 2 ^ r := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      calc
        1 < 2 := by decide
        _ ≤ 2 ^ r * 2 := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hpow1
        _ = q := by
          simp [q, pow_succ, Nat.mul_comm]
    have hqpos : 0 < q := lt_trans (by decide : 0 < 1) hq
    have hhost' :
        HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q ^ D * q) q 1 := by
      simpa [q, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhost
    have hterminal :
        HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G q q (D + 1) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_iterate
          (G := G) (q := q) (k := q) (r := 1) (D := D) hq hqpos hhost')
    simpa [q] using hterm G hterminal

/--
Combining terminal bounded-host regularization with the one-control reduction recovers the usual
fixed-witness terminal regularization theorem one exponent later.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
    {D : ℕ}
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 1) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasPolynomialCostFixedOneControlHostTerminalRegularization
      (hasPolynomialCostFixedOneControlHostTerminalRegularization_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
        hterm)

/--
The large-card fixed-witness reduction also isolates the weaker positive-dyadic terminal target: if
terminal bounded host witnesses on `2^j` vertices can already be bridged to the control-block
modular cascade package for every `j > 0`, then the viable positive-dyadic fixed-witness self-bridge
follows one exponent later.
-/
theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    {r : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hterm hj G hhost with
    ⟨s, chain, blocks, hkm, hq, hnonempty, hsep, hfrom, hext⟩
  exact
    hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_hasFixedModulusCascadeFrom_and_modExternalBlockDegrees
      G hkm hq hnonempty hsep hfrom hext

/--
Conversely, a terminal control-block modular cascade witness can be shrunk to its terminal bucket,
recovering the bounded-host external-block self-bridge presentation there.
-/
theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
    {r : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge r) :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge r := by
  intro n j hj G hhost
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases
      exists_terminal_externalBlockData_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
        (G := G) (hterm hj G hhost) with
    ⟨u, blocks, hkm, hq, hnonemptyU, hsepU, huMod, hextU⟩
  refine ⟨u, [], blocks, hkm, hq, hnonemptyU, hsepU, ?_, hextU⟩
  simpa [HasFixedModulusCascadeFrom, InducesModEqDegree] using huMod

/--
So the two bounded-host positive-dyadic terminal bridge presentations are equivalent.
-/
theorem
    hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge_iff_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    {r : ℕ} :
    HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge r ↔
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge r := by
  constructor
  · exact
      hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
  · exact
      hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge

/--
The large-card fixed-witness reduction also isolates the weaker positive-dyadic terminal target: if
terminal bounded host witnesses on `2^j` vertices can already be bridged to the explicit external-block
data package for every `j > 0`, then the viable positive-dyadic fixed-witness external-block
self-bridge follows one exponent later.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    {D : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
        (D + 1)) :
    HasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge (D + 1) := by
  intro n j hj G hfixed
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  have hhost :
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (2 ^ j) (2 ^ j) (D + 1) := by
    exact
      hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard_pow
        (G := G) (q := 2 ^ j) (k := 2 ^ j) (D := D) hq
        (Nat.pow_pos (by decide : 0 < 2)) hfixed
  exact hterm hj G hhost

/--
So the weaker terminal external-block bridge already implies the positive-dyadic terminal cascade
self-bridge one exponent later.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    {D : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
        (D + 1)) :
    HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge (D + 1) := by
  exact
    hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
      (hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
        hterm)

/--
So the weaker terminal external-block bridge already implies the full fixed-witness terminal
regularization theorem one exponent later.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
    {D : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
        (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 1) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge
      (hasPolynomialCostPositiveDyadicFixedWitnessExternalBlockSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalExternalBlockSelfBridge
        hterm)

/--
The large-card fixed-witness reduction also isolates the weaker positive-dyadic terminal target: if
terminal bounded host witnesses on `2^j` vertices can already be bridged to the control-block
modular cascade package for every `j > 0`, then the viable positive-dyadic fixed-witness self-bridge
follows one exponent later.
-/
theorem
    hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
    {D : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge (D + 1)) :
    HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge (D + 1) := by
  intro n j hj G hfixed
  have hq : 1 < 2 ^ j := by
    cases j with
    | zero =>
        cases (Nat.lt_irrefl 0 hj)
    | succ j =>
        have hpow : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
        calc
          1 < 2 := by decide
          _ ≤ 2 * 2 ^ j := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
          _ = 2 ^ Nat.succ j := by simp [Nat.pow_succ, Nat.mul_comm]
  have hhost :
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (2 ^ j) (2 ^ j) (D + 1) := by
    exact
      hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard_pow
        (G := G) (q := 2 ^ j) (k := 2 ^ j) (D := D) hq
        (Nat.pow_pos (by decide : 0 < 2)) hfixed
  exact hterm hj G hhost

/--
So the positive-dyadic bounded-host cascade bridge already implies the full fixed-witness terminal
regularization theorem one exponent later.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
    {D : ℕ}
    (hterm :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 1) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
      (hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicTerminalCascadeBridge
        hterm)

/--
If the positive-dyadic host package can already be upgraded in one step to the fixed-modulus
control-block modular cascade package, then one extra factor of `q` yields terminal regularization.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge
    {D : ℕ}
    (hstep :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepTerminalCascadeSelfBridge
        (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  intro n j G hfixed
  by_cases hj : j = 0
  · have hfixedOne : HasFixedModulusWitnessOfCard G 1 1 := by
      simpa [hj] using hfixed
    rcases hfixedOne with ⟨s, hs, _hmod⟩
    have hsPos : 0 < s.card := lt_of_lt_of_le (by decide : 0 < 1) hs
    rcases Finset.card_pos.mp hsPos with ⟨v, _hv⟩
    letI : Nonempty (Fin n) := ⟨v⟩
    simpa [hj] using hasRegularInducedSubgraphOfCard_one G
  · rcases Nat.exists_eq_succ_of_ne_zero hj with ⟨r, rfl⟩
    let q : ℕ := 2 ^ (r + 1)
    have hq : 1 < q := by
      have hpow : 1 ≤ 2 ^ r := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      calc
        1 < 2 := by decide
        _ ≤ 2 * 2 ^ r := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
        _ = q := by simp [q, Nat.pow_succ, Nat.mul_comm]
    have hqpos : 0 < q := lt_trans (by decide : 0 < 1) hq
    have hhost :
        HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q (D + 1) := by
      exact
        hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard_pow
          (G := G) (q := q) (k := q * q) (D := D) hq (Nat.mul_pos hqpos hqpos)
          (by
            simpa [q, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfixed)
    have hterm : HasFixedModulusControlBlockModularCascadeWitnessOfCard G q q := by
      exact hstep (j := r + 1) (Nat.succ_pos r) G hhost
    simpa [q] using
      hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G hterm

/--
If the positive-dyadic host package can be upgraded in one step to a bounded exact single-control
witness, then one extra factor of `q` already yields terminal regularization.
-/
theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
    {D : ℕ}
    (hstep :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  intro n j G hfixed
  by_cases hj : j = 0
  · have hfixedOne : HasFixedModulusWitnessOfCard G 1 1 := by
      simpa [hj] using hfixed
    rcases hfixedOne with ⟨s, hs, _hmod⟩
    have hsPos : 0 < s.card := lt_of_lt_of_le (by decide : 0 < 1) hs
    rcases Finset.card_pos.mp hsPos with ⟨v, _hv⟩
    letI : Nonempty (Fin n) := ⟨v⟩
    simpa [hj] using hasRegularInducedSubgraphOfCard_one G
  · rcases Nat.exists_eq_succ_of_ne_zero hj with ⟨r, rfl⟩
    let q : ℕ := 2 ^ (r + 1)
    have hq : 1 < q := by
      have hpow : 1 ≤ 2 ^ r := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      calc
        1 < 2 := by decide
        _ ≤ 2 * 2 ^ r := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hpow
        _ = q := by simp [q, Nat.pow_succ, Nat.mul_comm]
    have hqpos : 0 < q := lt_trans (by decide : 0 < 1) hq
    have hhost :
        HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G (q * q) q (D + 1) := by
      exact
        hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_hasFixedModulusWitnessOfCard_pow
          (G := G) (q := q) (k := q * q) (D := D) hq (Nat.mul_pos hqpos hqpos)
          (by
            simpa [q, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfixed)
    have hexact : HasBoundedSingleControlExactWitnessOfCard G q (q - 1) := by
      exact hstep (j := r + 1) (Nat.succ_pos r) G hhost
    simpa [q] using hasRegularInducedSubgraphOfCard_of_hasBoundedSingleControlExactWitnessOfCard G hexact

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {D : ℕ}
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
        (r := D + 1) hupgrade)

theorem hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    HasPolynomialCostFixedWitnessTerminalRegularization 2 := by
  intro n j G hfixed
  simpa using
    (hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      (D := 0) hupgrade G hfixed)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    HasPolynomialCostFixedWitnessTerminalRegularization 2 := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      (hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

/--
Gallai's theorem already proves the empty-control parity base case.
-/
theorem emptyControlDyadicParityBaseCase :
    EmptyControlDyadicParityBaseCase := by
  intro n G
  simpa using hasFixedModulusCascadeWitnessOfCard_two G

/--
Fixed-modulus parity base case suggested by the dyadic note: every graph on `n` vertices already
contains a modulus-`2` modular cascade witness on at least `n / 2` vertices.
-/
def DyadicParityBaseCase : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G (n / 2) 2

/--
Polynomial-cost dyadic lift hypothesis for the fixed-modulus cascade package: a modulus `2^j`
witness of order `(2^j)^C * m` can always be refined to a modulus `2^(j+1)` witness of order `m`.
-/
def HasPolynomialCostDyadicLift (C : ℕ) : Prop :=
  ∀ {n j m : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G ((2 ^ j) ^ C * m) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G m (2 ^ (j + 1))

lemma card_le_modulus_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k q : ℕ}
    (hfixed : HasFixedModulusControlBlockModularCascadeWitnessOfCard G k q) :
    k ≤ q := by
  rcases hfixed with ⟨s, blocks, chain, hk, hq, _hnonempty, _hsep, _hcascade⟩
  exact le_trans hk hq

theorem not_dyadicParityBaseCase : ¬ DyadicParityBaseCase := by
  intro hbase
  let G : SimpleGraph (Fin 6) := ⊥
  have hbound :
      6 / 2 ≤ 2 := by
    simpa using
      card_le_modulus_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G (hbase 6 G)
  norm_num at hbound

/--
How many vertices are needed to force a modulus `2^r` witness of order `m`, assuming the parity base
case and a polynomial-cost dyadic lift of exponent `C`.
-/
def dyadicLiftVertexCost (C : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | r + 2 => (2 ^ (r + 1)) ^ C * dyadicLiftVertexCost C (r + 1)

lemma hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift
    {C n r m : ℕ} (hr : 0 < r) (hbase : EmptyControlDyadicParityBaseCase)
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hsize : dyadicLiftVertexCost C r * m ≤ n) (G : SimpleGraph (Fin n)) :
    HasFixedModulusCascadeWitnessOfCard G m (2 ^ r) := by
  induction r generalizing m with
  | zero =>
      cases hr
  | succ r ih =>
      cases r with
      | zero =>
          have htwo : 2 * m ≤ n := by
            simpa [dyadicLiftVertexCost] using hsize
          have hm : m ≤ n / 2 := by
            exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [Nat.mul_comm] using htwo)
          exact hasFixedModulusCascadeWitnessOfCard_mono G hm (hbase n G)
      | succ r =>
          let m' : ℕ := (2 ^ (r + 1)) ^ C * m
          have hprev : dyadicLiftVertexCost C (r + 1) * m' ≤ n := by
            dsimp [m']
            simpa [dyadicLiftVertexCost, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize
          have hfixedPrev : HasFixedModulusCascadeWitnessOfCard G m' (2 ^ (r + 1)) := by
            exact ih (Nat.succ_pos _) hprev
          simpa [m'] using hlift G hfixedPrev

lemma hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_dyadicLift
    {C n r m : ℕ} (hr : 0 < r) (hbase : DyadicParityBaseCase)
    (hlift : HasPolynomialCostDyadicLift C) (hsize : dyadicLiftVertexCost C r * m ≤ n)
    (G : SimpleGraph (Fin n)) :
    HasFixedModulusControlBlockModularCascadeWitnessOfCard G m (2 ^ r) := by
  induction r generalizing m with
  | zero =>
      cases hr
  | succ r ih =>
      cases r with
      | zero =>
          have htwo : 2 * m ≤ n := by
            simpa [dyadicLiftVertexCost] using hsize
          have hm : m ≤ n / 2 := by
            exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [Nat.mul_comm] using htwo)
          exact hasFixedModulusControlBlockModularCascadeWitnessOfCard_mono G hm (hbase n G)
      | succ r =>
          let m' : ℕ := (2 ^ (r + 1)) ^ C * m
          have hprev : dyadicLiftVertexCost C (r + 1) * m' ≤ n := by
            dsimp [m']
            simpa [dyadicLiftVertexCost, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize
          have hfixedPrev :
              HasFixedModulusControlBlockModularCascadeWitnessOfCard G m' (2 ^ (r + 1)) := by
            exact ih (Nat.succ_pos _) hprev
          simpa [m'] using hlift G hfixedPrev

lemma dyadicLiftVertexCost_le_two_pow_quadratic {C r : ℕ} (hr : 0 < r) :
    dyadicLiftVertexCost C r ≤ 2 ^ (1 + C * r ^ 2) := by
  induction r with
  | zero =>
      cases hr
  | succ r ih =>
      cases r with
      | zero =>
          have hpow : 1 ≤ 2 ^ C := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
          simpa using
            (show dyadicLiftVertexCost C 1 ≤ 2 ^ (1 + C) from by
              calc
                dyadicLiftVertexCost C 1 = 2 := by simp [dyadicLiftVertexCost]
                _ = 2 * 1 := by simp
                _ ≤ 2 * 2 ^ C := Nat.mul_le_mul_left 2 hpow
                _ = 2 ^ (1 + C) := by
                      rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm])
      | succ r =>
          have hprev : dyadicLiftVertexCost C (r + 1) ≤ 2 ^ (1 + C * (r + 1) ^ 2) := by
            exact ih (Nat.succ_pos _)
          calc
            dyadicLiftVertexCost C (r + 2)
                = (2 ^ (r + 1)) ^ C * dyadicLiftVertexCost C (r + 1) := by
                    simp [dyadicLiftVertexCost]
            _ ≤ (2 ^ (r + 1)) ^ C * 2 ^ (1 + C * (r + 1) ^ 2) := by
                  exact Nat.mul_le_mul_left _ hprev
            _ = 2 ^ ((r + 1) * C + (1 + C * (r + 1) ^ 2)) := by
                  rw [← Nat.pow_mul, ← Nat.pow_add]
            _ ≤ 2 ^ (1 + C * (r + 2) ^ 2) := by
                  apply Nat.pow_le_pow_right (by decide : 0 < 2)
                  have hsq :
                      (r + 1) ^ 2 + (r + 1) ≤ (r + 2) ^ 2 := by
                    nlinarith
                  have hmul : C * ((r + 1) ^ 2 + (r + 1)) ≤ C * (r + 2) ^ 2 := by
                    exact Nat.mul_le_mul_left _ hsq
                  have hsum :
                      (r + 1) * C + (1 + C * (r + 1) ^ 2) =
                        1 + C * ((r + 1) ^ 2 + (r + 1)) := by
                    ring
                  rw [hsum]
                  exact Nat.add_le_add_left hmul 1

theorem forcingThreshold_pow_two_le_of_dyadicParityBaseCase_of_polynomialCostDyadicLift
    {C r : ℕ} (hr : 0 < r) (hbase : DyadicParityBaseCase)
    (hlift : HasPolynomialCostDyadicLift C) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + r) := by
  apply forcingThreshold_le_of_le_F
  rw [le_F_iff]
  intro G
  have hsize :
      dyadicLiftVertexCost C r * 2 ^ r ≤ 2 ^ (1 + C * r ^ 2 + r) := by
    calc
      dyadicLiftVertexCost C r * 2 ^ r ≤ 2 ^ (1 + C * r ^ 2) * 2 ^ r := by
        exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hr)
      _ = 2 ^ (1 + C * r ^ 2 + r) := by
        rw [← Nat.pow_add]
  exact
    hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
      (hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_dyadicLift hr hbase hlift hsize G)

private lemma exists_eventually_mul_sq_le_two_pow (A : ℕ) :
    ∃ R : ℕ, ∀ ⦃r : ℕ⦄, R ≤ r → A * (r + 1) ^ 2 ≤ 2 ^ r := by
  by_cases hA : A = 0
  · refine ⟨0, ?_⟩
    intro r hr
    simp [hA]
  · have hlog2 : 0 < Real.log 2 := by
      have htwo : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos htwo
    have htendsto :
        Tendsto (fun x : ℝ => Real.exp (Real.log 2 * x) / x ^ (2 : ℕ)) atTop atTop := by
      simpa using tendsto_exp_mul_div_rpow_atTop (s := (2 : ℝ)) (b := Real.log 2) hlog2
    have hbound :
        ∃ Y : ℝ, ∀ ⦃x : ℝ⦄, Y ≤ x → ((4 * A : ℕ) : ℝ) ≤ Real.exp (Real.log 2 * x) / x ^ (2 : ℕ) := by
      simpa using (Filter.tendsto_atTop.1 htendsto) (((4 * A : ℕ) : ℝ))
    rcases hbound with ⟨Y, hY⟩
    let R : ℕ := max 1 (Nat.ceil Y)
    refine ⟨R, ?_⟩
    intro r hr
    have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    have hYr : Y ≤ (r : ℝ) := by
      have hceil : Y ≤ Nat.ceil Y := Nat.le_ceil _
      exact le_trans hceil <| by
        exact_mod_cast (le_trans (le_max_right _ _) hr)
    have hmain :
        ((A * (r + 1) ^ 2 : ℕ) : ℝ) ≤ Real.exp (Real.log 2 * r) := by
      have hdiv :
          ((4 * A : ℕ) : ℝ) ≤ Real.exp (Real.log 2 * r) / (r : ℝ) ^ (2 : ℕ) := hY hYr
      have hrpow_pos : 0 < (r : ℝ) ^ (2 : ℕ) := by positivity
      have hmul :
          (((4 * A : ℕ) : ℝ) * (r : ℝ) ^ (2 : ℕ)) ≤ Real.exp (Real.log 2 * r) := by
        exact (le_div_iff₀ hrpow_pos).mp hdiv
      have hsquare : ((r + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ 4 * (r : ℝ) ^ (2 : ℕ) := by
        have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        have hsquare' : ((r : ℝ) + 1) ^ (2 : ℕ) ≤ 4 * (r : ℝ) ^ (2 : ℕ) := by
          nlinarith [hr1']
        simpa [Nat.cast_add, Nat.cast_one] using hsquare'
      calc
        ((A * (r + 1) ^ 2 : ℕ) : ℝ) = (A : ℝ) * ((r + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
          norm_num
        _ ≤ (A : ℝ) * (4 * (r : ℝ) ^ (2 : ℕ)) := by
          gcongr
        _ = (((4 * A : ℕ) : ℝ) * (r : ℝ) ^ (2 : ℕ)) := by
          norm_num [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ Real.exp (Real.log 2 * r) := hmul
    have hexp : Real.exp (Real.log 2 * r) = ((2 ^ r : ℕ) : ℝ) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log] <;> norm_num
    have hreal : ((A * (r + 1) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      simpa [hexp] using hmain
    exact_mod_cast hreal

theorem eventualNatPowerDomination_two_of_dyadicParityBaseCase_of_polynomialCostDyadicLift
    {C : ℕ} (hbase : DyadicParityBaseCase) (hlift : HasPolynomialCostDyadicLift C) :
    EventualNatPowerDomination 2 := by
  intro M
  by_cases hM : M = 0
  · refine ⟨0, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    refine ⟨∅, ?_, 0, inducesRegularOfDegree_empty G⟩
    simp [hM]
  · let D : ℕ := C + 2
    have hD : 0 < D := by
      dsimp [D]
      omega
    rcases exists_eventually_mul_sq_le_two_pow (A := 2 * M * D) with ⟨R, hR⟩
    let S : ℕ := max 1 R
    have hS :
        ∀ ⦃r : ℕ⦄, S ≤ r → 2 * M * D * (r + 1) ^ 2 ≤ 2 ^ r := by
      intro r hr
      exact hR (le_trans (le_max_right _ _) hr)
    refine ⟨max D (D * S ^ 2), ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    let r : ℕ := Nat.sqrt (k / D)
    have hkD : D ≤ k := le_trans (le_max_left _ _) hk
    have hdivOne : 1 ≤ k / D := by
      exact (Nat.le_div_iff_mul_le hD).2 (by simpa using hkD)
    have hrS : S ≤ r := by
      apply Nat.le_sqrt.2
      have hmul : D * S ^ 2 ≤ k := by
        exact le_trans (le_max_right _ _) hk
      have hdiv : S ^ 2 ≤ k / D := by
        exact (Nat.le_div_iff_mul_le hD).2 (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
      simpa [r, Nat.pow_two] using hdiv
    have hrPos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) hrS
    have hquadratic : 1 + C * r ^ 2 + r ≤ k := by
      let n : ℕ := k / D
      have hn1 : 1 ≤ n := by
        simpa [n] using hdivOne
      have hrSq : r ^ 2 ≤ k / D := by
        simpa [r] using Nat.sqrt_le' (k / D)
      have hrLeDiv : r ≤ k / D := by
        exact le_trans (by simpa [r] using Nat.sqrt_le_self (k / D)) le_rfl
      have hbound : 1 + C * r ^ 2 + r ≤ 1 + C * n + n := by
        dsimp [n]
        gcongr
      have hstep : 1 + C * n + n ≤ D * n := by
        have h1cn : 1 + C * n ≤ n + C * n := Nat.add_le_add_right hn1 _
        calc
          1 + C * n + n ≤ n + C * n + n := Nat.add_le_add_right h1cn _
          _ = D * n := by
              dsimp [D]
              ring
      have hkn : D * n ≤ k := by
        dsimp [n]
        exact Nat.mul_div_le k D
      exact le_trans hbound (le_trans hstep hkn)
    have hsize : M * k ≤ 2 ^ r := by
      have hkSmall : k ≤ 2 * D * (r + 1) ^ 2 := by
        let n : ℕ := k / D
        let t : ℕ := (r + 1) ^ 2
        have hnLt : n < t := by
          simpa [n, t, r] using Nat.lt_succ_sqrt' (k / D)
        have hmodLt : k % D < D := Nat.mod_lt _ hD
        have hEq : k = D * n + k % D := by
          simpa [n] using (Nat.div_add_mod k D).symm
        have hkAux : k < D * t + D := by
          rw [hEq]
          exact add_lt_add (Nat.mul_lt_mul_of_pos_left hnLt hD) hmodLt
        have htOne : 1 ≤ t := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos r))
        have hDle : D ≤ D * t := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left D htOne
        have hsum : D * t + D ≤ 2 * D * t := by
          calc
            D * t + D ≤ D * t + D * t := by
              exact Nat.add_le_add_left hDle _
            _ = 2 * D * t := by
              ring
        exact le_trans (Nat.le_of_lt hkAux) hsum
      have hkBound : M * k ≤ 2 * M * D * (r + 1) ^ 2 := by
        calc
          M * k ≤ M * (2 * D * (r + 1) ^ 2) := Nat.mul_le_mul_left _ hkSmall
          _ = 2 * M * D * (r + 1) ^ 2 := by
              ring
      exact le_trans hkBound (hS hrS)
    have hrequired : dyadicLiftVertexCost C r * 2 ^ r ≤ 2 ^ k := by
      calc
        dyadicLiftVertexCost C r * 2 ^ r ≤ 2 ^ (1 + C * r ^ 2) * 2 ^ r := by
          exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hrPos)
        _ = 2 ^ (1 + C * r ^ 2 + r) := by
          rw [← Nat.pow_add]
        _ ≤ 2 ^ k := by
          exact Nat.pow_le_pow_right (by decide : 0 < 2) hquadratic
    have hfixed :
        HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ r) (2 ^ r) := by
      exact
        hasFixedModulusControlBlockModularCascadeWitnessOfCard_of_dyadicLift hrPos hbase hlift
          hrequired G
    rcases
        hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
          hfixed with
      ⟨s, hs, d, hsreg⟩
    exact ⟨s, le_trans hsize hs, d, hsreg⟩

theorem targetStatement_of_dyadicParityBaseCase_of_polynomialCostDyadicLift
    {C : ℕ} (hbase : DyadicParityBaseCase) (hlift : HasPolynomialCostDyadicLift C) :
    TargetStatement := by
  have hpow :
      EventualNatPowerDomination 2 := by
    exact eventualNatPowerDomination_two_of_dyadicParityBaseCase_of_polynomialCostDyadicLift
      hbase hlift
  exact
    (eventualNatPowerDomination_iff_targetStatement (b := 2) (by decide : 1 < 2)).mp hpow

/--
Corrected dyadic reduction: Gallai's true empty-control parity base case, together with a
polynomial-cost empty-control dyadic lift and a polynomial-cost bridge from the empty-control
package to the terminal-capped control-block modular cascade package, already forces the `2^r`
thresholds to be subexponential.
-/
theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalBridge D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  apply forcingThreshold_le_of_le_F
  rw [le_F_iff]
  intro G
  have hsize :
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
        2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
    calc
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
          2 ^ (1 + C * r ^ 2) * ((2 ^ r) ^ D * 2 ^ r) := by
            exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hr)
      _ = 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
            rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
            congr 1
            ring
  have hempty :
      HasFixedModulusCascadeWitnessOfCard G ((2 ^ r) ^ D * 2 ^ r) (2 ^ r) := by
    exact
      hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift hr
        emptyControlDyadicParityBaseCase hlift hsize G
  have hfixed :
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ r) (2 ^ r) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbridge G hempty
  exact
    hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
      hfixed

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalBridge D) :
    EventualNatPowerDomination 2 := by
  intro M
  by_cases hM : M = 0
  · refine ⟨0, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    refine ⟨∅, ?_, 0, inducesRegularOfDegree_empty G⟩
    simp [hM]
  · let E : ℕ := C + D + 2
    have hE : 0 < E := by
      dsimp [E]
      omega
    rcases exists_eventually_mul_sq_le_two_pow (A := 2 * M * E) with ⟨R, hR⟩
    let S : ℕ := max 1 R
    have hS :
        ∀ ⦃r : ℕ⦄, S ≤ r → 2 * M * E * (r + 1) ^ 2 ≤ 2 ^ r := by
      intro r hr
      exact hR (le_trans (le_max_right _ _) hr)
    refine ⟨max E (E * S ^ 2), ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    let r : ℕ := Nat.sqrt (k / E)
    have hkE : E ≤ k := le_trans (le_max_left _ _) hk
    have hdivOne : 1 ≤ k / E := by
      exact (Nat.le_div_iff_mul_le hE).2 (by simpa using hkE)
    have hrS : S ≤ r := by
      apply Nat.le_sqrt.2
      have hmul : E * S ^ 2 ≤ k := by
        exact le_trans (le_max_right _ _) hk
      have hdiv : S ^ 2 ≤ k / E := by
        exact (Nat.le_div_iff_mul_le hE).2
          (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
      simpa [r, Nat.pow_two] using hdiv
    have hrPos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) hrS
    have hquadratic : 1 + C * r ^ 2 + (D + 1) * r ≤ k := by
      let n : ℕ := k / E
      have hn1 : 1 ≤ n := by
        simpa [n] using hdivOne
      have hbound : 1 + C * r ^ 2 + (D + 1) * r ≤ 1 + C * n + (D + 1) * n := by
        dsimp [n]
        gcongr
        · simpa [r] using Nat.sqrt_le' (k / E)
        · exact le_trans (by simpa [r] using Nat.sqrt_le_self (k / E)) le_rfl
      have hstep : 1 + C * n + (D + 1) * n ≤ E * n := by
        have h1cn : 1 + C * n ≤ n + C * n := Nat.add_le_add_right hn1 _
        calc
          1 + C * n + (D + 1) * n ≤ n + C * n + (D + 1) * n := Nat.add_le_add_right h1cn _
          _ = E * n := by
                dsimp [E]
                ring
      have hkn : E * n ≤ k := by
        dsimp [n]
        exact Nat.mul_div_le k E
      exact le_trans hbound (le_trans hstep hkn)
    have hsize : M * k ≤ 2 ^ r := by
      have hkSmall : k ≤ 2 * E * (r + 1) ^ 2 := by
        let n : ℕ := k / E
        let t : ℕ := (r + 1) ^ 2
        have hnLt : n < t := by
          simpa [n, t, r] using Nat.lt_succ_sqrt' (k / E)
        have hmodLt : k % E < E := Nat.mod_lt _ hE
        have hEq : k = E * n + k % E := by
          simpa [n] using (Nat.div_add_mod k E).symm
        have hkAux : k < E * t + E := by
          rw [hEq]
          exact add_lt_add (Nat.mul_lt_mul_of_pos_left hnLt hE) hmodLt
        have htOne : 1 ≤ t := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos r))
        have hEle : E ≤ E * t := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left E htOne
        have hsum : E * t + E ≤ 2 * E * t := by
          calc
            E * t + E ≤ E * t + E * t := by
              exact Nat.add_le_add_left hEle _
            _ = 2 * E * t := by
              ring
        exact le_trans (Nat.le_of_lt hkAux) hsum
      have hkBound : M * k ≤ 2 * M * E * (r + 1) ^ 2 := by
        calc
          M * k ≤ M * (2 * E * (r + 1) ^ 2) := Nat.mul_le_mul_left _ hkSmall
          _ = 2 * M * E * (r + 1) ^ 2 := by
                ring
      exact le_trans hkBound (hS hrS)
    have hthreshold : forcingThreshold (2 ^ r) ≤ 2 ^ k := by
      have hpow :
          forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
        exact
          forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
            (C := C) (D := D) hrPos hlift hbridge
      exact le_trans hpow (Nat.pow_le_pow_right (by decide : 0 < 2) hquadratic)
    have hkF : 2 ^ r ≤ F (2 ^ k) := by
      exact le_F_of_forcingThreshold_le hthreshold
    rw [le_F_iff] at hkF
    rcases hkF G with ⟨s, hs, d, hsreg⟩
    exact ⟨s, le_trans hsize hs, d, hsreg⟩

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalBridge D) :
    TargetStatement := by
  have hpow :
      EventualNatPowerDomination 2 := by
    exact
      eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
        hlift hbridge
  exact
    (eventualNatPowerDomination_iff_targetStatement (b := 2) (by decide : 1 < 2)).mp hpow

theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalSelfBridge D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  apply forcingThreshold_le_of_le_F
  rw [le_F_iff]
  intro G
  have hsize :
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
        2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
    calc
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
          2 ^ (1 + C * r ^ 2) * ((2 ^ r) ^ D * 2 ^ r) := by
            exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hr)
      _ = 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
            rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
            congr 1
            ring
  have hempty :
      HasFixedModulusCascadeWitnessOfCard G ((2 ^ r) ^ D * 2 ^ r) (2 ^ r) := by
    exact
      hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift hr
        emptyControlDyadicParityBaseCase hlift hsize G
  have hfixed :
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ r) (2 ^ r) := by
    exact hbridge G hempty
  exact
    hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
      hfixed

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalSelfBridge D) :
    EventualNatPowerDomination 2 := by
  intro M
  by_cases hM : M = 0
  · refine ⟨0, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    refine ⟨∅, ?_, 0, inducesRegularOfDegree_empty G⟩
    simp [hM]
  · let E : ℕ := C + D + 2
    have hE : 0 < E := by
      dsimp [E]
      omega
    rcases exists_eventually_mul_sq_le_two_pow (A := 2 * M * E) with ⟨R, hR⟩
    let S : ℕ := max 1 R
    have hS :
        ∀ ⦃r : ℕ⦄, S ≤ r → 2 * M * E * (r + 1) ^ 2 ≤ 2 ^ r := by
      intro r hr
      exact hR (le_trans (le_max_right _ _) hr)
    refine ⟨max E (E * S ^ 2), ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    let r : ℕ := Nat.sqrt (k / E)
    have hkE : E ≤ k := le_trans (le_max_left _ _) hk
    have hdivOne : 1 ≤ k / E := by
      exact (Nat.le_div_iff_mul_le hE).2 (by simpa using hkE)
    have hrS : S ≤ r := by
      apply Nat.le_sqrt.2
      have hmul : E * S ^ 2 ≤ k := by
        exact le_trans (le_max_right _ _) hk
      have hdiv : S ^ 2 ≤ k / E := by
        exact (Nat.le_div_iff_mul_le hE).2
          (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
      simpa [r, Nat.pow_two] using hdiv
    have hrPos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) hrS
    have hquadratic : 1 + C * r ^ 2 + (D + 1) * r ≤ k := by
      let n : ℕ := k / E
      have hn1 : 1 ≤ n := by
        simpa [n] using hdivOne
      have hrSq : r ^ 2 ≤ k / E := by
        simpa [r] using Nat.sqrt_le' (k / E)
      have hrLeDiv : r ≤ k / E := by
        exact le_trans (by simpa [r] using Nat.sqrt_le_self (k / E)) le_rfl
      have hbound : 1 + C * r ^ 2 + (D + 1) * r ≤ 1 + C * n + (D + 1) * n := by
        dsimp [n]
        gcongr
      have hstep : 1 + C * n + (D + 1) * n ≤ E * n := by
        have h1cn : 1 + C * n ≤ n + C * n := Nat.add_le_add_right hn1 _
        calc
          1 + C * n + (D + 1) * n ≤ n + C * n + (D + 1) * n := Nat.add_le_add_right h1cn _
          _ = E * n := by
              dsimp [E]
              ring
      have hkn : E * n ≤ k := by
        dsimp [n]
        exact Nat.mul_div_le k E
      exact le_trans hbound (le_trans hstep hkn)
    have hsize : M * k ≤ 2 ^ r := by
      have hkSmall : k ≤ 2 * E * (r + 1) ^ 2 := by
        let n : ℕ := k / E
        let t : ℕ := (r + 1) ^ 2
        have hnLt : n < t := by
          simpa [n, t, r] using Nat.lt_succ_sqrt' (k / E)
        have hmodLt : k % E < E := Nat.mod_lt _ hE
        have hEq : k = E * n + k % E := by
          simpa [n] using (Nat.div_add_mod k E).symm
        have hkAux : k < E * t + E := by
          rw [hEq]
          exact add_lt_add (Nat.mul_lt_mul_of_pos_left hnLt hE) hmodLt
        have htOne : 1 ≤ t := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos r))
        have hEle : E ≤ E * t := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left E htOne
        have hsum : E * t + E ≤ 2 * E * t := by
          calc
            E * t + E ≤ E * t + E * t := by
              exact Nat.add_le_add_left hEle _
            _ = 2 * E * t := by
              ring
        exact le_trans (Nat.le_of_lt hkAux) hsum
      have hkBound : M * k ≤ 2 * M * E * (r + 1) ^ 2 := by
        calc
          M * k ≤ M * (2 * E * (r + 1) ^ 2) := Nat.mul_le_mul_left _ hkSmall
          _ = 2 * M * E * (r + 1) ^ 2 := by
              ring
      exact le_trans hkBound (hS hrS)
    have hrequired : dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤ 2 ^ k := by
      calc
        dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
            2 ^ (1 + C * r ^ 2) * ((2 ^ r) ^ D * 2 ^ r) := by
              exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hrPos)
        _ = 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
              rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
              congr 1
              ring
        _ ≤ 2 ^ k := by
              exact Nat.pow_le_pow_right (by decide : 0 < 2) hquadratic
    have hfixed :
        HasFixedModulusControlBlockModularCascadeWitnessOfCard G (2 ^ r) (2 ^ r) := by
      exact
        hbridge G
          (hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift hrPos
            emptyControlDyadicParityBaseCase hlift hrequired G)
    rcases
        hasRegularInducedSubgraphOfCard_of_hasFixedModulusControlBlockModularCascadeWitnessOfCard G
          hfixed with
      ⟨s, hs, d, hsreg⟩
    exact ⟨s, le_trans hsize hs, d, hsreg⟩

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlTerminalSelfBridge D) :
    TargetStatement := by
  have hpow :
      EventualNatPowerDomination 2 := by
    exact
      eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
        hlift hbridge
  exact
    (eventualNatPowerDomination_iff_targetStatement (b := 2) (by decide : 1 < 2)).mp hpow

theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlExternalBlockBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
      hr hlift
      (hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
        hbridge)

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlExternalBlockBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
      hlift
      (hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
        hbridge)

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlExternalBlockBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostEmptyControlExternalBlockBridge D) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalBridge
      hlift
      (hasPolynomialCostEmptyControlTerminalBridge_of_hasPolynomialCostEmptyControlExternalBlockBridge
        hbridge)

theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalSelfBridge D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
      hr hlift
      (hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
        hbridge)

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalSelfBridge D) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
      hlift
      (hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
        hbridge)

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalSelfBridge D) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlTerminalSelfBridge
      hlift
      (hasPolynomialCostEmptyControlTerminalSelfBridge_of_hasPolynomialCostFixedWitnessTerminalSelfBridge
        hbridge)

theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalRegularization D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  apply forcingThreshold_le_of_le_F
  rw [le_F_iff]
  intro G
  have hsize :
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
        2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
    calc
      dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
          2 ^ (1 + C * r ^ 2) * ((2 ^ r) ^ D * 2 ^ r) := by
            exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hr)
      _ = 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
            rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
            congr 1
            ring
  have hempty :
      HasFixedModulusCascadeWitnessOfCard G ((2 ^ r) ^ D * 2 ^ r) (2 ^ r) := by
    exact
      hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift hr
        emptyControlDyadicParityBaseCase hlift hsize G
  exact
    hbridge G (hasFixedModulusWitnessOfCard_of_hasFixedModulusCascadeWitnessOfCard G hempty)

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalRegularization D) :
    EventualNatPowerDomination 2 := by
  intro M
  by_cases hM : M = 0
  · refine ⟨0, ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    refine ⟨∅, ?_, 0, inducesRegularOfDegree_empty G⟩
    simp [hM]
  · let E : ℕ := C + D + 2
    have hE : 0 < E := by
      dsimp [E]
      omega
    rcases exists_eventually_mul_sq_le_two_pow (A := 2 * M * E) with ⟨R, hR⟩
    let S : ℕ := max 1 R
    have hS :
        ∀ ⦃r : ℕ⦄, S ≤ r → 2 * M * E * (r + 1) ^ 2 ≤ 2 ^ r := by
      intro r hr
      exact hR (le_trans (le_max_right _ _) hr)
    refine ⟨max E (E * S ^ 2), ?_⟩
    intro k hk
    rw [le_F_iff]
    intro G
    let r : ℕ := Nat.sqrt (k / E)
    have hkE : E ≤ k := le_trans (le_max_left _ _) hk
    have hdivOne : 1 ≤ k / E := by
      exact (Nat.le_div_iff_mul_le hE).2 (by simpa using hkE)
    have hrS : S ≤ r := by
      apply Nat.le_sqrt.2
      have hmul : E * S ^ 2 ≤ k := by
        exact le_trans (le_max_right _ _) hk
      have hdiv : S ^ 2 ≤ k / E := by
        exact (Nat.le_div_iff_mul_le hE).2
          (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
      simpa [r, Nat.pow_two] using hdiv
    have hrPos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) hrS
    have hquadratic : 1 + C * r ^ 2 + (D + 1) * r ≤ k := by
      let n : ℕ := k / E
      have hn1 : 1 ≤ n := by
        simpa [n] using hdivOne
      have hrSq : r ^ 2 ≤ k / E := by
        simpa [r] using Nat.sqrt_le' (k / E)
      have hrLeDiv : r ≤ k / E := by
        exact le_trans (by simpa [r] using Nat.sqrt_le_self (k / E)) le_rfl
      have hbound : 1 + C * r ^ 2 + (D + 1) * r ≤ 1 + C * n + (D + 1) * n := by
        dsimp [n]
        gcongr
      have hstep : 1 + C * n + (D + 1) * n ≤ E * n := by
        have h1cn : 1 + C * n ≤ n + C * n := Nat.add_le_add_right hn1 _
        calc
          1 + C * n + (D + 1) * n ≤ n + C * n + (D + 1) * n := Nat.add_le_add_right h1cn _
          _ = E * n := by
              dsimp [E]
              ring
      have hkn : E * n ≤ k := by
        dsimp [n]
        exact Nat.mul_div_le k E
      exact le_trans hbound (le_trans hstep hkn)
    have hsize : M * k ≤ 2 ^ r := by
      have hkSmall : k ≤ 2 * E * (r + 1) ^ 2 := by
        let n : ℕ := k / E
        let t : ℕ := (r + 1) ^ 2
        have hnLt : n < t := by
          simpa [n, t, r] using Nat.lt_succ_sqrt' (k / E)
        have hmodLt : k % E < E := Nat.mod_lt _ hE
        have hEq : k = E * n + k % E := by
          simpa [n] using (Nat.div_add_mod k E).symm
        have hkAux : k < E * t + E := by
          rw [hEq]
          exact add_lt_add (Nat.mul_lt_mul_of_pos_left hnLt hE) hmodLt
        have htOne : 1 ≤ t := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos r))
        have hEle : E ≤ E * t := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left E htOne
        have hsum : E * t + E ≤ 2 * E * t := by
          calc
            E * t + E ≤ E * t + E * t := by
              exact Nat.add_le_add_left hEle _
            _ = 2 * E * t := by
              ring
        exact le_trans (Nat.le_of_lt hkAux) hsum
      have hkBound : M * k ≤ 2 * M * E * (r + 1) ^ 2 := by
        calc
          M * k ≤ M * (2 * E * (r + 1) ^ 2) := Nat.mul_le_mul_left _ hkSmall
          _ = 2 * M * E * (r + 1) ^ 2 := by
              ring
      exact le_trans hkBound (hS hrS)
    have hrequired : dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤ 2 ^ k := by
      calc
        dyadicLiftVertexCost C r * ((2 ^ r) ^ D * 2 ^ r) ≤
            2 ^ (1 + C * r ^ 2) * ((2 ^ r) ^ D * 2 ^ r) := by
              exact Nat.mul_le_mul_right _ (dyadicLiftVertexCost_le_two_pow_quadratic hrPos)
        _ = 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
              rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
              congr 1
              ring
        _ ≤ 2 ^ k := by
              exact Nat.pow_le_pow_right (by decide : 0 < 2) hquadratic
    have hreg :
        HasRegularInducedSubgraphOfCard G (2 ^ r) := by
      exact
        hbridge G
          (hasFixedModulusWitnessOfCard_of_hasFixedModulusCascadeWitnessOfCard G
            (hasFixedModulusCascadeWitnessOfCard_of_emptyControlDyadicLift hrPos
              emptyControlDyadicParityBaseCase hlift hrequired G))
    rcases hreg with ⟨s, hs, d, hsreg⟩
    exact ⟨s, le_trans hsize hs, d, hsreg⟩

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostFixedWitnessTerminalRegularization D) :
    TargetStatement := by
  have hpow :
      EventualNatPowerDomination 2 := by
    exact
      eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
        hlift hbridge
  exact
    (eventualNatPowerDomination_iff_targetStatement (b := 2) (by decide : 1 < 2)).mp hpow

theorem forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 1) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hr hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
        hbridge)

theorem eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
        hbridge)

theorem targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge : HasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge D) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_of_hasPolynomialCostPositiveDyadicFixedWitnessTerminalSelfBridge
        hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 2) * r) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      (C := C) (D := D + 1) hr hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
        hterm))

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
        hterm)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization
        hterm)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hstep :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      (C := C) (D := D + 2) hr hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
        hstep))

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hstep :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
        hstep)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hstep :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
        hstep)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
    {D : ℕ}
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
        (r := D + 1) hextract hselect)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hr hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
        (r := D + 1) hextract hselect)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
        (r := D + 1) hextract hselect)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicCompletedHostRegularSelection) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
        (r := D + 1) hextract hselect)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicModulusSquareRegularSelection
    {D : ℕ}
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
      hextract
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicModulusSquareRegularSelection
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
      hr hlift hextract
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicModulusSquareRegularSelection
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
      hlift hextract
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicModulusSquareRegularSelection
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hextract : HasCompletedHostExtractionFromHostWitness (D + 1))
    (hselect : HasPositiveDyadicModulusSquareRegularSelection) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasCompletedHostExtractionFromHostWitness_and_hasPositiveDyadicCompletedHostRegularSelection
      hlift hextract
      (hasPositiveDyadicCompletedHostRegularSelection_of_hasPositiveDyadicModulusSquareRegularSelection
        hselect)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {D : ℕ}
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1))
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := D + 1) hdiv hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1))
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hr hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := D + 1) hdiv hbridge)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1))
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := D + 1) hdiv hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1))
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge_and_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilityToTerminalSelfBridge
        (r := D + 1) hdiv hbridge)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    {D : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
        hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hr hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
        hbridge)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
        hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicStepExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
        hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
        hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
        (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
        hbridge)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {D : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hr hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementSmallAmbientSelfBridge
        hbridge)

theorem
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {D : ℕ}
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge (D + 1)) :
    HasPolynomialCostFixedWitnessTerminalRegularization (D + 2) := by
  exact
    hasPolynomialCostFixedWitnessTerminalRegularization_succ_succ_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
        hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {C D r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge (D + 1)) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + (D + 3) * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hr hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
        hbridge)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge (D + 1)) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
        hbridge)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
    {C D : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge (D + 1)) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDropSelfBridge
        hbridge)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {C r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + 3 * r) := by
  simpa using
    (forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      (C := C) (D := 2) hr hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
        hupgrade))

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {C : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
        hupgrade)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
    {C : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlUpgrade) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostFixedWitnessTerminalRegularization
      hlift
      (hasPolynomialCostFixedWitnessTerminalRegularization_two_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
        hupgrade)

theorem
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    {C r : ℕ} (hr : 0 < r) (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (1 + C * r ^ 2 + 3 * r) := by
  exact
    forcingThreshold_pow_two_le_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      hr hlift
      (hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

theorem
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    {C : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_emptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      hlift
      (hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

theorem
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
    {C : ℕ} (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hupgrade : HasExactCardFixedSingleControlHostMaximalControlResidueUpgrade) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasExactCardFixedSingleControlHostMaximalControlUpgrade
      hlift
      (hasExactCardFixedSingleControlHostMaximalControlUpgrade_of_hasExactCardFixedSingleControlHostMaximalControlResidueUpgrade
        hupgrade)

theorem
    forcingThreshold_pow_two_le_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
    {r : ℕ} (hr : 0 < r)
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (4 * r) := by
  let q : ℕ := 2 ^ r
  have hq : 1 < q := by
    have hpow1 : 1 ≤ 2 ^ (r - 1) := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
    calc
      1 < 2 := by decide
      _ ≤ 2 ^ (r - 1) * 2 := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 hpow1
      _ = q := by
        rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨m, hm⟩
        subst hm
        simp [q, pow_succ, Nat.mul_comm]
  have hsize :
      q * q * q + (q - 1) ≤ 2 ^ (4 * r) := by
    have hq0 : 0 < q := lt_trans (by decide : 0 < 1) hq
    have hqcube : q * q * q = 2 ^ (3 * r) := by
      dsimp [q]
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      ring
    have hqle : q ≤ 2 ^ (3 * r) := by
      dsimp [q]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hlt :
        q * q * q + (q - 1) < 2 ^ (3 * r + 1) := by
      calc
        q * q * q + (q - 1) < q * q * q + q := by
          exact Nat.add_lt_add_left (Nat.sub_lt hq0 (by decide : 0 < 1)) _
        _ ≤ 2 ^ (3 * r) + 2 ^ (3 * r) := by
          rw [hqcube]
          exact Nat.add_le_add le_rfl hqle
        _ = 2 ^ (3 * r + 1) := by
          rw [← two_mul]
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (3 * r)).symm
    exact
      le_trans (Nat.le_of_lt hlt)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  apply forcingThreshold_le_of_le_F
  rw [le_F_iff]
  intro G
  exact
    hterm (j := r) G
      (hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_of_large_card
        (G := G) hq
        (by simpa [q, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize))

theorem
    eventualNatPowerDomination_two_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1) :
    EventualNatPowerDomination 2 := by
  intro M
  rcases exists_eventually_mul_sq_le_two_pow (A := 4 * M) with ⟨R, hR⟩
  let S : ℕ := max 1 R
  refine ⟨4 * S, ?_⟩
  intro k hk
  rw [le_F_iff]
  intro G
  let r : ℕ := k / 4
  have hrS : S ≤ r := by
    exact
      (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
        (by simpa [S, Nat.mul_comm] using hk)
  have hrPos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left 1 R)) hrS
  have hthreshold : forcingThreshold (2 ^ r) ≤ 2 ^ k := by
    calc
      forcingThreshold (2 ^ r) ≤ 2 ^ (4 * r) := by
        exact
          forcingThreshold_pow_two_le_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
            hrPos hterm
      _ ≤ 2 ^ k := by
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by
          dsimp [r]
          exact Nat.mul_div_le k 4)
  have hkF : 2 ^ r ≤ F (2 ^ k) := le_F_of_forcingThreshold_le hthreshold
  have hsize : M * k ≤ 2 ^ r := by
    have hkSmall : k ≤ 4 * (r + 1) := by
      have hEq : k = 4 * r + k % 4 := by
        dsimp [r]
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod k 4).symm
      have hkAux : k < 4 * r + 4 := by
        rw [hEq]
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_lt_add_left (Nat.mod_lt k (by decide : 0 < 4)) (4 * r)
      simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.le_of_lt hkAux
    have hkBound : M * k ≤ 4 * M * (r + 1) := by
      calc
        M * k ≤ M * (4 * (r + 1)) := Nat.mul_le_mul_left _ hkSmall
        _ = 4 * M * (r + 1) := by ring
    have hsq :
        4 * M * (r + 1) ≤ 4 * M * (r + 1) ^ 2 := by
      have hone : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hsquare : r + 1 ≤ (r + 1) ^ 2 := by
        calc
          r + 1 = (r + 1) * 1 := by rw [Nat.mul_one]
          _ ≤ (r + 1) * (r + 1) := Nat.mul_le_mul_left _ hone
          _ = (r + 1) ^ 2 := by rw [pow_two]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_left (4 * M) hsquare
    have hpow : 4 * M * (r + 1) ^ 2 ≤ 2 ^ r := by
      exact hR (le_trans (le_max_right 1 R) hrS)
    exact le_trans hkBound (le_trans hsq hpow)
  exact (le_F_iff.mp (le_trans hsize hkF)) G

theorem
    targetStatement_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
    (hterm : HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1) :
    TargetStatement := by
  exact
    (eventualNatPowerDomination_iff_targetStatement (b := 2) (by decide : 1 < 2)).mp
      (eventualNatPowerDomination_two_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
        hterm)

theorem
    hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
    (hhost : HasPolynomialCostFixedSingleControlHostTerminalRegularization 0) :
    HasBoundedFixedModulusControlBlockModularHostTerminalRegularization 1 := by
  intro n j G hctrl
  have hctrl' :
      HasBoundedFixedModulusControlBlockModularHostWitnessOfCard G ((2 ^ j) ^ 0 * 2 ^ j) (2 ^ j) 1 := by
    simpa using hctrl
  simpa using
    hhost G
      (hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasBoundedFixedModulusControlBlockModularHostWitnessOfCard_one
        G hctrl')

theorem forcingThreshold_pow_two_le_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
    {r : ℕ} (hr : 0 < r)
    (hhost : HasPolynomialCostFixedSingleControlHostTerminalRegularization 0) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (4 * r) := by
  exact
    forcingThreshold_pow_two_le_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
      hr
      (hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
        hhost)

theorem eventualNatPowerDomination_two_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
    (hhost : HasPolynomialCostFixedSingleControlHostTerminalRegularization 0) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
      (hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
        hhost)

theorem targetStatement_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
    (hhost : HasPolynomialCostFixedSingleControlHostTerminalRegularization 0) :
    TargetStatement := by
  exact
    targetStatement_of_hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one
      (hasBoundedFixedModulusControlBlockModularHostTerminalRegularization_one_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
        hhost)

theorem
    hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization :
    HasPolynomialCostFixedSingleControlHostTerminalRegularization 0 ↔
      HasExactCardFixedSingleControlHostTerminalRegularization := by
  constructor
  · intro h n j G hhost
    have hhost' :
        HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G ((2 ^ j) ^ 0 * 2 ^ j) (2 ^ j) := by
      simpa using hhost
    exact
      h G
        (hasFixedModulusSingleControlModularHostWitnessOfCard_of_hasExactCardFixedModulusSingleControlModularHostWitnessOfCard
          G hhost')
  · intro h n j G hhost
    have hhost' :
        HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G ((2 ^ j) ^ 0 * 2 ^ j) (2 ^ j) := by
      exact
        hasExactCardFixedModulusSingleControlModularHostWitnessOfCard_of_hasFixedModulusSingleControlModularHostWitnessOfCard
          G hhost
    have hhost'' :
        HasExactCardFixedModulusSingleControlModularHostWitnessOfCard G (2 ^ j) (2 ^ j) := by
      simpa using hhost'
    simpa using h G hhost''

theorem targetStatement_of_hasExactCardFixedSingleControlHostTerminalRegularization
    (hhost : HasExactCardFixedSingleControlHostTerminalRegularization) :
    TargetStatement := by
  exact
    targetStatement_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
      ((hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization).2
        hhost)

theorem forcingThreshold_pow_two_le_of_hasExactCardFixedSingleControlHostTerminalRegularization
    {r : ℕ} (hr : 0 < r)
    (hhost : HasExactCardFixedSingleControlHostTerminalRegularization) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (4 * r) := by
  exact
    forcingThreshold_pow_two_le_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
      hr
      ((hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization).2
        hhost)

theorem eventualNatPowerDomination_two_of_hasExactCardFixedSingleControlHostTerminalRegularization
    (hhost : HasExactCardFixedSingleControlHostTerminalRegularization) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_polynomialCostFixedSingleControlHostTerminalRegularization_zero
      ((hasPolynomialCostFixedSingleControlHostTerminalRegularization_zero_iff_hasExactCardFixedSingleControlHostTerminalRegularization).2
        hhost)

theorem
    hasExactCardFixedSingleControlHostTerminalRegularization_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    HasExactCardFixedSingleControlHostTerminalRegularization := by
  classical
  intro n j G hhost
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact
    hasRegularInducedSubgraphOfCard_of_hasExactCardFixedModulusSingleControlResidueHostWitnessOfCard
      (G := G)
      (hupgrade G hhost)

theorem forcingThreshold_pow_two_le_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
    {r : ℕ} (hr : 0 < r)
    (hupgrade : HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    forcingThreshold (2 ^ r) ≤ 2 ^ (4 * r) := by
  exact
    forcingThreshold_pow_two_le_of_hasExactCardFixedSingleControlHostTerminalRegularization hr
      (hasExactCardFixedSingleControlHostTerminalRegularization_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
        hupgrade)

theorem eventualNatPowerDomination_two_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    EventualNatPowerDomination 2 := by
  exact
    eventualNatPowerDomination_two_of_hasExactCardFixedSingleControlHostTerminalRegularization
      (hasExactCardFixedSingleControlHostTerminalRegularization_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
        hupgrade)

theorem targetStatement_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
    (hupgrade : HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  exact
    targetStatement_of_hasExactCardFixedSingleControlHostTerminalRegularization
      (hasExactCardFixedSingleControlHostTerminalRegularization_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
        hupgrade)

/--
Dyadic-tail residue route to the global target.  Once beta-vanishing propagates the dropped-tail
residue, and the terminal bookkeeping turns that residue into an empty-control external-block bridge,
the existing asymptotic pipeline yields the conjecture.
-/
theorem targetStatement_of_dyadicTailResidueExternalBlockBridge
    {C D : ℕ}
    {AllBetaBitsVanish InitialResidueConst FinalDroppedTailResidueConst TerminalRegularQBucket
      ControlBlockBookkeeping : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hprop :
      Q64DyadicDroppedTailResiduePropagation AllBetaBitsVanish InitialResidueConst
        FinalDroppedTailResidueConst)
    (hbridge :
      Q64PositiveCostExternalBlockBridgeFromTailResidue FinalDroppedTailResidueConst
        TerminalRegularQBucket ControlBlockBookkeeping
        (HasPolynomialCostEmptyControlExternalBlockBridge D))
    (hbeta : AllBetaBitsVanish) (hinit : InitialResidueConst)
    (hterminal : TerminalRegularQBucket) (hbook : ControlBlockBookkeeping) :
    TargetStatement := by
  have hExternal : HasPolynomialCostEmptyControlExternalBlockBridge D :=
    hbridge (hprop hbeta hinit) hterminal hbook
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_polynomialCostEmptyControlExternalBlockBridge
      hlift hExternal

/--
Concrete bit-step version of the dyadic-tail route: beta vanishing at every bit below `j`, together
with the one-bit residue propagation steps, supplies the abstract final residue-constancy input used
by the positive-cost external-block bridge.
-/
theorem targetStatement_of_dyadicBetaBitStepsExternalBlockBridge
    {C D j : ℕ} {BetaVanishesAtBit ResidueConstAtBit : ℕ → Prop}
    {TerminalRegularQBucket ControlBlockBookkeeping : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hsteps : Q64DyadicBetaBitStepsUpTo j BetaVanishesAtBit ResidueConstAtBit)
    (hbridge :
      Q64PositiveCostExternalBlockBridgeFromTailResidue (ResidueConstAtBit j)
        TerminalRegularQBucket ControlBlockBookkeeping
        (HasPolynomialCostEmptyControlExternalBlockBridge D))
    (hbeta : Q64AllBetaBitsVanishUpTo j BetaVanishesAtBit)
    (hinit : ResidueConstAtBit 0)
    (hterminal : TerminalRegularQBucket) (hbook : ControlBlockBookkeeping) :
    TargetStatement := by
  exact
    targetStatement_of_dyadicTailResidueExternalBlockBridge
      (C := C) (D := D)
      (hlift := hlift)
      (hprop :=
        q64_dyadicDroppedTailResiduePropagation_of_betaBitStepsUpTo
          (j := j) hsteps)
      hbridge hbeta hinit hterminal hbook

/-- Concrete row-function bit step underlying the note-level `beta_m = 0` propagation. -/
theorem q64_dyadicBetaBitStep_of_dyadicTailBetaVanishesAt
    {W : Type*} {m : ℕ} {row : W → ℕ} :
    Q64DyadicBetaBitStep
      (DyadicTailBetaVanishesAt m row)
      (HasDyadicRowDivisibilityChain m row)
      (HasDyadicRowDivisibilityChain (m + 1) row) := by
  intro hbeta hchain
  rcases exists_hasDyadicRowDivisibilityChainTo_of_hasDyadicRowDivisibilityChain hchain with
    ⟨tail, htail⟩
  exact htail.succ_of_dyadicTailBetaVanishesAt hbeta

/--
The concrete dyadic-tail row package supplies all bit steps needed by the abstract q64 propagation
surface.
-/
theorem q64_dyadicBetaBitStepsUpTo_dyadicTail
    {W : Type*} (j : ℕ) (row : W → ℕ) :
    Q64DyadicBetaBitStepsUpTo j
      (fun m => DyadicTailBetaVanishesAt m row)
      (fun m => HasDyadicRowDivisibilityChain m row) := by
  intro _m _hm
  exact q64_dyadicBetaBitStep_of_dyadicTailBetaVanishesAt

/--
Corollary 3.2 in the existing row-divisibility language, routed through the q64 bit-step wrapper:
all beta bits below `j` yield a dyadic divisibility chain of depth `j`.
-/
theorem q64_hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo
    {W : Type*} {j : ℕ} {row : W → ℕ}
    (hbeta : DyadicTailBetaVanishesUpTo j row) :
    HasDyadicRowDivisibilityChain j row := by
  exact
    q64_dyadicResidueConstAt_of_betaBitStepsUpTo
      (j := j)
      (BetaVanishesAtBit := fun m => DyadicTailBetaVanishesAt m row)
      (ResidueConstAtBit := fun m => HasDyadicRowDivisibilityChain m row)
      (q64_dyadicBetaBitStepsUpTo_dyadicTail (W := W) j row)
      hbeta
      (HasDyadicRowDivisibilityChain.zero row)

/--
Concrete beta-vanishing implies the final dropped-tail row is constant modulo `2^j`.
-/
theorem q64_dyadicDroppedTailResiduePropagation_of_dyadicTailBetaVanishesUpTo
    {W : Type*} {j : ℕ} {row : W → ℕ} :
    Q64DyadicDroppedTailResiduePropagation
      (DyadicTailBetaVanishesUpTo j row) True
      (∀ v w, row v ≡ row w [MOD 2 ^ j]) := by
  intro hbeta _hinit
  exact
    modEq_of_hasDyadicRowDivisibilityChain
      (q64_hasDyadicRowDivisibilityChain_of_dyadicTailBetaVanishesUpTo hbeta)

/--
Concrete beta-tail version of the dyadic external-block route: the final bridge may now consume the
actual row congruence modulo `2^j`, rather than an uninterpreted final-residue proposition.
-/
theorem targetStatement_of_dyadicTailBetaExternalBlockBridge
    {C D j : ℕ} {W : Type*} {row : W → ℕ}
    {TerminalRegularQBucket ControlBlockBookkeeping : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hbridge :
      Q64PositiveCostExternalBlockBridgeFromTailResidue
        (∀ v w, row v ≡ row w [MOD 2 ^ j])
        TerminalRegularQBucket ControlBlockBookkeeping
        (HasPolynomialCostEmptyControlExternalBlockBridge D))
    (hbeta : DyadicTailBetaVanishesUpTo j row)
    (hterminal : TerminalRegularQBucket) (hbook : ControlBlockBookkeeping) :
    TargetStatement := by
  exact
    targetStatement_of_dyadicTailResidueExternalBlockBridge
      (C := C) (D := D)
      (hlift := hlift)
      (hprop :=
        q64_dyadicDroppedTailResiduePropagation_of_dyadicTailBetaVanishesUpTo
          (W := W) (j := j) (row := row))
      hbridge hbeta True.intro hterminal hbook

/--
The frontier audit really terminates at the conjecture: if carrier/marker coupling feeds the final
q=64 audit chain and that chain outputs the dropped-part host upgrade, the global target follows.
-/
theorem targetStatement_of_q64FinalAuditConditionalChain
    {CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      BetaVanishes : Prop}
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes HasExactCardFixedSingleControlHostDroppedPartUpgrade)
    (hcouple : CarrierMarkerCoupling) :
    TargetStatement := by
  exact targetStatement_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade
    (hchain hcouple).2.2.2.2.2

/--
Dyadic-tail version of the q=64 audit: the notes' `BetaVanishes` output is interpreted as the
refinement-data dyadic divisibility bridge.  Existing finite theorems turn that into the exact
self-bridge, and the empty-control lift then gives the conjecture.
-/
theorem targetStatement_of_q64FinalAuditConditionalChain_via_dyadicDivisibility
    {C D : ℕ}
    {CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
          (D + 1))
        GlobalBridge)
    (hcouple : CarrierMarkerCoupling) :
    TargetStatement := by
  have hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1) :=
    (hchain hcouple).2.2.2.2.1
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        hdiv)

/--
Beta-tail version of the q=64 audit: the final audit may output the note-level beta-vanishing
refinement bridge, which Lean now converts to dyadic divisibility and then to the exact self-bridge.
-/
theorem targetStatement_of_q64FinalAuditConditionalChain_via_dyadicBeta
    {C D : ℕ}
    {CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
          (D + 1))
        GlobalBridge)
    (hcouple : CarrierMarkerCoupling) :
    TargetStatement := by
  have hbeta :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
        (D + 1) :=
    (hchain hcouple).2.2.2.2.1
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
      hlift hbeta

/-- Final-audit route when the audit outputs beta-vanishing at every dyadic level. -/
theorem targetStatement_of_q64FinalAuditConditionalChain_via_dyadicBetaUpTo
    {C D : ℕ}
    {CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
      GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge)
    (hcouple : CarrierMarkerCoupling) :
    TargetStatement := by
  have hbeta :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
        (D + 1) :=
    (hchain hcouple).2.2.2.2.1
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
      hlift hbeta

/--
Global landing theorem for the claimed final obstruction proof: if the marker-splitting zero-sum
atom, product-firewall routing, and weighted-quotient packaging produce carrier/marker coupling, then
the already-audited q=64 endgame chain proves the conjecture.
-/
theorem targetStatement_of_q64LastObstructionLanding
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes : Prop}
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes HasExactCardFixedSingleControlHostDroppedPartUpgrade)
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    TargetStatement :=
  targetStatement_of_q64FinalAuditConditionalChain hchain
    (hlanding hzero hfirewall hpack)

/--
Global landing theorem for the dyadic-tail reading of the final obstruction proof: once landing
supplies carrier/marker coupling, beta-vanishing/divisibility gives the refinement exact self-bridge,
which is the honest finite frontier identified in the notes.
-/
theorem targetStatement_of_q64LastObstructionLanding_via_dyadicDivisibility
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
          (D + 1))
        GlobalBridge)
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    TargetStatement :=
  targetStatement_of_q64FinalAuditConditionalChain_via_dyadicDivisibility hlift hchain
    (hlanding hzero hfirewall hpack)

/--
Landing theorem for the beta-tail reading of the final obstruction proof.  The landing supplies
carrier/marker coupling; the final audit supplies the beta bridge; existing finite theorems finish.
-/
theorem targetStatement_of_q64LastObstructionLanding_via_dyadicBeta
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
          (D + 1))
        GlobalBridge)
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    TargetStatement :=
  targetStatement_of_q64FinalAuditConditionalChain_via_dyadicBeta hlift hchain
    (hlanding hzero hfirewall hpack)

/-- Landing theorem for the all-bits beta-tail reading of the final obstruction proof. -/
theorem targetStatement_of_q64LastObstructionLanding_via_dyadicBetaUpTo
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hlanding :
      Q64LastObstructionLandingSurface MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge)
    (hzero : MarkerSplittingZeroSumAtom) (hfirewall : ProductFirewall)
    (hpack : WeightedQuotientPackaging) :
    TargetStatement :=
  targetStatement_of_q64FinalAuditConditionalChain_via_dyadicBetaUpTo hlift hchain
    (hlanding hzero hfirewall hpack)

/--
One-object version of the final-frontier audit: a claimed final-proof certificate whose global bridge
is the dropped-part host upgrade immediately yields the conjecture.
-/
theorem targetStatement_of_q64ClaimedFinalProofCertificate
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes : Prop}
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  have hupgrade : HasExactCardFixedSingleControlHostDroppedPartUpgrade :=
    q64_globalBridge_of_claimedFinalProofCertificate
      (MarkerSplittingZeroSumAtom := MarkerSplittingZeroSumAtom)
      (ProductFirewall := ProductFirewall)
      (WeightedQuotientPackaging := WeightedQuotientPackaging)
      (CarrierMarkerCoupling := CarrierMarkerCoupling)
      (PrimeCycleBreaker := PrimeCycleBreaker)
      (SignLaw := SignLaw)
      (OneCornerLift := OneCornerLift)
      (CompensatorRouting := CompensatorRouting)
      (BetaVanishes := BetaVanishes)
      (GlobalBridge := HasExactCardFixedSingleControlHostDroppedPartUpgrade)
      hcert
  exact targetStatement_of_hasExactCardFixedSingleControlHostDroppedPartUpgrade hupgrade

/--
One-object dyadic-tail certificate-to-conjecture theorem.  This is the Lean translation of the note
claim that beta-vanishing propagates the dropped-tail residue and therefore supplies the
refinement-data exact self-bridge.
-/
theorem targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicDivisibility
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  have hdiv :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        (D + 1) :=
    q64_betaVanishes_of_claimedFinalProofCertificate
      (MarkerSplittingZeroSumAtom := MarkerSplittingZeroSumAtom)
      (ProductFirewall := ProductFirewall)
      (WeightedQuotientPackaging := WeightedQuotientPackaging)
      (CarrierMarkerCoupling := CarrierMarkerCoupling)
      (PrimeCycleBreaker := PrimeCycleBreaker)
      (SignLaw := SignLaw)
      (OneCornerLift := OneCornerLift)
      (CompensatorRouting := CompensatorRouting)
      (BetaVanishes :=
        HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
          (D + 1))
      (GlobalBridge := GlobalBridge)
      hcert
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge
      hlift
      (hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementExactSelfBridge_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
        hdiv)

/-- One-object beta-tail certificate-to-conjecture theorem. -/
theorem targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBeta
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  have hbeta :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
        (D + 1) :=
    q64_betaVanishes_of_claimedFinalProofCertificate
      (MarkerSplittingZeroSumAtom := MarkerSplittingZeroSumAtom)
      (ProductFirewall := ProductFirewall)
      (WeightedQuotientPackaging := WeightedQuotientPackaging)
      (CarrierMarkerCoupling := CarrierMarkerCoupling)
      (PrimeCycleBreaker := PrimeCycleBreaker)
      (SignLaw := SignLaw)
      (OneCornerLift := OneCornerLift)
      (CompensatorRouting := CompensatorRouting)
      (BetaVanishes :=
        HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
          (D + 1))
      (GlobalBridge := GlobalBridge)
      hcert
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
      hlift hbeta

/-- One-object all-bits beta-tail certificate-to-conjecture theorem. -/
theorem targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBetaUpTo
    {C D : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting GlobalBridge : Prop}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hcert :
      Q64ClaimedFinalProofCertificate MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  have hbeta :
      HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
        (D + 1) :=
    q64_betaVanishes_of_claimedFinalProofCertificate
      (MarkerSplittingZeroSumAtom := MarkerSplittingZeroSumAtom)
      (ProductFirewall := ProductFirewall)
      (WeightedQuotientPackaging := WeightedQuotientPackaging)
      (CarrierMarkerCoupling := CarrierMarkerCoupling)
      (PrimeCycleBreaker := PrimeCycleBreaker)
      (SignLaw := SignLaw)
      (OneCornerLift := OneCornerLift)
      (CompensatorRouting := CompensatorRouting)
      (BetaVanishes :=
        HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
      (GlobalBridge := GlobalBridge)
      hcert
  exact
    targetStatement_of_polynomialCostEmptyControlDyadicLift_of_hasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
      hlift hbeta

/--
Fully expanded product-firewall-transport route to the conjecture.  The sub-`q` trap removes the
transport-failure branch; ordered-boundary and local-exit branches feed carrier/marker coupling; the
final audit chain outputs the dropped-part host upgrade.
-/
theorem targetStatement_of_q64ProductFirewallTransportTrapCertificate
    {q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes : Prop}
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
        CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate
    (q64_claimedFinalProofCertificate_of_productFirewallTransportTrap hzero hfirewall hpack
      hbreaker hreduce htrap hboundary hlocal hchain)

/--
Fully expanded product-firewall transport route for the honest dyadic-tail/refinement-data target.
The transport trap supplies the landing; the final audit supplies dyadic divisibility; existing finite
theorems collapse the refinement data to the exact self-bridge and hence to the conjecture.
-/
theorem targetStatement_of_q64ProductFirewallTransportTrapCertificate_via_dyadicDivisibility
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
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
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementDivisibilitySelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicDivisibility hlift
    (q64_claimedFinalProofCertificate_of_productFirewallTransportTrap hzero hfirewall hpack
      hbreaker hreduce htrap hboundary hlocal hchain)

/--
Fully expanded product-firewall transport route for the beta-tail bridge: the transport trap supplies
landing, and the final audit supplies beta-vanishing in the concrete refinement-data form.
-/
theorem targetStatement_of_q64ProductFirewallTransportTrapCertificate_via_dyadicBeta
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
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
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBeta hlift
    (q64_claimedFinalProofCertificate_of_productFirewallTransportTrap hzero hfirewall hpack
      hbreaker hreduce htrap hboundary hlocal hchain)

/-- Fully expanded product-firewall transport route for all-bits beta-vanishing. -/
theorem targetStatement_of_q64ProductFirewallTransportTrapCertificate_via_dyadicBetaUpTo
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
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
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBetaUpTo hlift
    (q64_claimedFinalProofCertificate_of_productFirewallTransportTrap hzero hfirewall hpack
      hbreaker hreduce htrap hboundary hlocal hchain)

/--
Named transport-reduction version of the product-firewall route to the conjecture.  This uses the
frontier certificate surface `Q64ProductFirewallTransportReduction` and the two-exit
carrier/marker-coupling certificate instead of an anonymous reduction function.
-/
theorem targetStatement_of_q64TransportReductionCertificate_via_dyadicBetaUpTo
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
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
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBetaUpTo hlift
    (q64_claimedFinalProofCertificate_of_transportReduction_and_subqTrap hzero hfirewall hpack
      hbreaker htransport htrap hexits hchain)

/--
Global theorem from the named product-firewall proof certificate.  This is the tightest current Lean
translation of the note route: product-firewall transport proves the landing/coupling certificate,
the final audit emits all-bits beta vanishing, and the finite dyadic bridge collapses to the exact
self-bridge and hence to the conjecture.
-/
theorem targetStatement_of_q64ProductFirewallProofCertificate_via_dyadicBetaUpTo
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hcert :
      Q64ProductFirewallProofCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ClaimedFinalProofCertificate_via_dyadicBetaUpTo hlift
    (q64_claimedFinalProofCertificate_of_productFirewallProofCertificate hcert hchain)

/--
Global theorem from the fully expanded failed-transport marker-data product-firewall certificate.
This keeps the note's sub-`q` trap as data: each failed transport produces a positive marker contained
in a packet of size `< q`, and low-set congruence gives marker size `0 [MOD q]`.
-/
theorem targetStatement_of_q64ProductFirewallProofDataCertificate_via_dyadicBetaUpTo
    {C D q : ℕ}
    {MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging CarrierMarkerCoupling
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hcert :
      Q64ProductFirewallProofDataCertificate q MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging CarrierMarkerCoupling AmbientPacketBreaker OrderedBoundaryRow
        LocalExit TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain CarrierMarkerCoupling PrimeCycleBreaker SignLaw OneCornerLift
        CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ProductFirewallProofCertificate_via_dyadicBetaUpTo hlift
    (q64_productFirewallProofCertificate_of_dataCertificate hcert) hchain

/--
End-to-end formalization of the strongest product-firewall claim in the notes: the fully skew
q-marker branch is exhausted to the product firewall; any failed transport creates the forbidden
nonempty sub-`q` congruent marker; the surviving branches give carrier/marker coupling; the final
audit chain then reaches the dyadic beta-up-to handoff and the target statement.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingData_via_dyadicBetaUpTo
    {C D q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (hdata :
      Q64ProductFirewallQMarkerCouplingData q FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
        AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64FinalAuditConditionalChain_via_dyadicBetaUpTo hlift hchain
    (q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingData hdata)

/--
End-to-end product-firewall route with the failed-transport contradiction split into its three
note-level subclaims: dirty submarker production, proper-packet bound, and low-set congruence.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingComponents_via_dyadicBetaUpTo
    {C D q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (h :
      Q64ProductFirewallQMarkerCouplingComponents q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ProductFirewallQMarkerCouplingData_via_dyadicBetaUpTo hlift
    (q64_productFirewallQMarkerCouplingData_of_components h) hchain

/--
Most expanded dyadic-beta product-firewall route currently present in Lean: static split-quotient
exhaustion, failed-transport contradiction, and the final audit chain are all componentized.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingAudit_via_dyadicBetaUpTo
    {C D q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting GlobalBridge : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hlift : HasPolynomialCostEmptyControlDyadicLift C)
    (haudit :
      Q64ProductFirewallQMarkerCouplingAudit q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditComponentChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting
        (HasBoundedFixedModulusControlBlockModularHostPositiveDyadicRefinementBetaUpToSelfBridge
          (D + 1))
        GlobalBridge) :
    TargetStatement := by
  exact targetStatement_of_q64ProductFirewallQMarkerCouplingComponents_via_dyadicBetaUpTo hlift
    (q64_productFirewallQMarkerCouplingComponents_of_audit haudit)
    (q64_finalAuditConditionalChain_of_components hchain)

/--
Exact dropped-host-upgrade version of the product-firewall q-marker route.  This is the direct
endgame when the final audit chain already emits the host upgrade used by the asymptotic bridge.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingData
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (hdata :
      Q64ProductFirewallQMarkerCouplingData q FullySkewSplitter ProperSubmarker PrimeModuleExit
        ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
        AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  exact
    targetStatement_of_q64FinalAuditConditionalChain hchain
      (q64_qMarkerCarrierMarkerCoupling_of_productFirewallQMarkerCouplingData hdata)

/--
Component-level exact-route version: the failed-transport contradiction is supplied as the three
note-level pieces, then assembled to the q-marker data certificate above.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingComponents
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (h :
      Q64ProductFirewallQMarkerCouplingComponents q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditConditionalChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  exact targetStatement_of_q64ProductFirewallQMarkerCouplingData
    (q64_productFirewallQMarkerCouplingData_of_components h) hchain

/--
Most expanded exact-host-upgrade product-firewall route: both q-marker certificate layers and the
post-coupling final audit chain are split into named components.
-/
theorem targetStatement_of_q64ProductFirewallQMarkerCouplingAudit
    {q : ℕ}
    {FullySkewSplitter ProperSubmarker PrimeModuleExit ClosedLocalExit
      MarkerSplittingZeroSumAtom ProductFirewall WeightedQuotientPackaging
      AmbientPacketBreaker OrderedBoundaryRow LocalExit TransportFailure PrimeCycleBreaker SignLaw
      OneCornerLift CompensatorRouting BetaVanishes : Prop}
    {markerSize packetSize : TransportFailure → ℕ}
    (haudit :
      Q64ProductFirewallQMarkerCouplingAudit q FullySkewSplitter ProperSubmarker
        PrimeModuleExit ClosedLocalExit MarkerSplittingZeroSumAtom ProductFirewall
        WeightedQuotientPackaging AmbientPacketBreaker OrderedBoundaryRow LocalExit
        TransportFailure markerSize packetSize)
    (hchain :
      Q64FinalAuditComponentChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade) :
    TargetStatement := by
  exact targetStatement_of_q64ProductFirewallQMarkerCouplingComponents
    (q64_productFirewallQMarkerCouplingComponents_of_audit haudit)
    (q64_finalAuditConditionalChain_of_components hchain)

/--
Fully expanded q-marker endpoint-to-conjecture bridge.  The only local q-marker input is the detailed
provenance-routing chain; the rest is the already-audited final dependency chain ending in the
dropped-part host upgrade.
-/
theorem targetStatement_of_q64FinalAuditConditionalChain_of_provenanceRouting
    {FullySkewSplitter ProvenanceSelection OrderedFirstReturnRow ValidBreaker
      ProvenanceSplitterAdmissible FirstFailedRow MarkerInternalFailure NonMarkerFailure
      SmallerCompleteMarker LocalNonMarkerExit ProperSubmarker PrimeModuleExit ClosedLocalExit
      PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes : Prop}
    (hchain :
      Q64FinalAuditConditionalChain
        (Q64QMarkerCarrierMarkerCoupling FullySkewSplitter ProperSubmarker PrimeModuleExit
          ClosedLocalExit)
        PrimeCycleBreaker SignLaw OneCornerLift CompensatorRouting BetaVanishes
        HasExactCardFixedSingleControlHostDroppedPartUpgrade)
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
    TargetStatement := by
  exact
    targetStatement_of_q64FinalAuditConditionalChain hchain
      (q64_qMarkerCarrierMarkerCoupling_of_routing hroute hchoice htransport hadm hclass
        hnonmarker hdescent hadmissible hsmaller hlocal)

end DyadicLift

end Threshold

end RegularInducedSubgraph
