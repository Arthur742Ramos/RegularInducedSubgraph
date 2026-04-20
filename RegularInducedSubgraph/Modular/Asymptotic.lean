import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt
import RegularInducedSubgraph.Modular.Cascade

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
Polynomial-cost bridge from the empty-control fixed-modulus cascade package to the terminal-capped
control-block modular cascade package. The modulus stays fixed; only the witness order pays a
polynomial loss.
-/
def HasPolynomialCostEmptyControlTerminalBridge (D : ℕ) : Prop :=
  ∀ {n j m : ℕ} (G : SimpleGraph (Fin n)),
    HasFixedModulusCascadeWitnessOfCard G ((2 ^ j) ^ D * m) (2 ^ j) →
      HasFixedModulusControlBlockModularCascadeWitnessOfCard G m (2 ^ j)

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

end DyadicLift

end Threshold

end RegularInducedSubgraph
