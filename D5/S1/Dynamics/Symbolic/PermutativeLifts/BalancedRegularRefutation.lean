/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularRefutation
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularRefutation.claim; result=D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularRefutation.result; claim=D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularRefutation.claim
   digest: A single strictly ergodic regular Toeplitz base refutes minimality of every entire bipermutative lift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLiftSplitting
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedUniqueErgodic
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedRegularity
import D5.S1.Dynamics.Symbolic.PermutativeLifts.UniversalRefutation

set_option autoImplicit false

open Set MeasureTheory Filter SymbolicDynamics.FullShift
open scoped Topology

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedRegularRefutation

open Balanced BipermutativeLift UniversalRefutation

/-- Even the regular Toeplitz, strictly ergodic binary branch of Question
1.10 would require a minimal entire lift. Regularity refers to actual
skeleton densities along a positive essential period structure covering all
signed coordinates; the generator is aperiodic and generates the same base.
Strict ergodicity is literal minimality and uniqueness of invariant probability.
The length and both endpoint-permutative rules remain unrestricted. -/
def claim : Prop :=
  ∀ Y : Subshift Bool ℤ,
    Nonempty Y.carrier →
    (∀ y : Y.carrier, DenseRange (fun g : ℤ => translateBase Y g y)) →
    (∃! μ : Measure Y.carrier,
      IsProbabilityMeasure μ ∧ MeasurePreserving (translateBase Y 1) μ μ) →
    (∃ y : ℤ → Bool,
      y ∈ Y.carrier ∧ HasPeriodicCoordinates y ∧
      (∀ p : ℕ, 0 < p → shift (p : ℤ) y ≠ y) ∧
      closure (Set.range (fun g : ℤ => shift g y)) = Y.carrier ∧
      ∃ P : PeriodicSkeleton.PeriodStructure y,
        Tendsto P.skeletonDensity atTop (𝓝 1)) →
    ∃ (k : ℕ) (h : (Fin (k + 2) → Bool) → Bool),
      Bipermutative h ∧
        ∀ x : LiftPoint h Y, DenseRange (fun g : ℤ => translateLift Y g x)

/-- The very same balanced base is regular Toeplitz and strictly ergodic,
yet every allowed code and length has a nonminimal whole inverse image.
In particular no whole lift can be strictly ergodic. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨k, h, bh, hminimal⟩ := hclaim balancedSubshift
    (inferInstance : Nonempty BalancedPoint) balanced_orbit_dense
    balanced_unique_ergodic exists_balanced_regular_toeplitz_generator
  apply BalancedLift.full_lift_not_minimal bh
  constructor
  intro x
  exact hminimal x

end D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedRegularRefutation
