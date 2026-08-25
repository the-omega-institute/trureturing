/- GID: D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraOrderReversal
   generality: G
   mirror-B: D5/B/S3/Observer/WindowAlgebra/FinitePartitionAlgebraOrderReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Inclusion of finite state kernels reverses inclusion of their real effect algebras. -/

import D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraAntiequivalence

/- Library-search audit trail (2026-08-25):
   * Exact repository searches for order reversal, partition algebras, state
     kernels, and effect algebras found no theorem stating this corollary.
   * The real-carrier predecessor `finite_partition_algebra_antiequivalence`
     reconstructs an equivalence relation from its class-constant functions;
     the reverse implication below applies that theorem directly.
   * Pinned Mathlib searches for finite partition subalgebras, fiber algebras,
     and order-reversing subalgebra maps found no exact theorem. -/

namespace D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraOrderReversal

open D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraAntiequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For equivalence relations on a finite state space, relation inclusion is
exactly reverse inclusion of the real-valued class-constant effect algebras. -/
theorem finite_partition_algebra_order_reversal
    {X : Type*} [Finite X]
    (R₁ R₂ : Set (X × X))
    (_hR₁ : Equivalence (fun x y => (x, y) ∈ R₁))
    (hR₂ : Equivalence (fun x y => (x, y) ∈ R₂)) :
    R₁ ⊆ R₂ ↔
      ({f : X -> ℝ | ∀ ⦃x y⦄, (x, y) ∈ R₂ -> f x = f y} : Set (X -> ℝ)) ⊆
        ({f : X -> ℝ | ∀ ⦃x y⦄, (x, y) ∈ R₁ -> f x = f y} : Set (X -> ℝ)) := by
  constructor
  · intro hrelation f hf x y hxy
    exact hf (hrelation hxy)
  · intro halgebra pair hpair
    rcases pair with ⟨x, y⟩
    have hreconstruct :=
      (finite_partition_algebra_antiequivalence
        (fun a b => (a, b) ∈ R₂) hR₂
        (⊥ : Subalgebra ℝ (X -> ℝ))).1
    rw [← congrFun (congrFun hreconstruct x) y]
    intro f hf
    exact halgebra hf hpair

#print axioms finite_partition_algebra_order_reversal

end D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraOrderReversal
