/- GID: D5/S3/Observer/ProbabilisticClosure/CausalMemoryRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/CausalMemoryRecovery
   mirror-E: none(waiver:exact-causal-reconstruction)
   anchors: []
   utility: none
   digest: Full observed response maps reconstruct the actual block-memory
     kernel by a triangular causal inverse, without recovering hidden coordinates. -/

import D5.S3.Observer.ProbabilisticClosure.DiscreteMemoryElimination
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.CausalMemoryRecovery

open DiscreteMemoryElimination

/-- Reconstruction is triangular: its nth value uses only responses through
n+2 and already reconstructed lower indices. Composition order is retained. -/
noncomputable def recoverKernel {V : Type*} [AddCommGroup V]
    (response : Nat → V → V) (n : Nat) (v : V) : V :=
  response (n + 2) v - response 1 (response (n + 1) v) -
    ∑ i : Fin n, recoverKernel response (n - 1 - i.val)
      (response (i.val + 1) v)
termination_by n
decreasing_by
  have := i.isLt
  omega

variable {R V H : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AddCommGroup H] [Module R H]

/-- The whole visible response to each visible initial vector, with zero
initial hidden component. This is an operator-valued response, not its trace. -/
def visibleResponse (A : V →ₗ[R] V) (B : H →ₗ[R] V)
    (C : V →ₗ[R] H) (D : H →ₗ[R] H) (n : Nat) (v : V) : V :=
  (evolve A B C D n (v, 0)).1

/-- Causal reconstruction gives exactly the kernel of the actual coupled
recursion at every lag. It does not assume a memory kernel as extra data and
does not identify hidden realizations from their common input-output behavior. -/
theorem recover_actual_memory
    (A : V →ₗ[R] V) (B : H →ₗ[R] V)
    (C : V →ₗ[R] H) (D : H →ₗ[R] H) (n : Nat) (v : V) :
    recoverKernel (visibleResponse A B C D) n v = memoryKernel B C D n v := by
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    have hfirst (w : V) : visibleResponse A B C D 1 w = A w := by
      simp [visibleResponse, evolve]
    have equation := exact_memory_equation A B C D (v, 0) (n + 1)
    change visibleResponse A B C D (n + 2) v =
      A (visibleResponse A B C D (n + 1) v) + B ((D ^ (n + 1)) 0) +
        ∑ i ∈ Finset.range (n + 1), memoryKernel B C D (n + 1 - 1 - i)
          (visibleResponse A B C D i v) at equation
    simp only [map_zero, add_zero, Nat.add_sub_cancel] at equation
    rw [Finset.sum_range_succ'] at equation
    have hindex (i : Nat) : n - (i + 1) = n - 1 - i := by omega
    simp only [Nat.sub_zero] at equation
    simp_rw [hindex] at equation
    change visibleResponse A B C D (n + 2) v =
      A (visibleResponse A B C D (n + 1) v) +
        ((∑ i ∈ Finset.range n, memoryKernel B C D (n - 1 - i)
          (visibleResponse A B C D (i + 1) v)) + memoryKernel B C D n v) at equation
    rw [← Fin.sum_univ_eq_sum_range] at equation
    have hsum :
        (∑ i : Fin n, recoverKernel (visibleResponse A B C D) (n - 1 - i.val)
          (visibleResponse A B C D (i.val + 1) v)) =
        ∑ i : Fin n, memoryKernel B C D (n - 1 - i.val)
          (visibleResponse A B C D (i.val + 1) v) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ih (n - 1 - i.val) (by have := i.isLt; omega) _
    rw [recoverKernel, hfirst, hsum, equation]
    abel

#print axioms recover_actual_memory

end D5.S3.Observer.ProbabilisticClosure.CausalMemoryRecovery
