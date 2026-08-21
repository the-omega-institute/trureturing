/- GID: D5/S3/Quantum/Measurements/OrthogonalAdditivity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/OrthogonalAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normal states are countably additive on complete orthogonal projections. -/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace D5.S3.Quantum.Measurements.OrthogonalAdditivity

open scoped ComplexOrder
open Filter Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- A normality condition expressed only through monotone strong limits of operators. -/
def SequentiallyNormal {A H : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (representation : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (omega : A →ₚ[ℂ] ℂ) : Prop :=
  ∀ (sequence : ℕ → A) (limit : A),
    Monotone sequence →
      (∀ vector,
        Tendsto (fun n => representation (sequence n) vector) atTop
          (𝓝 (representation limit vector))) →
      Tendsto (fun n => (omega (sequence n)).re) atTop (𝓝 (omega limit).re)

/-- A normal state assigns total weight one to a complete countable orthogonal family,
and its pure-state weights satisfy the corresponding Parseval identity. -/
theorem orthogonal_additivity
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (projection : ℕ → A)
    (representation : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (state : A →ₚ[ℂ] ℂ)
    (projection_is_projection : ∀ i, IsStarProjection (projection i))
    (projection_orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0)
    (strong_complete :
      ∀ vector, HasSum (fun i => representation (projection i) vector) vector)
    (state_normalized : state 1 = 1)
    (state_normal : SequentiallyNormal representation state) :
    HasSum (fun i => state (projection i)) 1 ∧
      ∀ vector,
        HasSum
          (fun i => ‖representation (projection i) vector‖ ^ 2)
          (‖vector‖ ^ 2) := by
  have projection_nonnegative : ∀ i, 0 ≤ projection i := by
    intro i
    exact (projection_is_projection i).nonneg
  let partialSums : ℕ → A :=
    fun n => ∑ i ∈ Finset.range n, projection i
  have partial_monotone : Monotone partialSums := by
    apply monotone_nat_of_le_succ
    intro n
    rw [show partialSums (n + 1) = partialSums n + projection n by
      simp [partialSums, Finset.sum_range_succ]]
    exact le_add_of_nonneg_right (projection_nonnegative n)
  have partial_strong : ∀ vector,
      Tendsto (fun n => representation (partialSums n) vector) atTop
        (𝓝 (representation 1 vector)) := by
    intro vector
    simpa [partialSums, map_sum] using (strong_complete vector).tendsto_sum_nat
  have state_tendsto := state_normal partialSums 1 partial_monotone (by
    intro vector
    exact partial_strong vector)
  have weight_nonnegative_and_real :
      ∀ i, 0 ≤ (state (projection i)).re ∧ 0 = (state (projection i)).im := by
    intro i
    exact Complex.nonneg_iff.mp (state.map_nonneg (projection_nonnegative i))
  have weight_nonnegative : ∀ i, 0 ≤ (state (projection i)).re :=
    fun i => (weight_nonnegative_and_real i).1
  have weight_as_real (i : ℕ) :
      ((state (projection i)).re : ℂ) = state (projection i) := by
    apply Complex.ext
    · simp
    · simpa using (weight_nonnegative_and_real i).2
  constructor
  · have real_sum : HasSum (fun i => (state (projection i)).re) 1 := by
      apply (hasSum_iff_tendsto_nat_of_nonneg weight_nonnegative 1).mpr
      simpa [partialSums, map_sum, state_normalized] using state_tendsto
    have complex_sum := real_sum.mapL Complex.ofRealCLM
    change HasSum
      (fun i => ((state (projection i)).re : ℂ)) ((1 : ℝ) : ℂ) at complex_sum
    simpa only [weight_as_real, Complex.ofReal_one] using complex_sum
  · intro vector
    have inner_sum :
        HasSum
          (fun i => inner ℂ vector (representation (projection i) vector))
          (inner ℂ vector vector) :=
      (strong_complete vector).mapL (innerSL ℂ vector)
    have real_inner_sum := inner_sum.mapL Complex.reCLM
    have projection_norm (i : ℕ) :
        (inner ℂ vector (representation (projection i) vector)).re =
          ‖representation (projection i) vector‖ ^ 2 := by
      have operator_is_projection := (projection_is_projection i).map representation
      have symmetric := operator_is_projection.isSelfAdjoint.isSymmetric
      have idempotent_apply :
          representation (projection i) (representation (projection i) vector) =
            representation (projection i) vector := by
        have h := congrArg (fun operator : H →L[ℂ] H => operator vector)
          operator_is_projection.isIdempotentElem
        simpa [mul_apply] using h
      calc
        (inner ℂ vector (representation (projection i) vector)).re =
            (inner ℂ vector
              (representation (projection i) (representation (projection i) vector))).re := by
          exact congrArg Complex.re (congrArg (inner ℂ vector) idempotent_apply.symm)
        _ = (inner ℂ (representation (projection i) vector)
            (representation (projection i) vector)).re := by
          exact congrArg Complex.re
            (symmetric vector (representation (projection i) vector)).symm
        _ = ‖representation (projection i) vector‖ ^ 2 :=
          inner_self_eq_norm_sq (𝕜 := ℂ) (representation (projection i) vector)
    have real_inner_sum' := real_inner_sum
    change HasSum
      (fun i => (inner ℂ vector (representation (projection i) vector)).re)
      (inner ℂ vector vector).re at real_inner_sum'
    have endpoint : (inner ℂ vector vector).re = ‖vector‖ ^ 2 := by
      exact inner_self_eq_norm_sq (𝕜 := ℂ) vector
    rw [endpoint] at real_inner_sum'
    simpa only [projection_norm] using real_inner_sum'

#print axioms orthogonal_additivity

end D5.S3.Quantum.Measurements.OrthogonalAdditivity
