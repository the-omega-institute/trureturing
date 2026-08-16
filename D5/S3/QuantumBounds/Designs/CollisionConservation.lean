/- GID: D5/S3/QuantumBounds/Designs/CollisionConservation
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/Designs/CollisionConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Contract a finite projective two-design identity to collision conservation. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found only the downstream `CollisionEntropyUncertainty` theorem, which
     assumes collision conservation; no D5 theorem derived that conservation law.
   * Pinned-mathlib searches for mutually unbiased bases, projective designs, collision, and
     purity found no matching declaration. Loogle concept-name queries were also unbound.
   * `Matrix.trace`, `Fintype.sum_mul_sum`, and `Finset.sum_comm` are the exact upstream algebraic
     components used below. The LeanSearch `/api/search` endpoint returned HTTP 404.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.QuantumBounds.Designs.CollisionConservation

/-- Contracting the component identity for a finite projective two-design against a normalized
matrix gives collision conservation: the sum of squared measurement weights is one plus the
matrix purity. Positivity and self-adjointness are unnecessary for this algebraic implication. -/
theorem collision_sum_eq_one_add_purity
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (rho : Matrix ι ι ℝ) (projector : κ -> Matrix ι ι ℝ)
    (htrace : Matrix.trace rho = 1)
    (hdesign : forall a b c d,
      ∑ x, projector x a b * projector x c d =
        (if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = d then 1 else 0) * (if c = b then 1 else 0)) :
    ∑ x, (Matrix.trace (rho * projector x)) ^ 2 =
      1 + Matrix.trace (rho * rho) := by
  classical
  change (∑ a, rho a a) = 1 at htrace
  simp only [Matrix.trace]
  calc
    ∑ x, (∑ a, ∑ b, rho a b * projector x b a) ^ 2 =
        ∑ x, ∑ a, ∑ c, ∑ b, ∑ d,
          (rho a b * rho c d) * (projector x b a * projector x d c) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two]
      simp_rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = ∑ a, ∑ c, ∑ b, ∑ d,
        (rho a b * rho c d) * ∑ x, projector x b a * projector x d c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    _ = ∑ a, ∑ c, ∑ b, ∑ d,
        (rho a b * rho c d) *
          ((if b = a then 1 else 0) * (if d = c then 1 else 0) +
            (if b = c then 1 else 0) * (if d = a then 1 else 0)) := by
      simp_rw [hdesign]
    _ = 1 + ∑ a, ∑ b, rho a b * rho b a := by
      simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_left_inj]
      rw [← Fintype.sum_mul_sum, htrace]
      norm_num

end D5.S3.QuantumBounds.Designs.CollisionConservation
