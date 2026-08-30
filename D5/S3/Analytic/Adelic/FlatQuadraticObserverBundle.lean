/- GID: D5/S3/Analytic/Adelic/FlatQuadraticObserverBundle
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/FlatQuadraticObserverBundle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant second derivative and one compatible jet determine a positive flat quadratic bundle. -/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Classes

/- Library-search audit trail (2026-08-30):
   * Frozen D5 searches for flat quadratic observer bundles, constant second
     derivatives, quarter-square jets, and half-derivative operator recovery
     found no theorem stating the source identity on a common operator carrier.
   * The nearby `ZeroCompletionVelocity`, `NormalJetFormula`, and
     `JetResolventSemisimplification` modules concern simple-zero motion,
     logarithmic jets, and finite nilpotent pencils; none supplies this bundle.
   * Body-shape searches for `(1 / 4) • A' t0 ^ 2`, for
     `algebraMap _ _ t0 - (1 / 2) • A' t0`, and for a derivative constantly
     equal to `2 • 1` found no canonical D5 primitive. No new definition or
     abbreviation is introduced here.
   * Pinned Mathlib supplies `IsOpen.eqOn_of_deriv_eq`, `HasDerivAt.star`,
     and `IsSelfAdjoint.sq_nonneg`. These are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.FlatQuadraticObserverBundle

/-- A common self-adjoint operator family with constant second derivative and
one compatible value/velocity jet is the square of one self-adjoint affine
operator at every parameter. Its resulting fibers are positive. -/
theorem flat_quadratic_observer_bundle
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (A velocity : ℝ → B) (t0 : ℝ)
    (hA : ∀ t, HasDerivAt A (velocity t) t)
    (hVelocity : ∀ t, HasDerivAt velocity ((2 : ℝ) • (1 : B)) t)
    (hSelf : ∀ t, IsSelfAdjoint (A t))
    (hJet : A t0 = (1 / 4 : ℝ) • (velocity t0) ^ 2) :
    let H := algebraMap ℝ B t0 - (1 / 2 : ℝ) • velocity t0
    IsSelfAdjoint H ∧
      (∀ t, A t = (H - algebraMap ℝ B t) ^ 2) ∧
      (∀ t, 0 ≤ (H - algebraMap ℝ B t) ^ 2) := by
  have hAffineVelocity : ∀ t, HasDerivAt
      (fun u : ℝ => velocity t0 + (2 * (u - t0)) • (1 : B))
      ((2 : ℝ) • (1 : B)) t := by
    intro t
    simpa using ((((hasDerivAt_id t).sub_const t0).const_mul 2).smul_const
      (1 : B) |>.const_add (velocity t0))
  have hVelocityEq : ∀ t,
      velocity t = velocity t0 + (2 * (t - t0)) • (1 : B) := by
    have hEq := isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ
      (fun t _ => (hVelocity t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hAffineVelocity t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hVelocity t).deriv.trans (hAffineVelocity t).deriv.symm)
      (Set.mem_univ t0) (by simp)
    exact fun t => hEq (Set.mem_univ t)
  have hQuadratic : ∀ t, HasDerivAt
      (fun u : ℝ =>
        A t0 + (u - t0) • velocity t0 + (u - t0) ^ 2 • (1 : B))
      (velocity t0 + (2 * (t - t0)) • (1 : B)) t := by
    intro t
    have hDelta : HasDerivAt (fun u : ℝ => u - t0) 1 t :=
      (hasDerivAt_id t).sub_const t0
    have hLinear := hDelta.smul_const (velocity t0)
    have hSquare := hDelta.mul hDelta
    simpa only [Pi.add_apply, Pi.mul_apply, id_eq, one_smul, pow_two, two_mul,
      one_mul, mul_one, add_assoc] using
      ((hLinear.add (hSquare.smul_const (1 : B))).const_add (A t0))
  have hAEq : ∀ t,
      A t = A t0 + (t - t0) • velocity t0 + (t - t0) ^ 2 • (1 : B) := by
    have hEq := isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ
      (fun t _ => (hA t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hQuadratic t).differentiableAt.differentiableWithinAt)
      (fun t _ => by
        rw [(hA t).deriv, (hQuadratic t).deriv, hVelocityEq t])
      (Set.mem_univ t0) (by simp)
    exact fun t => hEq (Set.mem_univ t)
  have hVelocitySelf : IsSelfAdjoint (velocity t0) := by
    have hStarDerivative := (hA t0).star
    have hStarA : (fun t => star (A t)) = A := by
      funext t
      exact (hSelf t).star_eq
    rw [hStarA] at hStarDerivative
    exact hStarDerivative.unique (hA t0)
  let H := algebraMap ℝ B t0 - (1 / 2 : ℝ) • velocity t0
  have hHSelf : IsSelfAdjoint H := by
    apply IsSelfAdjoint.sub
    · exact IsSelfAdjoint.algebraMap B (by rfl)
    · exact (by rfl : IsSelfAdjoint (1 / 2 : ℝ)).smul hVelocitySelf
  refine ⟨hHSelf, ?_, fun t => (hHSelf.sub
    (IsSelfAdjoint.algebraMap B (by rfl))).sq_nonneg⟩
  intro t
  rw [hAEq t, hJet]
  have hDifference : t - t0 = -(t0 - t) := by ring
  have hSquareDifference : (t - t0) ^ 2 = (t0 - t) ^ 2 := by ring
  rw [hSquareDifference, hDifference]
  have hMapDifference :
      algebraMap ℝ B t0 - (1 / 2 : ℝ) • velocity t0 - algebraMap ℝ B t =
        algebraMap ℝ B (t0 - t) - (1 / 2 : ℝ) • velocity t0 := by
    rw [map_sub]
    abel
  rw [hMapDifference]
  set d : ℝ := t0 - t
  simp only [Algebra.algebraMap_eq_smul_one, pow_two, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

#print axioms flat_quadratic_observer_bundle

end D5.S3.Analytic.Adelic.FlatQuadraticObserverBundle
