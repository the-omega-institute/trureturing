/- GID: D5/S3/Quantum/Sharpness/SharpEffectComplementBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SharpEffectComplementBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Projection complement has no fixed projection; effect complement fixes the half-identity. -/

import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * Loogle and LeanSearch executables were unavailable in the pinned environment.
   * Pinned Mathlib has the exact projection-closure result `IsStarProjection.one_sub` and the
     idempotence projection `IsStarProjection.isIdempotentElem` in StarProjection.lean.
   * Pinned Mathlib has `ContinuousLinearMap.IsPositive`, `isPositive_one`, and
     `IsPositive.smul_of_nonneg` in InnerProductSpace/Positive.lean.
   * Repository searches found no theorem combining projection non-fixedness with the effect
     half-identity boundary. The exact supporting Mathlib results are applied below. -/

open scoped ComplexOrder

namespace D5.S3.Quantum.Sharpness.SharpEffectComplementBoundary

example : Nonempty (ℂ →L[ℂ] ℂ) := ⟨1⟩

example : ∀ E : ℂ →L[ℂ] ℂ, E + 1 ≠ E := by
  intro E hfixed
  have hzero : (1 : ℂ →L[ℂ] ℂ) = 0 := by
    have := congrArg (fun T : ℂ →L[ℂ] ℂ => T - E) hfixed
    simpa only [add_sub_cancel_left, sub_self] using this
  exact one_ne_zero hzero

/-- On a nonzero finite-dimensional complex Hilbert space, ordinary complement preserves sharp
projections and has no fixed sharp projection. The half-identity and its complement are positive
effects and coincide. Consequently, a twist that has no fixed point on any effect cannot be
ordinary effect complement. -/
theorem sharp_effect_complement_boundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] [Nontrivial H] :
    (∀ P : H →L[ℂ] H, IsStarProjection P →
      IsStarProjection (1 - P) ∧ 1 - P ≠ P) ∧
      (let half : H →L[ℂ] H := ((2 : ℝ)⁻¹ : ℂ) • 1
       half.IsPositive ∧ (1 - half).IsPositive ∧ 1 - half = half) ∧
      (∀ twist : (H →L[ℂ] H) → (H →L[ℂ] H),
        (∀ E, E.IsPositive ∧ (1 - E).IsPositive → twist E ≠ E) →
          twist ≠ fun E => 1 - E) := by
  have projection_complement_ne (P : H →L[ℂ] H) (hP : IsStarProjection P) :
      1 - P ≠ P := by
    intro hfixed
    have htwo : P + P = 1 := by
      calc
        P + P = P + (1 - P) := by rw [hfixed]
        _ = 1 := by abel
    have hsum := congrArg (fun Q : H →L[ℂ] H => Q * P) htwo
    have hzero : P = 0 := by
      simpa [add_mul, hP.isIdempotentElem.eq] using hsum
    have : (0 : H →L[ℂ] H) = 1 := by
      simpa only [hzero, zero_add] using htwo
    exact zero_ne_one this
  let half : H →L[ℂ] H := ((2 : ℝ)⁻¹ : ℂ) • 1
  have half_pos : half.IsPositive := by
    exact ContinuousLinearMap.isPositive_one.smul_of_nonneg (by positivity)
  have half_fixed : 1 - half = half := by
    simp [half]
    module
  have complement_pos : (1 - half).IsPositive := by
    rw [half_fixed]
    exact half_pos
  refine ⟨fun P hP => ⟨hP.one_sub, projection_complement_ne P hP⟩,
    ⟨half_pos, complement_pos, half_fixed⟩, ?_⟩
  intro twist htwist heq
  have hne := htwist half ⟨half_pos, complement_pos⟩
  apply hne
  rw [heq]
  exact half_fixed

end D5.S3.Quantum.Sharpness.SharpEffectComplementBoundary
