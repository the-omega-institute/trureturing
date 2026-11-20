/- GID: D5/S3/Quantum/PureState/ReflectionInvariantBornForm
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/ReflectionInvariantBornForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A reflection-invariant normalized quadratic reading is the Born weight. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# The Born form from one reflection

Let `f ψ φ` be a real reading on a complex inner product space. For each unit vector `φ`, assume
that `ψ ↦ f ψ φ` is `‖c‖ ^ 2`-homogeneous under complex scalars and satisfies the parallelogram
law, is invariant under the reflection `ψ ↦ 2 ⟪φ, ψ⟫ φ - ψ` fixing `φ`, equals one at `φ` and
vanishes at unit vectors orthogonal to `φ`. Then `f ψ φ = ‖⟪φ, ψ⟫‖ ^ 2`. A Hermitian form
`ψ ↦ re ⟪ψ, T ψ⟫` with `T` complex linear is the special case where both regularity conditions
hold automatically.

Write `ψ = z φ + w` with `z = ⟪φ, ψ⟫` and `w ⟂ φ`. The reflection sends `z φ + w` to `z φ - w`;
invariance under it and the parallelogram law make the cross term between `span φ` and the
orthogonal complement vanish, so the reading splits as `f (z φ) φ + f w φ = ‖z‖ ^ 2 + 0`.
-/

namespace D5.S3.Quantum.PureState.ReflectionInvariantBornForm

open scoped InnerProductSpace

/-- A reading that, in its first argument, is `‖c‖ ^ 2`-homogeneous under complex scalars and
satisfies the parallelogram law, is invariant under the reflection `ψ ↦ 2 ⟪φ, ψ⟫ φ - ψ` fixing
the second argument, is one on the diagonal and zero on orthogonal unit pairs, is the Born weight
`‖⟪φ, ψ⟫‖ ^ 2` for every `ψ`. -/
theorem eq_norm_inner_sq_of_reflection_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f : E → E → ℝ)
    (hsmul : ∀ φ : E, ‖φ‖ = 1 → ∀ (c : ℂ) (ψ : E), f (c • ψ) φ = ‖c‖ ^ 2 * f ψ φ)
    (hpar : ∀ φ : E, ‖φ‖ = 1 → ∀ ψ χ : E,
      f (ψ + χ) φ + f (ψ - χ) φ = 2 * f ψ φ + 2 * f χ φ)
    (hrefl : ∀ φ ψ : E, ‖φ‖ = 1 → f ((2 * ⟪φ, ψ⟫_ℂ) • φ - ψ) φ = f ψ φ)
    (hone : ∀ φ : E, ‖φ‖ = 1 → f φ φ = 1)
    (hzero : ∀ φ ψ : E, ‖φ‖ = 1 → ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 → f ψ φ = 0) :
    ∀ φ ψ : E, ‖φ‖ = 1 → f ψ φ = ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  intro φ ψ hφ
  set z := ⟪φ, ψ⟫_ℂ with hz
  set w := ψ - z • φ with hw
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hφw : ⟪φ, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hφφ, mul_one, hz, sub_self]
  -- The orthogonal part reads zero: rescale it to a unit vector.
  have hfw : f w φ = 0 := by
    by_cases hw0 : w = 0
    · have h := hsmul φ hφ 0 0
      rw [zero_smul] at h
      rw [hw0, h]; simp
    · have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw0
      have hu : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1 := norm_smul_inv_norm hw0
      have hφu : ⟪φ, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 0 := by
        rw [inner_smul_right, hφw, mul_zero]
      have h := hsmul φ hφ (‖w‖ : ℂ) (((‖w‖ : ℂ)⁻¹) • w)
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul, hzero φ _ hφ hu hφu, mul_zero] at h
      exact h
  have hψ : z • φ + w = ψ := by rw [hw]; abel
  -- The reflection fixing `φ` sends `z φ + w` to `z φ - w`.
  have hr : (2 * z) • φ - ψ = z • φ - w := by
    rw [← hψ, two_mul, add_smul]; abel
  have hpar' := hpar φ hφ (z • φ) w
  rw [hψ, ← hr, hz, hrefl φ ψ hφ, hsmul φ hφ, hone φ hφ, hfw] at hpar'
  linarith

end D5.S3.Quantum.PureState.ReflectionInvariantBornForm
