/- GID: D5/S3/Quantum/PureState/ReflectionInvariantBornForm
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/ReflectionInvariantBornForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized quadratic reading invariant under one reflection is the Born weight. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# The Born form from one reflection

Fix a vector `φ` of a complex inner product space and a real reading `g`. Assume that `g` is
`‖c‖ ^ 2`-homogeneous under complex scalars, satisfies the parallelogram law for the pairs
`(z φ, w)` with `w ⟂ φ`, is invariant under the reflection `ψ ↦ 2 ⟪φ, ψ⟫ φ - ψ` at unit vectors,
equals one at `φ` and vanishes at unit vectors orthogonal to `φ`. Then `g ψ = ‖⟪φ, ψ⟫‖ ^ 2`.
A Hermitian form `ψ ↦ re ⟪ψ, T ψ⟫` with `T` complex linear satisfies both regularity conditions.

The hypotheses force `‖φ‖ = 1`: with `r = ‖φ‖`, the reflection at the unit vector `φ / r` sends it
to `(2 r - 1 / r) φ`, and homogeneity with `g φ = 1` gives `(2 r - 1 / r) ^ 2 = 1 / r ^ 2`. Then
homogeneity extends the reflection invariance from unit vectors to all vectors. Write
`ψ = z φ + w` with `z = ⟪φ, ψ⟫` and `w ⟂ φ`. The reflection sends `z φ + w` to `z φ - w`;
invariance under it and the parallelogram law for `(z φ, w)` make the cross term vanish, so the
reading splits as `g (z φ) + g w = ‖z‖ ^ 2 + 0`.
-/

namespace D5.S3.Quantum.PureState.ReflectionInvariantBornForm

open scoped InnerProductSpace

/-- Homogeneity, reflection invariance at unit vectors and `g φ = 1` force `‖φ‖ = 1`. -/
private theorem norm_one_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (φ : E)
    (g : E → ℝ) (hsmul : ∀ (c : ℂ) (ψ : E), g (c • ψ) = ‖c‖ ^ 2 * g ψ)
    (hrefl : ∀ ψ : E, ‖ψ‖ = 1 → g ((2 * ⟪φ, ψ⟫_ℂ) • φ - ψ) = g ψ)
    (hone : g φ = 1) : ‖φ‖ = 1 := by
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := hsmul 0 0
    rw [zero_smul, hone] at this
    norm_num at this
  set r := ‖φ‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 h0
  have hu : ‖((r : ℂ)⁻¹) • φ‖ = 1 := norm_smul_inv_norm h0
  have h := hrefl _ hu
  have hin : ⟪φ, ((r : ℂ)⁻¹) • φ⟫_ℂ = (r : ℂ) := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, ← hr]
    field_simp [hrpos.ne']
    rfl
  have hv : (2 * ⟪φ, ((r : ℂ)⁻¹) • φ⟫_ℂ) • φ - ((r : ℂ)⁻¹) • φ
      = ((2 * (r : ℂ) - (r : ℂ)⁻¹)) • φ := by
    rw [hin, sub_smul]
  rw [hv, hsmul, hsmul, hone] at h
  have hn : ‖(2 * (r : ℂ) - (r : ℂ)⁻¹)‖ = |2 * r - r⁻¹| := by
    rw [show (2 * (r : ℂ) - (r : ℂ)⁻¹) = ((2 * r - r⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hm : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  rw [hn, hm, sq_abs, mul_one, mul_one] at h
  have h2 : (2 * r ^ 2 - 1) ^ 2 = 1 := by
    have := congrArg (· * r ^ 2) h
    field_simp at this
    nlinarith [this]
  have hf : (2 * r ^ 2 - 2) * (2 * r ^ 2) = 0 := by nlinarith [h2]
  have : r ^ 2 = 1 := by
    rcases mul_eq_zero.1 hf with h | h
    · linarith
    · nlinarith [mul_pos hrpos hrpos]
  nlinarith [this, hrpos]

/-- For a vector `φ`, a reading `g` that is `‖c‖ ^ 2`-homogeneous under complex scalars,
satisfies the parallelogram law for the pairs `(z φ, w)` with `w` orthogonal to `φ`, is invariant
under the reflection `ψ ↦ 2 ⟪φ, ψ⟫ φ - ψ` at unit vectors, is one at `φ` and zero at unit vectors
orthogonal to `φ`, is the Born weight `‖⟪φ, ψ⟫‖ ^ 2` for every `ψ`; the hypotheses force
`‖φ‖ = 1`. -/
theorem eq_norm_inner_sq_of_reflection_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (φ : E) (g : E → ℝ)
    (hsmul : ∀ (c : ℂ) (ψ : E), g (c • ψ) = ‖c‖ ^ 2 * g ψ)
    (hpar : ∀ (z : ℂ) (w : E), ⟪φ, w⟫_ℂ = 0 →
      g (z • φ + w) + g (z • φ - w) = 2 * g (z • φ) + 2 * g w)
    (hrefl : ∀ ψ : E, ‖ψ‖ = 1 → g ((2 * ⟪φ, ψ⟫_ℂ) • φ - ψ) = g ψ)
    (hone : g φ = 1)
    (hzero : ∀ ψ : E, ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 → g ψ = 0) :
    ∀ ψ : E, g ψ = ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  have hφ : ‖φ‖ = 1 := norm_one_of φ g hsmul hrefl hone
  -- Homogeneity extends the reflection invariance from unit vectors to all vectors.
  have hrefl' : ∀ ψ : E, g ((2 * ⟪φ, ψ⟫_ℂ) • φ - ψ) = g ψ := by
    intro ψ
    by_cases h0 : ψ = 0
    · subst h0; simp
    · have hn : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
      obtain ⟨u, hu, hψ⟩ : ∃ u : E, ‖u‖ = 1 ∧ ψ = (‖ψ‖ : ℂ) • u :=
        ⟨_, norm_smul_inv_norm h0, (smul_inv_smul₀ hn ψ).symm⟩
      generalize (‖ψ‖ : ℂ) = r at hψ
      subst hψ
      have key : (2 * ⟪φ, r • u⟫_ℂ) • φ - r • u = r • ((2 * ⟪φ, u⟫_ℂ) • φ - u) := by
        rw [inner_smul_right, smul_sub, smul_smul, mul_left_comm]
      rw [key, hsmul, hrefl u hu, ← hsmul]
  intro ψ
  set z := ⟪φ, ψ⟫_ℂ with hz
  set w := ψ - z • φ with hw
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hφw : ⟪φ, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hφφ, mul_one, hz, sub_self]
  -- The orthogonal part reads zero: rescale it to a unit vector.
  have hgw : g w = 0 := by
    by_cases hw0 : w = 0
    · have h := hsmul 0 0
      rw [zero_smul] at h
      rw [hw0, h]; simp
    · have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw0
      have hu : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1 := norm_smul_inv_norm hw0
      have hφu : ⟪φ, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 0 := by
        rw [inner_smul_right, hφw, mul_zero]
      have h := hsmul (‖w‖ : ℂ) (((‖w‖ : ℂ)⁻¹) • w)
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul, hzero _ hu hφu, mul_zero] at h
      exact h
  have hψ : z • φ + w = ψ := by rw [hw]; abel
  -- The reflection fixing `φ` sends `z φ + w` to `z φ - w`.
  have hr : (2 * z) • φ - ψ = z • φ - w := by
    rw [← hψ, two_mul, add_smul]; abel
  have hpar' := hpar z w hφw
  rw [hψ, ← hr, hz, hrefl' ψ, hsmul, hone, hgw] at hpar'
  linarith

end D5.S3.Quantum.PureState.ReflectionInvariantBornForm
