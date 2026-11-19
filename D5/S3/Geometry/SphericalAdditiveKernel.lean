/- GID: D5/S3/Geometry/SphericalAdditiveKernel
   generality: G
   mirror-B: D5/B/S3/Geometry/SphericalAdditiveKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: An additive subgroup containing a positive-radius sphere but no half-radius vector forces dimension at most one. -/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

noncomputable section
public section

open scoped InnerProductSpace

namespace D5.S3.Geometry.SphericalAdditiveKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An additive subgroup cannot contain a whole positive-radius sphere and
avoid the sphere of half that radius in a space of dimension at least two. -/
theorem finrank_le_one_of_sphere_mem (K : AddSubgroup E) {r : ℝ} (hr : 0 < r)
    (hsphere : ∀ x : E, ‖x‖ = r → x ∈ K)
    (hhalf : ∀ x : E, ‖x‖ = r / 2 → x ∉ K) :
    Module.finrank ℝ E ≤ 1 := by
  classical
  by_contra hd
  have hdim : 2 ≤ Module.finrank ℝ E := by omega
  let b := stdOrthonormalBasis ℝ E
  let i : Fin (Module.finrank ℝ E) := ⟨0, by omega⟩
  let j : Fin (Module.finrank ℝ E) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [i, j] at hh
  have horth : ⟪b i, b j⟫_ℝ = 0 := b.inner_eq_zero hij
  let u : E := (r / 4) • b i + (Real.sqrt 15 * r / 4) • b j
  let v : E := -(r / 4) • b i + (Real.sqrt 15 * r / 4) • b j
  have hsqrt : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hu_sq : ‖u‖ ^ 2 = r ^ 2 := by
    simp only [u, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, b.norm_eq_one, one_pow, mul_one,
      real_inner_smul_left, real_inner_smul_right, horth, mul_zero, add_zero]
    rw [div_pow, div_pow, mul_pow, hsqrt]
    ring
  have hv_sq : ‖v‖ ^ 2 = r ^ 2 := by
    simp only [v, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, b.norm_eq_one, one_pow, mul_one, neg_sq,
      real_inner_smul_left, real_inner_smul_right, horth, mul_zero, add_zero]
    rw [div_pow, div_pow, mul_pow, hsqrt]
    ring
  have hu : ‖u‖ = r := by nlinarith [norm_nonneg u]
  have hv : ‖v‖ = r := by nlinarith [norm_nonneg v]
  have hsub : u - v = (r / 2) • b i := by
    dsimp only [u, v]
    module
  have hnorm : ‖u - v‖ = r / 2 := by
    rw [hsub, norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
  exact hhalf (u - v) hnorm (K.sub_mem (hsphere u hu) (hsphere v hv))

end D5.S3.Geometry.SphericalAdditiveKernel
