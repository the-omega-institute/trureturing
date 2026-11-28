/- GID: D5/S3/Geometry/UnitQuaternions/SU2ErrorTransfer
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit quadratic transfer of triangle defects and fitting residuals between imaginary quaternions and the full round unit-quaternion group. -/

import D5.S3.Geometry.UnitQuaternions.SU2Quantitative

/-! Omega original.

Explicit quadratic transfer of triangle defects and fitting residuals between
imaginary quaternions and the full round unit-quaternion group.
-/

noncomputable section
open scoped Quaternion InnerProductSpace
open NormedSpace

namespace Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

theorem expUnit_neg (X : ℍ[ℝ]) (hX : X.re = 0) :
    expUnit (-X) (by simp [hX]) = (expUnit X hX)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Subtype.ext
  simpa using exp_smul_mul_neg (-X) 1

/-- The principal-radius identity, including the boundary radius pi. -/
theorem round_expUnit_eq_norm (X : ℍ[ℝ]) (hX : X.re = 0) (hpi : ‖X‖ ≤ Real.pi) :
    roundDist 1 (expUnit X hX) = ‖X‖ := by
  have hi : ⟪(1 : ℍ[ℝ]), exp X⟫_ℝ = Real.cos ‖X‖ := by
    simp [Quaternion.inner_def, Quaternion.exp_of_re_eq_zero X hX, hX]
  change Real.arccos ⟪(1 : ℍ[ℝ]), exp X⟫_ℝ = ‖X‖
  rw [hi, Real.arccos_cos (norm_nonneg X) hpi]

/-- Reverse triangle inequality for the reusable round metric. -/
theorem abs_round_sub_le (a b c : U) :
    |roundDist a b - roundDist a c| ≤ roundDist b c := by
  apply abs_le.mpr
  have h₁ := round_triangle a b c
  have h₂ := round_triangle a c b
  rw [round_comm c b] at h₂
  constructor <;> linarith

/-- Applying the global product bound twice gives the audited triple bound. -/
theorem round_exp_triple_le (X Y Z : ℍ[ℝ])
    (hX : X.re = 0) (hY : Y.re = 0) (hZ : Z.re = 0) :
    roundDist (expUnit X hX * expUnit Y hY * expUnit Z hZ)
      (expUnit (X + Y + Z) (by simp [hX, hY, hZ])) ≤
      ‖X‖ * ‖Y‖ + ‖X + Y‖ * ‖Z‖ := by
  apply (round_triangle _ (expUnit (X + Y) (by simp [hX, hY]) * expUnit Z hZ) _).trans
  rw [round_mul_right]
  exact add_le_add (round_exp_mul_le X Y hX hY)
    (round_exp_mul_le (X + Y) Z (by simp [hX, hY]) hZ)

/-- Explicit triple-defect transfer, with the precise unscaled coefficient. -/
theorem scaled_triple_error (X Y Z : ℍ[ℝ])
    (hX : X.re = 0) (hY : Y.re = 0) (hZ : Z.re = 0)
    {t : ℝ} (ht : 0 ≤ t) (hpi : t * ‖X + Y + Z‖ ≤ Real.pi) :
    |roundDist 1 (expPath X hX t * expPath Y hY t * expPath Z hZ t) -
      t * ‖X + Y + Z‖| ≤ t ^ 2 * (‖X‖ * ‖Y‖ + ‖X + Y‖ * ‖Z‖) := by
  have he : t • X + t • Y + t • Z = t • (X + Y + Z) := by module
  have hn : ‖t • (X + Y + Z)‖ = t * ‖X + Y + Z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have h := (abs_round_sub_le 1
    (expPath X hX t * expPath Y hY t * expPath Z hZ t)
    (expUnit (t • X + t • Y + t • Z) (by simp [hX, hY, hZ]))).trans
      (round_exp_triple_le (t • X) (t • Y) (t • Z)
        (by simp [hX]) (by simp [hY]) (by simp [hZ]))
  rw [round_expUnit_eq_norm _ _ (by rw [he, hn]; exact hpi), he, hn] at h
  convert h using 1
  rw [← smul_add, norm_smul, norm_smul, norm_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht]
  ring

/-- Source (2.3), before taking a finite maximum over triangles. -/
theorem triangle_error_le (X Y Z : ℍ[ℝ])
    (hX : X.re = 0) (hY : Y.re = 0) (hZ : Z.re = 0)
    {t M : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hXM : ‖X‖ ≤ M) (hYM : ‖Y‖ ≤ M) (hZM : ‖Z‖ ≤ M)
    (hsmall : t * (3 * M) ≤ Real.pi) :
    |roundDist 1 (expPath X hX t * expPath Y hY t * expPath Z hZ t) -
      t * ‖X + Y + Z‖| ≤ 3 * M ^ 2 * t ^ 2 := by
  have hXY : ‖X + Y‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
  have hsum : ‖X + Y + Z‖ ≤ 3 * M := (norm_add_le _ _).trans (by linarith)
  have hc : ‖X‖ * ‖Y‖ + ‖X + Y‖ * ‖Z‖ ≤ 3 * M ^ 2 := by
    have h₁ := mul_le_mul hXM hYM (norm_nonneg Y) hM
    have h₂ := mul_le_mul hXY hZM (norm_nonneg Z) (by linarith : 0 ≤ 2 * M)
    nlinarith
  exact (scaled_triple_error X Y Z hX hY hZ ht
    ((mul_le_mul_of_nonneg_left hsum ht).trans hsmall)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg t)])

/-- The pointwise fitting comparison for exponential potentials. -/
theorem scaled_edge_error (a u v : ℍ[ℝ])
    (ha : a.re = 0) (hu : u.re = 0) (hv : v.re = 0)
    {t : ℝ} (ht : 0 ≤ t) (hpi : t * ‖-a - u + v‖ ≤ Real.pi) :
    |roundDist (expPath a ha t) ((expPath u hu t)⁻¹ * expPath v hv t) -
      t * ‖a - (v - u)‖| ≤ t ^ 2 * (‖a‖ * ‖u‖ + ‖a + u‖ * ‖v‖) := by
  have h := scaled_triple_error (-a) (-u) v (by simp [ha]) (by simp [hu]) hv ht
    (by simpa only [sub_eq_add_neg] using hpi)
  have hneg (x : ℍ[ℝ]) (hx : x.re = 0) :
      expPath (-x) (by simp [hx]) t = (expPath x hx t)⁻¹ := by
    simpa only [expPath, smul_neg] using expUnit_neg (t • x) (by simp [hx])
  rw [hneg a ha, hneg u hu] at h
  have hd : roundDist 1 ((expPath a ha t)⁻¹ * (expPath u hu t)⁻¹ * expPath v hv t) =
      roundDist (expPath a ha t) ((expPath u hu t)⁻¹ * expPath v hv t) := by
    rw [← round_mul_left (expPath a ha t)]
    simp [mul_assoc]
  rw [hd, show -a + -u + v = -(a - (v - u)) by abel, norm_neg,
    show -a + -u = -(a + u) by abel, norm_neg, norm_neg, norm_neg] at h
  exact h

/-- Source (2.4)'s explicit edge error for bounded potentials. This is uniform
over all edges and over either choice of bounded potential. -/
theorem edge_error_le (a u v : ℍ[ℝ])
    (ha : a.re = 0) (hu : u.re = 0) (hv : v.re = 0)
    {t M D : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (haM : ‖a‖ ≤ M) (huM : ‖u‖ ≤ 2 * D * M) (hvM : ‖v‖ ≤ 2 * D * M)
    (hsmall : t * (M * (1 + 4 * D)) ≤ Real.pi) :
    |roundDist (expPath a ha t) ((expPath u hu t)⁻¹ * expPath v hv t) -
      t * ‖a - (v - u)‖| ≤ 4 * D * (D + 1) * M ^ 2 * t ^ 2 := by
  have hsum : ‖-a - u + v‖ ≤ M * (1 + 4 * D) := by
    have h₁ := norm_sub_le (-a) u
    have h₂ := norm_add_le (-a - u) v
    rw [norm_neg] at h₁
    nlinarith
  have hau : ‖a + u‖ ≤ M + 2 * D * M := (norm_add_le _ _).trans (by linarith)
  have hB : 0 ≤ 2 * D * M := by positivity
  have hc : ‖a‖ * ‖u‖ + ‖a + u‖ * ‖v‖ ≤ 4 * D * (D + 1) * M ^ 2 := by
    have h₁ := mul_le_mul haM huM (norm_nonneg u) hM
    have h₂ := mul_le_mul hau hvM (norm_nonneg v) (by positivity : 0 ≤ M + 2 * D * M)
    nlinarith
  exact (scaled_edge_error a u v ha hu hv ht
    ((mul_le_mul_of_nonneg_left hsum ht).trans hsmall)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg t)])

end Omega.Geometry.UnitQuaternion
