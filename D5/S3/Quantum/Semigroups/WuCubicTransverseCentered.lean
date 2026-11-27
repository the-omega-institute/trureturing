import D5.S3.Quantum.Semigroups.WuCubicConditionedHessian
import D5.S3.Quantum.Semigroups.WuCubicHessianResolvent
import D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy

/-! Local centered curvature of the actual Wu cubic operator deficit in an embedded
Hermitian direction. The mixed-generator inequality enters at the base point. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set Filter
open scoped Asymptotics ComplexOrder MatrixOrder Matrix.Norms.L2Operator Pointwise Topology

namespace D5.S3.Quantum.Semigroups.WuCubicTransverseCentered

open WuCubicOperatorBridge (Mat Occupation D G GInv)
open WuCubicOperatorNormalization (operatorDeficit operatorDeficit_eq_scaled)
open WuCubicConditionedHessian (embeddedGenerator physical_curvature_ge cubic_mass_ge
  mass_log_second_hasDerivAt)
open WuCubicHessianResolvent (cubicLog_centered_le)
open WuCubicHotInnerEntropy (entropyFactor)
open WuRepeatedMiddleCubic (alpha)
open private embedded_generator_affine cubic_mass_hasDerivAt from
  D5.S3.Quantum.Semigroups.WuCubicConditionedHessian
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private G_adjoint recover_embedded scaled_diagonal from
  D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
open WuCubicAngularCertificate (physicalFrame)
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private eventually_posDef from D5.S3.Quantum.Divergence.TraceEntropyCalculus
open private log_cube from D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy

private theorem trace_real_smul (a : ℝ) (X : Mat) :
    (a • X).trace.re = a * X.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private theorem energy_centered (r : ℝ) (M W : Mat) (t : ℝ) :
    let E := fun s : ℝ => (9 / 8 : ℝ) *
      ((M + s • W) ^ 2 * embeddedGenerator r (M + s • W)).trace.re
    E t + E (-t) - 2 * E 0 = t ^ 2 * ((9 / 4 : ℝ) *
      (W ^ 2 * embeddedGenerator r M + (M * W + W * M) * embeddedGenerator r W).trace.re) := by
  intro E
  let N := embeddedGenerator r M
  let V := embeddedGenerator r W
  let P := fun s : ℝ => (M + s • W) ^ 2 * (N + s • V)
  have h (s : ℝ) : E s = (9 / 8 : ℝ) * (P s).trace.re := by
    dsimp only [E, P, N, V]
    rw [embedded_generator_affine]
  have hc : P t + P (-t) - (2 : ℝ) • P 0 =
      (2 * t ^ 2) • (W ^ 2 * N + (M * W + W * M) * V) := by
    simp only [P, pow_two, add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      smul_add, smul_smul, mul_assoc]
    module
  have htr := congrArg (fun X : Mat => X.trace.re) hc
  rw [h t, h (-t), h 0]
  change _ = t ^ 2 * ((9 / 4 : ℝ) * (W ^ 2 * N + (M * W + W * M) * V).trace.re)
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    trace_real_smul] at htr ⊢
  linear_combination (9 / 8 : ℝ) * htr

private theorem reference_centered (M W K : Mat) (t : ℝ) :
    let R := fun s : ℝ => ((M + s • W) ^ 3 * K).trace.re
    R t + R (-t) - 2 * R 0 =
      t ^ 2 * (2 * ((M * W ^ 2 + W * M * W + W ^ 2 * M) * K).trace.re) := by
  intro R
  have hc : (M + t • W) ^ 3 + (M + (-t) • W) ^ 3 - (2 : ℝ) • M ^ 3 =
      (2 * t ^ 2) • (M * W ^ 2 + W * M * W + W ^ 2 * M) := by
    simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, mul_smul_comm,
      smul_mul_assoc, smul_add, smul_smul, mul_assoc]
    module
  have htr := congrArg (fun X : Mat => (X * K).trace.re) hc
  simp only [R, zero_smul, add_zero]
  simp only [add_mul, sub_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, trace_real_smul] at htr ⊢
  linear_combination htr

private theorem massLog_centered_isLittleO (M W : Mat) (hT : 0 < (M ^ 3).trace.re) :
    let Z := fun s : ℝ => ((M + s • W) ^ 3).trace.re * Real.log ((M + s • W) ^ 3).trace.re
    let c := 6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
      9 * ((M ^ 2 * W).trace.re) ^ 2 / (M ^ 3).trace.re
    (fun t : ℝ => Z t + Z (-t) - 2 * Z 0 - c * t ^ 2) =o[𝓝 0] (fun t => t ^ 2) := by
  intro Z c
  let T := fun s : ℝ => ((M + s • W) ^ 3).trace.re
  have hT0 : 0 < T 0 := by simpa [T] using hT
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < T s :=
    (cubic_mass_hasDerivAt M W 0).continuousAt.eventually (lt_mem_nhds hT0)
  obtain ⟨l, u, h0, hI⟩ := hpos.exists_Ioo_subset
  have hZ (s : ℝ) (hs : s ∈ Ioo l u) : HasDerivAt Z (deriv Z s) s := by
    have hd := (cubic_mass_hasDerivAt M W s).differentiableAt
    exact (hd.mul ((Real.differentiableAt_log (hI hs).ne').comp s hd)).hasDerivAt
  let R := fun t : ℝ => Z t - deriv Z 0 * t - (c / 2) * t ^ 2
  have hR (s : ℝ) (hs : s ∈ Ioo l u) :
      HasDerivAt R (deriv Z s - deriv Z 0 - c * s) s := by
    have hi := hasDerivAt_id' s
    refine (((hZ s hs).sub (hi.const_mul (deriv Z 0))).sub
      ((hi.fun_pow 2).const_mul (c / 2))).congr_deriv ?_
    ring
  have hd := (mass_log_second_hasDerivAt M W hT).isLittleO
  change (fun s : ℝ => deriv Z s - deriv Z 0 - (s - 0) • c) =o[𝓝 0]
    (fun s : ℝ => s - 0) at hd
  have hsmall : (fun s : ℝ => deriv Z s - deriv Z 0 - c * s)
      =o[𝓝[Ioo l u] 0] (fun s : ℝ => (s - 0) ^ 1) := by
    simpa only [sub_zero, pow_one, smul_eq_mul, mul_comm] using hd.mono nhdsWithin_le_nhds
  have hrem := (convex_Ioo l u).isLittleO_pow_succ_real h0
    (fun s hs => (hR s hs).hasDerivWithinAt) hsmall
  rw [isOpen_Ioo.nhdsWithin_eq h0] at hrem
  have hrem' : (fun t : ℝ => R t - R 0) =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
    simpa only [sub_zero] using hrem
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℝ))
  have hremNeg : (fun t : ℝ => R (-t) - R 0) =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
    simpa only [Function.comp_def, neg_sq] using hrem'.comp_tendsto hneg
  convert hrem'.add hremNeg using 1
  funext t
  simp only [R, mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), neg_sq]
  ring

private theorem entropy_majorant_eq (M W : Mat) (hM : M.IsHermitian) :
    2 * (W ^ 2 * ((15 / 2 : ℝ) • M + (9 : ℝ) • (M * cfc Real.log M))).trace.re =
      (W ^ 2 * cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M).trace.re := by
  have hc (f : ℝ → ℝ) := M.finite_real_spectrum.continuousOn f
  have he : cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M =
      (15 : ℝ) • M + (18 : ℝ) • (M * cfc Real.log M) := by
    rw [cfc_add M _ _ (hc _) (hc _), cfc_const_mul_id _ M hM.isSelfAdjoint]
    rw [show (fun x : ℝ => 18 * x * Real.log x) = fun x => 18 * (id x * Real.log x) by
      funext x
      dsimp only [id]
      ring]
    rw [cfc_const_mul _ _ M (hc _), cfc_mul id Real.log M (hc _) (hc _),
      cfc_id ℝ M hM.isSelfAdjoint]
  rw [he]
  simp only [mul_add, mul_smul_comm, Matrix.trace_add, Complex.add_re, trace_real_smul]
  ring

private theorem small_signed_smul (A : Mat) (hA : IsSelfAdjoint A) :
    ∀ᶠ t : ℝ in 𝓝 0, (-(1 / 2 : ℝ)) • (1 : Mat) ≤ t • A ∧
      (-(1 / 2 : ℝ)) • (1 : Mat) ≤ (-t) • A := by
  have hsmall (s : ℝ) (hs : ‖s • A‖ ≤ 1 / 2) :
      (-(1 / 2 : ℝ)) • (1 : Mat) ≤ s • A := by
    have hsa : IsSelfAdjoint (s • A) := IsSelfAdjoint.smul (show IsSelfAdjoint s from rfl) hA
    have h := hsa.neg_algebraMap_norm_le_self (a := s • A)
    rw [Algebra.algebraMap_eq_smul_one, ← neg_smul] at h
    exact (smul_le_smul_of_nonneg_right (neg_le_neg hs) Matrix.PosSemidef.one.nonneg).trans h
  have hn : Tendsto (fun t : ℝ => ‖t • A‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => ‖t • A‖) :=
      (continuous_id.smul continuous_const).norm
    simpa only [zero_smul, norm_zero] using hc.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [hn.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with t ht
  exact ⟨hsmall t ht, hsmall (-t) (by simpa only [neg_smul, norm_neg] using ht)⟩

private theorem trace_square_pos (W : Mat) (hW : W.IsHermitian) (hn : W ≠ 0) :
    0 < (W ^ 2).trace.re := by
  rw [pow_two, show W * W = Wᴴ * W by rw [hW.eq]]
  have h := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self W).trace_nonneg
  refine lt_of_le_of_ne h.1 fun he => hn ?_
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (Complex.ext he.symm h.2.symm)

/-- At a normalized conditioned matrix, the centered difference of the ordinary-trace
operator deficit has a positive local quadratic lower bound in every nonzero Hermitian
direction satisfying the mixed-generator inequality. -/
theorem operatorDeficit_centered_ge_normalized {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian) (hWne : W ≠ 0)
    (hlo : (5 / 9 : ℝ) • (1 : Mat) ≤ M) (hhi : M ≤ 1)
    (htrace : 3 ≤ M.trace.re) (hmax : ∃ i, hM.isHermitian.eigenvalues i = 1)
    (hmixed : (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * embeddedGenerator r W).trace.re) :
    let F := fun t : ℝ => operatorDeficit r (GInv r * (M + t • W) * GInv r)
    ∀ᶠ t : ℝ in 𝓝 0,
      (1 / 10 : ℝ) * (W ^ 2).trace.re * t ^ 2 ≤ F t + F (-t) - 2 * F 0 := by
  intro F
  let Y := fun s : ℝ => M + s • W
  let E := fun s : ℝ => (9 / 8 : ℝ) * ((Y s) ^ 2 * embeddedGenerator r (Y s)).trace.re
  let B := fun s : ℝ => ((Y s) ^ 3 * cfc Real.log (Y s)).trace.re
  let K := cfc Real.log (D r)
  let R := fun s : ℝ => ((Y s) ^ 3 * K).trace.re
  let Z := fun s : ℝ => ((Y s) ^ 3).trace.re * Real.log ((Y s) ^ 3).trace.re
  let e := (9 / 4 : ℝ) *
    (W ^ 2 * embeddedGenerator r M + (M * W + W * M) * embeddedGenerator r W).trace.re
  let b := (W ^ 2 * cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M).trace.re
  let d := 2 * ((M * W ^ 2 + W * M * W + W ^ 2 * M) * K).trace.re
  let z := 6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
    9 * ((M ^ 2 * W).trace.re) ^ 2 / (M ^ 3).trace.re
  have hF (s : ℝ) : F s = E s - alpha r * (3 * B s) + alpha r * R s + alpha r * Z s := by
    have hY : (Y s).IsHermitian := hM.isHermitian.add (hW.smul (star_trivial s))
    change operatorDeficit r (GInv r * Y s * GInv r) = _
    unfold operatorDeficit
    dsimp only
    rw [recover_embedded hr, log_cube hY]
    simp only [E, B, K, R, Z, embeddedGenerator, mul_sub, mul_smul_comm,
      Matrix.trace_sub, Complex.sub_re, trace_real_smul]
    ring
  have hmass := cubic_mass_ge hM htrace hmax
  have hband (i : Occupation) : hM.isHermitian.eigenvalues i ∈ Icc (5 / 9 : ℝ) 1 :=
    ⟨(Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hM.isHermitian _).mpr hlo i,
      (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hM.isHermitian _).mpr
        (by simpa only [one_smul] using hhi) i⟩
  have hcurv : (1 / 5 : ℝ) * (W ^ 2).trace.re ≤ e - alpha r * b + alpha r * d + alpha r * z := by
    have hlo' : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M := by
      have hs : (5 / 9 : ℝ) • (1 : Mat) = ((5 / 9 : ℝ) : ℂ) • (1 : Mat) := by
        ext i j
        exact Complex.real_smul
      rwa [← hs]
    have h := physical_curvature_ge hr hrhi M W hM hW hlo'
      hhi hband hmass b le_rfl hmixed
    dsimp only [e, d, z, K, embeddedGenerator]
    linarith only [h]
  let S := CFC.sqrt M
  let A := S⁻¹ * W * S⁻¹
  have hS : S.IsHermitian := (CFC.sqrt_nonneg M).posSemidef.isHermitian
  have hSu : IsUnit S := CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hM.isStrictlyPositive
  let := hSu.invertible
  have hA : IsSelfAdjoint A := by
    change IsSelfAdjoint (S⁻¹ * W * S⁻¹)
    rw [isSelfAdjoint_iff, star_mul, star_mul, hS.inv.star_eq, hW.star_eq, mul_assoc]
  have hrecover : S * A * S = W := by
    rw [show S * A * S = (S * S⁻¹) * W * (S⁻¹ * S) by dsimp only [A]; noncomm_ring,
      Matrix.mul_inv_of_invertible S, Matrix.inv_mul_of_invertible S, one_mul, mul_one]
  let C := 2 * (entropyFactor (5 / 9) 1 (1 / 2) * (A ^ 4).trace.re)
  have hB : ∀ᶠ t : ℝ in 𝓝 0,
      3 * (B t + B (-t) - 2 * B 0) ≤ t ^ 2 * b + C * t ^ 4 := by
    filter_upwards [small_signed_smul A hA] with t ht
    have h := cubicLog_centered_le M A hM hA (bMinus := 5/9) (bPlus := 1)
      (by norm_num) (by norm_num) hlo (by simpa only [one_smul] using hhi) t ht.1 ht.2
    dsimp only at h
    rw [show CFC.sqrt M * A * CFC.sqrt M = W from hrecover] at h
    change 3 * (B t + B (-t) - 2 * B 0) ≤ _ at h
    calc
      _ ≤ _ := h
      _ = _ := by
        rw [mul_comm (2 : ℝ) (t ^ 2), mul_assoc, entropy_majorant_eq M W hM.isHermitian]
        dsimp only [b, C]
        ring
  let margin := (1 / 10 : ℝ) * (W ^ 2).trace.re
  have hmargin : 0 < margin := mul_pos (by norm_num) (trace_square_pos W hW hWne)
  have hα := (WuCubicOccupationTaylor.alpha_bounds_of_one_le hr).1
  have hZo := massLog_centered_isLittleO M W (by linarith)
  change (fun t : ℝ => Z t + Z (-t) - 2 * Z 0 - z * t ^ 2)
    =o[𝓝 0] (fun t : ℝ => t ^ 2) at hZo
  have hZsmall := (hZo.const_mul_left (alpha r)).bound (half_pos hmargin)
  have hCsmall : ∀ᶠ t : ℝ in 𝓝 0, alpha r * C * t ^ 2 ≤ margin / 2 := by
    have hc : Continuous (fun t : ℝ => alpha r * C * t ^ 2) :=
      continuous_const.mul (continuous_id.pow 2)
    have ht : Tendsto (fun t : ℝ => alpha r * C * t ^ 2) (𝓝 0) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        hc.continuousAt.tendsto (x := (0 : ℝ))
    exact ht.eventually_le_const (half_pos hmargin)
  filter_upwards [hB, hZsmall, hCsmall] with t htB htZ htC
  have hZbound : -(margin / 2 * t ^ 2) ≤
      alpha r * (Z t + Z (-t) - 2 * Z 0 - z * t ^ 2) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at htZ
    exact (abs_le.mp htZ).1
  have hCbound := mul_le_mul_of_nonneg_right htC (sq_nonneg t)
  have hbt := mul_le_mul_of_nonneg_left htB hα
  have hct := mul_le_mul_of_nonneg_right hcurv (sq_nonneg t)
  have he : E t + E (-t) - 2 * E 0 = t ^ 2 * e := energy_centered r M W t
  have hd : R t + R (-t) - 2 * R 0 = t ^ 2 * d := reference_centered M W K t
  change margin * t ^ 2 ≤ _
  rw [hF t, hF (-t), hF 0]
  rw [show (1 / 5 : ℝ) * (W ^ 2).trace.re = 2 * margin by dsimp [margin]; ring] at hct
  nlinarith only [he, congrArg (alpha r * ·) hd, hZbound, hCbound, hbt, hct]

/-- The normalized conditioned operator deficit has strictly positive symmetric
differences at every sufficiently small positive step. -/
theorem operatorDeficit_centered_pos_normalized {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian) (hWne : W ≠ 0)
    (hlo : (5 / 9 : ℝ) • (1 : Mat) ≤ M) (hhi : M ≤ 1)
    (htrace : 3 ≤ M.trace.re) (hmax : ∃ i, hM.isHermitian.eigenvalues i = 1)
    (hmixed : (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * embeddedGenerator r W).trace.re) :
    let F := fun t : ℝ => operatorDeficit r (GInv r * (M + t • W) * GInv r)
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → 2 * F 0 < F t + F (-t) := by
  intro F
  obtain ⟨l, u, h0, hI⟩ :=
    (operatorDeficit_centered_ge_normalized hr hrhi M W hM hW hWne hlo hhi
      htrace hmax hmixed).exists_Ioo_subset
  refine ⟨u, h0.2, fun t ht htu => ?_⟩
  have hb := hI (show t ∈ Ioo l u from ⟨h0.1.trans ht, htu⟩)
  have hp : 0 < (1 / 10 : ℝ) * (W ^ 2).trace.re * t ^ 2 :=
    mul_pos (mul_pos (by norm_num) (trace_square_pos W hW hWne)) (pow_pos ht 2)
  exact lt_of_sub_pos (hp.trans_le hb)

#print axioms operatorDeficit_centered_pos_normalized

private theorem operatorDeficit_embedded_scale {r : ℝ} (hr : 1 ≤ r)
    (c : ℝ) (M : Mat) (hM : M.PosDef) :
    operatorDeficit r (GInv r * (c • M) * GInv r) =
      c ^ 3 * operatorDeficit r (GInv r * M * GInv r) := by
  let X := GInv r * M * GInv r
  have hG : IsUnit (G r) := ⟨⟨G r, GInv r, G_mul_GInv hr, GInv_mul_G hr⟩, rfl⟩
  have hX : X.PosDef := hG.posDef_star_left_conjugate_iff.mp (by
    rw [Matrix.star_eq_conjTranspose, G_adjoint]
    change (G r * (GInv r * M * GInv r) * G r).PosDef
    rwa [recover_embedded hr])
  obtain ⟨U, ell, m, n, q, _, _, _, _, _, _, hframe, hdef⟩ :=
    WuCubicOperatorNormalization.exists_ordered_normalization hr hX.posSemidef hX.isUnit.ne_zero
  rw [recover_embedded hr] at hframe
  have hscaled : G r * (GInv r * (c • M) * GInv r) * G r =
      physicalFrame U * diagonal (fun i => (((c * ell) * levelsAt m n q i : ℝ) : ℂ)) *
        (physicalFrame U)ᴴ := by
    have he : (fun i => (((c * ell) * levelsAt m n q i : ℝ) : ℂ)) =
        fun i => ((c * (ell * levelsAt m n q i) : ℝ) : ℂ) :=
      funext fun i => congrArg Complex.ofReal (mul_assoc c ell (levelsAt m n q i))
    rw [recover_embedded hr, he, scaled_diagonal, ← hframe]
    rfl
  rw [operatorDeficit_eq_scaled hr _ U (c * ell) m n q hscaled, hdef, mul_pow, mul_assoc]

/-- The local symmetric difference at arbitrary positive maximal eigenvalue
has the normalized quadratic bound multiplied by the spectral scale. -/
theorem operatorDeficit_centered_ge {r L : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian) (hWne : W ≠ 0)
    (hL : 0 < L) (hlo : (5 / 9 * L : ℝ) • (1 : Mat) ≤ M) (hhi : M ≤ L • (1 : Mat))
    (htrace : 3 * L ≤ M.trace.re) (hmax : ∃ i, hM.isHermitian.eigenvalues i = L)
    (hmixed : (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * embeddedGenerator r W).trace.re) :
    let F := fun t : ℝ => operatorDeficit r (GInv r * (M + t • W) * GInv r)
    ∀ᶠ t : ℝ in 𝓝 0,
      L * ((1 / 10 : ℝ) * (W ^ 2).trace.re) * t ^ 2 ≤ F t + F (-t) - 2 * F 0 := by
  intro F
  let N := L⁻¹ • M
  have hLi := inv_pos.mpr hL
  have hLinv := inv_mul_cancel₀ hL.ne'
  have hN : N.PosDef := hM.smul hLi
  have hNlo : (5 / 9 : ℝ) • (1 : Mat) ≤ N := by
    have he : L⁻¹ * (5 / 9 * L) = 5 / 9 := by rw [mul_left_comm, hLinv, mul_one]
    simpa only [smul_smul, he] using smul_le_smul_of_nonneg_left hlo hLi.le
  have hNhi : N ≤ 1 := by
    simpa only [smul_smul, hLinv, one_smul] using smul_le_smul_of_nonneg_left hhi hLi.le
  have hNtrace : 3 ≤ N.trace.re := by
    have ht := mul_le_mul_of_nonneg_left htrace hLi.le
    rw [mul_left_comm L⁻¹, hLinv, mul_one] at ht
    simpa only [N, trace_real_smul] using ht
  have hLspec : L ∈ spectrum ℝ M := by
    rwa [hM.isHermitian.spectrum_real_eq_range_eigenvalues]
  have hNmax : ∃ i, hN.isHermitian.eigenvalues i = 1 := by
    change (1 : ℝ) ∈ Set.range hN.isHermitian.eigenvalues
    rw [← hN.isHermitian.spectrum_real_eq_range_eigenvalues]
    change (1 : ℝ) ∈ spectrum ℝ (L⁻¹ • M)
    rw [spectrum.smul_eq_smul _ _ ⟨L, hLspec⟩]
    exact ⟨L, hLspec, hLinv⟩
  have hNmixed : (15 / 4 : ℝ) * (N * W ^ 2).trace.re ≤
      ((N * W + W * N) * embeddedGenerator r W).trace.re := by
    simp only [N, smul_mul_assoc, mul_smul_comm, ← smul_add, trace_real_smul]
    rw [mul_left_comm (15 / 4 : ℝ)]
    exact mul_le_mul_of_nonneg_left hmixed hLi.le
  let P := fun s : ℝ => N + s • W
  let f := fun s : ℝ => operatorDeficit r (GInv r * P s * GInv r)
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ), (P s).PosDef := by
    have hc : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
    exact eventually_posDef hc.continuousAt
      (Eventually.of_forall fun s => hN.isHermitian.add (hW.smul (star_trivial s)))
      (by simpa only [P, zero_smul, add_zero] using hN)
  have hscale (t : ℝ) (ht : (P (L⁻¹ * t)).PosDef) : F t = L ^ 3 * f (L⁻¹ * t) := by
    have he : L • P (L⁻¹ * t) = M + t • W := by
      simp only [P, N, smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_smul, one_mul]
    rw [show F t = operatorDeficit r (GInv r * (L • P (L⁻¹ * t)) * GInv r) by rw [he]]
    exact operatorDeficit_embedded_scale hr L _ ht
  have ht : Tendsto (fun t : ℝ => L⁻¹ * t) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => L⁻¹ * t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using hc.continuousAt.tendsto (x := (0 : ℝ))
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℝ))
  have hb := operatorDeficit_centered_ge_normalized hr hrhi N W hN hW hWne
    hNlo hNhi hNtrace hNmax hNmixed
  filter_upwards [ht.eventually hb, ht.eventually hp, (ht.comp hn).eventually hp] with t hb hp hn
  have hp0 : (P (L⁻¹ * 0)).PosDef := by simpa only [P, mul_zero, zero_smul, add_zero] using hN
  rw [hscale t hp, hscale (-t) hn, hscale 0 hp0, mul_zero, mul_neg]
  change (1 / 10 : ℝ) * (W ^ 2).trace.re * (L⁻¹ * t) ^ 2 ≤
    f (L⁻¹ * t) + f (-(L⁻¹ * t)) - 2 * f 0 at hb
  have hs : L ^ 3 * (L⁻¹ * t) ^ 2 = L * t ^ 2 := by field_simp [hL.ne']
  calc
    _ = L ^ 3 * ((1 / 10 : ℝ) * (W ^ 2).trace.re * (L⁻¹ * t) ^ 2) := by
      rw [mul_left_comm (L ^ 3), mul_assoc, hs]
      ring
    _ ≤ L ^ 3 * (f (L⁻¹ * t) + f (-(L⁻¹ * t)) - 2 * f 0) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hL.le 3)
    _ = _ := by ring

#print axioms operatorDeficit_centered_ge

end D5.S3.Quantum.Semigroups.WuCubicTransverseCentered
