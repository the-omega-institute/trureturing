import D5.S3.Quantum.Semigroups.WuCubicConditionedHessian

/-! Curvature of the conditioned Wu cubic deficit on the wider normalized spectral band. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicWiderCurvature

open WuCubicOperatorBridge (Mat Occupation)
open WuRepeatedMiddleCubic (alpha)
open WuCubicConditionedHessian
  (abs_theta_le combined_loss_log embeddedGenerator embedded_generator_eq gain imbalance
    logCenter logImbalance log_density_eq log_middle_ge loss neg_gain_trace_ge theta)
open private imbalance_hermitian imbalance_sq_le square_psd thermal_ratio_le trace_weighted_cfc
  from
  D5.S3.Quantum.Semigroups.WuCubicConditionedHessian

/-- Scalar curvature envelope with mixed-generator coefficient 187/50. -/
def p (x : ℝ) : ℝ :=
  x * (1521 / 200 - 3 * Real.log (52 * x ^ 3 / 21)) - 1620 / 341

private theorem log_endpoint_upper : Real.log (52 / 21) ≤ 11 / 12 := by
  have h := (abs_le.mp (Real.sum_range_sub_log_div_le (x := (31 / 73 : ℝ))
    (by norm_num) 3)).2
  rw [show (1 + (31 / 73 : ℝ)) / (1 - 31 / 73) = 52 / 21 by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem p_concave : ConcaveOn ℝ (Ioi 0) p := by
  have hlin := (concaveOn_id (𝕜 := ℝ) (convex_Ioi (0 : ℝ))).smul
    (c := 1521 / 200 - 3 * Real.log (52 / 21)) (by linarith [log_endpoint_upper])
  have hlog := (Real.convexOn_mul_log.subset
    (fun x (hx : x ∈ Ioi (0 : ℝ)) => show 0 ≤ x from le_of_lt hx)
    (convex_Ioi (0 : ℝ))).smul (c := 9) (by norm_num)
  apply ((hlin.sub hlog).sub (convexOn_const (c := (1620 / 341 : ℝ))
    (convex_Ioi (0 : ℝ)))).congr
  intro x hx
  have hxpos : 0 < x := hx
  have harg : 52 * x ^ 3 / 21 = (52 / 21) * x ^ 3 := by ring
  simp only [p, Pi.sub_apply, id_eq, smul_eq_mul, harg, Real.log_mul
    (by norm_num : (52 / 21 : ℝ) ≠ 0) (pow_ne_zero _ hxpos.ne'), Real.log_pow]
  ring

/-- The explicit envelope gives normalized curvature at least 1/10. -/
theorem p_ge {x : ℝ} (hx : x ∈ Icc (21 / 40 : ℝ) 1) : 1 / 10 ≤ p x := by
  have hlo : 1 / 10 + 33292441 / 218240000 ≤ p (21 / 40) := by
    unfold p
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (52 : ℝ) * (21 / 40) ^ 3 / 21 by norm_num)
    linarith only [h]
  have hhi : 1 / 10 + 291 / 68200 ≤ p 1 := by
    unfold p
    norm_num only [one_pow, mul_one]
    linarith only [log_endpoint_upper]
  have hc := p_concave.subset
    (fun y (hy : y ∈ Icc (21 / 40 : ℝ) 1) => show y ∈ Ioi 0 from
      lt_of_lt_of_le (by norm_num) hy.1) (convex_Icc (21 / 40 : ℝ) 1)
  exact (le_min (by linarith only [hlo]) (by linarith only [hhi])).trans
    (hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hx)

/-- The wider-band entropy cancellation uses the enlarged positive logarithmic bracket. -/
theorem entropy_coefficient_ge {r x T : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (hx : 21 / 40 ≤ x) (hT : 7 / 4 ≤ T) :
    -(x * (9 / 2 + 3 * Real.log (52 * x ^ 3 / 21))) ≤
      -(alpha r * (15 * x + 18 * x * Real.log x)) +
        alpha r * (6 * (1 + Real.log T) * x + 18 * logCenter r * x) := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hden : 0 < 1 + r ^ 3 := by positivity
  have hratio : 0 < (1 + r ^ 3) ^ 2 / r ^ 3 := by positivity
  have harg : (1 + r ^ 3) ^ 2 / r ^ 3 * x ^ 3 / T ≤ 52 * x ^ 3 / 21 := by
    calc
      _ ≤ (13 / 3 : ℝ) * x ^ 3 / T :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (thermal_ratio_le hr hhi) (by positivity)) hTpos.le
      _ ≤ (13 / 3 : ℝ) * x ^ 3 / (7 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hT
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity) harg
  rw [Real.log_div (by positivity : (1 + r ^ 3) ^ 2 / r ^ 3 * x ^ 3 ≠ 0) hTpos.ne',
    Real.log_mul hratio.ne' (pow_ne_zero _ hxpos.ne'),
    Real.log_div (pow_ne_zero _ hden.ne') (pow_ne_zero _ hrpos.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hexp : (3 : ℝ) < Real.exp (3 / 2) :=
    lt_of_lt_of_le (by norm_num) (Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hfloor : Real.exp (-(3 / 2)) ≤ 52 * x ^ 3 / 21 := calc
    _ ≤ (1 / 3 : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff_of_pos_left (by norm_num)
        (Real.exp_pos _) (by norm_num)]
      exact hexp.le
    _ ≤ 52 * (21 / 40 : ℝ) ^ 3 / 21 := by norm_num
    _ ≤ _ := by gcongr
  have hpos : 0 ≤ 9 + 6 * Real.log (52 * x ^ 3 / 21) := by
    have h := Real.log_le_log (Real.exp_pos _) hfloor
    rw [Real.log_exp] at h
    linarith only [h]
  have hc : 9 + 18 * Real.log x - 6 * Real.log T - 18 * logCenter r ≤
      9 + 6 * Real.log (52 * x ^ 3 / 21) := by
    unfold logCenter
    linarith only [hlog]
  have ha := WuCubicOccupationTaylor.alpha_bounds_of_one_le hr
  have h := (mul_le_mul_of_nonneg_left hc ha.1).trans
    (mul_le_mul_of_nonneg_right ha.2 hpos)
  nlinarith only [mul_le_mul_of_nonneg_right h hxpos.le]

/-- Removing one eigenvalue equal to one leaves three eigenvalues of mean at
least 63/100. The tangent bound for the cube gives the required mass floor. -/
theorem cubic_mass_ge {M : Mat} (hM : M.PosDef)
    (htrace : 289 / 100 ≤ M.trace.re)
    (hmax : ∃ j, hM.isHermitian.eigenvalues j = 1) :
    7 / 4 ≤ (M ^ 3).trace.re := by
  let m := hM.isHermitian.eigenvalues
  obtain ⟨j, hj⟩ := hmax
  change m j = 1 at hj
  let s := (Finset.univ : Finset Occupation).erase j
  have hs : s.card = 3 := by
    change ((Finset.univ : Finset Occupation).erase j).card = 3
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    decide
  have htr : M.trace.re = ∑ i : Occupation, m i :=
    RHLinalg.rtrace_eq_sum_eigenvalues hM.isHermitian
  have hpow : (M ^ 3).trace.re = ∑ i : Occupation, (m i) ^ 3 := by
    conv_lhs => rw [hM.isHermitian.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      Matrix.diagonal_pow, Matrix.trace_diagonal, Complex.re_sum]
    simp [m, ← Complex.ofReal_pow]
  have hsum := Finset.sum_erase_add (s := Finset.univ) m (Finset.mem_univ j)
  have hsumCube := Finset.sum_erase_add (s := Finset.univ)
    (fun i => (m i) ^ 3) (Finset.mem_univ j)
  change (∑ i ∈ s, m i) + m j = _ at hsum
  change (∑ i ∈ s, (m i) ^ 3) + (m j) ^ 3 = _ at hsumCube
  rw [hj, ← htr] at hsum
  rw [hj, one_pow, ← hpow] at hsumCube
  have htangent (i : Occupation) : 3 * (63 / 100 : ℝ) ^ 2 * m i -
      2 * (63 / 100) ^ 3 ≤ (m i) ^ 3 := by
    have hmi : 0 ≤ m i := hM.posSemidef.eigenvalues_nonneg i
    nlinarith only [mul_nonneg (sq_nonneg (m i - 63 / 100))
      (show 0 ≤ m i + 2 * (63 / 100) by linarith)]
  have h := Finset.sum_le_sum (s := s) (fun i _ => htangent i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hs, nsmul_eq_mul] at h
  linarith only [h, hsum, hsumCube, htrace]

private theorem combined_loss_trace_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    {M W : Mat} (hM : M.PosSemidef) (hW : W.IsHermitian)
    (hlo : (21 / 40 : ℝ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1) :
    (9 / 2 - 21 / 100 : ℝ) * (M * W ^ 2).trace.re ≤
      (9 / 4 : ℝ) * ((M * W ^ 2 + W ^ 2 * M) * loss r).trace.re +
      6 * alpha r * ((M * W ^ 2 + W ^ 2 * M) * logImbalance r).trace.re := by
  let K := imbalance
  let A := M * W ^ 2 + W ^ 2 * M
  let q := (M * W ^ 2).trace.re
  have hK : K.IsHermitian := imbalance_hermitian
  -- The reciprocal spectral floor is at most the square of 7/5.
  have hKM : K * M * K ≤ (49 / 25 : ℝ) • M := calc
    K * M * K ≤ K ^ 2 := by
      rw [Matrix.le_iff]
      simpa only [hK.eq, mul_sub, sub_mul, mul_one, pow_two] using
        ((Matrix.le_iff.mp hMhi).conjTranspose_mul_mul_same K)
    _ ≤ 1 := imbalance_sq_le
    _ ≤ (49 / 25 : ℝ) • ((21 / 40 : ℝ) • (1 : Mat)) := by
      rw [smul_smul]
      have hone : (0 : Mat) ≤ 1 := Matrix.PosSemidef.one.nonneg
      have hcoeff : (1 : ℝ) ≤ (49 / 25) * (21 / 40) := by norm_num
      simpa only [one_smul] using smul_le_smul_of_nonneg_right hcoeff hone
    _ ≤ _ := smul_le_smul_of_nonneg_left hlo (by norm_num)
  have hpenalty : (K * M * K * W ^ 2).trace.re ≤ (49 / 25 : ℝ) * q := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hKM) (square_psd hW)
    change 0 ≤ (((49 / 25 : ℝ) • M - K * M * K) * W ^ 2).trace.re at h
    simpa only [q, sub_mul, smul_mul_assoc, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul, sub_nonneg] using h
  have hcross : ((K * M + M * K) * W ^ 2).trace = (A * K).trace := by
    simp only [A, add_mul, Matrix.trace_add]
    rw [Matrix.trace_mul_cycle K M (W ^ 2), Matrix.trace_mul_cycle (W ^ 2) K M,
      Matrix.trace_mul_cycle M K (W ^ 2)]
  have hsquare (t : ℝ) :
      0 ≤ (K * M * K * W ^ 2).trace.re + t * (A * K).trace.re + t ^ 2 * q := by
    have ht : (K + t • (1 : Mat)).IsHermitian :=
      hK.add (Matrix.isHermitian_one.smul (star_trivial t))
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef
      (hM.conjTranspose_mul_mul_same (K + t • (1 : Mat))) (square_psd hW)
    rw [ht.eq, show (K + t • (1 : Mat)) * M * (K + t • (1 : Mat)) =
        K * M * K + t • (K * M + M * K) + t ^ 2 • M by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
        mul_one, smul_smul, pow_two, smul_add]
      abel] at h
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, Matrix.trace_add,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hcross] at h
    change 0 ≤ ((K * M * K * W ^ 2).trace + t • (A * K).trace +
      t ^ 2 • (M * W ^ 2).trace).re at h
    simpa only [q, Complex.add_re, Complex.smul_re, smul_eq_mul] using h
  have hb : |(A * K).trace.re| ≤ (14 / 5 : ℝ) * q := abs_le.mpr
    ⟨by linarith only [hsquare (7 / 5), hpenalty],
      by linarith only [hsquare (- (7 / 5)), hpenalty]⟩
  have ha : A.trace.re = 2 * q := by
    simp only [A, q, Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (W ^ 2) M]
    ring
  have hcombine := congrArg (fun X : Mat => (A * X).trace.re) (combined_loss_log r)
  simp only [mul_add, mul_smul_comm, mul_one, Matrix.trace_add, Complex.add_re,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ha] at hcombine
  have hprod := mul_le_mul (abs_theta_le hr hhi) hb (abs_nonneg _)
    (by norm_num : 0 ≤ (3 / 40 : ℝ))
  rw [← abs_mul] at hprod
  have hlow := (neg_le_neg hprod).trans (neg_abs_le (theta r * (A * K).trace.re))
  change _ ≤ (9 / 4 : ℝ) * (A * loss r).trace.re +
      6 * alpha r * (A * logImbalance r).trace.re
  change _ ≤ theta r * (A * imbalance).trace.re at hlow
  linarith only [hcombine, hlow]

/-- The normalized physical Hessian expression on the wider spectral band.
The mixed-generator and trace-function bounds enter with their actual trace forms. -/
theorem physical_curvature_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.IsHermitian) (hW : W.IsHermitian)
    (hm : ∀ i, hM.eigenvalues i ∈ Icc (21 / 40 : ℝ) 1)
    (htrace : 289 / 100 ≤ M.trace.re) (hmax : ∃ i, hM.eigenvalues i = 1)
    (traceCurvature : ℝ)
    (hTrace : traceCurvature ≤
      (W ^ 2 * cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M).trace.re)
    (hMixed : (187 / 50 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * embeddedGenerator r W).trace.re) :
    (1 / 10 : ℝ) * (W ^ 2).trace.re ≤
      (9 / 4 : ℝ) * (W ^ 2 * embeddedGenerator r M +
        (M * W + W * M) * embeddedGenerator r W).trace.re -
      alpha r * traceCurvature +
      2 * alpha r * ((M * W ^ 2 + W * M * W + W ^ 2 * M) *
        cfc Real.log (WuCubicOperatorBridge.D r)).trace.re +
      alpha r * (6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
        9 * ((M ^ 2 * W).trace.re) ^ 2 / (M ^ 3).trace.re) := by
  have hMp : M.PosDef := hM.posDef_iff_eigenvalues_pos.mpr
    (fun i => lt_of_lt_of_le (by norm_num) (hm i).1)
  have hlo := (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hM (21 / 40)).mp
    (fun i => (hm i).1)
  have hMhi : M ≤ 1 := by
    simpa only [one_smul] using (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hM 1).mp
      (fun i => (hm i).2)
  let m := hM.eigenvalues
  let U : Mat := hM.eigenvectorUnitary
  let w := fun i => ((Uᴴ * W ^ 2 * U) i i).re
  let q := (M * W ^ 2).trace.re
  let v := (W ^ 2).trace.re
  let T := (M ^ 3).trace.re
  let A := M * W ^ 2 + W ^ 2 * M
  let f := fun x : ℝ => 15 * x + 18 * x * Real.log x
  have hT : 7 / 4 ≤ T := cubic_mass_ge hMp htrace hmax
  have hw (i : Occupation) : 0 ≤ w i :=
    (Complex.nonneg_iff.mp ((square_psd hW).conjTranspose_mul_mul_same U).diag_nonneg).1
  have hv : ∑ i, w i = v := by
    have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    change (Uᴴ * W ^ 2 * U).trace.re = v
    rw [Matrix.trace_mul_cycle, hU, one_mul]
  have hq : ∑ i, m i * w i = q := by
    have h := trace_weighted_cfc M W hM id
    rw [cfc_id ℝ M hM.isSelfAdjoint, Matrix.trace_mul_comm] at h
    simpa only [m, w, U, id_eq, mul_comm] using h.symm
  have hpoint (i : Occupation) : (1 / 10 : ℝ) * w i ≤
      ((9 / 4) * (187 / 50) + (9 / 2 - 21 / 100) - 3 / 5) * (m i * w i) -
      (1620 / 341) * w i - alpha r * (w i * f (m i)) +
      alpha r * (6 * (1 + Real.log T) * (m i * w i)) +
      18 * alpha r * logCenter r * (m i * w i) := by
    have hp := mul_le_mul_of_nonneg_right (p_ge (hm i)) (hw i)
    have he := mul_le_mul_of_nonneg_right
      (entropy_coefficient_ge hr hhi (hm i).1 hT) (hw i)
    unfold p at hp
    dsimp only [f]
    linarith only [hp, he]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv, hq] at hsum
  rw [← trace_weighted_cfc M W hM f] at hsum
  have ha := (WuCubicOccupationTaylor.alpha_bounds_of_one_le hr).1
  have hF := mul_le_mul_of_nonneg_left hTrace ha
  have hGain := neg_gain_trace_ge hr hhi hMhi hW
  have hLoss := combined_loss_trace_ge hr hhi hMp.posSemidef hW hlo hMhi
  have hLog := log_middle_ge hr hhi hMp.posSemidef hW
  have hMass : 0 ≤ alpha r * (9 * ((M ^ 2 * W).trace.re) ^ 2 / T) :=
    mul_nonneg ha (div_nonneg (by positivity) (by linarith only [hT]))
  have henergy : (W ^ 2 * embeddedGenerator r M).trace.re =
      (A * loss r).trace.re - (W ^ 2 * gain r M).trace.re := by
    rw [embeddedGenerator, embedded_generator_eq hr M]
    simp only [mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
      Complex.add_re, A, add_mul]
    rw [Matrix.trace_mul_cycle' (W ^ 2) (loss r) M]
    simp only [Matrix.mul_assoc]
  have hcycle : (W * M * W).trace = (M * W ^ 2).trace := by
    rw [Matrix.trace_mul_comm (W * M) W, ← Matrix.mul_assoc, ← pow_two, Matrix.trace_mul_comm]
  have hc : (M * W ^ 2 + W * M * W + W ^ 2 * M).trace.re = 3 * q := by
    rw [Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re, hcycle,
      Matrix.trace_mul_comm (W ^ 2) M]
    dsimp only [q]
    ring
  have href : ((M * W ^ 2 + W * M * W + W ^ 2 * M) *
      cfc Real.log (WuCubicOperatorBridge.D r)).trace.re =
      9 * logCenter r * q + 3 * (A * logImbalance r).trace.re +
        3 * (W * M * W * logImbalance r).trace.re := by
    rw [log_density_eq hr, mul_add, mul_smul_comm, mul_one, mul_smul_comm,
      Matrix.trace_add, Complex.add_re, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, hc]
    simp only [A, add_mul, Matrix.trace_add, Complex.add_re]
    ring
  rw [Matrix.trace_add, Complex.add_re, henergy, href]
  change alpha r * traceCurvature ≤ alpha r * (W ^ 2 * cfc f M).trace.re at hF
  dsimp only [A, q, T, v] at hsum hMass ⊢
  linarith only [hsum, hMixed, hGain, hLoss, hLog, hF, hMass]

end D5.S3.Quantum.Semigroups.WuCubicWiderCurvature
