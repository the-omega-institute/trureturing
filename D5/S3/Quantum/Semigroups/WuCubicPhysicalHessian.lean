import D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian
import D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

/-! The ordinary-trace quadratic coefficient in Wu's cubic deficit (3.54), on a
Hermitian direction of fixed generator degree and absolute modular charge. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicPhysicalHessian

open WuCubicHotInnerDiagonalHessian (entropyPairKernel shiftHessian)
open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor (coth)

-- This local expression keeps the matrix bridge independent of the thermal gap module.
private def bohrG (v : ℝ) : ℝ :=
  if v = 0 then 1 / 2 else (v / 18) * (coth (v / 3) + coth (v / 6))

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Ordinary-trace quadratic energy for a Hermitian direction at a diagonal base. -/
theorem energy_trace_quadratic (x : n → ℝ) (U : Matrix n n ℂ) (hU : U.IsHermitian)
    (d : ℝ) :
    let B := diagonal (fun i => (x i : ℂ))
    (9 / 8 : ℝ) * d * ((B * U + U * B) * U).trace.re =
      (9 / 8 : ℝ) * d * ∑ i, ∑ j, (x i + x j) * Complex.normSq (U i j) := by
  intro B
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.add_apply, B, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [← hU.apply j i, Complex.star_def]
  rw [show ((x i : ℂ) * U i j + U i j * (x j : ℂ)) * starRingEnd ℂ (U i j) =
    ((x i : ℂ) + (x j : ℂ)) * (U i j * starRingEnd ℂ (U i j)) by ring]
  simp only [Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem entropyPairKernel_comm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    entropyPairKernel x y = entropyPairKernel y x := by
  by_cases hxy : x = y
  · rw [hxy]
  rw [entropyPairKernel, entropyPairKernel, ite_eq_right hxy, ite_eq_right (Ne.symm hxy),
    Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne']
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr (Ne.symm hxy)]
  ring

private theorem abs_log_div_comm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log (x / y)| = |Real.log (y / x)| := by
  rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne', abs_sub_comm]

private theorem exp_half_log_factors {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let a := Real.exp (Real.log (x / y) / 2)
    x = y * a ^ 2 ∧ Real.sqrt (x * y) = y * a := by
  intro a
  have hsq : a ^ 2 = x / y := by
    dsimp only [a]
    rw [pow_two, ← Real.exp_add, show Real.log (x / y) / 2 + Real.log (x / y) / 2 =
      Real.log (x / y) by ring, Real.exp_log (div_pos hx hy)]
  have hx' : x = y * a^2 := by
    rw [hsq, mul_comm, div_mul_cancel₀ _ hy.ne']
  refine ⟨hx', ?_⟩
  apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hx.le hy.le)
    (mul_nonneg hy.le (Real.exp_pos _).le)).2
  calc
    x * y = (y * a^2) * y := congrArg (· * y) hx'
    _ = (y * a)^2 := by ring

private theorem energy_pair_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x + y = 2 * Real.sqrt (x * y) * Real.cosh ((3 * |Real.log (x / y)|) / 6) := by
  let z := Real.log (x / y) / 2
  let a := Real.exp z
  obtain ⟨hxa, hs⟩ := exp_half_log_factors hx hy
  change x = y * a^2 at hxa
  change Real.sqrt (x * y) = y * a at hs
  have hz : (3 * |Real.log (x / y)|) / 6 = |z| := by
    rw [show (3 * |Real.log (x / y)|) / 6 = |Real.log (x / y)| / 2 by ring]
    simp [z, abs_div]
  rw [hz, Real.cosh_abs, Real.cosh_eq, Real.exp_neg, hs]
  change x + y = 2 * (y * a) * ((a + a⁻¹) / 2)
  rw [hxa]
  have ha : a ≠ 0 := (Real.exp_pos z).ne'
  field_simp [ha]

private theorem entropy_pair_factor_of_lt {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    let v := 3 * |Real.log (x / y)|
    entropyPairKernel x y / (2 * Real.sqrt (x * y)) = 9 * Real.cosh (v / 6) * bohrG v := by
  intro v
  have hx := hy.trans hyx
  let w := Real.log (x / y)
  let z := w / 2
  let a := Real.exp z
  have hw : 0 < w := Real.log_pos ((lt_div_iff₀ hy).2 (by simpa using hyx))
  have hz : 0 < z := half_pos hw
  have ha : 1 < a := Real.one_lt_exp_iff.mpr hz
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hv : v = 3 * w := by simp only [v, w, abs_of_pos hw]
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  obtain ⟨hxa, hs⟩ := exp_half_log_factors hx hy
  change x = y * a^2 at hxa
  change Real.sqrt (x * y) = y * a at hs
  change _ = 9 * Real.cosh (v / 6) *
    (if v = 0 then 1 / 2 else (v / 18) * (coth (v / 3) + coth (v / 6)))
  rw [entropyPairKernel, ite_eq_right hyx.ne', hs, ite_eq_right hv0, hv]
  change 3 * (x^2+x*y+y^2) * w / (x-y) / (2 * (y*a)) =
    9 * Real.cosh ((3*w)/6) * ((3*w)/18 * (coth ((3*w)/3) + coth ((3*w)/6)))
  rw [show (3*w)/6 = z by dsimp [z]; ring, show (3*w)/3 = z + z by dsimp [z]; ring]
  simp only [coth, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, Real.exp_add]
  change 3 * (x^2+x*y+y^2) * w / (x-y) / (2 * (y*a)) =
    9 * ((a+a⁻¹)/2) * ((3*w)/18 *
      (((a*a+(a*a)⁻¹)/2)/((a*a-(a*a)⁻¹)/2) + ((a+a⁻¹)/2)/((a-a⁻¹)/2)))
  rw [hxa]
  have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha.ne'
  have hap : a + 1 ≠ 0 := by positivity
  have hapsq : a^2 + 1 ≠ 0 := by positivity
  have hdiff : y*a^2-y = y*(a-1)*(a+1) := by ring
  have hz₁ : a*a - (a*a)⁻¹ = (a-1)*(a+1)*(a^2+1)/(a*a) := by
    field_simp [ha0.ne']
    ring
  have hz₂ : a - a⁻¹ = (a-1)*(a+1)/a := by
    field_simp [ha0.ne']
    ring
  rw [hdiff, hz₁, hz₂]
  field_simp [ha0.ne', hy.ne', ha1, hap, hapsq]
  ring

/-- The cubic entropy kernel per unordered pair, divided by the corresponding
norm weight. At a repeated level the quotient is 9/2. -/
theorem entropy_pair_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let v := 3 * |Real.log (x / y)|
    entropyPairKernel x y / (2 * Real.sqrt (x * y)) = 9 * Real.cosh (v / 6) * bohrG v := by
  rcases lt_trichotomy y x with h | h | h
  · exact entropy_pair_factor_of_lt hy h
  · subst y
    dsimp only
    rw [entropyPairKernel, ite_eq_left rfl, div_self hx.ne', Real.log_one, abs_zero, mul_zero,
      bohrG, ite_eq_left rfl, zero_div, Real.cosh_zero, mul_one, ← pow_two, Real.sqrt_sq hx.le]
    field_simp [hx.ne']
  · dsimp only
    rw [entropyPairKernel_comm hx hy, mul_comm x y, abs_log_div_comm hx hy]
    exact entropy_pair_factor_of_lt hx h

/-- The degree-d quadratic coefficient of the ordinary-trace deficit in a
sector of absolute charge v. The charge condition is imposed on each nonzero
entry of the sandwiched direction. -/
theorem physical_trace_quadratic (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (U : Matrix n n ℂ) (hU : U.IsHermitian) (d v alpha : ℝ)
    (hcharge : ∀ i j, U i j ≠ 0 → 3 * |Real.log (x i / x j)| = v) :
    let B := diagonal (fun i => (x i : ℂ))
    let T := B * U^2 + U * B * U + U^2 * B
    (9 / 8 : ℝ) * d * ((B * U + U * B) * U).trace.re -
      alpha * (3 * (∫ l in Ioi (0 : ℝ), (1/2 : ℝ) *
        ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) -
        T.trace.re - (T * cfc Real.log (B^3)).trace.re) =
      (9 / 4 : ℝ) * Real.cosh (v / 6) * (d - 4 * alpha * bohrG v) *
        ∑ i, ∑ j, Real.sqrt (x i * x j) * Complex.normSq (U i j) := by
  intro B T
  rw [WuCubicHotInnerDiagonalHessian.physical_trace_quadratic_sub_charges x hx U hU,
    energy_trace_quadratic x U hU d]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : U i j = 0
  · simp [h]
  · have harg := hcharge i j h
    have henergy := energy_pair_factor (hx i) (hx j)
    have hentropy := entropy_pair_factor (hx i) (hx j)
    dsimp only at hentropy
    rw [harg] at henergy hentropy
    have hweight : 2 * Real.sqrt (x i * x j) ≠ 0 :=
      mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (mul_pos (hx i) (hx j))).ne'
    rw [henergy, (div_eq_iff hweight).mp hentropy]
    ring

#print axioms energy_trace_quadratic
#print axioms entropy_pair_factor
#print axioms physical_trace_quadratic

open WuCubicHotInnerEntropy (cubicPolynomial)

private theorem log_cube {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    cfc Real.log (Y^3) = (3 : ℝ) • cfc Real.log Y := by
  have hc (f : ℝ → ℝ) := Y.finite_real_spectrum.continuousOn f
  have hp : ContinuousOn Real.log ((fun x : ℝ => x^3) '' spectrum ℝ Y) :=
    (Y.finite_real_spectrum.image _).continuousOn _
  rw [← cfc_comp_pow Real.log 3 Y hp hY.isSelfAdjoint, ← cfc_const_mul 3 Real.log Y (hc _)]
  exact cfc_congr (fun z _ => by simpa only [Nat.cast_ofNat] using Real.log_pow z 3)

/-- The shifted resolvent remainder of the cubic logarithm after its degree-three
polynomial has been subtracted. -/
private def shiftError (B U : Matrix n n ℂ) (t l : ℝ) : ℝ :=
  (WuCubicHotInnerResolvent.cubicLogIntegrand l (B + t • U)).trace.re -
    (cubicPolynomial B (t • U) l).trace.re

omit [DecidableEq n] in
private theorem trace_real_smul (s : ℝ) (A : Matrix n n ℂ) :
    (s • A).trace.re = s * A.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private theorem centered_cube (B U : Matrix n n ℂ) (t : ℝ) :
    (B + t • U)^3 + (B + (-t) • U)^3 - (2 : ℝ) • B^3 =
      (2*t^2) • (B * U^2 + U * B * U + U^2 * B) := by
  simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add,
    mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_assoc]
  module

private theorem centered_energy (B U : Matrix n n ℂ) (t d : ℝ) :
    let e := fun s : ℝ => (9 / 8 : ℝ) * (((B + s • U)^2) * ((s*d) • U)).trace.re
    e t + e (-t) - 2 * e 0 =
      2*t^2 * ((9 / 8 : ℝ) * d * ((B * U + U * B) * U).trace.re) := by
  dsimp only
  have h :
      (B + t • U)^2 * ((t*d) • U) + (B + (-t) • U)^2 * (((-t)*d) • U) =
        (2*t^2*d) • ((B*U+U*B)*U) := by
    simp only [pow_two, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul,
      mul_assoc]
    module
  have h' := congrArg (fun M : Matrix n n ℂ => M.trace.re) h
  simp only [Matrix.trace_add, Complex.add_re, trace_real_smul] at h'
  simp only [zero_mul, zero_smul, Matrix.trace_zero, Complex.zero_re, mul_zero,
    sub_zero]
  linarith only [h']

set_option maxHeartbeats 1200000 in
-- Elaborating the imported integral identity and comparing the trace expressions needs
-- extra heartbeats in this theorem.
private theorem centered_cubicDeficit
    (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) (hU : U.IsHermitian)
    (t d v alpha : ℝ)
    (hcharge : ∀ i j, U i j ≠ 0 → 3 * |Real.log (x i / x j)| = v) :
    let B := diagonal (fun i => (x i : ℂ))
    let Y := fun s : ℝ => B + s • U
    let m := fun s => ((Y s)^3).trace.re
    let F := fun s => (9 / 8 : ℝ) * (((Y s)^2) * ((s*d) • U)).trace.re -
      alpha * ((((Y s)^3) * (cfc Real.log ((Y s)^3) - cfc Real.log (B^3))).trace.re -
        m s * Real.log (m s))
    m 0 = 1 → (Y t).PosDef → (Y (-t)).PosDef →
    let r := fun l => shiftError B U t l + shiftError B U (-t) l - 2 * shiftError B U 0 l
    let massError := fun s => m s * Real.log (m s) - (m s - 1)
    IntegrableOn r (Ioi (0 : ℝ)) ∧
      F t + F (-t) - 2*F 0 =
        2*t^2 * ((9 / 4 : ℝ) * Real.cosh (v / 6) * (d - 4 * alpha * bohrG v) *
          ∑ i, ∑ j, Real.sqrt (x i * x j) * Complex.normSq (U i j)) -
        3*alpha*(∫ l in Ioi (0 : ℝ), r l) + alpha * (massError t + massError (-t)) := by
  intro B Y m F hm hp hn r massError
  let T := B * U^2 + U * B * U + U^2 * B
  have hB : B.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast hx i
  have hzero : Y 0 = B := by simp [Y]
  have h0 : (Y 0).PosDef := hzero ▸ hB
  let r₀ := fun l =>
    (((WuCubicHotInnerResolvent.cubicLogIntegrand l (Y t)).trace.re +
      (WuCubicHotInnerResolvent.cubicLogIntegrand l (Y (-t))).trace.re -
        2*(WuCubicHotInnerResolvent.cubicLogIntegrand l (Y 0)).trace.re) -
      ((cubicPolynomial B (t • U) l).trace.re + (cubicPolynomial B ((-t) • U) l).trace.re -
        2*(cubicPolynomial B ((0 : ℝ) • U) l).trace.re))
  have hr : r₀ = r := by
    funext l
    dsimp [r₀, r, shiftError, Y]
    ring
  have hlog := WuCubicHotInnerDiagonalHessian.cubicLog_trace_centeredRemainder x hx U hU t hp hn
  change IntegrableOn r₀ (Ioi (0 : ℝ)) ∧
    ((Y t)^3 * cfc Real.log (Y t)).trace.re +
      ((Y (-t))^3 * cfc Real.log (Y (-t))).trace.re -
      2 * ((Y 0)^3 * cfc Real.log (Y 0)).trace.re =
      t^2 * (∑ i, ∑ j, WuCubicHotInnerDiagonalHessian.logHessian (x i) (x j) *
        Complex.normSq (U i j)) + (∫ l in Ioi (0 : ℝ), r₀ l) at hlog
  rw [hr] at hlog
  obtain ⟨hi, hlog⟩ := hlog
  refine ⟨hi, ?_⟩
  have hcube : (Y t)^3 + (Y (-t))^3 - (2 : ℝ) • (Y 0)^3 = (2*t^2) • T := by
    rw [hzero]
    exact centered_cube B U t
  have hmDiff := congrArg (fun M : Matrix n n ℂ => M.trace.re) hcube
  have hgDiff := congrArg (fun M : Matrix n n ℂ => (M * cfc Real.log (B^3)).trace.re) hcube
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    trace_real_smul,
    add_mul, sub_mul, smul_mul_assoc] at hmDiff hgDiff
  change m t + m (-t) - 2 * m 0 = _ at hmDiff
  rw [hm] at hmDiff
  have hcoef := physical_trace_quadratic x hx U hU d v alpha hcharge
  dsimp only at hcoef
  rw [(WuCubicHotInnerDiagonalHessian.integral_trace_quadratic x hx U).2] at hcoef
  have henergy := centered_energy B U t d
  change _ + _ - _ = _ at henergy
  have hentropy (s : ℝ) (hs : (Y s).IsHermitian) :
      (((Y s)^3) * (cfc Real.log ((Y s)^3) - cfc Real.log (B^3))).trace.re =
        3 * (((Y s)^3) * cfc Real.log (Y s)).trace.re -
          (((Y s)^3) * cfc Real.log (B^3)).trace.re := by
    rw [log_cube hs, mul_sub, Matrix.trace_sub, Complex.sub_re, mul_smul_comm, trace_real_smul]
  have hremainder (s : ℝ) : m s * Real.log (m s) = m s - 1 + massError s := by
    dsimp [massError]
    ring
  dsimp only [F]
  rw [hentropy t hp.isHermitian, hentropy (-t) hn.isHermitian, hentropy 0 h0.isHermitian,
    hremainder t, hremainder (-t), hm, Real.log_one, mul_zero]
  linear_combination henergy - 3*alpha*hlog + alpha*hgDiff + alpha*hmDiff + 2*t^2*hcoef

open WuCubicOperatorBridge (Mat D G generator dissipator)
open WuRepeatedMiddleCubic (alpha)
open private rootValue rootValue_pos G_pow_six from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private gibbsOccupation gibbsLow gibbsHigh from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

private theorem trace_D_real {r : ℝ} (hr : 1 ≤ r) : (D r).trace.re = 1 := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  simp only [D, Matrix.trace_diagonal, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have h : gibbsLow r + gibbsHigh r = 1 := by
    unfold gibbsHigh gibbsLow
    field_simp [(show 0 < 1 + r^3 by positivity).ne']
  change gibbsLow r * gibbsLow r + gibbsLow r * gibbsHigh r +
      (gibbsHigh r * gibbsLow r + gibbsHigh r * gibbsHigh r) = 1
  rw [show gibbsLow r * gibbsLow r + gibbsLow r * gibbsHigh r +
      (gibbsHigh r * gibbsLow r + gibbsHigh r * gibbsHigh r) =
        (gibbsLow r + gibbsHigh r)^2 by ring, h, one_pow]

private theorem generator_affine (r t : ℝ) (H : Mat) :
    generator r (1 + t • H) = t • generator r H := by
  have hJ (J : Mat) : dissipator J (1 + t • H) = t • dissipator J H := by
    have hs : (1 / 2 : ℂ) • (Jᴴ * J + Jᴴ * J) = Jᴴ * J := by module
    unfold dissipator
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    rw [show (Jᴴ * J + t • ((Jᴴ * J) * H) + (Jᴴ * J + t • (H * (Jᴴ * J)))) =
      (Jᴴ * J + Jᴴ * J) + t • ((Jᴴ * J) * H + H * (Jᴴ * J)) by module,
      smul_add, hs]
    simp only [smul_sub, smul_comm (1 / 2 : ℂ) t]
    module
  simp only [generator, hJ, Finset.smul_sum, smul_add, smul_comm (_ : ℂ) t]

private theorem square_sandwich (r : ℝ) :
    G r * G r = diagonal (fun i => ((rootValue r i ^ 2 : ℝ) : ℂ)) := by
  rw [G, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Complex.ofReal_pow, pow_two]

/-- On a generator eigen-direction, the literal operator deficit has the
computed centered second difference plus its resolvent and scalar mass errors. -/
theorem operatorDeficit_centeredDifference {r : ℝ} (hr : 1 ≤ r)
    (H : Mat) (hH : H.IsHermitian) (t d v : ℝ)
    (hdegree : generator r H = d • H) :
    let x := fun i => rootValue r i ^ 2
    let B := G r * G r
    let U := G r * H * G r
    let Y := fun s : ℝ => B + s • U
    (∀ i j, U i j ≠ 0 → 3 * |Real.log (x i / x j)| = v) →
    (Y t).PosDef → (Y (-t)).PosDef →
    let F := fun s : ℝ => WuCubicOperatorNormalization.operatorDeficit r (1 + s • H)
    let m := fun s => ((Y s)^3).trace.re
    let e := fun l => shiftError B U t l + shiftError B U (-t) l - 2*shiftError B U 0 l
    let massError := fun s => m s * Real.log (m s) - (m s - 1)
    IntegrableOn e (Ioi (0 : ℝ)) ∧
      F t + F (-t) - 2*F 0 =
        2*t^2 * ((9 / 4 : ℝ) * Real.cosh (v / 6) * (d - 4 * alpha r * bohrG v) *
          ∑ i, ∑ j, Real.sqrt (x i * x j) * Complex.normSq (U i j)) -
        3*alpha r*(∫ l in Ioi (0 : ℝ), e l) + alpha r * (massError t + massError (-t)) := by
  intro x B U Y hcharge hp hn F m e massError
  have hG : (G r)ᴴ = G r := by
    rw [G, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun i => Complex.conj_ofReal (rootValue r i))
  have hU : U.IsHermitian := by
    change Uᴴ = U
    simp only [U, Matrix.conjTranspose_mul, hG, hH.eq, mul_assoc]
  have hx (i) : 0 < x i := pow_pos (rootValue_pos hr i) 2
  have hB : B = diagonal (fun i => (x i : ℂ)) := square_sandwich r
  have hD : B^3 = D r := by
    change (G r * G r)^3 = D r
    rw [← pow_two, ← pow_mul]
    exact G_pow_six hr
  have hmass : m 0 = 1 := by
    simpa only [m, Y, zero_smul, add_zero, hD] using trace_D_real hr
  have hF (s : ℝ) : F s =
      (9 / 8 : ℝ) * (((Y s)^2) * ((s*d) • U)).trace.re -
        alpha r * ((((Y s)^3) * (cfc Real.log ((Y s)^3) - cfc Real.log (B^3))).trace.re -
          m s * Real.log (m s)) := by
    have hY : G r * (1 + s • H) * G r = Y s := by
      simp only [Y, B, U, mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    have hgen : G r * generator r (1 + s • H) * G r = (s*d) • U := by
      rw [generator_affine, hdegree, smul_smul, mul_smul_comm, smul_mul_assoc]
    dsimp only [F, WuCubicOperatorNormalization.operatorDeficit, m]
    rw [hY, hgen, hD]
  rw [hF t, hF (-t), hF 0]
  have hh := centered_cubicDeficit x hx U hU t d v (alpha r) hcharge
  rw [← hB] at hh
  exact hh hmass hp hn

#print axioms operatorDeficit_centeredDifference

open private trace_diagonal_three from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian

/-- The ordered-pair sum is the Gibbs-symmetric squared norm of the physical
direction before sandwiching. -/
theorem weighted_norm_trace {r : ℝ} (hr : 1 ≤ r) (H : Mat) (hH : H.IsHermitian) :
    let x := fun i => rootValue r i ^ 2
    let U := G r * H * G r
    ((G r)^3 * H * (G r)^3 * H).trace.re =
      ∑ i, ∑ j, Real.sqrt (x i * x j) * Complex.normSq (U i j) := by
  intro x U
  let a := rootValue r
  have hG3 : (G r)^3 = diagonal (fun i => ((a i ^ 3 : ℝ) : ℂ)) := by
    simp only [G, Matrix.diagonal_pow, Complex.ofReal_pow, a]
    rfl
  rw [hG3]
  have htrace := trace_diagonal_three hH (fun i => a i ^ 3) (fun i => a i ^ 3) (fun _ => 1)
  simp only [Complex.ofReal_one, Matrix.diagonal_one, mul_one] at htrace
  rw [htrace]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have ha (k) : 0 ≤ a k := (rootValue_pos hr k).le
  change a i ^ 3 * a j ^ 3 * Complex.normSq (H i j) =
    Real.sqrt (a i ^ 2 * a j ^ 2) * Complex.normSq (U i j)
  rw [Real.sqrt_mul (sq_nonneg (a i)), Real.sqrt_sq (ha i), Real.sqrt_sq (ha j)]
  simp only [U, G, Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.normSq_mul,
    Complex.normSq_ofReal]
  dsimp only [a]
  ring

#print axioms weighted_norm_trace

open WuCubicHotInnerEntropy (entropyFactor entropyKernel integrated_entropyKernel_le)
open private entropyKernel_eq_sub displaced_posDef from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy

private theorem shiftError_bound (B H : Matrix n n ℂ) (hB : B.PosDef)
    (hH : H.IsHermitian) {bMinus bPlus t : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hBlo : bMinus • (1 : Matrix n n ℂ) ≤ B) (hBhi : B ≤ bPlus • (1 : Matrix n n ℂ))
    (ht : (-(1 / 2 : ℝ)) • (1 : Matrix n n ℂ) ≤ t • H) :
    let U := CFC.sqrt B * H * CFC.sqrt B
    IntegrableOn (shiftError B U t) (Ioi 0) ∧
      0 ≤ ∫ l in Ioi (0 : ℝ), shiftError B U t l ∧
      (∫ l in Ioi (0 : ℝ), shiftError B U t l) ≤
        (entropyFactor bMinus bPlus (1/2) * (H^4).trace.re / 3) * t^4 := by
  intro U
  have hs : IsSelfAdjoint (t • H) :=
    IsSelfAdjoint.smul (show IsSelfAdjoint t from rfl) hH.isSelfAdjoint
  obtain ⟨hi, hv⟩ := integrated_entropyKernel_le B (t • H) hB hs hb hbb hBlo hBhi
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) ht
  have hev (l : ℝ) (hl : l ∈ Ioi (0 : ℝ)) :
      (1/3 : ℝ) * entropyKernel B (t • H) l = shiftError B U t l := by
    have he := entropyKernel_eq_sub B (t • H) hB (by norm_num : (1/2 : ℝ) < 1) ht hl
    dsimp only at he
    rw [mul_smul_comm, smul_mul_assoc] at he
    change 3 * shiftError B U t l = _ at he
    rw [← he]
    ring
  have he : (∫ l in Ioi (0 : ℝ), shiftError B U t l) =
      (1/3 : ℝ) * ∫ l in Ioi (0 : ℝ), entropyKernel B (t • H) l := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hev, integral_const_mul]
  have hi' : IntegrableOn (fun l => (1/3 : ℝ) * entropyKernel B (t • H) l) (Ioi 0) :=
    hi.const_mul _
  refine ⟨hi'.congr_fun hev measurableSet_Ioi, ?_, ?_⟩
  · apply setIntegral_nonneg measurableSet_Ioi
    intro l hl
    rw [← hev l hl]
    exact mul_nonneg (by norm_num) ((WuCubicHotInnerEntropy.entropyKernel_bounds
      B (t • H) hB hs hb hbb hBlo hBhi (by norm_num) (by norm_num) ht hl).1)
  · rw [he]
    rw [smul_pow, trace_real_smul] at hv
    linarith only [mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 1/3)]

private theorem scalar_mass_error {m : ℝ} (hm : 0 < m) :
    0 ≤ m * Real.log m - (m - 1) ∧ m * Real.log m - (m - 1) ≤ (m - 1)^2 := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hm) hm.le
  have h₂ := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hm) hm.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hm.ne'] at h₁
  constructor <;> nlinarith only [h₁, h₂]

private theorem trace_cubic_mass_expansion (B U : Matrix n n ℂ) (t : ℝ) :
    ((B + t • U) ^ 3).trace.re = (B ^ 3).trace.re +
      t * (B ^ 2 * U + B * U * B + U * B ^ 2).trace.re +
      t^2 * (B * U^2 + U * B * U + U^2 * B).trace.re + t^3 * (U^3).trace.re := by
  have h : (B + t • U)^3 =
      B^3 + t • (B^2 * U + B * U * B + U * B^2) +
        t^2 • (B * U^2 + U * B * U + U^2 * B) + t^3 • U^3 := by
    simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add,
      mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_assoc]
    module
  rw [h]
  simp only [Matrix.trace_add, Complex.add_re, trace_real_smul]

private theorem massChargeError_bound (B U : Matrix n n ℂ)
    (hmass : (B ^ 3).trace.re = 1)
    (hcenter : (B ^ 2 * U + B * U * B + U * B ^ 2).trace.re = 0)
    {t : ℝ} (ht : |t| ≤ 1) (hm : 0 < ((B + t • U) ^ 3).trace.re) :
    let m := ((B + t • U) ^ 3).trace.re
    let q := (B * U^2 + U * B * U + U^2 * B).trace.re
    let c := (U^3).trace.re
    0 ≤ m * Real.log m - (m - 1) ∧
      m * Real.log m - (m - 1) ≤ (|q| + |c|)^2 * t^4 := by
  intro m q c
  have hp : m - 1 = t^2 * (q + t*c) := by
    dsimp [m, q, c]
    rw [trace_cubic_mass_expansion, hmass, hcenter]
    ring
  have hb : |q + t*c| ≤ |q| + |c| := by
    have hmul : |t*c| ≤ |c| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) ht
    exact (abs_add_le _ _).trans (add_le_add_right hmul _)
  obtain ⟨hlo, hhi⟩ := scalar_mass_error hm
  refine ⟨hlo, hhi.trans ?_⟩
  rw [hp, mul_pow]
  have hs : (q + t*c)^2 ≤ (|q| + |c|)^2 := by
    rw [← sq_abs (q + t*c)]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  calc
    (t^2)^2 * (q + t*c)^2 ≤ (t^2)^2 * (|q| + |c|)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private theorem trace_mass_linear {r : ℝ} (hr : 1 ≤ r) (H : Mat) :
    let B := G r * G r
    let U := G r * H * G r
    (B ^ 2 * U + B * U * B + U * B ^ 2).trace.re = 3 * (D r * H).trace.re := by
  intro B U
  have hD : B^3 = D r := by
    change (G r * G r)^3 = D r
    rw [← pow_two, ← pow_mul]
    exact G_pow_six hr
  have hleft : (B^2 * U).trace = (D r * H).trace := by
    rw [show B^2 * U = ((B^2 * G r) * H) * G r by simp only [U, mul_assoc]]
    rw [Matrix.trace_mul_comm _ (G r), ← hD]
    congr 1
    simp only [B, pow_succ, pow_zero, one_mul, mul_assoc]
  have hmid : (B * U * B).trace = (B^2 * U).trace := by
    rw [Matrix.trace_mul_comm _ B, ← mul_assoc, ← pow_two]
  have hright : (U * B^2).trace = (B^2 * U).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.trace_add, Complex.add_re, hmid, hright, hleft]
  ring

private theorem G_eq_sqrt {r : ℝ} (hr : 1 ≤ r) : CFC.sqrt (G r * G r) = G r := by
  have hG0 : 0 ≤ G r := by
    apply Matrix.PosSemidef.nonneg
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast (rootValue_pos hr i).le
  exact CFC.sqrt_mul_self (G r) hG0

private theorem zero_shiftError (B U : Matrix n n ℂ) (hB : B.PosDef)
    {l : ℝ} (hl : l ∈ Ioi (0 : ℝ)) : shiftError B U 0 l = 0 := by
  have hlo : (-(1 / 2 : ℝ)) • (1 : Matrix n n ℂ) ≤ 0 := by
    rw [neg_smul]
    apply neg_nonpos.mpr
    exact smul_nonneg (by norm_num) (Matrix.PosSemidef.one.nonneg)
  have he := entropyKernel_eq_sub B 0 hB (by norm_num : (1/2 : ℝ) < 1) hlo hl
  simp only [entropyKernel, Matrix.zero_mul, add_zero, Matrix.trace_zero,
    Complex.zero_re, zero_pow (by decide : 4 ≠ 0), mul_zero] at he
  dsimp [shiftError]
  simp only [zero_smul, add_zero]
  linarith only [he]

/-- A fourth-order bound for the centered operator deficit along a centered
generator eigen-direction, for both signs of a perturbation of relative size
at most one half. -/
theorem operatorDeficit_centeredQuartic {r : ℝ} (hr : 1 ≤ r)
    (H : Mat) (hH : H.IsHermitian) (d v : ℝ)
    (hdegree : generator r H = d • H) (hcenter : (D r * H).trace.re = 0)
    {bMinus bPlus : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus) :
    let x := fun i => rootValue r i ^ 2
    let B := G r * G r
    let U := G r * H * G r
    (∀ i j, U i j ≠ 0 → 3 * |Real.log (x i / x j)| = v) →
    bMinus • (1 : Mat) ≤ B → B ≤ bPlus • (1 : Mat) →
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      (-(1 / 2 : ℝ)) • (1 : Mat) ≤ t • H →
      (-(1 / 2 : ℝ)) • (1 : Mat) ≤ (-t) • H →
      let F := fun s : ℝ => WuCubicOperatorNormalization.operatorDeficit r (1 + s • H)
      |F t + F (-t) - 2*F 0 -
        2*t^2 * ((9 / 4 : ℝ) * Real.cosh (v / 6) * (d - 4 * alpha r * bohrG v) *
          ((G r)^3 * H * (G r)^3 * H).trace.re)| ≤ C * t^4 := by
  intro x B U hcharge hBlo hBhi
  have hB : B.PosDef := by
    change (G r * G r).PosDef
    rw [square_sandwich]
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast pow_pos (rootValue_pos hr i) 2
  have hD : B^3 = D r := by
    change (G r * G r)^3 = D r
    rw [← pow_two, ← pow_mul]
    exact G_pow_six hr
  have hm0 : (B ^ 3).trace.re = 1 := by rw [hD, trace_D_real hr]
  have hlin : (B ^ 2 * U + B * U * B + U * B ^ 2).trace.re = 0 := by
    simpa only [hcenter, mul_zero] using trace_mass_linear hr H
  let K := entropyFactor bMinus bPlus (1/2) * (H^4).trace.re / 3
  let Q := (|(B * U^2 + U * B * U + U^2 * B).trace.re| + |(U^3).trace.re|)^2
  refine ⟨|3*alpha r| * (2*K) + |alpha r| * (2*Q), fun t ht hpos hneg => ?_⟩
  let Y := fun s : ℝ => B + s • U
  have hsqrt : CFC.sqrt B = G r := G_eq_sqrt hr
  have hY (s : ℝ) (hs : (-(1 / 2 : ℝ)) • (1 : Mat) ≤ s • H) : (Y s).PosDef := by
    have h := displaced_posDef B (s • H) hB (by norm_num : (1/2 : ℝ) < 1) hs
    rwa [hsqrt, mul_smul_comm, smul_mul_assoc] at h
  obtain ⟨hiP, hloP, hhiP⟩ := shiftError_bound B H hB hH hb hbb hBlo hBhi hpos
  obtain ⟨hiN, hloN, hhiN⟩ := shiftError_bound B H hB hH hb hbb hBlo hBhi hneg
  have hpow : (-t)^4 = t^4 := by ring
  simp only [hsqrt] at hiP hloP hhiP hiN hloN hhiN
  rw [hpow] at hhiN
  have hmass (s : ℝ) (hs : (Y s).PosDef) : 0 < ((Y s)^3).trace.re := by
    have hc := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Y s) hs.isUnit).2 hs
    rw [hs.isHermitian.star_eq, ← pow_two, ← pow_succ] at hc
    exact (Complex.lt_def.mp hc.trace_pos).1
  have ht' : |-t| ≤ 1 := by simpa only [abs_neg] using ht
  obtain ⟨hmP, hmPle⟩ := massChargeError_bound B U hm0 hlin ht (hmass t (hY t hpos))
  obtain ⟨hmN, hmNle⟩ := massChargeError_bound B U hm0 hlin ht' (hmass (-t) (hY (-t) hneg))
  let rem := fun l => shiftError B U t l + shiftError B U (-t) l - 2 * shiftError B U 0 l
  have hre : ∫ l in Ioi (0 : ℝ), rem l =
      (∫ l in Ioi (0 : ℝ), shiftError B U t l) + ∫ l in Ioi (0 : ℝ), shiftError B U (-t) l := by
    rw [← integral_add hiP hiN]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro l hl
    simp [rem, zero_shiftError B U hB hl, U]
  obtain ⟨_, hv⟩ := operatorDeficit_centeredDifference hr H hH t d v hdegree hcharge
    (hY t hpos) (hY (-t) hneg)
  dsimp only at hv
  change _ = _ - 3*alpha r*(∫ l in Ioi (0 : ℝ), rem l) + _ at hv
  rw [← weighted_norm_trace hr H hH, hre] at hv
  dsimp only
  rw [hv]
  -- Bound the two errors with their one-sided estimates.
  change |(_ - _ + _) - _| ≤ _
  rw [show (_ - _ + _) - _ =
    -(3*alpha r) * ((∫ l in Ioi (0 : ℝ), shiftError B U t l) +
      ∫ l in Ioi (0 : ℝ), shiftError B U (-t) l) +
    alpha r * ((((Y t)^3).trace.re * Real.log ((Y t)^3).trace.re - (((Y t)^3).trace.re - 1)) +
      (((Y (-t))^3).trace.re * Real.log ((Y (-t))^3).trace.re -
        (((Y (-t))^3).trace.re - 1))) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (add_nonneg hloP hloN),
    abs_of_nonneg (add_nonneg hmP hmN)]
  calc
    _ ≤ |3*alpha r| * ((K * t^4) + (K * t^4)) + |alpha r| * ((Q * t^4) + (Q * t^4)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hhiP hhiN) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (add_le_add hmPle (by simpa only [hpow] using hmNle))
          (abs_nonneg _))
    _ = _ := by ring

#print axioms operatorDeficit_centeredQuartic

open scoped Topology Asymptotics Matrix.Norms.L2Operator in
/-- The centered difference of the cubic deficit along a centered generator
eigen-direction has the physical quadratic coefficient with an order-four
remainder as the real perturbation tends to zero. -/
theorem operatorDeficit_centered_isBigO {r : ℝ} (hr : 1 ≤ r)
    (H : Mat) (hH : H.IsHermitian) (d v : ℝ)
    (hdegree : generator r H = d • H) (hcenter : (D r * H).trace.re = 0) :
    let x := fun i => rootValue r i ^ 2
    let U := G r * H * G r
    (∀ i j, U i j ≠ 0 → 3 * |Real.log (x i / x j)| = v) →
    let F := fun s : ℝ => WuCubicOperatorNormalization.operatorDeficit r (1 + s • H)
    (fun t : ℝ => F t + F (-t) - 2 * F 0 -
      2 * t^2 * ((9 / 4 : ℝ) * Real.cosh (v / 6) * (d - 4 * alpha r * bohrG v) *
        ((G r)^3 * H * (G r)^3 * H).trace.re)) =O[𝓝 0] (fun t : ℝ => t^4) := by
  intro x U hcharge F
  let B := G r * G r
  have hB : B.PosDef := by
    change (G r * G r).PosDef
    rw [square_sandwich]
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast pow_pos (rootValue_pos hr i) 2
  have hBs := hB.isHermitian.isSelfAdjoint
  have hspec (y) (hy : y ∈ spectrum ℝ B) : 0 < y := by
    rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hy
    obtain ⟨i, rfl⟩ := hy
    exact hB.eigenvalues_pos i
  obtain ⟨bMinus, hb, hBlo⟩ := (CFC.exists_pos_algebraMap_le_iff B hBs).mpr hspec
  have hBhi := hBs.le_algebraMap_norm_self (a := B)
  rw [Algebra.algebraMap_eq_smul_one] at hBlo hBhi
  have hbb : bMinus ≤ ‖B‖ := by
    have hle := (algebraMap_le_iff_le_spectrum (r := bMinus) hBs).mp
      (by rwa [Algebra.algebraMap_eq_smul_one])
    let i : WuCubicOperatorBridge.Occupation := (0, 0)
    have hi : hB.isHermitian.eigenvalues i ∈ spectrum ℝ B := by
      rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact Set.mem_range_self i
    exact (hle _ hi).trans ((Real.le_norm_self _).trans (spectrum.norm_le_norm_of_mem hi))
  obtain ⟨C, hC⟩ := operatorDeficit_centeredQuartic hr H hH d v hdegree hcenter hb hbb
    hcharge hBlo hBhi
  have hsmall (s : ℝ) (hs : ‖s • H‖ ≤ 1 / 2) :
      (-(1 / 2 : ℝ)) • (1 : Mat) ≤ s • H := by
    have hsa : IsSelfAdjoint (s • H) :=
      IsSelfAdjoint.smul (show IsSelfAdjoint s from rfl) hH.isSelfAdjoint
    have h := hsa.neg_algebraMap_norm_le_self (a := s • H)
    rw [Algebra.algebraMap_eq_smul_one, ← neg_smul] at h
    exact (smul_le_smul_of_nonneg_right (neg_le_neg hs) (Matrix.PosSemidef.one.nonneg)).trans h
  have ht : Filter.Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.continuousAt.tendsto (x := (0 : ℝ))
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖t • H‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => ‖t • H‖) :=
      (continuous_id.smul continuous_const).norm
    simpa only [zero_smul, norm_zero] using hc.continuousAt.tendsto (x := (0 : ℝ))
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hnorm.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with t h₁ h₂
  have h₃ : ‖(-t) • H‖ ≤ 1/2 := by simpa only [neg_smul, norm_neg] using h₂
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ t^4 by positivity)] using
    hC t h₁ (hsmall t h₂) (hsmall (-t) h₃)

#print axioms operatorDeficit_centered_isBigO

end D5.S3.Quantum.Semigroups.WuCubicPhysicalHessian
