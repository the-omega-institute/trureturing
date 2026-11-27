import D5.S3.Quantum.Recovery.BKMPowerPullback
import D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian

/-! The actual Petz BKM integral at a diagonal cube and the Wu cubic entropy pairing. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicBKMEntropyPairing

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMPowerPullback (omega_cube)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)
open D5.S3.Quantum.Recovery.BKMSpectralVariance
  (logMean logMean_self logMean_mul_logRatio omegaLinear omega_trace_eq_trace_mul)
open WuCubicHotInnerDiagonalHessian
  (entropyPairKernel shiftHessian physical_trace_quadratic_sub_charges)

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "diagℝ" x => Matrix.diagonal (fun i => (x i : ℂ))

/-- The divided difference of `3 log`, with its derivative at coincident levels. -/
def logTangentCoefficient (x y : ℝ) : ℝ :=
  if x = y then 3 / x else 3 * (Real.log x - Real.log y) / (x - y)

/-- The entrywise logarithmic tangent associated to `U` and the spectrum `x`. -/
def logTangent (x : n → ℝ) (U : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => (logTangentCoefficient (x i) (x j) : ℂ) * U i j

/-- The linear coefficient of `(B + t • U)³` at `t = 0`. -/
def cubicTangent (B U : Matrix n n ℂ) : Matrix n n ℂ :=
  B ^ 2 * U + B * U * B + U * B ^ 2

private theorem logMean_mul_logTangentCoefficient {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logMean x y * logTangentCoefficient x y = 3 := by
  by_cases hxy : x = y
  · subst y
    rw [logMean_self hx, logTangentCoefficient, ite_eq_left rfl]
    calc
      _ = 3 * (x / x) := by ring
      _ = _ := by rw [div_self hx.ne', mul_one]
  · have hmean : logMean x y * (Real.log x - Real.log y) = x - y := by
      simpa only [Real.log_div hx.ne' hy.ne'] using logMean_mul_logRatio hx hy
    rw [logTangentCoefficient, ite_eq_right hxy]
    calc
      _ = 3 * (logMean x y * (Real.log x - Real.log y) / (x - y)) := by ring
      _ = _ := by rw [hmean, div_self (sub_ne_zero.mpr hxy), mul_one]

private theorem omega_diagonal_entry (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (X : Matrix n n ℂ) (i j : n) :
    omega (diagℝ x) X i j = (logMean (x i) (x j) : ℂ) * X i j := by
  let B := diagℝ x
  have hB : B.PosDef := Matrix.posDef_diagonal_iff.mpr (fun k => by exact_mod_cast hx k)
  have hpow (s : ℝ) : mpow B s = diagℝ (fun k => x k ^ s) := by
    rw [mpow]
    refine (Matrix.cfc_diagonal_real (𝕜 := ℂ) x (fun a : ℝ => a ^ s)).trans ?_
    exact congrArg Matrix.diagonal (funext fun _ => rfl)
  have hc := continuous_mpow B hB
  have hsub : Continuous (fun s : ℝ => 1 - s) := continuous_const.sub continuous_id
  have hint : IntervalIntegrable (fun s : ℝ => mpow B s * X * mpow B (1 - s)) volume 0 1 :=
    ((hc.mul continuous_const).mul (hc.comp hsub)).intervalIntegrable 0 1
  let entry := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  change entry (∫ s : ℝ in 0..1, mpow B s * X * mpow B (1 - s)) = _
  rw [← entry.intervalIntegral_comp_comm hint]
  change (∫ s : ℝ in 0..1, (mpow B s * X * mpow B (1 - s)) i j) = _
  have hentry (s : ℝ) : (mpow B s * X * mpow B (1 - s)) i j =
      ((x i ^ s * x j ^ (1 - s) : ℝ) : ℂ) * X i j := by
    simp only [hpow, Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_mul]
    ring
  simp only [hentry, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, logMean]

/-- Petz's integral maps the logarithmic tangent to the cubic tangent for every complex matrix. -/
theorem omega_cube_logTangent (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) :
    omega ((diagℝ x) ^ 3) (logTangent x U) = cubicTangent (diagℝ x) U := by
  let B := diagℝ x
  have hB : B.PosDef := Matrix.posDef_diagonal_iff.mpr (fun k => by exact_mod_cast hx k)
  have homega : omega B (logTangent x U) = (3 : ℝ) • U := by
    ext i j
    rw [omega_diagonal_entry x hx]
    simp only [logTangent, Matrix.of_apply, ← mul_assoc, ← Complex.ofReal_mul,
      logMean_mul_logTangentCoefficient (hx i) (hx j), Matrix.smul_apply,
      Complex.real_smul, Complex.ofReal_ofNat]
  change omega (B ^ 3) (logTangent x U) = cubicTangent B U
  rw [omega_cube hB, homega, cubicTangent]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, one_div]
  norm_num

private theorem cubicTangent_diagonal_entry (x : n → ℝ) (U : Matrix n n ℂ) (i j : n) :
    cubicTangent (diagℝ x) U i j = ((x i ^ 2 + x i * x j + x j ^ 2 : ℝ) : ℂ) * U i j := by
  simp only [cubicTangent, Matrix.diagonal_pow, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.pow_apply, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

private theorem logTangentCoefficient_comm (x y : ℝ) :
    logTangentCoefficient y x = logTangentCoefficient x y := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp only [logTangentCoefficient, ite_eq_right hxy, ite_eq_right (Ne.symm hxy)]
    rw [show Real.log y - Real.log x = -(Real.log x - Real.log y) by ring,
      show y - x = -(x - y) by ring, mul_neg, neg_div_neg_eq]

private theorem entropyPairKernel_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x ^ 2 + x * y + y ^ 2) * logTangentCoefficient x y = entropyPairKernel x y := by
  by_cases hxy : x = y
  · subst y
    rw [logTangentCoefficient, ite_eq_left rfl, entropyPairKernel, ite_eq_left rfl]
    field_simp [hx.ne']
    ring
  · rw [logTangentCoefficient, ite_eq_right hxy, entropyPairKernel, ite_eq_right hxy,
      Real.log_div hx.ne' hy.ne']
    ring

/-- The real BKM pairing equals the Wu entropy kernel summed over ordered pairs.
This sum is twice the quadratic coefficient in `physical_trace_quadratic_sub_charges`. -/
theorem trace_cubicTangent_mul_logTangent (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (U : Matrix n n ℂ) (hU : U.IsHermitian) :
    (cubicTangent (diagℝ x) U * logTangent x U).trace.re =
      ∑ i, ∑ j, entropyPairKernel (x i) (x j) * Complex.normSq (U i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [cubicTangent_diagonal_entry, logTangent, Matrix.of_apply]
  rw [logTangentCoefficient_comm (x i) (x j),
    ← hU.apply j i, Complex.star_def]
  rw [show ∀ a b : ℝ, ∀ z : ℂ,
    ((a : ℂ) * z) * ((b : ℂ) * starRingEnd ℂ z) =
      (a : ℂ) * (b : ℂ) * (z * starRingEnd ℂ z) by intros; ring]
  rw [Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
    entropyPairKernel_factor (hx i) (hx j)]

/-- The unnormalized quadratic coefficient before the rank-one mass correction is
half the pairing with the actual BKM inverse tangent. -/
theorem physical_trace_quadratic_eq_half_pairing (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (U : Matrix n n ℂ) (hU : U.IsHermitian) :
    let B := diagℝ x
    let T := B * U ^ 2 + U * B * U + U ^ 2 * B
    3 * (∫ l in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) *
      ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) -
      T.trace.re - (T * cfc Real.log (B ^ 3)).trace.re =
      (1 / 2 : ℝ) * (cubicTangent B U * logTangent x U).trace.re := by
  dsimp only
  rw [trace_cubicTangent_mul_logTangent x hx U hU]
  exact physical_trace_quadratic_sub_charges x hx U hU

omit [DecidableEq n] in
private theorem trace_real_smul (c : ℝ) (A : Matrix n n ℂ) :
    (c • A).trace.re = c * A.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- Removing the mass direction gives a BKM equation on the centered tangent and
subtracts exactly the rank-one mass term from the Hessian pairing. -/
theorem centered_bkm_pairing (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (U : Matrix n n ℂ) (hU : U.IsHermitian)
    (hmass : 0 < (((diagℝ x) ^ 3 : Matrix n n ℂ)).trace.re) :
    let B := diagℝ x
    let ρ := B ^ 3
    let L := cubicTangent B U
    let V := logTangent x U
    let c := L.trace.re / ρ.trace.re
    let L₀ := L - c • ρ
    let V₀ := V - c • (1 : Matrix n n ℂ)
    omega ρ V₀ = L₀ ∧ (L₀ * V₀).trace.re =
      (∑ i, ∑ j, entropyPairKernel (x i) (x j) * Complex.normSq (U i j)) -
        L.trace.re ^ 2 / ρ.trace.re := by
  intro B ρ L V c L₀ V₀
  have hρ : ρ = diagℝ (fun i => x i ^ 3) := by
    simp only [ρ, B, Matrix.diagonal_pow, Complex.ofReal_pow]
    rfl
  have hx₃ (i : n) : 0 < x i ^ 3 := pow_pos (hx i) _
  have hpos : ρ.PosDef := by
    rw [hρ]
    exact Matrix.posDef_diagonal_iff.mpr (fun k => by exact_mod_cast hx₃ k)
  have hone : omega ρ (1 : Matrix n n ℂ) = ρ := by
    rw [hρ]
    ext i j
    rw [omega_diagonal_entry _ hx₃]
    by_cases hij : i = j
    · subst j
      simp [logMean_self (hx₃ i)]
    · simp [hij]
  have hL : omega ρ V = L := omega_cube_logTangent x hx U
  have hρV : (ρ * V).trace = L.trace := by
    rw [← omega_trace_eq_trace_mul hpos, hL]
  have hmass₀ : L₀.trace.re = 0 := by
    dsimp only [L₀]
    rw [Matrix.trace_sub, Complex.sub_re, trace_real_smul]
    change L.trace.re - L.trace.re / ρ.trace.re * ρ.trace.re = 0
    rw [div_mul_cancel₀ _ hmass.ne', sub_self]
  constructor
  · let Ω := (omegaLinear hpos).restrictScalars ℝ
    change Ω (V - c • 1) = L - c • ρ
    rw [map_sub, map_smul]
    change omega ρ V - c • omega ρ 1 = _
    rw [hL, hone]
  · change (L₀ * (V - c • 1)).trace.re = _
    rw [mul_sub, mul_smul_comm, mul_one, Matrix.trace_sub, Complex.sub_re,
      trace_real_smul, hmass₀, mul_zero, sub_zero]
    change ((L - c • ρ) * V).trace.re = _
    rw [sub_mul, smul_mul_assoc, Matrix.trace_sub, Complex.sub_re, trace_real_smul, hρV]
    have hpair : (L * V).trace.re = _ := trace_cubicTangent_mul_logTangent x hx U hU
    rw [hpair]
    dsimp only [c]
    ring

#print axioms omega_cube_logTangent
#print axioms trace_cubicTangent_mul_logTangent
#print axioms physical_trace_quadratic_eq_half_pairing
#print axioms centered_bkm_pairing

end D5.S3.Quantum.Semigroups.WuCubicBKMEntropyPairing
