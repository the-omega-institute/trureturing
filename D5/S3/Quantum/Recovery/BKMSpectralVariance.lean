/- GID: D5/S3/Quantum/Recovery/BKMSpectralVariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMSpectralVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eigenbasis formulas and the logarithmic-mean variance bound for the BKM integral. -/

import D5.S3.Quantum.Recovery.BKMRelativeDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Spectral variance for the actual finite BKM integral -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Recovery.BKMRelativeDensity (continuous_mpow omega)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)

namespace D5.S3.Quantum.Recovery.BKMSpectralVariance

/-- The scalar integral occurring in a diagonal spectral entry of BKM omega. -/
private def logMean (x y : ℝ) : ℝ :=
  ∫ s : ℝ in 0..1, x ^ s * y ^ (1 - s)

private theorem logMean_self {x : ℝ} (hx : 0 < x) : logMean x x = x := by
  have h (s : ℝ) : x ^ s * x ^ (1 - s) = x := by
    rw [← Real.rpow_add hx, show s + (1 - s) = 1 by ring, Real.rpow_one]
  simp [logMean, h, intervalIntegral.integral_const]

private theorem logMean_mul_logRatio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logMean x y * Real.log (x / y) = x - y := by
  let r := Real.log (x / y)
  have hr : Real.exp r = x / y := Real.exp_log (div_pos hx hy)
  change logMean x y * r = x - y
  by_cases hzero : r = 0
  · rw [hzero, Real.exp_zero] at hr
    have hxy := (div_eq_iff hy.ne').mp hr.symm
    simp [hzero, hxy]
  have h (s : ℝ) : x ^ s * y ^ (1 - s) = y * Real.exp (s * r) := by
    calc
      _ = Real.exp (Real.log y) * Real.exp (s * r) := by
        rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [r]
        rw [Real.log_div hx.ne' hy.ne']
        ring
      _ = _ := by rw [Real.exp_log hy]
  simp only [logMean, h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_right Real.exp hzero, zero_mul, one_mul, smul_eq_mul,
    integral_exp, hr, Real.exp_zero]
  field_simp

private theorem cosh_quartic_lower (r : ℝ) :
    1 + r ^ 2 / 2 + r ^ 4 / 24 ≤ Real.cosh r := by
  have h := r.hasSum_cosh.summable.sum_le_tsum (Finset.range 3) (fun n _ =>
    div_nonneg (by rw [mul_comm 2 n, pow_mul]; exact sq_nonneg (r ^ n))
      (Nat.cast_nonneg _))
  rw [r.hasSum_cosh.tsum_eq] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- The scalar logarithmic rigidity estimate with the exact logarithmic ratio. -/
private theorem logMean_sq_sub_mul_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) ^ 2 / (12 + Real.log (x / y) ^ 2) ≤ logMean x y ^ 2 - x * y := by
  by_cases hxy : x = y
  · subst y
    rw [logMean_self hx]
    simp [pow_two]
  let r := Real.log (x / y)
  change (x - y) ^ 2 / (12 + r ^ 2) ≤ logMean x y ^ 2 - x * y
  have hr : Real.exp r = x / y := Real.exp_log (div_pos hx hy)
  have hL : logMean x y * r = x - y := logMean_mul_logRatio hx hy
  have hr0 : r ≠ 0 := by
    intro hz
    exact hxy (sub_eq_zero.mp (by simpa [hz] using hL.symm))
  have hcosh : x * y * (2 * (Real.cosh r - 1)) = (x - y) ^ 2 := by
    rw [Real.cosh_eq, Real.exp_neg, hr]
    field_simp [hx.ne', hy.ne']
    ring
  have hquartic : r ^ 2 + r ^ 4 / 12 ≤ 2 * (Real.cosh r - 1) := by
    linarith only [cosh_quartic_lower r]
  have hsquare : (logMean x y) ^ 2 * r ^ 2 = (x - y) ^ 2 := by
    rw [← mul_pow, hL]
  have hscaled := mul_le_mul_of_nonneg_left hquartic (mul_nonneg hx.le hy.le)
  rw [hcosh, ← hsquare] at hscaled
  have hcancel : x * y * (12 + r ^ 2) ≤ 12 * (logMean x y) ^ 2 := by
    apply le_of_mul_le_mul_right _ (sq_pos_of_ne_zero hr0)
    linarith only [hscaled]
  apply (div_le_iff₀ (by positivity : 0 < 12 + r ^ 2)).2
  rw [← hsquare]
  linarith only [hcancel]

section Spectral

variable {ι : Type*} [Fintype ι]

private theorem weighted_product_sum (p f g : ι → ℝ) :
    (∑ i, ∑ j, p i * p j * (f i * g j)) = (∑ i, p i * f i) * (∑ j, p j * g j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The squared pairwise gap is twice the variance under finite probability weights. -/
private theorem pairwise_sq_eq_twice_variance (p eigenvalue : ι → ℝ) (hp : ∑ i, p i = 1) :
    (∑ i, ∑ j, p i * p j * (eigenvalue i - eigenvalue j) ^ 2) =
      2 * ((∑ i, p i * eigenvalue i ^ 2) - (∑ i, p i * eigenvalue i) ^ 2) := by
  have h (i j : ι) :
      p i * p j * (eigenvalue i - eigenvalue j) ^ 2 =
        p i * p j * (eigenvalue i ^ 2 * 1) + p i * p j * (1 * eigenvalue j ^ 2) -
          2 * (p i * p j * (eigenvalue i * eigenvalue j)) := by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [weighted_product_sum p (fun i => eigenvalue i ^ 2) (fun _ => 1),
    weighted_product_sum p (fun _ => 1) (fun j => eigenvalue j ^ 2),
    weighted_product_sum p eigenvalue eigenvalue]
  simp only [mul_one, hp, one_mul]
  ring

/-- The actual logarithmic means in a probability-weighted spectral trace-square sum
give a lower bound by twice the variance divided by the common conditioning factor. -/
private theorem weighted_logMean_trace_sq_sub_mean_sq_ge (p eigenvalue : ι → ℝ) (T : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hprob : ∑ i, p i = 1) (heigenvalue : ∀ i, 0 < eigenvalue i)
    (hT : ∀ i j, |Real.log (eigenvalue i / eigenvalue j)| ≤ T) :
    2 * ((∑ i, p i * eigenvalue i ^ 2) - (∑ i, p i * eigenvalue i) ^ 2) / (12 + T ^ 2) ≤
      (∑ i, ∑ j, p i * p j * logMean (eigenvalue i) (eigenvalue j) ^ 2) -
        (∑ i, p i * eigenvalue i) ^ 2 := by
  have hpoint (i j : ι) :
      (eigenvalue i - eigenvalue j) ^ 2 / (12 + T ^ 2) ≤
        logMean (eigenvalue i) (eigenvalue j) ^ 2 - eigenvalue i * eigenvalue j := by
    have habs := hT i j
    have hsq : Real.log (eigenvalue i / eigenvalue j) ^ 2 ≤ T ^ 2 := by
      rw [← sq_abs (Real.log (eigenvalue i / eigenvalue j))]
      gcongr
    exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (add_le_add_right hsq 12)).trans (logMean_sq_sub_mul_ge (heigenvalue i) (heigenvalue j))
  have hsum : (∑ i, ∑ j, p i * p j * ((eigenvalue i - eigenvalue j) ^ 2 / (12 + T ^ 2))) ≤
      ∑ i, ∑ j, p i * p j *
        (logMean (eigenvalue i) (eigenvalue j) ^ 2 - eigenvalue i * eigenvalue j) := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hpoint i j) (mul_nonneg (hp i) (hp j))
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib] at hsum
  rw [pairwise_sq_eq_twice_variance p eigenvalue hprob,
    weighted_product_sum p eigenvalue eigenvalue, ← pow_two] at hsum
  exact hsum

end Spectral

section Matrix

open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation preserves the complex matrix trace. -/
theorem trace_conjStarAlgAut_symm (W : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    Matrix.trace ((Unitary.conjStarAlgAut ℂ _ W).symm A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]

/-- Conjugation from the spectral basis into the original matrix coordinates. -/
abbrev fromEigenbasis {a : Matrix n n ℂ} (ha : a.PosDef) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ha.isHermitian.eigenvectorUnitary).toAlgEquiv

/-- In the spectral basis of a positive definite matrix, the actual BKM integral
multiplies entry `i,j` by the logarithmic mean of the corresponding eigenvalues. -/
private theorem omega_eigenbasis_entry {a : Matrix n n ℂ} (ha : a.PosDef)
    (X : Matrix n n ℂ) (i j : n) :
    ((fromEigenbasis ha).symm (omega a X)) i j =
      (logMean (ha.isHermitian.eigenvalues i) (ha.isHermitian.eigenvalues j) : ℂ) *
        ((fromEigenbasis ha).symm X) i j := by
  let U := fromEigenbasis ha
  let eigenvalue := ha.isHermitian.eigenvalues
  let D (s : ℝ) : Matrix n n ℂ := diagonal fun k => (eigenvalue k ^ s : ℝ)
  have hpow (s : ℝ) : U.symm (mpow a s) = D s := by
    rw [mpow, ha.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
    exact U.symm_apply_apply (D s)
  have hc := continuous_mpow a ha
  have hsub : Continuous (fun s : ℝ => 1 - s) := continuous_const.sub continuous_id
  have hint : IntervalIntegrable (fun s : ℝ => mpow a s * X * mpow a (1 - s)) volume 0 1 :=
    ((hc.mul (continuous_const (y := X))).mul (hc.comp hsub)).intervalIntegrable 0 1
  let entry := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  let E := entry.comp U.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  change E (∫ s : ℝ in 0..1, mpow a s * X * mpow a (1 - s)) = _
  rw [← E.intervalIntegral_comp_comm hint]
  change (∫ s : ℝ in 0..1, (U.symm (mpow a s * X * mpow a (1 - s))) i j) = _
  have hentry (s : ℝ) :
      (U.symm (mpow a s * X * mpow a (1 - s))) i j =
        ((eigenvalue i ^ s * eigenvalue j ^ (1 - s) : ℝ) : ℂ) * (U.symm X) i j := by
    simp only [map_mul, hpow, D, Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_mul]
    ring
  simp only [hentry, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rfl

private theorem logMean_comm (x y : ℝ) : logMean x y = logMean y x := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun s => x ^ s * y ^ (1 - s)) 1
  simpa only [sub_self, sub_zero, sub_sub_cancel, logMean, mul_comm] using h.symm

/-- The BKM integral is complex-linear in its matrix input. -/
def omegaLinear {a : Matrix n n ℂ} (ha : a.PosDef) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := omega a
  map_add' B C := by
    apply (fromEigenbasis ha).symm.injective
    ext i j
    rw [map_add, Matrix.add_apply, omega_eigenbasis_entry, omega_eigenbasis_entry,
      omega_eigenbasis_entry, map_add, Matrix.add_apply, mul_add]
  map_smul' c B := by
    apply (fromEigenbasis ha).symm.injective
    ext i j
    rw [map_smul, Matrix.smul_apply, omega_eigenbasis_entry, omega_eigenbasis_entry,
      map_smul, Matrix.smul_apply, RingHom.id_apply]
    simp only [smul_eq_mul]
    ring

/-- BKM omega of a Hermitian input is Hermitian. -/
theorem omega_isHermitian {a A : Matrix n n ℂ} (ha : a.PosDef) (hA : A.IsHermitian) :
    (omega a A).IsHermitian := by
  let F := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ha.isHermitian.eigenvectorUnitary
  have hF (B : Matrix n n ℂ) (hB : B.IsHermitian) : (F.symm B).IsHermitian := by
    change star (F.symm B) = F.symm B
    rw [← map_star, hB.star_eq]
  change star (omega a A) = omega a A
  apply F.symm.injective
  refine (map_star F.symm _).trans ?_
  apply Matrix.IsHermitian.ext
  intro i j
  change star (((fromEigenbasis ha).symm (omega a A)) j i) =
    ((fromEigenbasis ha).symm (omega a A)) i j
  rw [omega_eigenbasis_entry, omega_eigenbasis_entry, star_mul]
  change (starRingEnd ℂ) (((fromEigenbasis ha).symm A) j i) *
    (starRingEnd ℂ) (↑(logMean (ha.isHermitian.eigenvalues j)
      (ha.isHermitian.eigenvalues i)) : ℂ) = _
  rw [Complex.conj_ofReal, logMean_comm (ha.isHermitian.eigenvalues j)
    (ha.isHermitian.eigenvalues i)]
  have hentry := (hF A hA).apply i j
  change (starRingEnd ℂ) (((fromEigenbasis ha).symm A) j i) =
    ((fromEigenbasis ha).symm A) i j at hentry
  rw [hentry, mul_comm]

/-- The real trace of the actual rank-one BKM output is the first spectral moment. -/
theorem omega_rankOne_trace_re {a : Matrix n n ℂ} (ha : a.PosDef) (v : n → ℂ) :
    (omega a ((fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v)))).trace.re =
      ∑ i, ‖v i‖ ^ 2 * ha.isHermitian.eigenvalues i := by
  let U := fromEigenbasis ha
  let P := U (vecMulVec v (starRingEnd ℂ ∘ v))
  change (omega a P).trace.re = _
  rw [← trace_conjStarAlgAut_symm ha.isHermitian.eigenvectorUnitary (omega a P)]
  change (U.symm (omega a P)).trace.re = _
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [omega_eigenbasis_entry, logMean_self (ha.eigenvalues_pos i)]
  change ((↑(ha.isHermitian.eigenvalues i) : ℂ) *
    (U.symm (U (vecMulVec v (starRingEnd ℂ ∘ v)))) i i).re = _
  simp only [AlgEquiv.symm_apply_apply, vecMulVec_apply, Function.comp_apply]
  rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- Unitary conjugation of the rank-one input into the original coordinates gives a
Hermitian BKM output. -/
theorem omega_rankOne_isHermitian {a : Matrix n n ℂ} (ha : a.PosDef) (v : n → ℂ) :
    (omega a ((fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v)))).IsHermitian := by
  apply omega_isHermitian ha
  let F := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ha.isHermitian.eigenvectorUnitary
  let P := vecMulVec v (starRingEnd ℂ ∘ v)
  have hP : P.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  change star (F P) = F P
  rw [← map_star, hP.star_eq]

/-- The trace-square deficit of the actual BKM output on a unit rank-one input
is bounded below by the corresponding spectral variance with the common bound `T`. -/
theorem omega_rankOne_trace_sq_sub_trace_sq_ge {a : Matrix n n ℂ} (ha : a.PosDef)
    (v : n → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (T : ℝ)
    (hT : ∀ i j, |Real.log (ha.isHermitian.eigenvalues i / ha.isHermitian.eigenvalues j)| ≤ T) :
    let p := fun i => ‖v i‖ ^ 2
    let eigenvalue := ha.isHermitian.eigenvalues
    let P := (fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v))
    let M := omega a P
    2 * ((∑ i, p i * eigenvalue i ^ 2) - (∑ i, p i * eigenvalue i) ^ 2) / (12 + T ^ 2) ≤
      (Matrix.trace (M * M)).re - (Matrix.trace M).re ^ 2 := by
  dsimp only
  let p := fun i => ‖v i‖ ^ 2
  let eigenvalue := ha.isHermitian.eigenvalues
  let U := fromEigenbasis ha
  let P := U (vecMulVec v (starRingEnd ℂ ∘ v))
  let M := omega a P
  change 2 * ((∑ i, p i * eigenvalue i ^ 2) - (∑ i, p i * eigenvalue i) ^ 2) /
    (12 + T ^ 2) ≤ (Matrix.trace (M * M)).re - (Matrix.trace M).re ^ 2
  have hentry (i j : n) :
      (U.symm M) i j = (logMean (eigenvalue i) (eigenvalue j) : ℂ) *
        (v i * (starRingEnd ℂ) (v j)) := by
    calc
      _ = (logMean (eigenvalue i) (eigenvalue j) : ℂ) * (U.symm P) i j :=
        omega_eigenbasis_entry ha P i j
      _ = _ := by
        change _ * (U.symm (U (vecMulVec v (starRingEnd ℂ ∘ v)))) i j = _
        simp only [AlgEquiv.symm_apply_apply, vecMulVec_apply, Function.comp_apply]
  have hnorm (i : n) : v i * (starRingEnd ℂ) (v i) = (p i : ℂ) := by
    simpa only [p, Complex.ofReal_pow] using Complex.mul_conj' (v i)
  have hfirst : (Matrix.trace M).re = ∑ i, p i * eigenvalue i :=
    omega_rankOne_trace_re ha v
  have hsecond : (Matrix.trace (M * M)).re =
      ∑ i, ∑ j, p i * p j * logMean (eigenvalue i) (eigenvalue j) ^ 2 := by
    rw [← trace_conjStarAlgAut_symm ha.isHermitian.eigenvectorUnitary (M * M)]
    change (U.symm (M * M)).trace.re = _
    rw [map_mul]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hentry i j, hentry j i, logMean_comm (eigenvalue j) (eigenvalue i)]
    have hprod :
        ((logMean (eigenvalue i) (eigenvalue j) : ℂ) * (v i * (starRingEnd ℂ) (v j))) *
        ((logMean (eigenvalue i) (eigenvalue j) : ℂ) * (v j * (starRingEnd ℂ) (v i))) =
          (v i * (starRingEnd ℂ) (v i)) * (v j * (starRingEnd ℂ) (v j)) *
            (logMean (eigenvalue i) (eigenvalue j) : ℂ) ^ 2 := by ring
    rw [hprod, hnorm, hnorm, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hfirst, hsecond]
  exact weighted_logMean_trace_sq_sub_mean_sq_ge p eigenvalue T
    (fun i => sq_nonneg ‖v i‖) hv ha.eigenvalues_pos hT

/-- The trace of the BKM integral equals the trace of left multiplication by the reference. -/
theorem omega_trace_eq_trace_mul {a : Matrix n n ℂ} (ha : a.PosDef)
    (B : Matrix n n ℂ) : (omega a B).trace = (a * B).trace := by
  let U := fromEigenbasis ha
  have hdiag : U.symm a = diagonal (fun i => (ha.isHermitian.eigenvalues i : ℂ)) := by
    conv_lhs => rw [ha.isHermitian.spectral_theorem]
    exact U.symm_apply_apply _
  rw [← trace_conjStarAlgAut_symm ha.isHermitian.eigenvectorUnitary (omega a B),
    ← trace_conjStarAlgAut_symm ha.isHermitian.eigenvectorUnitary (a * B)]
  change (U.symm (omega a B)).trace = (U.symm (a * B)).trace
  rw [map_mul, hdiag]
  simp only [Matrix.trace, Matrix.diag_apply, diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  change ((fromEigenbasis ha).symm (omega a B)) i i = _
  rw [omega_eigenbasis_entry, logMean_self (ha.eigenvalues_pos i)]

end Matrix

end D5.S3.Quantum.Recovery.BKMSpectralVariance
