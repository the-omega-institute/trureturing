/- GID: D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Finite-spectrum entropy order from actual shifted determinant order. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Entropy from shifted products of finite spectra

The cutoff calculation follows section 4 of `three-mode-bravyi-entropy-certificate.py`.
The common index type makes the constant cutoff terms agree. Equal traces cancel
the terms linear in the spectral values and proportional to `log R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped BigOperators Interval

namespace D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy

noncomputable section

/-- The nonlinear remainder after subtracting the term linear in the eigenvalue. -/
def logShiftRemainder (R x : ℝ) : ℝ :=
  (R + x) * Real.log (1 + x / R) - x

private theorem logShiftRemainder_bounds {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) :
    0 ≤ logShiftRemainder R x ∧ logShiftRemainder R x ≤ x ^ 2 / R := by
  let u : ℝ := 1 + x / R
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hRx : 0 ≤ R + x := add_nonneg hR.le hx
  have hRu : R * u = R + x := by
    dsimp [u]
    field_simp [hR.ne']
  have hinv : (R + x) * u⁻¹ = R := by
    rw [← hRu, mul_assoc, mul_inv_cancel₀ hu.ne', mul_one]
  have hlower := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (inv_pos.mpr hu)) hRx
  rw [Real.log_inv, mul_neg, mul_sub, hinv, mul_one] at hlower
  have hupper := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hRx
  have hu_sub : u - 1 = x / R := by
    dsimp [u]
    ring
  rw [hu_sub] at hupper
  have hquad : (R + x) * (x / R) = x + x ^ 2 / R := by
    field_simp [hR.ne']
  rw [hquad] at hupper
  change 0 ≤ (R + x) * Real.log u - x ∧ (R + x) * Real.log u - x ≤ x ^ 2 / R
  constructor
  · linarith only [hlower]
  · linarith only [hupper]

private theorem intervalIntegrable_log_add (R x : ℝ) :
    IntervalIntegrable (fun s => Real.log (s + x)) volume 0 R := by
  simpa only [sub_self, add_sub_cancel_right] using
    (intervalIntegral.intervalIntegrable_log' (a := x) (b := R + x)).comp_add_right x

-- Mathlib's `integral_log` includes `x = 0`, where the lower term `x * log x` is zero.
private theorem integral_log_add_eq {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) :
    (∫ s in (0 : ℝ)..R, Real.log (s + x)) =
      (R * Real.log R - R) + x * Real.log R - x * Real.log x + x + logShiftRemainder R x := by
  have hu : 0 < 1 + x / R := by positivity
  have hfactor : R * (1 + x / R) = R + x := by
    field_simp [hR.ne']
  have hlog : Real.log (R + x) = Real.log R + Real.log (1 + x / R) := by
    rw [← hfactor, Real.log_mul hR.ne' hu.ne']
  rw [intervalIntegral.integral_comp_add_right Real.log x, zero_add, _root_.integral_log, hlog]
  unfold logShiftRemainder
  ring

private theorem integral_sum_log_add_eq {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) {R : ℝ} (hR : 0 < R) :
    (∫ s in (0 : ℝ)..R, ∑ i, Real.log (s + a i)) =
      (∑ _ : ι, (R * Real.log R - R)) + (∑ i, a i) * Real.log R -
        (∑ i, a i * Real.log (a i)) + (∑ i, a i) + ∑ i, logShiftRemainder R (a i) := by
  calc
    _ = ∑ i, ∫ s in (0 : ℝ)..R, Real.log (s + a i) :=
      intervalIntegral.integral_finsetSum (f := fun i s => Real.log (s + a i))
        (fun i _ => intervalIntegrable_log_add R (a i))
    _ = ∑ i, ((R * Real.log R - R) + a i * Real.log R - a i * Real.log (a i) + a i +
        logShiftRemainder R (a i)) :=
      Finset.sum_congr rfl (fun i _ => integral_log_add_eq hR (ha i))
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]

private theorem intervalIntegrable_sum_log_add {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (R : ℝ) : IntervalIntegrable (fun s => ∑ i, Real.log (s + x i)) volume 0 R := by
  convert IntervalIntegrable.sum Finset.univ (f := fun i s => Real.log (s + x i))
    (fun i _ => intervalIntegrable_log_add R (x i)) using 1
  funext s
  rw [Finset.sum_apply]

private theorem log_shifted_product_eq_sum {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) {s : ℝ} (hs : 0 < s) :
    Real.log (∏ i, (s + x i)) = ∑ i, Real.log (s + x i) :=
  Real.log_prod (fun i _ => (add_pos_of_pos_of_nonneg hs (hx i)).ne')

/-- The interval integral of the difference of the shifted log products equals the
entropy difference plus a remainder. The lower endpoint may have zero eigenvalues. -/
theorem integral_log_shifted_product_sub_eq {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (htrace : (∑ i, a i) = ∑ i, b i)
    {R : ℝ} (hR : 0 < R) :
    (∫ s in (0 : ℝ)..R, Real.log (∏ i, (s + a i)) - Real.log (∏ i, (s + b i))) =
      -(∑ i, a i * Real.log (a i)) + (∑ i, b i * Real.log (b i)) +
        (∑ i, logShiftRemainder R (a i)) - ∑ i, logShiftRemainder R (b i) := by
  calc
    _ = ∫ s in (0 : ℝ)..R, (∑ i, Real.log (s + a i)) - ∑ i, Real.log (s + b i) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hR.le
      intro s hs
      dsimp only
      rw [log_shifted_product_eq_sum a ha hs.1, log_shifted_product_eq_sum b hb hs.1]
    _ = _ := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_sum_log_add a R)
        (intervalIntegrable_sum_log_add b R),
        integral_sum_log_add_eq a ha hR, integral_sum_log_add_eq b hb hR, htrace]
      ring

/-- Shifted product order implies entropy order for nonnegative spectra of equal trace.
The two spectra share a finite index type and may contain zeros. -/
theorem entropy_le_of_shifted_product_le {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (htrace : (∑ i, a i) = ∑ i, b i)
    (hprod : ∀ s : ℝ, 0 < s → (∏ i, (s + b i)) ≤ ∏ i, (s + a i)) :
    -(∑ i, b i * Real.log (b i)) ≤ -(∑ i, a i * Real.log (a i)) := by
  have hlog (s : ℝ) (hs : 0 < s) :
      Real.log (∏ i, (s + b i)) ≤ Real.log (∏ i, (s + a i)) := by
    have hpos : 0 < ∏ i, (s + b i) :=
      Finset.prod_pos (fun i _ => add_pos_of_pos_of_nonneg hs (hb i))
    exact Real.log_le_log hpos (hprod s hs)
  have hcutoff {R : ℝ} (hR : 0 < R) :
      (∑ i, a i * Real.log (a i)) - (∑ i, b i * Real.log (b i)) ≤
        (∑ i, logShiftRemainder R (a i)) - ∑ i, logShiftRemainder R (b i) := by
    have hnonneg :
        0 ≤ ∫ s in (0 : ℝ)..R, Real.log (∏ i, (s + a i)) - Real.log (∏ i, (s + b i)) := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hR.le
      rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := R))]
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := R))]
        with s hs
      exact sub_nonneg.mpr (hlog s hs.1)
    rw [integral_log_shifted_product_sub_eq ha hb htrace hR] at hnonneg
    linarith only [hnonneg]
  have hbound {R : ℝ} (hR : 0 < R) :
      (∑ i, a i * Real.log (a i)) - (∑ i, b i * Real.log (b i)) ≤ (∑ i, a i ^ 2) / R := by
    have hupper : (∑ i, logShiftRemainder R (a i)) ≤ (∑ i, a i ^ 2) / R := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ =>
        by simpa only [div_eq_mul_inv] using (logShiftRemainder_bounds hR (ha i)).2)
    have hlower : 0 ≤ ∑ i, logShiftRemainder R (b i) :=
      Finset.sum_nonneg (fun i _ => (logShiftRemainder_bounds hR (hb i)).1)
    exact (hcutoff hR).trans ((sub_le_self _ hlower).trans hupper)
  by_contra! h
  let d : ℝ := (∑ i, a i * Real.log (a i)) - (∑ i, b i * Real.log (b i))
  have hd : 0 < d := by
    dsimp [d]
    linarith only [h]
  obtain ⟨R, hR⟩ := exists_gt (max 0 ((∑ i, a i ^ 2) / d))
  have hRpos : 0 < R := (le_max_left _ _).trans_lt hR
  have hRlarge : (∑ i, a i ^ 2) / d < R := (le_max_right _ _).trans_lt hR
  have hlt : (∑ i, a i ^ 2) / R < d :=
    (div_lt_iff₀ hRpos).mpr (by simpa only [mul_comm R d] using (div_lt_iff₀ hd).mp hRlarge)
  exact (not_lt_of_ge (hbound hRpos)) hlt

private theorem det_shift_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (s : ℝ) :
    (s • (1 : Matrix ι ι ℝ) + A).det = ∏ i, (s + hA.eigenvalues i) := by
  have h := congrArg (Polynomial.eval (-s)) hA.charpoly_eq
  simp only [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    RCLike.ofReal_real_eq_id, id_eq] at h
  have hmatrix : (-s) • (1 : Matrix ι ι ℝ) - A = -(s • (1 : Matrix ι ι ℝ) + A) := by
    simp only [neg_smul, sub_eq_add_neg, neg_add_rev, add_comm]
  have hprod : (∏ i, (-s - hA.eigenvalues i)) = (∏ i, -(s + hA.eigenvalues i)) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  rw [hmatrix, Matrix.det_neg, hprod, Finset.prod_neg, Finset.card_univ] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

private theorem eigenvalues_nonneg_of_det_shift_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hdet : ∀ s : ℝ, 0 < s → 0 < (s • (1 : Matrix ι ι ℝ) + A).det) :
    ∀ i, 0 ≤ hA.eigenvalues i := by
  intro i
  by_contra! hi
  have h := hdet (-hA.eigenvalues i) (neg_pos.mpr hi)
  have hzero : (∏ j, (-hA.eigenvalues i + hA.eigenvalues j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (neg_add_cancel (hA.eigenvalues i))
  rw [det_shift_eq_prod hA, hzero] at h
  exact (lt_irrefl 0) h

private theorem eigenvalue_entropy_le_of_det_shift_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (htrace : A.trace = B.trace)
    (hBpos : ∀ s : ℝ, 0 < s → 0 < (s • (1 : Matrix ι ι ℝ) + B).det)
    (hdet : ∀ s : ℝ, 0 < s →
      (s • (1 : Matrix ι ι ℝ) + B).det ≤ (s • (1 : Matrix ι ι ℝ) + A).det) :
    -(∑ i, hB.eigenvalues i * Real.log (hB.eigenvalues i)) ≤
      -(∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i)) := by
  apply entropy_le_of_shifted_product_le
    (eigenvalues_nonneg_of_det_shift_pos hA (fun s hs => (hBpos s hs).trans_le (hdet s hs)))
    (eigenvalues_nonneg_of_det_shift_pos hB hBpos)
  · simpa only [hA.trace_eq_sum_eigenvalues, hB.trace_eq_sum_eigenvalues,
      RCLike.ofReal_real_eq_id, id_eq] using htrace
  · intro s hs
    rw [← det_shift_eq_prod hA, ← det_shift_eq_prod hB]
    exact hdet s hs

end

end D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
