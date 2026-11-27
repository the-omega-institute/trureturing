/- GID: D5/S3/Quantum/Divergence/GibbsCubicCorrectionBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/GibbsCubicCorrectionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A spectral interval bound on the cubic BKM correction by the weighted quadratic trace. -/

import D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.GibbsCubicCorrectionBound

open GibbsCubicTranslationEntropy (correction correction_spectral)
open D5.S3.Quantum.Recovery

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem logKernel_le {bmin bmax x y : ℝ} (hmin : 0 < bmin)
    (hx : x ∈ Set.Icc bmin bmax) (hy : y ∈ Set.Icc bmin bmax) :
    (x - y) * (Real.log x - Real.log y) ≤
      ((bmax - bmin) / (bmax + bmin) * Real.log (bmax / bmin)) * (x + y) := by
  have hmax : 0 < bmax := (hmin.trans_le hx.1).trans_le hx.2
  have hdiff (a b : ℝ) (ha : a ≤ bmax) (hb : bmin ≤ b) :
      a - b ≤ (bmax - bmin) / (bmax + bmin) * (a + b) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (add_pos hmax hmin)).mpr
    nlinarith only [mul_nonneg hmin.le (sub_nonneg.mpr ha),
      mul_nonneg hmax.le (sub_nonneg.mpr hb)]
  have habs : |x - y| ≤ (bmax - bmin) / (bmax + bmin) * (x + y) := by
    refine abs_le.mpr ⟨?_, hdiff x y hx.2 hy.1⟩
    have h := hdiff y x hy.2 hx.1
    rw [add_comm y x] at h
    linarith only [h]
  have hlog : |Real.log x - Real.log y| ≤ Real.log (bmax / bmin) := by
    rw [Real.log_div hmax.ne' hmin.ne']
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [Real.log_le_log hmin hx.1, Real.log_le_log (hmin.trans_le hy.1) hy.2]
    · linarith only [Real.log_le_log (hmin.trans_le hx.1) hx.2, Real.log_le_log hmin hy.1]
  calc
    _ ≤ |(x - y) * (Real.log x - Real.log y)| := le_abs_self _
    _ = |x - y| * |Real.log x - Real.log y| := abs_mul _ _
    _ ≤ ((bmax - bmin) / (bmax + bmin) * (x + y)) * Real.log (bmax / bmin) :=
      mul_le_mul habs hlog (abs_nonneg _) ((abs_nonneg _).trans habs)
    _ = _ := mul_right_comm _ _ _

/-- For every real translation parameter, the cubic BKM correction is bounded by
the weighted quadratic trace of the Hermitian perturbation. -/
theorem correction_le_weighted_trace (B U : Matrix n n ℂ) (hB : B.PosDef)
    (hU : U.IsHermitian) (t : ℝ) {bmin bmax : ℝ} (hmin : 0 < bmin)
    (hbounds : ∀ i, hB.isHermitian.eigenvalues i ∈ Set.Icc bmin bmax) :
    correction B (t • B + U) ≤
      ((bmax - bmin) / (bmax + bmin) * Real.log (bmax / bmin)) * (B * U ^ 2).trace.re := by
  let b := hB.isHermitian.eigenvalues
  let W := hB.isHermitian.eigenvectorUnitary
  let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W).symm
  let V := Q U
  let N (i j : n) := Complex.normSq (V i j)
  have hQB : Q B = diagonal (fun i => (b i : ℂ)) := by
    simpa only [Q, W, b, Unitary.conjStarAlgAut_symm, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal] using hB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hV : V.IsHermitian := hU.isSelfAdjoint.map Q
  have htrace : (B * U ^ 2).trace.re = ∑ i, ∑ j, b i * N i j := by
    rw [← BKMSpectralVariance.trace_conjStarAlgAut_symm W (B * U ^ 2)]
    change (Q (B * U ^ 2)).trace.re = _
    rw [map_mul, map_pow, hQB, pow_two]
    change (diagonal (fun i => (b i : ℂ)) * (V * V)).trace.re = _
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum]
    simp only [Matrix.mul_apply, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hV.apply j i, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hswap : (∑ i, ∑ j, b j * N i j) = ∑ i, ∑ j, b i * N i j := by
    calc
      _ = ∑ i, ∑ j, b j * N j i := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        have hnorm : N i j = N j i := by
          change Complex.normSq (V i j) = Complex.normSq (V j i)
          rw [← hV.apply i j, Complex.star_def, Complex.normSq_conj]
        rw [hnorm]
      _ = _ := Finset.sum_comm
  have hweighted : (B * U ^ 2).trace.re = (1 / 2 : ℝ) * ∑ i, ∑ j, (b i + b j) * N i j := by
    simp only [htrace, add_mul, Finset.sum_add_distrib, hswap]
    ring
  have hM : (t • B + U).IsHermitian := (hB.isHermitian.smul (star_trivial t)).add hU
  have hoff (i j : n) (hij : i ≠ j) : Q (t • B + U) i j = V i j := by
    have hsmul : Q (t • B) = t • Q B := Q.toAlgEquiv.toAlgHom.map_smul_of_tower t B
    rw [map_add, hsmul, hQB]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij,
      smul_zero, zero_add, V]
  have hspectral : correction B (t • B + U) = (1 / 2 : ℝ) * ∑ i, ∑ j,
      (b i - b j) * (Real.log (b i) - Real.log (b j)) *
        Complex.normSq (Q (t • B + U) i j) :=
    correction_spectral B (t • B + U) hB.isHermitian hM
  let K := (bmax - bmin) / (bmax + bmin) * Real.log (bmax / bmin)
  change correction B (t • B + U) ≤ K * (B * U ^ 2).trace.re
  calc
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) * N i j := by
      rw [hspectral]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases hij : i = j
      · simp only [hij, sub_self, zero_mul]
      · rw [hoff i j hij]
    _ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, (K * (b i + b j)) * N i j := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_right (logKernel_le hmin (hbounds i) (hbounds j))
        (Complex.normSq_nonneg _)
    _ = _ := by
      rw [hweighted, mul_left_comm K (1 / 2 : ℝ)]
      simp only [Finset.mul_sum, mul_assoc]

#print axioms correction_le_weighted_trace

end D5.S3.Quantum.Divergence.GibbsCubicCorrectionBound
