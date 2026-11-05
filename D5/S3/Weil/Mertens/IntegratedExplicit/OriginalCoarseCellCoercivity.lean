/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily strong finite-cell coercivity for the complete original positive kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The finite-cell condition concerns literal complex integrals of the inclusive
atomic prefix. No completed detail space or hat-function equivalence is used.
The candidate analytic inference is uniform low-band suppression by finite-cell
cancellation, consumed by the original full-kernel endpoint.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open OriginalActualFourier

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

private lemma phase_sub_bound (w u v : ℝ) :
    ‖phase w u - phase w v‖ ≤ |w| * |u - v| := by
  have he : phase w u - phase w v = phase w v * (phase w (u-v) - 1) := by
    rw [mul_sub, mul_one, ← phase_add]
    congr 1 <;> ring
  rw [he, norm_mul, phase_norm, one_mul]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one_le (x := w * (u-v))
  have he' : phase w (u-v) = Complex.exp (Complex.I * ((w * (u-v) : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  simpa only [he', Real.norm_eq_abs, abs_mul] using h

private lemma cell_transform_bound (A : ℝ → ℂ) (hA : Integrable A)
    (l r w : ℝ) (hlr : l ≤ r) (hz : (∫ u in l..r, A u) = 0) :
    ‖∫ u in l..r, A u * phase (-w) u‖ ≤
      (|w| * (r-l)) * ∫ u in l..r, ‖A u‖ := by
  have he : (∫ u in l..r, A u * phase (-w) u) =
      ∫ u in l..r, A u * (phase (-w) u - phase (-w) l) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub
      ((transform_integrable hA w).intervalIntegrable)
      ((hA.mul_const _).intervalIntegrable), intervalIntegral.integral_mul_const, hz]
    simp
  rw [he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le hlr
    ((hA.norm.const_mul _).intervalIntegrable)
  intro u hu
  have hu' : l ≤ u ∧ u ≤ r := ⟨hu.1.le, hu.2⟩
  have hp : ‖phase (-w) u - phase (-w) l‖ ≤ |w| * (r-l) := by
    calc
      _ ≤ |-w| * |u-l| := phase_sub_bound (-w) u l
      _ ≤ |w| * (r-l) := by
        rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hu'.1)]
        gcongr
        linarith [hu'.2]
  rw [norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (A u))]

private lemma cell_fourier_bound (A : ℝ → ℂ) (hA : Integrable A)
    (D h : ℝ) (n : ℕ) (hn : 0 < n) (hh : 0 < h) (hend : (n : ℝ)*h = D)
    (hs : ∀ u, u ∉ Icc 0 D → A u = 0)
    (hz : ∀ k < n, (∫ u in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, A u) = 0)
    (w : ℝ) : ‖Ahat A w‖ ≤ (|w|*h) * ∫ u, ‖A u‖ := by
  have hD : 0 ≤ D := by rw [← hend]; positivity
  have window (f : ℝ → ℂ) (hf : ∀ u, u ∉ Icc 0 D → f u = 0) :
      (∫ u, f u) = ∫ u in (0:ℝ)..D, f u := by
    rw [intervalIntegral.integral_of_le hD, ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
  have hwindow : Ahat A w = ∫ u in (0:ℝ)..D, A u * phase (-w) u :=
    window _ (fun u hu => by rw [hs u hu, zero_mul])
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k:ℝ)*h) (n := n)
    (fun k _ => (transform_integrable hA w).intervalIntegrable)
  have hnrm := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u => ‖A u‖) (a := fun k : ℕ => (k:ℝ)*h) (n := n)
    (fun k _ => hA.norm.intervalIntegrable)
  simp only [Nat.cast_zero, zero_mul, hend] at hsum hnrm
  rw [hwindow, ← hsum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖∫ u in (k:ℝ)*h..((k+1:ℕ):ℝ)*h,
        A u * phase (-w) u‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (|w|*h) *
        ∫ u in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, ‖A u‖ := by
      apply Finset.sum_le_sum
      intro k hk
      have he : ((k+1:ℕ):ℝ)*h - (k:ℝ)*h = h := by push_cast; ring
      simpa only [he] using cell_transform_bound A hA ((k:ℝ)*h) (((k+1:ℕ):ℝ)*h)
        w (by push_cast; nlinarith) (hz k (Finset.mem_range.mp hk))
    _ = (|w|*h) * ∫ u, ‖A u‖ := by
      rw [← Finset.mul_sum, hnrm, intervalIntegral.integral_of_le hD,
        ← integral_Icc_eq_integral_Ioc,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro u hu
      simp [hs u hu]

private lemma window_l1_sq (A : ℝ → ℂ) (hA : Integrable A)
    (hA2 : MemLp A 2) (D : ℝ) (hD : 0 < D)
    (hs : ∀ u, u ∉ Icc 0 D → A u = 0) :
    (∫ u, ‖A u‖)^2 ≤ D * ∫ u, ‖A u‖^2 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 D)
  have he1 : (∫ u, ‖A u‖ ∂μ) = ∫ u, ‖A u‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hs u hu])
  have he2 : (∫ u, ‖A u‖^2 ∂μ) = ∫ u, ‖A u‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hs u hu])
  have hv : μ.real univ = D := by simp [μ, Real.volume_Icc, hD.le]
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (by norm_num : (2:ℝ).HolderConjugate 2)
    (f := fun u => ‖A u‖) (g := fun _ : ℝ => (1:ℝ))
    (by simpa using hA2.norm.restrict (s := Icc 0 D))
    (by simpa using (memLp_const (1:ℝ) : MemLp (fun _ : ℝ => (1:ℝ)) 2 μ))
  simp only [Real.norm_eq_abs, abs_norm, norm_one, mul_one,
    Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    ← Real.sqrt_eq_rpow, he1, he2, hv] at h
  have hE : 0 ≤ ∫ u, ‖A u‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hL : 0 ≤ ∫ u, ‖A u‖ := integral_nonneg (fun _ => norm_nonneg _)
  have he := mul_self_le_mul_self hL h
  simpa only [← pow_two, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hD.le, mul_comm] using he

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
