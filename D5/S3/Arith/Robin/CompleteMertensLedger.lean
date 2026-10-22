/- GID: D5/S3/Arith/Robin/CompleteMertensLedger
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/CompleteMertensLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An integrable Chebyshev tail and Lay's identity give the complete weighted Mertens ledger. -/

import D5.S3.Weil.Mertens.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open scoped BigOperators
open Finset Real Set MeasureTheory

namespace D5.S3.Arith.Robin.CompleteMertensLedger

/-- The complete Chebyshev error kernel. -/
def psiErrorKernel (u : ℝ) : ℝ := (Chebyshev.psi u - u) / u ^ 2

/-- The unweighted complete Chebyshev tail. -/
def Q (t : ℝ) : ℝ := ∫ u in Ioi t, psiErrorKernel u

/-- The positive logarithmic weight. -/
def r (t : ℝ) : ℝ := (1 + log t) / (log t) ^ 2

/-- The weighted complete Chebyshev tail. -/
def I (t : ℝ) : ℝ := ∫ u in Ioi t, psiErrorKernel u * r u

/-- The finite complete Mangoldt cumulative error. -/
def U (t : ℝ) : ℝ :=
  t * (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
    Chebyshev.psi t - t * log t + (1 + eulerMascheroniConstant) * t

private lemma jy_majorant_integrable {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun u : ℝ =>
      (939 / 100) * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)) / u) (Ioi t) := by
  let g : ℝ → ℝ := fun v => (939 / 100) * v ^ (303 / 200 : ℝ) *
    exp (-(4137 / 5000) * sqrt v)
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < log t := log_pos (by linarith)
  have hg : IntegrableOn g (Ioi (log t)) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (303 / 200 : ℝ)) (p := (1 / 2 : ℝ)) (b := (4137 / 5000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)).const_mul (939 / 100 : ℝ)
    have hm := h.mono_set (Ioi_subset_Ioi hlogt.le)
    simpa only [g, sqrt_eq_rpow, mul_assoc] using hm
  have hmajor : IntegrableOn (fun u : ℝ => u⁻¹ * g (log u)) (Ioi t) := by
    simpa only [smul_eq_mul] using (integrableOn_comp_log_Ioi g ht0).mpr hg
  convert hmajor using 1
  ext u
  dsimp [g]
  ring

private lemma kernel_integrable
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)))
    {t : ℝ} (ht : 2 ≤ t) : IntegrableOn psiErrorKernel (Ioi t) := by
  apply (jy_majorant_integrable ht).mono'
    ((Chebyshev.psi_mono.measurable.sub measurable_id).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu2 : 2 ≤ u := ht.trans hu.le
  have hu0 : 0 < u := by linarith
  rw [Real.norm_eq_abs, psiErrorKernel, abs_div, abs_of_nonneg (sq_nonneg u)]
  calc
    |Chebyshev.psi u - u| / u ^ 2 ≤
        ((939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
          exp (-(4137 / 5000) * sqrt (log u))) / u ^ 2 :=
      div_le_div_of_nonneg_right (hJY u hu2) (sq_nonneg u)
    _ = (939 / 100) * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)) / u := by
      field_simp [hu0.ne']
      ring

private lemma inv_log_pow_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) (k : ℕ) :
    IntegrableOn (fun u => psiErrorKernel u / (log u) ^ k) (Ioi t) := by
  have hl : 0 < log t := log_pos (by linarith)
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioi t),
      ‖1 / (log u) ^ k‖ ≤ 1 / (log t) ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hlu : log t ≤ log u := log_le_log (by linarith) hu.le
    have hlu0 : 0 < log u := hl.trans_le hlu
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (log u) ^ k)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hlu k)
  simpa only [div_eq_mul_inv, one_mul] using
    hf.mul_bdd (g := fun u => 1 / (log u) ^ k) (by fun_prop) hbound

private lemma weighted_kernel_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi t) := by
  apply ((inv_log_pow_integrable ht hf 2).add
    (by simpa using inv_log_pow_integrable ht hf 1)).congr_fun _ measurableSet_Ioi
  intro u hu
  have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
  dsimp [r]
  field_simp [hlu]
  ring

private def triangle (s u : ℝ) : ℝ :=
  {p : ℝ × ℝ | p.1 < p.2}.indicator
    (fun p => (1 / (p.1 * log p.1 ^ 2)) * psiErrorKernel p.2) (s, u)

private lemma triangle_integrable {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    Integrable (Function.uncurry triangle)
      ((volume.restrict (Ioi t)).prod (volume.restrict (Ioi t))) := by
  exact ((Mertens.integrable_const_div_mul_log_sq (1 : ℝ) ht).mul_prod hf).indicator
    (measurableSet_lt measurable_fst measurable_snd)

private lemma triangle_right {t s : ℝ} (hs : t < s) :
    (∫ u in Ioi t, triangle s u) = Q s / (s * log s ^ 2) := by
  have heq : (fun u => triangle s u) =
      (Ioi s).indicator (fun u => (1 / (s * log s ^ 2)) * psiErrorKernel u) := by
    ext u
    simp only [triangle, indicator_apply, mem_setOf_eq, mem_Ioi]
  rw [heq, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hs.le), integral_const_mul]
  dsimp [Q]
  ring

private lemma triangle_left {t u : ℝ} (ht : 2 ≤ t) (hu : t < u) :
    (∫ s in Ioi t, triangle s u) =
      psiErrorKernel u * (1 / log t - 1 / log u) := by
  have heq : (fun s => triangle s u) =
      (Iio u).indicator (fun s => (1 / (s * log s ^ 2)) * psiErrorKernel u) := by
    ext s
    simp only [triangle, indicator_apply, mem_setOf_eq, mem_Iio]
  rw [heq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio,
    integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hu.le]
  have hdiff := intervalIntegral.integral_Ioi_sub_Ioi
    (Mertens.integrable_const_div_mul_log_sq (1 : ℝ) ht) hu.le
  rw [Mertens.integ_div_mul_log_sq 1 ht,
    Mertens.integ_div_mul_log_sq 1 (ht.trans hu.le)] at hdiff
  rw [← hdiff]
  ring

private lemma tail_log_integral {t : ℝ} (ht : 2 ≤ t)
    (hf : IntegrableOn psiErrorKernel (Ioi t)) :
    IntegrableOn (fun s => Q s / (s * log s ^ 2)) (Ioi t) ∧
      (∫ s in Ioi t, Q s / (s * log s ^ 2)) =
        Q t / log t - ∫ u in Ioi t, psiErrorKernel u / log u := by
  have htri := triangle_integrable ht hf
  have hint : IntegrableOn (fun s => Q s / (s * log s ^ 2)) (Ioi t) := by
    apply htri.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact triangle_right hs
  refine ⟨hint, ?_⟩
  have hswap := integral_integral_swap htri
  have hfirst : (∫ s in Ioi t, ∫ u in Ioi t, triangle s u) =
      ∫ s in Ioi t, Q s / (s * log s ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact triangle_right hs
  have hsecond : (∫ u in Ioi t, ∫ s in Ioi t, triangle s u) =
      ∫ u in Ioi t, psiErrorKernel u * (1 / log t - 1 / log u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact triangle_left ht hu
  rw [hfirst, hsecond] at hswap
  rw [hswap]
  have hlog := inv_log_pow_integrable ht hf 1
  simp only [pow_one] at hlog
  have heq : (fun u => psiErrorKernel u * (1 / log t - 1 / log u)) =
      (fun u => psiErrorKernel u / log t - psiErrorKernel u / log u) := by
    ext u; ring
  rw [heq, integral_sub (hf.div_const _) hlog, integral_div_const]
  rfl

/-- Johnston--Yang decay and Lay's complete identity give the weighted Mertens ledger. -/
theorem complete_mertens_ledger
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (log u) ^ (303 / 200 : ℝ) *
        exp (-(4137 / 5000) * sqrt (log u)))
    (hLay : ∀ t : ℝ, 2 ≤ t → Q t = Chebyshev.psi t / t -
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
        log t - 1 - eulerMascheroniConstant)
    {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn psiErrorKernel (Ioi t) ∧
      IntegrableOn (fun u => psiErrorKernel u * r u) (Ioi t) ∧
        Mertens.E₂Λ t = (Chebyshev.psi t - t) / (t * log t) - I t := by
  have hf := kernel_integrable hJY ht
  refine ⟨hf, weighted_kernel_integrable ht hf, ?_⟩
  have hlog2 := inv_log_pow_integrable ht hf 2
  obtain ⟨hQint, hQ⟩ := tail_log_integral ht hf
  have hE (u : ℝ) (hu : 2 ≤ u) :
      Mertens.E₁Λ u = (Chebyshev.psi u - u) / u -
        eulerMascheroniConstant - Q u := by
    have hu0 : u ≠ 0 := ne_of_gt (by linarith)
    have h := hLay u hu
    dsimp [Mertens.E₁Λ]
    field_simp [hu0] at h ⊢
    linarith
  have hintegrand : ∀ u ∈ Ioi t,
      Mertens.E₁Λ u / (u * log u ^ 2) =
        psiErrorKernel u / log u ^ 2 -
          eulerMascheroniConstant / (u * log u ^ 2) - Q u / (u * log u ^ 2) := by
    intro u hu
    rw [hE u (ht.trans hu.le)]
    dsimp [psiErrorKernel]
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu])
    have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
    field_simp [hu0, hlu]
    ring
  have hEi : (∫ u in Ioi t, Mertens.E₁Λ u / (u * log u ^ 2)) =
      (∫ u in Ioi t, psiErrorKernel u / log u ^ 2) -
        eulerMascheroniConstant / log t -
          (Q t / log t - ∫ u in Ioi t, psiErrorKernel u / log u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hintegrand,
      integral_sub (hlog2.sub (Mertens.integrable_const_div_mul_log_sq _ ht)) hQint,
      integral_sub hlog2 (Mertens.integrable_const_div_mul_log_sq _ ht),
      Mertens.integ_div_mul_log_sq _ ht, hQ]
  have hI : I t = (∫ u in Ioi t, psiErrorKernel u / log u ^ 2) +
      ∫ u in Ioi t, psiErrorKernel u / log u := by
    dsimp [I]
    rw [← integral_add hlog2 (by simpa using inv_log_pow_integrable ht hf 1)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [r]
    have hlu : log u ≠ 0 := ne_of_gt (log_pos (by linarith [hu] : 1 < u))
    field_simp [hlu]
    ring
  rw [Mertens.E₂Λ.eq ht, hEi, hE t ht, hI]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : log t ≠ 0 := ne_of_gt (log_pos (by linarith : 1 < t))
  field_simp [ht0, hlt]
  ring

end D5.S3.Arith.Robin.CompleteMertensLedger
