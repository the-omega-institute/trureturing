/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All complex derivatives of the full Mangoldt transform are the absolutely convergent signed logarithmic moments on the original half-plane. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

private def kernel (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (U (Real.exp u) : ℂ))

private theorem kernel_continuous (k : ℕ) (s : ℂ) : Continuous (kernel k s) := by
  unfold kernel
  have h := Complex.continuous_ofReal.comp U_exp_continuous
  exact (Complex.continuous_ofReal.neg.pow k).mul
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul h)

private theorem kernel_norm (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel k s u‖ = u ^ k * (Real.exp (-s.re * u) * |U (Real.exp u)|) := by
  simp [kernel, norm_pow, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]

private theorem kernel_bound (k : ℕ) {a d : ℝ} (hd : 0 < d) {s : ℂ} (hs : a + d ≤ s.re)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel k s u‖ ≤ (k.factorial : ℝ) / d ^ k * ‖kernel 0 a u‖ := by
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  have hf : 0 < (k.factorial : ℝ) := by positivity
  have hdk : 0 < d ^ k := pow_pos hd _
  rw [mul_pow, div_le_iff₀ hf] at hp
  have huPow : u ^ k ≤ (k.factorial : ℝ) / d ^ k * Real.exp (d * u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
    simpa [mul_comm] using hp
  rw [kernel_norm k s hu, kernel_norm 0 a hu]
  simp only [Complex.ofReal_re, pow_zero, one_mul]
  calc
    _ ≤ ((k.factorial : ℝ) / d ^ k * Real.exp (d * u)) *
        (Real.exp (-s.re * u) * |U (Real.exp u)|) :=
      mul_le_mul_of_nonneg_right huPow (by positivity)
    _ = ((k.factorial : ℝ) / d ^ k * Real.exp ((d - s.re) * u)) * |U (Real.exp u)| := by
      rw [show (d - s.re) * u = d * u + (-s.re) * u by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      gcongr
      linarith

private theorem base_integrable {a : ℝ} (ha : 1 < a) :
    IntegrableOn (kernel 0 (a : ℂ)) (Ioi 0) := by
  unfold kernel
  simpa using (CompleteMangoldtHalfPlane.u_laplace_half_plane (s := (a : ℂ)) ha).1

private theorem kernel_integrable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (kernel k s) (Ioi 0) := by
  let d := (s.re - 1) / 3
  let a := 1 + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : 1 < a := by dsimp [a]; linarith
  have h : IntegrableOn (fun u => (k.factorial : ℝ) / d ^ k * ‖kernel 0 a u‖) (Ioi 0) :=
    (base_integrable ha).norm.const_mul _
  refine h.mono' (kernel_continuous k s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  exact kernel_bound k hd (by dsimp [a,d]; linarith) (le_of_lt hu)

private theorem kernel_derivative (k : ℕ) (s : ℂ) (u : ℝ) :
    HasDerivAt (fun z => kernel k z u) (kernel (k+1) s u) s := by
  unfold kernel
  have h := (((hasDerivAt_id s).neg.mul_const (u : ℂ)).cexp.mul_const (U (Real.exp u) : ℂ)).const_mul ((-(u : ℂ)) ^ k)
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq, neg_one_mul, pow_succ]
  ring

private theorem integral_derivative (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z => ∫ u : ℝ in Ioi 0, kernel k z u)
      (∫ u : ℝ in Ioi 0, kernel (k+1) s u) s := by
  let d := (s.re - 1) / 3
  let a := 1 + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : 1 < a := by dsimp [a]; linarith
  have hn : {z : ℂ | a + d < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [a,d]; linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) hn
    (Eventually.of_forall fun z => (kernel_continuous k z).aestronglyMeasurable)
    (kernel_integrable k hs) (kernel_continuous (k+1) s).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu z hz
      exact kernel_bound (k+1) hd (le_of_lt hz) (le_of_lt hu))
    ((base_integrable ha).norm.const_mul ((k+1).factorial / d ^ (k+1) : ℝ))
    (Eventually.of_forall fun u z _ => kernel_derivative k z u)).2

/-- Every complex derivative is an absolutely convergent signed logarithmic
moment of the complete Mangoldt remainder on the full initial half-plane. -/
theorem iterated_derivative_moment (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (U (Real.exp u) : ℂ))) (Ioi 0) ∧
    iteratedDeriv k CompleteMangoldtLaurent.transform s =
      ∫ u : ℝ in Ioi 0, (-(u : ℂ)) ^ k *
        (Complex.exp (-s * u) * (U (Real.exp u) : ℂ)) := by
  refine ⟨kernel_integrable k hs, ?_⟩
  change iteratedDeriv k CompleteMangoldtLaurent.transform s = ∫ u : ℝ in Ioi 0, kernel k s u
  induction k generalizing s with
  | zero =>
    simpa [kernel, CompleteMangoldtLaurent.transform] using
      (CompleteMangoldtHalfPlane.u_laplace_half_plane hs).2.symm
  | succ k ih =>
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have heq : iteratedDeriv k CompleteMangoldtLaurent.transform =ᶠ[𝓝 s]
        (fun z => ∫ u : ℝ in Ioi 0, kernel k z u) := by
      filter_upwards [hopen] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq, (integral_derivative k hs).deriv]

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments
