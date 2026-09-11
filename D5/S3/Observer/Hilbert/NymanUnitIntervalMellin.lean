/- GID: D5/S3/Observer/Hilbert/NymanUnitIntervalMellin
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/NymanUnitIntervalMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual unit-interval Mellin functional gives the constrained Nyman zero obstruction. -/

import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import D5.S3.Weil.ZetaCore.Statement
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace BigOperators

namespace D5.S3.Observer.Hilbert.NymanUnitIntervalMellin

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
abbrev Carrier := Lp ℂ 2 unitMeasure

instance : IsFiniteMeasure unitMeasure := by
  constructor
  simp [Real.volume_Ioo]

def unitTarget : Carrier := (memLp_const (1 : ℂ)).toLp (fun _ : ℝ => (1 : ℂ))

theorem unitTarget_coe_ae : (unitTarget : ℝ → ℂ) =ᵐ[unitMeasure] fun _ => 1 :=
  MemLp.coeFn_toLp _

theorem source_memLp (theta : ℝ) :
    MemLp (fun x : ℝ => ((Int.fract (theta / x) : ℝ) : ℂ)) 2 unitMeasure := by
  have hm : AEStronglyMeasurable
      (fun x : ℝ => ((Int.fract (theta / x) : ℝ) : ℂ)) unitMeasure :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.div measurable_id).fract).aestronglyMeasurable
  apply MemLp.of_bound hm 1
  filter_upwards with x
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg (theta / x))]
    using (Int.fract_lt_one (theta / x)).le

def source (theta : ℝ) : Carrier :=
  (source_memLp theta).toLp (fun x : ℝ => ((Int.fract (theta / x) : ℝ) : ℂ))

theorem source_coe_ae (theta : ℝ) :
    (source theta : ℝ → ℂ) =ᵐ[unitMeasure] fun x => ((Int.fract (theta / x) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- Arbitrary finite complex synthesis, with the literal Nyman coefficient constraint. -/
def B0 : Set Carrier := {f | ∃ (n : ℕ) (u : Fin n → ℂ) (theta : Fin n → ℝ),
  (∀ j, 0 < theta j ∧ theta j ≤ 1) ∧
  (∑ j, u j * (theta j : ℂ)) = 0 ∧ f = ∑ j, u j • source (theta j)}

theorem finite_sum_coe_ae (n : ℕ) (u : Fin n → ℂ) (theta : Fin n → ℝ) :
    ((∑ j, u j • source (theta j) : Carrier) : ℝ → ℂ) =ᵐ[unitMeasure]
      fun x => ∑ j, u j * ((Int.fract (theta j / x) : ℝ) : ℂ) := by
  have hs : ∀ j, (u j • source (theta j) : Carrier) =ᵐ[unitMeasure]
      fun x => u j * ((Int.fract (theta j / x) : ℝ) : ℂ) := by
    intro j
    filter_upwards [Lp.coeFn_smul (u j) (source (theta j)), source_coe_ae (theta j)]
      with x hsm hsrc
    simpa only [Pi.smul_apply, smul_eq_mul, hsrc] using hsm
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => u j • source (theta j)),
    Filter.eventually_all.mpr hs] with x hsum hx
  simpa only [Finset.sum_apply, hx] using hsum

theorem zero_mem_B0 : (0 : Carrier) ∈ B0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · exact fun j => Fin.elim0 j
  · simp
  · simp

theorem closure_B0_nonempty : (closure B0).Nonempty :=
  ⟨0, subset_closure zero_mem_B0⟩

def kernelFn (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (starRingEnd ℂ s - 1)

private theorem kernel_norm_sq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖kernelFn s x‖ ^ 2 = x ^ (2 * s.re - 2) := by
  rw [kernelFn, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.conj_re, Complex.one_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  norm_num
  ring

theorem kernel_memLp (s : ℂ) (hs : 1 / 2 < s.re) : MemLp (kernelFn s) 2 unitMeasure := by
  have hm : AEStronglyMeasurable (kernelFn s) unitMeasure := by
    apply Integrable.aestronglyMeasurable
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    exact intervalIntegral.intervalIntegrable_cpow' (by
      simp only [Complex.sub_re, Complex.conj_re, Complex.one_re]
      linarith)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : IntegrableOn (fun x : ℝ => x ^ (2 * s.re - 2)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (kernel_norm_sq s hx.1).symm

def kernel (s : ℂ) (hs : 1 / 2 < s.re) : Carrier :=
  (kernel_memLp s hs).toLp (kernelFn s)

theorem kernel_coe_ae (s : ℂ) (hs : 1 / 2 < s.re) :
    (kernel s hs : ℝ → ℂ) =ᵐ[unitMeasure] kernelFn s := MemLp.coeFn_toLp _

private theorem kernel_conj (s : ℂ) {x : ℝ} (hx : 0 < x) :
    starRingEnd ℂ (kernelFn s x) = (x : ℂ) ^ (s - 1) := by
  have ha : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  simpa [kernelFn, map_sub] using (Complex.conj_cpow (x : ℂ) (s - 1) ha).symm

def mellinFunctional (s : ℂ) (hs : 1 / 2 < s.re) : Carrier →L[ℂ] ℂ :=
  innerSL ℂ (kernel s hs)

private theorem pairing_ae (s : ℂ) (hs : 1 / 2 < s.re) (f : Carrier) :
    (fun x => inner ℂ (kernel s hs x) (f x)) =ᵐ[unitMeasure]
      fun x => f x * (x : ℂ) ^ (s - 1) := by
  filter_upwards [kernel_coe_ae s hs, ae_restrict_mem measurableSet_Ioo] with x hk hx
  rw [hk, RCLike.inner_apply]
  change f x * starRingEnd ℂ (kernelFn s x) = _
  rw [kernel_conj s hx.1]

theorem pairing_integrable (s : ℂ) (hs : 1 / 2 < s.re) (f : Carrier) :
    Integrable (fun x => f x * (x : ℂ) ^ (s - 1)) unitMeasure :=
  (L2.integrable_inner (𝕜 := ℂ) (kernel s hs) f).congr (pairing_ae s hs f)

theorem pairing_integrable_representative (s : ℂ) (hs : 1 / 2 < s.re)
    (f : Carrier) (g : ℝ → ℂ) (hg : (f : ℝ → ℂ) =ᵐ[unitMeasure] g) :
    Integrable (fun x => g x * (x : ℂ) ^ (s - 1)) unitMeasure :=
  (pairing_integrable s hs f).congr (hg.mul EventuallyEq.rfl)

theorem mellinFunctional_apply (s : ℂ) (hs : 1 / 2 < s.re) (f : Carrier) :
    mellinFunctional s hs f = ∫ x in Ioo (0 : ℝ) 1, f x * (x : ℂ) ^ (s - 1) := by
  rw [mellinFunctional, innerSL_apply_apply, L2.inner_def]
  exact integral_congr_ae (pairing_ae s hs f)

theorem mellinFunctional_apply_representative (s : ℂ) (hs : 1 / 2 < s.re)
    (f : Carrier) (g : ℝ → ℂ) (hg : (f : ℝ → ℂ) =ᵐ[unitMeasure] g) :
    mellinFunctional s hs f = ∫ x in Ioo (0 : ℝ) 1, g x * (x : ℂ) ^ (s - 1) := by
  rw [mellinFunctional_apply]
  exact integral_congr_ae (hg.mul (EventuallyEq.rfl))

theorem kernel_norm_sq_exact (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖kernel s hs‖ ^ 2 = 1 / (2 * s.re - 1) := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (kernel s hs) (kernel s hs))]
  have he : (fun x => RCLike.re (inner ℂ (kernel s hs x) (kernel s hs x))) =ᵐ[unitMeasure]
      fun x : ℝ => x ^ (2 * s.re - 2) := by
    filter_upwards [kernel_coe_ae s hs, ae_restrict_mem measurableSet_Ioo] with x hk hx
    rw [← @norm_sq_eq_re_inner ℂ, hk, kernel_norm_sq s hx.1]
  rw [integral_congr_ae he, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith : -1 < 2 * s.re - 2))]
  rw [show 2 * s.re - 2 + 1 = 2 * s.re - 1 by ring,
    Real.zero_rpow (by linarith : 2 * s.re - 1 ≠ 0), Real.one_rpow]
  ring

/- The scalar integral calculation above directly applies Mathlib.integral_rpow,
the same eligible dependency slice used by l2_norm_sq_power in jrgochan/prime,
ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2,
proofs/Cathedral/MellinBridge/HilbertSetup.lean:57-64.
No archived separation theorem or custom orthogonality axiom is imported. -/

theorem mellinFunctional_norm_sq (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖mellinFunctional s hs‖ ^ 2 = 1 / (2 * s.re - 1) := by
  rw [mellinFunctional, innerSL_apply_norm, kernel_norm_sq_exact]

theorem mellinFunctional_norm (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖mellinFunctional s hs‖ = 1 / Real.sqrt (2 * s.re - 1) := by
  have hn := mellinFunctional_norm_sq s hs
  have hpos : 0 < 2 * s.re - 1 := by linarith
  have he : (1 / Real.sqrt (2 * s.re - 1)) ^ 2 = 1 / (2 * s.re - 1) := by
    rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
  nlinarith [norm_nonneg (mellinFunctional s hs),
    div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (Real.sqrt_nonneg (2 * s.re - 1))]

theorem mellinFunctional_unitTarget (s : ℂ) (hs : 1 / 2 < s.re) :
    mellinFunctional s hs unitTarget = 1 / s := by
  rw [mellinFunctional_apply_representative s hs unitTarget _ unitTarget_coe_ae]
  simp only [one_mul]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))]
  simp only [sub_add_cancel, Complex.ofReal_one, Complex.ofReal_zero]
  rw [Complex.one_cpow, Complex.zero_cpow (by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith)]
  simp

theorem mellinFunctional_source (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re < 1) :
    mellinFunctional s hs (source theta) =
      (theta : ℂ) / (s - 1) - (theta : ℂ) ^ s * riemannZeta s / s := by
  rw [mellinFunctional_apply_representative s hs (source theta) _ (source_coe_ae theta)]
  exact D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin.fractionalMellin_eq_zeta
    theta htheta htheta1 s (by linarith) hs1

theorem mellinFunctional_B0 (rho : ℂ) (hrho : 1 / 2 < rho.re) (hrho1 : rho.re < 1)
    (hzeta : riemannZeta rho = 0) (f : Carrier) (hf : f ∈ B0) :
    mellinFunctional rho hrho f = 0 := by
  obtain ⟨n, u, theta, htheta, hsum, rfl⟩ := hf
  rw [map_sum]
  simp_rw [map_smul, mellinFunctional_source _ (htheta _).1 (htheta _).2 rho hrho hrho1,
    hzeta, mul_zero, zero_div, sub_zero, smul_eq_mul, ← mul_div_assoc]
  rw [← Finset.sum_div, hsum, zero_div]

theorem mellinFunctional_closure_B0 (rho : ℂ) (hrho : 1 / 2 < rho.re)
    (hrho1 : rho.re < 1) (hzeta : riemannZeta rho = 0) (f : Carrier)
    (hf : f ∈ closure B0) : mellinFunctional rho hrho f = 0 := by
  have hsub : B0 ⊆ (mellinFunctional rho hrho).ker := by
    intro g hg
    exact mellinFunctional_B0 rho hrho hrho1 hzeta g hg
  exact (closure_minimal hsub (mellinFunctional rho hrho).isClosed_ker) hf

theorem nyman_unitInterval_zero_obstruction_of_strip (rho : ℂ) (hrho : 1 / 2 < rho.re)
    (hrho1 : rho.re < 1) (hzeta : riemannZeta rho = 0) :
    Real.sqrt (2 * rho.re - 1) / ‖rho‖ ≤ Metric.infDist unitTarget (closure B0) := by
  have hrho0 : rho ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  have hn : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hp : 0 < Real.sqrt (2 * rho.re - 1) := Real.sqrt_pos.mpr (by linarith)
  apply (Metric.le_infDist closure_B0_nonempty).mpr
  intro f hf
  have hb := (mellinFunctional rho hrho).le_opNorm (unitTarget - f)
  rw [map_sub, mellinFunctional_unitTarget,
    mellinFunctional_closure_B0 rho hrho hrho1 hzeta f hf, sub_zero,
    norm_div, norm_one, mellinFunctional_norm, ← dist_eq_norm] at hb
  apply (div_le_iff₀ hn).mpr
  have hh := (le_div_iff₀ hp).mp (by simpa only [one_div_mul_eq_div] using hb)
  calc
    _ = (1 / ‖rho‖ * Real.sqrt (2 * rho.re - 1)) * ‖rho‖ := by field_simp
    _ ≤ dist unitTarget f * ‖rho‖ := mul_le_mul_of_nonneg_right hh hn.le

/-- The original endpoint is conditional on an actual canonical nontrivial zero. -/
theorem nontrivial_zero_domain (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho) :
    rho.re < 1 ∧ rho ≠ 0 ∧ rho ≠ 1 ∧ 0 < ‖rho‖ := by
  have h0 : rho ≠ 0 := by intro h; simpa [h] using hz.2.1
  have h1 : rho ≠ 1 := by intro h; simpa [h] using hz.2.2
  exact ⟨hz.2.2, h0, h1, norm_pos_iff.mpr h0⟩

theorem nyman_unitInterval_zero_obstruction (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hrho : 1 / 2 < rho.re) :
    Real.sqrt (2 * rho.re - 1) / ‖rho‖ ≤ Metric.infDist unitTarget (closure B0) :=
  nyman_unitInterval_zero_obstruction_of_strip rho hrho (nontrivial_zero_domain rho hz).1 hz.1

/-- Both literal clauses, with their independent quantifiers, in one addressable statement. -/
theorem nyman_unitInterval_mellin_and_zero_obstruction :
    (∀ (theta : ℝ), 0 < theta → theta ≤ 1 → ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      (∫ x in Ioo (0 : ℝ) 1, ((Int.fract (theta / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
        (theta : ℂ) / (s - 1) - (theta : ℂ) ^ s * riemannZeta s / s) ∧
    (∀ (rho : ℂ), Zeta23.IsNontrivialZero rho → ∀ (hrho : 1 / 2 < rho.re),
      ‖mellinFunctional rho hrho‖ = 1 / Real.sqrt (2 * rho.re - 1) ∧
      mellinFunctional rho hrho unitTarget = 1 / rho ∧
      (∀ f ∈ closure B0, mellinFunctional rho hrho f = 0) ∧
      Real.sqrt (2 * rho.re - 1) / ‖rho‖ ≤ Metric.infDist unitTarget (closure B0)) :=
  ⟨D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin.fractionalMellin_eq_zeta,
    fun rho hz hrho => ⟨mellinFunctional_norm rho hrho, mellinFunctional_unitTarget rho hrho,
      fun f hf => mellinFunctional_closure_B0 rho hrho hz.2.2 hz.1 f hf,
      nyman_unitInterval_zero_obstruction rho hz hrho⟩⟩

end D5.S3.Observer.Hilbert.NymanUnitIntervalMellin
