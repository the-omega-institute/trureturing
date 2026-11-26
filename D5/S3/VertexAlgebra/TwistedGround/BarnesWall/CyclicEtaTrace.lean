/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CyclicEtaTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/CyclicEtaTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.Discriminant]
   utility: none
   digest: The cyclic modular identity fixes the ground trace at 2^32. -/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The eta quotient for the order-four Barnes–Wall trace has its modular
transform at the negative-inversion cusp. Squaring removes the square-root
factors before taking the sixty-fourth power. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CyclicEtaTrace

open Complex hiding eta
open Filter
open scoped Topology
open UpperHalfPlane hiding I
open ModularForm (eta eta_ne_zero eta_comp_eq_csqrt_I_inv)

private theorem sqrt_sq_of_ne_zero {z : ℂ} (hz : z ≠ 0) : sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  convert Complex.exp_log hz using 2
  ring

private theorem eta_S_sq {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    eta (-1 / z) ^ 2 = (I⁻¹ * z) * eta z ^ 2 := by
  have he : eta (-1 / z) = (sqrt I)⁻¹ * (sqrt z * eta z) := by
    simpa only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using
      eta_comp_eq_csqrt_I_inv hz
  simp only [he, mul_pow, inv_pow, sqrt_sq_of_ne_zero I_ne_zero,
    sqrt_sq_of_ne_zero (⟨z, hz⟩ : ℍ).ne_zero]
  ring

private theorem positive_scale {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (n : ℝ)
    (hn : 0 < n) : ((n : ℂ) * z) ∈ upperHalfPlaneSet := by
  change 0 < z.im at hz
  change 0 < ((n : ℂ) * z).im
  simpa [Complex.mul_im] using mul_pos hn hz

/-- The exact modular transform of the Barnes–Wall order-four twisted trace
eta quotient. The same ground multiplicity multiplies both sides. -/
theorem eta_quotient_S {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    (eta ((-1 / z) / 4) * eta (-1 / z) / eta ((-1 / z) / 2) ^ 2) ^ 64 =
      (eta (4 * z) * eta z / eta (2 * z) ^ 2) ^ 64 := by
  have h2 : (2 : ℂ) * z ∈ upperHalfPlaneSet := by
    simpa using positive_scale hz 2 (by norm_num)
  have h4 : (4 : ℂ) * z ∈ upperHalfPlaneSet := by
    simpa using positive_scale hz 4 (by norm_num)
  have hn2 := eta_ne_zero h2
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hzn := (⟨z, hz⟩ : ℍ).ne_zero
  have s2 : (-1 / z) / 2 = -1 / (2 * z) := by field_simp [hzn]
  have s4 : (-1 / z) / 4 = -1 / (4 * z) := by field_simp [hzn]
  rw [s4, s2]
  have hs :
      (eta (-1 / (4 * z)) * eta (-1 / z) / eta (-1 / (2 * z)) ^ 2) ^ 2 =
        (eta (4 * z) * eta z / eta (2 * z) ^ 2) ^ 2 := by
    simp only [div_pow, mul_pow, eta_S_sq h4, eta_S_sq hz, eta_S_sq h2]
    field_simp
    ring
  rw [show (64 : ℕ) = 2 * 32 by decide, pow_mul, pow_mul, hs]

private noncomputable def eulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

private theorem eulerProduct_tendsto :
    Tendsto eulerProduct (𝓝 (0 : ℂ)) (𝓝 1) := by
  have ht := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 (0 : ℂ)) (g := 0)
    (f := fun q (n : ℕ) => -q ^ (n + 1)) (bound := fun n => (1 / 2 : ℝ) ^ (n + 1))
  simp only [Pi.zero_apply, norm_neg, add_zero, tprod_one] at ht
  unfold eulerProduct
  simp_rw [sub_eq_add_neg]
  refine ht ?_ (fun n => by simpa using ((continuous_pow (M := ℂ) (n + 1)).tendsto 0).neg) ?_
  · simpa only [pow_succ'] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (1 / 2)
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq n
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _

private theorem qParam_scale (h k : ℝ) (z : ℂ) :
    Function.Periodic.qParam h ((k : ℂ) * z) = Function.Periodic.qParam (h / k) z := by
  unfold Function.Periodic.qParam
  congr 1
  rw [Complex.ofReal_div, div_div_eq_mul_div]
  ring

private theorem eta_scaled (k : ℝ) (z : ℂ) :
    eta ((k : ℂ) * z) = Function.Periodic.qParam (24 / k) z *
      eulerProduct (Function.Periodic.qParam (1 / k) z) := by
  simp only [eta, ModularForm.eta_q, qParam_scale _ k, eulerProduct]

private theorem leading_parameters (z : ℂ) :
    Function.Periodic.qParam 6 z * Function.Periodic.qParam 24 z /
      Function.Periodic.qParam 12 z ^ 2 = Function.Periodic.qParam 24 z := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add,
    ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- The transformed order-four oscillator quotient has leading coefficient
one after its known exponential factor is removed. -/
theorem eta_quotient_cusp_limit :
    Tendsto (fun z : ℍ =>
      (eta (4 * (z : ℂ)) * eta z / eta (2 * (z : ℂ)) ^ 2) ^ 64 /
      Function.Periodic.qParam 24 z ^ 64) atImInfty (𝓝 1) := by
  let E (h : ℝ) (z : ℍ) := eulerProduct (Function.Periodic.qParam h z)
  have hE (h : ℝ) (hh : 0 < h) : Tendsto (E h) atImInfty (𝓝 1) :=
    eulerProduct_tendsto.comp (qParam_tendsto_atImInfty hh)
  have htail : Tendsto (fun z => (E (1 / 4) z * E 1 z / E (1 / 2) z ^ 2) ^ 64)
      atImInfty (𝓝 1) := by
    simpa using (((hE (1 / 4) (by norm_num)).mul (hE 1 (by norm_num))).div
      ((hE (1 / 2) (by norm_num)).pow 2) (by norm_num : (1 : ℂ) ^ 2 ≠ 0)).pow 64
  refine htail.congr fun z => ?_
  have h₄ := eta_scaled 4 (z : ℂ)
  have h₂ := eta_scaled 2 (z : ℂ)
  have h₁ := eta_scaled 1 (z : ℂ)
  norm_num at h₄ h₂ h₁
  have hfact : eta (4 * (z : ℂ)) * eta z / eta (2 * (z : ℂ)) ^ 2 =
      Function.Periodic.qParam 24 z * (E (1 / 4) z * E 1 z / E (1 / 2) z ^ 2) := by
    calc
      _ = (Function.Periodic.qParam 6 z * Function.Periodic.qParam 24 z /
          Function.Periodic.qParam 12 z ^ 2) * (E (1 / 4) z * E 1 z / E (1 / 2) z ^ 2) := by
        rw [h₄, h₂, h₁]
        simp only [E, mul_pow, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [leading_parameters]
  rw [hfact, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _
    (Function.Periodic.qParam_ne_zero (h := 24) (z : ℂ)))]

/-- The phase-free cyclic modular identity fixes the ground coefficient
at the exact value dictated by the order-four defect multiplicity. -/
theorem cyclic_ground_trace_eq_two_pow_32 (Z : ℍ → ℂ) (groundTrace : ℂ)
    (hS : ∀ z : ℍ, Z z = (2 : ℂ) ^ 32 *
      (eta ((-1 / (z : ℂ)) / 4) * eta (-1 / (z : ℂ)) /
        eta ((-1 / (z : ℂ)) / 2) ^ 2) ^ 64)
    (hground : Tendsto (fun z : ℍ => Z z / Function.Periodic.qParam 24 z ^ 64)
      atImInfty (𝓝 groundTrace)) :
    groundTrace = (2 : ℂ) ^ 32 := by
  apply tendsto_nhds_unique hground
  have hlim : Tendsto (fun z : ℍ => (2 : ℂ) ^ 32 *
      ((eta (4 * (z : ℂ)) * eta z / eta (2 * (z : ℂ)) ^ 2) ^ 64 /
        Function.Periodic.qParam 24 z ^ 64)) atImInfty (𝓝 ((2 : ℂ) ^ 32)) := by
    simpa only [mul_one] using eta_quotient_cusp_limit.const_mul ((2 : ℂ) ^ 32)
  refine hlim.congr fun z => ?_
  rw [hS z, eta_quotient_S z.2]
  exact (mul_div_assoc _ _ _).symm

#print axioms eta_quotient_S
#print axioms eta_quotient_cusp_limit

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CyclicEtaTrace
