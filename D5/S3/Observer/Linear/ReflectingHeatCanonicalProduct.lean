/- GID: D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatCanonicalProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatQuantile]
   utility: none
   digest: The canonical product of the heat quantiles and its signed axis estimates. -/

import D5.S3.Observer.Linear.ReflectingHeatQuantile
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The entire product of the equal-mass quantiles for the reflecting heat multiplier. -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

namespace EqualMassBins

variable {β : ℝ} {density : ℝ → ℝ} (bins : EqualMassBins β density)

/-- The product uses the right endpoints, with the left endpoint at index zero
excluded. -/
def canonicalProduct (z : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - z ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2)

/-- The potential sampled on the imaginary axis. -/
def imaginaryPotential (β : ℝ) (density : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in Ioi β, Real.log (1 + y ^ 2 / x ^ 2) * density x

private theorem endpoint_pos (hβ : 0 < β) (k : ℕ) : 0 < bins.endpoint k :=
  hβ.trans_le (bins.start_le k)

private theorem spacing {D : ℝ} (hcap : ∀ x ∈ Ici β, density x ≤ D) (k : ℕ) :
    (k : ℝ) ≤ D * (bins.endpoint k - β) := by
  induction k with
  | zero => simp [bins.start]
  | succ k ih =>
    have hab := bins.increasing.monotone (Nat.le_succ k)
    have hu := bins.start_le k
    have hci : IntervalIntegrable density volume (bins.endpoint k) (bins.endpoint (k + 1)) :=
      (bins.continuous_density.mono (fun _ hx => hu.trans hx.1)).intervalIntegrable_of_Icc hab
    have h := intervalIntegral.integral_mono_on hab hci
      (intervalIntegrable_const (c := D)) (fun x hx => hcap x (hu.trans hx.1))
    rw [bins.mass, intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h
    push_cast
    linarith

private theorem summable_endpoint_inv_sq (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) :
    Summable fun k => ((bins.endpoint (k + 1)) ^ 2)⁻¹ := by
  have hs : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by decide : 1 < 2))
  refine (hs.mul_left (D ^ 2)).of_nonneg_of_le (fun _ => by positivity) fun k => ?_
  have ht := bins.endpoint_pos hβ (k + 1)
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hle : ((k + 1 : ℕ) : ℝ) ≤ D * bins.endpoint (k + 1) := by
    have := bins.spacing hcap (k + 1)
    nlinarith
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_pow] using pow_le_pow_left₀ hk.le hle 2

private theorem product_summable (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) (z : ℂ) :
    Summable fun k : ℕ => ‖-(z ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2)‖ := by
  simpa [norm_div, Real.norm_eq_abs, abs_of_pos (bins.endpoint_pos hβ _), div_eq_mul_inv]
    using (bins.summable_endpoint_inv_sq hβ hD hcap).mul_left (‖z‖ ^ 2)

/-- Summable inverse-square endpoints make the canonical product entire. -/
theorem canonicalProduct_entire (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) :
    Differentiable ℂ bins.canonicalProduct := by
  let f (k : ℕ) (z : ℂ) := -(z ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2)
  have hp : HasProdLocallyUniformlyOn (fun k z => 1 + f k z) bins.canonicalProduct univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le (E := ℂ) (s := K)
    have hu := (bins.summable_endpoint_inv_sq hβ hD hcap).mul_left (R ^ 2)
    have hb : ∀ k z, z ∈ K → ‖f k z‖ ≤ R ^ 2 * ((bins.endpoint (k + 1)) ^ 2)⁻¹ := by
      intro k z hz
      change ‖-(z ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2)‖ ≤ _
      rw [norm_neg, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (bins.endpoint_pos hβ (k + 1)), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hR z hz) 2)
        (inv_nonneg.mpr (sq_nonneg _))
    have he : bins.canonicalProduct = (fun z => ∏' k, (1 + f k z)) := by
      funext z
      simp only [canonicalProduct, f, sub_eq_add_neg]
    rw [he]
    exact hu.hasProdUniformlyOn_nat_one_add hK (.of_forall hb) (fun _ => by fun_prop)
  have h := hp.differentiableOn (.of_forall fun _ => by
    simpa only [Finset.prod_fn] using
      (DifferentiableOn.finsetProd fun i _ =>
        (show Differentiable ℂ (fun z => 1 + f i z) by dsimp [f]; fun_prop).differentiableOn))
    isOpen_univ
  exact differentiableOn_univ.mp h

private theorem canonicalProduct_even (z : ℂ) :
    bins.canonicalProduct (-z) = bins.canonicalProduct z := by
  simp [canonicalProduct]

private theorem imaginary_factor (x y : ℝ) :
    1 - ((y : ℂ) * Complex.I) ^ 2 / (x : ℂ) ^ 2 = Complex.ofReal (1 + y ^ 2 / x ^ 2) := by
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

private theorem imaginary_kernel_nonnegative (y x : ℝ) :
    0 ≤ Real.log (1 + y ^ 2 / x ^ 2) :=
  Real.log_nonneg (le_add_of_nonneg_right (by positivity))

private theorem imaginary_kernel_le (y x : ℝ) :
    Real.log (1 + y ^ 2 / x ^ 2) ≤ y ^ 2 / x ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + y ^ 2 / x ^ 2 by positivity)
  linarith

private theorem integrableOn_inv_sq (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioi β) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hβ).congr_fun ?_ measurableSet_Ioi
  intro x hx
  change x ^ (-2 : ℝ) = (x ^ 2)⁻¹
  rw [Real.rpow_neg ((hβ.trans hx).le)]
  norm_num

/-- On the imaginary axis the signed right-endpoint error is between
the negative first logarithmic factor and zero. The lower bound is positive
also at negative imaginary arguments. -/
theorem canonicalProduct_imaginary_bounds (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) (y : ℝ) :
    Real.exp (imaginaryPotential β density y - Real.log (1 + y ^ 2 / β ^ 2)) ≤
        ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖ ∧
      ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖ ≤
        Real.exp (imaginaryPotential β density y) := by
  let g (x : ℝ) := Real.log (1 + y ^ 2 / x ^ 2)
  have hpos : ∀ x ∈ Ici β, 0 < x := fun _ hx => hβ.trans_le hx
  have hg : ContinuousOn g (Ici β) := by
    apply ContinuousOn.log (continuousOn_const.add
      (continuousOn_const.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne'))
    intro x _
    change 1 + y ^ 2 / x ^ 2 ≠ 0
    positivity
  have hanti : AntitoneOn g (Ici β) := by
    intro u hu v hv huv
    apply Real.log_le_log (by positivity)
    apply add_le_add_right
    exact div_le_div_of_nonneg_left (sq_nonneg y) (sq_pos_of_pos (hpos u hu))
      (pow_le_pow_left₀ (hpos u hu).le huv 2)
  have hs : Summable fun k : ℕ => g (bins.endpoint (k + 1)) := by
    refine ((bins.summable_endpoint_inv_sq hβ hD hcap).mul_left (y ^ 2)).of_nonneg_of_le
      (fun _ => imaginary_kernel_nonnegative _ _) ?_
    simpa [g, div_eq_mul_inv] using fun k : ℕ => imaginary_kernel_le y (bins.endpoint (k + 1))
  have hi : IntegrableOn (fun x => g x * density x) (Ioi β) := by
    have hbound := (integrableOn_inv_sq hβ).const_mul (D * y ^ 2)
    apply hbound.mono'
      (((hg.mul bins.continuous_density).mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' := Ioi_subset_Ici_self hx
    change |g x * density x| ≤ D * y ^ 2 * (x ^ 2)⁻¹
    rw [abs_of_nonneg (mul_nonneg (imaginary_kernel_nonnegative y x) (bins.nonnegative x hx'))]
    calc
      g x * density x ≤ (y ^ 2 / x ^ 2) * D :=
        mul_le_mul (imaginary_kernel_le y x) (hcap x hx') (bins.nonnegative x hx') (by positivity)
      _ = _ := by ring
  have hz : Tendsto g atTop (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => y ^ 2 * x⁻¹ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_inv_atTop_zero.pow 2).const_mul (y ^ 2)
    have he := (Real.continuousAt_log (show (1 + 0 : ℝ) ≠ 0 by norm_num)).tendsto.comp
      (tendsto_const_nhds.add ht)
    simpa [g, div_eq_mul_inv, inv_pow, Function.comp_def] using he
  have hn := bins.discrepancy_antitone hg hanti hz hs hi
  have hm (z : ℂ) :
      Multipliable (fun k : ℕ => 1 - z ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2) :=
    multipliable_one_sub_of_summable
      (by simpa only [norm_neg] using bins.product_summable hβ hD hcap z)
  have hp : ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖ = Real.exp (∑' k, g (bins.endpoint (k + 1))) := by
    rw [canonicalProduct, (hm ((y : ℂ) * Complex.I)).norm_tprod]
    have hnonneg (x : ℝ) : 0 ≤ 1 + y ^ 2 / x ^ 2 := by positivity
    simp only [imaginary_factor, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    exact (Real.rexp_tsum_eq_tprod (fun _ => by positivity) hs).symm
  rw [hp, Real.exp_le_exp, Real.exp_le_exp]
  exact ⟨by dsimp [imaginaryPotential, g] at *; linarith [hn.1],
    by dsimp [imaginaryPotential, g] at *; linarith [hn.2]⟩

/-- The imaginary product majorizes the product on the whole circle. -/
theorem canonicalProduct_radial_comparison (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) (z : ℂ) :
    ‖bins.canonicalProduct z‖ ≤ ‖bins.canonicalProduct ((‖z‖ : ℂ) * Complex.I)‖ := by
  let w : ℂ := (‖z‖ : ℂ) * Complex.I
  have hm (u : ℂ) :
      Multipliable (fun k : ℕ => 1 - u ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2) :=
    multipliable_one_sub_of_summable
      (by simpa only [norm_neg] using bins.product_summable hβ hD hcap u)
  apply le_of_tendsto_of_tendsto' (hm z).hasProd.norm.tendsto_prod_nat
    (hm w).hasProd.norm.tendsto_prod_nat
  intro N
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  rw [show w = (‖z‖ : ℂ) * Complex.I from rfl, imaginary_factor, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (norm_sub_le _ _).trans_eq (by
    simp [norm_div, Real.norm_eq_abs, abs_of_pos (bins.endpoint_pos hβ _)])

/-- An imaginary-axis potential bound at half the rescaled time gives the
radial exponential envelope required by the inverse Fourier support theorem. -/
theorem canonicalProduct_half_width (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) {L : ℝ}
    (hpotential : ∀ y ≥ 0, imaginaryPotential β density y ≤ L / 2 * y) (z : ℂ) :
    ‖bins.canonicalProduct z‖ ≤ Real.exp (L / 2 * ‖z‖) :=
  (bins.canonicalProduct_radial_comparison hβ hD hcap z).trans
    ((bins.canonicalProduct_imaginary_bounds hβ hD hcap ‖z‖).2.trans
      (Real.exp_le_exp.mpr (hpotential ‖z‖ (norm_nonneg z))))

end EqualMassBins
end D5.S3.Observer.Linear.ReflectingHeatInterpolation
