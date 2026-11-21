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
  have hp : ‖bins.canonicalProduct ((y : ℂ) * Complex.I)‖ =
      Real.exp (∑' k, g (bins.endpoint (k + 1))) := by
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
    simp [Real.norm_eq_abs, abs_of_pos (bins.endpoint_pos hβ _)])

/-- An imaginary-axis potential bound at half the rescaled time gives the
radial exponential envelope required by the inverse Fourier support theorem. -/
theorem canonicalProduct_half_width (hβ : 0 < β)
    {D : ℝ} (hD : 0 < D) (hcap : ∀ x ∈ Ici β, density x ≤ D) {L : ℝ}
    (hpotential : ∀ y ≥ 0, imaginaryPotential β density y ≤ L / 2 * y) (z : ℂ) :
    ‖bins.canonicalProduct z‖ ≤ Real.exp (L / 2 * ‖z‖) :=
  (bins.canonicalProduct_radial_comparison hβ hD hcap z).trans
    ((bins.canonicalProduct_imaginary_bounds hβ hD hcap ‖z‖).2.trans
      (Real.exp_le_exp.mpr (hpotential ‖z‖ (norm_nonneg z))))

/-- The logarithmic potential on the real axis, with its locally integrable
singularity at the evaluation point. -/
def realPotential (β : ℝ) (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi β, Real.log |1 - x ^ 2 / t ^ 2| * density t

private def clippedRatio (x δ t : ℝ) : ℝ :=
  max |t - x| δ * (t + x) / t ^ 2

private def clippedLog (x δ t : ℝ) : ℝ := Real.log (clippedRatio x δ t)

private theorem clippedRatio_pos {x δ t : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (ht : 0 < t) :
    0 < clippedRatio x δ t := by
  exact div_pos (mul_pos (hδ.trans_le (le_max_right _ _)) (by linarith)) (by positivity)

private theorem clippedRatio_left {x δ t : ℝ} (hx : 0 ≤ x) (ht : 0 < t)
    (h : t ≤ x + δ) :
    clippedRatio x δ t = max (x ^ 2 / t ^ 2 - 1) (δ / t + δ * x / t ^ 2) := by
  have hmax : max |t - x| δ = max (x - t) δ := by
    rw [abs_sub_comm, abs_eq_max_neg, max_assoc, neg_sub, max_eq_right (show t - x ≤ δ by linarith)]
  rw [clippedRatio, hmax]
  have hc : 0 ≤ (t + x) / t ^ 2 := by positivity
  rw [mul_div_assoc, max_mul_of_nonneg _ _ hc]
  congr 1
  · field_simp
    ring
  · field_simp

private theorem clippedRatio_right {x δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (h : x + δ ≤ t) :
    clippedRatio x δ t = 1 - x ^ 2 / t ^ 2 := by
  rw [clippedRatio, abs_of_nonneg (show 0 ≤ t - x by linarith),
    max_eq_left (show δ ≤ t - x by linarith)]
  field_simp
  ring

private theorem clippedLog_shape {β x δ : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) (hδ : 0 < δ) :
    ContinuousOn (clippedLog x δ) (Ici β) ∧
      AntitoneOn (clippedLog x δ) (Icc β (max β (x + δ))) ∧
      MonotoneOn (clippedLog x δ) (Ici (max β (x + δ))) := by
  have hpos (t : ℝ) (ht : β ≤ t) := clippedRatio_pos hx hδ (hβ.trans_le ht)
  have hright : MonotoneOn (clippedLog x δ) (Ici (x + δ)) := by
    intro u hu v hv huv
    have hu' : 0 < u := (add_pos_of_nonneg_of_pos hx hδ).trans_le hu
    have hv' : 0 < v := hu'.trans_le huv
    apply Real.log_le_log (clippedRatio_pos hx hδ hu')
    rw [clippedRatio_right hδ hu' hu, clippedRatio_right hδ hv' hv]
    exact sub_le_sub_left (div_le_div_of_nonneg_left (sq_nonneg x) (sq_pos_of_pos hu')
      (pow_le_pow_left₀ hu'.le huv 2)) _
  refine ⟨?_, ?_, hright.mono (Ici_subset_Ici.mpr (le_max_right _ _))⟩
  · apply ContinuousOn.log
    · unfold clippedRatio
      have hnum : Continuous fun t : ℝ => max |t - x| δ * (t + x) := by fun_prop
      exact hnum.continuousOn.div (continuousOn_id.pow 2) fun t ht =>
        pow_ne_zero 2 (hβ.trans_le (mem_Ici.mp ht)).ne'
    · exact fun t ht => (hpos t ht).ne'
  · rcases le_total (x + δ) β with hs | hs
    · rw [max_eq_left hs]
      intro u hu v hv _
      rw [le_antisymm hu.2 hu.1, le_antisymm hv.2 hv.1]
    · rw [max_eq_right hs]
      intro u hu v hv huv
      have hu' := hβ.trans_le hu.1
      have hv' := hβ.trans_le hv.1
      have hsq := pow_le_pow_left₀ hu'.le huv 2
      apply Real.log_le_log (hpos v hv.1)
      rw [clippedRatio_left hx hu' hu.2, clippedRatio_left hx hv' hv.2]
      exact max_le_max
        (sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg x) (sq_pos_of_pos hu') hsq) _)
        (add_le_add (div_le_div_of_nonneg_left hδ.le hu' huv)
          (div_le_div_of_nonneg_left (mul_nonneg hδ.le hx) (sq_pos_of_pos hu') hsq))

private theorem clippedLog_min {β x δ : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) (hδ : 0 < δ) :
    -clippedLog x δ (max β (x + δ)) ≤ Real.log (1 + x / δ) := by
  have hs : 0 < x + δ := add_pos_of_nonneg_of_pos hx hδ
  have hm : 0 < max β (x + δ) := hβ.trans_le (le_max_left _ _)
  have hle : clippedLog x δ (x + δ) ≤ clippedLog x δ (max β (x + δ)) := by
    apply Real.log_le_log (clippedRatio_pos hx hδ hs)
    rw [clippedRatio_right hδ hs le_rfl, clippedRatio_right hδ hm (le_max_right _ _)]
    exact sub_le_sub_left (div_le_div_of_nonneg_left (sq_nonneg x) (sq_pos_of_pos hs)
      (pow_le_pow_left₀ hs.le (le_max_right _ _) 2)) _
  have hr : (1 + x / δ)⁻¹ ≤ clippedRatio x δ (x + δ) := by
    rw [clippedRatio_right hδ hs le_rfl, show 1 + x / δ = (x + δ) / δ by
      field_simp; ring, inv_div]
    apply (le_sub_iff_add_le).2
    calc
      δ / (x + δ) + x ^ 2 / (x + δ) ^ 2 =
          (δ * (x + δ) + x ^ 2) / (x + δ) ^ 2 := by field_simp
      _ ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hs)).2 (by nlinarith [mul_nonneg hx hδ.le])
  have hlog : Real.log ((1 + x / δ)⁻¹) ≤ clippedLog x δ (x + δ) :=
    Real.log_le_log (by positivity) hr
  rw [Real.log_inv] at hlog
  linarith

private theorem clippedLog_tail {x δ : ℝ} (hδ : 0 < δ) :
    Tendsto (clippedLog x δ) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 - x ^ 2 / t ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa [div_eq_mul_inv, inv_pow] using
      tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.pow 2).const_mul (x ^ 2))
  have h := (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp ht
  rw [Real.log_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 (x + δ))] with t ht
  rw [Function.comp_apply, clippedLog, clippedRatio_right hδ
    (zero_lt_one.trans_le ((le_max_left _ _).trans ht)) ((le_max_right _ _).trans ht)]

private theorem clippedLog_tail_bound {x δ t : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ)
    (ht : 0 < t) (hside : x + δ ≤ t) (hfar : 2 * x ≤ t) :
    |clippedLog x δ t| ≤ 2 * x ^ 2 * (t ^ 2)⁻¹ := by
  let u := x ^ 2 / t ^ 2
  have hu : 0 ≤ u := by positivity
  have hhalf : u ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).2
    nlinarith [pow_le_pow_left₀ (show 0 ≤ 2 * x by positivity) hfar 2]
  have hpos : 0 < 1 - u := by linarith
  have hneg : Real.log (1 - u) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hsmall : (1 - u)⁻¹ - 1 ≤ 2 * u := by
    rw [sub_le_iff_le_add, inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hu (show 0 ≤ 1 - 2 * u by linarith)]
  rw [clippedLog, clippedRatio_right hδ ht hside]
  change |Real.log (1 - u)| ≤ _
  rw [abs_of_nonpos hneg, show 2 * x ^ 2 * (t ^ 2)⁻¹ = 2 * u by simp [u, div_eq_mul_inv, mul_assoc]]
  linarith

include bins in
private theorem clippedLog_integrable (hβ : 0 < β) {D x δ : ℝ}
    (hcap : ∀ t ∈ Ici β, density t ≤ D) (hx : 0 ≤ x) (hδ : 0 < δ) :
    IntegrableOn (fun t => clippedLog x δ t * density t) (Ioi β) := by
  let K := max β (max (x + δ) (2 * x))
  have hK : β ≤ K := le_max_left _ _
  have hc := (clippedLog_shape hβ hx hδ).1.mul bins.continuous_density
  rw [← Ioc_union_Ioi_eq_Ioi hK]
  apply IntegrableOn.union
  · have hsub : Icc β K ⊆ Ici β := fun _ ht => mem_Ici.mpr ht.1
    exact (hc.mono hsub).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have hdom := ((integrableOn_inv_sq hβ).mono_set (Ioi_subset_Ioi hK)).const_mul
      (D * (2 * x ^ 2))
    apply hdom.mono'
      ((hc.mono ((Ioi_subset_Ioi hK).trans Ioi_subset_Ici_self)).aestronglyMeasurable
        measurableSet_Ioi)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := K))] with t ht
    have hβt : t ∈ Ici β := mem_Ici.mpr (hK.trans ht.le)
    change |clippedLog x δ t * density t| ≤ D * (2 * x ^ 2) * (t ^ 2)⁻¹
    rw [abs_mul, abs_of_nonneg (bins.nonnegative t hβt)]
    calc
      _ ≤ (2 * x ^ 2 * (t ^ 2)⁻¹) * D :=
        mul_le_mul (clippedLog_tail_bound hx hδ (hβ.trans_le hβt)
          ((le_max_left _ _).trans ((le_max_right _ _).trans ht.le))
          ((le_max_right _ _).trans ((le_max_right _ _).trans ht.le)))
          (hcap t hβt) (bins.nonnegative t hβt) (by positivity)
      _ = _ := by ring

private theorem clippedLog_summable (hβ : 0 < β) {D x δ : ℝ} (hD : 0 < D)
    (hcap : ∀ t ∈ Ici β, density t ≤ D) (hx : 0 ≤ x) (hδ : 0 < δ) :
    Summable fun k : ℕ => clippedLog x δ (bins.endpoint (k + 1)) := by
  apply ((bins.summable_endpoint_inv_sq hβ hD hcap).mul_left (2 * x ^ 2)).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  have ht := bins.unbounded.comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually (eventually_ge_atTop (max (x + δ) (2 * x)))] with k hk
  exact clippedLog_tail_bound hx hδ (bins.endpoint_pos hβ _)
    ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk)

private theorem clipped_factor_bound {x δ t : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (ht : 0 < t) :
    ‖1 - (x : ℂ) ^ 2 / (t : ℂ) ^ 2‖ ≤ Real.exp (clippedLog x δ t) := by
  rw [clippedLog, Real.exp_log (clippedRatio_pos hx hδ ht), ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, clippedRatio]
  rw [show 1 - x ^ 2 / t ^ 2 = (t - x) * (t + x) / t ^ 2 by
    field_simp; ring, abs_div, abs_mul, abs_of_nonneg (show 0 ≤ t + x by positivity),
    abs_of_nonneg (sq_nonneg t)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    (by positivity)

private theorem canonicalProduct_real_clipped (hβ : 0 < β) {D x δ : ℝ} (hD : 0 < D)
    (hcap : ∀ t ∈ Ici β, density t ≤ D) (hx : 0 ≤ x) (hδ : 0 < δ) :
    ‖bins.canonicalProduct (x : ℂ)‖ ≤
      Real.exp ((∫ t in Ioi β, clippedLog x δ t * density t) + Real.log (1 + x / δ)) := by
  have hs := bins.clippedLog_summable hβ hD hcap hx hδ
  have hm : Multipliable (fun k : ℕ => 1 - (x : ℂ) ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2) :=
    multipliable_one_sub_of_summable
      (by simpa only [norm_neg] using bins.product_summable hβ hD hcap (x : ℂ))
  have hnorm : ‖bins.canonicalProduct (x : ℂ)‖ ≤
      Real.exp (∑' k, clippedLog x δ (bins.endpoint (k + 1))) := by
    apply le_of_tendsto_of_tendsto' hm.hasProd.norm.tendsto_prod_nat
      (Real.continuous_exp.continuousAt.tendsto.comp hs.hasSum.tendsto_sum_nat)
    intro N
    change (∏ k ∈ Finset.range N, ‖1 - (x : ℂ) ^ 2 / (bins.endpoint (k + 1) : ℂ) ^ 2‖) ≤
      Real.exp (∑ k ∈ Finset.range N, clippedLog x δ (bins.endpoint (k + 1)))
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ =>
      clipped_factor_bound hx hδ (bins.endpoint_pos hβ (k + 1))
  obtain ⟨hc, hl, hr⟩ := clippedLog_shape hβ hx hδ
  have hd := bins.discrepancy_le (le_max_left β (x + δ)) hc hl hr (clippedLog_tail hδ)
    hs (bins.clippedLog_integrable hβ hcap hx hδ)
  refine hnorm.trans (Real.exp_le_exp.mpr ?_)
  linarith [clippedLog_min hβ hx hδ]

private def clippingCorrection (x δ : ℝ) : ℝ → ℝ :=
  (Ioc (x - δ) (x + δ)).indicator (fun t => Real.log δ - Real.log (t - x))

private theorem clippingCorrection_integral {x δ : ℝ} (hδ : 0 < δ) :
    Integrable (clippingCorrection x δ) ∧
      (∫ t, clippingCorrection x δ t) = 2 * δ := by
  have hi : IntervalIntegrable Real.log volume (-δ) δ := intervalIntegral.intervalIntegrable_log'
  have hit : IntervalIntegrable (fun t => Real.log (t - x)) volume (x - δ) (x + δ) := by
    convert hi.comp_sub_right x using 1 <;> ring
  have hle : x - δ ≤ x + δ := by linarith
  refine ⟨(integrable_indicator_iff measurableSet_Ioc).2
    (intervalIntegrable_const.sub hit).1, ?_⟩
  rw [clippingCorrection, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_sub intervalIntegrable_const hit,
    intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_comp_sub_right Real.log x]
  rw [show x - δ - x = -δ by ring, show x + δ - x = δ by ring, integral_log,
    Real.log_neg_eq_log]
  ring

private theorem ae_ne_real (x : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ x := by
  rw [ae_iff]
  simp

private theorem clippingCorrection_nonnegative {x δ t : ℝ} (hne : t ≠ x) :
    0 ≤ clippingCorrection x δ t := by
  by_cases ht : t ∈ Ioc (x - δ) (x + δ)
  · rw [clippingCorrection, indicator_of_mem ht, sub_nonneg, ← Real.log_abs (t - x)]
    exact Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hne)) (abs_le.mpr ⟨by linarith [ht.1],
      by linarith [ht.2]⟩)
  · simp [clippingCorrection, ht]

private theorem clippedLog_eq_add_correction {x δ t : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ)
    (ht : 0 < t) (hne : t ≠ x) :
    clippedLog x δ t = Real.log |1 - x ^ 2 / t ^ 2| + clippingCorrection x δ t := by
  let w := (t + x) / t ^ 2
  have hw : 0 < w := by dsimp [w]; positivity
  have ht' : 0 < |t - x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have he : |1 - x ^ 2 / t ^ 2| = |t - x| * w := by
    rw [show 1 - x ^ 2 / t ^ 2 = (t - x) * w by dsimp [w]; field_simp; ring,
      abs_mul, abs_of_pos hw]
  rw [clippedLog, clippedRatio, mul_div_assoc, he,
    Real.log_mul (hδ.trans_le (le_max_right _ _)).ne' hw.ne', Real.log_mul ht'.ne' hw.ne',
    Real.log_abs]
  by_cases h : t ∈ Ioc (x - δ) (x + δ)
  · have hh : |t - x| ≤ δ := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [max_eq_right hh, clippingCorrection, indicator_of_mem h]
    ring
  · have hh : δ ≤ |t - x| := by
      by_contra! hn
      exact h ⟨by linarith [(abs_lt.mp hn).1], by linarith [(abs_lt.mp hn).2]⟩
    rw [max_eq_left hh, Real.log_abs, clippingCorrection, indicator_of_notMem h, add_zero]

include bins in
private theorem clipping_cost (hβ : 0 < β) {D x δ : ℝ} (hD : 0 < D)
    (hcap : ∀ t ∈ Ici β, density t ≤ D) (hx : 0 ≤ x) (hδ : 0 < δ) :
    (∫ t in Ioi β, clippedLog x δ t * density t) ≤ realPotential β density x + 2 * D * δ := by
  let c := clippingCorrection x δ
  obtain ⟨hci, hcv⟩ := clippingCorrection_integral (x := x) hδ
  have hci' : Integrable c := hci
  have hcv' : (∫ t, c t) = 2 * δ := hcv
  have hcn : 0 ≤ᵐ[volume] c := (ae_ne_real x).mono fun _ ht => clippingCorrection_nonnegative ht
  have hweight : IntegrableOn (fun t => c t * density t) (Ioi β) := by
    apply (hci'.restrict.const_mul D).mono'
      (hci'.restrict.aestronglyMeasurable.mul
        ((bins.continuous_density.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi))
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β)),
      ae_restrict_of_ae hcn] with t ht hct
    have ht' := Ioi_subset_Ici_self ht
    change |c t * density t| ≤ D * c t
    rw [abs_of_nonneg (mul_nonneg hct (bins.nonnegative t ht')), mul_comm D]
    exact mul_le_mul_of_nonneg_left (hcap t ht') hct
  have hclip := bins.clippedLog_integrable hβ hcap hx hδ
  have hsub : (fun t => clippedLog x δ t * density t - c t * density t) =ᵐ[volume.restrict (Ioi β)]
      fun t => Real.log |1 - x ^ 2 / t ^ 2| * density t := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β)),
      ae_restrict_of_ae (ae_ne_real x)] with t ht hne
    rw [clippedLog_eq_add_correction hx hδ (hβ.trans ht) hne]
    dsimp [c]
    ring
  have hsplit : (∫ t in Ioi β, clippedLog x δ t * density t) =
      realPotential β density x + ∫ t in Ioi β, c t * density t := by
    unfold realPotential
    rw [← integral_congr_ae hsub, integral_sub hclip hweight]
    ring
  rw [hsplit]
  apply add_le_add_right
  calc
    _ ≤ ∫ t in Ioi β, D * c t := by
      apply integral_mono_ae hweight (hci'.restrict.const_mul D)
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β)),
        ae_restrict_of_ae hcn] with t ht hct
      exact (mul_le_mul_of_nonneg_left (hcap t (Ioi_subset_Ici_self ht)) hct).trans_eq
        (mul_comm _ _)
    _ ≤ ∫ t, D * c t := integral_mono_measure Measure.restrict_le_self
      (hcn.mono fun _ ht => mul_nonneg hD.le ht) (hci'.const_mul D)
    _ = _ := by rw [integral_const_mul, hcv']; ring

/-- The real-axis bound at inverse density cap, including the cost of clipping
a logarithmic singularity even when it lies at a quantile. -/
theorem canonicalProduct_real_bound (hβ : 0 < β) {D : ℝ} (hD : 0 < D)
    (hcap : ∀ t ∈ Ici β, density t ≤ D) (x : ℝ) :
    ‖bins.canonicalProduct (x : ℂ)‖ ≤
      Real.exp 2 * (1 + D * |x|) * Real.exp (realPotential β density |x|) := by
  have habs : bins.canonicalProduct (x : ℂ) = bins.canonicalProduct (|x| : ℝ) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Complex.ofReal_neg, bins.canonicalProduct_even]
  rw [habs]
  refine (bins.canonicalProduct_real_clipped hβ hD hcap (abs_nonneg x) (inv_pos.mpr hD)).trans ?_
  have hcost := bins.clipping_cost hβ hD hcap (abs_nonneg x) (inv_pos.mpr hD)
  rw [mul_assoc, mul_inv_cancel₀ hD.ne', mul_one] at hcost
  calc
    _ ≤ Real.exp (realPotential β density |x| + 2 + Real.log (1 + |x| / D⁻¹)) :=
      Real.exp_le_exp.mpr (add_le_add_left hcost _)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), div_inv_eq_mul]
      ring

#print axioms canonicalProduct_entire
#print axioms canonicalProduct_real_bound
#print axioms canonicalProduct_imaginary_bounds
#print axioms canonicalProduct_half_width

end EqualMassBins
end D5.S3.Observer.Linear.ReflectingHeatInterpolation
