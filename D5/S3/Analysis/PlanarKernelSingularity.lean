/- GID: D5/S3/Analysis/PlanarKernelSingularity
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-shear-obstruction4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polar annulus integrals and square-integrability obstructions for planar kernels with a directional inverse-square singularity. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
Omega original.

Polar annulus integrals and square-integrability obstructions for planar kernels with a
directional inverse-square singularity. The complex numbers carry the Euclidean plane metric.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Omega

/-- The squared inverse-square kernel has an exact annular integral. -/
theorem polar_annulus_squared (C : ℝ → ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    (∫ r in ε..ρ, (∫ θ in (0 : ℝ)..(2 * Real.pi), (C θ / r ^ 2) ^ 2) * r) =
      (1 / 2 : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), C θ ^ 2) *
        ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) := by
  let A := ∫ θ in (0 : ℝ)..(2 * Real.pi), C θ ^ 2
  calc
    _ = ∫ r in ε..ρ, A * r ^ (-3 : ℤ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : r ≠ 0 := ne_of_gt (hε.trans_le ((uIcc_of_le hερ.le ▸ hr).1))
      have hinner : (∫ θ in (0 : ℝ)..(2 * Real.pi), (C θ / r ^ 2) ^ 2) =
          A * ((r ^ 2) ^ 2)⁻¹ := by
        simp_rw [div_pow, div_eq_mul_inv]
        exact intervalIntegral.integral_mul_const _ _
      change (∫ θ in (0 : ℝ)..(2 * Real.pi), (C θ / r ^ 2) ^ 2) * r = A * r ^ (-3 : ℤ)
      rw [hinner, zpow_neg, zpow_ofNat]
      field_simp
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_zpow
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hε (hε.trans hερ)⟩)]
      norm_num [zpow_neg, A]
      ring

/-- The annulus integral diverges as the inner radius decreases to zero. -/
theorem tendsto_polar_annulus_squared (C : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hC : 0 < ∫ θ in (0 : ℝ)..(2 * Real.pi), C θ ^ 2) :
    Tendsto (fun ε : ℝ => ∫ r in ε..ρ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (C θ / r ^ 2) ^ 2) * r) (𝓝[>] 0) atTop := by
  have hp : Tendsto (fun ε : ℝ => (ε⁻¹) ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_inv_nhdsGT_zero
  have hmain := (tendsto_atTop_add_const_right _ (-((ρ ^ 2)⁻¹)) hp).const_mul_atTop
    (show 0 < (1 / 2 : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), C θ ^ 2) by positivity)
  refine hmain.congr' ?_
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ := nhdsWithin_le_nhds (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hερ
  simp only [polar_annulus_squared C hε hερ, inv_pow, sub_eq_add_neg]

private def sector (δ a b : ℝ) : Set ℂ :=
  {w | 0 < ‖w‖ ∧ ‖w‖ < δ ∧ Complex.arg w ∈ Ioo a b}

private theorem measurableSet_sector (δ a b : ℝ) : MeasurableSet (sector δ a b) :=
  (measurableSet_lt measurable_const continuous_norm.measurable).inter
    ((measurableSet_lt continuous_norm.measurable measurable_const).inter
      (Complex.measurable_arg measurableSet_Ioo))

private theorem sector_inverse_square_not_integrable {δ c a b : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (ha : -Real.pi ≤ a) (hab : a < b) (hb : b ≤ Real.pi) :
    ¬ IntegrableOn (fun w : ℂ => (c / ‖w‖ ^ 2) ^ 2) (sector δ a b) volume := by
  intro h
  let W := sector δ a b
  let S := Ioo (0 : ℝ) δ ×ˢ Ioo a b
  let f : ℂ → ℝ≥0∞ := W.indicator fun w => ENNReal.ofReal ((c / ‖w‖ ^ 2) ^ 2)
  have hfinite : (∫⁻ w, f w) < ∞ := by
    rw [show f = W.indicator _ from rfl, lintegral_indicator (measurableSet_sector δ a b)]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => sq_nonneg (c / ‖w‖ ^ 2))).mp h.2
  have hS : S ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    exact prod_mono (fun _ hr => hr.1) (Ioo_subset_Ioo ha hb)
  have hinf : (∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (r ^ (-3 : ℝ))) = ∞ := by
    by_contra hne
    have hpow : IntegrableOn (fun r : ℝ => r ^ (-3 : ℝ)) (Ioo (0 : ℝ) δ) volume := by
      refine ⟨(by fun_prop), (hasFiniteIntegral_iff_ofReal ?_).mpr (lt_top_iff_ne_top.mpr hne)⟩
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun r hr =>
        Real.rpow_nonneg hr.1.le _)
    have := intervalIntegral.integrableOn_Ioo_rpow_iff hδ |>.mp hpow
    norm_num at this
  have hpoint (p : ℝ × ℝ) (hp : p ∈ S) :
      ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) =
        (ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (p.1 ^ (-3 : ℝ))) := by
    have hr : 0 < p.1 := hp.1.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have harg : Complex.arg (Complex.polarCoord.symm p) = p.2 := by
      have heq := Complex.polarCoord.right_inv (hS hp)
      exact congrArg Prod.snd heq
    have hw : Complex.polarCoord.symm p ∈ W :=
      ⟨by simpa only [hnorm] using hr, by simpa only [hnorm] using hp.1.2,
        by simpa only [harg] using hp.2⟩
    rw [show f (Complex.polarCoord.symm p) = _ from indicator_of_mem hw _,
      smul_eq_mul, hnorm, ← ENNReal.ofReal_mul hr.le,
      ← ENNReal.ofReal_mul (sq_nonneg c), show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast, zpow_neg, zpow_ofNat]
    congr 1
    field_simp
  have htop : (∫⁻ p in S, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) = ∞ := by
    rw [setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) hpoint,
      Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    have hc' : ENNReal.ofReal (c ^ 2) ≠ 0 := by positivity
    have hab' : ENNReal.ofReal (b - a) ≠ 0 := by positivity
    rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul' _ _ (by simp), hinf,
      ENNReal.mul_top hc', ENNReal.top_mul hab']
  have hle := lintegral_mono_set (μ := volume) (f := fun p => ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) hS
  rw [htop] at hle
  exact (not_le_of_gt hfinite) (hle.trans_eq (Complex.lintegral_comp_polarCoord_symm f))

/-- A uniform off-diagonal inverse-square lower bound on any nonempty angular sector in an
open ball precludes a square-integrable kernel. The bound can hold almost everywhere. -/
theorem planarWedge_not_memLp {K : ℂ × ℂ → ℂ} {z : ℂ} {R ρ c a b : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hc : 0 < c) (ha : -Real.pi ≤ a) (hab : a < b)
    (hb : b ≤ Real.pi)
    (hK : ∀ᵐ p ∂((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))),
      0 < ‖p.1 - p.2‖ → ‖p.1 - p.2‖ < ρ →
        Complex.arg (p.1 - p.2) ∈ Ioo a b → c / ‖p.1 - p.2‖ ^ 2 ≤ ‖K p‖) :
    ¬ MemLp K 2 ((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))) := by
  intro h
  let B := Metric.ball z R
  let μ : Measure ℂ := volume.restrict B
  have hsq := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  have hsec := (integrable_prod_iff hsq.aestronglyMeasurable).mp hsq |>.1
  have haeb : ∀ᵐ x ∂μ, x ∈ B := ae_restrict_mem Metric.isOpen_ball.measurableSet
  have hm : μ ≠ 0 := by
    intro hzero
    have hbpos := Metric.isOpen_ball.measure_pos (μ := (volume : Measure ℂ))
      ⟨z, Metric.mem_ball_self hR⟩
    exact hbpos.ne' (by simpa [μ] using congrArg (fun ν : Measure ℂ => ν univ) hzero)
  have : NeBot (ae μ) := ae_neBot.mpr hm
  obtain ⟨x, hx, hInt, hbound⟩ :
      ∃ x, x ∈ B ∧ Integrable (fun y => ‖K (x, y)‖ ^ 2) μ ∧
        ∀ᵐ y ∂μ, 0 < ‖x - y‖ → ‖x - y‖ < ρ →
          Complex.arg (x - y) ∈ Ioo a b → c / ‖x - y‖ ^ 2 ≤ ‖K (x, y)‖ := by
    exact (haeb.and (hsec.and (Measure.ae_ae_of_ae_prod hK))).exists
  let δ := min ρ (R - dist x z)
  have hδ : 0 < δ := lt_min hρ (sub_pos.mpr hx)
  let W := sector δ a b
  let S : Set ℂ := (fun y => x - y) ⁻¹' W
  have hS : S ⊆ B := by
    intro y hy
    have hy' : ‖x - y‖ < R - dist x z := hy.2.1.trans_le (min_le_right _ _)
    show dist y z < R
    calc
      _ ≤ dist y x + dist x z := dist_triangle _ _ _
      _ = ‖x - y‖ + dist x z := by rw [dist_comm y x, dist_eq_norm]
      _ < _ := by linarith
  have hmS : MeasurableSet S :=
    (measurableSet_sector δ a b).preimage (measurable_const.sub measurable_id)
  have hout : IntegrableOn (fun y : ℂ => (c / ‖x - y‖ ^ 2) ^ 2) S volume := by
    refine (hInt.mono_measure (Measure.restrict_mono hS le_rfl)).mono' ((by fun_prop : Measurable (fun y : ℂ => (c / ‖x - y‖ ^ 2) ^ 2)).aestronglyMeasurable) ?_
    apply (ae_restrict_iff' hmS).mpr
    have hboundS := ae_mono (Measure.restrict_mono hS (le_refl (volume : Measure ℂ))) hbound
    filter_upwards [(ae_restrict_iff' hmS).mp hboundS] with y hy hyS
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hyW : x - y ∈ W := hyS
    exact pow_le_pow_left₀ (by positivity)
      (hy hyS hyW.1 (hyW.2.1.trans_le (min_le_left _ _)) hyW.2.2) _
  have hneg : MeasurePreserving (fun y : ℂ => -y) volume volume :=
    (LinearIsometryEquiv.neg ℝ (E := ℂ)).measurePreserving
  have hmp : MeasurePreserving (fun y : ℂ => x - y) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℂ) x).comp hneg
  have hemb : MeasurableEmbedding (fun y : ℂ => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  exact sector_inverse_square_not_integrable hδ hc ha hab hb
    ((hmp.integrableOn_comp_preimage hemb).mp hout)

/-- The complex-valued off-diagonal kernel of an angular coefficient in a planar chart. -/
def angularKernel (C : ℝ → ℝ) (p : ℂ × ℂ) : ℂ :=
  (↑(C (Complex.arg (p.1 - p.2)) / ‖p.1 - p.2‖ ^ 2) : ℂ)

/-- A nonzero continuous angular coefficient at angle zero supplies a full sector witness. -/
theorem angularKernel_not_memLp {C : ℝ → ℝ} (hC : Continuous C) (h0 : C 0 ≠ 0)
    (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ¬ MemLp (angularKernel C) 2
      ((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))) := by
  let c := |C 0| / 2
  have hc : 0 < c := half_pos (abs_pos.mpr h0)
  have he : ∀ᶠ θ in 𝓝 (0 : ℝ), c < |C θ| :=
    hC.abs.continuousAt.eventually_const_lt (half_lt_self (abs_pos.mpr h0))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp he
  let η := min δ Real.pi
  have hη : 0 < η := lt_min hδ Real.pi_pos
  refine planarWedge_not_memLp hR zero_lt_one hc (neg_le_neg (min_le_right _ _))
    (show -η < η by linarith) (min_le_right _ _) (ae_of_all _ ?_)
  intro p _ _ hp
  have ha : dist (Complex.arg (p.1 - p.2)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hp.1, hp.2.trans_le (min_le_left _ _)⟩
  rw [angularKernel, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖p.1 - p.2‖)]
  exact div_le_div_of_nonneg_right (hsmall ha).le (sq_nonneg _)

/-- Uniform positive separation of two sets of planar coordinates. -/
def PositivelySeparated (s t : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∀ y ∈ t, δ ≤ dist x y

private theorem PositivelySeparated.mono {s t u v : Set ℂ} (h : PositivelySeparated s t)
    (hu : u ⊆ s) (hv : v ⊆ t) : PositivelySeparated u v := by
  obtain ⟨δ, hδ, hh⟩ := h
  exact ⟨δ, hδ, fun x hx y hy => hh x (hu hx) y (hv hy)⟩

private theorem ae_eq_of_rectangle_integrals {μ ν : Measure ℂ} {J K : ℂ × ℂ → ℂ}
    (hJ : Integrable J (μ.prod ν)) (hK : Integrable K (μ.prod ν))
    (hEq : ∀ s t : Set ℂ, MeasurableSet s → MeasurableSet t →
      ∫ p in s ×ˢ t, J p ∂(μ.prod ν) = ∫ p in s ×ˢ t, K p ∂(μ.prod ν)) :
    J =ᵐ[μ.prod ν] K := by
  have h := hJ.sub hK
  have hrect (s t : Set ℂ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫ p in s ×ˢ t, (J - K) p ∂(μ.prod ν) = 0 := by
    rw [Pi.sub_def, integral_sub hJ.integrableOn hK.integrableOn, hEq s t hs ht, sub_self]
  have hall : ∫ p, (J - K) p ∂(μ.prod ν) = 0 := by
    simpa using hrect univ univ .univ .univ
  apply eventuallyEq_iff_sub.mpr
  have hsets (s : Set (ℂ × ℂ)) (hs : MeasurableSet s) :
      ∫ p in s, (J - K) p ∂(μ.prod ν) = 0 := by
    induction s, hs using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic u hu =>
      obtain ⟨s, hs, t, ht, rfl⟩ := hu
      exact hrect s t hs ht
    | compl u hu ih =>
      have he := integral_add_compl hu h
      rwa [ih, zero_add, hall] at he
    | iUnion u hd hu ih =>
      rw [integral_iUnion hu hd h.integrableOn]
      simp only [ih, tsum_zero]
  exact h.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => hsets s hs)

/-- Locally integrable kernels with matching integrals on every positively separated measurable
rectangle agree almost everywhere off the diagonal. -/
theorem ae_eq_offDiagonal_of_rectangle_integrals {μ : Measure ℂ} [SFinite μ]
    {J K : ℂ × ℂ → ℂ} (hJ : Integrable J (μ.prod μ))
    (hK : ∀ s t : Set ℂ, MeasurableSet s → MeasurableSet t → PositivelySeparated s t →
      IntegrableOn K (s ×ˢ t) (μ.prod μ))
    (hEq : ∀ s t : Set ℂ, MeasurableSet s → MeasurableSet t → PositivelySeparated s t →
      ∫ p in s ×ˢ t, J p ∂(μ.prod μ) = ∫ p in s ×ˢ t, K p ∂(μ.prod μ)) :
    ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 → J p = K p := by
  classical
  let U := TopologicalSpace.countableBasis ℂ
  have hU := TopologicalSpace.isBasis_countableBasis ℂ
  have : Countable U := TopologicalSpace.countable_countableBasis ℂ
  have hlocal (s t : U) : ∀ᵐ p ∂(μ.prod μ),
      PositivelySeparated (s : Set ℂ) t → p ∈ (s : Set ℂ) ×ˢ (t : Set ℂ) → J p = K p := by
    by_cases hst : PositivelySeparated (s : Set ℂ) t
    · have hs := (hU.isOpen s.property).measurableSet
      have ht := (hU.isOpen t.property).measurableSet
      have hJ' : Integrable J ((μ.restrict s).prod (μ.restrict t)) := by
        rw [Measure.prod_restrict]
        exact hJ.integrableOn
      have hK' : Integrable K ((μ.restrict s).prod (μ.restrict t)) := by
        rw [Measure.prod_restrict]
        exact hK s t hs ht hst
      have hAE := ae_eq_of_rectangle_integrals hJ' hK' (fun u v hu hv => by
        simp only [Measure.prod_restrict, Measure.restrict_restrict (hu.prod hv),
          prod_inter_prod]
        exact hEq _ _ (hu.inter hs) (hv.inter ht)
          (hst.mono inter_subset_right inter_subset_right))
      rw [Measure.prod_restrict] at hAE
      filter_upwards [(ae_restrict_iff' (hs.prod ht)).mp hAE] with p hp
      exact fun _ => hp
    · exact ae_of_all _ fun _ h => (hst h).elim
  have hAll : ∀ᵐ p ∂(μ.prod μ), ∀ s t : U,
      PositivelySeparated (s : Set ℂ) t → p ∈ (s : Set ℂ) ×ˢ (t : Set ℂ) → J p = K p :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr (hlocal s)
  filter_upwards [hAll] with p hp hne
  let δ := dist p.1 p.2 / 3
  have hδ : 0 < δ := div_pos (dist_pos.mpr hne) (by norm_num)
  obtain ⟨s, hs, hps, hsub⟩ := hU.exists_subset_of_mem_open (Metric.mem_ball_self hδ)
    Metric.isOpen_ball
  obtain ⟨t, ht, hpt, hsub'⟩ := hU.exists_subset_of_mem_open
    (Metric.mem_ball_self (x := p.2) hδ) Metric.isOpen_ball
  apply hp ⟨s, hs⟩ ⟨t, ht⟩ _ ⟨hps, hpt⟩
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  have hxs : dist x p.1 < δ := hsub hx
  have hyt : dist y p.2 < δ := hsub' hy
  have htri := (dist_triangle p.1 x p.2).trans
    (add_le_add_right (dist_triangle x y p.2) (dist p.1 x))
  rw [dist_comm p.1 x] at htri
  dsimp [δ] at *
  linarith

end Omega
