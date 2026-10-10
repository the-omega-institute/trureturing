/- GID: D5/S3/Quantum/Petz/StieltjesRepresentation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stieltjes integration of the boundary density by scaled logarithmic master integrals. -/

import D5.S3.Quantum.Petz.StieltjesDensity
import D5.S3.Quantum.Petz.SymmetricKernel

namespace D5.S3.Quantum.Petz.StieltjesRepresentation

open Set MeasureTheory Filter
open scoped Topology
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.Petz.SymmetricKernel
open D5.S3.Quantum.PositiveResolvent.LogarithmicIntegral

private noncomputable def B (x u t : ℝ) : ℝ :=
  1 / ((x + t) * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2))

private noncomputable def A (u t : ℝ) : ℝ :=
  1 / (t * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2))

private lemma B_scaled (x u t : ℝ) (hu : 0 < u) :
    B x u (u * t) = u⁻¹ *
      (1 / ((x / u + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) := by
  dsimp [B]
  rw [mul_div_cancel_left₀ _ hu.ne']
  field_simp
  <;> ring

private lemma B_integral {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    IntegrableOn (B x u) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), B x u t) = masterValue (x / u) := by
  have hm := master_integral (x / u) (div_pos hx hu)
  have heq : (fun t => B x u (u * t)) =
      (fun t => u⁻¹ * (1 / ((x / u + t) * ((Real.log t) ^ 2 + Real.pi ^ 2)))) := by
    funext t
    exact B_scaled x u t hu
  constructor
  · have h := (integrableOn_Ioi_comp_mul_left_iff (B x u) 0 hu).mp
      (by rw [heq]; exact hm.1.const_mul _)
    simpa only [mul_zero] using h
  · have h := integral_comp_mul_left_Ioi (B x u) 0 hu
    simp only [mul_zero, smul_eq_mul] at h
    rw [heq, integral_const_mul, hm.2] at h
    exact mul_left_cancel₀ (inv_ne_zero hu.ne') h.symm

private lemma A_integral {u : ℝ} (hu : 0 < u) :
    IntegrableOn (A u) (Ioi 0) ∧ (∫ t in Ioi (0 : ℝ), A u t) = 1 :=
  logarithmic_density_mass u hu

private lemma B_div_integrable {x v u : ℝ} (hx : 0 < x) (hv : 0 < v) (hu : 0 < u) :
    IntegrableOn (fun t => B x u t / (v + t)) (Ioi 0) := by
  apply ((B_integral hx hu).1.const_mul (1 / v)).mono'
  · exact (by unfold B; fun_prop : Measurable (fun t => B x u t / (v + t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hB : 0 < B x u t := by dsimp [B]; positivity
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hB (add_pos hv ht))]
    simpa only [one_div_mul_eq_div] using
      (div_le_div_of_nonneg_left hB.le hv (le_add_of_nonneg_right ht.le))

private lemma A_div_integrable {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    IntegrableOn (fun t => A u t / (x + t)) (Ioi 0) := by
  apply ((A_integral hu).1.const_mul (1 / x)).mono'
  · exact (by unfold A; fun_prop : Measurable (fun t => A u t / (x + t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hA : 0 < A u t := by dsimp [A]; positivity
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hA (add_pos hx ht))]
    simpa only [one_div_mul_eq_div] using
      (div_le_div_of_nonneg_left hA.le hx (le_add_of_nonneg_right ht.le))

private lemma B_div_integral {x v u : ℝ} (hx : 0 < x) (hv : 0 < v) (hu : 0 < u)
    (hne : x ≠ v) :
    (∫ t in Ioi (0 : ℝ), B x u t / (v + t)) =
      (masterValue (x / u) - masterValue (v / u)) / (v - x) := by
  have heq : ∀ t ∈ Ioi (0 : ℝ), B x u t / (v + t) =
      (B x u t - B v u t) / (v - x) := by
    intro t ht
    change 0 < t at ht
    dsimp [B]
    field_simp [(add_pos hx ht).ne', (add_pos hv ht).ne', sub_ne_zero.mpr hne.symm]
    <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_div,
    integral_sub (B_integral hx hu).1 (B_integral hv hu).1,
    (B_integral hx hu).2, (B_integral hv hu).2]

private lemma A_div_integral {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    (∫ t in Ioi (0 : ℝ), A u t / (x + t)) = (1 - masterValue (x / u)) / x := by
  have heq : ∀ t ∈ Ioi (0 : ℝ), A u t / (x + t) = (A u t - B x u t) / x := by
    intro t ht
    change 0 < t at ht
    dsimp [A, B]
    field_simp [ht.ne', hx.ne', (add_pos hx ht).ne']
    <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_div,
    integral_sub (A_integral hu).1 (B_integral hx hu).1,
    (A_integral hu).2, (B_integral hx hu).2]

private lemma rP_decompose {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : 0 < t) (hne : y ≠ z) :
    rP y z t / (x + t) = (B x y t - B x z t) / (y - z) +
      B x y t / (z + t) + B x z t / (y + t) := by
  dsimp [rP, B]
  field_simp [(add_pos hx ht).ne', (add_pos ht hy).ne', (add_pos ht hz).ne',
    (add_pos hy ht).ne', (add_pos hz ht).ne', sub_ne_zero.mpr hne]
  <;> ring

private lemma rQ_decompose {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : 0 < t) :
    rQ y z t / (x + t) =
      (B x z t / z + A z t / (x + t) - (B x y t / y + A y t / (x + t))) /
        Real.log (y / z) := by
  dsimp [rQ, B, A]
  field_simp [ht.ne', hy.ne', hz.ne', (add_pos hx ht).ne']
  <;> ring

private lemma rP_integrable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : y ≠ z) : IntegrableOn (fun t => rP y z t / (x + t)) (Ioi 0) := by
  apply ((((B_integral hx hy).1.sub (B_integral hx hz).1).div_const (y - z)).add
    (B_div_integrable hx hz hy) |>.add (B_div_integrable hx hy hz)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (rP_decompose hx hy hz ht hne).symm

private lemma rQ_integrable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t => rQ y z t / (x + t)) (Ioi 0) := by
  apply ((((B_integral hx hz).1.div_const z).add (A_div_integrable hx hz) |>.sub
    (((B_integral hx hy).1.div_const y).add (A_div_integrable hx hy))).div_const
    (Real.log (y / z))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (rQ_decompose hx hy hz ht).symm

private lemma rho_integrable_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : y ≠ z) : IntegrableOn (fun t => rho y z t / (x + t)) (Ioi 0) := by
  apply (((rQ_integrable hx hy hz).const_mul 2).sub (rP_integrable hx hy hz hne)
    |>.div_const 6).congr
  exact Eventually.of_forall (fun t => by simp only [rho, if_neg hne]; dsimp only [Pi.sub_apply]; ring)

private lemma rho_integrable_self {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t => rho y y t / (x + t)) (Ioi 0) := by
  have hf : AEStronglyMeasurable
      (fun t : ℝ => Real.log (t / y) / ((Real.log (t / y)) ^ 2 + Real.pi ^ 2))
      (volume.restrict (Ioi 0)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hb : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Real.log (t / y) / ((Real.log (t / y)) ^ 2 + Real.pi ^ 2)‖ ≤
        1 + 1 / Real.pi ^ 2 :=
    Eventually.of_forall (fun t => log_factor_bound (Real.log (t / y)))
  have hi := (((B_integral hx hy).1.div_const y).sub
    (B_div_integrable hx hy hy) |>.div_const 3).sub
    ((((B_integral hx hy).1.div_const y).add
      ((A_div_integrable hx hy).const_mul (2 / 3 : ℝ))).bdd_mul hf hb)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp only [rho, if_pos rfl]
  dsimp [B, A]
  have hD : (Real.log (t / y)) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  field_simp [hx.ne', hy.ne', ht.ne', (add_pos hx ht).ne', (add_pos hy ht).ne',
    (add_pos ht hy).ne', hD]
  <;> ring

/-- Absolute convergence for every positive node, including the confluent density. -/
theorem rho_integrable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t => rho y z t / (x + t)) (Ioi 0) := by
  by_cases hne : y = z
  · subst z
    exact rho_integrable_self hx hy
  · exact rho_integrable_ne hx hy hz hne

private lemma rP_integral {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∫ t in Ioi (0 : ℝ), rP y z t / (x + t)) =
      (masterValue (x / y) - masterValue (x / z)) / (y - z) +
      (masterValue (x / y) - masterValue (z / y)) / (z - x) +
      (masterValue (x / z) - masterValue (y / z)) / (y - x) := by
  have h1 : IntegrableOn (fun t => (B x y t - B x z t) / (y - z)) (Ioi 0) :=
    ((B_integral hx hy).1.sub (B_integral hx hz).1).div_const _
  have h2 : IntegrableOn (fun t => B x y t / (z + t)) (Ioi 0) := B_div_integrable hx hz hy
  have h3 : IntegrableOn (fun t => B x z t / (y + t)) (Ioi 0) := B_div_integrable hx hy hz
  have h12 : IntegrableOn (fun t => (B x y t - B x z t) / (y - z) +
      B x y t / (z + t)) (Ioi 0) := h1.add h2
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => rP_decompose hx hy hz ht hyz),
    integral_add h12 h3, integral_add h1 h2, integral_div,
    integral_sub (B_integral hx hy).1 (B_integral hx hz).1,
    (B_integral hx hy).2, (B_integral hx hz).2,
    B_div_integral hx hz hy hxz, B_div_integral hx hy hz hxy]

private lemma rQ_integral {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), rQ y z t / (x + t)) =
      ((1 / z - 1 / x) * masterValue (x / z) -
        (1 / y - 1 / x) * masterValue (x / y)) / Real.log (y / z) := by
  have h1 : IntegrableOn (fun t => B x z t / z + A z t / (x + t)) (Ioi 0) :=
    ((B_integral hx hz).1.div_const z).add (A_div_integrable hx hz)
  have h2 : IntegrableOn (fun t => B x y t / y + A y t / (x + t)) (Ioi 0) :=
    ((B_integral hx hy).1.div_const y).add (A_div_integrable hx hy)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => rQ_decompose hx hy hz ht),
    integral_div,
    integral_sub h1 h2,
    integral_add ((B_integral hx hz).1.div_const z) (A_div_integrable hx hz),
    integral_add ((B_integral hx hy).1.div_const y) (A_div_integrable hx hy),
    integral_div, integral_div, (B_integral hx hz).2, (B_integral hx hy).2,
    A_div_integral hx hz, A_div_integral hx hy]
  ring

private lemma masterValue_distinct {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hne : x ≠ u) :
    masterValue (x / u) = 1 / (Real.log x - Real.log u) - u / (x - u) := by
  rw [masterValue, if_neg ((div_eq_one_iff_eq hu.ne').not.mpr hne), Real.log_div hx.ne' hu.ne']
  field_simp
  <;> ring

set_option maxRecDepth 2048 in
/-- The representation at three distinct positive nodes. -/
private theorem stieltjes_representation_distinct {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∫ t in Ioi (0 : ℝ), rho y z t / (x + t)) = -hs x y z := by
  have heq : ∀ t : ℝ, rho y z t / (x + t) =
      (2 * (rQ y z t / (x + t)) - rP y z t / (x + t)) / 6 := by
    intro t
    simp only [rho, if_neg hyz]
    ring
  simp_rw [heq]
  rw [integral_div, integral_sub ((rQ_integrable hx hy hz).const_mul 2)
    (rP_integrable hx hy hz hyz), integral_const_mul,
    rP_integral hx hy hz hxy hxz hyz, rQ_integral hx hy hz,
    masterValue_distinct hx hy hxy, masterValue_distinct hx hz hxz,
    masterValue_distinct hz hy hyz.symm, masterValue_distinct hy hz hyz,
    hs_eq_closedForm hx hy hz hxy hxz hyz, Real.log_div hy.ne' hz.ne']
  have ha : Real.log x - Real.log y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxy (Real.log_injOn_pos hx hy h))
  have hb : Real.log x - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxz (Real.log_injOn_pos hx hz h))
  have hc : Real.log y - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hyz (Real.log_injOn_pos hy hz h))
  have hcr : Real.log z - Real.log y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hyz (Real.log_injOn_pos hy hz h.symm))
  dsimp [closedForm]
  field_simp [hx.ne', hy.ne', hz.ne', ha, hb, hc, hcr, sub_ne_zero.mpr hxy,
    sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz,
    sub_ne_zero.mpr hxy.symm, sub_ne_zero.mpr hxz.symm, sub_ne_zero.mpr hyz.symm]
  <;> ring

private lemma integral_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContinuousAt (fun v => ∫ t in Ioi (0 : ℝ), rho y z t / (v + t)) x := by
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun t => 2 * ‖rho y z t / (x + t)‖)
  · exact Eventually.of_forall (fun v => (by
      unfold rho rP rQ
      split_ifs <;> fun_prop : Measurable (fun t => rho y z t / (v + t))).aestronglyMeasurable)
  · filter_upwards [eventually_gt_nhds (show x / 2 < x by linarith)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hvt : 0 < v + t := by linarith
    have hxt : 0 < x + t := by positivity
    rw [norm_div, norm_div, Real.norm_eq_abs (v + t), abs_of_pos hvt,
      Real.norm_eq_abs (x + t), abs_of_pos hxt]
    rw [div_le_iff₀ hvt]
    calc
      ‖rho y z t‖ = ‖rho y z t‖ / (x + t) * (x + t) := by field_simp
      _ ≤ 2 * (‖rho y z t‖ / (x + t)) * (v + t) := by
        have hh : x + t ≤ 2 * (v + t) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hh
          (div_nonneg (norm_nonneg (rho y z t)) hxt.le)]
  · exact (rho_integrable hx hy hz).norm.const_mul 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact continuousAt_const.div (continuousAt_id.add_const t) (add_pos hx ht).ne'

/-- Distinct density parameters allow every positive evaluation node. -/
private theorem stieltjes_representation_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) :
    (∫ t in Ioi (0 : ℝ), rho y z t / (x + t)) = -hs x y z := by
  let S := Set.univ \ ({y, z} : Set ℝ)
  have hd : Dense S := dense_univ.sdiff_finite (Set.toFinite _)
  haveI : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp (hd x)
  have hi := (integral_continuousAt hx hy hz).tendsto.mono_left
    (show 𝓝[S] x ≤ 𝓝 x from nhdsWithin_le_nhds)
  have hc : ContinuousAt (fun v => -hs v y z) x :=
    ((hs_continuousAt hx hy hz).comp_of_eq
      (show ContinuousAt (fun v : ℝ => (v, y, z)) x by fun_prop) rfl).neg
  apply tendsto_nhds_unique hi
    (hc.tendsto.mono_left (show 𝓝[S] x ≤ 𝓝 x from nhdsWithin_le_nhds) |>.congr' ?_)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with v hv hp
  have hn : v ≠ y ∧ v ≠ z := by simpa [S] using hv.2
  exact (stieltjes_representation_distinct hp hy hz hn.1 hn.2 hyz).symm

private lemma stieltjes_representation_self {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioi (0 : ℝ), rho y y t / (x + t)) = -hs x y y := by
  obtain ⟨C, hC, hb⟩ := rho_uniform_bound hy
  have hi : Tendsto (fun z => ∫ t in Ioi (0 : ℝ), rho y z t / (x + t))
      (𝓝[≠] y) (𝓝 (∫ t in Ioi (0 : ℝ), rho y y t / (x + t))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun t => C * (B x y t + A y t / (x + t)))
    · exact Eventually.of_forall (fun z => (by
        unfold rho rP rQ
        split_ifs <;> fun_prop : Measurable (fun t => rho y z t / (x + t))).aestronglyMeasurable)
    · filter_upwards [hb] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      rw [norm_div, Real.norm_eq_abs (x + t), abs_of_pos (add_pos hx ht)]
      calc
        ‖rho y z t‖ / (x + t) ≤
            (C * (1 + 1 / t) / ((Real.log (t / y)) ^ 2 + Real.pi ^ 2)) / (x + t) :=
          div_le_div_of_nonneg_right (hz t ht) (add_pos hx ht).le
        _ = C * (B x y t + A y t / (x + t)) := by
          dsimp [B, A]
          field_simp
          <;> ring
    · exact ((B_integral hx hy).1.add (A_div_integrable hx hy)).const_mul C
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (rho_tendsto hy ht).div tendsto_const_nhds (add_pos hx ht).ne'
  have hc : ContinuousAt (fun z => -hs x y z) y :=
    ((hs_continuousAt hx hy hy).comp_of_eq
      (show ContinuousAt (fun z : ℝ => (x, y, z)) y by fun_prop) rfl).neg
  apply tendsto_nhds_unique hi
    (hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ?_)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds] with z hne hz
  have hyz : y ≠ z := by simpa [mem_compl_iff, mem_singleton_iff, ne_comm] using hne
  exact (stieltjes_representation_ne hx hy hz hyz).symm

/-- Stieltjes representation of the negative symmetric kernel, including all coincidences. -/
theorem stieltjes_representation {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), rho y z t / (x + t)) = -hs x y z := by
  by_cases hne : y = z
  · subst z
    exact stieltjes_representation_self hx hy
  · exact stieltjes_representation_ne hx hy hz hne

end D5.S3.Quantum.Petz.StieltjesRepresentation
