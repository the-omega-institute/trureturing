/- GID: D5/S3/FluidDynamics/Fourier/BochnerRowHeatPath
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/BochnerRowHeatPath
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: The full-lattice row-divergence heat kernel has a continuous Bochner Duhamel path. -/

import Mathlib

open scoped ENNReal BigOperators
open Set MeasureTheory Filter Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath

set_option maxHeartbeats 4000000 in
-- The full-lattice Bochner construction and its dominated-convergence proof need this bounded heartbeat budget.
/-- The time-singular projected row divergence of a bounded continuous tensor
path admits an actual Hilbert-valued Bochner integral on the full lattice. -/
theorem bochner_row_heat_path (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let G := lp (fun _ : K => TV) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    ∀ (q : ℝ → G) (hq : Continuous q) (C : ℝ) (hC : 0 ≤ C)
      (hqbound : ∀ t, ‖q t‖ ≤ C),
    ∃ D : ℝ → H, Continuous D ∧
      D 0 = 0 ∧
      (∀ t ∈ Icc 0 τ, ‖D t‖ ≤ 2 * C * Real.sqrt (t / ν)) ∧
      ∀ t ∈ Icc 0 τ, ∀ k : K,
        D t k = ∫ s in (0 : ℝ)..t,
          Real.exp (-ν * (t-s) * ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * q s k (i,j)))) := by
  classical
  intro K V TV H G ρ κ P q hq C hC hqbound
  have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
  let hc : ℝ → ℝ := fun r => (ν*r)^(-(1/2:ℝ))
  have hc0 (r : ℝ) (hr : 0 ≤ r) : 0 ≤ hc r :=
    Real.rpow_nonneg (mul_nonneg hν.le hr) _
  have hGaussian (r : ℝ) (hr : 0 < r) (k : K) :
      Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k) ≤ hc r := by
    have hvr : 0 < ν*r := mul_pos hν hr
    have hz : 0 ≤ ν*r*ρ k := mul_nonneg hvr.le (hρ k)
    have he : ν*r*ρ k ≤ Real.exp (ν*r*ρ k) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have heP := Real.rpow_le_rpow hz he (by norm_num : (0:ℝ) ≤ 1/2)
    have hB : (ν*r)^(1/2:ℝ) *
        ((ρ k)^(1/2:ℝ) * Real.exp (-ν*r*ρ k)) ≤ 1 := by
      calc
        _ = (ν*r*ρ k)^(1/2:ℝ) * Real.exp (-(ν*r*ρ k)) := by
          rw [Real.mul_rpow hvr.le (hρ k)]
          rw [show -ν*r*ρ k = -(ν*r*ρ k) by ring]
          ring
        _ ≤ (Real.exp (ν*r*ρ k))^(1/2:ℝ) *
            Real.exp (-(ν*r*ρ k)) :=
          mul_le_mul_of_nonneg_right heP (Real.exp_pos _).le
        _ = Real.exp (-(ν*r*ρ k)/2) := by
          rw [← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [hc]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hvr.le, ← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hvr _)).mpr
    simpa [mul_comm] using hB
  have hcontract (k : K) (Z : TV) :
      ‖(WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, κ k j * Z (i,j)) : V)‖ ≤
        Real.sqrt (ρ k) * ‖Z‖ := by
    let row := fun i : Fin 2 =>
      (WithLp.toLp 2 (fun j : Fin 2 => Z (i,j)) : V)
    have hrow (i) : ‖∑ j : Fin 2, κ k j * Z (i,j)‖ ≤ ‖κ k‖ * ‖row i‖ := by
      simpa [V, TV, PiLp.inner_apply, κ, row, mul_comm] using
        norm_inner_le_norm (𝕜 := ℂ) (κ k) (row i)
    have hk : ‖κ k‖ ^ 2 = ρ k := by
      simp [V, EuclideanSpace.norm_sq_eq, κ, ρ, Complex.norm_intCast, sq_abs,
        Fin.sum_univ_two]
    have hrows : ∑ i : Fin 2, ‖row i‖ ^ 2 = ‖Z‖ ^ 2 := by
      simp only [TV, EuclideanSpace.norm_sq_eq, row,
        Fintype.sum_prod_type]
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (hρ k)]
    calc
      _ = ∑ i : Fin 2, ‖∑ j : Fin 2, κ k j * Z (i,j)‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i : Fin 2, (‖κ k‖ * ‖row i‖) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
      _ = _ := by simp only [mul_pow, ← Finset.mul_sum, hk, hrows]
  let Dlin (k : K) : TV →ₗ[ℂ] V :=
    { toFun := fun Z => WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * Z (i,j))
      map_add' := by
        intro Z W
        ext i
        change (∑ j : Fin 2, κ k j * (Z (i,j) + W (i,j))) =
          (∑ j : Fin 2, κ k j * Z (i,j)) +
            ∑ j : Fin 2, κ k j * W (i,j)
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro z Z
        ext i
        change (∑ j : Fin 2, κ k j * (z * Z (i,j))) =
          z * ∑ j : Fin 2, κ k j * Z (i,j)
        simp [← Finset.mul_sum, mul_left_comm] }
  let DC (k : K) : TV →L[ℂ] V :=
    (Dlin k).mkContinuous (Real.sqrt (ρ k)) (hcontract k)
  let DCp (k : K) : TV →L[ℂ] V := Complex.I • (P k).comp (DC k)
  have hDC (k : K) (Z : TV) : ‖DCp k Z‖ ≤ Real.sqrt (ρ k) * ‖Z‖ := by
    change ‖Complex.I • P k (DC k Z)‖ ≤ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact ((ℂ ∙ κ k)ᗮ.norm_starProjection_apply_le _).trans (hcontract k Z)
  let RK (r : ℝ) (k : K) : TV →L[ℂ] V :=
    Real.exp (-ν*r*ρ k) • DCp k
  have hRK (r : ℝ) (hr : 0 < r) (k : K) : ‖RK r k‖ ≤ hc r := by
    apply ContinuousLinearMap.opNorm_le_bound _ (hc0 r hr.le)
    intro Z
    change ‖(Real.exp (-ν*r*ρ k) : ℝ) • DCp k Z‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-ν*r*ρ k) * (Real.sqrt (ρ k) * ‖Z‖) :=
        mul_le_mul_of_nonneg_left (hDC k Z) (Real.exp_pos _).le
      _ ≤ hc r * ‖Z‖ := by
        calc
          _ = (Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k)) * ‖Z‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hGaussian r hr k) (norm_nonneg _)
  let R : ℝ → G →L[ℂ] H := fun r => if hr : 0 < r then
    lp.mapCLM 2 (RK r) (hc0 r hr.le) (hRK r hr) else 0
  have hRcoeff (r : ℝ) (hr : 0 < r) (Z : G) (k : K) :
      R r Z k = Real.exp (-ν*r*ρ k) • DCp k (Z k) := by
    simp only [R, dif_pos hr]
    rfl
  have hRbound (r : ℝ) (hr : 0 < r) (Z : G) : ‖R r Z‖ ≤ hc r * ‖Z‖ := by
    apply (R r).le_of_opNorm_le
    simp only [R, dif_pos hr]
    exact lp.norm_mapCLM_le 2 (RK r) (hc0 r hr.le) (hRK r hr)
  have hcInt : IntervalIntegrable hc volume 0 τ := by
    have hi := (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=τ)
      (by norm_num : -1 < (-(1/2):ℝ))).const_mul (ν^(-(1/2:ℝ)))
    apply hi.congr
    intro r hr
    rw [uIoc_of_le hτ.le] at hr
    dsimp [hc]
    exact (Real.mul_rpow hν.le hr.1.le).symm
  have hcI : IntegrableOn hc (Ioc 0 τ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mp hcInt
  have hRm (t : ℝ) : StronglyMeasurable (fun r => R r (q (t-r))) := by
    let g : ℝ → H := fun r => R r (q (t-r))
    have hgk (k : K) : StronglyMeasurable (fun r => g r k) := by
      let v : ℝ → V := fun r => Real.exp (-ν*r*ρ k) • DCp k (q (t-r) k)
      have hv : Continuous v := by
        have he : Continuous (fun r : ℝ => q (t-r) k) :=
          (lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp
            (hq.comp (continuous_const.sub continuous_id))
        exact (Real.continuous_exp.comp (by fun_prop)).smul
          ((DCp k).continuous.comp he)
      convert hv.stronglyMeasurable.indicator (measurableSet_Ioi (a := (0:ℝ))) using 1
      funext r
      by_cases hr : 0 < r
      · simpa only [Set.indicator, mem_Ioi, hr, ite_true, v, g] using
          hRcoeff r hr (q (t-r)) k
      · simp [g, R, hr, Set.indicator_of_notMem hr]
    have hf (s : Finset K) : StronglyMeasurable
        (fun r => ∑ k ∈ s, lp.single (E := fun _ : K => V) 2 k (g r k)) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro k hk
      exact (lp.singleContinuousLinearMap ℝ (fun _ : K => V) 2 k).continuous.comp_stronglyMeasurable
        (hgk k)
    exact stronglyMeasurable_of_tendsto (atTop : Filter (Finset K)) hf
      (tendsto_pi_nhds.mpr (fun r => lp.hasSum_single (by norm_num) (g r)))
  let F : ℝ → ℝ → H := fun t r =>
    (Iic t).indicator (fun r => R r (q (t-r))) r
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 τ)) :=
    ((hRm t).indicator measurableSet_Iic).aestronglyMeasurable
  have hFB (t r : ℝ) (hr : r ∈ Ioc 0 τ) : ‖F t r‖ ≤ hc r * C := by
    dsimp [F]
    by_cases hrt : r ≤ t
    · simp only [Set.indicator, mem_Iic, hrt, ite_true]
      exact (hRbound r hr.1 _).trans
        (mul_le_mul_of_nonneg_left (hqbound _) (hc0 r hr.1.le))
    · simp only [Set.indicator, mem_Iic, hrt, ite_false, norm_zero]
      exact mul_nonneg (hc0 r hr.1.le) hC
  have hFI (t : ℝ) : Integrable (F t) (volume.restrict (Ioc 0 τ)) := by
    apply (hcI.mul_const C).mono' (hFm t)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFB t r hr
  have hFt (t r : ℝ) (hr : r ≠ t) : ContinuousAt (fun s => F s r) t := by
    have hcR : Continuous (fun s : ℝ => R r (q (s-r))) :=
      (R r).continuous.comp (hq.comp (continuous_id.sub continuous_const))
    rcases lt_or_gt_of_ne hr with hrt | htr
    · apply hcR.continuousAt.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hrt] with s hs
      have hs' : r ≤ s := le_of_lt hs
      simp only [F, Set.indicator, mem_Iic, hs', ite_true]
    · apply (continuousAt_const (y := (0:H))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds htr] with s hs
      have hs' : ¬ r ≤ s := not_le.mpr hs
      simp only [F, Set.indicator, mem_Iic, hs', ite_false]
  let D : ℝ → H := fun t => ∫ r in Ioc 0 τ, F t r
  have hDcont : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply continuousAt_of_dominated
      (Filter.Eventually.of_forall hFm)
      (Filter.Eventually.of_forall fun s => ?_) (hcI.mul_const C)
    · have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioc 0 τ), r ≠ t :=
        ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
      filter_upwards [hn] with r hr
      exact hFt t r hr
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB s r hr
  have hDzero : D 0 = 0 := by
    dsimp [D]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    simp [F, not_le.mpr hr.1]
  have hDbound (t : ℝ) (ht : t ∈ Icc 0 τ) :
      ‖D t‖ ≤ 2 * C * Real.sqrt (t / ν) := by
    have hDinterval : D t = ∫ r in (0 : ℝ)..t, R r (q (t-r)) := by
      dsimp [D]
      rw [← intervalIntegral.integral_of_le hτ.le]
      exact intervalIntegral.integral_indicator ht
    rw [hDinterval]
    have hct : IntervalIntegrable hc volume 0 t := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      exact hcI.mono_set (Ioc_subset_Ioc le_rfl ht.2)
    have hbound :
        ‖∫ r in (0 : ℝ)..t, R r (q (t-r))‖ ≤
          ∫ r in (0 : ℝ)..t, hc r * C := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1
        (ae_of_all _ (fun r hr => ?_))
        (hct.mul_const C)
      have hr' : r ∈ Ioc (0 : ℝ) t := by
        simpa [uIoc_of_le ht.1] using hr
      exact (hRbound r hr'.1 (q (t-r))).trans
        (mul_le_mul_of_nonneg_left (hqbound _) (hc0 r hr'.1.le))
    calc
      ‖∫ r in (0 : ℝ)..t, R r (q (t-r))‖ ≤
          ∫ r in (0 : ℝ)..t, hc r * C := hbound
      _ = 2 * C * Real.sqrt (t / ν) := by
        calc
          (∫ r in (0 : ℝ)..t, hc r * C) =
              (∫ r in (0 : ℝ)..t, hc r) * C := by
                rw [intervalIntegral.integral_mul_const]
          _ = (ν ^ (-(1/2 : ℝ)) *
              ∫ r in (0 : ℝ)..t, r ^ (-(1/2 : ℝ))) * C := by
                congr 1
                rw [← intervalIntegral.integral_const_mul]
                apply intervalIntegral.integral_congr
                intro r hr
                by_cases hr0 : r = 0
                · simp [hr0, hc]
                · have hrI : r ∈ Icc (0 : ℝ) t := by
                    simpa [uIcc_of_le ht.1] using hr
                  have hrp : 0 < r := lt_of_le_of_ne hrI.1 (Ne.symm hr0)
                  dsimp [hc]
                  rw [Real.mul_rpow hν.le hrp.le]
          _ = 2 * C * Real.sqrt (t / ν) := by
            rw [integral_rpow (Or.inl (by norm_num : -1 < -(1/2 : ℝ)))]
            norm_num [Real.zero_rpow]
            rw [← Real.sqrt_eq_rpow]
            have hfactor : ν ^ (-(1/2 : ℝ)) *
                (Real.sqrt t / (1/2 : ℝ)) * C =
                2 * C * (ν ^ (-(1/2 : ℝ)) * Real.sqrt t) := by ring
            rw [hfactor]
            rw [show ν ^ (-(1/2 : ℝ)) * Real.sqrt t = Real.sqrt (t / ν) by
              rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
              rw [Real.div_rpow ht.1 hν.le, Real.rpow_neg hν.le]
              ring]
  refine ⟨D, hDcont, hDzero, hDbound, ?_⟩
  intro t ht k
  have hEv := (lp.evalCLM ℝ (fun _ : K => V) 2 k).integral_comp_comm (hFI t)
  change (lp.evalCLM ℝ (fun _ : K => V) 2 k) (∫ r in Ioc 0 τ, F t r) = _
  rw [← hEv]
  let g : ℝ → V := fun r => Real.exp (-ν*r*ρ k) • DCp k (q (t-r) k)
  calc
    _ = ∫ r in Ioc 0 τ, (Iic t).indicator g r := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      by_cases hrt : r ≤ t
      · change ((Iic t).indicator (fun r => R r (q (t-r))) r) k = _
        simp only [Set.indicator, mem_Iic, hrt, ite_true]
        exact hRcoeff r hr.1 (q (t-r)) k
      · change ((Iic t).indicator (fun r => R r (q (t-r))) r) k = _
        simp only [Set.indicator, mem_Iic, hrt, ite_false]
        rfl
    _ = ∫ r in (0:ℝ)..t, g r := by
      rw [← intervalIntegral.integral_of_le hτ.le]
      exact intervalIntegral.integral_indicator ht
    _ = ∫ s in (0:ℝ)..t,
          Real.exp (-ν*(t-s)*ρ k) • DCp k (q s k) := by
      have hs := intervalIntegral.integral_comp_sub_left
        (fun s : ℝ => Real.exp (-ν*(t-s)*ρ k) • DCp k (q s k)) (a:=0) (b:=t) t
      simpa only [sub_sub_cancel, sub_self, sub_zero] using hs
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      rfl

#print axioms bochner_row_heat_path

end D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath
