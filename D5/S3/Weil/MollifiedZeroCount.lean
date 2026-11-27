/- GID: D5/S3/Weil/MollifiedZeroCount
   generality: I
   mirror-B: D5/B/S3/Weil/MollifiedZeroCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A mollified zeta second moment bounds the actual dyadic right-strip zero count. -/

import D5.S3.Weil.ZetaRvm.LocalCount
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
The dyadic zero count follows from a uniform vertical second moment.

For a disk of radius r centered at c, normalize the angular integral by 2π. The mean-value
identity gives f(c) on every circle of radius 0 < x ≤ r. With b = ‖f(c)‖, the norm inequality
for the average and the pointwise square (‖f(z)‖ - b)^2 imply
  b^2 ≤ circleAverage (fun z ↦ ‖f z‖^2) c x.
Polar coordinates contribute the radial Jacobian x. Integrating the circle inequality against
2πx on (0,r) gives πr²‖f(c)‖² ≤ ∫ z in ball c r, ‖f z‖².
-/

open Complex Metric MeasureTheory Set
open scoped BigOperators Classical

noncomputable section

namespace Zeta23

private theorem norm_sq_le_circleAverage_norm_sq {f : ℂ → ℂ} {c : ℂ} {x : ℝ}
    (hx : 0 ≤ x) (hf : DifferentiableOn ℂ f (closedBall c x)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z ↦ ‖f z‖ ^ 2) c x := by
  let b : ℝ := ‖f c‖
  have hb : 0 ≤ b := norm_nonneg _
  have hmean : Real.circleAverage f c x = f c := by
    apply DiffContOnCl.circleAverage
    rw [abs_of_nonneg hx]
    exact hf.diffContOnCl_ball Subset.rfl
  have havg : b ≤ Real.circleAverage (fun z ↦ ‖f z‖) c x := by
    simpa only [hmean, b] using
      (Real.norm_circleAverage_le_circleAverage_norm (f := f) (c := c) (R := x))
  have hcont := hf.continuousOn.mono (sphere_subset_closedBall : sphere c x ⊆ closedBall c x)
  have hlin : CircleIntegrable (fun z ↦ (2 * b) • ‖f z‖) c x := by
    exact (hcont.norm.const_smul (2 * b)).circleIntegrable hx
  have hsq : CircleIntegrable (fun z ↦ ‖f z‖ ^ 2) c x :=
    (hcont.norm.pow 2).circleIntegrable hx
  have hcomp := Real.circleAverage_mono (hlin.add (circleIntegrable_const (-(b ^ 2)) c x))
    hsq (fun z _ ↦ by
      change (2 * b) * ‖f z‖ + -(b ^ 2) ≤ ‖f z‖ ^ 2
      nlinarith [sq_nonneg (‖f z‖ - b)])
  rw [Real.circleAverage_add hlin (circleIntegrable_const (-(b ^ 2)) c x),
    Real.circleAverage_fun_smul, Real.circleAverage_const, smul_eq_mul] at hcomp
  have hmul := mul_le_mul_of_nonneg_left havg (show 0 ≤ 2 * b by positivity)
  change b ^ 2 ≤ _
  nlinarith only [hcomp, hmul]

/-- The planar integral over an open disk is the radial integral of its circle averages. -/
private theorem integral_ball_eq_circleAverage {g : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (closedBall c r)) :
    (∫ z in ball c r, g z) =
      ∫ x in Ioo 0 r, (2 * Real.pi) * x * Real.circleAverage g c x := by
  let q : ℝ × ℝ → ℝ := fun p ↦ p.1 * g (circleMap c p.1 p.2)
  have hq : Integrable q
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine IntegrableOn.mono_set (t := Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) ?_
      (fun _ hp ↦ ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hmap : MapsTo (fun p : ℝ × ℝ ↦ circleMap c p.1 p.2)
        (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) (closedBall c r) := fun p hp ↦
      closedBall_subset_closedBall hp.1.2 (circleMap_mem_closedBall c hp.1.1 p.2)
    have hc : Continuous (fun p : ℝ × ℝ ↦ circleMap c p.1 p.2) :=
      Real.circleMap.continuous
    exact continuous_fst.continuousOn.mul (hg.comp hc.continuousOn hmap)
  let G : ℂ → ℝ := (ball c r).indicator g
  have htranslate : (∫ w : ℂ, G (w + c)) = ∫ z : ℂ, G z := by
    exact (measurePreserving_add_right (volume : Measure ℂ) c).integral_comp
      (MeasurableEquiv.addRight c).measurableEmbedding G
  have hpolar : (∫ w : ℂ, G (w + c)) =
      ∫ p in Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi, q p := by
    rw [← Complex.integral_comp_polarCoord_symm (fun w ↦ G (w + c))]
    change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • G (Complex.polarCoord.symm p + c)) = _
    rw [← integral_indicator (measurableSet_Ioi.prod measurableSet_Ioo),
      ← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro p
    have hnorm : ‖Complex.polarCoord.symm p + c - c‖ = |p.1| := by
      rw [add_sub_cancel_right, Complex.norm_polarCoord_symm]
    have hcircle : Complex.polarCoord.symm p + c = circleMap c p.1 p.2 := by
      rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
      ac_rfl
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
    · rw [indicator_of_mem hp]
      have hrmem : Complex.polarCoord.symm p + c ∈ ball c r ↔ p.1 < r := by
        rw [Metric.mem_ball, dist_eq_norm, hnorm, abs_of_pos hp.1]
      by_cases hpr : p.1 < r
      · rw [indicator_of_mem (show p ∈ Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi from
            ⟨⟨hp.1, hpr⟩, hp.2⟩)]
        rw [show G (Complex.polarCoord.symm p + c) = g (circleMap c p.1 p.2) by
          rw [show G (Complex.polarCoord.symm p + c) =
            (ball c r).indicator g (Complex.polarCoord.symm p + c) from rfl,
            indicator_of_mem (hrmem.mpr hpr), hcircle]]
        rfl
      · rw [indicator_of_notMem (show p ∉ Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi from
            fun h ↦ hpr h.1.2)]
        simp only [G, indicator_of_notMem (mt hrmem.mp hpr), smul_zero]
    · rw [indicator_of_notMem hp, indicator_of_notMem
        (fun h : p ∈ Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi ↦ hp ⟨h.1.1, h.2⟩)]
  calc
    (∫ z in ball c r, g z) = ∫ w : ℂ, G (w + c) := by
      rw [htranslate]
      exact (integral_indicator isOpen_ball.measurableSet).symm
    _ = ∫ p in Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi, q p := hpolar
    _ = ∫ x in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, q (x, θ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod q hq]
    _ = ∫ x in Ioo 0 r, (2 * Real.pi) * x * Real.circleAverage g c x := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x _
      have hperiod : Function.Periodic (fun θ ↦ g (circleMap c x θ)) (2 * Real.pi) :=
        fun θ ↦ by
          change g (circleMap c x (θ + 2 * Real.pi)) = g (circleMap c x θ)
          rw [periodic_circleMap c x θ]
      have hangle : (∫ θ in Ioo (-Real.pi) Real.pi, g (circleMap c x θ)) =
          ∫ θ in 0..2 * Real.pi, g (circleMap c x θ) := by
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
        simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] using
          hperiod.intervalIntegral_add_eq (-Real.pi) 0
      simp only [q, integral_const_mul, hangle, Real.circleAverage_def, smul_eq_mul]
      field_simp [Real.pi_ne_zero] <;> ring

theorem norm_sq_mul_disk_area_le_integral {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r)) :
    (Real.pi * r ^ 2) * ‖f c‖ ^ 2 ≤ ∫ z in ball c r, ‖f z‖ ^ 2 := by
  let g : ℂ → ℝ := fun z ↦ ‖f z‖ ^ 2
  let k : ℝ := (2 * Real.pi) * ‖f c‖ ^ 2
  have hg : ContinuousOn g (closedBall c r) := hf.continuousOn.norm.pow 2
  have havg : ContinuousOn (Real.circleAverage g c) (Icc 0 r) := by
    apply Real.ContinuousOn.circleAverage _ (fun _ hx ↦ hx.1)
    exact hg.mono (fun z hz ↦ by
      rw [mem_closedBall, dist_eq_norm]
      exact hz.2)
  have hL : IntegrableOn (fun x : ℝ ↦ k * x) (Ioo 0 r) :=
    ((continuous_const.mul continuous_id).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hR : IntegrableOn (fun x : ℝ ↦ (2 * Real.pi) * x * Real.circleAverage g c x)
      (Ioo 0 r) :=
    (((continuous_const.mul continuous_id).continuousOn.mul havg).integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  change _ ≤ ∫ z in ball c r, g z
  rw [integral_ball_eq_circleAverage hr hg]
  calc
    (Real.pi * r ^ 2) * ‖f c‖ ^ 2 = ∫ x in Ioo 0 r, k * x := by
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hr.le, integral_id]
      dsimp [k]
      ring
    _ ≤ _ := setIntegral_mono_on hL hR measurableSet_Ioo (fun x hx ↦ by
      have hc := norm_sq_le_circleAverage_norm_sq hx.1.le
        (hf.mono (closedBall_subset_closedBall hx.2.le))
      have hfactor := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) hx.1.le
      have h := mul_le_mul_of_nonneg_left hc hfactor
      simpa only [g, k, mul_assoc, mul_left_comm, mul_comm] using h)

/-- Integrating disk indicators bounds the sum of their weights by their weighted overlap. -/
theorem weighted_count_le_integral_of_disks {ι : Type*} (s : Finset ι) (center : ι → ℂ)
    (w : ι → ℝ) {r k H : ℝ} {U : Set ℂ} {g : ℂ → ℝ}
    (hU : MeasurableSet U) (hg : IntegrableOn g U)
    (hg0 : ∀ z ∈ U, 0 ≤ g z)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsub : ∀ i ∈ s, ball (center i) r ⊆ U)
    (hmass : ∀ i ∈ s, k ≤ ∫ z in ball (center i) r, g z)
    (hoverlap : ∀ z ∈ U,
      (∑ i ∈ s.filter (fun i ↦ z ∈ ball (center i) r), w i) ≤ H) :
    k * (∑ i ∈ s, w i) ≤ H * ∫ z in U, g z := by
  classical
  let B := fun i ↦ ball (center i) r
  let p := fun i z ↦ (B i).indicator (fun x ↦ w i * g x) z
  have hp : ∀ i ∈ s, IntegrableOn (p i) U := by
    intro i hi
    exact (hg.const_mul (w i)).indicator isOpen_ball.measurableSet
  have hint : ∀ i ∈ s, (∫ z in U, p i z) = w i * ∫ z in B i, g z := by
    intro i hi
    dsimp [p]
    rw [integral_indicator isOpen_ball.measurableSet,
      Measure.restrict_restrict_of_subset (hsub i hi), integral_const_mul]
  calc
    k * (∑ i ∈ s, w i) = ∑ i ∈ s, w i * k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
    _ ≤ ∑ i ∈ s, ∫ z in U, p i z := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hint i hi]
      exact mul_le_mul_of_nonneg_left (hmass i hi) (hw i hi)
    _ = ∫ z in U, ∑ i ∈ s, p i z := (integral_finsetSum s hp).symm
    _ ≤ ∫ z in U, H * g z := by
      apply setIntegral_mono_on (integrable_finsetSum s hp) (hg.const_mul H) hU
      intro z hz
      have hpoint : (∑ i ∈ s, p i z) =
          (∑ i ∈ s.filter (fun i ↦ z ∈ B i), w i) * g z := by
        rw [Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hz' : z ∈ B i <;> simp [p, hz']
      rw [hpoint]
      exact mul_le_mul_of_nonneg_right (hoverlap z hz) (hg0 z hz)
    _ = _ := integral_const_mul _ _

/-- Actual nontrivial zeros with strict real cutoff and both signs of the ordinate. -/
def rightStripDyadicZeros (σ T : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZero ρ ∧ σ < ρ.re ∧ T < |ρ.im| ∧ |ρ.im| ≤ 2 * T}

noncomputable def rightStripDyadicCount (σ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ rightStripDyadicZeros σ T, zeroMult ρ

theorem rightStripDyadicZeros_finite (σ T : ℝ) : (rightStripDyadicZeros σ T).Finite :=
  (zerosIn_finite (-(2 * T + 1)) (2 * T)).subset fun ρ hρ ↦
    ⟨hρ.1, by linarith [neg_abs_le ρ.im, hρ.2.2.2],
      (le_abs_self ρ.im).trans hρ.2.2.2⟩

theorem rightStripDyadicCount_eq_zero {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) :
    rightStripDyadicCount σ T = 0 := by
  have h : rightStripDyadicZeros σ T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    exact (not_lt_of_ge (hσ.trans hρ.2.1.le)) hρ.1.2.2
  simp [rightStripDyadicCount, h]

/-- The vertical domain for the uniform mean-square input. -/
def paddedDyadicHeights (T : ℝ) : Set ℝ :=
  Icc (T - 1) (2 * T + 1) ∪ Icc (-(2 * T + 1)) (-(T - 1))

private def paddedStrip (a r T : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc a (1 + r) ∧ z.im ∈ paddedDyadicHeights T}

private theorem mem_paddedDyadicHeights_iff {T y : ℝ} (hT : 2 ≤ T) :
    y ∈ paddedDyadicHeights T ↔ T - 1 ≤ |y| ∧ |y| ≤ 2 * T + 1 := by
  change (T - 1 ≤ y ∧ y ≤ 2 * T + 1) ∨ (-(2 * T + 1) ≤ y ∧ y ≤ -(T - 1)) ↔ _
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso
        linarith [h.2]
    · exact Or.inl
  · rw [abs_of_neg (lt_of_not_ge hy)]
    constructor
    · rintro (h | h)
      · exfalso
        linarith [h.1, lt_of_not_ge hy]
      · constructor <;> linarith [h.1, h.2]
    · intro h
      right
      constructor <;> linarith [h.1, h.2]

private theorem closedBall_subset_paddedStrip {σ a r T : ℝ} {ρ : ℂ}
    (haσ : a + r ≤ σ) (hr : r ≤ 1 / 2) (hT : 2 ≤ T)
    (hρ : ρ ∈ rightStripDyadicZeros σ T) :
    closedBall ρ r ⊆ paddedStrip a r T := by
  intro z hz
  have hdist : ‖z - ρ‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hre : |z.re - ρ.re| ≤ r := by
    simpa only [sub_re] using (Complex.abs_re_le_norm (z - ρ)).trans hdist
  have him : |z.im - ρ.im| ≤ r := by
    simpa only [sub_im] using (Complex.abs_im_le_norm (z - ρ)).trans hdist
  have him' : |ρ.im - z.im| ≤ r := by
    rw [abs_sub_comm]
    exact him
  have hdown := (abs_sub_abs_le_abs_sub ρ.im z.im).trans him'
  have hup := (abs_sub_abs_le_abs_sub z.im ρ.im).trans him
  refine ⟨⟨?_, ?_⟩, (mem_paddedDyadicHeights_iff hT).mpr ⟨?_, ?_⟩⟩
  · linarith [(abs_le.mp hre).1, hρ.2.1]
  · linarith [(abs_le.mp hre).2, hρ.1.2.2]
  · linarith [hρ.2.2.1]
  · linarith [hρ.2.2.2]

private theorem one_notMem_paddedStrip {a r T : ℝ} (hT : 2 ≤ T) :
    (1 : ℂ) ∉ paddedStrip a r T := by
  intro h
  have hlower := ((mem_paddedDyadicHeights_iff hT).mp h.2).1
  simp at hlower
  linarith

private theorem sum_zeroMult_disk_overlap {r : ℝ} (hr : r ≤ 1 / 2)
    (z : ℂ) (s : Finset ℂ) (hs : ∀ ρ ∈ s, IsNontrivialZero ρ) :
    (∑ ρ ∈ s.filter (fun ρ ↦ z ∈ ball ρ r), (zeroMult ρ : ℝ)) ≤
      (Ncount (z.im - 1 / 2) (z.im - 1 / 2 + 1) : ℝ) := by
  classical
  let t : ℝ := z.im - 1 / 2
  have hfin := zerosIn_finite t (t + 1)
  have hsub : s.filter (fun ρ ↦ z ∈ ball ρ r) ⊆ hfin.toFinset := by
    intro ρ hρ
    obtain ⟨hρs, hρb⟩ := Finset.mem_filter.mp hρ
    have hdist : ‖z - ρ‖ < r := by
      simpa [dist_eq_norm] using mem_ball.mp hρb
    have him : |z.im - ρ.im| < r := by
      simpa only [sub_im] using (Complex.abs_im_le_norm (z - ρ)).trans_lt hdist
    refine hfin.mem_toFinset.mpr ⟨hs ρ hρs, ?_, ?_⟩
    · dsimp [t]
      linarith [(abs_lt.mp him).2]
    · dsimp [t]
      linarith [(abs_lt.mp him).1]
  change _ ≤ (Ncount t (t + 1) : ℝ)
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.cast_nonneg _)

private theorem integral_paddedStrip_le {a r T E : ℝ} (ha : a ≤ 1 + r)
    {g : ℂ → ℝ} (hg : ContinuousOn g (paddedStrip a r T))
    (hv : ∀ u ∈ Icc a (1 + r),
      (∫ t in paddedDyadicHeights T, g ((u : ℂ) + (t : ℂ) * I)) ≤ E) :
    (∫ z in paddedStrip a r T, g z) ≤ (1 + r - a) * E := by
  let e := Complex.measurableEquivRealProd.symm
  let R := Icc a (1 + r) ×ˢ paddedDyadicHeights T
  have hpre (p : ℝ × ℝ) : e p ∈ paddedStrip a r T ↔ p ∈ R := Iff.rfl
  have hBand : IsCompact (paddedDyadicHeights T) := isCompact_Icc.union isCompact_Icc
  have hR : IsCompact R := isCompact_Icc.prod hBand
  have hU : MeasurableSet (paddedStrip a r T) :=
    (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
      (hBand.measurableSet.preimage Complex.continuous_im.measurable)
  let q : ℝ × ℝ → ℝ := fun p ↦ g (e p)
  have hq : IntegrableOn q R := by
    apply ContinuousOn.integrableOn_compact hR
    exact hg.comp Complex.equivRealProdCLM.symm.continuous.continuousOn
      (fun p hp ↦ (hpre p).mpr hp)
  have hcoord : ∀ (u t : ℝ), e (u, t) = (u : ℂ) + (t : ℂ) * I :=
    fun u t ↦ Complex.equivRealProdCLM_symm_apply (u, t)
  have hrect : (∫ z in paddedStrip a r T, g z) = ∫ p in R, q p := by
    have he : MeasurePreserving e (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm _
    rw [← integral_indicator hU, ← integral_indicator hR.measurableSet]
    rw [← he.integral_comp' ((paddedStrip a r T).indicator g)]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro p
    by_cases hp : p ∈ R
    · simp only [indicator_of_mem hp, indicator_of_mem ((hpre p).mpr hp), q]
    · rw [indicator_of_notMem hp, indicator_of_notMem
        (mt (hpre p).mp hp)]
  have hfun : Integrable q
      ((volume.restrict (Icc a (1 + r))).prod (volume.restrict (paddedDyadicHeights T))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hq
  calc
    (∫ z in paddedStrip a r T, g z) = ∫ p in R, q p := hrect
    _ = ∫ u in Icc a (1 + r), ∫ t in paddedDyadicHeights T, g ((u : ℂ) + (t : ℂ) * I) := by
      change (∫ p in Icc a (1 + r) ×ˢ paddedDyadicHeights T, q p) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod q hfun]
      simp only [q, hcoord]
    _ ≤ ∫ _u in Icc a (1 + r), E := by
      apply setIntegral_mono_on _ (integrableOn_const isCompact_Icc.measure_ne_top)
        measurableSet_Icc hv
      simpa only [IntegrableOn, q, hcoord] using hfun.integral_prod_left
    _ = _ := by rw [setIntegral_const, Real.volume_real_Icc_of_le ha, smul_eq_mul]

/-!
The center set is contained in the finite signed window (−(2T+1), 2T]. Every disk
through z has a center with ordinate in (Im z − 1/2, Im z + 1/2]. Thus the two-sided
unit-height bound controls the sum of analytic multiplicities of those disks. On the
padded strip |Im z − 1/2| + 3 ≤ 5T for T ≥ 2. The uniform vertical estimate gives
the area bound (1+r−a) C T^(1−η) by Fubini. Absorb the overlap logarithm via
log(5T) ≤ (5T)^(η/2)/(η/2). The resulting constant is independent of T.

For 1/2 < σ < 1 one may take a = (σ + 1/2)/2 and r = min ((σ − a)/2) (1/4).
Every closed disk stays in the padded strip, which excludes 1 when T ≥ 2.
At its center ρ the mollified error is −1, so the disk integral is at least πr².
Integrating the weighted disk indicators against the squared error gives
πr² times the right-strip count on the lower side and at most
A log(5T) times the strip integral on the upper side, with A as in the local count.
-/
theorem rightStripDyadicCount_le_of_mollified_second_moment
    {σ a r η C : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 2)
    (haσ : a + r ≤ σ) (hσ : σ < 1) (hη : 0 < η) (hC : 0 ≤ C)
    {M : ℝ → ℂ → ℂ} (hM : ∀ T, Differentiable ℂ (M T))
    (hmoment : ∀ T : ℝ, 2 ≤ T → ∀ u ∈ Icc a (1 + r),
      (∫ t in paddedDyadicHeights T,
        ‖riemannZeta ((u : ℂ) + (t : ℂ) * I) * M T ((u : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
        ≤ C * T ^ (1 - η)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 2 ≤ T →
      (rightStripDyadicCount σ T : ℝ) ≤ D * T ^ (1 - η / 2) := by
  classical
  obtain ⟨A, hA, hlocal⟩ := RvM.zeta_local_zero_count
  have ha : a ≤ 1 + r := by linarith
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let K : ℝ := A * ((5 : ℝ) ^ ε / ε)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let L : ℝ := (1 + r - a) * C
  have hL : 0 ≤ L := mul_nonneg (sub_nonneg.mpr ha) hC
  let k : ℝ := Real.pi * r ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨K * L / k, by positivity, fun T hT ↦ ?_⟩
  let U := paddedStrip a r T
  let F : ℂ → ℂ := fun z ↦ riemannZeta z * M T z - 1
  let g : ℂ → ℝ := fun z ↦ ‖F z‖ ^ 2
  have hF : DifferentiableOn ℂ F U := by
    intro z hz
    have hz1 : z ≠ 1 := fun h ↦ one_notMem_paddedStrip hT (h ▸ hz)
    exact (((differentiableAt_riemannZeta hz1).mul ((hM T) z)).sub_const 1).differentiableWithinAt
  have hg : ContinuousOn g U := hF.continuousOn.norm.pow 2
  have hg0 : ∀ z ∈ U, 0 ≤ g z := fun z _ ↦ sq_nonneg ‖F z‖
  have hUcompact : IsCompact U :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
      (isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc))
  have hsFin := rightStripDyadicZeros_finite σ T
  let s := hsFin.toFinset
  have hs : ∀ ρ ∈ s, ρ ∈ rightStripDyadicZeros σ T :=
    fun _ hρ ↦ hsFin.mem_toFinset.mp hρ
  have hdisks : ∀ ρ ∈ s, closedBall ρ r ⊆ U :=
    fun ρ hρ ↦ closedBall_subset_paddedStrip haσ hrsmall hT (hs ρ hρ)
  have hmass : ∀ ρ ∈ s, k ≤ ∫ z in ball ρ r, g z := by
    intro ρ hρ
    have hzero : riemannZeta ρ = 0 := (hs ρ hρ).1.1
    simpa [g, F, hzero, k] using
      norm_sq_mul_disk_area_le_integral hr (hF.mono (hdisks ρ hρ))
  have ht : 0 < T := by linarith
  have hoverlap : ∀ z ∈ U,
      (∑ ρ ∈ s.filter (fun ρ ↦ z ∈ ball ρ r), (zeroMult ρ : ℝ)) ≤ K * T ^ ε := by
    intro z hz
    let t := z.im - 1 / 2
    have hzupper := ((mem_paddedDyadicHeights_iff hT).mp hz.2).2
    have htupper : |t| + 3 ≤ 5 * T := by
      have htr : |t| ≤ |z.im| + 1 / 2 := by
        dsimp [t]
        simpa [sub_eq_add_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
          (abs_add_le z.im (-(1 / 2 : ℝ)))
      linarith
    have hlog : Real.log (|t| + 3) ≤ (5 * T) ^ ε / ε := by
      exact (Real.log_le_log (by positivity) htupper).trans
        (Real.log_le_rpow_div (by positivity) hε)
    calc
      _ ≤ (Ncount t (t + 1) : ℝ) :=
        sum_zeroMult_disk_overlap hrsmall z s (fun ρ hρ ↦ (hs ρ hρ).1)
      _ ≤ A * Real.log (|t| + 3) := hlocal t
      _ ≤ A * ((5 * T) ^ ε / ε) := mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = K * T ^ ε := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) ht.le]
        dsimp [K]
        ring
  have harea : (∫ z in U, g z) ≤ L * T ^ (1 - η) := by
    have hb := integral_paddedStrip_le ha hg (fun u hu ↦ hmoment T hT u hu)
    simpa only [L, mul_assoc] using hb
  have hsum := weighted_count_le_integral_of_disks s id (fun ρ ↦ (zeroMult ρ : ℝ))
    hUcompact.measurableSet (hg.integrableOn_compact hUcompact) hg0
    (fun _ _ ↦ Nat.cast_nonneg _) (fun ρ hρ ↦ ball_subset_closedBall.trans (hdisks ρ hρ))
    hmass hoverlap
  have hcount : (rightStripDyadicCount σ T : ℝ) = ∑ ρ ∈ s, (zeroMult ρ : ℝ) := by
    rw [rightStripDyadicCount, finsum_mem_eq_finite_toFinset_sum _ hsFin]
    simp only [Nat.cast_sum, s]
  rw [hcount]
  apply (mul_le_mul_iff_of_pos_left hk).mp
  calc
    k * (∑ ρ ∈ s, (zeroMult ρ : ℝ)) ≤ (K * T ^ ε) * ∫ z in U, g z := hsum
    _ ≤ (K * T ^ ε) * (L * T ^ (1 - η)) :=
      mul_le_mul_of_nonneg_left harea (mul_nonneg hK (Real.rpow_nonneg ht.le _))
    _ = k * (K * L / k * T ^ (1 - η / 2)) := by
      have hexp : T ^ ε * T ^ (1 - η) = T ^ (1 - η / 2) := by
        rw [← Real.rpow_add ht]
        congr 1
        dsimp [ε]
        ring
      rw [← hexp]
      field_simp [hk.ne']

/-- The finite Möbius mollifier, with positive bases and the usual complex power. -/
noncomputable def moebiusMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)

theorem differentiable_moebiusMollifier (X : ℕ) : Differentiable ℂ (moebiusMollifier X) := by
  intro s
  unfold moebiusMollifier
  apply DifferentiableAt.fun_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hbase : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  simp_rw [Complex.cpow_def_of_ne_zero hbase]
  fun_prop

/-- In particular one may take X(T) = floor(T^δ) after proving the stated moment. -/
theorem rightStripDyadicCount_le_of_moebius_second_moment
    {σ a r η C : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 2)
    (haσ : a + r ≤ σ) (hσ : σ < 1) (hη : 0 < η) (hC : 0 ≤ C)
    (X : ℝ → ℕ)
    (hmoment : ∀ T : ℝ, 2 ≤ T → ∀ u ∈ Icc a (1 + r),
      (∫ t in paddedDyadicHeights T,
        ‖riemannZeta ((u : ℂ) + (t : ℂ) * I) *
          moebiusMollifier (X T) ((u : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
        ≤ C * T ^ (1 - η)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 2 ≤ T →
      (rightStripDyadicCount σ T : ℝ) ≤ D * T ^ (1 - η / 2) :=
  rightStripDyadicCount_le_of_mollified_second_moment hr hrsmall haσ hσ hη hC
    (fun T ↦ differentiable_moebiusMollifier (X T)) hmoment

end Zeta23
