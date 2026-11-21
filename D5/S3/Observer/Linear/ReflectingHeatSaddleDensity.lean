/- GID: D5/S3/Observer/Linear/ReflectingHeatSaddleDensity
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatSaddleDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatCanonicalProduct]
   utility: none
   digest: The reflecting heat saddle radius, density, and imaginary potential. -/

import D5.S3.Observer.Linear.ReflectingHeatCanonicalProduct
import Mathlib.Analysis.Real.Pi.Bounds

/-! The reflecting heat saddle radius, density, and imaginary potential. -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open D5.S3.Analytic.Hardy.FiniteStripMomentBound (radius)
open EqualMassBins

/-- The arcsine spectral average, in its regular angular coordinate. -/
def spectralAverage (f : ℝ → ℝ) : ℝ :=
  (∫ θ in 0..Real.pi, f (2 - 2 * Real.cos θ)) / Real.pi

/-- The continuum saddle exponent at mode rate `q` and saddle radius `β`. -/
def saddleRate (a β q : ℝ) : ℝ :=
  spectralAverage (fun r => Real.log (radius β q + radius β r)) - a / 2 * (radius β q - q)

/-- The scalar function in the stationarity equation for the continuum saddle. -/
def saddleMass (β : ℝ) : ℝ := spectralAverage (fun r => (radius β r)⁻¹)

/-- Bounds on the saddle radius and its inverse at stationarity. -/
theorem saddle_radius_bounds {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hs : saddleMass β = a / 2) :
    β ≤ 2 / a ∧ β⁻¹ ≤ 16 * max 1 (a ^ 2) := by
  let f (θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hr (r : ℝ) : β ≤ radius β r := by
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg r])
  have hf : Continuous f := by
    apply Continuous.inv₀ (by dsimp [radius]; fun_prop)
    exact fun x => (hβ.trans_le (hr _)).ne'
  have hm : (∫ θ in 0..Real.pi, f θ) / Real.pi = a / 2 := hs
  have hπ : 0 < Real.pi := Real.pi_pos
  have hle := intervalIntegral.integral_mono_on (μ := volume) hπ.le
    (hf.intervalIntegrable _ _) (intervalIntegrable_const (c := β⁻¹))
    (fun x _ => inv_anti₀ hβ (hr (2 - 2 * Real.cos x)))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
  have hc : a / 2 ≤ β⁻¹ := by
    rw [← hm, div_le_iff₀ hπ, mul_comm]
    exact hle
  constructor
  · rw [le_div_iff₀ ha]
    have := (le_div_iff₀ hβ).1 (show a / 2 ≤ 1 / β by simpa using hc)
    linarith
  · by_cases hβ1 : β ≤ 1
    · let w := Real.sqrt β
      have hw : 0 < w := Real.sqrt_pos.2 hβ
      have hw1 : w ≤ 1 := by simpa [w] using Real.sqrt_le_sqrt hβ1
      have hwπ : w ≤ Real.pi := hw1.trans (by linarith [Real.pi_gt_three])
      have hw_sq : w ^ 2 = β := Real.sq_sqrt hβ.le
      have hg (x : ℝ) (hx : x ∈ Icc 0 w) : (2 * β)⁻¹ ≤ f x := by
        have hp0 : 0 ≤ 2 - 2 * Real.cos x := by linarith [Real.cos_le_one x]
        have hpβ : 2 - 2 * Real.cos x ≤ β := by
          have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
          have hxw := pow_le_pow_left₀ hx.1 hx.2 2
          linarith
        apply inv_anti₀ (hβ.trans_le (hr _))
        unfold radius
        refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
        nlinarith [pow_le_pow_left₀ hp0 hpβ 2]
      have hpart := intervalIntegral.integral_mono_on (μ := volume) hw.le
        (intervalIntegrable_const (c := (2 * β)⁻¹)) (hf.intervalIntegrable _ _) hg
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hpart
      have htail : 0 ≤ ∫ x in w..Real.pi, f x :=
        intervalIntegral.integral_nonneg hwπ
          (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hf.intervalIntegrable (0 : ℝ) w) (hf.intervalIntegrable w Real.pi)
      have hfull : w * (2 * β)⁻¹ ≤ ∫ x in 0..Real.pi, f x := by linarith
      have heq := (div_eq_iff hπ.ne').1 hm
      have hwa : 1 ≤ Real.pi * a * w := by
        have h := (div_le_iff₀ (by positivity : 0 < 2 * β)).1
          (show w / (2 * β) ≤ a / 2 * Real.pi by rw [div_eq_mul_inv, ← heq]; exact hfull)
        have h' : w * 1 ≤ w * (Real.pi * a * w) := by
          rw [show w * (Real.pi * a * w) = a / 2 * Real.pi * (2 * β) by
            rw [← hw_sq]; ring]
          simpa using h
        exact le_of_mul_le_mul_left h' hw
      have hwi : w⁻¹ ≤ Real.pi * a := by
        rw [inv_eq_one_div]
        exact (div_le_iff₀ hw).2 hwa
      have hbi : β⁻¹ ≤ (Real.pi * a) ^ 2 := by
        rw [← hw_sq, ← inv_pow w 2]
        exact pow_le_pow_left₀ (inv_nonneg.mpr hw.le) hwi 2
      calc
        _ ≤ (Real.pi * a) ^ 2 := hbi
        _ ≤ 16 * a ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [Real.pi_lt_four, Real.pi_pos] : Real.pi ^ 2 ≤ 16) (sq_nonneg a)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    · exact (inv_le_one_of_one_le₀ (le_of_not_ge hβ1)).trans (by
        linarith [le_max_left (1 : ℝ) (a ^ 2)])

private theorem saddleMass_pos {β : ℝ} (hβ : 0 < β) : 0 < saddleMass β := by
  let f (θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hp (θ : ℝ) : 0 < f θ := by dsimp [f, radius]; positivity
  have hf : Continuous f := by
    apply Continuous.inv₀ (by dsimp [radius]; fun_prop)
    intro θ h
    exact (hp θ).ne' (by simp [f, h])
  unfold saddleMass spectralAverage
  exact div_pos (intervalIntegral.integral_pos Real.pi_pos hf.continuousOn
    (fun θ _ => (hp θ).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hp 0⟩) Real.pi_pos

private theorem saddleMass_strictAnti : StrictAntiOn saddleMass (Ioi 0) := by
  intro b hb c hc hbc
  let f (β θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hp {β : ℝ} (hβ : 0 < β) (θ : ℝ) :
      0 < radius β (2 - 2 * Real.cos θ) := by unfold radius; positivity
  have hf {β : ℝ} (hβ : 0 < β) : Continuous (f β) :=
    (by dsimp [radius]; fun_prop : Continuous fun θ => radius β (2 - 2 * Real.cos θ)).inv₀
      (fun θ => (hp hβ θ).ne')
  have hlt (θ : ℝ) : f c θ < f b θ := by
    apply inv_strictAnti₀ (hp hb θ)
    unfold radius
    exact Real.sqrt_lt_sqrt (by positivity) (add_lt_add_right
      (pow_lt_pow_left₀ hbc (le_of_lt hb) (by decide : 2 ≠ 0)) _)
  unfold saddleMass spectralAverage
  exact div_lt_div_of_pos_right
    (intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.pi_pos (hf hc).continuousOn (hf hb).continuousOn
      (fun θ _ => (hlt θ).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hlt 0⟩) Real.pi_pos

private theorem saddleMass_continuousOn {l u : ℝ} (hl : 0 < l) :
    ContinuousOn saddleMass (Icc l u) := by
  let f (β θ : ℝ) := (radius β (2 - 2 * Real.cos θ))⁻¹
  have hb (β : ℝ) (hβ : β ∈ Icc l u) (θ : ℝ) :
      l ≤ radius β (2 - 2 * Real.cos θ) := by
    unfold radius
    apply (Real.le_sqrt hl.le (by positivity)).2
    nlinarith [pow_le_pow_left₀ hl.le hβ.1 2, sq_nonneg (2 - 2 * Real.cos θ)]
  have hi : ContinuousOn (fun β => ∫ θ in 0..Real.pi, f β θ) (Icc l u) := by
    intro b hbi
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => l⁻¹)
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact ((show Continuous (fun θ => radius β (2 - 2 * Real.cos θ)) by
        dsimp [radius]; fun_prop).inv₀ (fun θ => (hl.trans_le (hb β hβ θ)).ne')).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact ae_of_all _ fun θ _ => by
        change |(radius β (2 - 2 * Real.cos θ))⁻¹| ≤ l⁻¹
        rw [abs_of_nonneg (inv_nonneg.mpr (hl.le.trans (hb β hβ θ)))]
        exact inv_anti₀ hl (hb β hβ θ)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun θ _ =>
        (ContinuousOn.inv₀ (by dsimp [radius]; fun_prop)
          (fun β hβ => (hl.trans_le (hb β hβ θ)).ne')) b hbi
  change ContinuousOn (fun β => (∫ θ in 0..Real.pi, f β θ) / Real.pi) (Icc l u)
  exact hi.div_const _

/-- Every positive window parameter has a unique positive saddle radius. -/
theorem existsUnique_saddle_radius {a : ℝ} (ha : 0 < a) :
    ∃! β : ℝ, 0 < β ∧ saddleMass β = a / 2 := by
  let l : ℝ := (32 * (1 + a) ^ 2)⁻¹
  let u : ℝ := max 1 (4 / a)
  have hl : 0 < l := by dsimp [l]; positivity
  have hpow : 1 ≤ (1 + a) ^ 2 := by
    nlinarith [sq_nonneg a]
  have hlu : l ≤ u := by
    exact (inv_le_one_of_one_le₀ (show 1 ≤ 32 * (1 + a) ^ 2 by linarith)).trans (le_max_left _ _)
  have hu : 0 < u := hl.trans_le hlu
  have hlval : a / 2 ≤ saddleMass l := by
    by_contra! h
    have hlmass := saddleMass_pos hl
    have hb := (saddle_radius_bounds hl (show 0 < 2 * saddleMass l by positivity)
      (show saddleMass l = (2 * saddleMass l) / 2 by ring)).2
    have hs : (2 * saddleMass l) ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hx : max 1 ((2 * saddleMass l) ^ 2) ≤ (1 + a) ^ 2 :=
      max_le hpow (hs.trans (by linarith))
    have hh := hb.trans (mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ 16 by norm_num))
    change ((32 * (1 + a) ^ 2)⁻¹)⁻¹ ≤ 16 * (1 + a) ^ 2 at hh
    rw [inv_inv] at hh
    linarith
  have huval : saddleMass u ≤ a / 2 := by
    have humass := saddleMass_pos hu
    have hb := (saddle_radius_bounds hu (show 0 < 2 * saddleMass u by positivity)
      (show saddleMass u = (2 * saddleMass u) / 2 by ring)).1
    have hh : 4 / a ≤ 2 / (2 * saddleMass u) := (le_max_right _ _).trans hb
    have he := (div_le_div_iff₀ ha (show 0 < 2 * saddleMass u by positivity)).1 hh
    linarith
  obtain ⟨β, hβ, he⟩ := intermediate_value_Icc' hlu (saddleMass_continuousOn hl) ⟨huval, hlval⟩
  have hp := hl.trans_le hβ.1
  refine ⟨β, ⟨hp, he⟩, ?_⟩
  intro γ hγ
  exact saddleMass_strictAnti.injOn hγ.1 hp (hγ.2.trans he.symm)

/-- The positive solution of the scalar saddle equation for a physical window. -/
def saddleRadius (a : ℝ) : ℝ :=
  if ha : 0 < a then (existsUnique_saddle_radius ha).exists.choose else 0

/-- The selected radius is positive and solves the saddle equation. -/
theorem saddleRadius_spec {a : ℝ} (ha : 0 < a) :
    0 < saddleRadius a ∧ saddleMass (saddleRadius a) = a / 2 := by
  simpa only [saddleRadius, dite_eq_left ha] using (existsUnique_saddle_radius ha).exists.choose_spec

/-- The continuous zero density, including the number of cells in the
equal-mass condition. This is the nonnegative formula at the saddle. -/
def saddleDensity (n : ℕ) (β t : ℝ) : ℝ :=
  (n : ℝ) * spectralAverage (fun r =>
    (radius β r)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2))) / Real.pi

/-- The saddle density satisfies the cap and has enough positive mass to form equal-mass bins. -/
theorem saddleDensity_spec (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) :
    ContinuousOn (saddleDensity n β) (Ici β) ∧
    (∀ t ∈ Ici β, 0 ≤ saddleDensity n β t ∧ saddleDensity n β t ≤ (n : ℝ) * a / (2 * Real.pi)) ∧
    (∀ t > β, 0 < saddleDensity n β t) ∧
    Tendsto (fun u => ∫ t in β..u, saddleDensity n β t) atTop atTop := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let F (t θ : ℝ) := (radius β (r θ))⁻¹ *
    (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + (r θ) ^ 2))
  let G (θ : ℝ) := (radius β (r θ))⁻¹
  have hgpos (θ : ℝ) : 0 < G θ := by dsimp [G, radius]; positivity
  have hgcap (θ : ℝ) : G θ ≤ β⁻¹ := by
    apply inv_anti₀ hβ
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by nlinarith [sq_nonneg (r θ)])
  have hgcont : Continuous G := by
    apply Continuous.inv₀ (by dsimp [radius, r]; fun_prop)
    intro x
    exact fun h => (hgpos x).ne' (by simp [G, h])
  have hnum (t : ℝ) (ht : β ≤ t) : Real.sqrt (t ^ 2 - β ^ 2) ≤ t :=
    (Real.sqrt_le_iff.mpr ⟨hβ.le.trans ht, by linarith [sq_nonneg β]⟩)
  have hpoint (t : ℝ) (ht : β ≤ t) (θ : ℝ) : 0 ≤ F t θ ∧ F t θ ≤ G θ := by
    have ht0 := hβ.trans_le ht
    have hr : t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2
        (by nlinarith [mul_le_mul_of_nonneg_left (hnum t ht) ht0.le, sq_nonneg (r θ)])
    exact ⟨mul_nonneg (hgpos θ).le (div_nonneg (mul_nonneg ht0.le (Real.sqrt_nonneg _))
      (by positivity)), mul_le_of_le_one_right (hgpos θ).le hr⟩
  have hFcont (t : ℝ) (ht : β ≤ t) : Continuous (F t) := by
    apply hgcont.mul
    apply continuous_const.div (by dsimp [r]; fun_prop)
    intro x
    have ht0 := hβ.trans_le ht
    positivity
  have hFpar (θ : ℝ) : ContinuousOn (fun t => F t θ) (Ici β) := by
    apply continuousOn_const.mul
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have ht0 := hβ.trans_le ht
    positivity
  have hc : ContinuousOn (saddleDensity n β) (Ici β) := by
    have hloc : ContinuousOn (fun t => ∫ θ in 0..Real.pi, F t θ) (Ici β) := by
      intro x hx
      apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ => β⁻¹)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hFcont t ht).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact ae_of_all _ fun θ _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hpoint t ht θ).1]
          exact (hpoint t ht θ).2.trans (hgcap θ)
      · exact intervalIntegrable_const
      · exact ae_of_all _ fun θ _ => hFpar θ x hx
    change ContinuousOn (fun t => (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi) (Ici β)
    exact ((hloc.div_const _).const_mul _).div_const _
  have hG : (∫ θ in 0..Real.pi, G θ) / Real.pi = a / 2 := hs
  have hπ : 0 < Real.pi := Real.pi_pos
  have hbounds (t : ℝ) (ht : t ∈ Ici β) :
      0 ≤ saddleDensity n β t ∧ saddleDensity n β t ≤ (n : ℝ) * a / (2 * Real.pi) := by
    have huv := intervalIntegral.integral_mono_on (μ := volume) hπ.le
      ((hFcont t ht).intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
      (fun θ _ => (hpoint t ht θ).2)
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume) hπ.le (fun θ _ => (hpoint t ht θ).1)
    change 0 ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi ∧ _
    constructor
    · positivity
    · change (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi ≤ _
      calc
        _ ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, G θ) / Real.pi) / Real.pi := by gcongr
        _ = _ := by rw [hG]; ring
  have hpos (t : ℝ) (ht : β < t) : 0 < saddleDensity n β t := by
    have ht0 := hβ.trans ht
    have hdiff : 0 < t ^ 2 - β ^ 2 := by nlinarith [mul_pos (sub_pos.mpr ht) (add_pos ht0 hβ)]
    have hfpos (θ : ℝ) : 0 < F t θ := by
      exact mul_pos (hgpos θ) (div_pos (mul_pos ht0 (Real.sqrt_pos.2 hdiff)) (by positivity))
    have hp := intervalIntegral.integral_pos hπ (hFcont t ht.le).continuousOn
      (fun θ _ => (hfpos θ).le) ⟨0, ⟨le_rfl, hπ.le⟩, hfpos 0⟩
    change 0 < (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi
    exact div_pos (mul_pos hn (div_pos hp hπ)) hπ
  refine ⟨hc, hbounds, hpos, ?_⟩
  let K := max (2 * β) 4
  have hβK : β ≤ K := by dsimp [K]; linarith [le_max_left (2 * β) (4 : ℝ)]
  let m := (n : ℝ) * a / (8 * Real.pi)
  have hm : 0 < m := by dsimp [m]; positivity
  have hflo (t : ℝ) (ht : K ≤ t) : m ≤ saddleDensity n β t := by
    have htβ : 2 * β ≤ t := (le_max_left _ _).trans ht
    have ht4 : 4 ≤ t := (le_max_right _ _).trans ht
    have ht0 : 0 < t := by positivity [hβ.trans_le (hβK.trans ht)]
    have hlo : t / 2 ≤ Real.sqrt (t ^ 2 - β ^ 2) := by
      apply (Real.le_sqrt (by positivity) (by nlinarith)).2
      nlinarith [pow_le_pow_left₀ (show 0 ≤ 2 * β by positivity) htβ 2]
    have hKern (θ : ℝ) : G θ / 4 ≤ F t θ := by
      have hr0 : 0 ≤ r θ := by dsimp [r]; linarith [Real.cos_le_one θ]
      have hr4 : r θ ≤ 4 := by dsimp [r]; linarith [Real.neg_one_le_cos θ]
      have hs := pow_le_pow_left₀ hr0 (hr4.trans ht4) 2
      have h := (le_div_iff₀ (by positivity : 0 < t ^ 2 + r θ ^ 2)).2
        (show 1 / 4 * (t ^ 2 + r θ ^ 2) ≤ t * Real.sqrt (t ^ 2 - β ^ 2) by
          nlinarith [mul_le_mul_of_nonneg_left hlo ht0.le])
      simpa only [div_eq_mul_inv, one_mul, F] using mul_le_mul_of_nonneg_left h (hgpos θ).le
    have hI := intervalIntegral.integral_mono_on (μ := volume) hπ.le ((hgcont.div_const _).intervalIntegrable _ _)
      ((hFcont t (hβK.trans ht)).intervalIntegrable _ _) (fun θ _ => hKern θ)
    have hloI : (∫ θ in 0..Real.pi, G θ) / 4 ≤ ∫ θ in 0..Real.pi, F t θ := by
      simpa only [intervalIntegral.integral_div] using hI
    change _ ≤ (n : ℝ) * ((∫ θ in 0..Real.pi, F t θ) / Real.pi) / Real.pi
    calc
      _ = (n : ℝ) * (((∫ θ in 0..Real.pi, G θ) / 4) / Real.pi) / Real.pi := by
        rw [show ((∫ θ in 0..Real.pi, G θ) / 4) / Real.pi =
          ((∫ θ in 0..Real.pi, G θ) / Real.pi) / 4 by ring, hG]
        dsimp [m]
        ring
      _ ≤ _ := by gcongr
  have hb : 0 ≤ ∫ x in β..K, saddleDensity n β x :=
    intervalIntegral.integral_nonneg hβK (fun x hx => (hbounds x (mem_Ici.mpr hx.1)).1)
  apply tendsto_atTop.2
  intro R
  filter_upwards [eventually_ge_atTop (max K (K + R / m))] with t ht
  have hKt := (le_max_left _ _).trans ht
  have hconst := intervalIntegral.integral_mono_on (μ := volume) hKt
    (intervalIntegrable_const (c := m))
    ((hc.mono (show Icc K t ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr (hβK.trans hx.1))).intervalIntegrable_of_Icc hKt)
    (fun x hx => hflo x hx.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hc.mono (show Icc β K ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr hx.1)).intervalIntegrable_of_Icc hβK)
    ((hc.mono (show Icc K t ⊆ Ici β from fun _ hx =>
      mem_Ici.mpr (hβK.trans hx.1))).intervalIntegrable_of_Icc hKt)
  have hR := (div_le_iff₀ hm).1 (show R / m ≤ t - K by
    linarith [(le_max_right K (K + R / m)).trans ht])
  linarith

/-- The logarithmic sum entering the real and imaginary saddle identities. -/
def saddleLogAverage (β q : ℝ) : ℝ :=
  spectralAverage (fun r => Real.log (radius β q + radius β r))

/-- The logarithmic angular average increases with the nonnegative radial argument. -/
theorem saddleLogAverage_mono {β : ℝ} (hβ : 0 < β) {u v : ℝ}
    (hu : 0 ≤ u) (h : u ≤ v) : saddleLogAverage β u ≤ saddleLogAverage β v := by
  let g (q θ : ℝ) := Real.log (radius β q + radius β (2 - 2 * Real.cos θ))
  have hp (q θ : ℝ) : 0 < radius β q + radius β (2 - 2 * Real.cos θ) := by
    unfold radius
    positivity
  have hg (q : ℝ) : Continuous (g q) := by
    apply Continuous.log (by dsimp [radius]; fun_prop)
    exact fun θ => (hp q θ).ne'
  have hR : radius β u ≤ radius β v := by
    unfold radius
    exact Real.sqrt_le_sqrt (add_le_add_left (pow_le_pow_left₀ hu h 2) _)
  unfold saddleLogAverage spectralAverage
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  exact intervalIntegral.integral_mono_on Real.pi_pos.le
    ((hg u).intervalIntegrable _ _) ((hg v).intervalIntegrable _ _)
    (fun θ _ => Real.log_le_log (hp u θ) (add_le_add_left hR _))

private theorem hasDerivAt_saddleRadiusFunction {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    HasDerivAt (radius β) (y / radius β y) y := by
  have h := ((hasDerivAt_pow 2 y).add_const (β ^ 2)).sqrt
    (show y ^ 2 + β ^ 2 ≠ 0 by positivity)
  unfold radius
  convert h using 1
  norm_num
  ring

private theorem hasDerivAt_saddleLogAverage {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    HasDerivAt (saddleLogAverage β)
      (y / radius β y * spectralAverage (fun r => (radius β y + radius β r)⁻¹)) y := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let F (v θ : ℝ) := Real.log (radius β v + radius β (r θ))
  let G (v θ : ℝ) := (radius β v + radius β (r θ))⁻¹
  let F' (v θ : ℝ) := (v / radius β v) * G v θ
  let μ := volume.restrict (Ioc (0 : ℝ) Real.pi)
  have hb (v : ℝ) : β ≤ radius β v := by
    unfold radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg v])
  have hp (v θ : ℝ) : 0 < radius β v + radius β (r θ) := by
    exact add_pos_of_pos_of_nonneg (hβ.trans_le (hb v)) (Real.sqrt_nonneg _)
  have hc (v : ℝ) : Continuous (F v) := by
    apply Continuous.log (by dsimp [r, radius]; fun_prop)
    exact fun θ => (hp v θ).ne'
  have hcG (v : ℝ) : Continuous (G v) := by
    apply Continuous.inv₀ (by dsimp [r, radius]; fun_prop)
    exact fun θ => (hp v θ).ne'
  have hf' (v θ : ℝ) : HasDerivAt (fun u => F u θ) (F' v θ) v := by
    simpa only [F, F', G, div_eq_mul_inv] using
      ((hasDerivAt_saddleRadiusFunction hβ v).add_const (radius β (r θ))).log (hp v θ).ne'
  have hbound (v θ : ℝ) : ‖F' v θ‖ ≤ β⁻¹ := by
    have hv : |v| ≤ radius β v := by
      unfold radius
      exact (Real.le_sqrt (abs_nonneg v) (by positivity)).2 (by nlinarith [sq_abs v])
    have hg : G v θ ≤ β⁻¹ :=
      inv_anti₀ hβ ((hb v).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    rw [Real.norm_eq_abs, show F' v θ = (v / radius β v) * G v θ from rfl,
      abs_mul, abs_div, abs_of_pos (hβ.trans_le (hb v)),
      abs_of_nonneg (inv_nonneg.mpr (hp v θ).le)]
    exact (mul_le_of_le_one_left (inv_nonneg.mpr (hp v θ).le)
      ((div_le_one (hβ.trans_le (hb v))).2 hv)).trans hg
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := univ) univ_mem
    (.of_forall fun v => (hc v).aestronglyMeasurable)
    ((hc y).intervalIntegrable (μ := volume) 0 Real.pi).1
    ((hcG y).const_mul (y / radius β y)).aestronglyMeasurable
    (ae_of_all μ fun θ v _ => hbound v θ)
    (integrable_const β⁻¹)
    (ae_of_all μ fun θ v _ => hf' v θ)).2
  have h := hd.div_const Real.pi
  change HasDerivAt (fun v => (∫ θ in 0..Real.pi, F v θ) / Real.pi) _ y
  rw [show (fun v => (∫ θ in 0..Real.pi, F v θ) / Real.pi) =
    (fun v => (∫ θ, F v θ ∂μ) / Real.pi) by
      funext v
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]]
  simpa only [spectralAverage, F', G, μ, r, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_const_mul, mul_div_assoc] using h

private theorem cauchy_half {A : ℝ} (hA : 0 < A) :
    Integrable (fun s : ℝ => (s ^ 2 + A ^ 2)⁻¹) ∧
      (∫ s in Ioi (0 : ℝ), (s ^ 2 + A ^ 2)⁻¹) = Real.pi / (2 * A) := by
  let f (s : ℝ) := (1 + s ^ 2)⁻¹
  have hA' : 0 < A⁻¹ := inv_pos.mpr hA
  have he (s : ℝ) : (s ^ 2 + A ^ 2)⁻¹ = (A ^ 2)⁻¹ * f (A⁻¹ * s) := by
    have hs : 0 < s ^ 2 + A ^ 2 := by positivity
    have hf : 0 < 1 + (A⁻¹ * s) ^ 2 := by positivity
    dsimp [f]
    field_simp [hA.ne', hs.ne', hf.ne']
    <;> ring
  simp_rw [he]
  have hi := (integrable_inv_one_add_mul_sq hA'.ne').const_mul (A ^ 2)⁻¹
  refine ⟨hi, ?_⟩
  rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hA', mul_zero, inv_inv, smul_eq_mul]
  have h := integral_Ioi_inv_one_add_sq (i := 0)
  rw [Real.arctan_zero, sub_zero] at h
  change (A ^ 2)⁻¹ * (A * ∫ s in Ioi (0 : ℝ), f s) = _
  rw [show (∫ s in Ioi (0 : ℝ), f s) = Real.pi / 2 from h]
  field_simp

private theorem cauchy_pair_half {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    (∫ s in Ioi (0 : ℝ), s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))) =
      Real.pi / (2 * (A + R)) := by
  let C := A * R
  let g (s : ℝ) := s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))
  let h (s : ℝ) := C / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))
  have hC : 0 < C := mul_pos hA hR
  have hg (s : ℝ) : 0 ≤ g s := by dsimp [g]; positivity
  have hh (s : ℝ) : 0 ≤ h s := by dsimp [h, C]; positivity
  have hplus (s : ℝ) :
      g s + h s = (A * (s ^ 2 + A ^ 2)⁻¹ + R * (s ^ 2 + R ^ 2)⁻¹) / (A + R) := by
    dsimp [g, h, C]
    field_simp [show 0 < s ^ 2 + A ^ 2 by positivity, show 0 < s ^ 2 + R ^ 2 by positivity,
      (add_pos hA hR).ne']
    ring
  have hi : Integrable (fun s => g s + h s) := by
    simp_rw [hplus, div_eq_mul_inv]
    exact (((cauchy_half hA).1.const_mul A).add ((cauchy_half hR).1.const_mul R)).mul_const _
  have hgc : Continuous g := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    positivity
  have hhc : Continuous h := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    positivity
  have hgi : Integrable g := hi.mono' hgc.aestronglyMeasurable
    (.of_forall fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg s)] using hh s)
  have hhi : Integrable h := hi.mono' hhc.aestronglyMeasurable
    (.of_forall fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (hh s)] using hg s)
  let f (s : ℝ) := C * s⁻¹
  have hf : Set.InjOn f (Ioi 0) := by
    intro u _ v _ huv
    exact inv_injective (mul_left_cancel₀ hC.ne' huv)
  have himage : f '' Ioi 0 = Ioi 0 := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mul_pos hC (inv_pos.mpr hu)
    · intro hs
      refine ⟨C * s⁻¹, mul_pos hC (inv_pos.mpr hs), ?_⟩
      dsimp [f]
      field_simp [hC.ne', (show 0 < s from hs).ne']
  have hDeriv (s : ℝ) (hs : s ∈ Ioi 0) :
      HasDerivWithinAt f (C * (-(s ^ 2)⁻¹)) (Ioi 0) s :=
    ((hasDerivAt_inv (show 0 < s from hs).ne').const_mul C).hasDerivWithinAt
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hDeriv hf g
  rw [himage] at he
  have hsub : (∫ s in Ioi (0 : ℝ), g s) = ∫ s in Ioi (0 : ℝ), h s := by
    refine he.trans (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_)
    have hs' : 0 < s := hs
    have hCnonneg : 0 ≤ C * (s ^ 2)⁻¹ := by positivity
    rw [mul_neg, abs_neg, abs_of_nonneg hCnonneg, smul_eq_mul]
    dsimp [f, g, h, C]
    field_simp [hs'.ne', hA.ne', hR.ne',
      show 0 < s ^ 2 + A ^ 2 by positivity, show 0 < s ^ 2 + R ^ 2 by positivity,
      show 0 < (A * R * s⁻¹) ^ 2 + A ^ 2 by positivity,
      show 0 < (A * R * s⁻¹) ^ 2 + R ^ 2 by positivity]
    <;> ring
  have hm : (∫ s in Ioi (0 : ℝ), g s + h s) = Real.pi / (A + R) := by
    simp_rw [hplus, div_eq_mul_inv]
    rw [integral_mul_const, integral_add ((cauchy_half hA).1.const_mul A).integrableOn
      ((cauchy_half hR).1.const_mul R).integrableOn,
      integral_const_mul, integral_const_mul, (cauchy_half hA).2, (cauchy_half hR).2]
    field_simp [hA.ne', hR.ne', (add_pos hA hR).ne']
    <;> ring
  rw [integral_add hgi.integrableOn hhi.integrableOn, ← hsub] at hm
  change (∫ s in Ioi (0 : ℝ), g s) = _
  apply (eq_div_iff (by positivity : 2 * (A + R) ≠ 0)).2
  apply (eq_div_iff (add_pos hA hR).ne').1 at hm
  linarith

private theorem saddle_radial_resolvent {β : ℝ} (hβ : 0 < β) (y r : ℝ) :
    (∫ t in Ioi β,
      (2 * y / (t ^ 2 + y ^ 2)) *
        ((radius β r)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2)))) =
      Real.pi * y / (radius β r * (radius β y + radius β r)) := by
  let A := radius β y
  let R := radius β r
  let f := radius β
  have hA : 0 < A := by dsimp [A, radius]; positivity
  have hR : 0 < R := by dsimp [R, radius]; positivity
  have hp (s : ℝ) : 0 < f s := by dsimp [f, radius]; positivity
  have hsq (s : ℝ) : f s ^ 2 = s ^ 2 + β ^ 2 :=
    Real.sq_sqrt (by positivity)
  have ha' : A ^ 2 = y ^ 2 + β ^ 2 := hsq y
  have hr' : R ^ 2 = r ^ 2 + β ^ 2 := hsq r
  have hf : Set.InjOn f (Ioi 0) := by
    intro u hu v hv h
    exact (sq_eq_sq₀ (le_of_lt hu) (le_of_lt hv)).1 (by
      linarith [hsq u, hsq v, congrArg (fun z : ℝ => z ^ 2) h])
  have himage : f '' Ioi 0 = Ioi β := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (sq_lt_sq₀ hβ.le (hp s).le).1 (by
        rw [hsq]
        linarith [sq_pos_of_pos (show 0 < s from hs)])
    · intro ht
      have ht0 : 0 < t := hβ.trans ht
      have ht2 : β ^ 2 < t ^ 2 := (sq_lt_sq₀ hβ.le ht0.le).2 ht
      refine ⟨Real.sqrt (t ^ 2 - β ^ 2), Real.sqrt_pos.mpr (sub_pos.mpr ht2), ?_⟩
      dsimp [f, radius]
      rw [Real.sq_sqrt (by linarith), sub_add_cancel, Real.sqrt_sq ht0.le]
  have hDeriv (s : ℝ) (_ : s ∈ Ioi 0) : HasDerivWithinAt f (s / f s) (Ioi 0) s :=
    (hasDerivAt_saddleRadiusFunction hβ s).hasDerivWithinAt
  let Q (t : ℝ) := (2 * y / (t ^ 2 + y ^ 2)) *
    (R⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r ^ 2)))
  have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hDeriv hf Q
  rw [himage] at hc
  calc
    _ = ∫ s in Ioi (0 : ℝ), |s / f s| • Q (f s) := hc
    _ = ∫ s in Ioi (0 : ℝ), (2 * y / R) *
        (s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs' : 0 < s := hs
      change |s / f s| • Q (f s) = (2 * y / R) *
        (s ^ 2 / ((s ^ 2 + A ^ 2) * (s ^ 2 + R ^ 2)))
      rw [abs_of_nonneg (div_nonneg hs'.le (hp s).le), smul_eq_mul]
      have hsqrt : Real.sqrt (f s ^ 2 - β ^ 2) = s := by
        rw [hsq, add_sub_cancel_right, Real.sqrt_sq hs'.le]
      dsimp only [Q]
      rw [hsqrt, hsq, ha', hr']
      have hz : 0 < s ^ 2 + β ^ 2 + y ^ 2 := by positivity
      have hz' : 0 < s ^ 2 + β ^ 2 + r ^ 2 := by positivity
      have h₁ : s ^ 2 + (y ^ 2 + β ^ 2) = s ^ 2 + β ^ 2 + y ^ 2 := by ring
      have h₂ : s ^ 2 + (r ^ 2 + β ^ 2) = s ^ 2 + β ^ 2 + r ^ 2 := by ring
      rw [h₁, h₂]
      field_simp [(hp s).ne', hR.ne', hz.ne', hz'.ne']
    _ = _ := by
      rw [integral_const_mul, cauchy_pair_half hA hR]
      change (2 * y / R) * (Real.pi / (2 * (A + R))) = Real.pi * y / (R * (A + R))
      field_simp [hR.ne', (add_pos hA hR).ne']

private theorem saddleDensity_resolvent (n : ℕ) {a β : ℝ} (hβ : 0 < β)
    (hs : saddleMass β = a / 2) (y : ℝ) :
    (∫ t in Ioi β, (2 * y / (t ^ 2 + y ^ 2)) * saddleDensity n β t) =
      (n : ℝ) * (y / radius β y) *
        (a / 2 - spectralAverage (fun r => (radius β y + radius β r)⁻¹)) := by
  let r (θ : ℝ) := 2 - 2 * Real.cos θ
  let A := radius β y
  let R (θ : ℝ) := radius β (r θ)
  let H (t θ : ℝ) := (R θ)⁻¹ * (t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2))
  let Q (t θ : ℝ) := (2 * y / (t ^ 2 + y ^ 2)) * H t θ
  let μ := volume.restrict (Ioi β)
  let ν := volume.restrict (Ioc (0 : ℝ) Real.pi)
  let N : ℝ := n
  have hA : 0 < A := by dsimp [A, radius]; positivity
  have hR (θ : ℝ) : β ≤ R θ := by
    unfold R radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg (r θ)])
  have hRp (θ : ℝ) : 0 < R θ := hβ.trans_le (hR θ)
  have hcap (t θ : ℝ) (ht : β < t) : 0 ≤ H t θ ∧ H t θ ≤ β⁻¹ := by
    have ht0 := hβ.trans ht
    have hS : Real.sqrt (t ^ 2 - β ^ 2) ≤ t :=
      Real.sqrt_le_iff.mpr ⟨ht0.le, by linarith [sq_nonneg β]⟩
    have hfactor : t * Real.sqrt (t ^ 2 - β ^ 2) / (t ^ 2 + r θ ^ 2) ≤ 1 := by
      exact (div_le_iff₀ (by positivity)).2
        (by nlinarith [mul_le_mul_of_nonneg_left hS ht0.le, sq_nonneg (r θ)])
    exact ⟨mul_nonneg (inv_nonneg.mpr (hRp θ).le) (by positivity),
      (mul_le_of_le_one_right (inv_nonneg.mpr (hRp θ).le) hfactor).trans (inv_anti₀ hβ (hR θ))⟩
  have hmeas : AEStronglyMeasurable (Function.uncurry Q) (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    dsimp [Function.uncurry, Q, H, R, r, radius]
    fun_prop
  have hinv : Integrable (fun t : ℝ => 2 * |y| * β⁻¹ * (t ^ 2)⁻¹) μ := by
    exact (integrableOn_inv_sq hβ).const_mul _
  have hmajor : Integrable (fun x : ℝ × ℝ => 2 * |y| * β⁻¹ * (x.1 ^ 2)⁻¹) (μ.prod ν) := by
    exact hinv.comp_fst ν
  have hi : Integrable (Function.uncurry Q) (μ.prod ν) := by
    apply hmajor.mono' hmeas
    have ht : ∀ᵐ x : ℝ × ℝ ∂μ.prod ν, β < x.1 := by
      apply (Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × ℝ => β < x.1)
        (measurable_fst measurableSet_Ioi)).2
      exact (ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β))).mono
        (fun t ht => ae_of_all ν fun _ => ht)
    filter_upwards [ht] with x hx
    have ht0 := hβ.trans hx
    have hcc := hcap x.1 x.2 hx
    change |(2 * y / (x.1 ^ 2 + y ^ 2)) * H x.1 x.2| ≤ _
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ x.1 ^ 2 + y ^ 2), abs_of_nonneg hcc.1]
    calc
      _ ≤ (2 * |y| / x.1 ^ 2) * β⁻¹ :=
        mul_le_mul (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by linarith [sq_nonneg y])) hcc.2 hcc.1 (by positivity)
      _ = _ := by ring
  have hfub := integral_integral_swap hi
  have houter :
      (∫ t, (2 * y / (t ^ 2 + y ^ 2)) * saddleDensity n β t ∂μ) =
        N / Real.pi ^ 2 * ∫ θ, (∫ t, Q t θ ∂μ) ∂ν := by
    rw [← hfub, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [saddleDensity, spectralAverage, Q, H, ν, r, R, N]
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_const_mul]
    ring
  have hintegral : (∫ θ, (∫ t, Q t θ ∂μ) ∂ν) =
      ∫ θ, Real.pi * y / (R θ * (A + R θ)) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun θ => saddle_radial_resolvent hβ y (r θ)
  have hsplit (θ : ℝ) : Real.pi * y / (R θ * (A + R θ)) =
      Real.pi * (y / A) * ((R θ)⁻¹ - (A + R θ)⁻¹) := by
    field_simp [hA.ne', (hRp θ).ne', (add_pos hA (hRp θ)).ne']
    ring
  have hRc : Continuous R := by dsimp [R, r, radius]; fun_prop
  have hiR : Integrable (fun θ => (R θ)⁻¹) ν :=
    (hRc.inv₀ fun θ => (hRp θ).ne').intervalIntegrable (μ := volume) 0 Real.pi |>.1
  have hiA : Integrable (fun θ => (A + R θ)⁻¹) ν :=
    ((continuous_const.add hRc).inv₀ fun θ => (add_pos hA (hRp θ)).ne').intervalIntegrable
      (μ := volume) 0 Real.pi |>.1
  have hs' : (∫ θ, (R θ)⁻¹ ∂ν) / Real.pi = a / 2 := by
    simpa only [saddleMass, spectralAverage, intervalIntegral.integral_of_le Real.pi_pos.le, ν, R, r]
      using hs
  change (∫ t, _ ∂μ) = _
  rw [houter, hintegral]
  simp_rw [hsplit]
  rw [integral_const_mul, integral_sub hiR hiA, ← hs']
  unfold spectralAverage
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  let U := ∫ θ, (R θ)⁻¹ ∂ν
  let V := ∫ θ, (A + R θ)⁻¹ ∂ν
  change N / Real.pi ^ 2 * (Real.pi * (y / A) * (U - V)) =
    N * (y / A) * (U / Real.pi - V / Real.pi)
  field_simp [Real.pi_ne_zero, hA.ne']

/-- The weighted resolvent evaluates the imaginary potential at the continuum saddle. -/
theorem imaginaryPotential_eval_at_saddle (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) :
    ∀ y ≥ 0, imaginaryPotential β (saddleDensity n β) y =
      (n : ℝ) * (a / 2 * (radius β y - β) -
        (saddleLogAverage β y - saddleLogAverage β 0)) := by
  obtain ⟨hc, hcap, _, _⟩ := saddleDensity_spec n hn ha hβ hs
  let F := imaginaryPotential β (saddleDensity n β)
  let G (v : ℝ) := (n : ℝ) * (a / 2 * (radius β v - β) -
        (saddleLogAverage β v - saddleLogAverage β 0))
  let D (v : ℝ) := (n : ℝ) * (v / radius β v) *
    (a / 2 - spectralAverage (fun r => (radius β v + radius β r)⁻¹))
  have hf (v : ℝ) : HasDerivAt F (D v) v := by
    dsimp only [D, F]
    rw [← saddleDensity_resolvent n hβ hs v]
    exact hasDerivAt_imaginaryPotential hβ hc hcap v
  have hg (v : ℝ) : HasDerivAt G (D v) v := by
    have hR := (hasDerivAt_saddleRadiusFunction hβ v).sub_const β
    have hJ := (hasDerivAt_saddleLogAverage hβ v).sub_const (saddleLogAverage β 0)
    convert ((hR.const_mul (a / 2)).sub hJ).const_mul (n : ℝ) using 1
    dsimp [D]
    ring
  have h0 : F 0 = G 0 := by
    simp [F, G, imaginaryPotential, radius, Real.sqrt_sq hβ.le]
  intro y hy
  exact eq_of_has_deriv_right_eq (fun v _ => (hf v).hasDerivWithinAt)
    (fun v _ => (hg v).hasDerivWithinAt)
    (fun v _ => (hf v).continuousAt.continuousWithinAt)
    (fun v _ => (hg v).continuousAt.continuousWithinAt) h0 y ⟨hy, le_rfl⟩

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
