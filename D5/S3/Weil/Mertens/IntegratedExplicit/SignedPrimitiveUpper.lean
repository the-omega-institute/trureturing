/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimitiveUpper
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SignedPrimitiveUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded centered signed primitive controls negative tail mass at power one sixth. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! Pointwise and integrated bounds from a bounded centered signed primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped Interval Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper

noncomputable section

private theorem integral_reciprocal (g : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, g u⁻¹ / u ^ 2) = ∫ x in b⁻¹..a⁻¹, g x := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := a) (b := b) (f := fun u : ℝ => u⁻¹) (f' := fun u : ℝ => -(u ^ 2)⁻¹)
    (g := g)
    (continuousOn_inv₀.mono (by
      rw [uIcc_of_le hab]
      exact fun u hu => by simpa using (ha.trans_le hu.1).ne'))
    (by
      rw [min_eq_left hab, max_eq_right hab]
      exact fun u hu => hasDerivAt_inv (ha.trans hu.1).ne')
    (fun u _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u)))
  calc
    (∫ u in a..b, g u⁻¹ / u ^ 2) =
        -(∫ u in a..b, (g ∘ fun v : ℝ => v⁻¹) u * (-(u ^ 2)⁻¹)) := by
          rw [← intervalIntegral.integral_neg]
          exact intervalIntegral.integral_congr (fun u _ => by
            simp [Function.comp_def, div_eq_mul_inv])
    _ = ∫ x in b⁻¹..a⁻¹, g x := by
      rw [hsub, intervalIntegral.integral_symm b⁻¹ a⁻¹, neg_neg]

/-- Remove the reciprocal weight using the interval primitive with its right endpoint fixed. -/
private theorem integral_unweighted_lower {F : ℝ → ℝ} {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hbound : ∀ v ∈ Icc a b, -C ≤ ∫ u in v..b, F u * u ^ (-(3 / 2) : ℝ)) :
    -C * b ^ (3 / 2 : ℝ) ≤ ∫ u in a..b, F u := by
  let w (u : ℝ) := F u * u ^ (-(3 / 2) : ℝ)
  let J (v : ℝ) := ∫ u in v..b, w u
  let L (u : ℝ) := u ^ (3 / 2 : ℝ)
  let L' (u : ℝ) := (3 / 2 : ℝ) * u ^ (1 / 2 : ℝ)
  have hpos : ∀ u ∈ Icc a b, 0 < u := fun u hu => ha.trans_le hu.1
  have hw : ContinuousOn w [[a, b]] := by
    rw [uIcc_of_le hab]
    exact hF.mul (fun u hu =>
      (Real.continuousAt_rpow_const u (-(3 / 2) : ℝ)
        (Or.inl (hpos u hu).ne')).continuousWithinAt)
  have hJ : ContinuousOn J [[a, b]] :=
    intervalIntegral.continuousOn_primitive_interval_left hw.integrableOn_Icc
  have hL : ContinuousOn L [[a, b]] :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn
  have hL' : ContinuousOn L' [[a, b]] :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousOn.const_mul _
  have hLd : ∀ u : ℝ, HasDerivAt L (L' u) u := by
    intro u
    simpa only [L, L', show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using
      (Real.hasDerivAt_rpow_const (x := u) (p := 3 / 2) (Or.inr (by norm_num)))
  have hJd : ∀ v ∈ Ioo (min a b) (max a b), HasDerivAt J (-w v) v := by
    intro v hv
    rw [min_eq_left hab, max_eq_right hab] at hv
    have hvb : v ≤ b := hv.2.le
    have hsub : [[v, b]] ⊆ [[a, b]] := by
      rw [uIcc_of_le hvb, uIcc_of_le hab]
      exact Icc_subset_Icc_left hv.1.le
    have hwv : ContinuousAt w v :=
      (hw v (hsub left_mem_uIcc)).continuousAt (by
        rw [uIcc_of_le hab]
        exact Icc_mem_nhds hv.1 hv.2)
    have hwOpen : ContinuousOn w (Ioo a b) :=
      hw.mono (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self)
    have hmeas : StronglyMeasurableAtFilter w (𝓝 v) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hwOpen v hv
    exact intervalIntegral.integral_hasDerivAt_left (hw.mono hsub).intervalIntegrable hmeas hwv
  have hproduct : ∀ u ∈ [[a, b]], L u * (-w u) = -F u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hpow : L u * u ^ (-(3 / 2) : ℝ) = 1 := by
      change u ^ (3 / 2 : ℝ) * u ^ (-(3 / 2) : ℝ) = 1
      rw [← Real.rpow_add (hpos u hu), add_neg_cancel, Real.rpow_zero]
    change L u * (-(F u * u ^ (-(3 / 2) : ℝ))) = -F u
    calc
      _ = -F u * (L u * u ^ (-(3 / 2) : ℝ)) := by ring
      _ = _ := by rw [hpow, mul_one]
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hL hJ (fun u _ => hLd u) hJd hL'.intervalIntegrable hw.neg.intervalIntegrable
  have hLeft : IntervalIntegrable (fun x => L' x * J x) volume a b :=
    (hL'.mul hJ).intervalIntegrable
  have hRight : IntervalIntegrable (fun x => L x * -w x) volume a b :=
    (hL.mul hw.neg).intervalIntegrable
  rw [intervalIntegral.integral_add hLeft hRight, intervalIntegral.integral_congr hproduct,
    intervalIntegral.integral_neg] at hparts
  have hJb : J b = 0 := intervalIntegral.integral_same
  rw [hJb, mul_zero, zero_sub] at hparts
  have hL'int : (∫ u in a..b, L' u) = L b - L a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hLd u) hL'.intervalIntegrable
  have hmono : (∫ u in a..b, (-C) * L' u) ≤ ∫ u in a..b, L' u * J u := by
    apply intervalIntegral.integral_mono_on hab (hL'.const_mul _).intervalIntegrable hLeft
    intro u hu
    change -C * L' u ≤ L' u * J u
    rw [mul_comm (L' u)]
    exact mul_le_mul_of_nonneg_right (hbound u hu)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (hpos u hu).le _))
  rw [intervalIntegral.integral_const_mul, hL'int] at hmono
  have hend : -C * L a ≤ L a * J a := by
    rw [mul_comm (L a) (J a)]
    exact mul_le_mul_of_nonneg_right (hbound a ⟨le_rfl, hab⟩) (by dsimp [L]; positivity)
  change -C * L b ≤ _
  linarith only [hparts, hmono, hend]

private theorem concave_log_correction {r d : ℝ} (hr : 0 < r) (hd : d ≤ r / 2) :
    ConcaveOn ℝ (Icc (r - d) (r + d))
      (fun u => -Real.log u - (2 / r ^ 2) * u ^ 2) := by
  let G (u : ℝ) := -Real.log u - (2 / r ^ 2) * u ^ 2
  let G' (u : ℝ) := -u⁻¹ - (2 / r ^ 2) * (2 * u)
  have hd1 : ∀ u : ℝ, u ≠ 0 → HasDerivAt G (G' u) u := by
    intro u hu
    have h := (Real.hasDerivAt_log hu).neg.sub ((hasDerivAt_pow 2 u).const_mul (2 / r ^ 2))
    have heq : (-Real.log - (fun y : ℝ => 2 / r ^ 2 * y ^ 2)) = G := rfl
    rw [heq] at h
    norm_num [G'] at h ⊢
    exact h
  have hd2 : ∀ u : ℝ, u ≠ 0 → HasDerivAt (deriv G) ((u ^ 2)⁻¹ - 4 / r ^ 2) u := by
    intro u hu
    have hlin : HasDerivAt (fun v : ℝ => (2 / r ^ 2) * (2 * v)) (4 / r ^ 2) u := by
      convert (((hasDerivAt_id u).const_mul 2).const_mul (2 / r ^ 2)) using 1 <;>
        simp [id] <;> ring
    have hG' : HasDerivAt G' ((u ^ 2)⁻¹ - 4 / r ^ 2) u := by
      have h := (hasDerivAt_inv hu).neg.sub hlin
      have heq : (-(fun y : ℝ => y⁻¹) - (fun v : ℝ => 2 / r ^ 2 * (2 * v))) = G' := rfl
      simpa only [heq, neg_neg] using h
    refine hG'.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton (show u ∈ ({0} : Set ℝ)ᶜ from
      by simpa using hu)] with v hv
    exact (hd1 v (by simpa using hv)).deriv
  change ConcaveOn ℝ _ G
  apply concaveOn_of_deriv2_nonpos' (convex_Icc _ _)
  · intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (show 0 < u by linarith [hu.1])
    exact (hd1 u hu0).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (show 0 < u by linarith [hu.1])
    exact (hd2 u hu0).differentiableAt.differentiableWithinAt
  · intro u hu
    have hhalf : r / 2 ≤ u := by linarith [hu.1]
    have hu0 : 0 < u := by linarith
    change deriv (deriv G) u ≤ 0
    rw [(hd2 u hu0.ne').deriv, sub_nonpos]
    calc
      (u ^ 2)⁻¹ ≤ ((r / 2) ^ 2)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2
          (pow_le_pow_left₀ (by positivity) hhalf 2)
      _ = 4 / r ^ 2 := by field_simp [hr.ne'] <;> ring

private theorem integral_midpoint_upper {F : ℝ → ℝ} {r d c : ℝ}
    (hd : 0 ≤ d) (hF : ContinuousOn F (Icc (r - d) (r + d)))
    (hconc : ConcaveOn ℝ (Icc (r - d) (r + d)) (fun u => F u - c * u ^ 2)) :
    (∫ u in (r - d)..(r + d), F u) ≤ 2 * d * F r + (2 * c) * (d ^ 3 / 3) := by
  have hminus : MapsTo (fun s : ℝ => r - s) (Icc 0 d) (Icc (r - d) (r + d)) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hplus : MapsTo (fun s : ℝ => r + s) (Icc 0 d) (Icc (r - d) (r + d)) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hleft : IntervalIntegrable (fun s => F (r - s)) volume 0 d :=
    ContinuousOn.intervalIntegrable_of_Icc hd
      (hF.comp (by fun_prop : ContinuousOn (fun s : ℝ => r - s) (Icc 0 d)) hminus)
  have hright : IntervalIntegrable (fun s => F (r + s)) volume 0 d :=
    ContinuousOn.intervalIntegrable_of_Icc hd
      (hF.comp (by fun_prop : ContinuousOn (fun s : ℝ => r + s) (Icc 0 d)) hplus)
  have hquad : IntervalIntegrable (fun s : ℝ => (2 * c) * s ^ 2) volume 0 d :=
    (by fun_prop : Continuous (fun s : ℝ => (2 * c) * s ^ 2)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hd (hleft.add hright)
    (intervalIntegrable_const.add hquad) (fun s hs => show
      F (r - s) + F (r + s) ≤ 2 * F r + (2 * c) * s ^ 2 from by
        have hmid := hconc.2 (hminus hs) (hplus hs)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
        simp only [smul_eq_mul] at hmid
        rw [show (1 / 2 : ℝ) * (r - s) + (1 / 2 : ℝ) * (r + s) = r by ring] at hmid
        linear_combination 2 * hmid)
  rw [intervalIntegral.integral_add hleft hright,
    intervalIntegral.integral_comp_sub_left (f := F) r,
    intervalIntegral.integral_comp_add_left (f := F) r, sub_zero, add_zero,
    intervalIntegral.integral_add intervalIntegrable_const hquad,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_pow] at hmono
  have hl : IntervalIntegrable F volume (r - d) r :=
    (hF.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hu : IntervalIntegrable F volume r (r + d) :=
    (hF.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
  rw [intervalIntegral.integral_add_adjacent_intervals hl hu] at hmono
  norm_num [smul_eq_mul] at hmono
  linarith only [hmono]

private theorem reciprocal_lower {Q : ℝ → ℝ} {R κ C r : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hr : 0 < r) (hr1 : r ≤ 1) (hroom : (3 / 2) * r ≤ R)
    (hQ : ContinuousOn Q (Ioc 0 R))
    (hconc : ConcaveOn ℝ (Ioc 0 R) (fun u => Q u + Real.log u))
    (hsigned : ∀ a b, 0 < a → a ≤ b → b ≤ R →
      |∫ u in a..b, (Q u + κ * u ^ (1 / 2 : ℝ)) * u ^ (-(3 / 2) : ℝ)| ≤ C) :
    -(2 * C + 1 / 6) * r ^ (1 / 3 : ℝ) ≤ Q r + κ * r ^ (1 / 2 : ℝ) := by
  let F (u : ℝ) := Q u + κ * u ^ (1 / 2 : ℝ)
  let d : ℝ := r ^ (7 / 6 : ℝ) / 2
  let a := r - d
  let b := r + d
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hr _) (by norm_num)
  have hdr : d ≤ r / 2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show (1 : ℝ) ≤ 7 / 6 by norm_num)
    rw [Real.rpow_one] at h
    exact div_le_div_of_nonneg_right h (by norm_num)
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : b ≤ (3 / 2) * r := by dsimp [b]; linarith
  have hinterval : Icc a b ⊆ Ioc 0 R :=
    fun u hu => ⟨ha.trans_le hu.1, hu.2.trans (hb.trans hroom)⟩
  have hF : ContinuousOn F (Icc a b) :=
    (hQ.mono hinterval).add
      ((Real.continuous_rpow_const (show (0 : ℝ) ≤ 1 / 2 by norm_num)).continuousOn.const_mul κ)
  have hsqrt : ConcaveOn ℝ (Icc a b) (fun u => κ * u ^ (1 / 2 : ℝ)) := by
    have hroot := (Real.concaveOn_rpow (p := 1 / 2) (by norm_num) (by norm_num)).subset
      (show Icc a b ⊆ Ici 0 from fun u hu => (ha.trans_le hu.1).le) (convex_Icc a b)
    simpa only [smul_eq_mul] using ConcaveOn.smul hκ hroot
  have hmid : ConcaveOn ℝ (Icc a b) (fun u => F u - (2 / r ^ 2) * u ^ 2) := by
    have hadd := ((hconc.subset hinterval (convex_Icc a b)).add
      (concave_log_correction hr hdr)).add hsqrt
    convert hadd using 1
    ext u
    dsimp [F]
    ring
  have hu := integral_midpoint_upper hd.le hF hmid
  have hl := integral_unweighted_lower ha hab hF (C := C) (fun v hv =>
    (abs_le.mp (hsigned v b (ha.trans_le hv.1) hv.2 (hb.trans hroom))).1)
  have hfactor : (3 / 2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 := by
    have hpow : ((3 / 2 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = (3 / 2 : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_mul_natCast (show (0 : ℝ) ≤ 3 / 2 by norm_num) (3 / 2) 2]
      rw [show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    by_contra! h
    have hsq := pow_lt_pow_left₀ h (show (0 : ℝ) ≤ 2 by norm_num) (by decide : 2 ≠ 0)
    rw [hpow] at hsq
    norm_num at hsq
  have hbpow : b ^ (3 / 2 : ℝ) ≤ 2 * r ^ (3 / 2 : ℝ) := calc
    _ ≤ ((3 / 2) * r) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (ha.le.trans hab) hb (by norm_num)
    _ = (3 / 2 : ℝ) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) hr.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hr.le _)
  have hl' : -C * (2 * r ^ (3 / 2 : ℝ)) ≤ ∫ u in a..b, F u :=
    (mul_le_mul_of_nonpos_left hbpow (neg_nonpos.mpr hC)).trans hl
  have hscale : (2 * d) * r ^ (1 / 3 : ℝ) = r ^ (3 / 2 : ℝ) := by
    dsimp [d]
    rw [show (2 : ℝ) * (r ^ (7 / 6 : ℝ) / 2) = r ^ (7 / 6 : ℝ) by ring,
      ← Real.rpow_add hr, show (7 / 6 : ℝ) + 1 / 3 = 3 / 2 by norm_num]
  have hdsq : d ^ 2 = (r ^ (1 / 3 : ℝ) * r ^ 2) / 4 := by
    dsimp [d]
    rw [div_pow, ← Real.rpow_mul_natCast hr.le (7 / 6) 2,
      ← Real.rpow_add_natCast hr.ne' (1 / 3) 2]
    norm_num
  have herr : (2 * (2 / r ^ 2)) * (d ^ 3 / 3) = (2 * d) * (r ^ (1 / 3 : ℝ) / 6) := calc
    _ = (2 * d) * (d ^ 2 * 2 / (3 * r ^ 2)) := by field_simp [hr.ne'] <;> ring
    _ = _ := by rw [hdsq]; field_simp [hr.ne'] <;> ring
  change (∫ u in a..b, F u) ≤ 2 * d * F r + (2 * (2 / r ^ 2)) * (d ^ 3 / 3) at hu
  rw [herr] at hu
  rw [← hscale] at hl'
  change -(2 * C + 1 / 6) * r ^ (1 / 3 : ℝ) ≤ F r
  refine le_of_mul_le_mul_left (a := 2 * d) ?_ (by positivity)
  linarith only [hl', hu]

/-- A bounded centered signed primitive controls the negative part of the actual
tail of a monotone count. The count may be a step function. The integrability
assumption makes the Lebesgue tail well-defined at every point above the cutoff. -/
theorem signedPrimitiveUpper (A : ℝ → ℝ) {X₀ κ C : ℝ} (hX₁ : 1 ≤ X₀) (hκ : 0 ≤ κ)
    (htail : IntegrableOn (fun t => (A t - t) / t ^ 2) (Ioi X₀))
    (hA : MonotoneOn A (Ici X₀))
    (hprim : let q := (fun x : ℝ => ∫ t in Ioi x, (A t - t) / t ^ 2);
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
        |(∫ x in a..b, q x / Real.sqrt x) + κ * Real.log (b / a)| ≤ C) :
    let q := (fun x : ℝ => ∫ t in Ioi x, (A t - t) / t ^ 2);
    (∀ x : ℝ, (3 / 2) * X₀ ≤ x →
      -κ / Real.sqrt x - (2 * C + 1 / 6) * x ^ (-(1 / 3) : ℝ) ≤ q x) ∧
    (∀ a b : ℝ, (3 / 2) * X₀ ≤ a → a ≤ b →
      (∫ x in a..b, max (-q x) 0 / Real.sqrt x) ≤
        κ * Real.log (b / a) + (12 * C + 1) * (b ^ (1 / 6 : ℝ) - a ^ (1 / 6 : ℝ))) := by
  let f (t : ℝ) := (A t - t) / t ^ 2
  let q (x : ℝ) := ∫ t in Ioi x, f t
  let R := X₀⁻¹
  let Q (u : ℝ) := q u⁻¹
  let D (u : ℝ) := A u⁻¹
  have hX : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₁
  change ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
    |(∫ x in a..b, q x / Real.sqrt x) + κ * Real.log (b / a)| ≤ C at hprim
  have hC : 0 ≤ C := by
    simpa only [intervalIntegral.integral_same, div_self hX.ne', Real.log_one,
      mul_zero, add_zero, abs_zero] using hprim X₀ X₀ le_rfl le_rfl
  have htail' : IntegrableOn f (Ioi X₀) := htail
  have hext : Integrable ((Ioi X₀).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioi).2 htail'
  have hqcont : ContinuousOn q (Ici X₀) := by
    have hc : Continuous (fun x => q X₀ - ∫ t in X₀..x, (Ioi X₀).indicator f t) :=
      continuous_const.sub (intervalIntegral.continuous_primitive
        (fun _ _ => hext.intervalIntegrable) X₀)
    refine hc.continuousOn.congr (fun x hx => ?_)
    have heq : (∫ t in X₀..x, (Ioi X₀).indicator f t) = ∫ t in X₀..x, f t := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le hx] at ht
      exact indicator_of_mem ht.1 f
    have hdiff : q X₀ - q x = ∫ t in X₀..x, f t :=
      intervalIntegral.integral_Ioi_sub_Ioi htail' hx
    change q x = q X₀ - (∫ t in X₀..x, (Ioi X₀).indicator f t)
    rw [heq, ← hdiff]
    ring
  have hinv : MapsTo (fun u : ℝ => u⁻¹) (Ioc 0 R) (Ici X₀) :=
    fun _ hu => (le_inv_comm₀ hX hu.1).2 hu.2
  have hQ : ContinuousOn Q (Ioc 0 R) :=
    hqcont.comp (continuousOn_inv₀.mono (fun _ hu => by
      simpa using (show (0 : ℝ) < _ from hu.1).ne')) hinv
  have hD : AntitoneOn D (Ioc 0 R) := fun u hu v hv huv =>
    hA (hinv hv) (hinv hu) (inv_anti₀ hu.1 huv)
  have hDint : ∀ {u v : ℝ}, u ∈ Ioc 0 R → v ∈ Ioc 0 R → u ≤ v →
      IntervalIntegrable D volume u v := by
    intro u v hu hv huv
    apply AntitoneOn.intervalIntegrable
    exact hD.mono (by
      rw [uIcc_of_le huv]
      exact fun _ hy => ⟨hu.1.trans_le hy.1, hy.2.trans hv.2⟩)
  have hinc : ∀ {u v : ℝ}, u ∈ Ioc 0 R → v ∈ Ioc 0 R → u ≤ v →
      (Q v + Real.log v) - (Q u + Real.log u) = ∫ s in u..v, D s := by
    intro u v hu hv huv
    have hdiff : Q v - Q u = ∫ t in v⁻¹..u⁻¹, f t :=
      intervalIntegral.integral_Ioi_sub_Ioi (htail'.mono_set (Ioi_subset_Ioi (hinv hv)))
        (inv_anti₀ hu.1 huv)
    have hchange : (∫ t in v⁻¹..u⁻¹, f t) = ∫ s in u..v, D s - s⁻¹ := by
      rw [← integral_reciprocal f hu.1 huv]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le huv] at hs
      have hs0 : s ≠ 0 := (hu.1.trans_le hs.1).ne'
      simp only [f, D, inv_inv]
      field_simp [hs0] <;> ring
    have hinvInt : IntervalIntegrable (fun s : ℝ => s⁻¹) volume u v :=
      (continuousOn_inv₀.mono (by
        rw [uIcc_of_le huv]
        exact fun _ hs => by simpa using (hu.1.trans_le hs.1).ne')).intervalIntegrable
    rw [hchange, intervalIntegral.integral_sub (hDint hu hv huv) hinvInt,
      integral_inv_of_pos hu.1 hv.1, Real.log_div hv.1.ne' hu.1.ne'] at hdiff
    linarith only [hdiff]
  have hconc : ConcaveOn ℝ (Ioc 0 R) (fun u => Q u + Real.log u) := by
    apply concaveOn_of_slope_anti_adjacent (convex_Ioc _ _)
    intro u v w hu hw huv hvw
    have hv : v ∈ Ioc 0 R := ⟨hu.1.trans huv, hvw.le.trans hw.2⟩
    have hfirst : (v - u) * D v ≤ ∫ s in u..v, D s := by
      have hm := intervalIntegral.integral_mono_on huv.le intervalIntegrable_const
        (hDint hu hv huv.le) (fun s hs => show D v ≤ D s from
          hD ⟨hu.1.trans_le hs.1, hs.2.trans hv.2⟩ hv hs.2)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
    have hsecond : (∫ s in v..w, D s) ≤ (w - v) * D v := by
      have hm := intervalIntegral.integral_mono_on hvw.le (hDint hv hw hvw.le)
        intervalIntegrable_const (fun s hs => show D s ≤ D v from
          hD hv ⟨hv.1.trans_le hs.1, hs.2.trans hw.2⟩ hs.1)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
    rw [hinc hv hw hvw.le, hinc hu hv huv.le]
    apply le_trans (b := D v)
    · exact (div_le_iff₀ (sub_pos.mpr hvw)).2 (by simpa [mul_comm] using hsecond)
    · exact (le_div_iff₀ (sub_pos.mpr huv)).2 (by simpa [mul_comm] using hfirst)
  let W (x : ℝ) := q x / Real.sqrt x + κ * x⁻¹
  have hsigned : ∀ u v : ℝ, 0 < u → u ≤ v → v ≤ R →
      |∫ s in u..v, (Q s + κ * s ^ (1 / 2 : ℝ)) * s ^ (-(3 / 2) : ℝ)| ≤ C := by
    intro u v hu huv hvR
    have hv := hu.trans_le huv
    have hvu := inv_anti₀ hu huv
    have hvX : X₀ ≤ v⁻¹ := hinv (show v ∈ Ioc 0 R from ⟨hv, hvR⟩)
    have hdom : [[v⁻¹, u⁻¹]] ⊆ Ici X₀ := by
      rw [uIcc_of_le hvu]
      exact fun _ hx => hvX.trans hx.1
    have hcont : ContinuousOn (fun x => q x / Real.sqrt x) [[v⁻¹, u⁻¹]] :=
      (hqcont.mono hdom).div Real.continuous_sqrt.continuousOn (fun x hx =>
        (Real.sqrt_pos.2 (hX.trans_le (hdom hx))).ne')
    have hci : ContinuousOn (fun x : ℝ => x⁻¹) [[v⁻¹, u⁻¹]] :=
      continuousOn_inv₀.mono (fun _ hx => by simpa using (hX.trans_le (hdom hx)).ne')
    have hW : (∫ x in v⁻¹..u⁻¹, W x) =
        (∫ x in v⁻¹..u⁻¹, q x / Real.sqrt x) + κ * Real.log (u⁻¹ / v⁻¹) := by
      dsimp only [W]
      rw [intervalIntegral.integral_add hcont.intervalIntegrable
        (hci.const_mul κ).intervalIntegrable, intervalIntegral.integral_const_mul,
        integral_inv_of_pos (inv_pos.mpr hv) (inv_pos.mpr hu)]
    have hchange : (∫ s in u..v, (Q s + κ * s ^ (1 / 2 : ℝ)) * s ^ (-(3 / 2) : ℝ)) =
        ∫ x in v⁻¹..u⁻¹, W x := by
      rw [← integral_reciprocal W hu huv]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le huv] at hs
      have hs0 := hu.trans_le hs.1
      have h1 : s ^ (1 / 2 : ℝ) / s ^ (2 : ℕ) = s ^ (-(3 / 2) : ℝ) := by
        rw [← Real.rpow_sub_natCast hs0.ne' (1 / 2) 2]
        norm_num
      have h2 : s / s ^ (2 : ℕ) = s⁻¹ := by field_simp [hs0.ne'] <;> ring
      have h3 : s ^ (1 / 2 : ℝ) * s ^ (-(3 / 2) : ℝ) = s⁻¹ := by
        rw [← Real.rpow_add hs0, show (1 / 2 : ℝ) + -(3 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
      dsimp only [Q, W]
      rw [Real.sqrt_inv]
      simp only [Real.sqrt_eq_rpow, div_inv_eq_mul, inv_inv]
      calc
        _ = q s⁻¹ * s ^ (-(3 / 2) : ℝ) + κ * s⁻¹ := by rw [add_mul, mul_assoc, h3]
        _ = q s⁻¹ * (s ^ (1 / 2 : ℝ) / s ^ 2) + κ * (s / s ^ 2) := by rw [h1, h2]
        _ = _ := by ring
    rw [hchange, hW]
    exact hprim v⁻¹ u⁻¹ hvX hvu
  have hpoint : ∀ x : ℝ, (3 / 2) * X₀ ≤ x →
      -κ / Real.sqrt x - (2 * C + 1 / 6) * x ^ (-(1 / 3) : ℝ) ≤ q x := by
    intro x hx
    have hxX : X₀ ≤ x := (by linarith : X₀ ≤ (3 / 2) * X₀).trans hx
    have hx0 := hX.trans_le hxX
    have hx1 := hX₁.trans hxX
    have hr1 : x⁻¹ ≤ 1 := by simpa only [inv_one] using inv_anti₀ zero_lt_one hx1
    have hroom : (3 / 2 : ℝ) * x⁻¹ ≤ R := by
      change (3 / 2 : ℝ) * x⁻¹ ≤ X₀⁻¹
      rw [← div_eq_mul_inv, div_le_iff₀ hx0]
      calc
        (3 / 2 : ℝ) = X₀⁻¹ * ((3 / 2) * X₀) := by field_simp [hX.ne'] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hX.le)
    have hp := reciprocal_lower hκ hC (inv_pos.mpr hx0) hr1 hroom hQ hconc hsigned
    change -(2 * C + 1 / 6) * x⁻¹ ^ (1 / 3 : ℝ) ≤
      q (x⁻¹)⁻¹ + κ * x⁻¹ ^ (1 / 2 : ℝ) at hp
    rw [inv_inv, ← Real.rpow_neg_eq_inv_rpow x (1 / 3), ← Real.sqrt_eq_rpow,
      Real.sqrt_inv, ← div_eq_mul_inv] at hp
    rw [neg_div]
    linarith only [hp]
  refine ⟨hpoint, ?_⟩
  intro a b ha hab
  have haX : X₀ ≤ a := (by linarith : X₀ ≤ (3 / 2) * X₀).trans ha
  have ha0 := hX.trans_le haX
  have hb0 := ha0.trans_le hab
  have hdom : [[a, b]] ⊆ Ici X₀ := by
    rw [uIcc_of_le hab]
    exact fun _ hx => haX.trans hx.1
  let K := 2 * C + 1 / 6
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hmass : IntervalIntegrable (fun x => max (-q x) 0 / Real.sqrt x) volume a b :=
    (((hqcont.mono hdom).neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun _ hx => (Real.sqrt_pos.2 (hX.trans_le (hdom hx))).ne')).intervalIntegrable
  have hci : ContinuousOn (fun x : ℝ => x⁻¹) [[a, b]] :=
    continuousOn_inv₀.mono (fun _ hx => by simpa using (hX.trans_le (hdom hx)).ne')
  have hcp : ContinuousOn (fun x : ℝ => x ^ (-(5 / 6) : ℝ)) [[a, b]] :=
    fun x hx => (Real.continuousAt_rpow_const x (-(5 / 6) : ℝ)
      (Or.inl (hX.trans_le (hdom hx)).ne')).continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on hab hmass
    ((hci.const_mul κ).add (hcp.const_mul K)).intervalIntegrable (fun x hx => by
      have hx0 := ha0.trans_le hx.1
      have hs := Real.sqrt_pos.2 hx0
      have hmax : max (-q x) 0 ≤ κ / Real.sqrt x + K * x ^ (-(1 / 3) : ℝ) := by
        apply max_le
        · have h := hpoint x (ha.trans hx.1)
          change -κ / Real.sqrt x - K * x ^ (-(1 / 3) : ℝ) ≤ q x at h
          rw [neg_div] at h
          linarith only [h]
        · positivity
      calc
        _ ≤ (κ / Real.sqrt x + K * x ^ (-(1 / 3) : ℝ)) / Real.sqrt x :=
          div_le_div_of_nonneg_right hmax hs.le
        _ = κ * x⁻¹ + K * x ^ (-(5 / 6) : ℝ) := by
          rw [add_div, div_div, Real.mul_self_sqrt hx0.le, div_eq_mul_inv κ x]
          congr 1
          calc
            _ = K * (x ^ (-(1 / 3) : ℝ) / x ^ (1 / 2 : ℝ)) := by
              rw [← Real.sqrt_eq_rpow]
              ring
            _ = _ := by rw [← Real.rpow_sub hx0]; norm_num)
  have hpow : (∫ x in a..b, x ^ (-(5 / 6) : ℝ)) =
      (b ^ (1 / 6 : ℝ) - a ^ (1 / 6 : ℝ)) / (1 / 6) := by
    simpa only [show (-(5 / 6) : ℝ) + 1 = 1 / 6 by norm_num] using
      (integral_rpow (a := a) (b := b) (r := -(5 / 6)) (Or.inl (by norm_num)))
  change (∫ u in a..b, max (-q u) 0 / Real.sqrt u) ≤
    (∫ u in a..b, κ * u⁻¹ + K * u ^ (-(5 / 6) : ℝ)) at hmono
  have hinvInt : IntervalIntegrable (fun u => κ * u⁻¹) volume a b :=
    (hci.const_mul κ).intervalIntegrable
  have hpowInt : IntervalIntegrable (fun u => K * u ^ (-(5 / 6) : ℝ)) volume a b :=
    (hcp.const_mul K).intervalIntegrable
  rw [intervalIntegral.integral_add hinvInt hpowInt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hb0, hpow] at hmono
  convert hmono using 1
  dsimp [K]
  ring

end
end D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper
