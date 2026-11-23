/- GID: D5/S3/Weil/Mertens/WeightedTailWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/WeightedTailWindowMass
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Finite-window integral transport for logarithmically weighted tails. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import D5.S3.Weil.Mertens.WeightedTailInverse

/-! Integrating inverse logarithmic tail transport over a finite test window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.WeightedTailWindowMass

open Real Set MeasureTheory
open D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail transport)
open D5.S3.Weil.Mertens.WeightedTailInverse (a v inverse a_pos v_nonneg)

noncomputable section

/-- The signed endpoint contribution of finite inverse transport. -/
def endpointDefect (k : ℝ → ℝ) (B : ℝ) : ℝ :=
  tail k B - a B * weightedTail k B

/-- The contribution of the integrated inverse tail at `t` after changing order.
The local inverse term contributes `a t / sqrt t` separately on `[Y, X]`. -/
def triangleWeight (Y X t : ℝ) : ℝ :=
  2 * (sqrt (min t X) - sqrt Y) * v t

/-- Uniform comparison factor for the full inverse-weighted budget. -/
def massFactor (Y : ℝ) : ℝ :=
  1 + 2 * ((log Y + 2) / (log Y * (1 + log Y)))

/-- Negative mass of the weighted tail, with the inverse weight in the density. -/
def weightedNegativeMass (k : ℝ → ℝ) (Y B : ℝ) : ℝ :=
  ∫ t in Y..B, (a t / sqrt t) * max (-weightedTail k t) 0

private lemma a_continuousOn {Y B : ℝ} (hY : 1 < Y) : ContinuousOn a (Icc Y B) := by
  intro t ht
  have ht1 := hY.trans_le ht.1
  have hl := log_pos ht1
  have hc := continuousAt_log (zero_lt_one.trans ht1).ne'
  exact ((hc.pow 2).div (hc.const_add 1) (by positivity)).continuousWithinAt

private lemma v_continuousOn {Y B : ℝ} (hY : 1 < Y) : ContinuousOn v (Icc Y B) := by
  intro t ht
  have ht1 := hY.trans_le ht.1
  have ht0 := zero_lt_one.trans ht1
  have hl := log_pos ht1
  have hc := continuousAt_log ht0.ne'
  have hd : t * (1 + log t) ^ 2 ≠ 0 :=
    mul_ne_zero ht0.ne' (pow_ne_zero 2 (by linarith))
  exact ((hc.mul (hc.add_const 2)).div
    (continuousAt_id.mul ((hc.const_add 1).pow 2)) hd).continuousWithinAt

private lemma invSqrt_continuousOn {Y B : ℝ} (hY : 0 < Y) :
    ContinuousOn (fun t : ℝ => 1 / sqrt t) (Icc Y B) :=
  continuousOn_const.div continuous_sqrt.continuousOn
    (fun _ ht => (sqrt_pos.2 (hY.trans_le ht.1)).ne')

private lemma invSqrt_interval {Y t : ℝ} (hY : 0 < Y) (hYt : Y ≤ t) :
    (∫ x in Y..t, 1 / sqrt x) = 2 * (sqrt t - sqrt Y) := by
  have hpoint : EqOn (fun x : ℝ => 1 / sqrt x)
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (uIcc Y t) := by
    intro x hx
    have hx0 := hY.trans_le ((uIcc_of_le hYt ▸ hx).1)
    simp only [sqrt_eq_rpow, rpow_neg hx0.le, one_div]
  rw [intervalIntegral.integral_congr hpoint,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))),
    show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← sqrt_eq_rpow t, ← sqrt_eq_rpow Y]
  ring

private lemma finite_inverse {k : ℝ → ℝ} {x B : ℝ} (hx : 2 ≤ x) (hxB : x ≤ B)
    (hk : IntegrableOn k (Ioi x)) :
    tail k x = a x * weightedTail k x +
      (∫ t in x..B, v t * weightedTail k t) + endpointDefect k B := by
  obtain ⟨hIx, hQx⟩ := inverse hx hk
  obtain ⟨_, hQB⟩ := inverse (hx.trans hxB) (hk.mono_set (Ioi_subset_Ioi hxB))
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hIx hxB
  unfold endpointDefect
  linarith only [hQx, hQB, hsplit]

private lemma tail_continuousOn {k : ℝ → ℝ} {Y B : ℝ} (hk : IntegrableOn k (Ioi Y)) :
    ContinuousOn (tail k) (Icc Y B) :=
  hk.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)

private lemma weightedTail_continuousOn {k : ℝ → ℝ} {Y B : ℝ} (hY : 2 ≤ Y)
    (hk : IntegrableOn k (Ioi Y)) : ContinuousOn (weightedTail k) (Icc Y B) :=
  (transport hY hk).1.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)

/-- Fubini over the portion of `[Y, X] × [Y, B]` with `x ≤ t`. -/
private lemma integral_triangle {f g : ℝ → ℝ} {Y X B : ℝ}
    (hYX : Y ≤ X) (hXB : X ≤ B)
    (hf : IntegrableOn f (Icc Y X)) (hg : IntegrableOn g (Icc Y B)) :
    IntervalIntegrable (fun x => f x * (∫ t in x..B, g t)) volume Y X ∧
      (∫ x in Y..X, f x * (∫ t in x..B, g t)) =
        ∫ t in Y..B, (∫ x in Y..min t X, f x) * g t := by
  let F : ℝ × ℝ → ℝ :=
    {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => f p.1 * g p.2)
  have hF : Integrable F ((volume.restrict (Icc Y X)).prod (volume.restrict (Icc Y B))) :=
    (hf.integrable.mul_prod hg.integrable).indicator
      (measurableSet_le measurable_fst measurable_snd)
  have row (x : ℝ) (hx : x ∈ Icc Y X) :
      (∫ t in Icc Y B, F (x, t)) = f x * (∫ t in x..B, g t) := by
    have hs : (fun t => F (x, t)) = fun t => f x * (Ici x).indicator g t := by
      funext t
      by_cases h : x ≤ t <;> simp [F, h]
    have hi : Ici x ∩ Icc Y B = Icc x B := by
      ext t
      change (x ≤ t ∧ Y ≤ t ∧ t ≤ B) ↔ x ≤ t ∧ t ≤ B
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx.1.trans h.1, h.2⟩⟩
    rw [hs, integral_const_mul, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hi, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hx.2.trans hXB)]
  have col (t : ℝ) (ht : t ∈ Icc Y B) :
      (∫ x in Icc Y X, F (x, t)) = (∫ x in Y..min t X, f x) * g t := by
    have hs : (fun x => F (x, t)) = fun x => (Iic t).indicator f x * g t := by
      funext x
      by_cases h : x ≤ t <;> simp [F, h]
    have hi : Iic t ∩ Icc Y X = Icc Y (min t X) := by
      ext x
      change (x ≤ t ∧ Y ≤ x ∧ x ≤ X) ↔ Y ≤ x ∧ x ≤ min t X
      exact ⟨fun h => ⟨h.2.1, le_min h.1 h.2.2⟩,
        fun h => ⟨h.2.trans (min_le_left _ _), h.1, h.2.trans (min_le_right _ _)⟩⟩
    rw [hs, integral_mul_const, integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hi, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_min ht.1 hYX)]
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).mpr
    exact (show IntegrableOn (fun x => ∫ t in Icc Y B, F (x, t)) (Icc Y X) volume from
      hF.integral_prod_left).congr_fun (fun {x} hx => row x hx) measurableSet_Icc
  · simp only [intervalIntegral.integral_of_le hYX,
      intervalIntegral.integral_of_le (hYX.trans hXB), ← integral_Icc_eq_integral_Ioc]
    calc
      (∫ x in Icc Y X, f x * (∫ t in x..B, g t)) =
          ∫ x in Icc Y X, ∫ t in Icc Y B, F (x, t) :=
        setIntegral_congr_fun measurableSet_Icc (fun {x} hx => (row x hx).symm)
      _ = ∫ t in Icc Y B, ∫ x in Icc Y X, F (x, t) :=
        integral_integral_swap (f := fun x t => F (x, t)) hF
      _ = ∫ t in Icc Y B, (∫ x in Y..min t X, f x) * g t :=
        setIntegral_congr_fun measurableSet_Icc (fun {t} ht => col t ht)

private def windowExpression (g : ℝ → ℝ) (c B x : ℝ) : ℝ :=
  (a x * g x + (∫ t in x..B, v t * g t) + c) / sqrt x

private lemma integral_windowExpression {g : ℝ → ℝ} {Y X B : ℝ} (c : ℝ) (hY : 1 < Y)
    (hYX : Y ≤ X) (hXB : X ≤ B) (hg : IntegrableOn g (Icc Y B)) :
    IntervalIntegrable (windowExpression g c B) volume Y X ∧
      (∫ x in Y..X, windowExpression g c B x) =
        (∫ t in Y..X, (a t / sqrt t) * g t) +
        (∫ t in Y..B, triangleWeight Y X t * g t) + 2 * (sqrt X - sqrt Y) * c := by
  have hY0 := zero_lt_one.trans hY
  have hw := invSqrt_continuousOn (B := X) hY0
  have ha : ContinuousOn (fun x => a x / sqrt x) (Icc Y X) :=
    (a_continuousOn hY).div continuous_sqrt.continuousOn
      (fun _ ht => (sqrt_pos.2 (hY0.trans_le ht.1)).ne')
  have hs : IntervalIntegrable (fun x => (a x / sqrt x) * g x) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2
      (IntegrableOn.continuousOn_mul ha (hg.mono_set (Icc_subset_Icc le_rfl hXB)) isCompact_Icc)
  have hvg : IntegrableOn (fun t => v t * g t) (Icc Y B) :=
    IntegrableOn.continuousOn_mul (v_continuousOn hY) hg isCompact_Icc
  have ht := integral_triangle hYX hXB hw.integrableOn_Icc hvg
  have hc : IntervalIntegrable (fun x => (1 / sqrt x) * c) volume Y X :=
    (hw.mul continuousOn_const).intervalIntegrable_of_Icc hYX
  have hsplit : windowExpression g c B =
      fun x => a x / sqrt x * g x +
        (1 / sqrt x) * (∫ t in x..B, v t * g t) + (1 / sqrt x) * c := by
    funext x
    unfold windowExpression
    ring
  have htriangle :
      (∫ t in Y..B, (∫ x in Y..min t X, 1 / sqrt x) * (v t * g t)) =
        ∫ t in Y..B, triangleWeight Y X t * g t := by
    apply intervalIntegral.integral_congr
    intro t ht'
    rw [uIcc_of_le (hYX.trans hXB)] at ht'
    change (∫ x in Y..min t X, 1 / sqrt x) * (v t * g t) = triangleWeight Y X t * g t
    rw [invSqrt_interval hY0 (le_min ht'.1 hYX)]
    unfold triangleWeight
    ring
  simp only [hsplit]
  refine ⟨(hs.add ht.1).add hc, ?_⟩
  rw [intervalIntegral.integral_add (hs.add ht.1) hc, intervalIntegral.integral_add hs ht.1,
    ht.2, htriangle, intervalIntegral.integral_mul_const, invSqrt_interval hY0 hYX]

/-- Transport a majorant of the negative weighted tail on `[Y, B]` to negative
mass on `[Y, X]`. The nonlocal coefficient uses `min t X` and the endpoint
payment depends on the length of the tested window in the square-root variable. -/
theorem negative_mass_le_of_majorant {k g : ℝ → ℝ} {Y X B c : ℝ}
    (hY : 2 ≤ Y) (hYX : Y ≤ X) (hXB : X ≤ B) (hk : IntegrableOn k (Ioi Y))
    (hg : IntegrableOn g (Icc Y B))
    (hg0 : ∀ t ∈ Icc Y B, 0 ≤ g t) (hgW : ∀ t ∈ Icc Y B, -weightedTail k t ≤ g t)
    (hc0 : 0 ≤ c) (hc : -endpointDefect k B ≤ c) :
    (∫ x in Y..X, max (-tail k x) 0 / sqrt x) ≤
      (∫ t in Y..X, (a t / sqrt t) * g t) +
      (∫ t in Y..B, triangleWeight Y X t * g t) + 2 * (sqrt X - sqrt Y) * c := by
  have hY1 : 1 < Y := by linarith
  have hY0 := zero_lt_one.trans hY1
  have hW := weightedTail_continuousOn (B := B) hY hk
  have hlhs : IntervalIntegrable (fun x => max (-tail k x) 0 / sqrt x) volume Y X :=
    (((tail_continuousOn hk).neg.sup continuousOn_const).div continuous_sqrt.continuousOn
      (fun _ ht => (sqrt_pos.2 (hY0.trans_le ht.1)).ne')).intervalIntegrable_of_Icc hYX
  obtain ⟨hrhs, htransport⟩ := integral_windowExpression c hY1 hYX hXB hg
  rw [← htransport]
  apply intervalIntegral.integral_mono_on hYX hlhs hrhs
  intro x hx
  have hxB := hx.2.trans hXB
  have hx' : x ∈ Icc Y B := ⟨hx.1, hxB⟩
  have hx1 := hY1.trans_le hx.1
  have hsub : Icc x B ⊆ Icc Y B := fun _ ht => ⟨hx.1.trans ht.1, ht.2⟩
  have hv := v_continuousOn (B := B) hx1
  have hvg : IntervalIntegrable (fun t => v t * g t) volume x B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxB).2
      (IntegrableOn.continuousOn_mul hv (hg.mono_set hsub) isCompact_Icc)
  have htri : -(∫ t in x..B, v t * weightedTail k t) ≤ ∫ t in x..B, v t * g t := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hxB
      ((hv.mul (hW.mono hsub)).neg.intervalIntegrable_of_Icc hxB) hvg
    intro t ht
    change -(v t * weightedTail k t) ≤ v t * g t
    simpa only [mul_neg] using
      mul_le_mul_of_nonneg_left (hgW t (hsub ht)) (v_nonneg (hx1.trans_le ht.1))
  have htri0 : 0 ≤ ∫ t in x..B, v t * g t :=
    intervalIntegral.integral_nonneg hxB
      (fun t ht => mul_nonneg (v_nonneg (hx1.trans_le ht.1)) (hg0 t (hsub ht)))
  have hax := (a_pos hx1).le
  have hfinite := finite_inverse (hY.trans hx.1) hxB (hk.mono_set (Ioi_subset_Ioi hx.1))
  have hpoint := mul_le_mul_of_nonneg_left (hgW x hx') hax
  rw [mul_neg] at hpoint
  unfold windowExpression
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
  exact max_le (by linarith only [hfinite, hpoint, htri, hc])
    (by linarith only [mul_nonneg hax (hg0 x hx'), htri0, hc0])

private lemma mul_v_le {Y t : ℝ} (hY : 1 < Y) (hYt : Y ≤ t) :
    t * v t ≤ ((log Y + 2) / (log Y * (1 + log Y))) * a t := by
  have hY0 := zero_lt_one.trans hY
  have ht1 := hY.trans_le hYt
  have ht0 := zero_lt_one.trans ht1
  have hly := log_pos hY
  have hlt := log_pos ht1
  have hdy : 0 < 1 + log Y := by positivity
  have hdt : 0 < 1 + log t := by positivity
  have hlog := log_le_log hY0 hYt
  have hratio : (log t + 2) / (1 + log t) ≤ (log Y + 2) / (1 + log Y) :=
    (div_le_div_iff₀ hdt hdy).2 (by nlinarith only [hlog])
  have hratio0 : 0 ≤ (log Y + 2) / (1 + log Y) := by positivity
  calc
    t * v t = ((log t + 2) / (1 + log t)) * (a t / log t) := by
      unfold a v
      field_simp [ht0.ne', hlt.ne', hdt.ne']
    _ ≤ ((log Y + 2) / (1 + log Y)) * (a t / log t) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg (a_pos ht1).le hlt.le)
    _ ≤ ((log Y + 2) / (1 + log Y)) * (a t / log Y) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (a_pos ht1).le hly hlog) hratio0
    _ = _ := by field_simp [hly.ne', hdy.ne']

private lemma triangleWeight_le {Y X t : ℝ} (hY : 1 < Y) (hYt : Y ≤ t) :
    triangleWeight Y X t ≤ (massFactor Y - 1) * (a t / sqrt t) := by
  have ht1 := hY.trans_le hYt
  have ht0 := zero_lt_one.trans ht1
  have hs := sqrt_pos.2 ht0
  unfold triangleWeight
  calc
    _ ≤ 2 * sqrt t * v t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((sub_le_self _ (sqrt_nonneg Y)).trans (sqrt_le_sqrt (min_le_left t X))) (by norm_num))
        (v_nonneg ht1)
    _ = 2 * (t * v t) / sqrt t := by
      apply (eq_div_iff hs.ne').2
      calc
        2 * sqrt t * v t * sqrt t = 2 * (sqrt t ^ 2 * v t) := by ring
        _ = _ := by rw [sq_sqrt ht0.le]
    _ ≤ 2 * (((log Y + 2) / (log Y * (1 + log Y))) * a t) / sqrt t :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_v_le hY hYt) (by norm_num)) hs.le
    _ = _ := by unfold massFactor; ring

/-- Negative mass on the tested window is bounded by the weighted negative mass
on the full window plus the negative part of the outer endpoint defect. -/
theorem negative_mass_le {k : ℝ → ℝ} {Y X B : ℝ}
    (hY : 2 ≤ Y) (hYX : Y ≤ X) (hXB : X ≤ B) (hk : IntegrableOn k (Ioi Y)) :
    (∫ x in Y..X, max (-tail k x) 0 / sqrt x) ≤
      massFactor Y * weightedNegativeMass k Y B +
        2 * (sqrt X - sqrt Y) * max (-endpointDefect k B) 0 := by
  have hY1 : 1 < Y := by linarith
  have hY0 := zero_lt_one.trans hY1
  have hYB := hYX.trans hXB
  let g (t : ℝ) := max (-weightedTail k t) 0
  let density (t : ℝ) := (a t / sqrt t) * g t
  have hg : ContinuousOn g (Icc Y B) :=
    (weightedTail_continuousOn hY hk).neg.sup continuousOn_const
  have hd : ContinuousOn density (Icc Y B) :=
    ((a_continuousOn hY1).div continuous_sqrt.continuousOn
      (fun _ ht => (sqrt_pos.2 (hY0.trans_le ht.1)).ne')).mul hg
  have hmin : Continuous (fun t : ℝ => min t X) := continuous_id.inf continuous_const
  have hK : ContinuousOn (triangleWeight Y X) (Icc Y B) :=
    (continuousOn_const.mul
      ((continuous_sqrt.comp hmin).continuousOn.sub continuousOn_const)).mul
        (v_continuousOn hY1)
  have htransport := negative_mass_le_of_majorant (g := g)
    (c := max (-endpointDefect k B) 0) hY hYX hXB hk hg.integrableOn_Icc
    (fun _ _ => le_max_right _ _) (fun _ _ => le_max_left _ _)
    (le_max_right _ _) (le_max_left _ _)
  have hlocal : (∫ t in Y..X, density t) ≤ weightedNegativeMass k Y B := by
    have hXd := (hd.mono (Icc_subset_Icc hYX le_rfl)).intervalIntegrable_of_Icc
      (μ := volume) hXB
    have hYd := (hd.mono (Icc_subset_Icc le_rfl hXB)).intervalIntegrable_of_Icc
      (μ := volume) hYX
    have hnonneg : 0 ≤ ∫ t in X..B, density t :=
      intervalIntegral.integral_nonneg hXB (fun t ht =>
        mul_nonneg (div_nonneg (a_pos (hY1.trans_le (hYX.trans ht.1))).le (sqrt_nonneg t))
          (le_max_right _ _))
    calc
      _ ≤ (∫ t in Y..X, density t) + ∫ t in X..B, density t := le_add_of_nonneg_right hnonneg
      _ = _ := intervalIntegral.integral_add_adjacent_intervals hYd hXd
  have hnonlocal : (∫ t in Y..B, triangleWeight Y X t * g t) ≤
      (massFactor Y - 1) * weightedNegativeMass k Y B := by
    change _ ≤ (massFactor Y - 1) * ∫ t in Y..B, density t
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hYB ((hK.mul hg).intervalIntegrable_of_Icc hYB)
      ((hd.intervalIntegrable_of_Icc hYB).const_mul _)
    intro t ht
    calc
      _ ≤ ((massFactor Y - 1) * (a t / sqrt t)) * g t :=
        mul_le_mul_of_nonneg_right (triangleWeight_le hY1 ht.1) (le_max_right _ _)
      _ = _ := by unfold density; ring
  have hbudget :
      (∫ t in Y..X, density t) + (∫ t in Y..B, triangleWeight Y X t * g t) ≤
        massFactor Y * weightedNegativeMass k Y B := by
    calc
      _ ≤ weightedNegativeMass k Y B + (massFactor Y - 1) * weightedNegativeMass k Y B :=
        add_le_add hlocal hnonlocal
      _ = _ := by ring
  exact htransport.trans (add_le_add hbudget le_rfl)

theorem weightedNegativeMass_nonneg {k : ℝ → ℝ} {Y B : ℝ} (hY : 1 < Y)
    (hYB : Y ≤ B) : 0 ≤ weightedNegativeMass k Y B := by
  apply intervalIntegral.integral_nonneg hYB
  intro t ht
  exact mul_nonneg (div_nonneg (a_pos (hY.trans_le ht.1)).le (sqrt_nonneg t))
    (le_max_right _ _)

#print axioms negative_mass_le_of_majorant
#print axioms negative_mass_le
#print axioms weightedNegativeMass_nonneg

end
end D5.S3.Weil.Mertens.WeightedTailWindowMass

