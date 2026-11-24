/- GID: D5/S3/Analytic/Resolvent/PoissonKernelTail
   generality: G
   mirror-B: D5/B/S3/Analytic/Resolvent/PoissonKernelTail
   mirror-E: none(waiver:real-positive-kernel-estimate)
   anchors: []
   utility: none
   digest: Control reciprocal-square tails by finite positive Poisson-kernel sums. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Analytic.Boundary.HorizontalLogPotential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Finite positive-kernel integration controls both ordinate tails without symmetry. -/

noncomputable section

namespace D5.S3.Analytic.Resolvent.PoissonKernelTail

open MeasureTheory Set
open scoped BigOperators

open private horizontalKernel_integral_eq_arctan
  from D5.S3.Analytic.Boundary.HorizontalLogPotential

/-- The unnormalized Cauchy kernel of width `w`. -/
def cauchyKernel (w x : ℝ) : ℝ := w / (w ^ 2 + x ^ 2)

theorem cauchyKernel_continuous (w : ℝ) : Continuous (cauchyKernel w) := by
  unfold cauchyKernel
  by_cases hw : w = 0
  · subst w
    simpa only [zero_div] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · exact continuous_const.div (continuous_const.add (continuous_id.pow 2))
      (fun x => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hw) (sq_nonneg x)))

/-- The unnormalized positive Poisson kernel. -/
def kernel (u g t : ℝ) : ℝ := cauchyKernel u (t - g)

private theorem kernel_continuous (u g : ℝ) :
    Continuous (kernel u g) :=
  (cauchyKernel_continuous u).comp (continuous_id.sub continuous_const)

private theorem kernel_nonneg {u : ℝ} (hu : 0 ≤ u) (g t : ℝ) :
    0 ≤ kernel u g t := div_nonneg hu (by positivity)

private theorem kernel_window (u g : ℝ) :
    (∫ t in (g - 16)..(g + 16), kernel u g t) = 2 * Real.arctan (16 / u) := by
  have h := horizontalKernel_integral_eq_arctan (g - 16) (g + 16) g u
  have hk : (fun t => Boundary.HorizontalLogPotential.horizontalKernel g t u) =
      (fun t => 2 * kernel u g t) := by
    funext t
    simp only [Boundary.HorizontalLogPotential.horizontalKernel, kernel, cauchyKernel,
      add_comm, mul_div_assoc]
  have hplus : (g + 16 - g) / u = 16 / u := by ring
  have hminus : (g - 16 - g) / u = -(16 / u) := by ring
  rw [hk, intervalIntegral.integral_const_mul, hplus, hminus, Real.arctan_neg] at h
  linarith

private theorem weighted_continuous {a b : ℝ} (u : ℝ) (ha : 16 < a)
    (g : ℝ) : ContinuousOn (fun t => kernel u g t / (t - 16) ^ 2) (Icc a b) := by
  refine (kernel_continuous u g).continuousOn.div (by fun_prop) ?_
  intro t ht
  exact pow_ne_zero _ (ne_of_gt (by linarith [ht.1]))

private theorem weighted_window {u g a b : ℝ} (hu : 0 ≤ u)
    (ha : 16 < a) (hag : a ≤ g - 16) (hgb : g + 16 ≤ b) :
    (2 * Real.arctan (16 / u)) / g ^ 2 ≤ ∫ t in a..b, kernel u g t / (t - 16) ^ 2 := by
  have hg : 0 < g := by linarith
  have hw : g - 16 ≤ g + 16 := by linarith
  have hgw : 16 < g - 16 := by linarith
  have hci := weighted_continuous (b := g + 16) u hgw g
  have hint : IntervalIntegrable (fun t => kernel u g t / (t - 16) ^ 2)
      volume (g - 16) (g + 16) := hci.intervalIntegrable_of_Icc hw
  have hcomp : (∫ t in (g - 16)..(g + 16), kernel u g t / g ^ 2) ≤
      ∫ t in (g - 16)..(g + 16), kernel u g t / (t - 16) ^ 2 := by
    apply intervalIntegral.integral_mono_on hw
      (((kernel_continuous u g).intervalIntegrable _ _).div_const _) hint
    intro t ht
    have ht0 : 0 < t - 16 := by linarith [ht.1]
    have htg : t - 16 ≤ g := by linarith [ht.2]
    apply div_le_div_of_nonneg_left (kernel_nonneg hu g t) (sq_pos_of_pos ht0)
    nlinarith [sq_nonneg (g - (t - 16))]
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) hag hw hgb
    (Filter.Eventually.of_forall (fun t =>
      div_nonneg (kernel_nonneg hu g t) (sq_nonneg _)))
    ((weighted_continuous u ha g).intervalIntegrable_of_Icc (by linarith))
  calc
    (2 * Real.arctan (16 / u)) / g ^ 2 =
        (∫ t in (g - 16)..(g + 16), kernel u g t) / g ^ 2 := by
      rw [kernel_window]
    _ = ∫ t in (g - 16)..(g + 16), kernel u g t / g ^ 2 :=
      (intervalIntegral.integral_div _ _).symm
    _ ≤ _ := hcomp.trans hsub

/-- The endpoint budget for the shifted logarithmic integral. -/
def endpointBudget (q x : ℝ) : ℝ :=
  (Real.log (q * (x + 3)) + (if q = 0 then 1 else 2)) / (x - 16)

private theorem logarithmic_budget (q a b : ℝ) (ha : 16 < a) (hab : a ≤ b) :
    (∫ t in a..b, (Real.log (q * (t + 3)) + 1) / (t - 16) ^ 2) ≤
      endpointBudget q a - endpointBudget q b := by
  unfold endpointBudget
  by_cases hq : q = 0
  · subst q
    simp only [zero_mul, Real.log_zero, zero_add, ↓reduceIte]
    have hz : (0 : ℝ) ∉ Set.uIcc (a - 16) (b - 16) := by
      rw [uIcc_of_le (by linarith)]
      intro h
      linarith [h.1]
    have hi := integral_zpow (a := a - 16) (b := b - 16) (n := -2)
      (Or.inr ⟨by norm_num, hz⟩)
    have he : (∫ t in a..b, 1 / (t - 16) ^ 2) =
        1 / (a - 16) - 1 / (b - 16) := by
      rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x ^ 2) 16]
      convert hi using 1 <;> norm_num [zpow_neg, zpow_natCast, one_div]
      ring
    exact he.le
  · simp only [hq, ↓reduceIte]
    let L := fun t : ℝ => Real.log (q * (t + 3))
    let F := fun t : ℝ => -(L t + 2) / (t - 16)
    have hl (t : ℝ) (ht : 16 < t) : HasDerivAt L (1 / (t + 3)) t := by
      apply ((((hasDerivAt_id t).add_const 3).const_mul q).log
        (mul_ne_zero hq (by linarith : t + 3 ≠ 0))).congr_deriv
      simp only [id_eq, mul_one]
      field_simp
    have hc : ContinuousOn L (Icc a b) := by
      intro t ht
      exact (hl t (ha.trans_le ht.1)).continuousAt.continuousWithinAt
    have hF : ContinuousOn F (Icc a b) :=
      (hc.add continuousOn_const).neg.div (by fun_prop)
        (fun t ht => ne_of_gt (by linarith [ht.1]))
    have hD (t : ℝ) (ht : 16 < t) :
        HasDerivAt F ((L t + 2 - (t - 16) / (t + 3)) / (t - 16) ^ 2) t := by
      apply (((hl t ht).add_const 2).neg.div
        ((hasDerivAt_id t).sub_const 16) (by linarith : t - 16 ≠ 0)).congr_deriv
      simp only [id_eq, Pi.neg_apply]
      ring
    have hi : IntegrableOn (fun t => (L t + 1) / (t - 16) ^ 2) (Icc a b) :=
      ContinuousOn.integrableOn_Icc ((hc.add continuousOn_const).div (by fun_prop)
        (fun t ht => pow_ne_zero _ (by linarith [ht.1])))
    have hb := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hF
      (fun t ht => (hD t (by linarith [ht.1])).hasDerivWithinAt) hi (by
        intro t ht
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have hratio : (t - 16) / (t + 3) ≤ 1 :=
          (div_le_one (by linarith [ht.1] : 0 < t + 3)).2 (by linarith)
        linarith)
    change (∫ t in a..b, (L t + 1) / (t - 16) ^ 2) ≤ _
    convert hb using 1; dsimp [F, L]; ring

private theorem logarithmic_continuous (q a b : ℝ) (ha : 16 < a) :
    ContinuousOn (fun t => (Real.log (q * (t + 3)) + 1) / (t - 16) ^ 2) (Icc a b) := by
  have hl : ContinuousOn (fun t => Real.log (q * (t + 3))) (Icc a b) := by
    by_cases hq : q = 0
    · simp only [hq, zero_mul, Real.log_zero]
      exact continuousOn_const
    · exact (continuous_const.mul (continuous_id.add continuous_const)).continuousOn.log
        (fun t ht => mul_ne_zero hq (by
          change t + 3 ≠ 0
          linarith [ht.1]))
  exact (hl.add continuousOn_const).div (by fun_prop)
    (fun t ht => pow_ne_zero _ (by linarith [ht.1]))

private theorem windowMass_gt : Real.pi - 1 / 4 < 2 * Real.arctan 8 := by
  have hi := Real.arctan_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num only [one_div, inv_inv] at hi
  have hb := Real.arctan_lt_self (by norm_num : (0 : ℝ) < 1 / 8)
  linarith

/-- The explicit two-sided logarithmic budget. -/
def tailBound (q T : ℝ) : ℝ :=
  (1 / (2 * Real.arctan 8)) * (Real.log (q * (T - 13)) + (if q = 0 then 1 else 2)) / (T - 32)

/-- The exact window mass relative to the uniform mass at width two. -/
def massRatio (u : ℝ) : ℝ :=
  (2 * Real.arctan (16 / u)) / (2 * Real.arctan 8)

private theorem massRatio_ge_one {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) :
    1 ≤ massRatio u := by
  have hc : 0 < 2 * Real.arctan 8 := by linarith [windowMass_gt, Real.pi_gt_three]
  apply (le_div_iff₀ hc).2
  have hr : (8 : ℝ) ≤ 16 / u := (le_div_iff₀ hu).2 (by linarith)
  have hb := Real.arctan_mono hr
  linarith

private theorem finite_positive_bound {ι : Type*} (J : Finset ι)
    (w u g : ι → ℝ) (q T : ℝ) (hT : 32 < T)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hu : ∀ i ∈ J, 0 ≤ u i)
    (hg : ∀ i ∈ J, T < g i)
    (henv : ∀ t : ℝ, T - 16 ≤ t →
      ∑ i ∈ J, w i * kernel (u i) (g i) t ≤ (Real.log (q * (t + 3)) + 1) / 2) :
    let E := endpointBudget q (T - 16 + ∑ i ∈ J, |g i|) / (2 * (2 * Real.arctan 8))
    (∑ i ∈ J, massRatio (u i) * (w i / (g i) ^ 2) ≤ tailBound q T / 2 - E) ∧
      tailBound q T / 2 - E < tailBound q T / 2 := by
  let a := T - 16
  let b := T - 16 + ∑ i ∈ J, |g i|
  have hs : 0 ≤ ∑ i ∈ J, |g i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have ha : 16 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hgb (i : ι) (hi : i ∈ J) : g i + 16 ≤ b := by
    have hi' : |g i| ≤ ∑ j ∈ J, |g j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (g j)) hi
    dsimp [b]
    linarith [le_abs_self (g i)]
  have hint (i : ι) (hi : i ∈ J) :
      IntervalIntegrable (fun t => w i * kernel (u i) (g i) t / (t - 16) ^ 2)
        volume a b := by
    have hc := (weighted_continuous (b := b) (u i) ha (g i)).const_mul (w i)
    have hh : IntervalIntegrable
        (fun t => w i * (kernel (u i) (g i) t / (t - 16) ^ 2)) volume a b :=
      hc.intervalIntegrable_of_Icc hab
    simpa only [mul_div_assoc] using hh
  have hterm (i : ι) (hi : i ∈ J) :
      (2 * Real.arctan (16 / u i)) * (w i / (g i) ^ 2) ≤
        ∫ t in a..b, w i * kernel (u i) (g i) t / (t - 16) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (weighted_window (hu i hi) ha
        (by dsimp [a]; linarith [hg i hi]) (hgb i hi)) (hw i hi)
    rw [show (2 * Real.arctan (16 / u i)) * (w i / (g i) ^ 2) =
      w i * ((2 * Real.arctan (16 / u i)) / (g i) ^ 2) by ring]
    simpa only [mul_div_assoc, intervalIntegral.integral_const_mul] using h
  have hsum : (2 * Real.arctan 8) * (∑ i ∈ J, massRatio (u i) * (w i / (g i) ^ 2)) ≤
      ∫ t in a..b, (∑ i ∈ J, w i * kernel (u i) (g i) t) / (t - 16) ^ 2 := by
    have hc : 2 * Real.arctan 8 ≠ 0 := by
      linarith [windowMass_gt, Real.pi_gt_three]
    have heq (i : ι) : (2 * Real.arctan 8) *
        (massRatio (u i) * (w i / (g i) ^ 2)) =
        (2 * Real.arctan (16 / u i)) * (w i / (g i) ^ 2) := by
      dsimp [massRatio]
      calc
        _ = ((2 * Real.arctan (16 / u i)) / (2 * Real.arctan 8) *
            (2 * Real.arctan 8)) * (w i / (g i) ^ 2) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hc]
    simp_rw [Finset.mul_sum, heq]
    calc
      _ ≤ ∑ i ∈ J, ∫ t in a..b,
          w i * kernel (u i) (g i) t / (t - 16) ^ 2 :=
        Finset.sum_le_sum hterm
      _ = _ := by
        simp_rw [Finset.sum_div]
        exact (intervalIntegral.integral_finsetSum hint).symm
  have hci : IntervalIntegrable
      (fun t => (∑ i ∈ J, w i * kernel (u i) (g i) t) / (t - 16) ^ 2) volume a b := by
    simp_rw [Finset.sum_div]
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum J hint
  have hlog : IntervalIntegrable
      (fun t => (Real.log (q * (t + 3)) + 1) / (t - 16) ^ 2) volume a b :=
    (logarithmic_continuous q a b ha).intervalIntegrable_of_Icc hab
  have hup : (∫ t in a..b,
      (∑ i ∈ J, w i * kernel (u i) (g i) t) / (t - 16) ^ 2) ≤
      (∫ t in a..b, (Real.log (q * (t + 3)) + 1) / (t - 16) ^ 2) / 2 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on hab hci (hlog.div_const 2)
    intro t ht
    have h := div_le_div_of_nonneg_right (henv t ht.1) (sq_nonneg (t - 16))
    convert h using 1; ring
  have hn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ Real.log (q * (t + 3)) + 1 := by
    have hnon : 0 ≤ ∑ i ∈ J, w i * kernel (u i) (g i) t :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi)
        (kernel_nonneg (hu i hi) _ _))
    linarith [henv t ht.1]
  have hb := logarithmic_budget q a b ha hab
  have hall := hsum.trans (hup.trans (div_le_div_of_nonneg_right hb (by norm_num)))
  have hc : 0 < 2 * Real.arctan 8 := by linarith [windowMass_gt, Real.pi_gt_three]
  have he : 0 < endpointBudget q b := by
    unfold endpointBudget
    apply div_pos _ (by linarith)
    by_cases hq : q = 0
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      linarith [hn b ⟨hab, le_rfl⟩]
  have hE : 0 < endpointBudget q b / (2 * (2 * Real.arctan 8)) :=
    div_pos he (mul_pos (by norm_num) hc)
  have haeq : endpointBudget q a / (2 * (2 * Real.arctan 8)) =
      tailBound q T / 2 := by
    dsimp [endpointBudget, a, tailBound]
    rw [show T - 16 + 3 = T - 13 by ring, show T - 16 - 16 = T - 32 by ring]
    ring
  refine ⟨?_, by change tailBound q T / 2 - _ < _; dsimp [b] at hE; linarith⟩
  change (∑ i ∈ J, massRatio (u i) * (w i / (g i) ^ 2)) ≤ tailBound q T / 2 - _
  rw [← haeq]
  have hh : (∑ i ∈ J, massRatio (u i) * (w i / (g i) ^ 2)) ≤
      ((endpointBudget q a - endpointBudget q b) / 2) / (2 * Real.arctan 8) :=
    (le_div_iff₀ hc).2 (by nlinarith [hall])
  change _ ≤ _ - endpointBudget q b / (2 * (2 * Real.arctan 8))
  convert hh using 1; ring

/-- The absolute-height reciprocal-square tail with its original weights. -/
def tailTerm {ι : Type*} (g : ι → ℝ) (T : ℝ) (w : ι → ℝ) (i : ι) : ℝ :=
  if T < |g i| then w i / (g i) ^ 2 else 0

/-- The reciprocal-square tail on one chosen side of the height axis. -/
def positiveTerm {ι : Type*} (g : ι → ℝ) (T : ℝ) (w : ι → ℝ) (i : ι) : ℝ :=
  if T < g i then w i / (g i) ^ 2 else 0

/-- An endpoint beyond all positive-weight windows in a finite one-sided tail. -/
def finiteEndpoint {ι : Type*} (g : ι → ℝ) (T : ℝ) (w : ι → ℝ) (J : Finset ι) : ℝ := by
  classical
  exact T - 16 + ∑ i ∈ J.filter (fun i => T < g i ∧ 0 < w i), |g i|

/-- The positive endpoint correction retained in a finite one-sided bound. -/
def finiteCorrection {ι : Type*} (q T : ℝ) (g w : ι → ℝ) (J : Finset ι) : ℝ :=
  endpointBudget q (finiteEndpoint g T w J) / (2 * (2 * Real.arctan 8))

private theorem signed_le_abs {s : ℝ} (hs : s = 1 ∨ s = -1) (x : ℝ) :
    s * x ≤ |x| := by
  rcases hs with rfl | rfl
  · simpa only [one_mul] using le_abs_self x
  · simpa only [neg_one_mul] using neg_le_abs x

private theorem finite_signed_bound {ι : Type*} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hw : ∀ i, T < s * g i → 0 ≤ w i)
    (hu : ∀ i, T < s * g i → 0 < w i → 0 ≤ u i)
    (hT : 32 < T)
    (hbound : ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2) (J : Finset ι) :
    (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
      tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
    tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
      tailBound q T / 2 := by
  classical
  let K := J.filter (fun i => T < s * g i ∧ 0 < w i)
  have hk := finite_positive_bound K w u (fun i => s * g i) q T hT
    (fun i hi => hw i ((Finset.mem_filter.mp hi).2.1))
    (fun i hi => hu i ((Finset.mem_filter.mp hi).2.1)
      (Finset.mem_filter.mp hi).2.2)
    (fun i hi => (Finset.mem_filter.mp hi).2.1) (by
      intro t ht
      have hb := hbound t ht K (fun i hi => (Finset.mem_filter.mp hi).2.1)
      rcases hs with rfl | rfl
      · simpa only [one_mul] using hb
      · have he (i : ι) : kernel (u i) (-1 * g i) t = kernel (u i) (g i) (-t) := by
          unfold kernel cauchyKernel
          congr 2; ring
        simp_rw [he]
        simpa only [neg_one_mul] using hb)
  have heq : (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) =
      ∑ i ∈ K, massRatio (u i) * (w i / (s * g i) ^ 2) := by
    simp only [K, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    unfold positiveTerm
    by_cases hg : T < s * g i
    · by_cases hw0 : 0 < w i
      · simp [hg, hw0]
      · have hz : w i = 0 := le_antisymm (le_of_not_gt hw0)
          (hw i hg)
        simp [hg, hz]
    · simp [hg]
  rw [heq]
  simpa only [finiteCorrection, finiteEndpoint, K] using hk

private theorem positive_le_mass {ι : Type*} (u g : ι → ℝ) (T : ℝ) (w : ι → ℝ)
    (hw : ∀ i, T < g i → 0 ≤ w i)
    (hu : ∀ i, T < g i → 0 < w i → 0 < u i ∧ u i ≤ 2) (i : ι) :
    0 ≤ positiveTerm g T w i ∧
      positiveTerm g T w i ≤ massRatio (u i) * positiveTerm g T w i := by
  unfold positiveTerm
  split_ifs with hi
  · have hn := div_nonneg (hw i hi) (sq_nonneg (g i))
    refine ⟨hn, ?_⟩
    by_cases hp : 0 < w i
    · simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (massRatio_ge_one (hu i hi hp).1 (hu i hi hp).2) hn
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hp) (hw i hi)
      simp [hz]
  · simp

private theorem positive_mass_nonneg {ι : Type*} (u g : ι → ℝ) (T : ℝ) (w : ι → ℝ)
    (hw : ∀ i, T < g i → 0 ≤ w i)
    (hu : ∀ i, T < g i → 0 < w i → 0 ≤ u i) (i : ι) :
    0 ≤ massRatio (u i) * positiveTerm g T w i := by
  unfold positiveTerm
  split_ifs with hi
  · by_cases hp : 0 < w i
    · apply mul_nonneg _ (div_nonneg (hw i hi) (sq_nonneg _))
      unfold massRatio
      exact div_nonneg (mul_nonneg (by norm_num)
        (Real.arctan_nonneg.mpr (div_nonneg (by norm_num) (hu i hi hp))))
        (by linarith [windowMass_gt, Real.pi_gt_three])
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hp) (hw i hi)
      simp [hz]
  · simp

/-- Nonnegative widths suffice for the exact mass-weighted bound on one side. -/
theorem reciprocalSquare_mass_side_bound {ι : Type*} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hw : ∀ i, T < s * g i → 0 ≤ w i)
    (hu : ∀ i, T < s * g i → 0 < w i → 0 ≤ u i)
    (hT : 32 < T)
    (hbound : ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2) :
    (∀ J : Finset ι,
      (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
      tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
        tailBound q T / 2) ∧
    Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
    (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ≤
      tailBound q T / 2 := by
  have hf := finite_signed_bound u g q T w s hs hw hu hT hbound
  have hn := positive_mass_nonneg u (fun i => s * g i) T w hw hu
  have hb J := ((hf J).1.trans_lt (hf J).2).le
  exact ⟨hf, summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

/-- A fixed-side envelope controls that side using only its own weight and width conditions. -/
theorem reciprocalSquare_side_bound {ι : Type*} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hw : ∀ i, T < s * g i → 0 ≤ w i)
    (hu : ∀ i, T < s * g i → 0 < w i → 0 < u i ∧ u i ≤ 2)
    (hT : 32 < T)
    (hbound : ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2) :
    (∀ J : Finset ι,
      (∑ i ∈ J, positiveTerm (fun i => s * g i) T w i) ≤
        (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
      (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
      tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
        tailBound q T / 2) ∧
    Summable (positiveTerm (fun i => s * g i) T w) ∧
    (∑' i, positiveTerm (fun i => s * g i) T w i) ≤ tailBound q T / 2 ∧
    Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
    (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ≤
      tailBound q T / 2 := by
  have hf := reciprocalSquare_mass_side_bound u g q T w s hs hw
    (fun i hi hp => (hu i hi hp).1.le) hT hbound
  have hd := positive_le_mass u (fun i => s * g i) T w hw hu
  have hn : 0 ≤ positiveTerm (fun i => s * g i) T w := fun i => (hd i).1
  have hb J := ((hf.1 J).1.trans_lt (hf.1 J).2).le
  have ho J := (Finset.sum_le_sum (fun i _ => (hd i).2)).trans (hb J)
  exact ⟨(fun J => ⟨Finset.sum_le_sum (fun i _ => (hd i).2), hf.1 J⟩),
    summable_of_sum_le hn ho, Real.tsum_le_of_sum_le hn ho, hf.2⟩

private theorem finite_tail_bound {ι : Type*} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (hw : ∀ i, T < |g i| → 0 ≤ w i)
    (hu : ∀ i, T < |g i| → 0 < w i → 0 ≤ u i)
    (hT : 32 < T)
    (hbound : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2) (J : Finset ι) :
    (∑ i ∈ J, massRatio (u i) * tailTerm g T w i ≤ tailBound q T -
      (finiteCorrection q T (fun i => 1 * g i) w J +
        finiteCorrection q T (fun i => -1 * g i) w J)) ∧
    tailBound q T - (finiteCorrection q T (fun i => 1 * g i) w J +
      finiteCorrection q T (fun i => -1 * g i) w J) < tailBound q T := by
  have hpos := (reciprocalSquare_mass_side_bound u g q T w 1 (Or.inl rfl)
    (fun i hi => hw i (hi.trans_le (signed_le_abs (Or.inl rfl) _)))
    (fun i hi => hu i (hi.trans_le (signed_le_abs (Or.inl rfl) _)))
    hT (hbound 1 (Or.inl rfl))).1 J
  have hneg := (reciprocalSquare_mass_side_bound u g q T w (-1) (Or.inr rfl)
    (fun i hi => hw i (hi.trans_le (signed_le_abs (Or.inr rfl) _)))
    (fun i hi => hu i (hi.trans_le (signed_le_abs (Or.inr rfl) _)))
    hT (hbound (-1) (Or.inr rfl))).1 J
  have heq (i : ι) : tailTerm g T w i =
      positiveTerm (fun i => 1 * g i) T w i +
        positiveTerm (fun i => -1 * g i) T w i := by
    unfold tailTerm positiveTerm
    simp only [one_mul, neg_one_mul, neg_sq]
    by_cases hg : 0 ≤ g i
    · rw [abs_of_nonneg hg]
      have hn : ¬T < -g i := by linarith
      simp [hn]
    · rw [abs_of_neg (lt_of_not_ge hg)]
      have hn : ¬T < g i := by linarith
      simp [hn]
  simp_rw [heq, mul_add, Finset.sum_add_distrib]
  constructor <;> linarith [hpos.1, hpos.2, hneg.1, hneg.2]

/-- Both mass-weighted tails require only nonnegative widths. Ordinary comparisons
and ordinary tail bounds additionally require positive widths at most two. -/
theorem reciprocalSquare_tail_bound {ι : Type*} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (hw : ∀ i, T < |g i| → 0 ≤ w i)
    (hu : ∀ i, T < |g i| → 0 < w i → 0 ≤ u i)
    (hT : 32 < T)
    (hbound : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2) :
    (∀ J : Finset ι,
      (∑ i ∈ J, massRatio (u i) * tailTerm g T w i ≤ tailBound q T -
        (finiteCorrection q T (fun i => 1 * g i) w J +
          finiteCorrection q T (fun i => -1 * g i) w J)) ∧
      tailBound q T - (finiteCorrection q T (fun i => 1 * g i) w J +
        finiteCorrection q T (fun i => -1 * g i) w J) < tailBound q T) ∧
    Summable (fun i => massRatio (u i) * tailTerm g T w i) ∧
    (∑' i, massRatio (u i) * tailTerm g T w i) ≤ tailBound q T ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 →
      (∀ J : Finset ι,
        (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
          tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
          tailBound q T / 2) ∧
      Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
      (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ≤
        tailBound q T / 2) ∧
    ((∀ i, T < |g i| → 0 < w i → 0 < u i ∧ u i ≤ 2) →
      (∀ J : Finset ι,
        (∑ i ∈ J, tailTerm g T w i) ≤
          (∑ i ∈ J, massRatio (u i) * tailTerm g T w i)) ∧
      Summable (tailTerm g T w) ∧
      (∑' i, tailTerm g T w i) ≤ tailBound q T ∧
      (∀ s : ℝ, s = 1 ∨ s = -1 →
        (∀ J : Finset ι,
          (∑ i ∈ J, positiveTerm (fun i => s * g i) T w i) ≤
            (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i)) ∧
        Summable (positiveTerm (fun i => s * g i) T w) ∧
        (∑' i, positiveTerm (fun i => s * g i) T w i) ≤ tailBound q T / 2)) := by
  have hf := finite_tail_bound u g q T w hw hu hT hbound
  have hm (i : ι) : 0 ≤ massRatio (u i) * tailTerm g T w i := by
    simpa only [positiveTerm, tailTerm, sq_abs] using
      positive_mass_nonneg u (fun i => |g i|) T w hw hu i
  have hb J := ((hf J).1.trans_lt (hf J).2).le
  refine ⟨hf, summable_of_sum_le hm hb, Real.tsum_le_of_sum_le hm hb, ?_, ?_⟩
  · intro s hs
    exact reciprocalSquare_mass_side_bound u g q T w s hs
      (fun i hi => hw i (hi.trans_le (signed_le_abs hs _)))
      (fun i hi => hu i (hi.trans_le (signed_le_abs hs _))) hT (hbound s hs)
  · intro hu2
    have hd (i : ι) : 0 ≤ tailTerm g T w i ∧
        tailTerm g T w i ≤ massRatio (u i) * tailTerm g T w i := by
      simpa only [positiveTerm, tailTerm, sq_abs] using
        positive_le_mass u (fun i => |g i|) T w hw hu2 i
    have hn : 0 ≤ tailTerm g T w := fun i => (hd i).1
    have ho J := (Finset.sum_le_sum (fun i _ => (hd i).2)).trans (hb J)
    refine ⟨(fun J => Finset.sum_le_sum (fun i _ => (hd i).2)),
      summable_of_sum_le hn ho, Real.tsum_le_of_sum_le hn ho, ?_⟩
    intro s hs
    have h := reciprocalSquare_side_bound u g q T w s hs
      (fun i hi => hw i (hi.trans_le (signed_le_abs hs _)))
      (fun i hi => hu2 i (hi.trans_le (signed_le_abs hs _))) hT (hbound s hs)
    exact ⟨(fun J => (h.1 J).1), h.2.1, h.2.2.1⟩

end D5.S3.Analytic.Resolvent.PoissonKernelTail
