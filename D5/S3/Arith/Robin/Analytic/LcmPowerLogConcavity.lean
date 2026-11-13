/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLogConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict logarithmic concavity of real power differences. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Logarithmic concavity of the difference of two consecutive real powers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity

def powerDifference (κ t : ℝ) : ℝ := (1 + t) ^ κ - t ^ κ

def logPowerDifference (κ t : ℝ) : ℝ := Real.log (powerDifference κ t)

private def cfirst (κ t : ℝ) : ℝ :=
  κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1))

private def csecond (κ t : ℝ) : ℝ :=
  κ * (κ - 1) * ((1 + t) ^ (κ - 2) - t ^ (κ - 2))

lemma difference_pos {κ t : ℝ} (hκ : 1 < κ) (ht : 0 ≤ t) :
    0 < powerDifference κ t := by
  apply sub_pos.mpr
  exact Real.rpow_lt_rpow ht (by linarith) (by linarith)

private lemma first_derivative {κ t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerDifference κ) (cfirst κ t) t := by
  have ha := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := κ) (Or.inl (by linarith : 1 + t ≠ 0))
  have hb := (hasDerivAt_id t).rpow_const (p := κ) (Or.inl ht.ne')
  convert ha.sub hb using 1
  · rfl
  · simp only [cfirst, id_eq, one_mul]
    ring

private lemma second_derivative {κ t : ℝ} (ht : 0 < t) :
    HasDerivAt (cfirst κ) (csecond κ t) t := by
  have ha := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := κ - 1) (Or.inl (by linarith : 1 + t ≠ 0))
  have hb := (hasDerivAt_id t).rpow_const (p := κ - 1) (Or.inl ht.ne')
  convert (ha.sub hb).const_mul κ using 1
  · rfl
  · simp only [csecond, id_eq, one_mul, show κ - 1 - 1 = κ - 2 by ring]
    ring

private lemma curvature_identity {κ t : ℝ} (ht : 0 < t) :
    (cfirst κ t) ^ 2 - powerDifference κ t * csecond κ t =
      κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) ^ 2 +
        κ * (κ - 1) * (t * (1 + t)) ^ (κ - 2) := by
  have hp (x : ℝ) (hx : 0 < x) :
      x ^ κ = x ^ (κ - 2) * x ^ 2 ∧
        x ^ (κ - 1) = x ^ (κ - 2) * x := by
    constructor
    · calc
        x ^ κ = x ^ ((κ - 2) + 2) := by congr 1 <;> ring
        _ = _ := by rw [Real.rpow_add hx, Real.rpow_two]
    · calc
        x ^ (κ - 1) = x ^ ((κ - 2) + 1) := by congr 1 <;> ring
        _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
  have ha := hp (1 + t) (by linarith)
  have hb := hp t ht
  simp only [cfirst, csecond, powerDifference]
  rw [ha.1, hb.1, ha.2, hb.2, Real.mul_rpow ht.le (by linarith : 0 ≤ 1 + t)]
  ring

private lemma second_deriv_value {κ t : ℝ} (ht : 0 < t) :
    deriv (deriv (powerDifference κ)) t = csecond κ t := by
  have heq : deriv (powerDifference κ) =ᶠ[𝓝 t] cfirst κ := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (first_derivative hx).deriv
  exact ((second_derivative ht).congr_of_eventuallyEq heq).deriv

/-- The exact positive-curvature numerator identity for a unit power difference. -/
theorem powerDifference_curvature {κ t : ℝ} (ht : 0 < t) :
    (deriv (powerDifference κ) t) ^ (2 : ℝ) -
        powerDifference κ t * deriv (deriv (powerDifference κ)) t =
      κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) ^ (2 : ℝ) +
        κ * (κ - 1) * (t * (1 + t)) ^ (κ - 2) := by
  simp only [Real.rpow_two]
  rw [(first_derivative ht).deriv, second_deriv_value ht]
  exact curvature_identity ht

lemma log_derivative {κ t : ℝ} (hκ : 1 < κ) (ht : 0 < t) :
    HasDerivAt (logPowerDifference κ)
      (κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) / powerDifference κ t) t := by
  exact (first_derivative ht).log (difference_pos hκ ht.le).ne'

private lemma log_second_derivative {κ t : ℝ} (hκ : 1 < κ) (ht : 0 < t) :
    HasDerivAt (deriv (logPowerDifference κ))
      ((csecond κ t * powerDifference κ t - (cfirst κ t) ^ 2) /
        (powerDifference κ t) ^ 2) t := by
  have hd := (second_derivative (κ := κ) ht).div (first_derivative ht)
    (difference_pos hκ ht.le).ne'
  have heq : deriv (logPowerDifference κ) =ᶠ[𝓝 t]
      (fun x => cfirst κ x / powerDifference κ x) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (log_derivative hκ hx).deriv
  apply HasDerivAt.congr_of_eventuallyEq (by convert hd using 1 <;> ring) heq

/-- The logarithm of the unit power difference is strictly concave in the
positive half-line, concave up to zero, and vanishes at zero. -/
theorem logPowerDifference_concavity {κ : ℝ} (hκ : 1 < κ) :
    StrictConcaveOn ℝ (Ioi 0) (logPowerDifference κ) ∧
      ConcaveOn ℝ (Ici 0) (logPowerDifference κ) ∧
        logPowerDifference κ 0 = 0 := by
  have hc : ContinuousOn (powerDifference κ) (Ici 0) := by
    apply ContinuousOn.sub
    · exact (continuous_const.add continuous_id).continuousOn.rpow_const
        (fun _ _ => Or.inr (by linarith : 0 ≤ κ))
    · exact continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith : 0 ≤ κ))
  have hb : ContinuousOn (logPowerDifference κ) (Ici 0) :=
    hc.log (fun t ht => (difference_pos hκ ht).ne')
  have hs : StrictConcaveOn ℝ (Ici 0) (logPowerDifference κ) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Ici 0) hb
    intro t ht
    have ht : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hp : 0 < κ * (κ - 1) * (t * (1 + t)) ^ (κ - 2) :=
      mul_pos (mul_pos (by linarith) (by linarith))
        (Real.rpow_pos_of_pos (mul_pos ht (by linarith)) _)
    have hcurv := powerDifference_curvature (κ := κ) ht
    simp only [Real.rpow_two] at hcurv
    rw [(first_derivative ht).deriv, second_deriv_value ht] at hcurv
    have hnonneg : 0 ≤ κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hn : csecond κ t * powerDifference κ t - (cfirst κ t) ^ 2 < 0 := by
      nlinarith
    have hneg := div_neg_of_neg_of_pos hn (sq_pos_of_pos (difference_pos hκ ht.le))
    simpa only [Function.iterate_succ_apply, Function.iterate_zero, id_eq] using
      (log_second_derivative hκ ht).deriv.trans_lt hneg
  refine ⟨hs.subset Ioi_subset_Ici_self (convex_Ioi 0), hs.concaveOn, ?_⟩
  simp [logPowerDifference, powerDifference, Real.zero_rpow (by linarith : κ ≠ 0)]

end D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
