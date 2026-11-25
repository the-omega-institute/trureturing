/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftLimit
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The all-degree left boundary limit of the positive-center ordered BMV log kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenter
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-! # The left boundary of the positive-center refined BMV log kernel -/

noncomputable section

namespace RefinedBMV.PositiveCenter

open Filter Set
open scoped Topology

open DimThree (defect defect_corner defect_corner_eq_iff gaps mem_gaps_iff_total word_counts_all)
open UniformThreeSpectrum (defect_cycle_all)

private abbrev Gap := ℕ × ℕ × ℕ

private def exponent (p n : ℕ) : ℝ := 3 * (n : ℝ) / p - 1

private def gapCount (p : ℕ) : ℝ := (gaps p).length

private theorem gapCount_pos (p : ℕ) : 0 < gapCount p := by
  unfold gapCount
  exact_mod_cast (word_counts_all p).2.1

private theorem compositionMoment_zero_zero (p : ℕ) :
    compositionMoment p 0 0 = 0 := by
  change ((gaps p).map (fun g ↦ Real.exp
    (exponent p g.2.1 * 0 + exponent p g.2.2 * 0))).sum / gapCount p - 1 = 0
  have h : ((gaps p).map (fun _ ↦ (1 : ℝ))).sum = gapCount p := by simp [gapCount]
  simp only [mul_zero, add_zero, Real.exp_zero, h, div_self (gapCount_pos p).ne', sub_self]

/-- A nonzero marginal gap gives a strictly positive centered moment. -/
theorem compositionMoment_marginal_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    0 < compositionMoment p 0 t := by
  let x := Real.exp (t / (p : ℝ))
  have hx : 0 < x := Real.exp_pos _
  have hcoord : logCoordinate p 1 x = t := by
    simpa only [one_mul] using logCoordinate_mul_exp hp zero_lt_one t
  have hne : (1 : ℝ) ≠ x := by
    intro h
    rw [← h, logCoordinate, div_one, Real.log_one, mul_zero] at hcoord
    exact ht hcoord.symm
  have hdef : 0 < defect p 1 1 x := by
    rw [← defect_cycle_all p 1 1 x]
    refine (Real.sqrt_nonneg _).trans_lt (lt_of_le_of_ne
      (defect_corner p zero_le_one hx.le zero_le_one) ?_)
    intro h
    exact ((defect_corner_eq_iff p zero_le_one hx.le zero_le_one).mp h).elim hp.ne' hne
  have h := defect_eq_compositionMoment hp zero_lt_one zero_lt_one hx
  rw [show logCoordinate p 1 1 = 0 by simp [logCoordinate], hcoord] at h
  rw [h] at hdef
  exact pos_of_mul_pos_right hdef
    (mul_pos (gapCount_pos p) (pow_pos (mul_pos (mul_pos zero_lt_one zero_lt_one) hx) p)).le

private theorem hasDerivAt_exp_sum (l : List Gap) (w a b : Gap → ℝ) (x : ℝ) :
    HasDerivAt (fun t ↦ (l.map fun g ↦ w g * Real.exp (a g * t + b g)).sum)
      (l.map fun g ↦ (w g * a g) * Real.exp (a g * x + b g)).sum x := by
  induction l with
  | nil => simpa using (hasDerivAt_const x (0 : ℝ))
  | cons g l ih =>
    have hg : HasDerivAt (fun t ↦ w g * Real.exp (a g * t + b g))
        ((w g * a g) * Real.exp (a g * x + b g)) x := by
      convert (((hasDerivAt_const_mul (a g)).add_const (b g)).exp.const_mul (w g)) using 1
      ring
    exact hg.add ih

private def affineRate (p : ℕ) (r s : ℝ) (g : Gap) : ℝ :=
  exponent p g.2.1 * r + exponent p g.2.2 * s

private def momentRate (p : ℕ) (u v r s : ℝ) : ℝ :=
  ((gaps p).map fun g ↦ affineRate p r s g * Real.exp (affineRate p u v g)).sum / gapCount p

private theorem hasDerivAt_compositionMoment_affine (p : ℕ) (u v r s x : ℝ) :
    HasDerivAt (fun t ↦ compositionMoment p (u + r * t) (v + s * t))
      (momentRate p (u + r * x) (v + s * x) r s) x := by
  have h := ((hasDerivAt_exp_sum (gaps p) (fun _ ↦ 1)
    (affineRate p r s) (affineRate p u v) x).div_const (gapCount p)).sub_const 1
  have harg (g : Gap) (t : ℝ) :
      affineRate p r s g * t + affineRate p u v g =
        affineRate p (u + r * t) (v + s * t) g := by
    unfold affineRate
    ring
  simp only [one_mul, harg] at h
  exact h

/-- The first-coordinate slope at zero is the weighted marginal sum. -/
theorem deriv_compositionMoment_fst_zero (p : ℕ) (v : ℝ) :
    deriv (fun u ↦ compositionMoment p u v) 0 =
      ((gaps p).map fun g ↦ (3 * (g.2.1 : ℝ) / (p : ℝ) - 1) *
        Real.exp ((3 * (g.2.2 : ℝ) / (p : ℝ) - 1) * v)).sum /
          ((gaps p).length : ℝ) := by
  simpa only [mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, momentRate, gapCount, affineRate, exponent] using
    (hasDerivAt_compositionMoment_affine p 0 v 1 0 0).deriv

private theorem momentRate_neg_both (p : ℕ) (v : ℝ) :
    momentRate p 0 v (-1) (-1) = -momentRate p 0 v 1 0 - momentRate p 0 v 0 1 := by
  have h (g : Gap) :
      affineRate p (-1) (-1) g * Real.exp (affineRate p 0 v g) =
        (-1) * (affineRate p 1 0 g * Real.exp (affineRate p 0 v g)) +
          (-1) * (affineRate p 0 1 g * Real.exp (affineRate p 0 v g)) := by
    simp only [affineRate, mul_zero, mul_one, mul_neg, zero_add, add_zero]
    ring
  simp only [momentRate, h, List.sum_map_add, List.sum_map_mul_left]
  simp only [add_div, neg_one_mul, neg_div, sub_eq_add_neg]

/-- The exact numerator has zero first derivative at the left endpoint. -/
theorem hasDerivAt_logKernel_numerator_zero {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun u ↦ compositionMoment p u v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v - u))) 0 0 := by
  let A := momentRate p 0 v 1 0
  let B := momentRate p 0 v 0 1
  have hleft : HasDerivAt (fun u ↦ compositionMoment p u v) A 0 := by
    simpa only [A, one_mul, zero_add, zero_mul, add_zero] using
      hasDerivAt_compositionMoment_affine p 0 v 1 0 0
  have hswap : HasDerivAt (fun u ↦ compositionMoment p (-u) (v - u)) (-A - B) 0 := by
    simpa only [zero_add, A, B, mul_zero, add_zero, neg_one_mul, sub_eq_add_neg,
      momentRate_neg_both] using hasDerivAt_compositionMoment_affine p 0 v (-1) (-1) 0
  have hsame := hswap.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ compositionMoment_swap_center hp u v)
  have hab : A = -A - B := hleft.unique hsame
  have hmarginal : HasDerivAt (fun t ↦ compositionMoment p 0 t) B v := by
    simpa only [B, zero_mul, zero_add, one_mul] using
      hasDerivAt_compositionMoment_affine p 0 0 0 1 v
  have hshift : HasDerivAt (fun u : ℝ ↦ v - u) (-1) 0 := by
    exact (hasDerivAt_id' 0).const_sub v
  have hm := compositionMoment_marginal_pos hp hv.ne'
  have harg : HasDerivAt (fun u ↦ compositionMoment p 0 v * compositionMoment p 0 (v - u))
      (compositionMoment p 0 v * (-B)) 0 := by
    have h : HasDerivAt (fun t ↦ compositionMoment p 0 t) B (v - 0) := by
      simpa only [sub_zero] using hmarginal
    simpa only [Function.comp_apply, mul_neg, mul_one] using (h.comp 0 hshift).const_mul _
  have hsqrt := harg.sqrt (by simpa only [sub_zero] using mul_ne_zero hm.ne' hm.ne')
  refine (hleft.sub hsqrt).congr_deriv ?_
  rw [sub_zero, Real.sqrt_mul_self hm.le]
  field_simp [hm.ne']
  linarith only [hab]

/-- The exact numerator vanishes at the left endpoint. -/
theorem logKernel_numerator_zero {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    compositionMoment p 0 v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 v) = 0 := by
  rw [Real.sqrt_mul_self (compositionMoment_marginal_pos hp hv.ne').le, sub_self]

/-- The numerator divided by the lower log gap tends to zero from the ordered side. -/
theorem tendsto_logKernel_numerator_div_zero {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun u ↦ (compositionMoment p u v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v - u))) / u)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [zero_add, sub_zero, logKernel_numerator_zero hp hv, smul_eq_mul,
    ← div_eq_inv_mul] using (hasDerivAt_logKernel_numerator_zero hp hv).tendsto_slope_zero_right

/-- The second moment of the last exponent, which is centered for positive degree. -/
def compositionMarginalVariance (p : ℕ) : ℝ :=
  ((gaps p).map fun g ↦ (3 * (g.2.2 : ℝ) / p - 1) ^ 2).sum / (gaps p).length

theorem compositionMarginalVariance_pos (p : ℕ) : 0 < compositionMarginalVariance p := by
  unfold compositionMarginalVariance
  refine div_pos ?_ (gapCount_pos p)
  let f (g : Gap) := (3 * (g.2.2 : ℝ) / p - 1) ^ 2
  have hg : (p, 0, 0) ∈ gaps p := (mem_gaps_iff_total _ _).mpr (by simp)
  have hf : f (p, 0, 0) = 1 := by simp [f]
  have hm := List.mem_map_of_mem (f := f) hg
  rw [hf] at hm
  change 0 < ((gaps p).map f).sum
  refine zero_lt_one.trans_le (List.single_le_sum (fun y hy ↦ ?_) 1 hm)
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hy
  exact sq_nonneg _

private def negativeMarginalDerivative (p : ℕ) (t : ℝ) : ℝ :=
  ((gaps p).map fun g ↦ -exponent p g.2.2 * Real.exp (-exponent p g.2.2 * t)).sum /
    gapCount p

private theorem hasDerivAt_negativeMarginal (p : ℕ) (t : ℝ) :
    HasDerivAt (fun u ↦ compositionMoment p 0 (-u)) (negativeMarginalDerivative p t) t := by
  simpa only [momentRate, affineRate, negativeMarginalDerivative, zero_mul, mul_zero,
    zero_add, mul_neg, mul_one, one_mul, neg_mul, neg_one_mul] using
    hasDerivAt_compositionMoment_affine p 0 0 0 (-1) t

private theorem negativeMarginalDerivative_zero {p : ℕ} (hp : 0 < p) :
    negativeMarginalDerivative p 0 = 0 := by
  have hmin : IsLocalMin (fun u ↦ compositionMoment p 0 (-u)) 0 := by
    refine Filter.Eventually.of_forall fun u ↦ ?_
    simp only [neg_zero, compositionMoment_zero_zero]
    by_cases hu : u = 0
    · simp [hu, compositionMoment_zero_zero]
    · exact (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu)).le
  exact hmin.hasDerivAt_eq_zero (hasDerivAt_negativeMarginal p 0)

/-- The last centered exponent has zero sum over the compositions. -/
theorem composition_last_exponent_sum_zero {p : ℕ} (hp : 0 < p) :
    ((gaps p).map fun g ↦ 3 * (g.2.2 : ℝ) / (p : ℝ) - 1).sum = 0 := by
  have h := negativeMarginalDerivative_zero hp
  have hterm : ((gaps p).map fun g ↦ -exponent p g.2.2).sum =
      -((gaps p).map fun g ↦ exponent p g.2.2).sum := by
    calc
      _ = ((gaps p).map fun g ↦ (-1 : ℝ) * exponent p g.2.2).sum := by
        simp only [neg_one_mul]
      _ = _ := by rw [List.sum_map_mul_left, neg_one_mul]
  simp only [negativeMarginalDerivative, mul_zero, Real.exp_zero, mul_one, hterm, neg_div,
    neg_eq_zero] at h
  exact (div_eq_zero_iff.mp h).resolve_right (gapCount_pos p).ne'

private theorem hasDerivAt_negativeMarginalDerivative_zero (p : ℕ) :
    HasDerivAt (negativeMarginalDerivative p) (compositionMarginalVariance p) 0 := by
  have h := (hasDerivAt_exp_sum (gaps p) (fun g ↦ -exponent p g.2.2)
    (fun g ↦ -exponent p g.2.2) (fun _ ↦ 0) 0).div_const (gapCount p)
  simp only [add_zero, mul_zero, Real.exp_zero, mul_one, ← sq, neg_sq] at h
  exact h

/-- The quadratic coefficient of the marginal in the lower weight is half the variance. -/
theorem tendsto_compositionMoment_neg_div_sq {p : ℕ} (hp : 0 < p) :
    Tendsto (fun u ↦ compositionMoment p 0 (-u) / u ^ 2) (𝓝[>] 0)
      (𝓝 (compositionMarginalVariance p / 2)) := by
  have hslope : Tendsto (fun u ↦ negativeMarginalDerivative p u / u) (𝓝[>] 0)
      (𝓝 (compositionMarginalVariance p)) := by
    simpa only [zero_add, negativeMarginalDerivative_zero hp, sub_zero, smul_eq_mul,
      ← div_eq_inv_mul] using (hasDerivAt_negativeMarginalDerivative_zero p).tendsto_slope_zero_right
  have hdiv : Tendsto (fun u ↦ negativeMarginalDerivative p u / (2 * u)) (𝓝[>] 0)
      (𝓝 (compositionMarginalVariance p / 2)) :=
    (hslope.div_const 2).congr fun u ↦ by rw [div_div, mul_comm u 2]
  have hsq (u : ℝ) : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * u) u := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 u
  refine HasDerivAt.lhopital_zero_nhdsGT
    (.of_forall (hasDerivAt_negativeMarginal p)) (.of_forall hsq) ?_ ?_ ?_ hdiv
  · filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    exact mul_ne_zero two_ne_zero hu.ne'
  · have h := (hasDerivAt_negativeMarginal p 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [neg_zero, compositionMoment_zero_zero] using h
  · have h := (hsq 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [zero_pow (show (2 : ℕ) ≠ 0 by decide)] using h

/-- At fixed positive upper log gap, the ordered kernel tends to zero at the left boundary. -/
theorem tendsto_logKernel_left {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun u ↦ logKernel p u v) (𝓝[>] 0) (𝓝 0) := by
  have hm := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hvar : 0 < compositionMarginalVariance p / 2 :=
    div_pos (compositionMarginalVariance_pos p) zero_lt_two
  have hden := ((tendsto_compositionMoment_neg_div_sq hp).mul_const
    (compositionMoment p 0 (-v))).sqrt
  have h := (tendsto_logKernel_numerator_div_zero hp hv).div hden
    (Real.sqrt_pos.2 (mul_pos hvar hm)).ne'
  rw [zero_div] at h
  refine (tendsto_congr' ?_).2 h
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  have hfactor : compositionMoment p 0 (-u) * compositionMoment p 0 (-v) =
      u ^ 2 * (compositionMoment p 0 (-u) / u ^ 2 * compositionMoment p 0 (-v)) := by
    field_simp [hu.ne']
  simp only [logKernel, hfactor, Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu.le,
    Pi.div_apply, div_div]

#print axioms logKernel_numerator_zero
#print axioms hasDerivAt_logKernel_numerator_zero
#print axioms tendsto_logKernel_numerator_div_zero
#print axioms tendsto_compositionMoment_neg_div_sq
#print axioms tendsto_logKernel_left

end RefinedBMV.PositiveCenter
