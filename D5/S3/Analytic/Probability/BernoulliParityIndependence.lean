/- GID: D5/S3/Analytic/Probability/BernoulliParityIndependence
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/BernoulliParityIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Characterize independence of two parity events under a Bernoulli product law. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The covariance of two parity indicators factors through their symmetric
difference and their intersection. -/

open scoped BigOperators symmDiff

namespace D5.S3.Analytic.Probability.BernoulliParityIndependence

private def bitSign (b : Bool) : ℝ := if b then -1 else 1

private def bitMass (t : ℝ) (b : Bool) : ℝ := if b then t else 1 - t

private def paritySign {I : Type*} (s : Finset I) (x : I → Bool) : ℝ :=
  ∏ i ∈ s, bitSign (x i)

private theorem paritySign_pm_one {I : Type*} (s : Finset I) (x : I → Bool) :
    paritySign s x = 1 ∨ paritySign s x = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp [paritySign]
  | @insert i s hi ih =>
    have hfactor : paritySign (insert i s) x = bitSign (x i) * paritySign s x :=
      Finset.prod_insert hi
    rw [hfactor]
    cases h : x i <;> rcases ih with hs | hs <;> simp [bitSign, hs]

private theorem paritySign_mul {I : Type*} [DecidableEq I]
    (s t : Finset I) (x : I → Bool) :
    paritySign s x * paritySign t x = paritySign (s ∆ t) x := by
  have hdis : Disjoint (s ∆ t) (s ∩ t) := disjoint_symmDiff_inf s t
  have hunion : (s ∆ t) ∪ (s ∩ t) = s ∪ t := symmDiff_sup_inf s t
  have hsquare : (∏ i ∈ s ∩ t, bitSign (x i)) * ∏ i ∈ s ∩ t, bitSign (x i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    cases x i <;> simp [bitSign]
  unfold paritySign
  rw [← Finset.prod_union_inter, ← hunion, Finset.prod_union hdis, mul_assoc, hsquare, mul_one]

open Classical in
private theorem paritySign_expectation {I : Type*} [Fintype I]
    (p : I → ℝ) (s : Finset I) :
    (∑ x : I → Bool, (∏ i, bitMass (p i) (x i)) * paritySign s x) =
      ∏ i ∈ s, (1 - 2 * p i) := by
  unfold paritySign
  have hfactor (x : I → Bool) :
      (∏ i ∈ s, bitSign (x i)) = ∏ i, if i ∈ s then bitSign (x i) else 1 := by
    rw [← Finset.prod_filter]
    simp
  simp_rw [hfactor, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => bitMass (p i) b *
    (if i ∈ s then bitSign b else 1))]
  have hsum (i : I) :
      (∑ b : Bool, bitMass (p i) b * (if i ∈ s then bitSign b else 1)) =
        if i ∈ s then 1 - 2 * p i else 1 := by
    have hBool : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hBool]
    by_cases hi : i ∈ s <;> simp [hi, bitMass, bitSign] <;> ring
  simp_rw [hsum]
  rw [← Finset.prod_filter]
  simp

private noncomputable def eventIndicator {I : Type*}
    (s : Finset I) (d : Bool) (x : I → Bool) : ℝ :=
  (1 + bitSign d * paritySign s x) / 2

private theorem eventIndicator_eq {I : Type*} (s : Finset I) (d : Bool) (x : I → Bool) :
    eventIndicator s d x = if paritySign s x = bitSign d then 1 else 0 := by
  rcases paritySign_pm_one s x with h | h <;> cases d <;> norm_num [eventIndicator, bitSign, h]

open Classical in
private theorem joint_event_factorization {I : Type*} [Fintype I]
    (p : I → ℝ) (s t : Finset I) (d e : Bool) :
    let w (x : I → Bool) := ∏ i, bitMass (p i) (x i)
    let mass (s : Finset I) (d : Bool) := ∑ x, w x * eventIndicator s d x
    let joint := ∑ x, w x * (eventIndicator s d x * eventIndicator t e x)
    let bias (s : Finset I) := ∏ i ∈ s, (1 - 2 * p i)
    joint - mass s d * mass t e =
      bitSign d * bitSign e * bias (s ∆ t) * (1 - (bias (s ∩ t)) ^ 2) / 4 := by
  intro w mass joint bias
  have htotal : ∑ x, w x = 1 := by
    simpa [w, paritySign] using paritySign_expectation p (∅ : Finset I)
  have hmoment (r : Finset I) : ∑ x, w x * paritySign r x = bias r :=
    paritySign_expectation p r
  have hsingle (r : Finset I) (a : Bool) :
      mass r a = (1 + bitSign a * bias r) / 2 := by
    change (∑ x, w x * eventIndicator r a x) = _
    calc
      _ = (∑ x, (w x + bitSign a * (w x * paritySign r x))) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        unfold eventIndicator
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, hmoment]
  have hjoint :
      joint = (1 + bitSign d * bias s + bitSign e * bias t +
        (bitSign d * bitSign e) * bias (s ∆ t)) / 4 := by
    change (∑ x, w x * (eventIndicator s d x * eventIndicator t e x)) = _
    calc
      _ = (∑ x, (w x + bitSign d * (w x * paritySign s x) +
          bitSign e * (w x * paritySign t x) +
            (bitSign d * bitSign e) * (w x * paritySign (s ∆ t) x))) / 4 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        rw [← paritySign_mul]
        unfold eventIndicator
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, hmoment]
  have hprod : bias s * bias t = bias (s ∆ t) * (bias (s ∩ t)) ^ 2 := by
    have hdis : Disjoint (s ∆ t) (s ∩ t) := disjoint_symmDiff_inf s t
    have hunion : (s ∆ t) ∪ (s ∩ t) = s ∪ t := symmDiff_sup_inf s t
    dsimp [bias]
    rw [← Finset.prod_union_inter, ← hunion, Finset.prod_union hdis, mul_assoc, pow_two]
  rw [hjoint, hsingle, hsingle]
  calc
    _ = bitSign d * bitSign e * (bias (s ∆ t) - bias s * bias t) / 4 := by ring
    _ = _ := by rw [hprod]; ring

open Classical in
/-- The indicators are independent for disjoint supports or when a fair input
appears in exactly one support. -/
theorem parity_events_independent_iff {I : Type*} [Fintype I]
    (p : I → ℝ) (s t : Finset I) (d e : Bool)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1 / 2) :
    let w (x : I → Bool) := ∏ i, bitMass (p i) (x i)
    let mass (s : Finset I) (d : Bool) :=
      ∑ x, if paritySign s x = bitSign d then w x else 0
    let joint := ∑ x, if paritySign s x = bitSign d ∧ paritySign t x = bitSign e then w x else 0
    joint = mass s d * mass t e ↔ Disjoint s t ∨ ∃ i ∈ s ∆ t, p i = 1 / 2 := by
  intro w mass joint
  let bias (s : Finset I) := ∏ i ∈ s, (1 - 2 * p i)
  have hsingle (s : Finset I) (d : Bool) :
      mass s d = ∑ x, w x * eventIndicator s d x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [eventIndicator_eq]
    by_cases h : paritySign s x = bitSign d <;> simp [h]
  have hjoint : joint = ∑ x, w x * (eventIndicator s d x * eventIndicator t e x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [eventIndicator_eq, eventIndicator_eq]
    by_cases hs : paritySign s x = bitSign d <;>
      by_cases ht : paritySign t x = bitSign e <;> simp [hs, ht]
  have hcov : joint - mass s d * mass t e =
      bitSign d * bitSign e * bias (s ∆ t) * (1 - (bias (s ∩ t)) ^ 2) / 4 := by
    rw [hjoint, hsingle, hsingle]
    exact joint_event_factorization p s t d e
  have hsign (d : Bool) : bitSign d ≠ 0 := by cases d <;> norm_num [bitSign]
  have hn (i : I) : 0 ≤ 1 - 2 * p i := by linarith [(hp i).2]
  have hlt (i : I) : 1 - 2 * p i < 1 := by linarith [(hp i).1]
  have hzero : bias (s ∆ t) = 0 ↔ ∃ i ∈ s ∆ t, p i = 1 / 2 := by
    rw [show bias (s ∆ t) = _ from rfl, Finset.prod_eq_zero_iff]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    constructor <;> intro h <;> linarith
  have hsame : 1 - (bias (s ∩ t)) ^ 2 = 0 ↔ Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    constructor
    · intro hz
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hlow : 0 ≤ bias (s ∩ t) := Finset.prod_nonneg (fun i _ => hn i)
      have hhigh : bias (s ∩ t) < 1 := by
        dsimp [bias]
        rw [← Finset.prod_erase_mul _ _ hi]
        exact (mul_le_of_le_one_left (hn i)
          (Finset.prod_le_one₀ (fun j _ => hn j) (fun j _ => (hlt j).le))).trans_lt (hlt i)
      nlinarith
    · intro h
      simp [bias, h]
  rw [← sub_eq_zero, hcov, div_eq_zero_iff, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  simp only [hsign, false_or, show (4 : ℝ) ≠ 0 by norm_num, or_false, hzero, hsame]
  exact or_comm

end D5.S3.Analytic.Probability.BernoulliParityIndependence
