/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarMapDomination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Grouped endpoint MAP loss is dominated by nonmerged unordered initial affinities. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarMapDomination
variable {S C : Type*} [Fintype S] [DecidableEq S] [DecidableEq C]

/-- Half the ordered off-diagonal sum, equal to the sum over any ordering a < b. -/
def pairWeight (pi : S → ℝ) : ℝ :=
  (∑ i, ∑ j, if i ≠ j then Real.sqrt (pi i * pi j) else 0) / 2

private theorem sqrt_group (a : S → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : S → C) (m : C) (i : S)
    (hi : a i ≤ ∑ j, if f j = m then a j else 0) :
    a i ≤ ∑ j, if f j = m then Real.sqrt (a i*a j) else 0 := by
  let g : S → ℝ := fun j => if f j = m then Real.sqrt (a i*a j) else 0
  have hn (j : S) : 0 ≤ g j := by dsimp [g]; split_ifs <;> positivity
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := g) (fun j _ => hn j)
  have he : ∑ j, g j^2 = a i * ∑ j, if f j = m then a j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    split_ifs <;> simp [Real.sq_sqrt (mul_nonneg (ha i) (ha j))]
  rw [he] at hs
  have hn' : 0 ≤ ∑ j, g j := Finset.sum_nonneg (fun j _ => hn j)
  have hm := mul_le_mul_of_nonneg_left hi (ha i)
  change a i ≤ ∑ j, g j
  nlinarith

/-- This estimate applies to actual endpoint groups, including zero groups and ties.
Its sum omits all pairs whose final states have merged. -/
theorem grouped_map_pair_bound (a : S → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : S → C) (m : C)
    (hm : ∀ c, (∑ i, if f i = c then a i else 0) ≤
      ∑ i, if f i = m then a i else 0) :
    (∑ i, a i) - (∑ i, if f i = m then a i else 0) ≤
      (∑ i, ∑ j, if f i ≠ f j then Real.sqrt (a i*a j) else 0) / 2 := by
  classical
  let star : S → S → ℝ := fun i j =>
    if f i ≠ m ∧ f j = m then Real.sqrt (a i*a j) else 0
  have hstar : (∑ i, a i) - (∑ i, if f i = m then a i else 0) ≤
      ∑ i, ∑ j, star i j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : f i = m
    · simp [star,hi]
    · simp only [if_neg hi,sub_zero]
      have hlocal : a i ≤ ∑ j, if f j = f i then a j else 0 := by
        calc
          a i = if f i = f i then a i else 0 := by simp
          _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (a := i)
            (f := fun j => if f j = f i then a j else 0) (by
              intro j _
              split_ifs
              · exact ha j
              · exact le_rfl) (Finset.mem_univ i)
      simpa only [star,ne_eq,hi,not_false_eq_true,true_and] using sqrt_group a ha f m i (hlocal.trans (hm (f i)))
  have hdouble : 2*(∑ i, ∑ j, star i j) ≤
      ∑ i, ∑ j, if f i ≠ f j then Real.sqrt (a i*a j) else 0 := by
    have hpoint (i j : S) : star i j+star j i ≤
        if f i ≠ f j then Real.sqrt (a i*a j) else 0 := by
      dsimp [star]
      by_cases hi : f i = m <;> by_cases hj : f j = m <;>
        by_cases hij : f i = f j <;> simp_all [mul_comm,Real.sqrt_nonneg] <;> positivity
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
    simp only [Finset.sum_add_distrib] at hsum
    rw [Finset.sum_comm (f := fun i j => star j i)] at hsum
    linarith
  linarith

/-- The coefficient is the source unordered sum and has the stationary cardinal bound. -/
theorem pair_weight_bound (pi : S → ℝ) (hp : ∀ i, 0 ≤ pi i) (hs : ∑ i, pi i = 1) :
    0 ≤ pairWeight pi ∧ pairWeight pi ≤ ((Fintype.card S : ℝ)-1)/2 ∧
    (∀ (_ : LinearOrder S), pairWeight pi =
      ∑ i, ∑ j, if i < j then Real.sqrt (pi i*pi j) else 0) := by
  classical
  have hoff : (∑ i, ∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
      (∑ i, Real.sqrt (pi i))^2-1 := by
    have hsplit (i : S) : (∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
        (∑ j, Real.sqrt (pi i*pi j)) - pi i := by
      have he : (∑ j, if i = j then Real.sqrt (pi i*pi j) else 0) = pi i := by
        simp [Real.sqrt_mul_self (hp i)]
      have hall : (∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) +
          (∑ j, if i = j then Real.sqrt (pi i*pi j) else 0) =
          ∑ j, Real.sqrt (pi i*pi j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij]
      linarith
    simp_rw [hsplit,Real.sqrt_mul (hp _)]
    rw [Finset.sum_sub_distrib,hs,← Finset.sum_mul_sum]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : S => Real.sqrt (pi i)) (g := fun _ : S => (1:ℝ))
  simp only [mul_one,Real.sq_sqrt (hp _),hs,one_pow,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,one_mul] at hcs
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
    split_ifs <;> positivity))) (by norm_num),?_,?_⟩
  · dsimp [pairWeight]
    rw [hoff]
    linarith
  · intro order
    letI := order
    have hsplit (i j : S) : (if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
        (if i < j then Real.sqrt (pi i*pi j) else 0) +
        (if j < i then Real.sqrt (pi i*pi j) else 0) := by
      rcases lt_trichotomy i j with h | h | h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,h.le]
    unfold pairWeight
    simp_rw [hsplit,Finset.sum_add_distrib]
    have he : (∑ i, ∑ j, if j < i then Real.sqrt (pi i*pi j) else 0) =
        ∑ i, ∑ j, if i < j then Real.sqrt (pi i*pi j) else 0 := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [he]
    ring

#print axioms grouped_map_pair_bound
#print axioms pair_weight_bound
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarMapDomination
