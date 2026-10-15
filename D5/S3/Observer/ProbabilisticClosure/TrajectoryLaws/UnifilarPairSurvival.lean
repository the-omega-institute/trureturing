/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonmerged unifilar word affinity is the survival mass of the killed pair matrix. -/

import D5.S3.TotalVariation.Bhattacharyya
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Matrix Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

variable {H : Type*} [Fintype H]

/-- An ordered pair of distinct states of the same producer. -/
abbrev Pair (H : Type*) := {s : H × H // s.1 ≠ s.2}

/-- The final state after the actual shared binary word. -/
def endpoint (δ : H → Bool → H) : (n : ℕ) → H → (Fin n → Bool) → H
  | 0, a, _ => a
  | n + 1, a, w => endpoint δ n (δ a (w 0)) (Fin.tail w)

/-- The emitted-word mass along its unique trajectory, including zero-weight symbols. -/
def wordMass (p : H → Bool → ℝ) (δ : H → Bool → H) :
    (n : ℕ) → H → (Fin n → Bool) → ℝ
  | 0, _, _ => 1
  | n + 1, a, w => p a (w 0) * wordMass p δ n (δ a (w 0)) (Fin.tail w)

/-- Hellinger affinity restricted to words whose two endpoints remain distinct. -/
def survivingAffinity (p : H → Bool → ℝ) (δ : H → Bool → H)
    (n : ℕ) (s : Pair H) : ℝ := by
  classical
  exact D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
    (fun w => if endpoint δ n s.val.1 w ≠ endpoint δ n s.val.2 w
      then wordMass p δ n s.val.1 w else 0)
    (wordMass p δ n s.val.2)

/-- The common-symbol pair transition discards a pair as soon as its states meet. -/
def pairMatrix (p : H → Bool → ℝ) (δ : H → Bool → H) :
    Matrix (Pair H) (Pair H) ℝ := by
  classical
  exact fun s t => ∑ x : Bool,
    if h : δ s.val.1 x ≠ δ s.val.2 x then
      if t = ⟨(δ s.val.1 x, δ s.val.2 x), h⟩
        then Real.sqrt (p s.val.1 x * p s.val.2 x) else 0
    else 0

theorem sum_words (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ w, f w = ∑ x : Bool, ∑ w : Fin n → Bool, f (Fin.cons x w) := by
  let e : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) := {
    toFun := fun w => (w 0, Fin.tail w)
    invFun := fun z => Fin.cons z.1 z.2
    left_inv := fun w => Fin.cons_self_tail w
    right_inv := fun z => by simp }
  calc
    (∑ w, f w) = ∑ z : Bool × (Fin n → Bool), f (Fin.cons z.1 z.2) :=
      Fintype.sum_equiv e f (fun z => f (Fin.cons z.1 z.2))
        (fun w => congrArg f (Fin.cons_self_tail w).symm)
    _ = _ := Fintype.sum_prod_type _

theorem pairMatrix_action (p : H → Bool → ℝ) (δ : H → Bool → H)
    (s : Pair H) (f : Pair H → ℝ) :
    ∑ t, pairMatrix p δ s t * f t = ∑ x : Bool,
      if h : δ s.val.1 x ≠ δ s.val.2 x then
        Real.sqrt (p s.val.1 x * p s.val.2 x) *
          f ⟨(δ s.val.1 x, δ s.val.2 x), h⟩ else 0 := by
  classical
  simp only [pairMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : δ s.val.1 x ≠ δ s.val.2 x
  · simp [h, ite_mul]
  · simp [h]

omit [Fintype H] in
private theorem affinity_step (p : H → Bool → ℝ) (δ : H → Bool → H)
    (hp : ∀ a x, 0 ≤ p a x) (n : ℕ) (s : Pair H) :
    survivingAffinity p δ (n + 1) s = ∑ x : Bool,
      if h : δ s.val.1 x ≠ δ s.val.2 x then
        Real.sqrt (p s.val.1 x * p s.val.2 x) *
          survivingAffinity p δ n ⟨(δ s.val.1 x, δ s.val.2 x), h⟩ else 0 := by
  classical
  unfold survivingAffinity D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
  rw [sum_words]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : δ s.val.1 x ≠ δ s.val.2 x
  · rw [dif_pos h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    change Real.sqrt ((if endpoint δ n (δ s.val.1 x) w ≠ endpoint δ n (δ s.val.2 x) w
      then p s.val.1 x * wordMass p δ n (δ s.val.1 x) w else 0) *
      (p s.val.2 x * wordMass p δ n (δ s.val.2 x) w)) =
      Real.sqrt (p s.val.1 x * p s.val.2 x) *
        Real.sqrt ((if endpoint δ n (δ s.val.1 x) w ≠ endpoint δ n (δ s.val.2 x) w
          then wordMass p δ n (δ s.val.1 x) w else 0) * wordMass p δ n (δ s.val.2 x) w)
    by_cases he : endpoint δ n (δ s.val.1 x) w ≠ endpoint δ n (δ s.val.2 x) w
    · rw [if_pos he, if_pos he]
      rw [show p s.val.1 x * wordMass p δ n (δ s.val.1 x) w *
          (p s.val.2 x * wordMass p δ n (δ s.val.2 x) w) =
          (p s.val.1 x * p s.val.2 x) *
          (wordMass p δ n (δ s.val.1 x) w * wordMass p δ n (δ s.val.2 x) w) by ring]
      exact Real.sqrt_mul (mul_nonneg (hp _ _) (hp _ _)) _
    · simp [he]
  · have he : δ s.val.1 x = δ s.val.2 x := not_ne_iff.mp h
    simp [endpoint, Fin.tail_cons, he]

/-- At every length, the killed pair matrix counts precisely the affinity of nonmerged words. -/
theorem pair_survival_word_affinity (p : H → Bool → ℝ) (δ : H → Bool → H)
    (hp : ∀ a x, 0 ≤ p a x) (n : ℕ) (s : Pair H) :
    (∑ t, (pairMatrix p δ ^ n) s t) = survivingAffinity p δ n s := by
  classical
  induction n generalizing s with
  | zero =>
      simp [survivingAffinity, D5.S3.TotalVariation.Bhattacharyya.bhattacharyya,
        endpoint, wordMass, s.property, Matrix.one_apply]
  | succ n ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      simp_rw [ih]
      rw [pairMatrix_action, affinity_step p δ hp]

#print axioms pair_survival_word_affinity
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
