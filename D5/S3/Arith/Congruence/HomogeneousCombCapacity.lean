/- GID: D5/S3/Arith/Congruence/HomogeneousCombCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/HomogeneousCombCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset]
   utility: none
   digest: One forbidden prefix per depth bounds actual homogeneous tree flow below by comb flow. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
The obstacle predicate is on actual finite words over Fin p. Its value at
each prefix blocks that whole subtree. The flow recursively applies the
node capacity and sums the actual child-subtree flows. The global hypothesis
counts forbidden words at each depth, including redundant blocked descendants.

Search result: repository congruence and capacity declarations, pinned Mathlib
tree and finite-sum declarations, and public LeanSearch searches for homogeneous
tree capacity and comb extremality supplied no matching theorem. Mathlib's
finite-sum inequalities are used directly. This is a symbolic theorem for every
branching number, finite height, obstacle predicate and nonnegative capacity
profile; it has no computational-instance content.
-/

open Finset

namespace D5.S3.Arith.Congruence.HomogeneousCombCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Number of forbidden words at the given depth, before removing redundancy. -/
def forbiddenCount (p : ℕ) (f : List (Fin p) → Bool) : ℕ → ℕ
  | 0 => if f [] then 1 else 0
  | n + 1 => ∑ i : Fin p, forbiddenCount p (fun w => f (i :: w)) n

/-- The capacity recursion on the actual forbidden-prefix tree. -/
noncomputable def prefixFlow (p : ℕ) :
    ℕ → (ℕ → ℝ) → (List (Fin p) → Bool) → ℝ
  | 0, β, f => if f [] then 0 else β 0
  | n + 1, β, f => if f [] then 0 else
      min (β 0) (∑ i : Fin p,
        prefixFlow p n (fun d => β (d + 1)) (fun w => f (i :: w)))

/-- Homogeneous capacity recursion with no forbidden nodes. -/
noncomputable def fullFlow (p : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, β => β 0
  | n + 1, β => min (β 0) ((p : ℝ) * fullFlow p n (fun d => β (d + 1)))

/-- One blocked child, p-2 full children and one continuing child at every depth. -/
noncomputable def combFlow (p : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, β => β 0
  | n + 1, β => min (β 0)
      (((p - 2 : ℕ) : ℝ) * fullFlow p n (fun d => β (d + 1)) +
        combFlow p n (fun d => β (d + 1)))

/-- Loss envelope for an arbitrary nonnegative number of forbidden nodes per depth. -/
noncomputable def depthLoss (p : ℕ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | 0, _, _ => 0
  | n + 1, β, a => max 0
      (a 0 * fullFlow p n (fun d => β (d + 1)) +
        depthLoss p n (fun d => β (d + 1)) (fun d => a (d + 1)) -
        ((p : ℝ) * fullFlow p n (fun d => β (d + 1)) - fullFlow p (n + 1) β))

/-- A full p-ary actual prefix tree with at most one forbidden word at each
positive depth has capacity flow at least the homogeneous comb recursion. -/
theorem comb_le_actual_prefix_flow
    (p H : ℕ) (hp : 2 ≤ p) (β : ℕ → ℝ) (hβ : ∀ d, 0 ≤ β d)
    (f : List (Fin p) → Bool) (hroot : f [] = false)
    (hlevels : ∀ d < H, forbiddenCount p f (d + 1) ≤ 1) :
    combFlow p H β ≤ prefixFlow p H β f := by
  classical
  have full_nonneg : ∀ n (b : ℕ → ℝ), (∀ d, 0 ≤ b d) → 0 ≤ fullFlow p n b := by
    intro n
    induction n with
    | zero => intro b hb; exact hb 0
    | succ n ih =>
        intro b hb
        exact le_min (hb 0) (mul_nonneg (Nat.cast_nonneg p) (ih _ (fun d => hb _)))
  have loss_nonneg (n : ℕ) (b a : ℕ → ℝ) : 0 ≤ depthLoss p n b a := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have loss_mono : ∀ n (b a c : ℕ → ℝ), (∀ d, 0 ≤ b d) →
      (∀ d < n, a d ≤ c d) → depthLoss p n b a ≤ depthLoss p n b c := by
    intro n
    induction n with
    | zero => intros; exact le_rfl
    | succ n ih =>
        intro b a c hb hac
        apply max_le_max le_rfl
        apply sub_le_sub_right
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hac 0 (Nat.zero_lt_succ n))
            (full_nonneg n _ (fun d => hb _)))
          (ih _ _ _ (fun d => hb _) (fun d hd => hac (d + 1) (by omega)))
  have loss_superadd : ∀ n (b a c : ℕ → ℝ), (∀ d, 0 ≤ b d) →
      (∀ d, 0 ≤ a d) → (∀ d, 0 ≤ c d) →
      depthLoss p n b a + depthLoss p n b c ≤
        depthLoss p n b (fun d => a d + c d) := by
    intro n
    induction n with
    | zero => intros; simp [depthLoss]
    | succ n ih =>
        intro b a c hb ha hc
        have hF := full_nonneg n (fun d => b (d + 1)) (fun d => hb _)
        have hs : 0 ≤ (p : ℝ) * fullFlow p n (fun d => b (d + 1)) -
            fullFlow p (n + 1) b :=
          sub_nonneg.mpr (min_le_right (b 0)
            ((p : ℝ) * fullFlow p n (fun d => b (d + 1))))
        have ha' := mul_nonneg (ha 0) hF
        have hc' := mul_nonneg (hc 0) hF
        have hla := loss_nonneg n (fun d => b (d + 1)) (fun d => a (d + 1))
        have hlc := loss_nonneg n (fun d => b (d + 1)) (fun d => c (d + 1))
        have ih' := ih (fun d => b (d + 1)) (fun d => a (d + 1))
          (fun d => c (d + 1)) (fun d => hb _) (fun d => ha _) (fun d => hc _)
        simp only [depthLoss]
        simp only [max_def]
        split_ifs <;> nlinarith
  have loss_sum : ∀ n (b : ℕ → ℝ), (∀ d, 0 ≤ b d) →
      ∀ (s : Finset (Fin p)) (a : Fin p → ℕ → ℝ), (∀ i d, 0 ≤ a i d) →
      (∑ i ∈ s, depthLoss p n b (a i)) ≤
        depthLoss p n b (fun d => ∑ i ∈ s, a i d) := by
    intro n b hb s a ha
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using loss_nonneg n b (fun _ => 0)
    | @insert i s his ih =>
        simp only [Finset.sum_insert his]
        exact (add_le_add le_rfl ih).trans
          (loss_superadd n b (a i) (fun d => ∑ j ∈ s, a j d) hb
            (ha i) (fun d => Finset.sum_nonneg (fun j hj => ha j d)))
  have actual_bound : ∀ n (b : ℕ → ℝ) (g : List (Fin p) → Bool),
      (∀ d, 0 ≤ b d) →
      0 ≤ prefixFlow p n b g ∧ prefixFlow p n b g ≤ fullFlow p n b ∧
      fullFlow p n b - prefixFlow p n b g ≤
        (forbiddenCount p g 0 : ℝ) * fullFlow p n b +
          depthLoss p n b (fun d => (forbiddenCount p g (d + 1) : ℝ)) := by
    intro n
    induction n with
    | zero =>
        intro b g hb
        cases hg : g [] <;> simp [prefixFlow, fullFlow, forbiddenCount, depthLoss, hg, hb]
    | succ n ih =>
        intro b g hb
        have ihc (i : Fin p) := ih (fun d => b (d + 1))
          (fun w => g (i :: w)) (fun d => hb _)
        have sum_upper : (∑ i : Fin p,
            prefixFlow p n (fun d => b (d + 1)) (fun w => g (i :: w))) ≤
              (p : ℝ) * fullFlow p n (fun d => b (d + 1)) := by
          simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin p))) =>
            (ihc i).2.1)
        have sum_nonneg : 0 ≤ ∑ i : Fin p,
            prefixFlow p n (fun d => b (d + 1)) (fun w => g (i :: w)) :=
          Finset.sum_nonneg (fun i hi => (ihc i).1)
        cases hg : g [] with
        | true =>
            simp only [prefixFlow, hg, ↓reduceIte, forbiddenCount,
              Nat.cast_one, one_mul, sub_zero, le_refl, true_and]
            exact ⟨full_nonneg (n + 1) b hb,
              le_add_of_nonneg_right (loss_nonneg _ _ _)⟩
        | false =>
            have deficit_sum := Finset.sum_le_sum
              (fun i (_ : i ∈ (Finset.univ : Finset (Fin p))) => (ihc i).2.2)
            have aggregate := loss_sum n (fun d => b (d + 1)) (fun d => hb _)
              Finset.univ (fun i d => (forbiddenCount p (fun w => g (i :: w)) (d + 1) : ℝ))
              (fun i d => Nat.cast_nonneg _)
            have hcount (d : ℕ) :
                (∑ i : Fin p, (forbiddenCount p (fun w => g (i :: w)) d : ℝ)) =
                  (forbiddenCount p g (d + 1) : ℝ) := by
              simp [forbiddenCount]
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, Finset.sum_add_distrib,
              ← Finset.sum_mul, hcount] at deficit_sum
            simp only [hcount] at aggregate
            have loss_upper :
                (p : ℝ) * fullFlow p n (fun d => b (d + 1)) -
                  (∑ i : Fin p, prefixFlow p n (fun d => b (d + 1))
                    (fun w => g (i :: w))) ≤
                (forbiddenCount p g 1 : ℝ) * fullFlow p n (fun d => b (d + 1)) +
                  depthLoss p n (fun d => b (d + 1))
                    (fun d => (forbiddenCount p g (d + 2) : ℝ)) :=
              deficit_sum.trans (add_le_add le_rfl aggregate)
            simp only [prefixFlow, hg, Bool.false_eq_true, ↓reduceIte, forbiddenCount,
              Nat.cast_zero, zero_mul, zero_add]
            refine ⟨le_min (hb 0) sum_nonneg, min_le_min_left _ sum_upper, ?_⟩
            change fullFlow p (n + 1) b - min (b 0) _ ≤
              max 0 ((forbiddenCount p g 1 : ℝ) *
                fullFlow p n (fun d => b (d + 1)) +
                depthLoss p n (fun d => b (d + 1))
                  (fun d => (forbiddenCount p g (d + 2) : ℝ)) -
                ((p : ℝ) * fullFlow p n (fun d => b (d + 1)) - fullFlow p (n + 1) b))
            have cap := min_le_left (b 0) ((p : ℝ) * fullFlow p n (fun d => b (d + 1)))
            change fullFlow p (n + 1) b ≤ b 0 at cap
            rw [min_def]
            split_ifs
            · exact (sub_nonpos.mpr cap).trans (le_max_left _ _)
            · linarith [le_max_right (0 : ℝ)
                 ((forbiddenCount p g 1 : ℝ) *
                   fullFlow p n (fun d => b (d + 1)) +
                   depthLoss p n (fun d => b (d + 1))
                     (fun d => (forbiddenCount p g (d + 2) : ℝ)) -
                   ((p : ℝ) * fullFlow p n (fun d => b (d + 1)) -
                     fullFlow p (n + 1) b))]
  have comb_identity : ∀ n (b : ℕ → ℝ), (∀ d, 0 ≤ b d) →
      fullFlow p n b - combFlow p n b = depthLoss p n b (fun _ => 1) := by
    intro n
    induction n with
    | zero => intro b hb; simp [fullFlow, combFlow, depthLoss]
    | succ n ih =>
        intro b hb
        have ih' := ih (fun d => b (d + 1)) (fun d => hb _)
        have hF := full_nonneg n (fun d => b (d + 1)) (fun d => hb _)
        have hL := loss_nonneg n (fun d => b (d + 1)) (fun _ => 1)
        have hC : combFlow p n (fun d => b (d + 1)) ≤
            fullFlow p n (fun d => b (d + 1)) := by linarith
        simp only [fullFlow, combFlow, depthLoss, one_mul, Nat.cast_sub hp, Nat.cast_ofNat]
        simp only [min_def, max_def]
        split_ifs <;> nlinarith
  have bound := (actual_bound H β f hβ).2.2
  have mono := loss_mono H β
    (fun d => (forbiddenCount p f (d + 1) : ℝ)) (fun _ => 1) hβ
    (fun d hd => by exact_mod_cast hlevels d hd)
  have root_count : forbiddenCount p f 0 = 0 := by simp [forbiddenCount, hroot]
  rw [root_count, Nat.cast_zero, zero_mul, zero_add] at bound
  linarith [comb_identity H β hβ]

#print axioms comb_le_actual_prefix_flow

end D5.S3.Arith.Congruence.HomogeneousCombCapacity
