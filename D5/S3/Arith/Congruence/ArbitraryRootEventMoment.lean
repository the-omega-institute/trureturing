/- GID: D5/S3/Arith/Congruence/ArbitraryRootEventMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ArbitraryRootEventMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Geometric event caps bound square increments under arbitrary root switching. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Arith.Congruence.ArbitraryRootEventMoment

/-- The load counts every occurrence of an event in the finite list. -/
noncomputable def eventLoad {X I : Type*} [DecidableEq X]
    (events : List (I × Finset X)) (x : X) : ℝ :=
  (events.map fun e => if x ∈ e.2 then (1 : ℝ) else 0).sum

/-- Events stay inside their labelled roots; all root caps are multiplied
by the same discount after every event. -/
def geometricRootCaps {X I : Type*} (μ : X → ℝ) (root : X → I)
    (r : ℝ) (d : I → ℝ) : List (I × Finset X) → Prop
  | [] => True
  | (i, s) :: rest =>
      (∀ x ∈ s, root x = i) ∧ (∑ x ∈ s, μ x) ≤ d i ∧
      geometricRootCaps μ root r (fun j => r * d j) rest

/-- A common bound for the constant-root geometric costs also bounds the
actual load-square increment of every finite switching sequence. The roots
need not be finite, events need not be nested, and the discount may be zero. -/
theorem arbitrary_root_event_moment_le
    {X I : Type*} [Fintype X] [DecidableEq X]
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (root : X → I)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (a : I → ℕ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbudget : ∀ i,
      d i * ((2 * (a i : ℝ) + 3) / (1 - r) + 2 * r / (1 - r) ^ 2) ≤ M)
    (W : X → ℝ) (hW : ∀ x, W x ≤ 1 + (a (root x) : ℝ))
    (events : List (I × Finset X))
    (hcaps : geometricRootCaps μ root r d events) :
    (∑ x, μ x * ((W x + eventLoad events x) ^ 2 - W x^2)) ≤ M := by
  classical
  have hs : 0 < 1 - r := sub_pos.mpr hr1
  induction events generalizing d a M W with
  | nil => simpa [eventLoad] using hM
  | cons e rest ih =>
      rcases e with ⟨i, s⟩
      rcases hcaps with ⟨hroot, hmass, hrest⟩
      let c : ℝ := (2 * (a i : ℝ) + 3) * d i
      let v : X → ℝ := fun x => if x ∈ s then 1 else 0
      let a' : I → ℕ := Function.update a i (a i + 1)
      have hcs : c ≤ (1 - r) * M := by
        have hi := mul_le_mul_of_nonneg_left (hbudget i) hs.le
        have expansion : (1 - r) *
            (d i * ((2 * (a i : ℝ) + 3) / (1 - r) + 2 * r / (1 - r) ^ 2)) =
            c + 2 * r * d i / (1 - r) := by
          dsimp [c]
          field_simp
        rw [expansion] at hi
        have htail : 0 ≤ 2 * r * d i / (1 - r) :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (hd i)) hs.le
        linarith
      have hcM : c ≤ M := by nlinarith [mul_nonneg hr hM]
      have nextBudget (j : I) :
          (r * d j) *
            ((2 * (a' j : ℝ) + 3) / (1 - r) + 2 * r / (1 - r) ^ 2) ≤ M - c := by
        by_cases hji : j = i
        · subst j
          have hi := hbudget i
          have balance :
              (r * d i) *
                ((2 * (a' i : ℝ) + 3) / (1 - r) + 2 * r / (1 - r) ^ 2) =
              d i * ((2 * (a i : ℝ) + 3) / (1 - r) + 2 * r / (1 - r) ^ 2) - c := by
            simp only [a', Function.update_self, Nat.cast_add, Nat.cast_one]
            dsimp [c]
            field_simp
            ring
          rw [balance]
          linarith
        · simp only [a', Function.update_of_ne hji]
          have hj := mul_le_mul_of_nonneg_left (hbudget j) hr
          nlinarith
      have nextLoad : ∀ x, W x + v x ≤ 1 + (a' (root x) : ℝ) := by
        intro x
        have hw := hW x
        by_cases hx : x ∈ s
        · rw [hroot x hx] at hw ⊢
          simp only [a', Function.update_self, Nat.cast_add, Nat.cast_one, v, if_pos hx]
          linarith
        · simp only [v, if_neg hx, add_zero]
          by_cases heq : root x = i
          · simp only [a', heq, Function.update_self, Nat.cast_add, Nat.cast_one]
            rw [heq] at hw
            linarith
          · simpa only [a', Function.update_of_ne heq] using hw
      have correction : (∑ x, μ x * ((W x + v x) ^ 2 - W x^2)) ≤ c := by
        calc
          _ ≤ ∑ x, if x ∈ s then (2 * (a i : ℝ) + 3) * μ x else 0 := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hx : x ∈ s
            · have hw := hW x
              rw [hroot x hx] at hw
              simp only [v, if_pos hx]
              nlinarith [mul_nonneg (hμ x) (sub_nonneg.mpr hw)]
            · simp [v, hx]
          _ = (2 * (a i : ℝ) + 3) * (∑ x ∈ s, μ x) := by
            rw [← Finset.sum_filter]
            simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
            rw [Finset.mul_sum]
          _ ≤ c := mul_le_mul_of_nonneg_left hmass (by positivity)
      have tail := ih (fun j => r * d j) (fun j => mul_nonneg hr (hd j))
        a' (M - c) (sub_nonneg.mpr hcM) nextBudget
        (fun x => W x + v x) nextLoad hrest
      have telescoping :
          (∑ x, μ x * ((W x + eventLoad ((i, s) :: rest) x) ^ 2 - W x^2)) =
          (∑ x, μ x * (((W x + v x) + eventLoad rest x) ^ 2 - (W x + v x) ^ 2)) +
          (∑ x, μ x * ((W x + v x) ^ 2 - W x^2)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        simp only [eventLoad, List.map_cons, List.sum_cons]
        dsimp [v]
        ring
      rw [telescoping]
      linarith

#print axioms arbitrary_root_event_moment_le

end D5.S3.Arith.Congruence.ArbitraryRootEventMoment
