/- GID: D5/S3/Arith/Congruence/TwoRootEventMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TwoRootEventMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint roots and geometric mass caps bound actual event-load square increments. -/

import D5.S3.Arith.Congruence.TernaryRootLoadTail
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators
open D5.S3.Arith.Congruence.TernaryRootLoadTail

namespace D5.S3.Arith.Congruence.TwoRootEventMoment

/-- Each occurrence of an event contributes its indicator to the load. -/
noncomputable def eventLoad {X : Type*} [DecidableEq X]
    (events : List (Bool × Finset X)) (x : X) : ℝ :=
  (events.map fun e => if x ∈ e.2 then (1 : ℝ) else 0).sum

/-- Each event lies in its indicated root. Its mass is bounded by the
current root cap; both caps decrease by a factor of three at each step. -/
def rootEventCaps {X : Type*} (μ : X → ℝ) (root : X → Bool)
    (d₀ d₁ : ℝ) : List (Bool × Finset X) → Prop
  | [] => True
  | (r, s) :: rest =>
      (∀ x ∈ s, root x = r) ∧
      (∑ x ∈ s, μ x) ≤ (if r then d₁ else d₀) ∧
      rootEventCaps μ root (d₀ / 3) (d₁ / 3) rest

/-- The actual square increment from any finite event sequence obeys the
root potential. The initial load is bounded separately on the two roots. -/
theorem two_root_event_moment_le {X : Type*} [Fintype X] [DecidableEq X]
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (root : X → Bool)
    (d₀ d₁ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (a b : ℕ) (W : X → ℝ)
    (hW : ∀ x, W x ≤ 1 + if root x then (b : ℝ) else (a : ℝ))
    (events : List (Bool × Finset X)) (hcaps : rootEventCaps μ root d₀ d₁ events) :
    (∑ x, μ x * ((W x + eventLoad events x)^2 - W x ^ 2)) ≤
      3 * max (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2)) := by
  classical
  have scale (u v : ℝ) (a b : ℕ) (rs : List Bool) :
      rootLoadTail (u / 3) (v / 3) a b rs = rootLoadTail u v a b rs / 3 := by
    induction rs generalizing a b with
    | nil => simp [rootLoadTail]
    | cons r rs ih =>
      cases r <;> simp only [rootLoadTail, ih] <;> ring
  have estimate (d₀ d₁ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
      (a b : ℕ) (W : X → ℝ)
      (hW : ∀ x, W x ≤ 1 + if root x then (b : ℝ) else (a : ℝ))
      (events : List (Bool × Finset X))
      (hcaps : rootEventCaps μ root d₀ d₁ events) :
      (∑ x, μ x * ((W x + eventLoad events x)^2 - W x ^ 2)) ≤
        rootLoadTail d₀ d₁ a b (events.map Prod.fst) := by
    induction events generalizing d₀ d₁ a b W with
    | nil => simp [eventLoad, rootLoadTail]
    | cons e rest ih =>
      rcases e with ⟨r, s⟩
      rcases hcaps with ⟨hroot, hmass, hrest⟩
      let v : X → ℝ := fun x => if x ∈ s then 1 else 0
      have expansion :
          (∑ x, μ x * ((W x + eventLoad ((r,s)::rest) x)^2 - W x^2)) =
          (∑ x, μ x * (((W x + v x) + eventLoad rest x)^2 - (W x + v x)^2)) +
          (∑ x, μ x * ((W x + v x)^2 - W x^2)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        simp only [eventLoad, List.map_cons, List.sum_cons]
        dsimp [v]
        ring
      have correction : (∑ x, μ x * ((W x + v x)^2 - W x^2)) ≤
          (3 + 2 * (if r then (b : ℝ) else (a : ℝ))) *
            (∑ x ∈ s, μ x) := by
        calc
          _ ≤ ∑ x, if x ∈ s then
              (3 + 2 * (if r then (b : ℝ) else (a : ℝ))) * μ x else 0 := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hx : x ∈ s
            · have hw := hW x
              rw [hroot x hx] at hw
              simp only [v, if_pos hx]
              nlinarith [mul_nonneg (hμ x)
                (sub_nonneg.mpr hw)]
            · simp [v, hx]
          _ = _ := by
            rw [← Finset.sum_filter]
            simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
            rw [Finset.mul_sum]
      cases r with
      | false =>
        have next : ∀ x, W x + v x ≤
            1 + if root x then (b : ℝ) else ((a+1 : ℕ) : ℝ) := by
          intro x
          have hw := hW x
          by_cases hx : x ∈ s
          · rw [hroot x hx] at hw ⊢
            simp only [Bool.false_eq_true, if_false] at hw
            simp only [v, if_pos hx, Bool.false_eq_true, if_false,
              Nat.cast_add, Nat.cast_one]
            linarith
          · simp only [v, if_neg hx, add_zero]
            split_ifs with hr
            · simpa [hr] using hw
            · simp only [Nat.cast_add, Nat.cast_one]
              simp [hr] at hw
              linarith
        have tail := ih (d₀/3) (d₁/3) (by positivity) (by positivity)
          (a+1) b (fun x => W x + v x) next hrest
        rw [scale] at tail
        simp only [Bool.false_eq_true, if_false] at correction hmass
        have hfactor : 0 ≤ 3 + 2 * (a : ℝ) := by positivity
        have bound := mul_le_mul_of_nonneg_left hmass hfactor
        rw [expansion]
        simp only [List.map_cons, rootLoadTail]
        linarith
      | true =>
        have next : ∀ x, W x + v x ≤
            1 + if root x then ((b+1 : ℕ) : ℝ) else (a : ℝ) := by
          intro x
          have hw := hW x
          by_cases hx : x ∈ s
          · rw [hroot x hx] at hw ⊢
            simp only [if_true] at hw
            simp only [v, if_pos hx, if_true, Nat.cast_add, Nat.cast_one]
            linarith
          · simp only [v, if_neg hx, add_zero]
            split_ifs with hr
            · simp only [Nat.cast_add, Nat.cast_one]
              simp only [hr, if_true] at hw
              linarith
            · simpa [hr] using hw
        have tail := ih (d₀/3) (d₁/3) (by positivity) (by positivity)
          a (b+1) (fun x => W x + v x) next hrest
        rw [scale] at tail
        simp only [if_true] at correction hmass
        have hfactor : 0 ≤ 3 + 2 * (b : ℝ) := by positivity
        have bound := mul_le_mul_of_nonneg_left hmass hfactor
        rw [expansion]
        simp only [List.map_cons, rootLoadTail]
        linarith
  exact (estimate d₀ d₁ hd₀ hd₁ a b W hW events hcaps).trans
    (root_load_tail_le d₀ d₁ hd₀ hd₁ a b (events.map Prod.fst))

#print axioms two_root_event_moment_le

end D5.S3.Arith.Congruence.TwoRootEventMoment
