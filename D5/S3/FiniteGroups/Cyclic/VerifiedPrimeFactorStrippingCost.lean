/- GID: D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStrippingCost
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStrippingCost
   mirror-E: none(waiver:general-monoid-recursion)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Exact power-test accounting and logarithmic resource bound. -/

import D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStripping
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact accounting for the executable power-equality tests in prime stripping. -/

set_option autoImplicit false

namespace PrimeFactorStrippingCost

open PrimeFactorStripping

/-- The output and number of power-equality tests made by one factor pass. -/
def stripFactorCost {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (p m : ℕ) : ℕ × ℕ :=
  if h : 1 < p ∧ 0 < m ∧ p ∣ m then
    if hp : x ^ (m / p) = 1 then
      let r := stripFactorCost x p (m / p)
      (r.1, r.2 + 1)
    else (m, 1)
  else (m, 0)
termination_by m
decreasing_by exact Nat.div_lt_self h.2.1 h.1

/-- The output and total number of power-equality tests over the supplied list. -/
def stripFactorsCost {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ) : ℕ × ℕ :=
  P.foldl (fun r p =>
    let s := stripFactorCost x p r.1
    (s.1, r.2 + s.2)) (m, 0)

private theorem stripFactorCost_fst {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (p m : ℕ) : (stripFactorCost x p m).1 = stripFactor x p m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : 1 < p ∧ 0 < m ∧ p ∣ m
    · by_cases hp : x ^ (m / p) = 1
      · have hlt : m / p < m := Nat.div_lt_self h.2.1 h.1
        have hfull : 1 < p ∧ 0 < m ∧ p ∣ m ∧ x ^ (m / p) = 1 :=
          ⟨h.1, h.2.1, h.2.2, hp⟩
        rw [stripFactorCost, dite_eq_left h, dite_eq_left hp, stripFactor, dite_eq_left hfull]
        exact ih (m / p) hlt
      · have hfull : ¬(1 < p ∧ 0 < m ∧ p ∣ m ∧ x ^ (m / p) = 1) := by
          intro hf
          exact hp hf.2.2.2
        rw [stripFactorCost, dite_eq_left h, dite_eq_right hp, stripFactor, dite_eq_right hfull]
    · have hfull : ¬(1 < p ∧ 0 < m ∧ p ∣ m ∧ x ^ (m / p) = 1) := by
        intro hf
        exact h ⟨hf.1, hf.2.1, hf.2.2.1⟩
      rw [stripFactorCost, dite_eq_right h, stripFactor, dite_eq_right hfull]

private theorem stripFactorCost_budget {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (p m : ℕ) :
    (stripFactorCost x p m).2 + Nat.log 2 (stripFactorCost x p m).1 ≤
      1 + Nat.log 2 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : 1 < p ∧ 0 < m ∧ p ∣ m
    · by_cases hp : x ^ (m / p) = 1
      · have hlt : m / p < m := Nat.div_lt_self h.2.1 h.1
        have hp2 : 2 ≤ p := by omega
        have hm_p : p ≤ m := Nat.le_of_dvd h.2.1 h.2.2
        have hm2 : 2 ≤ m := hp2.trans hm_p
        have hdiv : m / p ≤ m / 2 := Nat.div_le_div_left hp2 (by decide)
        rw [stripFactorCost, dite_eq_left h, dite_eq_left hp]
        dsimp
        have hi := ih (m / p) hlt
        calc
          (stripFactorCost x p (m / p)).2 + 1 +
              Nat.log 2 (stripFactorCost x p (m / p)).1 ≤
              (1 + Nat.log 2 (m / p)) + 1 := by omega
          _ ≤ 1 + Nat.log 2 m := by
            have hstep : Nat.log 2 (m / p) + 1 ≤ Nat.log 2 m := by
              calc
                Nat.log 2 (m / p) + 1 ≤ Nat.log 2 (m / 2) + 1 :=
                  Nat.add_le_add_right (Nat.log_mono_right hdiv) 1
                _ = Nat.log 2 m := by
                  symm
                  exact Nat.log_of_one_lt_of_le (b := 2) (n := m) (by decide) hm2
            omega
      · rw [stripFactorCost, dite_eq_left h, dite_eq_right hp]
    · simp [stripFactorCost, h]

private theorem stripFactorsCost_fold {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m c : ℕ) :
    (P.foldl (fun r p =>
      let s := stripFactorCost x p r.1
      (s.1, r.2 + s.2)) (m, c)).1 =
      P.foldl (fun n p => stripFactor x p n) m := by
  induction P generalizing m c with
  | nil => rfl
  | cons p P ih =>
    simp only [List.foldl]
    calc
      (P.foldl (fun r p =>
          let s := stripFactorCost x p r.1
          (s.1, r.2 + s.2))
          ((stripFactorCost x p m).1, c + (stripFactorCost x p m).2)).1 =
          P.foldl (fun n p => stripFactor x p n) (stripFactorCost x p m).1 := ih _ _
      _ = P.foldl (fun n p => stripFactor x p n) (stripFactor x p m) :=
        congrArg (fun n => P.foldl (fun n p => stripFactor x p n) n)
          (stripFactorCost_fst x p m)

private theorem stripFactorsCost_count_fold {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m c : ℕ) :
    (P.foldl (fun r p =>
      let s := stripFactorCost x p r.1
      (s.1, r.2 + s.2)) (m, c)).2 ≤ c + P.length + Nat.log 2 m := by
  induction P generalizing m c with
  | nil => simp
  | cons p P ih =>
    let s := stripFactorCost x p m
    have hs := stripFactorCost_budget x p m
    simp only [List.foldl]
    have hi := ih s.1 (c + s.2)
    dsimp [s] at hi ⊢
    calc
      (P.foldl (fun r p =>
          let t := stripFactorCost x p r.1
          (t.1, r.2 + t.2)) ((stripFactorCost x p m).1, c + (stripFactorCost x p m).2)).2 ≤
          (c + (stripFactorCost x p m).2) + P.length + Nat.log 2 (stripFactorCost x p m).1 := hi
      _ ≤ c + (P.length + 1) + Nat.log 2 m := by
        omega

/-- The cost instrument preserves the original numeric output and counts at most one
power test per list entry plus one test for every successful division. -/
/-
proof_shape: content
escape_witness: stripFactorCost_budget, the live telescoping inequality
  count + Nat.log 2 output ≤ 1 + Nat.log 2 input
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping
  statement_id=sha256:f7057762ad30365e0185653dd26f24f5955b5c6ae000fe2ed82c658a4c75b632
private helpers: stripFactorCost_fst (bind-only, consumed by stripFactorsCost_fold);
  stripFactorCost_budget (content, consumed by stripFactorsCost_count_fold);
  stripFactorsCost_fold (bind-only, consumed by stripFactorsCost_spec);
  stripFactorsCost_count_fold (content, consumed by stripFactorsCost_spec).
-/
theorem stripFactorsCost_spec {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ) :
    let result := stripFactorsCost x P m
    result.1 = stripFactors x P m ∧
      result.2 ≤ P.length + Nat.log 2 m := by
  constructor
  · simpa [stripFactorsCost, stripFactors] using stripFactorsCost_fold x P m 0
  · simpa [stripFactorsCost, Nat.zero_add] using stripFactorsCost_count_fold x P m 0

end PrimeFactorStrippingCost
