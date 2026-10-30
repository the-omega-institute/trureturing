/- GID: D5/S1/Words/FibonacciIncidence
   generality: G
   mirror-B: D5/B/S1/Words/FibonacciIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci substitution words act on Parikh vectors by a reusable incidence matrix and transport arbitrary additive observables. -/

import D5.S1.Words.GoldenGapPrefix
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace D5.S1.Words.FibonacciIncidence

open D5.S0.Tower.GoldenGapWord

/-- The Parikh vector of a binary word, indexed by its actual Bool alphabet. -/
def parikh (w : List Bool) : Bool → ℕ :=
  fun b => w.count b

/-- One Fibonacci substitution step on a finite word. -/
def substitute (w : List Bool) : List Bool :=
  w.flatMap subst

/-- Iterated Fibonacci substitution, with the zeroth iterate equal to the input word. -/
def iterate : ℕ → List Bool → List Bool
  | 0, w => w
  | n + 1, w => substitute (iterate n w)

/-- The incidence matrix has output letters as rows and input letters as columns. -/
def incidence : Matrix Bool Bool ℕ :=
  fun output input => parikh (subst input) output

/-- An additive observable obtained by assigning a value to each letter. -/
def weightedSum {R : Type*} [AddCommMonoid R] (weight : Bool → R)
    (w : List Bool) : R :=
  (w.map weight).sum

@[simp] theorem parikh_nil : parikh [] = 0 := by
  ext b
  simp [parikh]

@[simp] theorem parikh_append (u v : List Bool) (b : Bool) :
    parikh (u ++ v) b = parikh u b + parikh v b := by
  simp [parikh]

theorem parikh_substitute (w : List Bool) :
    parikh (substitute w) = incidence.mulVec (parikh w) := by
  funext b
  induction w with
  | nil =>
      simp [substitute, parikh, incidence, Matrix.mulVec_apply_eq_sum,
        Fintype.univ_bool]
  | cons a w ih =>
      change parikh (subst a ++ substitute w) b = _
      rw [parikh_append, ih]
      cases a <;> cases b <;>
        simp [parikh, incidence, subst, Matrix.mulVec_apply_eq_sum,
          Fintype.univ_bool] <;> omega

theorem parikh_iterate (n : ℕ) (w : List Bool) :
    parikh (iterate n w) = (incidence ^ n).mulVec (parikh w) := by
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      rw [iterate, parikh_substitute, ih]
      simpa [pow_succ'] using
        (Matrix.mulVec_mulVec (parikh w) incidence (incidence ^ n)).symm

theorem weightedSum_eq_parikh {R : Type*} [AddCommMonoid R]
    (weight : Bool → R) (w : List Bool) :
    weightedSum weight w = ∑ b : Bool, parikh w b • weight b := by
  induction w with
  | nil =>
      simp [weightedSum, parikh, Fintype.univ_bool]
  | cons b w ih =>
      change weight b + weightedSum weight w = _
      rw [ih]
      cases b <;>
        simp [parikh, Fintype.univ_bool, add_nsmul] <;> ac_rfl

theorem weighted_iterate {R : Type*} [AddCommMonoid R]
    (weight : Bool → R) (n : ℕ) (w : List Bool) :
    weightedSum weight (iterate n w) =
      ∑ b : Bool, ((incidence ^ n).mulVec (parikh w)) b • weight b := by
  rw [weightedSum_eq_parikh, parikh_iterate]

theorem fibWord_eq_iterate (n : ℕ) :
    D5.S0.Tower.GoldenGapWord.fibWord n = iterate n [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [D5.S0.Tower.GoldenGapWord.fibWord, iterate, substitute, ih]

theorem fibWord_parikh (n : ℕ) :
    parikh (D5.S0.Tower.GoldenGapWord.fibWord n) =
      (fun b : Bool => if b = true then Nat.fib (n + 1) else Nat.fib n) := by
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · ext b
    cases b <;> simp [D5.S0.Tower.GoldenGapWord.fibWord, parikh, Nat.fib]
  · ext b
    cases b <;> simp [D5.S0.Tower.GoldenGapWord.fibWord, subst, parikh, Nat.fib]
  · intro n hn hn1
    rw [D5.S1.Words.fibWord_append_rec]
    funext b
    rw [parikh_append]
    rw [congrFun hn1 b, congrFun hn b]
    cases b
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.fib_add_two (n := n)).symm
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.fib_add_two (n := n + 1)).symm

end D5.S1.Words.FibonacciIncidence
