/- GID: D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Universal modular invariants of the overlap-two grid transfer. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
The row index is zero-based: `row R n k` denotes b_(n+1)(k).
These are algebraically defined transfer rows, not the actual packing count.
The missing insertion/deletion correspondence must identify A(j) with
`row ℕ (j-1) 3` before their residues apply to the source permutations.
Escape audits: https://github.com/the-omega-institute/trureturing/issues/28504.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer

open scoped BigOperators

/-- The sum from r=1 to k, with summation variable shifted down by one. -/
def transfer {R : Type*} [Semiring R] (f : ℕ → R) (k : ℕ) : R :=
  ∑ r ∈ Finset.range k, (r + 1 : R) * f (r + 3)

/-- The initial row is constant one, including auxiliary arguments below three. -/
def row (R : Type*) [Semiring R] : ℕ → ℕ → R
  | 0, _ => 1
  | n + 1, k => transfer (row R n) k

private theorem transfer_succ {R : Type*} [Semiring R] (f : ℕ → R) (k : ℕ) :
    transfer f (k + 1) = transfer f k + (k + 1 : R) * f (k + 3) := by
  exact Finset.sum_range_succ _ _

private def firstProfile (k : ℕ) : ZMod 5 :=
  ![0, 1, 3, 1, 0] ⟨k % 5, Nat.mod_lt _ (by decide)⟩

private def stableProfile (k : ℕ) : ZMod 5 :=
  ![0, 1, 1, 1, 0] ⟨k % 5, Nat.mod_lt _ (by decide)⟩

private theorem profile_steps (k : ℕ) :
    firstProfile (k + 1) = firstProfile k + (k + 1 : ZMod 5) ∧
    stableProfile (k + 1) = stableProfile k +
      (k + 1 : ZMod 5) * firstProfile (k + 3) ∧
    stableProfile (k + 1) = stableProfile k +
      (k + 1 : ZMod 5) * stableProfile (k + 3) := by
  have hc : (k : ZMod 5) = (k % 5 : ℕ) := by simp
  have hk := Nat.mod_lt k (by decide : 0 < 5)
  interval_cases h : k % 5 <;>
    norm_num [firstProfile, stableProfile, Nat.add_mod, h, Nat.cast_add, hc]

private theorem transfer_one : transfer (fun _ => (1 : ZMod 5)) = firstProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih, mul_one]
    exact (profile_steps k).1.symm

private theorem transfer_first : transfer firstProfile = stableProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih]
    exact (profile_steps k).2.1.symm

private theorem transfer_stable : transfer stableProfile = stableProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih]
    exact (profile_steps k).2.2.symm

private theorem rows_stabilize (n : ℕ) : row (ZMod 5) (n + 2) = stableProfile := by
  induction n with
  | zero => exact (congrArg transfer transfer_one).trans transfer_first
  | succ n ih =>
    change transfer (row (ZMod 5) (n + 2)) = stableProfile
    rw [ih, transfer_stable]

/-- Every transfer row has residue one at the source's argument three. -/
theorem row_mod_five (n : ℕ) : row (ZMod 5) n 3 = 1 := by
  rcases n with _ | _ | n
  · rfl
  · exact congrFun transfer_one 3
  · rw [rows_stabilize]
    rfl

end D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
