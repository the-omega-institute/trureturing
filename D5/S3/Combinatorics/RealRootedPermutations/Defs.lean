/- GID: D5/S3/Combinatorics/RealRootedPermutations/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RealRootedPermutations/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.Data.Fin.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Basic]
   utility: none
   digest: Pinned definitions for coefficient-sorting permutations of positive real-rooted products. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic

open Polynomial
open scoped BigOperators

namespace D5.S3.Combinatorics.RealRootedPermutations

noncomputable section

 /-- Coefficient of x^k in (1 + r₀x)(1 + r₁x)⋯(1 + r_{n}x). -/
 noncomputable def coeffs {n : ℕ} (r : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
   (∏ i : Fin (n + 1), (1 + C (r i) * X)).coeff k

 /-- Unimodal permutation of [n+1] in the sense of (4): with peak value m = π(last), the positions of the values 0,…,m increase and the positions of m,…,n decrease. Values and positions are 0-based; value v stands for coefficient index v + 1. -/
 def IsUnimodal {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) : Prop :=
   (∀ i j : Fin (n + 1), i < j → j ≤ π (Fin.last n) → π.symm i < π.symm j) ∧
   (∀ i j : Fin (n + 1), π (Fin.last n) ≤ i → i < j → π.symm j < π.symm i)

 /-- π arises via (1): the nonconstant coefficients listed in the order π are weakly increasing. -/
 def Arises {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) : Prop :=
   ∃ r : Fin (n + 1) → ℝ, (∀ i, 0 < r i) ∧
     Monotone (fun t : Fin (n + 1) => coeffs r ((π t : ℕ) + 1))

 /-- Answer to Question 4.6: exactly the unimodal permutations arise. -/
 def claim : Prop := ∀ (n : ℕ) (π : Equiv.Perm (Fin (n + 1))), Arises π ↔ IsUnimodal π

end
end D5.S3.Combinatorics.RealRootedPermutations
