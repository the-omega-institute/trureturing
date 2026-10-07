/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim; result=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result; claim=D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim
   digest: The full multiset rook-Eulerian polynomial fails real-rootedness on a positive Ferrers board. -/


import D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
import D5.S3.Combinatorics.Permutation.MultisetRookEulerianNonrealCertificate
import D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block64

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianNonrealCertificate
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation

/-- The 120-row Ferrers board (2^3,3^4,4^10,5^2,6^101). -/
def board (i : Fin 120) : ℕ :=
  if i.val < 3 then 2 else
  if i.val < 7 then 3 else
  if i.val < 17 then 4 else
  if i.val < 19 then 5 else 6

/-- Nonnegative content is enforced by the natural-valued codomain. -/
def content : Fin 6 → ℕ := ![6, 1, 4, 8, 1, 100]

theorem board_monotone : Monotone board := by
  intro i j hij
  have hval : i.val ≤ j.val := hij
  unfold board
  split_ifs <;> omega

theorem board_positive : ∀ i, 0 < board i := by
  intro i
  unfold board
  split_ifs <;> norm_num

theorem content_sum : (∑ c, content c) = 120 := by
  decide

/-- Equation (10), using the original W, strict adjacent asc, and R. -/
theorem R_eq_explicit : R board content = X ^ 2 * Q := by
  have hboard : List.ofFn board = [2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hletters : sourceLetters content = [1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  rw [W_sum_eq_dp board content content_sum, hboard, hletters,
    D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block64.dag_1768]
  norm_num [Q, ← C_mul_X_pow_eq_monomial, C_ofNat] <;> ring

/-- The distinct real-rootedness FIRST clause of Conjecture 28.
    α : Fin k → ℕ supplies precisely nonnegative integer multiplicities;
    λ_i > μ_i in Section 3.3 becomes positivity of every row when μ = 0. -/
noncomputable def claim : Prop :=
  ∀ (n k : ℕ) (lam : Fin n → ℕ) (α : Fin k → ℕ),
    0 < n → Monotone lam → (∀ i, 0 < lam i) → (∑ c, α c) = n →
      (R lam α).Splits

/-- The full source polynomial on a positive, monotone Ferrers board fails
    real-rootedness; this does not project the old interlacing conjunction. -/
theorem result : ¬ claim := by
  intro h
  have hs := h 120 6 board content (by decide)
    board_monotone board_positive content_sum
  rw [R_eq_explicit] at hs
  exact full_explicit_not_splits hs

#print axioms R_eq_explicit
#print axioms result

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianRealRootednessRefutation
