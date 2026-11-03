/- GID: D5/S3/Arith/Primes/BourasA372763OnceRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/BourasA372763OnceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Primes/BourasA372763OnceRefutation.claim; result=D5/S3/Arith/Primes/BourasA372763OnceRefutation.result; claim=D5/S3/Arith/Primes/BourasA372763OnceRefutation.claim
   digest: Refutes unique prime occurrence using the two indices for 11 in A372763. -/
/-
proof_shape: nested, K, a, claim: not-applicable-definition; result: bind-only.
Consumers: nested is used by K; K by a; a by claim and result; claim by result.
escape_witness: none.
admission_basis: open-problem-resolution (#18628; Refuted).
Direct frozen dependencies: none (every declaration); only pinned Mathlib is imported.
The continued fraction and its index range are those of OEIS A372763, NAME and COMMENTS.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false

namespace D5.S3.Arith.Primes.BourasA372763OnceRefutation

/-- The inner expression, evaluated from the terminal rational value x. -/
def nested (n : ℕ) (x : ℚ) : ℚ :=
  (List.range' 2 (n - 2)).foldr (fun (k : ℕ) (t : ℚ) => (k : ℚ) - ((k : ℚ) + 1) / t) x

/-- The continued fraction with terminal value x. -/
def K (n : ℕ) (x : ℚ) : ℚ := 1 / nested n x

/-- OEIS A372763, NAME (unpaginated):
"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5)))))." -/
def a (n : ℕ) : ℕ := (K n ((n : ℚ) + 5)).den

/-- OEIS A372763, COMMENTS (unpaginated):
"Conjecture 2: Except for 2 and 3, all primes appear in the sequence once." -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∃! n : ℕ, 3 ≤ n ∧ a n = p

/-- The prime 11 occurs at both indices 10 and 21, contradicting uniqueness. -/
theorem result : ¬ claim := by
  intro h
  have hten : a 10 = 11 := by decide +kernel
  have htwentyone : a 21 = 11 := by decide +kernel
  have hunique := h 11 Nat.prime_eleven (by decide) (by decide)
  have heq : (10 : ℕ) = 21 :=
    hunique.unique ⟨by decide, hten⟩ ⟨by decide, htwentyone⟩
  exact (by decide : (10 : ℕ) ≠ 21) heq

end D5.S3.Arith.Primes.BourasA372763OnceRefutation
