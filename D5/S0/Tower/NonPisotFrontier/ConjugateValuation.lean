/- GID: D5/S0/Tower/NonPisotFrontier/ConjugateValuation
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/ConjugateValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reading exact codes at the conjugate turns periodic digits into finitely many values. -/

import D5.S0.Tower.NonPisot.Beta13Infinite
import D5.S0.Tower.NonPisotFrontier.BaseIdentification

/- Library-search audit trail (2026-08-18):
   * Searched on the object this time.  `D5/S0/Tower/NonPisot/Beta13Infinite.lean`
     already carries the exact quadratic codes, the multiplication reduced by the
     defining relation, the greedy remainder stream and the greedy digits; none
     of that is rebuilt here.  Issue 2427 records that an earlier plan assumed it
     was missing.
   * What that module does not carry is a reading of a code at the conjugate,
     which is the one thing added below.  The conjugate's own quadratic relation
     comes from the frontier side and reaches this module through the
     identification of the two names for the base.
   * Pinned Mathlib supplies `Nat.strong_induction_on`; nothing else is used. -/

namespace D5.S0.Tower.NonPisotFrontier.ConjugateValuation

open D5.S0.Tower.NonPisot.Beta13
open D5.S0.Tower.NonPisot.Beta13Infinite
open D5.S0.Tower.NonPisotFrontier.BetaThirteen

local notation "β'" => betaThirteenConjugate

/-- An exact code read at the conjugate instead of at the base. -/
noncomputable def conjugateValue (code : Beta13Code) : Real :=
  (code.1 : Real) + (code.2 : Real) * β'

/-- The reduction that defines code multiplication is the base's relation, and the
conjugate satisfies the same one, so the reading intertwines with it. -/
theorem conjugateValue_mul (code : Beta13Code) :
    conjugateValue (beta13CodeMul code) = β' * conjugateValue code := by
  have hq := betaThirteenConjugate_quadratic
  simp only [conjugateValue, beta13CodeMul]
  push_cast
  have hrhs : β' * ((code.1 : Real) + (code.2 : Real) * β')
      = (code.1 : Real) * β' + (code.2 : Real) * β' ^ 2 := by ring
  rw [hrhs, hq]
  ring

/-- Digit subtraction is untouched by which root the code is read at. -/
theorem conjugateValue_subDigit (code : Beta13Code) (digit : Int) :
    conjugateValue (beta13CodeSubDigit code digit) = conjugateValue code - digit := by
  simp only [conjugateValue, beta13CodeSubDigit]
  push_cast
  ring

/-- The conjugate orbit of the greedy expansion of one. -/
noncomputable def conjugateRemainder (n : Nat) : Real :=
  conjugateValue (beta13RemainderCode n)

/-- It is driven by the very same digits as the orbit at the base. -/
theorem conjugateRemainder_succ (n : Nat) :
    conjugateRemainder (n + 1) = β' * conjugateRemainder n - beta13GreedyDigit n := by
  simp only [conjugateRemainder, beta13RemainderCode, beta13GreedyDigit]
  rw [conjugateValue_subDigit, conjugateValue_mul]

/-- Periodicity of the codes transports to the conjugate reading. -/
theorem conjugateRemainder_periodic {p N : Nat}
    (hper : ∀ n, N ≤ n → beta13RemainderCode (n + p) = beta13RemainderCode n) :
    ∀ n, N ≤ n → conjugateRemainder (n + p) = conjugateRemainder n := by
  intro n hn
  simp only [conjugateRemainder, hper n hn]

/-- So an eventually periodic code stream lets the conjugate orbit take only the
values it already takes before the period closes. -/
theorem conjugateRemainder_eq_early {p N : Nat} (hp : 0 < p)
    (hper : ∀ n, N ≤ n → beta13RemainderCode (n + p) = beta13RemainderCode n) :
    ∀ n, ∃ k, k < N + p ∧ conjugateRemainder n = conjugateRemainder k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      by_cases hlt : n < N + p
      · exact ⟨n, hlt, rfl⟩
      · have hge : N + p ≤ n := Nat.le_of_not_lt hlt
        have hNle : N ≤ n - p := by omega
        have hback : n - p + p = n := by omega
        have hstep : conjugateRemainder n = conjugateRemainder (n - p) := by
          have h := conjugateRemainder_periodic hper (n - p) hNle
          rwa [hback] at h
        obtain ⟨k, hk, hval⟩ := ih (n - p) (by omega)
        exact ⟨k, hk, by rw [hstep, hval]⟩

/-- Every greedy digit lies in the alphabet, which the digit function's own case
split already decides.  The escape estimate needs exactly this range. -/
theorem greedyDigit_mem_alphabet (n : Nat) :
    0 ≤ beta13GreedyDigit n ∧ beta13GreedyDigit n ≤ 2 := by
  simp only [beta13GreedyDigit, beta13CodeDigit]
  split_ifs <;> norm_num

/-- The fourth remainder code, so the hand-written witness and the recursive stream
are the same object rather than two computations that happen to agree. -/
theorem remainderCode_four : beta13RemainderCode 4 = (5, -2) := by decide

/-- Hence the conjugate orbit at step four is the witness value. -/
theorem conjugateRemainder_four : conjugateRemainder 4 = 5 + (-2 : Real) * β' := by
  simp only [conjugateRemainder, remainderCode_four, conjugateValue]
  norm_num

/-- The conjugate reading exists, is driven by the same digits, and collapses to a
finite set of values as soon as the digits repeat. -/
theorem conjugate_reading_of_the_expansion :
    (∀ n : Nat,
        conjugateRemainder (n + 1) = β' * conjugateRemainder n - beta13GreedyDigit n) ∧
      ∀ p N : Nat, 0 < p →
        (∀ n, N ≤ n → beta13RemainderCode (n + p) = beta13RemainderCode n) →
          ∀ n, ∃ k, k < N + p ∧ conjugateRemainder n = conjugateRemainder k :=
  ⟨conjugateRemainder_succ, fun _ _ hp hper => conjugateRemainder_eq_early hp hper⟩

end D5.S0.Tower.NonPisotFrontier.ConjugateValuation
