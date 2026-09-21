/- GID: D5/S3/Arith/FriedFibonacciShiftNonFibonacci
   generality: G
   mirror-B: D5/B/S3/Arith/FriedFibonacciShiftNonFibonacci
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: For every n at least one the number F(n+2) + 2nF(n+1) is not a Fibonacci number. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FriedFibonacciShiftNonFibonacci

/-
proof_shape: result: content
escape_witness: three intermediate facts on the active path, none of them an
  instantiation, projection or normalisation of a pinned upstream statement:
  (i) `2 * k < Nat.fib k` for every `k` at least eight, obtained by induction;
  (ii) the truncated-subtraction identity
       `(F j - 1) * F n = (2n + 1 - F (j+1)) * F (n+1)`
       extracted from the addition formula;
  (iii) `F (n+1) <= F j - 1`, obtained from that identity by coprimality of
       consecutive Fibonacci numbers together with positivity.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- Fried's conjecture at the end of Section 6 of *Proofs of Several Conjectures
From the OEIS*, stated there as the equivalent form of the disjointness of
`{n F(n/2 + 3) - (n-1) F(n/2 + 2) : n >= 1 even}` and
`{F((n+1)/2 + 2) : n >= 1 odd}`: for every `n` in `N` the number
`F(n + 2) + 2 n F(n + 1)` is not a Fibonacci number.  The indexing convention of
the source, `F 1 = F 2 = 1`, is the indexing of `Nat.fib`, and its `N` starts at
one. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, Nat.fib m ≠ Nat.fib (n + 2) + 2 * n * Nat.fib (n + 1)

/-- The conjecture holds.  Write `X n = F (n+2) + 2 n F (n+1) = F n + (2n+1) F (n+1)`.
For `n` at most seven the value of `X n` is below `F 14 = 377`, which bounds the index
of any Fibonacci number equal to it and leaves finitely many pairs to check.  For `n`
at least eight, a Fibonacci number `F m` equal to `X n` has `m` at least `n + 2`,
because `X n` exceeds `F (n+1)`; writing `m = j + n + 1` the addition formula turns
the equation into `(F j - 1) F n = (2n + 1 - F (j+1)) F (n+1)`.  If `F j = 1` then
`j` is at most two and the right factor is at least three times the left one, which is
impossible.  Otherwise `F j - 1` is positive, and since `F n` and `F (n+1)` are
coprime, `F (n+1)` divides `F j - 1`, hence `F (n+1) <= F j - 1`.  The left side is
then at least `F (n+1) F n` while the right side is at most `2 n F (n+1)`, so
`F n <= 2 n`, contradicting `2 n < F n` for `n` at least eight. -/
theorem result : claim := by
  intro n hn m hm
  rw [Nat.fib_add_two] at hm
  have hm' : Nat.fib m = Nat.fib n + (2 * n + 1) * Nat.fib (n + 1) := by
    rw [hm]; ring
  have hfn1 : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  rcases Nat.lt_or_ge n 8 with hsmall | hbig
  · have hval : Nat.fib n + (2 * n + 1) * Nat.fib (n + 1) < 377 := by
      interval_cases n <;> decide
    have hmb : m < 14 := by
      by_contra hc
      have h1 : Nat.fib 14 ≤ Nat.fib m := Nat.fib_mono (by omega)
      have h2 : Nat.fib 14 = 377 := by decide
      omega
    interval_cases n <;> interval_cases m <;> revert hm' <;> decide
  · have hfn : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
    have key : ∀ k : ℕ, 8 ≤ k → 2 * k < Nat.fib k := by
      intro k
      induction k with
      | zero => intro h; omega
      | succ p ih =>
        intro hp
        rcases Nat.lt_or_ge p 8 with h | h
        · have hp7 : p = 7 := by omega
          subst hp7
          decide
        · have hf : Nat.fib (p + 1) = Nat.fib (p - 1) + Nat.fib p := Nat.fib_add_one (by omega)
          have h1 : Nat.fib 7 ≤ Nat.fib (p - 1) := Nat.fib_mono (by omega)
          have h7 : Nat.fib 7 = 13 := by decide
          have h2 := ih h
          omega
    have key8 : 2 * n < Nat.fib n := key n hbig
    rcases Nat.lt_or_ge m (n + 2) with hm2 | hm2
    · have h1 : Nat.fib m ≤ Nat.fib (n + 1) := Nat.fib_mono (by omega)
      have h3 : 3 * Nat.fib (n + 1) ≤ (2 * n + 1) * Nat.fib (n + 1) :=
        Nat.mul_le_mul (by omega) (le_refl _)
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + n + 1 := ⟨m - n - 1, by omega⟩
      have hj : 1 ≤ j := by omega
      rw [Nat.fib_add j n] at hm'
      have hfj : 0 < Nat.fib j := Nat.fib_pos.mpr (by omega)
      have hfj1 : 0 < Nat.fib (j + 1) := Nat.fib_pos.mpr (by omega)
      have hsub : Nat.fib n ≤ Nat.fib j * Nat.fib n := Nat.le_mul_of_pos_left _ hfj
      have hCD : Nat.fib (j + 1) * Nat.fib (n + 1) ≤ (2 * n + 1) * Nat.fib (n + 1) := by omega
      have hle1 : Nat.fib (j + 1) ≤ 2 * n + 1 := Nat.le_of_mul_le_mul_right hCD hfn1
      rcases eq_or_ne (Nat.fib j) 1 with hu | hu
      · have hv2 : Nat.fib (j + 1) ≤ 2 := by
          have hj2 : j ≤ 2 := by
            by_contra hc
            have h3 : Nat.fib 3 ≤ Nat.fib j := Nat.fib_mono (by omega)
            have h3' : Nat.fib 3 = 2 := by decide
            omega
          have h3 : Nat.fib (j + 1) ≤ Nat.fib 3 := Nat.fib_mono (by omega)
          have h3' : Nat.fib 3 = 2 := by decide
          omega
        rw [hu, one_mul] at hm'
        have hA : Nat.fib (j + 1) * Nat.fib (n + 1) ≤ 2 * Nat.fib (n + 1) :=
          Nat.mul_le_mul hv2 (le_refl _)
        have hB : 3 * Nat.fib (n + 1) ≤ (2 * n + 1) * Nat.fib (n + 1) :=
          Nat.mul_le_mul (by omega) (le_refl _)
        omega
      · have hu2 : 2 ≤ Nat.fib j := by omega
        have keyeq : (Nat.fib j - 1) * Nat.fib n
            = (2 * n + 1 - Nat.fib (j + 1)) * Nat.fib (n + 1) := by
          rw [Nat.sub_mul, Nat.sub_mul, one_mul]
          omega
        have hdvd : Nat.fib (n + 1) ∣ (Nat.fib j - 1) * Nat.fib n := by
          refine ⟨2 * n + 1 - Nat.fib (j + 1), ?_⟩
          rw [keyeq]
          exact Nat.mul_comm _ _
        have hdvd2 : Nat.fib (n + 1) ∣ Nat.fib j - 1 :=
          (Nat.fib_coprime_fib_succ n).symm.dvd_of_dvd_mul_right hdvd
        have hposj : 0 < Nat.fib j - 1 := by omega
        have hge : Nat.fib (n + 1) ≤ Nat.fib j - 1 := Nat.le_of_dvd hposj hdvd2
        have hL : Nat.fib (n + 1) * Nat.fib n ≤ (Nat.fib j - 1) * Nat.fib n :=
          Nat.mul_le_mul hge (le_refl _)
        have hR : (2 * n + 1 - Nat.fib (j + 1)) * Nat.fib (n + 1)
            ≤ 2 * n * Nat.fib (n + 1) := Nat.mul_le_mul (by omega) (le_refl _)
        have hchain : Nat.fib (n + 1) * Nat.fib n ≤ Nat.fib (n + 1) * (2 * n) := by
          rw [Nat.mul_comm (Nat.fib (n + 1)) (2 * n)]
          omega
        have hfinal : Nat.fib n ≤ 2 * n := Nat.le_of_mul_le_mul_left hchain hfn1
        omega

end D5.S3.Arith.FriedFibonacciShiftNonFibonacci
