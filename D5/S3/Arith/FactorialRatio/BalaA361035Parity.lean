/- GID: D5/S3/Arith/FactorialRatio/BalaA361035Parity
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA361035Parity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A361035 factorial quotient is odd exactly at shifted powers of two. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18607; Proved)
Direct frozen dependencies: the declarations listed below belong to
D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.
The scoped report records declaration statement_id values:
  mul_div_reduce = sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9;
  factorial_prod_dvd_of_floor = sha256:50335c191d9334cd159b0c8f8c463c3090bb5624f2a0108461ea86f752952f0e.
No module pin is used as a declaration ID.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21857
The sequence and claim use the source expressions with natural division.
The upstream route for of_digits_sum_one described in BalaA361034Parity makes
this result bind-only after helper expansion; no escape witness is claimed.
Its admission basis is the external open-problem resolution above.
Declarations (same-delivery helpers expanded for proof classification):
  a: proof_shape: bind-only; escape_witness: none; consumers: claim, result.
    Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none; consumers: result.
    Direct frozen dependencies: none.
  result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
-/

import D5.S3.Arith.FactorialRatio.BalaA361034Parity

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.BalaA361035Parity

/-- `a(n) = 9979200*(4*n)!/(n!*(n+3)!^3)`. -/
def a (n : ℕ) : ℕ := 9979200 * (4 * n).factorial / (n.factorial * (n + 3).factorial ^ 3)

/-- The conjecture of A361035: `a(n)` is odd iff `n = 2^k - 3` for some `k >= 2`. -/
def claim : Prop := ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k - 3


theorem result : claim := by
  intro n
  have h := D5.S3.Arith.FactorialRatio.BalaA361034Parity.quotient_odd 9979200 3 n (by decide) (by decide)
    (by norm_num [Nat.factorial]) (by decide +kernel)
  change Odd (9979200 * (4*n).factorial / (n.factorial * (n+3).factorial^3)) ↔ _
  rw [h]
  constructor
  · rintro ⟨k, hk⟩
    have hkm : 2 ≤ k := by
      by_contra hlt
      have hh : k < 2 := by exact Nat.lt_of_not_le hlt
      interval_cases k <;> norm_num at hk
    exact ⟨k, hkm, by omega⟩
  · rintro ⟨k, hkm, hk⟩
    have hp : 3 ≤ (2:ℕ)^k := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hkm
      norm_num at hh
      omega
    exact ⟨k, by omega⟩

end D5.S3.Arith.FactorialRatio.BalaA361035Parity
