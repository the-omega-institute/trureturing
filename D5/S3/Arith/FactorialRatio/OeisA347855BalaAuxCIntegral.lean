/- GID: D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A347855C fractional-factorial integrality. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18693; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19874
The fractional factorial and sequence definitions retain the source expressions.
No finite computational declaration refutes the claim; utility is none.
Declarations (all dependencies outside this delivery are pinned Mathlib):
  c: proof_shape: bind-only; escape_witness: none;
    consumers: claim, result. Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  denominator_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  result: proof_shape: bind-only; escape_witness: none;
    consumers: settling result. Direct frozen dependencies: none.
-/

import D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaAuxCIntegral

/-- A347855, `c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) )`. -/
def c (n : ℕ) : ℚ :=
  (Nat.factorial (12 * n + 8) : ℚ) /
    ((Nat.factorial (6 * n + 4) : ℚ) * (Nat.factorial (3 * n + 1) : ℚ) *
      ∏ k ∈ Finset.range (3 * n + 3), ((3 * n + 3 * k + 2 : ℕ) : ℚ))

/-- A347855 ("a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = … appears to be integral."). -/
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = c n

end D5.S3.Arith.FactorialRatio.OeisA347855BalaAuxCIntegral

set_option maxHeartbeats 800000

namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaAuxCIntegral
open D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

private lemma denominator_dvd (n : ℕ) :
    (6*n+4).factorial * (3*n+1).factorial *
      (∏ k ∈ Finset.range (3*n+3), (3*n+3*k+2)) ∣ (12*n+8).factorial := by
    have hd := third_dvd (3*n+2) (by omega)
    have he : (∏ k ∈ Finset.range (3*n+3), (3*n+3*k+2)) =
        (3*n+2) * progression (3*n+2) := by
      rw [show 3*n+3 = (3*n+2)+1 by omega, Finset.prod_range_succ']
      simp only [Nat.mul_zero, add_zero]
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      ring
    rw [show 2*(3*n+2) = 6*n+4 by omega, show 4*(3*n+2) = 12*n+8 by omega] at hd
    have hfac : (3*n+2).factorial = (3*n+2)*(3*n+1).factorial :=
      Nat.factorial_succ (3*n+1)
    convert hd using 1
    rw [he, hfac]
    ring

theorem result : claim := by
  intro n
  obtain ⟨k, hk⟩ := denominator_dvd n
  refine ⟨(k : ℤ), ?_⟩
  simp only [c]
  rw [hk]
  push_cast
  have hprod : (∏ k ∈ Finset.range (3*n+3), ((3*n+3*k+2 : ℕ) : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    positivity
  field_simp

end D5.S3.Arith.FactorialRatio.OeisA347855BalaAuxCIntegral
