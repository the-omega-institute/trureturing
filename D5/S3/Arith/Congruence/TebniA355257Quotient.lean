/- GID: D5/S3/Arith/Congruence/TebniA355257Quotient
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/TebniA355257Quotient
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Tebni's prime quotient congruence for even row indices. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25143
admission_basis: open-problem-resolution (#18640; Proved).
result: proof_shape: bind-only; escape_witness: none.
Direct frozen dependencies: LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime,
through the coefficient and residue arguments of the same delivery.
utility_reason: Universal symbolic divisibility and congruence, with no bounded
enumeration or separately delivered certified instance.

Per-declaration judgement (the module basis above applies to each row):
name | proof_shape | Direct frozen dependencies | escape_witness | consumers
claim | bind-only | none | none | TebniA355257Quotient.result
result | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | source conjecture
-/

import D5.S3.Arith.Congruence.TebniA355257Divisibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.TebniA355257Quotient
open D5.S3.Arith.Congruence.TebniA355257Divisibility

/-- A355257 ("Conjecture: For p prime and n even, (A(n, p) / (p - 1)) == 1 (mod p)."): the quotient is an
integer congruent to 1 modulo p. -/
def claim : Prop :=
  ∀ n p : ℕ, p.Prime → Even n → ∃ q : ℤ, (q : ℚ) = A n p / ((p : ℚ) - 1) ∧ q ≡ 1 [ZMOD p]


theorem result : claim := by
  intro n p hp hn
  obtain ⟨q, hq⟩ := even_pred_divides n p hp hn
  refine ⟨q, ?_, ?_⟩
  · rw [A_eq_Z, hq, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one]
    have hpq : (p : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    exact (mul_div_cancel_left₀ (q : ℚ) hpq).symm
  · have hm := prime_residue n p hp
    rw [← ZMod.intCast_eq_intCast_iff] at hm ⊢
    rw [hq] at hm
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one,
      Int.cast_neg, ZMod.natCast_self, zero_sub, neg_one_mul] at hm
    have hh : (q : ZMod p) = 1 := neg_injective hm
    simpa only [Int.cast_one] using hh


end D5.S3.Arith.Congruence.TebniA355257Quotient
