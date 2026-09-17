/- GID: D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Squarefree]
   utility: none
   digest: Rotondo's three-prime Lucas-Carmichael sufficient condition. -/

import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.RotondoLucasCarmichaelCriterion

set_option linter.unusedVariables false

/-- A Lucas-Carmichael number is a squarefree composite `k > 1` such that
`s + 1` divides `k + 1` for every prime divisor `s` of `k`. -/
def IsLucasCarmichael (k : ℕ) : Prop :=
  Squarefree k ∧ ¬Nat.Prime k ∧ 1 < k ∧
    ∀ s : ℕ, Nat.Prime s → s ∣ k → s + 1 ∣ k + 1

/-- Rotondo's sufficient condition for a product of three distinct odd primes
to be a Lucas-Carmichael number. -/
theorem result (a b c d p q r k : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp0 : 0 < p) (hq0 : 0 < q) (hr0 : 0 < r) (hk0 : 0 < k)
    (hk : k = p * q * r)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpad : p + 1 = a * d) (hqbd : q + 1 = b * d) (hrcd : r + 1 = c * d)
    (hgcd : d = Nat.gcd (p + 1) (Nat.gcd (q + 1) (r + 1)))
    (habcd : a * b * c * d ∣ k + 1) : IsLucasCarmichael k := by
  subst k
  have hp_q : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hp_r : p.Coprime r := (Nat.coprime_primes hp hr).2 hpr
  have hq_r : q.Coprime r := (Nat.coprime_primes hq hr).2 hqr
  have hpq_r : (p * q).Coprime r := (Nat.coprime_mul_iff_left).2 ⟨hp_r, hq_r⟩
  refine ⟨(Nat.squarefree_mul hpq_r).2
      ⟨(Nat.squarefree_mul hp_q).2 ⟨hp.squarefree, hq.squarefree⟩, hr.squarefree⟩,
    ?_, one_lt_mul'' (one_lt_mul'' hp.one_lt hq.one_lt) hr.one_lt, ?_⟩
  · exact Nat.not_prime_mul (mul_ne_one.mpr (Or.inl hp.ne_one)) hr.ne_one
  · intro s hs hs_dvd
    rcases (hs.dvd_mul).1 hs_dvd with hs_pq | hsr
    · rcases (hs.dvd_mul).1 hs_pq with hsp | hsq
      · have hsp_eq : s = p := (Nat.prime_dvd_prime_iff_eq hs hp).1 hsp
        rw [hsp_eq, hpad]
        exact (show a * d ∣ a * b * c * d by
          refine ⟨b * c, ?_⟩
          ac_rfl).trans habcd
      · have hsq_eq : s = q := (Nat.prime_dvd_prime_iff_eq hs hq).1 hsq
        rw [hsq_eq, hqbd]
        exact (show b * d ∣ a * b * c * d by
          refine ⟨a * c, ?_⟩
          ac_rfl).trans habcd
    · have hsr_eq : s = r := (Nat.prime_dvd_prime_iff_eq hs hr).1 hsr
      rw [hsr_eq, hrcd]
      exact (show c * d ∣ a * b * c * d by
        refine ⟨a * b, ?_⟩
        ac_rfl).trans habcd

end D5.S3.Arith.Congruence.RotondoLucasCarmichaelCriterion
