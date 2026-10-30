/- GID: D5/S3/Arith/ExponentExchange/CoprimeNormalForm
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/CoprimeNormalForm
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: consumed-by-robin-5040
   digest: Prime-exponent exchange preserves coprimality with an external modulus. -/

import D5.S3.Arith.ExponentExchange.IntegerSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ExponentExchange.CoprimeNormalForm

open D5.S3.Arith.ExponentExchange.IntegerSwap

noncomputable section

/- The order condition is imposed only on prime axes that survive the external
   modulus.  Requiring it for every prime is false when the modulus itself
   contains one of the axes. -/
def AllowedOrdered (M m : ℕ) : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → p.Coprime M → q.Coprime M →
    m.factorization q ≤ m.factorization p

/-- Every positive integer coprime to `M` has a smaller-or-equal representative
with the same external coprimality and non-increasing exponents on all prime
axes coprime to `M`; the normalized divisor sum does not decrease. -/
theorem exists_coprime_allowed_ordered_form {M n : ℕ} (hn : 1 ≤ n)
    (hcn : n.Coprime M) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ m.Coprime M ∧ AllowedOrdered M m ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
        (ArithmeticFunction.sigma 1 m : ℝ) / m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hanti : AllowedOrdered M n
    · exact ⟨n, hn, le_rfl, hcn, hanti, le_rfl⟩
    · simp only [AllowedOrdered, not_forall, not_le] at hanti
      obtain ⟨p, q, hp, hq, hpq, hpM, hqM, hlt⟩ := hanti
      obtain ⟨ht, htc, hdecomp, ⟨hpos, hsmall⟩, hZ⟩ :=
        prime_exponent_swap hn hp hq hpq hlt
      let a := n.factorization p
      let b := n.factorization q
      let t := n / (p ^ a * q ^ b)
      have hfactor : t * p ^ a * q ^ b = n := by
        simpa only [a, b, t, Nat.mul_assoc] using hdecomp.symm
      have ht_dvd : t ∣ t * p ^ a * q ^ b := by
        simpa only [Nat.mul_assoc] using (dvd_mul_right t (p ^ a * q ^ b))
      have htM : t.Coprime M := hcn.coprime_dvd_left (hfactor ▸ ht_dvd)
      have hrestM : (p ^ b * q ^ a).Coprime M :=
        (hpM.pow_left b).mul_left (hqM.pow_left a)
      have hn'M : (t * p ^ b * q ^ a).Coprime M := by
        simpa [Nat.mul_assoc] using htM.mul_left hrestM
      obtain ⟨m, hm1, hmle, hmM, hmanti, hmZ⟩ := ih _ hsmall hpos hn'M
      refine ⟨m, hm1, hmle.trans hsmall.le, hmM, hmanti, ?_⟩
      exact hZ.le.trans hmZ

#print axioms exists_coprime_allowed_ordered_form

end

end D5.S3.Arith.ExponentExchange.CoprimeNormalForm
