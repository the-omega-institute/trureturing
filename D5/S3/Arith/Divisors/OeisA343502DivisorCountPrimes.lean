/- GID: D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/OeisA343502DivisorCountPrimes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dequatre's A343502 conjecture holds: all members except 2 and 3 are composite. -/

/- Judgement form for this open-problem settlement.
   proof_shape: InA343502: definition; claim: definition; result: bind-only; consumer=none.
   proof_shape: tau_owner_correspondence: bind-only; consumer=result.
   escape_witness: none.
   admission_basis: open-problem-resolution (#18685; Proved).
   Direct frozen dependencies (result and tau_owner_correspondence):
     D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau
     (statement_id sha256:c60d6dd1dcf157704ddfe7463d3d2589218b93b1448382f0ba01ceffcbe2c1e5).
   Direct frozen dependencies (result only):
     D5.S3.Arith.DivisorCountRadicalCoincidence.primeFactors_card_le_cardFactors_card_divisors
     (baseline private statement_id
      sha256:51872255a710ceeb7da14301b2db1371c29d66a8f4030f488d688c6001d106e4).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19974.
   The public predicates inline the preregistered divisor-count convention; the frozen tau owner
   is used only through the consumed correspondence lemma in result, so no duplicate tau is added.
   The public result is the settling declaration and supplies no escape witness.
-/

import D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample
import D5.S3.Arith.DivisorCountRadicalCoincidence
import Mathlib.NumberTheory.Fermat
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.OeisA343502DivisorCountPrimes

/- Numbers k such that tau(tau(k)) and tau(k+1) are both prime, where tau is the number of
   divisors function. The divisor-count expression is written literally to avoid duplicating the
   frozen owner `D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau`. -/
def InA343502 (k : ℕ) : Prop :=
  1 ≤ k ∧ (k.divisors.card.divisors.card).Prime ∧ ((k + 1).divisors.card).Prime

/- OEIS A343502: "Conjecture: all members except 2 and 3 are composite." -/
def claim : Prop :=
  ∀ k : ℕ, InA343502 k → k ≠ 2 → k ≠ 3 → 1 < k ∧ ¬ k.Prime

/- Fidelity checks: the first terms 2, 3, 4, 6, 8, 10, 15, 16, and that 1, 5, 7, 9 are absent. -/
example : InA343502 2 ∧ InA343502 3 ∧ InA343502 4 ∧ InA343502 6 ∧ InA343502 8 ∧ InA343502 10 ∧
    InA343502 15 ∧ InA343502 16 := by
  unfold InA343502
  decide

example : ¬ InA343502 1 ∧ ¬ InA343502 5 ∧ ¬ InA343502 7 ∧ ¬ InA343502 9 := by
  unfold InA343502
  decide

private theorem tau_owner_correspondence (n : ℕ) :
    n.divisors.card = D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau n := by
  rfl

theorem result : claim := by
  intro k hk hk2 hk3
  have hk_owner : 1 ≤ k ∧
      (D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau
        (D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau k)).Prime ∧
      (D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau (k + 1)).Prime := by
    simpa only [InA343502, tau_owner_correspondence] using hk
  have hk1 : k ≠ 1 := by
    intro heq
    subst k
    norm_num [InA343502] at hk
  refine ⟨Nat.lt_of_le_of_ne hk.1 (Ne.symm hk1), ?_⟩
  intro hprime
  have hodd : k % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hprime).mpr hk2
  have hn0 : k + 1 ≠ 0 := Ne.symm (Nat.zero_ne_add_one k)
  have htwo : 2 ∣ k + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hm2 : 2 ∈ (k + 1).primeFactors :=
    Nat.prime_two.mem_primeFactors htwo hn0
  have hsingle : (k + 1).primeFactors = {2} := by
    have hbound :=
      D5.S3.Arith.DivisorCountRadicalCoincidence.primeFactors_card_le_cardFactors_card_divisors hn0
    have hprimeCount : ((k + 1).divisors.card).Prime := hk.2.2
    rw [ArithmeticFunction.cardFactors_apply_prime hprimeCount] at hbound
    exact Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hm2, fun p hp => Finset.card_le_one.mp hbound p hp 2 hm2⟩
  have hpow : k + 1 = 2 ^ (k + 1).factorization 2 := by
    calc
      k + 1 = ∏ p ∈ (k + 1).primeFactors, p ^ (k + 1).factorization p :=
        Nat.prod_primeFactors_pow_factorization hn0
      _ = 2 ^ (k + 1).factorization 2 := by rw [hsingle, Finset.prod_singleton]
  have hcount :
      D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau (k + 1) =
        (k + 1).factorization 2 + 1 := by
    rw [D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample.tau,
      Nat.card_divisors hn0, hsingle]
    simp
  have hexp1 : (k + 1).factorization 2 ≠ 1 := by
    intro heq
    rw [heq] at hpow
    norm_num at hpow
    omega
  have hkpow : k = 2 ^ (k + 1).factorization 2 - 1 := Nat.eq_sub_of_add_eq hpow
  have hexpprime : ((k + 1).factorization 2).Prime :=
    (Nat.prime_of_pow_sub_one_prime hexp1 (hkpow ▸ hprime)).2
  have hemod : (k + 1).factorization 2 % 2 = 0 := by
    have hcountprime := hk_owner.2.2
    rw [hcount] at hcountprime
    rcases hcountprime.eq_two_or_odd with h | h <;> omega
  have hexp2 : (k + 1).factorization 2 = 2 :=
    hexpprime.eq_two_or_odd.resolve_right (by omega)
  rw [hexp2] at hpow
  norm_num at hpow
  omega

end D5.S3.Arith.Divisors.OeisA343502DivisorCountPrimes
