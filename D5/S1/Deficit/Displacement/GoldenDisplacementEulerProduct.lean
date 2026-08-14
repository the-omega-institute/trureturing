/- GID: D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenDisplacementEulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves that the hidden product nS is multiplicative over coprime factors and computes it on prime powers, then assembles the displacement-surface Dirichlet series D(s,w) = sum over n of nS(n)^(-s) * n^(-w). Establishes absolute convergence for 0 <= s and 1 < s + w via the divisibility n | nS n, and derives the Euler product over primes whose local factor is the two-variable Hecke-Mahler series sum over e of P^(goldenSubstStart e) * Q^e at P = p^(-s), Q = p^(-w). Records the zeta cross-section at s = 0 and the failure of complete multiplicativity that keeps the local factor from being geometric. -/

import D5.S1.Deficit.Displacement.GoldenSubstitutionOrbit
import Mathlib

/- Provenance: the Euler product is the pinned mathlib
   `EulerProduct.eulerProduct_tprod` applied to the repository's hidden product
   `nS`; convergence uses `Real.summable_nat_rpow` and
   `Real.rpow_le_rpow_of_nonpos`. No local reproof of the Euler product. -/

open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionLength
open GoldenSubstitutionOrbit

namespace GoldenDisplacementEulerProduct

/-! ### The hidden product is multiplicative -/

theorem nS_one : nS 1 = 1 := by simp [nS]

/-- On a prime power the hidden product applies the substitution start to the exponent. -/
theorem nS_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    nS (p ^ k) = p ^ goldenSubstStart k := by
  rw [nS, Nat.Prime.factorization_pow hp, Finsupp.prod_single_index]
  exact pow_zero p

/-- The hidden product is multiplicative over coprime factors: their prime supports are
disjoint, so the substituted exponents never interact. -/
theorem nS_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    nS (m * n) = nS m * nS n := by
  classical
  have hdis : Disjoint m.factorization.support n.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact Nat.Coprime.disjoint_primeFactors h
  rw [nS, nS, nS, Nat.factorization_mul_of_coprime h]
  exact Finsupp.prod_add_index_of_disjoint hdis _

/-- Multiplicativity is not complete: the substitution start is not additive, so the local
factor of the Euler product below is not a geometric series. -/
theorem nS_not_completelyMultiplicative :
    ∃ p : ℕ, p.Prime ∧ nS (p * p) ≠ nS p * nS p := by
  have h1 : goldenSubstStart 1 = 2 := by decide
  have h2 : goldenSubstStart 2 = 3 := by decide
  refine ⟨2, Nat.prime_two, ?_⟩
  have h4 : nS (2 * 2) = 8 := by
    rw [show (2 : ℕ) * 2 = 2 ^ 2 by norm_num, nS_prime_pow Nat.prime_two 2, h2]
    norm_num
  have hp2 : nS 2 = 4 := by
    have h := nS_prime_pow Nat.prime_two 1
    rwa [pow_one, h1] at h
  rw [h4, hp2]
  norm_num

/-! ### The hidden product dominates its argument -/

theorem self_le_goldenSubstStart (k : ℕ) : k ≤ goldenSubstStart k := by
  have := goldenSubstStart_add_le 0 k
  rw [goldenSubstStart_zero] at this
  simpa using this

theorem dvd_nS {n : ℕ} (hn : n ≠ 0) : n ∣ nS n := by
  rw [← Nat.factorization_le_iff_dvd hn (nS_ne_zero n), nS_factorization]
  intro p
  simpa using self_le_goldenSubstStart (n.factorization p)

theorem le_nS {n : ℕ} (hn : n ≠ 0) : n ≤ nS n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (nS_ne_zero n)) (dvd_nS hn)

/-! ### The displacement surface -/

/-- The displacement-surface Dirichlet term `nS n ^ (-s) * n ^ (-w)`. -/
noncomputable def dTerm (s w : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (nS n : ℝ) ^ (-s) * (n : ℝ) ^ (-w)

theorem dTerm_zero (s w : ℝ) : dTerm s w 0 = 0 := if_pos rfl

theorem dTerm_one (s w : ℝ) : dTerm s w 1 = 1 := by
  simp [dTerm, nS_one]

theorem dTerm_nonneg (s w : ℝ) (n : ℕ) : 0 ≤ dTerm s w n := by
  unfold dTerm
  split
  · exact le_refl 0
  · positivity

/-- The displacement term inherits multiplicativity from the hidden product. -/
theorem dTerm_mul_of_coprime {s w : ℝ} {m n : ℕ} (h : Nat.Coprime m n) :
    dTerm s w (m * n) = dTerm s w m * dTerm s w n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := Nat.coprime_zero_left n |>.mp h
    subst hn
    simp [dTerm_zero, dTerm_one]
  rcases eq_or_ne n 0 with rfl | hn
  · have hm' : m = 1 := Nat.coprime_zero_right m |>.mp h
    subst hm'
    simp [dTerm_zero, dTerm_one]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  unfold dTerm
  rw [if_neg hmn, if_neg hm, if_neg hn, nS_mul_of_coprime h]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- Because `n` divides `nS n`, the displacement term is dominated by the `s + w` power. -/
theorem dTerm_le {s w : ℝ} (hs : 0 ≤ s) (n : ℕ) (hn : n ≠ 0) :
    dTerm s w n ≤ (n : ℝ) ^ (-(s + w)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase : ((nS n : ℝ)) ^ (-s) ≤ (n : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hnpos (by exact_mod_cast le_nS hn) (neg_nonpos.mpr hs)
  have hval : dTerm s w n = (nS n : ℝ) ^ (-s) * (n : ℝ) ^ (-w) := if_neg hn
  rw [hval, show -(s + w) = -s + -w by ring, Real.rpow_add hnpos]
  exact mul_le_mul_of_nonneg_right hbase (by positivity)

/-- The displacement series converges absolutely on the half-plane `0 ≤ s`, `1 < s + w`. -/
theorem dTerm_summable {s w : ℝ} (hs : 0 ≤ s) (hsw : 1 < s + w) :
    Summable (fun n : ℕ => ‖dTerm s w n‖) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(s + w))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hp
  rcases eq_or_ne n 0 with rfl | hn
  · rw [dTerm_zero]
    simp only [norm_zero]
    positivity
  · rw [Real.norm_of_nonneg (dTerm_nonneg s w n)]
    exact dTerm_le hs n hn

/-- On a prime power the displacement term is the Hecke-Mahler monomial. -/
theorem dTerm_prime_pow {s w : ℝ} {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dTerm s w (p ^ e) =
      ((p : ℝ) ^ (-s)) ^ (goldenSubstStart e) * ((p : ℝ) ^ (-w)) ^ e := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  unfold dTerm
  rw [if_neg hne, nS_prime_pow hp e]
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (goldenSubstStart e),
    ← Real.rpow_natCast ((p : ℝ) ^ (-w)) e,
    ← Real.rpow_natCast ((p : ℝ)) (goldenSubstStart e),
    ← Real.rpow_natCast ((p : ℝ)) e,
    ← Real.rpow_mul hppos.le, ← Real.rpow_mul hppos.le,
    ← Real.rpow_mul hppos.le, ← Real.rpow_mul hppos.le]
  ring_nf

/-- **Euler product of the displacement surface.** On the absolute-convergence half-plane the
displacement series factors over the primes, and each local factor is the two-variable
Hecke-Mahler series evaluated at `P = p ^ (-s)`, `Q = p ^ (-w)`. -/
theorem displacement_euler_product {s w : ℝ} (hs : 0 ≤ s) (hsw : 1 < s + w) :
    ∏' p : Nat.Primes,
        (∑' e : ℕ, ((p : ℝ) ^ (-s)) ^ (goldenSubstStart e) * ((p : ℝ) ^ (-w)) ^ e)
      = ∑' n : ℕ, dTerm s w n := by
  have hEuler := EulerProduct.eulerProduct_tprod (f := dTerm s w) (dTerm_one s w)
    (fun {m n} h => dTerm_mul_of_coprime h) (dTerm_summable hs hsw) (dTerm_zero s w)
  rw [← hEuler]
  exact tprod_congr fun p => tsum_congr fun e => (dTerm_prime_pow p.prop e).symm

/-- The zeta cross-section: at `s = 0` the displacement surface is the zeta series. -/
theorem dTerm_zero_left (w : ℝ) (n : ℕ) :
    dTerm 0 w n = if n = 0 then 0 else (n : ℝ) ^ (-w) := by
  unfold dTerm
  split
  · rfl
  · simp

theorem zeta_section (w : ℝ) :
    ∑' n : ℕ, dTerm 0 w n = ∑' n : ℕ, if n = 0 then 0 else (n : ℝ) ^ (-w) :=
  tsum_congr fun n => dTerm_zero_left w n

example : dTerm 0 2 1 = 1 := by
  rw [dTerm_zero_left]
  norm_num

end GoldenDisplacementEulerProduct
