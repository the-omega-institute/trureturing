/- GID: D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound
   mirror-E: none(waiver:symbolic-asymptotic-lower-bound)
   anchors: []
   utility: none
   digest: Odd squarefree primitive non-deficient integers avoiding finite prime sets. -/

import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound

open ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)
open ZelinskyZhangKLPrimitive (Deficient sig sig_prime_mul)

private def eulerH (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 + 1 / (p : ℝ))

private lemma prime_product_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < ∏ p ∈ s, p := prod_pos (fun p hp => (hs p hp).pos)

private lemma eulerH_pos (s : Finset ℕ) : 0 < eulerH s :=
  prod_pos (fun p _ => by positivity)

private lemma ratio_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    sig (∏ p ∈ s, p) / (∏ p ∈ s, p) = eulerH s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sig, eulerH]
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self _ _)
    have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpp (hsp q hq)).mpr
        (fun he => hp (he ▸ hq))
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hs0 : ((∏ q ∈ s, q : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (prime_product_pos s hsp).ne'
    rw [prod_insert hp, sig_prime_mul hpp hcop, Nat.cast_mul]
    have he : eulerH (insert p s) = (1 + 1 / (p : ℝ)) * eulerH s := by
      simp only [eulerH, prod_insert hp]
    rw [he]
    rw [← ih hsp]
    field_simp

private lemma product_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · exact fun p hp => (hs p hp).squarefree

private lemma prime_mem_of_dvd_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ s, q) : p ∈ s := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have he : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hpq
  exact he ▸ hq

private lemma primitive_of_erase (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hab : 2 ≤ eulerH s) (herase : ∀ p ∈ s, eulerH (s.erase p) < 2) :
    PrimitiveNonDeficient (∏ p ∈ s, p) := by
  classical
  have hn := prime_product_pos s hs
  have hnR : (0 : ℝ) < ∏ p ∈ s, p := by exact_mod_cast hn
  constructor
  · change ¬ sig (∏ p ∈ s, p) < 2 * (∏ p ∈ s, p)
    rw [← ratio_product s hs] at hab
    exact not_lt.mpr ((le_div_iff₀ hnR).mp hab)
  · intro d hd hlt
    have hdn := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hepos : 0 < (∏ p ∈ s, p) / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have hene : (∏ p ∈ s, p) / d ≠ 1 := by
      intro he
      have hh := Nat.div_mul_cancel hdn
      rw [he, one_mul] at hh
      omega
    obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd hene
    have hpn : p ∣ ∏ q ∈ s, q :=
      hpe.trans (Nat.div_dvd_of_dvd hdn)
    have hps := prime_mem_of_dvd_product s hs hp hpn
    have hprod : p * (∏ q ∈ s.erase p, q) = ∏ q ∈ s, q :=
      mul_prod_erase s id hps
    have hdp : d ∣ ∏ q ∈ s.erase p, q := by
      have hmul : p * d ∣ ∏ q ∈ s, q := by
        obtain ⟨a, ha⟩ := hpe
        refine ⟨a, ?_⟩
        calc
          _ = ((∏ q ∈ s, q) / d) * d := (Nat.div_mul_cancel hdn).symm
          _ = (p * a) * d := by rw [ha]
          _ = (p * d) * a := by ring
      rw [← hprod] at hmul
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hmul
    have hsmall := prime_product_pos (s.erase p)
      (fun q hq => hs q (mem_of_mem_erase hq))
    have hm := D5.S3.Arith.Robin.GA2ForcedPrimeSource.abundancy_mono
      hdpos hsmall hdp
    change sig d < 2 * d
    apply (div_lt_iff₀ (show (0 : ℝ) < d by exact_mod_cast hdpos)).mp
    apply hm.trans_lt
    change sig _ / _ < 2
    rw [ratio_product _ (fun q hq => hs q (mem_of_mem_erase hq))]
    exact herase p hps

private lemma strict_bernoulli (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 2 ≤ k) :
    1 + 1 / a < (1 + 1 / ((k : ℝ) * a)) ^ k := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hpos : 0 < 1 / ((k : ℝ) * a) := by positivity
  have h := one_add_mul_self_lt_rpow_one_add
    (s := 1 / ((k : ℝ) * a)) (by linarith) hpos.ne' hkR
  rw [rpow_natCast] at h
  convert h using 1
  congr 1
  field_simp

private lemma block_product_lower (s : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hk : 2 ≤ s.card) (hs : ∀ q ∈ s, (0 : ℝ) < q ∧ (q : ℝ) ≤ s.card * a) :
    1 + 1 / a < eulerH s := by
  apply (strict_bernoulli a ha s.card hk).trans_le
  change _ ≤ ∏ q ∈ s, (1 + 1 / (q : ℝ))
  rw [← Finset.prod_const (s := s)]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun q hq =>
    add_le_add le_rfl (one_div_le_one_div_of_le (hs q hq).1 (hs q hq).2))

private lemma block_product_upper (s : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hs : s.Nonempty) (hlo : ∀ q ∈ s, (s.card : ℝ) * (a + 1) < q) :
    eulerH s < 1 + 1 / a := by
  have hk : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have hy : 0 < (s.card : ℝ) * (a + 1) := by positivity
  have hsum : (∑ q ∈ s, 1 / (q : ℝ)) < 1 / (a + 1) := by
    calc
      _ < ∑ _q ∈ s, 1 / ((s.card : ℝ) * (a + 1)) := by
        apply sum_lt_sum_of_nonempty hs
        intro q hq
        exact one_div_lt_one_div_of_lt hy (hlo q hq)
      _ = 1 / (a + 1) := by simp; field_simp
  have hlog : 1 / (a + 1) ≤ log (1 + 1 / a) := by
    convert one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / a by positivity) using 1
    field_simp
    <;> ring
  calc
    eulerH s ≤ exp (∑ q ∈ s, 1 / (q : ℝ)) :=
      prod_one_add_le_exp_sum s (fun q => by positivity)
    _ < exp (1 / (a + 1)) := exp_lt_exp.mpr hsum
    _ ≤ exp (log (1 + 1 / a)) := exp_le_exp.mpr hlog
    _ = 1 + 1 / a := exp_log (by positivity)

end D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
