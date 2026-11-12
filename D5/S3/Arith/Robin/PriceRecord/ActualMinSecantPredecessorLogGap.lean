/-
SOURCE ONLY: candidate for baseline e5c0aaffd35b1e17544000d3aea1dfed58a3f7f8.
Lean 4.35.0 / mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
UNCOMPILED, N0 OPEN. No kernel acceptance is claimed.

Ordinary mathematical input: Sections I.1--I.2 only of
answer-active-facet-bank-integer-geometry-20261112.txt,
SHA256 318699a0206675aaa3bea64288947d252d17c344df6b4a25b905caf78c5ee8ca.
The finite proof uses the equivalent split h < log P / log P <= h, avoiding
an extra gcd sum. It never changes the given minimizer. In particular q=1
is included. There is no BHP, target-gap, price-localization or payment premise.
-/

import D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)

/- Every helper below is private and consumed by the main theorem. No library
exposure patch is needed. `goldenResourceObjective 0 n` is exactly ell(n),
by golden_resource_sigma_identity for n >= 1. -/

private theorem price_change (t : ℝ) (n : ℕ) :
    goldenResourceObjective t n = goldenResourceObjective 0 n - t * Real.log n := by
  simp only [goldenResourceObjective, zero_mul, sub_zero]

private theorem log_gap_pos {m q : ℕ} (hq : 0 < q) (hqm : q < m) :
    0 < Real.log ((m : ℝ) / q) := by
  apply Real.log_pos
  exact (one_lt_div (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
    (by exact_mod_cast hqm)

private theorem secant_support {m q : ℕ} (hq : 0 < q) (hqm : q < m)
    {mu : ℝ}
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hmin : ∀ r : ℕ, 0 < r → r < m →
      (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
          Real.log ((m : ℝ) / q) ≤
        (goldenResourceObjective 0 m - goldenResourceObjective 0 r) /
          Real.log ((m : ℝ) / r)) :
    let nu := (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
      Real.log ((m : ℝ) / q)
    mu < nu ∧ goldenResourceObjective nu q = goldenResourceObjective nu m ∧
      ∀ r : ℕ, 0 < r → r ≤ m →
        goldenResourceObjective nu r ≤ goldenResourceObjective nu m := by
  let nu := (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
    Real.log ((m : ℝ) / q)
  change mu < nu ∧ _
  have hm : 0 < m := hq.trans hqm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hh := log_gap_pos hq hqm
  have hid : nu * Real.log ((m : ℝ) / q) =
      goldenResourceObjective 0 m - goldenResourceObjective 0 q :=
    div_mul_cancel₀ _ hh.ne'
  have hprice : mu < nu := by
    apply (lt_div_iff₀ hh).mpr
    have hr := hrecord q hq hqm
    rw [price_change mu q, price_change mu m] at hr
    rw [Real.log_div hmR hqR]
    nlinarith
  have htie : goldenResourceObjective nu q = goldenResourceObjective nu m := by
    rw [Real.log_div hmR hqR] at hid
    rw [price_change nu q, price_change nu m]
    nlinarith
  refine ⟨hprice, htie, ?_⟩
  intro r hr hrm
  rcases hrm.eq_or_lt with heq | hlt
  · subst r
    exact le_rfl
  · have hineq : nu * Real.log ((m : ℝ) / r) ≤
        goldenResourceObjective 0 m - goldenResourceObjective 0 r :=
      (le_div_iff₀ (log_gap_pos hr hlt)).mp (hmin r hr hlt)
    rw [Real.log_div hmR (by exact_mod_cast hr.ne')] at hineq
    rw [price_change nu r, price_change nu m]
    nlinarith

/- This is a non-strict maximum lemma: deletion is an actual positive integer
predecessor, and equality of a marginal with nu is permitted. -/
private theorem occupied_top_price {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    {nu : ℝ}
    (hmax : ∀ r : ℕ, 0 < r → r ≤ m →
      goldenResourceObjective nu r ≤ goldenResourceObjective nu m)
    (ha : 1 ≤ m.factorization p) :
    nu ≤ goldenLayerMarginal p (m.factorization p) := by
  have hd : p ∣ m := (hp.dvd_iff_one_le_factorization hm.ne').mpr ha
  have hn : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hd) hp.pos
  have heq : m / p * p = m := Nat.div_mul_cancel hd
  have hfac : (m / p).factorization p + 1 = m.factorization p := by
    have h := congrArg (fun n : ℕ => n.factorization p) heq
    simpa [Nat.factorization_mul hn.ne' hp.ne_zero, hp.factorization] using h
  have hdelta := golden_resource_objective_single_layer_delta nu
    (by omega : 1 ≤ m / p) hp
  rw [heq, hfac] at hdelta
  have hcomp := hmax (m / p) hn (Nat.div_le_self _ _)
  have hnet : 0 ≤ (goldenLayerMarginal p (m.factorization p) - nu) * Real.log p := by
    rw [← hdelta]
    exact sub_nonneg.mpr hcomp
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp.log_pos).mp hnet)

private theorem affordable_excess {m q p : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hp : p.Prime) {nu : ℝ}
    (hmax : ∀ r : ℕ, 0 < r → r ≤ m →
      goldenResourceObjective nu r ≤ goldenResourceObjective nu m)
    (htie : goldenResourceObjective nu q = goldenResourceObjective nu m)
    (hinsert : q * p ≤ m) (hexcess : q.factorization p < m.factorization p) :
    m.factorization p = q.factorization p + 1 ∧
      goldenLayerMarginal p (m.factorization p) = nu := by
  have htop := occupied_top_price hm hp hmax (by omega)
  have hdelta := golden_resource_objective_single_layer_delta nu
    (by omega : 1 ≤ q) hp
  have hcomp := hmax (q * p) (Nat.mul_pos hq hp.pos) hinsert
  have hnext : goldenLayerMarginal p (q.factorization p + 1) ≤ nu := by
    have hnet : 0 ≤ (nu - goldenLayerMarginal p (q.factorization p + 1)) * Real.log p := by
      nlinarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp.log_pos).mp hnet)
  have heq : m.factorization p = q.factorization p + 1 := by
    by_contra hne
    have hlt : q.factorization p + 1 < m.factorization p := by omega
    have hs := golden_layer_strict_decrease hp (by omega) hlt
    linarith
  refine ⟨heq, le_antisymm ?_ htop⟩
  simpa only [heq] using hnext

/- General-layer prime monotonicity. The denominator S_j(p) = p*(1+...+p^(j-1))
is strictly increasing in p. This is not a pairwise irrationality assertion. -/
private theorem marginal_geom {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    goldenLayerMarginal p j =
      Real.log (1 + ((p : ℝ) * ∑ i ∈ range j, (p : ℝ) ^ i)⁻¹) / Real.log p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpj : 1 < (p : ℝ) ^ j := one_lt_pow₀ hp1 (by omega)
  have hpjne : (p : ℝ) ^ j ≠ 0 := pow_ne_zero _ hp0.ne'
  unfold goldenLayerMarginal
  congr 2
  rw [geom_sum_eq (ne_of_gt hp1)]
  simp only [inv_pow, pow_succ]
  field_simp [hp0.ne', hpjne, sub_ne_zero.mpr hpj.ne', sub_ne_zero.mpr hp1.ne']
  <;> ring

private theorem marginal_prime_strictAnti {p r j : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p < r) (hj : 1 ≤ j) :
    goldenLayerMarginal r j < goldenLayerMarginal p j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hprR : (p : ℝ) < r := by exact_mod_cast hpr
  have hsumpos : 0 < ∑ i ∈ range j, (p : ℝ) ^ i := by
    have hle : (1 : ℝ) ≤ ∑ i ∈ range j, (p : ℝ) ^ i := by
      simpa using (Finset.single_le_sum
        (fun i (_ : i ∈ range j) => pow_nonneg hp0.le i)
        (show 0 ∈ range j by simp; omega))
    linarith
  have hsumle : (∑ i ∈ range j, (p : ℝ) ^ i) ≤
      ∑ i ∈ range j, (r : ℝ) ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hp0.le hprR.le i)
  have hden : (p : ℝ) * (∑ i ∈ range j, (p : ℝ) ^ i) <
      (r : ℝ) * (∑ i ∈ range j, (r : ℝ) ^ i) :=
    (mul_lt_mul_of_pos_right hprR hsumpos).trans_le
      (mul_le_mul_of_nonneg_left hsumle hr0.le)
  have hdenpos : 0 < (p : ℝ) * (∑ i ∈ range j, (p : ℝ) ^ i) :=
    mul_pos hp0 hsumpos
  have hdenrpos := hdenpos.trans hden
  have hinvrpos := inv_pos.mpr hdenrpos
  have hinv := inv_strictAnti₀ hdenpos hden
  have hnum : Real.log (1 + ((r : ℝ) * ∑ i ∈ range j, (r : ℝ) ^ i)⁻¹) <
      Real.log (1 + ((p : ℝ) * ∑ i ∈ range j, (p : ℝ) ^ i)⁻¹) :=
    Real.log_lt_log (by linarith) (by linarith)
  have hnumpos : 0 < Real.log
      (1 + ((p : ℝ) * ∑ i ∈ range j, (p : ℝ) ^ i)⁻¹) :=
    Real.log_pos (by linarith [inv_pos.mpr hdenpos])
  rw [marginal_geom hp hj, marginal_geom hr hj]
  exact div_lt_div₀ hnum (Real.log_lt_log hp0 hprR).le hnumpos.le hp.log_pos

private theorem log_on_support {n : ℕ} (s : Finset ℕ)
    (hsub : n.primeFactors ⊆ s) :
    Real.log (n : ℝ) = ∑ p ∈ s, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization n]
  simp only [Finsupp.sum, Nat.support_factorization]
  apply sum_subset hsub
  intro p _ hp
  have hz : n.factorization p = 0 := by
    simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
  simp only [hz, Nat.cast_zero, zero_mul]

/- Finite endpoint: max(log P, log(4P^2) H_floor(log(4P^2)/log 2)).
The natural-number prime-power envelope is imported and discharged from the
original full strict record, never assumed as an extra hypothesis. -/
private theorem finite_log_gap {m q : ℕ} (hm : 2 ≤ m) (hq : 0 < q)
    (hqm : q < m) {mu : ℝ} (hmu : 0 < mu)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hmin : ∀ r : ℕ, 0 < r → r < m →
      (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
          Real.log ((m : ℝ) / q) ≤
        (goldenResourceObjective 0 m - goldenResourceObjective 0 r) /
          Real.log ((m : ℝ) / r)) :
    Real.log ((m : ℝ) / q) ≤
      max (Real.log (largestPrime m : ℝ))
        (Real.log (4 * (largestPrime m : ℝ) ^ 2) *
          (harmonic ⌊Real.log (4 * (largestPrime m : ℝ) ^ 2) / Real.log 2⌋₊ : ℝ)) := by
  classical
  let P : ℝ := largestPrime m
  let B : ℝ := Real.log (4 * P ^ 2)
  let N : ℕ := ⌊B / Real.log 2⌋₊
  let nu := (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
    Real.log ((m : ℝ) / q)
  obtain ⟨hmunu, htie, hmax⟩ := secant_support hq hqm hrecord hmin
  change goldenResourceObjective nu q = goldenResourceObjective nu m at htie
  change ∀ r : ℕ, 0 < r → r ≤ m →
    goldenResourceObjective nu r ≤ goldenResourceObjective nu m at hmax
  have hm0 : 0 < m := by omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hrP : r ≤ largestPrime m :=
    Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hr, hrd, hm0.ne'⟩)
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hr.two_le.trans hrP
  have hP0 : 0 < P := by linarith
  have hB : 0 ≤ B := Real.log_nonneg (by nlinarith [sq_nonneg (P - 1)])
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change Real.log ((m : ℝ) / q) ≤ max (Real.log P) (B * (harmonic N : ℝ))
  by_cases hsmall : Real.log ((m : ℝ) / q) < Real.log P
  · exact hsmall.le.trans (le_max_left _ _)
  have hlarge : Real.log P ≤ Real.log ((m : ℝ) / q) := le_of_not_gt hsmall
  let s := m.primeFactors ∪ q.primeFactors
  let S := s.filter (fun p => q.factorization p < m.factorization p)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hSm (p : ℕ) (hp : p ∈ S) : p ∈ m.primeFactors := by
    obtain ⟨hps, hex⟩ := mem_filter.mp hp
    have hpp := hprime p hps
    exact Nat.mem_primeFactors.mpr ⟨hpp,
      (hpp.dvd_iff_one_le_factorization hm0.ne').mpr (by omega), hm0.ne'⟩
  have hex (p : ℕ) (hp : p ∈ S) :
      m.factorization p = q.factorization p + 1 ∧
        goldenLayerMarginal p (m.factorization p) = nu := by
    have hpp := Nat.prime_of_mem_primeFactors (hSm p hp)
    have hpP : (p : ℝ) ≤ P := by
      exact_mod_cast (Finset.le_sup (f := id) (hSm p hp))
    have hlogp : Real.log (p : ℝ) ≤ Real.log ((m : ℝ) / q) :=
      (Real.log_le_log (by exact_mod_cast hpp.pos) hpP).trans hlarge
    have hple : (p : ℝ) ≤ (m : ℝ) / q :=
      (Real.log_le_log_iff (by exact_mod_cast hpp.pos)
        (div_pos (by exact_mod_cast hm0) (by exact_mod_cast hq))).mp hlogp
    have hinsertR : (q : ℝ) * p ≤ m := by
      have hh := (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mp hple
      nlinarith
    exact affordable_excess hm0 hq hpp hmax htie
      (by exact_mod_cast hinsertR) (mem_filter.mp hp).2
  have hgap : Real.log ((m : ℝ) / q) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    rw [Real.log_div (by exact_mod_cast hm0.ne') (by exact_mod_cast hq.ne'),
      log_on_support (n := m) s subset_union_left,
      log_on_support (n := q) s subset_union_right,
      ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ s, if q.factorization p < m.factorization p
          then Real.log (p : ℝ) else 0 := by
        apply sum_le_sum
        intro p hp
        by_cases he : q.factorization p < m.factorization p
        · have ha := (hex p (mem_filter.mpr ⟨hp, he⟩)).1
          simp only [if_pos he, ha, Nat.cast_add, Nat.cast_one]
          nlinarith
        · have hle : (m.factorization p : ℝ) ≤ q.factorization p := by
            exact_mod_cast (le_of_not_gt he)
          simp only [if_neg he]
          nlinarith [mul_nonneg (sub_nonneg.mpr hle)
            (Real.log_natCast_nonneg p)]
      _ = ∑ p ∈ S, Real.log (p : ℝ) := by rw [sum_filter]
  have hbound (p : ℕ) (hp : p ∈ S) :
      1 ≤ m.factorization p ∧ m.factorization p ≤ N ∧
        Real.log (p : ℝ) ≤ B / (m.factorization p : ℝ) := by
    have hpp := Nat.prime_of_mem_primeFactors (hSm p hp)
    have ha : 1 ≤ m.factorization p := by have := (mem_filter.mp hp).2; omega
    have hpow := price_record_prime_power_envelope hm hmu.le hrecord p hpp
      (Nat.dvd_of_mem_primeFactors (hSm p hp))
    have hpowR : (p : ℝ) ^ m.factorization p < 4 * P ^ 2 := by
      exact_mod_cast hpow
    have hlog := Real.log_lt_log (pow_pos (by exact_mod_cast hpp.pos) _) hpowR
    rw [Real.log_pow] at hlog
    change (m.factorization p : ℝ) * Real.log p < B at hlog
    have hlog2p : Real.log (2 : ℝ) ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
    have hN : m.factorization p ≤ N := by
      apply (Nat.le_floor_iff (div_nonneg hB hlog2.le)).mpr
      apply (le_div_iff₀ hlog2).mpr
      exact (mul_le_mul_of_nonneg_left hlog2p (Nat.cast_nonneg _)).trans hlog.le
    refine ⟨ha, hN, ?_⟩
    apply (le_div_iff₀ (by exact_mod_cast (by omega : 0 < m.factorization p))).mpr
    nlinarith
  have hinj : Set.InjOn (fun p : ℕ => m.factorization p) S := by
    intro p hp r hr heq
    have hpp := Nat.prime_of_mem_primeFactors (hSm p hp)
    have hrp := Nat.prime_of_mem_primeFactors (hSm r hr)
    have hpprice := (hex p hp).2
    have hrprice := (hex r hr).2
    rcases lt_trichotomy p r with hlt | he | hgt
    · have hrprice' : goldenLayerMarginal r (m.factorization p) = nu := by
        simpa only [heq] using hrprice
      have hh := marginal_prime_strictAnti hpp hrp hlt (hbound p hp).1
      rw [hrprice', hpprice] at hh
      exact (lt_irrefl nu hh).elim
    · exact he
    · have hpprice' : goldenLayerMarginal p (m.factorization r) = nu := by
        simpa only [← heq] using hpprice
      have hh := marginal_prime_strictAnti hrp hpp hgt (hbound r hr).1
      rw [hpprice', hrprice] at hh
      exact (lt_irrefl nu hh).elim
  have himage : S.image (fun p => m.factorization p) ⊆ Icc 1 N := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨(hbound p hp).1, (hbound p hp).2.1⟩
  have hsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ B * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, B / (m.factorization p : ℝ) :=
        sum_le_sum (fun p hp => (hbound p hp).2.2)
      _ = ∑ j ∈ S.image (fun p => m.factorization p), B / (j : ℝ) :=
        (sum_image hinj).symm
      _ ≤ ∑ j ∈ Icc 1 N, B / (j : ℝ) :=
        sum_le_sum_of_subset_of_nonneg himage (fun j _ _ =>
          div_nonneg hB (Nat.cast_nonneg j))
      _ = B * (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          mul_sum, div_eq_mul_inv]
  exact (hgap.trans hsum).trans (le_max_right _ _)

/- Explicit uniform conversion. The constants are chosen before all m, mu, q.
P >= exp 4 implies L >= 4 and log L >= 1; the final constant 32 is generous. -/
private theorem harmonic_bound_uniform {P : ℝ} (hP : Real.exp 4 ≤ P) :
    max (Real.log P)
      (Real.log (4 * P ^ 2) *
        (harmonic ⌊Real.log (4 * P ^ 2) / Real.log 2⌋₊ : ℝ)) ≤
      32 * Real.log P * Real.log (Real.log P) := by
  let L := Real.log P
  let B := Real.log (4 * P ^ 2)
  have hP0 : 0 < P := (Real.exp_pos 4).trans_le hP
  have hL : 4 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos 4) hP
    simpa [L, Real.log_exp] using hh
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog2hi : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hB : B = 2 * Real.log 2 + 2 * L := by
    dsimp [B, L]
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hP0.ne'), Real.log_pow, hlog4]
  have hB0 : 0 ≤ B := by linarith
  have hBupper : B ≤ 4 * L := by linarith
  have hy : 1 ≤ B / Real.log 2 := by
    apply (le_div_iff₀ hlog2pos).mpr
    linarith
  have hyupper : B / Real.log 2 ≤ 8 * L := by
    apply (div_le_iff₀ hlog2pos).mpr
    have hmul := mul_nonneg (by linarith : 0 ≤ L)
      (by linarith : 0 ≤ 2 * Real.log 2 - 1)
    nlinarith
  have hlogL : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hL
    rw [hlog4] at hh
    linarith
  have hH : (harmonic ⌊B / Real.log 2⌋₊ : ℝ) ≤ 5 * Real.log L := by
    calc
      _ ≤ 1 + Real.log (B / Real.log 2) := harmonic_floor_le_one_add_log _ hy
      _ ≤ 1 + Real.log (8 * L) := add_le_add_left
        (Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy)
          hyupper) 1
      _ = 1 + 3 * Real.log 2 + Real.log L := by
        rw [Real.log_mul (by norm_num) (by linarith : L ≠ 0), hlog8]
      _ ≤ 5 * Real.log L := by linarith
  have hprod : B * (harmonic ⌊B / Real.log 2⌋₊ : ℝ) ≤
      (4 * L) * (5 * Real.log L) :=
    (mul_le_mul_of_nonneg_left hH hB0).trans
      (mul_le_mul_of_nonneg_right hBupper (by linarith))
  change max L (B * (harmonic ⌊B / Real.log 2⌋₊ : ℝ)) ≤
    32 * L * Real.log L
  have hLL : 0 ≤ L * Real.log L :=
    mul_nonneg (by linarith) (by linarith)
  have hLle : L ≤ L * Real.log L := by
    have hh := mul_nonneg (by linarith : 0 ≤ L)
      (by linarith : 0 ≤ Real.log L - 1)
    nlinarith
  apply max_le
  · nlinarith
  · nlinarith

/-- Absolute constants precede every actual integer, every original positive
price/full strict record, and every actual minimum-secant predecessor. The
minimizer premise is precisely attainment of the minimum of all actual ratios
on {1,...,m-1}; no selected inventory, unique minimizer or gap premise occurs.
The logarithmic numerators are literally log(sigma(n)/n).
UNCOMPILED candidate: formal status N0 OPEN. -/
theorem actual_min_secant_predecessor_eventual_log_gap :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective mu n < goldenResourceObjective mu m) →
      ∀ q : ℕ, 0 < q → q < m →
      (∀ r : ℕ, 0 < r → r < m →
        (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) -
          Real.log ((ArithmeticFunction.sigma 1 q : ℝ) / q)) /
            Real.log ((m : ℝ) / q) ≤
        (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) -
          Real.log ((ArithmeticFunction.sigma 1 r : ℝ) / r)) /
            Real.log ((m : ℝ) / r)) →
      T ≤ (largestPrime m : ℝ) →
      0 < Real.log ((m : ℝ) / q) ∧
        Real.log ((m : ℝ) / q) ≤
          C * Real.log (largestPrime m : ℝ) *
            Real.log (Real.log (largestPrime m : ℝ)) := by
  refine ⟨32, Real.exp 4, by norm_num, Real.exp_pos 4, ?_⟩
  intro m hm mu hmu hrecord q hq hqm hmin hlarge
  have hmin' : ∀ r : ℕ, 0 < r → r < m →
      (goldenResourceObjective 0 m - goldenResourceObjective 0 q) /
          Real.log ((m : ℝ) / q) ≤
        (goldenResourceObjective 0 m - goldenResourceObjective 0 r) /
          Real.log ((m : ℝ) / r) := by
    intro r hr hrm
    simpa only [golden_resource_sigma_identity 0 (by omega : 1 ≤ m),
      golden_resource_sigma_identity 0 (by omega : 1 ≤ q),
      golden_resource_sigma_identity 0 (by omega : 1 ≤ r), zero_mul, sub_zero]
      using hmin r hr hrm
  exact ⟨log_gap_pos hq hqm,
    (finite_log_gap hm hq hqm hmu hrecord hmin').trans (harmonic_bound_uniform hlarge)⟩

end D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap
