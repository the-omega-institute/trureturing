/- GID: D5/S3/ArithSums/EldarAntiharmonicAdjacency
   generality: G
   mirror-B: D5/B/S3/ArithSums/EldarAntiharmonicAdjacency
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Adjacent totative antiharmonic means are classified by Moebius signs. -/

/-
result:
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#24175; Proved)
Direct frozen dependencies:
  ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_two_mul_pow_one
  ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_six_mul_pow_two
  Owner: D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation.
  Declaration statement_id readings require the scoped Stage-B report; the cached
  report does not contain this owner. No module pin is used as a declaration identity.
The first and second power sums apply these owners after the injective rational-to-real cast.
The source uses inclusive positive totatives, including one at modulus one.
The classical first and second moments are attributed to Petridi, arXiv:1612.07632v2,
Section 1, and the sources credited there. The adjacent-equality classification is Eldar's
OEIS A179875 conjecture. It does not assert infinitude or the A179873 integral-mean claim.
All declarations have utility none: these are symbolic sums and identities, not a checker,
a reduction with numerical premises, an enumerator, or a certified finite instance.

indicator: proof_shape: bind-only; consumers: moment_moebius.
sum_multiples: proof_shape: content; consumers: moment_moebius.
moment_moebius: proof_shape: content; consumers: first_moment, second_moment.
first_power_sum: proof_shape: bind-only; consumers: first_moment.
second_power_sum: proof_shape: bind-only; consumers: second_moment.
moebius_product: proof_shape: bind-only; consumers: moebius_reciprocal, moebius_weighted.
moebius_sum: proof_shape: bind-only; consumers: first_moment, second_moment.
moebius_reciprocal: proof_shape: bind-only; consumers: first_moment, second_moment.
moebius_weighted: proof_shape: bind-only; consumers: second_moment.
signed_product: proof_shape: bind-only; consumers: error_product.
error_product: proof_shape: bind-only; consumers: normalized_moment.
first_moment: proof_shape: content; consumers: normalized_moment.
second_moment: proof_shape: content; consumers: normalized_moment.
normalized_moment: proof_shape: content; consumers: result.
error_abs: proof_shape: bind-only; consumers: error_bounds, error_endpoint.
error_bounds: proof_shape: bind-only; consumers: result.
error_on_squarefree: proof_shape: bind-only; consumers: error_endpoint.
error_endpoint: proof_shape: bind-only; consumers: result.
result: proof_shape: content; consumers: none.
The finite-sum bridge constructs multiplication by d with inverse natural division;
its arithmetic side conditions are verified in sum_multiples. Later moment identities
use this bridge. Other helpers use upstream identities and normalization.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25446.
-/

import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Foundation
import Mathlib.RingTheory.Radical.NatInt

/-! Positive totative moments and Eldar’s adjacency criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.EldarAntiharmonicAdjacency

open scoped BigOperators

/-- The positive reduced-residue moment from OEIS A053818 and A023896.
The inclusive endpoint gives the source convention S_j(1) = 1.
For n > 1 the condition k ≤ n and coprimality excludes k = n. -/
def totativeMoment (j n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, if Nat.Coprime k n then k ^ j else 0

/-- The rational antiharmonic mean B(n) = A053818(n) / A023896(n).
The claim only uses positive n; its denominator is positive since k = 1 occurs. -/
def antiharmonicMean (n : ℕ) : ℚ :=
  (totativeMoment 2 n : ℚ) / (totativeMoment 1 n : ℚ)

/-- Eldar's conjecture in OEIS A179875: exactly the positive indices with
Möbius signs 1 and -1 give equal adjacent rational antiharmonic means. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (antiharmonicMean n = antiharmonicMean (n + 1) ↔
      ArithmeticFunction.moebius n = 1 ∧ ArithmeticFunction.moebius (n + 1) = -1)

open Finset
open UniqueFactorizationMonoid
open scoped BigOperators

private theorem indicator (n k : ℕ) (hn : n ≠ 0) :
    (if k.Coprime n then (1 : ℚ) else 0) =
      ∑ d ∈ n.divisors, if d ∣ k then (ArithmeticFunction.moebius d : ℚ) else 0 := by
  have hs : (Nat.gcd k n).divisors = n.divisors.filter (fun d => d ∣ k) := by
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_right k n)]
    apply Finset.filter_congr
    intro d hd
    simp only [Nat.dvd_gcd_iff, Nat.dvd_of_mem_divisors hd, and_true]
  have h := congrArg (fun f : ArithmeticFunction ℚ => f (Nat.gcd k n))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] at h
  rw [← sum_filter, ← hs, h]

private theorem sum_multiples (n d j : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    (∑ k ∈ Icc 1 n, if d ∣ k then (k : ℚ)^j else 0) =
      (d : ℚ)^j * ∑ k ∈ Icc 1 (n / d), (k : ℚ)^j := by
  rw [← sum_filter, mul_sum]
  symm
  apply sum_bij (fun k _ => d * k)
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by nlinarith,
      (Nat.mul_le_mul_left d hk2).trans_eq (Nat.mul_div_cancel' hd)⟩, dvd_mul_right d k⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hd0 hab
  · intro k hk
    rcases mem_filter.mp hk with ⟨hk, hdk⟩
    refine ⟨k / d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right (mem_Icc.mp hk).2⟩,
      Nat.mul_div_cancel' hdk⟩
    exact Nat.one_le_div_iff hd0 |>.mpr (Nat.le_of_dvd (mem_Icc.mp hk).1 hdk)
  · intro k hk
    simp only [Nat.cast_mul, mul_pow]

private theorem moment_moebius (j n : ℕ) (hn : n ≠ 0) :
    (totativeMoment j n : ℚ) = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℚ) * (d : ℚ)^j *
        ∑ k ∈ Icc 1 (n / d), (k : ℚ)^j := by
  simp only [totativeMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_zero]
  calc
    (∑ k ∈ Icc 1 n, if k.Coprime n then (k : ℚ)^j else 0) =
        ∑ k ∈ Icc 1 n, (∑ d ∈ n.divisors,
          if d ∣ k then (ArithmeticFunction.moebius d : ℚ) else 0) * (k : ℚ)^j := by
      apply sum_congr rfl
      intro k hk
      rw [← indicator n k hn]
      split_ifs <;> simp
    _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) *
        ∑ k ∈ Icc 1 n, if d ∣ k then (k : ℚ)^j else 0 := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [sum_multiples n d j (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd)]
      ring

private theorem first_power_sum (m : ℕ) :
    (∑ k ∈ Icc 1 m, (k : ℚ)^1) = (m : ℚ) * ((m : ℚ) + 1) / 2 := by
  have h := ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_two_mul_pow_one m
  rw [← mul_sum] at h
  have hq : (2 : ℚ) * (∑ k ∈ Icc 1 m, (k : ℚ)^1) = (m : ℚ) * ((m : ℚ) + 1) := by
    exact_mod_cast h
  linarith

private theorem second_power_sum (m : ℕ) :
    (∑ k ∈ Icc 1 m, (k : ℚ)^2) = (m : ℚ) * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) / 6 := by
  have h := ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_six_mul_pow_two m
  rw [← mul_sum] at h
  have hq : (6 : ℚ) * (∑ k ∈ Icc 1 m, (k : ℚ)^2) =
      (m : ℚ) * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) := by
    exact_mod_cast h
  linarith

private theorem moebius_product (f : ArithmeticFunction ℚ) (hf : f.IsMultiplicative)
    (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * f d) =
      ∏ p ∈ n.primeFactors, (1 - f p) := by
  let r := radical n
  have hsf : Squarefree r := squarefree_radical
  have hsets : n.divisors.filter Squarefree = r.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hs⟩
      exact ⟨(dvd_radical_iff hs.isRadical hn).mpr hd, radical_ne_zero⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans radical_dvd_self, hn⟩, hsf.squarefree_of_dvd hd⟩
  have hfilter : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * f d) =
      ∑ d ∈ n.divisors.filter Squarefree, (ArithmeticFunction.moebius d : ℚ) * f d := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hds
    have hs : ¬Squarefree d := by simpa only [mem_filter, hd, true_and] using hds
    simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, Int.cast_zero, zero_mul]
  rw [hfilter, hsets,
    ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hsf]
  rw [Nat.primeFactors_radical]

private theorem moebius_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℚ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

private theorem moebius_reciprocal (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) / d) =
      (Nat.totient n : ℚ) / n := by
  let f : ArithmeticFunction ℚ := ⟨fun d => (d : ℚ)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro a b hab
      simp only [f, ArithmeticFunction.coe_mk, Nat.cast_mul, mul_inv_rev, mul_comm]
  have h := moebius_product f hf n hn
  simp only [f, ArithmeticFunction.coe_mk, ← div_eq_mul_inv] at h
  rw [h, Nat.totient_eq_mul_prod_factors]
  field_simp [hn]

private theorem moebius_weighted (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * d) =
      ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
  exact moebius_product (ArithmeticFunction.id : ArithmeticFunction ℚ)
    ArithmeticFunction.isMultiplicative_id.natCast n hn

private noncomputable def radicalError (n : ℕ) : ℚ :=
  (-1 : ℚ)^n.primeFactors.card * (radical n : ℕ) / n

private theorem signed_product (n : ℕ) :
    (∏ p ∈ n.primeFactors, (1 - (p : ℚ))) =
      (-1 : ℚ)^n.primeFactors.card * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
  simp_rw [show ∀ p : ℕ, (1 - (p : ℚ)) = -1 * ((p : ℚ) - 1) by
    intro p
    simpa only [neg_one_mul] using (neg_sub (p : ℚ) 1).symm]
  rw [prod_mul_distrib, prod_const]

private theorem error_product (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (1 - (p : ℚ))) / Nat.totient n = radicalError n := by
  have hphi := Nat.totient_mul_prod_primeFactors n
  have hc : (Nat.totient n : ℚ) * (radical n : ℕ) =
      (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
    rw [Nat.radical_eq_prod_primeFactors]
    have hp : ∀ p ∈ n.primeFactors, (↑(p - 1) : ℚ) = (p : ℚ) - 1 := by
      intro p hp
      exact Nat.cast_sub (Nat.one_le_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
    have h := congrArg (fun x : ℕ => (x : ℚ)) hphi
    simp only [Nat.cast_mul, Nat.cast_prod] at h
    rw [← Finset.prod_congr rfl hp]
    simpa only [Nat.cast_prod] using h
  have hnq : (n : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hn
  have hphiq : (Nat.totient n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  rw [signed_product]
  unfold radicalError
  field_simp
  nlinarith [hc]

private theorem first_moment (n : ℕ) (hn : 1 < n) :
    (totativeMoment 1 n : ℚ) = (n : ℚ) * Nat.totient n / 2 := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_zero_of_lt hn
  have hn1 : n ≠ 1 := by
    exact Ne.symm (Nat.ne_of_lt hn)
  have hnq : (n : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hn0
  calc
    (totativeMoment 1 n : ℚ) = ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (d : ℚ)^1 *
          ∑ k ∈ Icc 1 (n / d), (k : ℚ)^1 := moment_moebius 1 n hn0
    _ = ∑ d ∈ n.divisors, ((n : ℚ)^2 / 2 * ((ArithmeticFunction.moebius d : ℚ) / d) +
        (n : ℚ) / 2 * (ArithmeticFunction.moebius d : ℚ)) := by
      apply sum_congr rfl
      intro d hd
      rw [first_power_sum, Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
      have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      field_simp
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, moebius_reciprocal n hn0, moebius_sum,
        ite_eq_right hn1]
      field_simp
      ring

private theorem second_moment (n : ℕ) (hn : 1 < n) :
    (totativeMoment 2 n : ℚ) = (n : ℚ)^2 * Nat.totient n / 3 +
      (n : ℚ) / 6 * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_zero_of_lt hn
  have hn1 : n ≠ 1 := by
    exact Ne.symm (Nat.ne_of_lt hn)
  have hnq : (n : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hn0
  calc
    (totativeMoment 2 n : ℚ) = ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (d : ℚ)^2 *
          ∑ k ∈ Icc 1 (n / d), (k : ℚ)^2 := moment_moebius 2 n hn0
    _ = ∑ d ∈ n.divisors, ((n : ℚ)^3 / 3 * ((ArithmeticFunction.moebius d : ℚ) / d) +
        (n : ℚ)^2 / 2 * (ArithmeticFunction.moebius d : ℚ) +
        (n : ℚ) / 6 * ((ArithmeticFunction.moebius d : ℚ) * d)) := by
      apply sum_congr rfl
      intro d hd
      rw [second_power_sum, Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
      have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      field_simp
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
        moebius_reciprocal n hn0, moebius_sum, ite_eq_right hn1, moebius_weighted n hn0]
      field_simp
      ring

private theorem normalized_moment (n : ℕ) (hn : 1 ≤ n) :
    3 * antiharmonicMean n = 2 * (n : ℚ) + radicalError n := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    norm_num [antiharmonicMean, totativeMoment, radicalError]
  · have hn0 : n ≠ 0 := by
      exact Nat.ne_zero_of_lt hn
    have hnq : (n : ℚ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr hn0
    have hphiq : (Nat.totient n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)).ne'
    rw [antiharmonicMean, first_moment n h, second_moment n h, ← error_product n hn0]
    field_simp
    ring

private theorem error_abs (n : ℕ) :
    (|radicalError n|) = (radical n : ℕ) / (n : ℚ) := by
  unfold radicalError
  rw [abs_div, abs_mul, abs_pow]
  norm_num

private theorem error_bounds (n : ℕ) (hn : 1 ≤ n) :
    -1 ≤ radicalError n ∧ radicalError n ≤ 1 := by
  apply abs_le.mp
  rw [error_abs n]
  have hnq : (0 : ℚ) < n := by
    exact Rat.natCast_pos.mpr hn
  apply (div_le_one hnq).mpr
  exact_mod_cast (Nat.radical_le_self_iff.mpr (by omega : n ≠ 0))

private theorem error_on_squarefree (n : ℕ) (hn : Squarefree n) :
    radicalError n = (ArithmeticFunction.moebius n : ℚ) := by
  have hc : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
    rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors,
      List.toFinset_card_of_nodup hn.nodup_primeFactorsList]
  have hr : radical n = n := by
    rw [Nat.radical_eq_prod_primeFactors, Nat.prod_primeFactors_of_squarefree hn]
  rw [radicalError, hr, hc, ArithmeticFunction.moebius_apply_of_squarefree hn]
  push_cast
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne_zero
  field_simp

private theorem error_endpoint (n : ℕ) (hn : 1 ≤ n) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    radicalError n = (s : ℚ) ↔ ArithmeticFunction.moebius n = s := by
  constructor
  · intro he
    have ha : |radicalError n| = 1 := by
      rw [he]
      rcases hs with rfl | rfl <;> norm_num
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [error_abs n, div_eq_one_iff_eq hnq] at ha
    have hr : radical n = n := by exact_mod_cast ha
    have hsf : Squarefree n := by rw [← hr]; exact squarefree_radical
    rw [error_on_squarefree n hsf] at he
    exact_mod_cast he
  · intro hm
    have hm0 : ArithmeticFunction.moebius n ≠ 0 := by
      rw [hm]
      rcases hs with rfl | rfl <;> norm_num
    rw [error_on_squarefree n (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hm0), hm]

theorem result : claim := by
  intro n hn
  have hnp : 1 ≤ n + 1 := by
    exact Nat.le_add_right_of_le hn
  have h1 := normalized_moment n hn
  have h2 := normalized_moment (n + 1) hnp
  have hbn := error_bounds n hn
  have hbnp := error_bounds (n + 1) hnp
  have he1 := error_endpoint n hn 1 (Or.inl rfl)
  have he2 := error_endpoint (n + 1) hnp (-1) (Or.inr rfl)
  norm_num only [Int.cast_one, Int.cast_neg] at he1 he2
  rw [← he1, ← he2]
  push_cast at h2
  constructor
  · intro hm
    rw [hm] at h1
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    rw [ha] at h1
    rw [hb] at h2
    linarith

end D5.S3.ArithSums.EldarAntiharmonicAdjacency
