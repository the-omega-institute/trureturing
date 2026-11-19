/- GID: D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization
   generality: I
   mirror-B: D5/B/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime support of primitive numerators proves Kurkov's composite-term factorization. -/

/-
admission_basis: open-problem-resolution (#23541; Proved)
escape_witness: source_prime_support (admission uses the settling result).
Direct frozen dependencies: none (no D5 imports).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30662
The source's numerator, enumeration and claim retain their stated expressions.
The private polynomial recurrence is ring-parametric; the scalar H owner does
not supply this polynomial construction or its coefficient statements.

Declarations (same-delivery helpers expanded when assessing proof_shape):
sourcePolynomial: proof_shape: bind-only; kind: definition; consumers: IsSourceSequence, source_Q, source_prime_support, source_divisor_closed,
  source_one, source_three_pow, source_sequence_exists, source_sequence_one,
  result.
IsSourceSequence: proof_shape: bind-only; kind: definition; consumers: claim,
  source_sequence_exists, source_sequence_one, result.
claim: proof_shape: bind-only; kind: definition; consumer: result.
Q: proof_shape: bind-only; kind: recursive definition; consumers: Q_sum, source_Q, Q_coeff, Q_map,
  Q_reset, Q_reduce, source_prime_support, source_divisor_closed,
  source_three_pow.
Q_sum: proof_shape: content; escape_witness: Q_sum;
  Direct frozen dependencies: none; consumers: source_Q.
source_Q: proof_shape: content; escape_witness: Q_sum;
  Direct frozen dependencies: none; consumers: source_prime_support.
Q_coeff: proof_shape: content; escape_witness: Q_coeff;
  Direct frozen dependencies: none; consumers: source_prime_support.
Q_map: proof_shape: content; escape_witness: Q_map;
  Direct frozen dependencies: none; consumers: source_prime_support.
Q_reset: proof_shape: content; escape_witness: Q_reset;
  Direct frozen dependencies: none; consumers: Q_reduce.
primitive_iff_no_prime: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: source_prime_support.
C_dvd_iff_zmod: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: source_prime_support.
Q_reduce: proof_shape: content; escape_witness: Q_reset;
  Direct frozen dependencies: none; consumers: source_prime_support.
source_prime_support: proof_shape: content; escape_witness: source_prime_support;
  Direct frozen dependencies: none; consumers: source_divisor_closed, source_three_pow.
source_divisor_closed: proof_shape: content; escape_witness: source_prime_support;
  Direct frozen dependencies: none; consumers: result.
source_one: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: source_sequence_one.
source_three_pow: proof_shape: content; escape_witness: source_prime_support;
  Direct frozen dependencies: none; consumers: source_sequence_exists.
source_sequence_exists: proof_shape: content; escape_witness: source_prime_support;
  Direct frozen dependencies: none; consumers: result.
source_sequence_one: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
result: proof_shape: content; escape_witness: source_prime_support;
  Direct frozen dependencies: none; consumers: none (settling result).

The inductive polynomial representation, coefficient bound and modular reset
are the mathematical steps beyond instantiation and normalization. Integer
primitiveness and coefficientwise reduction use Mathlib directly.
-/

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Nth

namespace D5.S3.Arith.PolynomialValues.KurkovA248667CompositeFactorization

open Polynomial
open scoped BigOperators

/-- The unreduced numerator over the full denominator specified in OEIS A248667.
The interval Ico (j + 1) n lists precisely j + 1, ..., n - 1. -/
noncomputable def sourcePolynomial (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range n,
    ∏ i ∈ Finset.Ico (j + 1) n, (C (n : ℤ) * X + C (i : ℤ))

/-- The increasing, one-based enumeration of the positive indices whose numerator
polynomial has relatively prime coefficients. The dummy value a 0 = 0 is outside
the source's index domain. IsPrimitive is Mathlib's existing polynomial predicate. -/
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ StrictMono a ∧
    ∀ n : ℕ, (∃ k : ℕ, 0 < k ∧ a k = n) ↔
      0 < n ∧ (sourcePolynomial n).IsPrimitive

/-- Kurkov's composite-term factorization conjecture, with existence of the source
sequence included. Equal factor indices are allowed. -/
def claim : Prop :=
  (∃ a : ℕ → ℕ, IsSourceSequence a) ∧
    ∀ a : ℕ → ℕ, IsSourceSequence a →
      ∀ k : ℕ, 0 < k → 1 < a k → ¬ Nat.Prime (a k) →
        ∃ i : ℕ, ∃ j : ℕ, 1 < i ∧ 1 < j ∧ a k = a i * a j


private noncomputable def Q {R : Type*} [CommRing R] (a : R) : ℕ → R[X]
  | 0 => 1
  | m+1 => (C a * X + C (m+1 : R)) * Q a m + 1

private theorem Q_sum {R : Type*} [CommRing R] (a : R) (m : ℕ) :
    Q a m = ∑ j ∈ Finset.range (m+1),
      ∏ i ∈ Finset.Ico (j+1) (m+1), (C a * X + C (i : R)) := by
  induction m with
  | zero => simp [Q]
  | succ m ih =>
    rw [Q, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Finset.Ico_self, Finset.prod_empty]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m+1 := Finset.mem_range.mp hj
    rw [Finset.prod_Ico_succ_top (a := j+1) (b := m+1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    exact mul_comm _ _

private theorem source_Q (n : ℕ) (hn : 0 < n) : sourcePolynomial n = Q (n : ℤ) (n-1) := by
  rw [Q_sum]
  simp [Nat.sub_add_cancel hn, sourcePolynomial]

private theorem Q_coeff {R : Type*} [CommRing R] (a : R) (m : ℕ) :
    (∀ k, m < k → (Q a m).coeff k = 0) ∧ (Q a m).coeff m = a^m := by
  induction m with
  | zero =>
    constructor
    · intro k hk; simp [Q, coeff_one, show k ≠ 0 by omega]
    · simp [Q]
  | succ m ih =>
    have he : Q a (m+1) = C a * (Q a m * X) + C (m+1 : R) * Q a m + 1 := by
      rw [Q]; ring
    rw [he]
    constructor
    · intro k hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      simp only [coeff_add, coeff_C_mul, coeff_mul_X, coeff_one]
      rw [ih.1 k (by omega), ih.1 (k+1) (by omega)]
      simp
    · simp only [coeff_add, coeff_C_mul, coeff_mul_X, coeff_one, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ite_false, add_zero]
      rw [ih.2, ih.1 (m+1) (by omega)]
      simp [pow_succ, mul_comm]

private theorem Q_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (m : ℕ) :
    (Q a m).map f = Q (f a) m := by
  induction m with
  | zero => simp [Q]
  | succ m ih => simp [Q, ih]

private theorem Q_reset {R : Type*} [CommRing R] (b j : ℕ) (hb : (b : R) = 0) :
    Q (0 : R) (b+j) = Q (0 : R) j := by
  induction j with
  | zero =>
    cases b with
    | zero => rfl
    | succ b =>
      have hb' : (b : R) + 1 = 0 := by simpa using hb
      simp [Q, hb']
  | succ j ih =>
    change (C (0:R) * X + C (((b+j:ℕ):R)+1)) * Q (0:R) (b+j) + 1 = _
    rw [Nat.cast_add, hb, zero_add, ih]
    rfl

private theorem primitive_iff_no_prime (P : ℤ[X]) :
    P.IsPrimitive ↔ ∀ p : ℕ, Nat.Prime p → ¬ C (p : ℤ) ∣ P := by
  constructor
  · intro h p hp hd
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (h _ hd)
  · intro h r hr
    apply Int.isUnit_iff_natAbs_eq.mpr
    by_contra hnu
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hnu
    exact h p hp (dvd_trans (map_dvd C (Int.natCast_dvd.mpr hpd)) hr)

private theorem C_dvd_iff_zmod (P : ℤ[X]) (p : ℕ) :
    C (p : ℤ) ∣ P ↔ P.map (Int.castRingHom (ZMod p)) = 0 := by
  rw [C_dvd_iff_dvd_coeff]
  simp only [Polynomial.ext_iff, coeff_map, coeff_zero,
    Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem Q_reduce (p n : ℕ) (hn : 0 < n) (hp : 0 < p) (hpn : p ∣ n) :
    Q (0 : ZMod p) (n-1) = Q (0 : ZMod p) (p-1) := by
  have hle : p ≤ n := Nat.le_of_dvd hn hpn
  have hb : ((n-p : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hle]
    simp [(ZMod.natCast_eq_zero_iff n p).mpr hpn]
  have hidx : n-1 = (n-p) + (p-1) := (Nat.sub_add_sub_cancel hle hp).symm
  rw [hidx, Q_reset (n-p) (p-1) hb]

private theorem source_prime_support (n : ℕ) (hn : 0 < n) :
    (sourcePolynomial n).IsPrimitive ↔
      ∀ p : ℕ, Nat.Prime p → p ∣ n → Q (0 : ZMod p) (p-1) ≠ 0 := by
  rw [primitive_iff_no_prime]
  constructor
  · intro h p hp hpn hz
    apply h p hp
    rw [C_dvd_iff_zmod, source_Q n hn, Q_map]
    simp only [map_natCast]
    rw [(ZMod.natCast_eq_zero_iff n p).mpr hpn, Q_reduce p n hn hp.pos hpn]
    exact hz
  · intro h p hp hc
    have hpow : (p : ℤ) ∣ (n : ℤ)^(n-1) := by
      have ht := (C_dvd_iff_dvd_coeff (p : ℤ) (sourcePolynomial n)).mp hc (n-1)
      rwa [source_Q n hn, (Q_coeff (n : ℤ) (n-1)).2] at ht
    have hpn : p ∣ n := Int.natCast_dvd_natCast.mp
      ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpow)
    rw [C_dvd_iff_zmod, source_Q n hn, Q_map] at hc
    simp only [map_natCast] at hc
    rw [(ZMod.natCast_eq_zero_iff n p).mpr hpn, Q_reduce p n hn hp.pos hpn] at hc
    exact h p hp hpn hc

private theorem source_divisor_closed {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ∣ n) (h : (sourcePolynomial n).IsPrimitive) :
    (sourcePolynomial d).IsPrimitive := by
  rw [source_prime_support d hd]
  intro p hp hpd
  exact (source_prime_support n hn).mp h p hp (dvd_trans hpd hdn)

private theorem source_one : (sourcePolynomial 1).IsPrimitive := by
  simp [sourcePolynomial]

private theorem source_three_pow (r : ℕ) : (sourcePolynomial (3^r)).IsPrimitive := by
  rw [source_prime_support (3^r) (by positivity)]
  intro p hp hpd
  have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (hp.dvd_of_dvd_pow hpd)
  subst p
  intro hz
  have hc := congrArg (fun P : (ZMod 3)[X] => P.coeff 0) hz
  norm_num [Q] at hc
  exact (by decide : (5 : ZMod 3) ≠ 0) hc
private theorem source_sequence_exists : ∃ a : ℕ → ℕ, IsSourceSequence a := by
  classical
  let s : ℕ → Prop := fun n => n = 0 ∨ 0 < n ∧ (sourcePolynomial n).IsPrimitive
  have hs : (Set.ofPred s).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun r : ℕ => 3^r)
      (Nat.pow_right_injective (by omega : 2 ≤ 3))
    intro r
    exact Or.inr ⟨by positivity, source_three_pow r⟩
  refine ⟨Nat.nth s, ?_, Nat.nth_strictMono hs, ?_⟩
  · exact Nat.nth_zero_of_zero (Or.inl rfl)
  · intro n
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hpos : 0 < Nat.nth s k := by
        have hm := Nat.nth_strictMono hs hk
        simpa [Nat.nth_zero_of_zero (show s 0 from Or.inl rfl)] using hm
      have hm := Nat.nth_mem_of_infinite hs k
      exact ⟨hpos, (hm.resolve_left (Nat.ne_of_gt hpos)).2⟩
    · intro hn
      have hm : n ∈ Set.range (Nat.nth s) := by
        rw [Nat.range_nth_of_infinite hs]
        exact Or.inr hn
      obtain ⟨k, hk⟩ := hm
      refine ⟨k, ?_, hk⟩
      by_contra hnot
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
      subst k
      rw [Nat.nth_zero_of_zero (show s 0 from Or.inl rfl)] at hk
      omega

private theorem source_sequence_one {a : ℕ → ℕ} (ha : IsSourceSequence a) : a 1 = 1 := by
  obtain ⟨k, hk, hka⟩ := (ha.2.2 1).mpr ⟨by omega, source_one⟩
  have hle : a 1 ≤ a k := ha.2.1.monotone (by omega)
  have hpos : 0 < a 1 := by simpa [ha.1] using ha.2.1 (by omega : 0 < 1)
  omega

theorem result : claim := by
  refine ⟨source_sequence_exists, ?_⟩
  intro a ha k hk hn hnp
  have hnmem := (ha.2.2 (a k)).mp ⟨k, hk, rfl⟩
  obtain ⟨p, hprime, hpd⟩ := Nat.exists_prime_and_dvd (by omega : a k ≠ 1)
  obtain ⟨q, hpq⟩ := hpd
  have hp : 1 < p := hprime.one_lt
  have hq : 1 < q := by
    by_contra h
    have hq0 : q ≠ 0 := by intro he; simp [he] at hpq; omega
    have hq1 : q = 1 := by omega
    apply hnp
    simpa [hpq, hq1] using hprime
  have hpd : p ∣ a k := ⟨q, hpq⟩
  have hqd : q ∣ a k := ⟨p, by rw [mul_comm]; exact hpq⟩
  have hpmem := source_divisor_closed hnmem.1 (by omega : 0 < p) hpd hnmem.2
  have hqmem := source_divisor_closed hnmem.1 (by omega : 0 < q) hqd hnmem.2
  obtain ⟨i, hi, hai⟩ := (ha.2.2 p).mpr ⟨by omega, hpmem⟩
  obtain ⟨j, hj, haj⟩ := (ha.2.2 q).mpr ⟨by omega, hqmem⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · have he := source_sequence_one ha
    by_contra h
    have : i = 1 := by omega
    subst i
    omega
  · have he := source_sequence_one ha
    by_contra h
    have : j = 1 := by omega
    subst j
    omega
  · rw [hai, haj]
    exact hpq


end D5.S3.Arith.PolynomialValues.KurkovA248667CompositeFactorization
