/- GID: D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BourasA363102PrimeMultiplicity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime values occur twice or three times in Bouras A363102. -/

/-
admission_basis: open-problem-resolution (#18627; Proved)
escape_witness: BourasShared.denominator_formula_aux (live recurrence and factorial identity).
Direct D5 dependency: BourasA363347PrimeMultiplicity (same delivery).
No D5 dependency was frozen on the protected baseline.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21990
public theorem BourasA363102.result; proof_shape: content; escape_witness: BourasShared.denominator_formula_aux; consumers:
settling result.
The continued-fraction definitions retain the source's right fold and rational denominator.
The prime quantifier ranges over values that occur at indices at least three.
Set.ncard is applied after the occurrence set is exhibited as a finite pair or triple.
The shared helpers are public exactly where the second delivered module uses them.
-/

import D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity

open D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity

/-! Prime occurrence counts for rational continued-fraction denominators. -/

namespace D5.S3.Arith.Congruence.BourasA363102PrimeMultiplicity

set_option autoImplicit false

namespace BourasA363102

open BourasA356360

/-- A363102: the denominator of `1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))`, `n ≥ 3`. -/
def a (n : ℕ) : ℕ := (K n (-2)).den

/-- Conjecture 2 of A363102 ("All prime numbers appear either twice ... or three times."): every
prime value is taken at exactly two or exactly three indices `n ≥ 3`. -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → (∃ n : ℕ, 3 ≤ n ∧ a n = p) →
    {n : ℕ | 3 ≤ n ∧ a n = p}.ncard = 2 ∨ {n : ℕ | 3 ≤ n ∧ a n = p}.ncard = 3

end BourasA363102

namespace BourasA363102
open BourasPolynomials BourasPrimeValues BourasRoots

theorem result : claim := by
  intro p hp hex
  obtain ⟨n0, hn0, ha0⟩ := hex
  have h0 := U_prime_constraints n0 p hn0 hp ha0
  have hz : (n0 : ZMod p) ^ 2 = 2 := by
    have hzero := (ZMod.natCast_eq_zero_iff (U n0) p).mpr h0.2.1
    rw [cast_U n0 p hn0] at hzero
    exact sub_eq_zero.mp hzero
  obtain ⟨r, q, hr, hq, hrp, hqp, hrq, hsum, hrroot⟩ :=
    square_residue_pair p 0 2 hp (Or.inl ⟨rfl, rfl, h0.1⟩) (n0 : ZMod p) hz
  have hfiber := root_fiber_eq_pair p 0 r q hp hr hq hrp hqp hsum
  simp only [Nat.add_zero] at hfiber hrroot hrp hqp
  have hbelow : {n : ℕ | 3 ≤ n ∧ n < p ∧ a n = p} = {r, q} := by
    ext n
    constructor
    · rintro ⟨hn, hnp, ha⟩
      have hc := U_prime_constraints n p hn hp ha
      have hz : (n : ZMod p) ^ 2 = 2 := by
        have he := (ZMod.natCast_eq_zero_iff (U n) p).mpr hc.2.1
        rw [cast_U n p hn] at he
        exact sub_eq_zero.mp he
      rw [← hfiber]
      exact ⟨hn, hnp, hz.trans hrroot.symm⟩
    · intro he
      rw [← hfiber] at he
      obtain ⟨hn, hnp, hz⟩ := he
      refine ⟨hn, hnp, ?_⟩
      apply U_prime_of_root n p hn hp hnp
      apply (ZMod.natCast_eq_zero_iff (U n) p).mp
      rw [cast_U n p hn, hz.trans hrroot]
      norm_num
  by_cases hextra : ∃ t : ℕ, 3 ≤ t ∧ p ≤ t ∧ a t = p
  · obtain ⟨t, ht, hpt, hat⟩ := hextra
    have htP : t ^ 2 = 2 * p ^ 2 + 2 :=
      (U_prime_constraints t p ht hp hat).2.2.resolve_left (by omega)
    have huniq : ∀ n : ℕ, 3 ≤ n → p ≤ n → a n = p → n = t := by
      intro n hn hpn ha
      have hnP : n ^ 2 = 2 * p ^ 2 + 2 :=
        (U_prime_constraints n p hn hp ha).2.2.resolve_left (by omega)
      nlinarith
    have hset : {n : ℕ | 3 ≤ n ∧ a n = p} = {r, q, t} := by
      ext n
      constructor
      · rintro ⟨hn, ha⟩
        by_cases hnp : n < p
        · have he : n ∈ ({r, q} : Set ℕ) := by rw [← hbelow]; exact ⟨hn, hnp, ha⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he ⊢
          tauto
        · have he := huniq n hn (by omega) ha
          simp only [he, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (hnr | hnq | hnt)
        · rw [hnr]
          have he : r ∈ ({r, q} : Set ℕ) := by exact Set.mem_insert r {q}
          rw [← hbelow] at he
          exact ⟨he.1, he.2.2⟩
        · rw [hnq]
          have he : q ∈ ({r, q} : Set ℕ) := by exact Set.mem_insert_of_mem r rfl
          rw [← hbelow] at he
          exact ⟨he.1, he.2.2⟩
        · rw [hnt]
          exact ⟨ht, hat⟩
    right
    exact Set.ncard_eq_three.mpr ⟨r, q, t, hrq, by omega, by omega, hset⟩
  · left
    have hset : {n : ℕ | 3 ≤ n ∧ a n = p} = {r, q} := by
      ext n
      constructor
      · rintro ⟨hn, ha⟩
        have hnp : n < p := by
          by_contra h
          exact hextra ⟨n, hn, by omega, ha⟩
        rw [← hbelow]
        exact ⟨hn, hnp, ha⟩
      · intro he
        rw [← hbelow] at he
        exact ⟨he.1, he.2.2⟩
    rw [hset]
    exact Set.ncard_pair hrq

end BourasA363102

end D5.S3.Arith.Congruence.BourasA363102PrimeMultiplicity
