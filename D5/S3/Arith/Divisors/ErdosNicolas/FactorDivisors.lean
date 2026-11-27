/- GID: D5/S3/Arith/Divisors/ErdosNicolas/FactorDivisors
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main00.chunk_checked
   digest: Complete divisor enumeration from certified prime and exponent lists. -/

import D5.S3.Arith.Divisors.ErdosNicolas.DivisorChecker
import Mathlib.Data.Finset.NatDivisors

/-! Enumeration uses prime powers rather than scanning up to the represented integer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open scoped Pointwise

/-- Cartesian enumeration of the prime-power coordinates of a divisor. -/
def factorDivisors : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, a) :: fs =>
      (List.range (a + 1)).flatMap fun i => (factorDivisors fs).map (p ^ i * ·)

/-- The enumeration has the expected product length, independently of primality. -/
theorem factorDivisors_length (fs : List (ℕ × ℕ)) :
    (factorDivisors fs).length = factorTau fs := by
  induction fs with
  | nil => simp [factorDivisors, factorTau]
  | cons v fs ih =>
    rcases v with ⟨p, a⟩
    simp [factorDivisors, factorTau, List.length_flatMap, List.map_const', ih]

/-- Certified prime powers enumerate the complete divisor set. -/
theorem factorDivisors_toFinset {fs : List (ℕ × ℕ)} (h : checkFactors fs = true) :
    (factorDivisors fs).toFinset = (factorValue fs).divisors := by
  induction fs with
  | nil => simp [factorDivisors, factorValue]
  | cons v fs ih =>
    rcases v with ⟨p, a⟩
    simp only [checkFactors, Bool.and_eq_true, decide_eq_true_eq] at h
    change ((List.range (a + 1)).flatMap fun i =>
      (factorDivisors fs).map (p ^ i * ·)).toFinset =
      (p ^ a * factorValue fs).divisors
    rw [Nat.divisors_mul]
    ext d
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_range, List.mem_map,
      Finset.mem_mul]
    constructor
    · rintro ⟨i, hi, e, he, rfl⟩
      refine ⟨p ^ i, (Nat.mem_divisors_prime_pow h.1.1 a).mpr ⟨i, by omega, rfl⟩,
        e, ?_, rfl⟩
      rw [← ih h.2]
      exact List.mem_toFinset.mpr he
    · rintro ⟨x, hx, e, he, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.mem_divisors_prime_pow h.1.1 a).mp hx
      refine ⟨i, by omega, e, ?_, rfl⟩
      apply List.mem_toFinset.mp
      rwa [ih h.2]

/-- Equal cardinality rules out repetitions in the Cartesian enumeration. -/
theorem factorDivisors_nodup {fs : List (ℕ × ℕ)} (h : checkFactors fs = true) :
    (factorDivisors fs).Nodup := by
  apply Multiset.coe_nodup.mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (factorDivisors fs).toFinset.card = (factorDivisors fs).length
  rw [factorDivisors_toFinset h, factorDivisors_length]
  exact (checkFactors_sound h).2

/-- Concatenated prime coordinates represent the product of the represented integers. -/
private theorem factorValue_append (fs gs : List (ℕ × ℕ)) :
    factorValue (fs ++ gs) = factorValue fs * factorValue gs := by
  induction fs with
  | nil => simp [factorValue]
  | cons v fs ih => rcases v with ⟨p, a⟩; simp [factorValue, ih, mul_assoc]

/-- Predicted divisor counts multiply under concatenation. -/
theorem factorTau_append (fs gs : List (ℕ × ℕ)) :
    factorTau (fs ++ gs) = factorTau fs * factorTau gs := by
  induction fs with
  | nil => simp [factorTau]
  | cons v fs ih => rcases v with ⟨p, a⟩; simp [factorTau, ih, mul_assoc]

/-- A full factor certificate also certifies each side of any prefix split. -/
theorem checkFactors_append {fs gs : List (ℕ × ℕ)}
    (h : checkFactors (fs ++ gs) = true) :
    checkFactors fs = true ∧ checkFactors gs = true := by
  induction fs with
  | nil => exact ⟨rfl, h⟩
  | cons v fs ih =>
    rcases v with ⟨p, a⟩
    simp only [List.cons_append, checkFactors, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hf, hg⟩ := ih h.2
    refine ⟨?_, hg⟩
    simp only [checkFactors, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h.1.1, ?_⟩, hf⟩
    intro hd
    apply h.1.2
    rw [factorValue_append]
    exact dvd_mul_of_dvd_left hd _

/-- A prefix and suffix Cartesian product is complete and has no repeated divisors. -/
theorem factorDivisors_products_sound {fs gs : List (ℕ × ℕ)}
    (h : checkFactors (fs ++ gs) = true) :
    let ds := (factorDivisors gs).flatMap fun e => (factorDivisors fs).map (e * ·)
    ds.Nodup ∧ ds.toFinset = (factorValue (fs ++ gs)).divisors ∧
      ds.length = factorTau (fs ++ gs) := by
  obtain ⟨hf, hg⟩ := checkFactors_append h
  dsimp only
  have he : ((factorDivisors gs).flatMap fun e =>
      (factorDivisors fs).map (e * ·)).toFinset = (factorValue (fs ++ gs)).divisors := by
    rw [factorValue_append, Nat.divisors_mul]
    ext d
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, Finset.mem_mul]
    constructor
    · rintro ⟨e, he, x, hx, hd⟩
      have hx' : x ∈ (factorValue fs).divisors := by
        rw [← factorDivisors_toFinset hf]
        exact List.mem_toFinset.mpr hx
      have he' : e ∈ (factorValue gs).divisors := by
        rw [← factorDivisors_toFinset hg]
        exact List.mem_toFinset.mpr he
      exact ⟨x, hx', e, he', by simpa only [mul_comm] using hd⟩
    · rintro ⟨x, hx, e, he, hd⟩
      have hx' : x ∈ factorDivisors fs := by
        apply List.mem_toFinset.mp
        rwa [factorDivisors_toFinset hf]
      have he' : e ∈ factorDivisors gs := by
        apply List.mem_toFinset.mp
        rwa [factorDivisors_toFinset hg]
      exact ⟨e, he', x, hx', by simpa only [mul_comm] using hd⟩
  have hl : ((factorDivisors gs).flatMap fun e =>
      (factorDivisors fs).map (e * ·)).length = factorTau (fs ++ gs) := by
    simp [List.length_flatMap, List.map_const', factorDivisors_length,
      factorTau_append, mul_comm]
  refine ⟨?_, he, hl⟩
  apply Multiset.coe_nodup.mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change ((factorDivisors gs).flatMap fun e =>
    (factorDivisors fs).map (e * ·)).toFinset.card =
      ((factorDivisors gs).flatMap fun e => (factorDivisors fs).map (e * ·)).length
  rw [he, hl]
  exact (checkFactors_sound h).2

#print axioms factorDivisors_length
#print axioms factorDivisors_toFinset
#print axioms factorDivisors_nodup
#print axioms factorDivisors_products_sound

end D5.S3.Arith.ErdosNicolas
