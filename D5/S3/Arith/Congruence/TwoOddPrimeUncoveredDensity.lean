/- GID: D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-odd-prime congruence families leave at least one eighth uncovered. -/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.Prime

open scoped BigOperators

namespace D5.S3.Arith.Congruence.TwoOddPrimeUncoveredDensity

open Finset

private theorem residue_fibre_count_range {L d r : ℕ} (hd : d ∣ L) (hd0 : 0 < d) :
    #{x ∈ Finset.range L | x % d = r % d} = L / d := by
  rw [← Nat.count_eq_card_filter_range]
  change L.count (· ≡ r [MOD d]) = L / d
  rw [Nat.count_modEq_card L hd0 r]
  rw [Nat.mod_eq_zero_of_dvd hd]
  simp

private theorem residue_fibre_count {L d r : ℕ} (hd : d ∣ L) (hd0 : 0 < d) :
    #{x : Fin L | x.val % d = r % d} = L / d := by
  rw [← residue_fibre_count_range hd hd0]
  apply Finset.card_bij (fun x _ ↦ x.val)
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨x.isLt, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact Fin.ext hxy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, Finset.mem_range.mp hy'.1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩

private theorem covered_card_le_sum_fibres {L : ℕ} (D : Finset ℕ) (a : ℕ → ℕ)
    (hdvd : ∀ d ∈ D, d ∣ L) (hdpos : ∀ d ∈ D, 0 < d) :
    #{x : Fin L | ∃ d ∈ D, x.val % d = a d % d} ≤ ∑ d ∈ D, L / d := by
  let fibre : ℕ → Finset (Fin L) :=
    fun d ↦ Finset.univ.filter fun x ↦ x.val % d = a d % d
  have hcovered :
      (Finset.univ.filter fun x : Fin L ↦ ∃ d ∈ D, x.val % d = a d % d) =
        D.biUnion fibre := by
    ext x
    simp [fibre]
  rw [hcovered]
  calc
    #(D.biUnion fibre) ≤ ∑ d ∈ D, #(fibre d) := Finset.card_biUnion_le
    _ = ∑ d ∈ D, L / d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact residue_fibre_count (hdvd d hd) (hdpos d hd)

private theorem two_mul_geom_sum_le_three_mul_pow {p A : ℕ} (hp : 3 ≤ p) :
    2 * (∑ i ∈ Finset.range (A + 1), p ^ i) ≤ 3 * p ^ A := by
  induction A with
  | zero => simp
  | succ A ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [Nat.mul_le_mul_right (p ^ A) hp]

private theorem four_mul_geom_sum_le_five_mul_pow {q B : ℕ} (hq : 5 ≤ q) :
    4 * (∑ j ∈ Finset.range (B + 1), q ^ j) ≤ 5 * q ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [Nat.mul_le_mul_right (q ^ B) hq]

private theorem eight_mul_sum_divisors_le_fifteen_mul {p q A B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q) :
    8 * (∑ d ∈ (p ^ A * q ^ B).divisors, d) ≤ 15 * (p ^ A * q ^ B) := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  have hcop := Nat.coprime_pow_primes A B hp hq hpq
  rw [hcop.sum_divisors_mul, Nat.sum_divisors_prime_pow hp,
    Nat.sum_divisors_prime_pow hq]
  rcases lt_or_gt_of_ne hpq with hpqlt | hqplt
  · have hq5 : 5 ≤ q := by
      have hq4 : q ≠ 4 := by
        intro h
        subst q
        norm_num at hq
      omega
    have h1 := two_mul_geom_sum_le_three_mul_pow (A := A) hp3
    have h2 := four_mul_geom_sum_le_five_mul_pow (B := B) hq5
    nlinarith [Nat.mul_le_mul h1 h2]
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro h
        subst p
        norm_num at hp
      omega
    have h1 := four_mul_geom_sum_le_five_mul_pow (B := A) hp5
    have h2 := two_mul_geom_sum_le_three_mul_pow (A := B) hq3
    nlinarith [Nat.mul_le_mul h1 h2]

/-- Distinct congruences whose moduli are nontrivial divisors of a number supported on two
odd primes leave at least one eighth of the residue classes uncovered. -/
theorem two_odd_prime_uncovered_density
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hpq : p ≠ q) (A B : ℕ) (D : Finset ℕ) (a : ℕ → ℕ)
    (hmoduli : ∀ d ∈ D, 1 < d ∧ d ∣ p ^ A * q ^ B) :
    p ^ A * q ^ B ≤
      8 * #{x : Fin (p ^ A * q ^ B) |
        ∀ d ∈ D, x.val % d ≠ a d % d} := by
  let L := p ^ A * q ^ B
  have hL0 : L ≠ 0 := by
    dsimp [L]
    exact Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have hcovered :
      #{x : Fin L | ∃ d ∈ D, x.val % d = a d % d} ≤ ∑ d ∈ D, L / d := by
    apply covered_card_le_sum_fibres D a
    · intro d hd
      simpa [L] using (hmoduli d hd).2
    · intro d hd
      exact (hmoduli d hd).1.trans' Nat.zero_lt_one
  have hDsub : D ⊆ L.divisors.erase 1 := by
    intro d hd
    rw [Finset.mem_erase]
    exact ⟨(hmoduli d hd).1.ne',
      Nat.mem_divisors.mpr ⟨by simpa [L] using (hmoduli d hd).2, hL0⟩⟩
  have hsumD : (∑ d ∈ D, L / d) ≤ ∑ d ∈ L.divisors.erase 1, L / d :=
    Finset.sum_le_sum_of_subset hDsub
  have hdivisor := eight_mul_sum_divisors_le_fifteen_mul
    (A := A) (B := B) hp hq hpodd hqodd hpq
  have hinversion :
      (∑ d ∈ L.divisors, L / d) = ∑ d ∈ L.divisors, d := by
    simpa using Nat.sum_div_divisors L (fun d ↦ d)
  have hall : 8 * (∑ d ∈ L.divisors, L / d) ≤ 15 * L := by
    rw [hinversion]
    simpa [L] using hdivisor
  have hone : 1 ∈ L.divisors := Nat.one_mem_divisors.mpr hL0
  have herase_add :
      L + (∑ d ∈ L.divisors.erase 1, L / d) = ∑ d ∈ L.divisors, L / d := by
    simpa using (Finset.add_sum_erase L.divisors (fun d ↦ L / d) hone)
  have herase : 8 * (∑ d ∈ L.divisors.erase 1, L / d) ≤ 7 * L := by
    nlinarith
  have hcovered7 :
      8 * #{x : Fin L | ∃ d ∈ D, x.val % d = a d % d} ≤ 7 * L :=
    (Nat.mul_le_mul_left 8 (hcovered.trans hsumD)).trans herase
  have hpartition :
      #{x : Fin L | ∃ d ∈ D, x.val % d = a d % d} +
        #{x : Fin L | ∀ d ∈ D, x.val % d ≠ a d % d} = L := by
    simpa only [Finset.card_univ, Fintype.card_fin, not_exists, not_and,
      Decidable.not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin L)))
        (p := fun x ↦ ∃ d ∈ D, x.val % d = a d % d))
  change L ≤ 8 * #{x : Fin L | ∀ d ∈ D, x.val % d ≠ a d % d}
  nlinarith

/-- Consequently, no such family of residue classes covers all residues modulo the product. -/
theorem two_odd_prime_residue_classes_do_not_cover
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hpq : p ≠ q) (A B : ℕ) (D : Finset ℕ) (a : ℕ → ℕ)
    (hmoduli : ∀ d ∈ D, 1 < d ∧ d ∣ p ^ A * q ^ B) :
    ¬ (∀ x : Fin (p ^ A * q ^ B),
      ∃ d ∈ D, x.val % d = a d % d) := by
  intro hcover
  have hdensity :=
    two_odd_prime_uncovered_density p q hp hq hpodd hqodd hpq A B D a hmoduli
  have hempty :
      (Finset.univ.filter fun x : Fin (p ^ A * q ^ B) ↦
        ∀ d ∈ D, x.val % d ≠ a d % d) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hunc
    obtain ⟨d, hd, heq⟩ := hcover x
    exact (hunc d hd) heq
  rw [hempty] at hdensity
  simp only [Finset.card_empty, mul_zero] at hdensity
  have hpositive : 0 < p ^ A * q ^ B :=
    Nat.mul_pos (pow_pos hp.pos A) (pow_pos hq.pos B)
  omega

example : ∀ d ∈ ({3, 5, 15} : Finset ℕ), 1 < d ∧ d ∣ 3 ^ 1 * 5 ^ 1 := by
  decide

example : Nonempty (Fin (3 ^ 1 * 5 ^ 1)) := ⟨0⟩

example :
    #{x : Fin 15 | x.val % 3 ≠ 0 ∧ x.val % 5 ≠ 0 ∧ x.val % 15 ≠ 0} = 8 := by
  decide

#print axioms two_odd_prime_uncovered_density
#print axioms two_odd_prime_residue_classes_do_not_cover

end D5.S3.Arith.Congruence.TwoOddPrimeUncoveredDensity
