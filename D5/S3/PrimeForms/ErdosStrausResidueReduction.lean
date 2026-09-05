/- GID: D5/S3/PrimeForms/ErdosStrausResidueReduction
   generality: I
   mirror-B: D5/B/S3/PrimeForms/ErdosStrausResidueReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reciprocal and integral forms bridge a modulo 24 residue reduction. -/

import Mathlib.Tactic
import D5.S3.Arith.Congruence.ErdosStrausModularWitnesses

namespace D5.S3.PrimeForms.ErdosStrausResidueReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.Congruence.ErdosStrausModularWitnesses

/-- The division-free form of the Erdos--Straus equation. -/
def ESSolvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

private theorem rational_eq_iff_integer_eq {n x y z : ℕ}
    (hn : n ≠ 0) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((4 : ℚ) / (n : ℚ) =
        1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      4 * x * y * z = n * (x * y + x * z + y * z) := by
  constructor
  · intro h
    have hq :
        (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
      field_simp [hn, Nat.ne_of_gt hx, Nat.ne_of_gt hy, Nat.ne_of_gt hz] at h ⊢
      nlinarith
    exact_mod_cast hq
  · intro h
    have hq :
        (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
      exact_mod_cast h
    field_simp [hn, Nat.ne_of_gt hx, Nat.ne_of_gt hy, Nat.ne_of_gt hz] at hq ⊢
    nlinarith

/-- Integer solvability is equivalent to the rational reciprocal form, and
positive multiples inherit solvability by scaling every denominator. -/
theorem es_integer_reciprocal_scaling :
    (∀ n : ℕ, ESSolvable n ↔
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (n : ℚ) =
          1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ∧
    (∀ {n m : ℕ}, ESSolvable n → 1 ≤ m → ESSolvable (n * m)) := by
  constructor
  · intro n
    constructor
    · rintro ⟨x, y, z, hx, hy, hz, hxyz⟩
      have hn : n ≠ 0 := by
        intro hn
        subst n
        simp only [Nat.zero_mul] at hxyz
        have hpos : 0 < 4 * x * y * z := by positivity
        omega
      exact ⟨x, y, z, hx, hy, hz,
        (rational_eq_iff_integer_eq hn hx hy hz).2 hxyz⟩
    · rintro ⟨x, y, z, hx, hy, hz, hreciprocal⟩
      have hn : n ≠ 0 := by
        intro hn
        subst n
        norm_num at hreciprocal
        have hpositive :
            (0 : ℚ) < 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
          positivity
        have hzero :
            1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) = 0 := by
          simpa only [one_div] using hreciprocal.symm
        exact ne_of_gt hpositive hzero
      exact ⟨x, y, z, hx, hy, hz,
        (rational_eq_iff_integer_eq hn hx hy hz).1 hreciprocal⟩
  · intro n m hsolvable hm
    rcases hsolvable with ⟨x, y, z, hx, hy, hz, hxyz⟩
    refine ⟨x * m, y * m, z * m, Nat.mul_pos hx (by omega),
      Nat.mul_pos hy (by omega), Nat.mul_pos hz (by omega), ?_⟩
    calc
      4 * (x * m) * (y * m) * (z * m) = m ^ 3 * (4 * x * y * z) := by ring
      _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hxyz]
      _ = (n * m) * ((x * m) * (y * m) + (x * m) * (z * m) +
            (y * m) * (z * m)) := by ring

private theorem rational_solution_of_witness {n x y z : ℕ}
    (h : IsErdosStrausWitness n x y z) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (n : ℚ) =
        1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) :=
  ⟨x, y, z, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem residue_dispatch_24 (n : ℕ) (h : n % 24 ≠ 1) :
    n % 2 = 0 ∨ n % 3 = 0 ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5 := by
  omega

private theorem es_of_not_one_mod_24 (n : ℕ) (hn : 2 ≤ n) (h : n % 24 ≠ 1) :
    ESSolvable n := by
  obtain ⟨familyTwo, familyThree, familyThreeTwo, familyFourThree,
      familyEightFive, _, _, _⟩ := erdos_straus_modular_witnesses
  have fromWitness : ∀ {a b c d : ℕ}, IsErdosStrausWitness a b c d → ESSolvable a := by
    intro a b c d hwitness
    exact (es_integer_reciprocal_scaling.1 a).2
      (rational_solution_of_witness hwitness)
  rcases residue_dispatch_24 n h with hTwo | hThree | hThreeTwo | hFourThree | hEightFive
  · obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hTwo
    have hqPositive : 1 ≤ q := by omega
    rw [hq]
    exact es_integer_reciprocal_scaling.2
      (fromWitness (familyTwo 1 (by norm_num))) hqPositive
  · obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hThree
    have hqPositive : 0 < q := by omega
    rw [hq]
    exact fromWitness (familyThree q hqPositive)
  · let k := n / 3
    have hnForm : n = 3 * k + 2 := by
      have hdivision := Nat.mod_add_div n 3
      omega
    rw [hnForm]
    exact fromWitness (familyThreeTwo k)
  · let k := n / 4
    have hnForm : n = 4 * k + 3 := by
      have hdivision := Nat.mod_add_div n 4
      omega
    rw [hnForm]
    exact fromWitness (familyFourThree k)
  · let k := n / 8
    have hnForm : n = 8 * k + 5 := by
      have hdivision := Nat.mod_add_div n 8
      omega
    rw [hnForm]
    exact fromWitness (familyEightFive k)

private theorem residue_one_excluded :
    ∀ n : ℕ, n % 24 = 1 →
      ¬ (2 ∣ n ∨ 3 ∣ n ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5) := by
  omega

/-- Every residue class modulo 24 except one is solved by the five frozen
families; residue one belongs to none of those families. -/
theorem es_mod_24_reduction :
    (∀ n : ℕ, 2 ≤ n → n % 24 ≠ 1 → ESSolvable n) ∧
    (∀ n : ℕ, n % 24 = 1 →
      ¬ (2 ∣ n ∨ 3 ∣ n ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5)) := by
  exact ⟨es_of_not_one_mod_24, residue_one_excluded⟩

-- Step-6 witnesses: both quantified domains and the reduction premise are inhabited.
example : ∃ n : ℕ, ESSolvable n := by
  refine ⟨2, (es_integer_reciprocal_scaling.1 2).2 ?_⟩
  exact rational_solution_of_witness
    erdos_straus_modular_witnesses.2.2.2.2.2.1

example : ∃ n : ℕ, 2 ≤ n ∧ n % 24 ≠ 1 := ⟨2, by norm_num, by norm_num⟩

#print axioms es_integer_reciprocal_scaling
#print axioms es_mod_24_reduction

end D5.S3.PrimeForms.ErdosStrausResidueReduction
