/- GID: D5/S3/PrimeForms/ErdosStrausResidueReduction
   generality: I
   mirror-B: D5/B/S3/PrimeForms/ErdosStrausResidueReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Erdos-Straus equation has equivalent reciprocal and integral forms, is stable under positive scaling, admits five explicit congruence families with witnesses at 2, 5, and 7, and is therefore solvable in every residue class modulo 24 except 1; residue 1 belongs to none of those five families. -/

import Mathlib

namespace ErdosStrausResidueReduction

/-- A division-free form of the Erdos-Straus equation. -/
def ESSolvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

private theorem rational_eq_iff_integer_eq {n x y z : ℕ}
    (hn : n ≠ 0) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((4 : ℚ) / n = 1 / x + 1 / y + 1 / z) ↔
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

private theorem es_scale {n m : ℕ} (h : ESSolvable n) (hm : 1 ≤ m) :
    ESSolvable (n * m) := by
  rcases h with ⟨x, y, z, hx, hy, hz, hxyz⟩
  refine ⟨x * m, y * m, z * m, Nat.mul_pos hx (by omega),
    Nat.mul_pos hy (by omega), Nat.mul_pos hz (by omega), ?_⟩
  calc
    4 * (x * m) * (y * m) * (z * m) = m ^ 3 * (4 * x * y * z) := by ring
    _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hxyz]
    _ = (n * m) * ((x * m) * (y * m) + (x * m) * (z * m) +
          (y * m) * (z * m)) := by ring

private theorem es_two : ESSolvable 2 := by
  exact ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

private theorem es_three : ESSolvable 3 := by
  exact ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

private theorem es_five : ESSolvable 5 := by
  exact ⟨2, 4, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩

private theorem es_seven : ESSolvable 7 := by
  exact ⟨2, 28, 28, by norm_num, by norm_num, by norm_num, by norm_num⟩

private theorem es_of_mod_two {n : ℕ} (hmod : n % 2 = 0) (hn : 1 ≤ n) :
    ESSolvable n := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hkpos : 1 ≤ k := by omega
  rw [hk]
  exact es_scale es_two hkpos

private theorem es_of_mod_three_zero {n : ℕ} (hmod : n % 3 = 0) (hn : 1 ≤ n) :
    ESSolvable n := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hkpos : 1 ≤ k := by omega
  rw [hk]
  exact es_scale es_three hkpos

private theorem es_of_mod_three_two {n : ℕ} (hmod : n % 3 = 2) (_hn : 1 ≤ n) :
    ESSolvable n := by
  let k := n / 3
  have hnform : n = 3 * k + 2 := by
    have hdiv := Nat.mod_add_div n 3
    omega
  rw [hnform]
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega,
    by positivity, ?_⟩
  ring

private theorem es_of_mod_four_three {n : ℕ} (hmod : n % 4 = 3) (_hn : 1 ≤ n) :
    ESSolvable n := by
  let k := n / 4
  have hnform : n = 4 * k + 3 := by
    have hdiv := Nat.mod_add_div n 4
    omega
  rw [hnform]
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1),
    2 * (4 * k + 3) * (k + 1), by omega, by positivity, by positivity, ?_⟩
  ring

private theorem es_of_mod_eight_five {n : ℕ} (hmod : n % 8 = 5) (_hn : 1 ≤ n) :
    ESSolvable n := by
  let k := n / 8
  have hnform : n = 8 * k + 5 := by
    have hdiv := Nat.mod_add_div n 8
    omega
  rw [hnform]
  refine ⟨2 * (k + 1), (8 * k + 5) * (k + 1),
    2 * (8 * k + 5) * (k + 1), by omega, by positivity, by positivity, ?_⟩
  ring

private theorem residue_dispatch_24 (n : ℕ) (h : n % 24 ≠ 1) :
    n % 2 = 0 ∨ n % 3 = 0 ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5 := by
  omega

private theorem es_of_not_one_mod_24 (n : ℕ) (hn : 2 ≤ n) (h : n % 24 ≠ 1) :
    ESSolvable n := by
  rcases residue_dispatch_24 n h with h2 | h3 | h32 | h43 | h85
  · exact es_of_mod_two h2 (by omega)
  · exact es_of_mod_three_zero h3 (by omega)
  · exact es_of_mod_three_two h32 (by omega)
  · exact es_of_mod_four_three h43 (by omega)
  · exact es_of_mod_eight_five h85 (by omega)

private theorem one_not_covered_by_families :
    ¬ (1 % 2 = 0 ∨ 1 % 3 = 0 ∨ 1 % 3 = 2 ∨ 1 % 4 = 3 ∨ 1 % 8 = 5) := by
  norm_num

/-- The reciprocal equation, integer equation, and positive scaling law agree. -/
theorem es_integer_reciprocal_scaling :
    (∀ {n x y z : ℕ}, n ≠ 0 → 0 < x → 0 < y → 0 < z →
      (((4 : ℚ) / n = 1 / x + 1 / y + 1 / z) ↔
        4 * x * y * z = n * (x * y + x * z + y * z))) ∧
    (∀ {n m : ℕ}, ESSolvable n → 1 ≤ m → ESSolvable (n * m)) := by
  exact ⟨fun hn hx hy hz => rational_eq_iff_integer_eq hn hx hy hz,
    fun h hm => es_scale h hm⟩

/-- Five explicit residue families solve the equation, including witnesses at 2, 5, and 7. -/
theorem es_explicit_residue_families :
    (∀ n : ℕ, n % 2 = 0 → 1 ≤ n → ESSolvable n) ∧
    (∀ n : ℕ, n % 3 = 0 → 1 ≤ n → ESSolvable n) ∧
    (∀ n : ℕ, n % 3 = 2 → 1 ≤ n → ESSolvable n) ∧
    (∀ n : ℕ, n % 4 = 3 → 1 ≤ n → ESSolvable n) ∧
    (∀ n : ℕ, n % 8 = 5 → 1 ≤ n → ESSolvable n) ∧
    ESSolvable 2 ∧ ESSolvable 5 ∧ ESSolvable 7 := by
  exact ⟨fun _ hmod hn => es_of_mod_two hmod hn,
    fun _ hmod hn => es_of_mod_three_zero hmod hn,
    fun _ hmod hn => es_of_mod_three_two hmod hn,
    fun _ hmod hn => es_of_mod_four_three hmod hn,
    fun _ hmod hn => es_of_mod_eight_five hmod hn,
    es_two, es_five, es_seven⟩

/-- All classes modulo 24 except 1 are solved, while residue 1 is in none of the five families. -/
theorem es_mod_24_reduction :
    (∀ n : ℕ, 2 ≤ n → n % 24 ≠ 1 → ESSolvable n) ∧
    ¬ (1 % 2 = 0 ∨ 1 % 3 = 0 ∨ 1 % 3 = 2 ∨ 1 % 4 = 3 ∨ 1 % 8 = 5) := by
  exact ⟨es_of_not_one_mod_24, one_not_covered_by_families⟩

-- Step-6 witnesses: the quantified domain and the reduction hypotheses are inhabited.
example : ∃ n : ℕ, ESSolvable n := ⟨2, es_two⟩

example : ∃ n : ℕ, 2 ≤ n ∧ n % 24 ≠ 1 := ⟨2, by norm_num, by norm_num⟩

#print axioms es_integer_reciprocal_scaling
#print axioms es_explicit_residue_families
#print axioms es_mod_24_reduction

end ErdosStrausResidueReduction
