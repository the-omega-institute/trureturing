/- GID: D5/S3/ArithSums/SpeziaA320043PrimeRowCriterion
   generality: I
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043PrimeRowCriterion
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For prime p≥5, A320043 a(p-1) is a square exactly when p^2-12y^2=1 is solvable. -/

import D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation

/-! # The prime-row square criterion for A320043

For `a(n) = ∑_{k=1}^{n} (n+1-k)^2 k / gcd(n+1-k, k)^3` and a prime `p ≥ 5`, the value
`a(p-1)` is a perfect square exactly when `p^2 - 12 y^2 = 1` for some integer `y ≥ 1`, and
then `a(p-1) = (p y)^2`.
-/

namespace D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion

open D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation

private theorem prime_row (p : ℕ) (hp : p.Prime) :
    (12 : ℤ) * (a (p - 1) : ℤ) = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - 1) := by
  have hp2 := hp.two_le
  have he : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hs : a (p - 1) = ∑ k ∈ Finset.Icc 1 (p - 1), (p - k) ^ 2 * k := by
    unfold a
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hcop : Nat.Coprime (p - k) k :=
      (Nat.coprime_sub_self_left (by omega)).mpr
        (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk1 (by omega)))
    rw [hcop.gcd_eq_one]
    simp
  rw [hs, Nat.cast_sum, Finset.mul_sum]
  let F : ℕ → ℤ := fun k =>
    6 * (p : ℤ) ^ 2 * k * (k - 1) -
    4 * p * k * (k - 1) * (2 * k - 1) + 3 * k ^ 2 * (k - 1) ^ 2
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1), (12 : ℤ) * (((p - k) ^ 2 * k : ℕ) : ℤ)) =
        ∑ k ∈ Finset.Icc 1 (p - 1), (F (k + 1) - F k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : k ≤ p := (Finset.mem_Icc.mp hk).2.trans (Nat.sub_le p 1)
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk2]
      dsimp [F]
      ring
    _ = F (p - 1 + 1) - F 1 := Finset.sum_Icc_sub (by omega) F
    _ = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - 1) := by
      rw [he]
      dsimp [F]
      ring

/-- For every prime `p ≥ 5`, `a(p-1)` is a perfect square if and only if `p^2 - 12 y^2 = 1`
for some natural `y ≥ 1`; for every such `y`, `a(p-1) = (p y)^2`. -/
theorem prime_row_square_iff (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ((∃ m : ℕ, a (p - 1) = m ^ 2) ↔ ∃ y : ℕ, 1 ≤ y ∧ (p : ℤ) ^ 2 - 12 * (y : ℤ) ^ 2 = 1) ∧
      ∀ y : ℕ, (p : ℤ) ^ 2 - 12 * (y : ℤ) ^ 2 = 1 → a (p - 1) = (p * y) ^ 2 := by
  have hr := prime_row p hp
  have hsuff : ∀ y : ℕ, (p : ℤ) ^ 2 - 12 * (y : ℤ) ^ 2 = 1 → a (p - 1) = (p * y) ^ 2 := by
    intro y hy
    have he : (a (p - 1) : ℤ) = ((p * y) ^ 2 : ℕ) := by
      push_cast
      have hP : (p : ℤ) ^ 2 - 1 = 12 * (y : ℤ) ^ 2 := by linarith
      rw [hP] at hr
      nlinarith only [hr]
    exact_mod_cast he
  refine ⟨⟨?_, fun ⟨y, _, hy⟩ => ⟨p * y, hsuff y hy⟩⟩, hsuff⟩
  rintro ⟨m, hm⟩
  rw [hm] at hr
  push_cast at hr
  have hdvd : p ∣ 12 * m ^ 2 := by
    have hz : (p : ℤ) ∣ ((12 * m ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hr]
      exact Dvd.intro ((p : ℤ) * ((p : ℤ) ^ 2 - 1)) (by ring)
    exact_mod_cast hz
  have h12 : ¬ p ∣ 12 := by
    intro h
    have h' : p ∣ 2 ^ 2 * 3 := by norm_num; exact h
    rcases hp.dvd_mul.mp h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hpm : p ∣ m := hp.dvd_of_dvd_pow ((hp.dvd_mul.mp hdvd).resolve_left h12)
  obtain ⟨y, rfl⟩ := hpm
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hy : (p : ℤ) ^ 2 - 12 * (y : ℤ) ^ 2 = 1 := by
    have h' : (p : ℤ) ^ 2 * (12 * (y : ℤ) ^ 2) = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - 1) := by
      push_cast at hr
      linarith
    have := mul_left_cancel₀ (pow_ne_zero 2 hp0) h'
    linarith
  refine ⟨y, ?_, hy⟩
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0
    have : (p : ℤ) ^ 2 = 1 := by simpa using hy
    have h25 : (25 : ℤ) ≤ (p : ℤ) ^ 2 := by
      have : (5 : ℤ) ≤ p := by exact_mod_cast h5
      nlinarith
    linarith
  · exact h0

end D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion
