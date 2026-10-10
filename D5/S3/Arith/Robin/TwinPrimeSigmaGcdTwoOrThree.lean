/- GID: D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: A prime sigma-gcd at a twin-prime center equals two or three. -/

import D5.S3.Arith.Robin.TwinPrimeSigmaGcdThreeTwiceSquare

namespace D5.S3.Arith.Robin.TwinPrimeSigmaGcdTwoOrThree

open ArithmeticFunction
open D5.S3.Factorization.TwinPrimeSigmaGcdDivisibility

private theorem three_dvd_sigma_twice_square {t : ℕ} (ht : t ≠ 0) :
    3 ∣ sigma 1 (2 * t ^ 2) := by
  obtain ⟨b, r, hr, htr⟩ := Nat.exists_eq_two_pow_mul_odd ht
  have hcop : Nat.Coprime (2 ^ (2 * b + 1)) (r ^ 2) :=
    (Nat.coprime_two_left.mpr hr).pow_left _ |>.pow_right _
  have hshape : 2 * t ^ 2 = 2 ^ (2 * b + 1) * r ^ 2 := by
    rw [htr, mul_pow, ← pow_mul, show b * 2 = 2 * b by omega, pow_succ]
    ring
  rw [hshape, isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_apply_prime_pow Nat.prime_two]
  apply dvd_mul_of_dvd_left
  rw [Nat.geomSum_eq (by decide : 2 ≤ 2)]
  simp only [show 2 - 1 = 1 by decide, Nat.div_one]
  apply Nat.dvd_of_mod_eq_zero
  have hpow : 2 ^ (2 * b + 1 + 1) % 3 = 1 := by
    rw [show 2 * b + 1 + 1 = 2 * (b + 1) by omega, pow_mul]
    norm_num [Nat.pow_mod]
  omega

open ArithmeticFunction in
/-- OEIS A394757 second conjecture: a prime `gcd(k, σ(k))` at a twin-prime center is `2` or `3`. -/
def claim : Prop :=
  ∀ k : ℕ, (k - 1).Prime → (k + 1).Prime → (Nat.gcd k (sigma 1 k)).Prime →
    Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3

theorem result : claim := by
  intro k hp hq hg
  have hk : 1 < k := by
    have h := hp.two_le
    omega
  have heven : 2 ∣ k := even_center hk hp hq
  rcases Nat.even_or_odd (sigma 1 k) with hsigma | hsigma
  · left
    exact ((Nat.dvd_prime hg).mp (Nat.dvd_gcd heven hsigma.two_dvd)).resolve_left
      (by norm_num) |>.symm
  · right
    have h18 : 18 ∣ k := sigma_gcd_divisibility hk hp hq hg
    have hk4 : 4 < k := by
      have hle := Nat.le_of_dvd (by omega : 0 < k) h18
      omega
    obtain ⟨t, hkt⟩ :=
      D5.S3.Arith.Robin.TwinPrimeSigmaGcdThreeTwiceSquare.twice_square_of_odd_sigma
        hk4 hp hsigma
    have ht : t ≠ 0 := by intro h; subst t; simp at hkt; omega
    have hthree : 3 ∣ k := three_center hk hp hq hg heven
    have hs3 : 3 ∣ sigma 1 k := hkt ▸ three_dvd_sigma_twice_square ht
    exact ((Nat.dvd_prime hg).mp (Nat.dvd_gcd hthree hs3)).resolve_left
      (by norm_num) |>.symm

end D5.S3.Arith.Robin.TwinPrimeSigmaGcdTwoOrThree
