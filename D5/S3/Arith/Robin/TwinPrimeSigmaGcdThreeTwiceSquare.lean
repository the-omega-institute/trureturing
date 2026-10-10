/- GID: D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: A twin-prime center with sigma-gcd three is twice a square. -/

import D5.S3.Factorization.TwinPrimeSigmaGcdDivisibility
import D5.S3.Arith.KrizekTriangularSquareSigmaParity

namespace D5.S3.Arith.Robin.TwinPrimeSigmaGcdThreeTwiceSquare

open ArithmeticFunction
open D5.S3.Factorization.TwinPrimeSigmaGcdDivisibility

/-- Odd divisor sum at a center above four excludes the square alternative. -/
theorem twice_square_of_odd_sigma {k : ℕ} (hk : 4 < k)
    (hp : (k - 1).Prime) (hsigma : Odd (sigma 1 k)) :
    ∃ m : ℕ, k = 2 * m ^ 2 := by
  rcases (D5.S3.Arith.KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square
    k (by omega)).mp hsigma with hsquare | htwice
  · obtain ⟨s, hs⟩ := hsquare
    have hs1 : 1 ≤ s := by nlinarith
    have hs2 : 2 < s := by nlinarith
    have hfactor : k - 1 = (s - 1) * (s + 1) := by
      have hsub := Nat.sub_add_cancel hs1
      have hk1 : 1 ≤ k := by omega
      have hkSub := Nat.sub_add_cancel hk1
      nlinarith
    rw [hfactor] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · exact htwice

open ArithmeticFunction in
/-- OEIS A394399 conjecture: a twin-prime center `k` with `gcd(k, σ(k)) = 3` is twice a square. -/
def claim : Prop :=
  ∀ k : ℕ, (k - 1).Prime → (k + 1).Prime → Nat.gcd k (sigma 1 k) = 3 → ∃ m : ℕ, k = 2 * m ^ 2

theorem result : claim := by
  intro k hp hq hg
  have hk3 : 3 ≤ k := by
    have h := hp.two_le
    omega
  have hk : 1 < k := by omega
  have heven : 2 ∣ k := even_center hk hp hq
  have hk4 : 4 < k := by
    by_contra h
    have hcases : k = 3 ∨ k = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hq
    · have hs : sigma 1 4 = 7 := by
        rw [show 4 = 2 ^ 2 by norm_num, sigma_one_apply_prime_pow Nat.prime_two]
        norm_num
      rw [hs] at hg
      norm_num at hg
  apply twice_square_of_odd_sigma hk4 hp
  apply Nat.not_even_iff_odd.mp
  intro hs
  have htwo : 2 ∣ Nat.gcd k (sigma 1 k) := Nat.dvd_gcd heven hs.two_dvd
  rw [hg] at htwo
  norm_num at htwo

end D5.S3.Arith.Robin.TwinPrimeSigmaGcdThreeTwiceSquare
