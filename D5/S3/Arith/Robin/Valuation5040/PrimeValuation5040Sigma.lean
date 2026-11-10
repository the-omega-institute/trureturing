/- GID: D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact divisor-sum and normalized-sigma factorization on the 5040 valuation fibre. -/

/- New public theorem registration audits remain linked to issue #24055; no
   four-slot registration status is asserted without source-bound evidence. -/

import D5.S3.Arith.ExponentExchange.IntegerSwap
import D5.S3.Arith.ExponentExchange.CoprimeNormalForm
import D5.S3.Arith.Robin.PrimeValuation5040Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma

open D5.S3.Arith.ExponentExchange.IntegerSwap
open D5.S3.Arith.ExponentExchange.CoprimeNormalForm
open D5.S3.Arith.Robin.PrimeValuation5040Bridge

private theorem coprime_5040_of_coprime_210 {n : ℕ} (hn : n.Coprime 210) :
    n.Coprime 5040 := by
  apply (hn.pow_right 4).coprime_dvd_right
  norm_num [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 * 7 by norm_num]

private theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  decide +kernel

/-- The exact raw divisor-sum factor carried by the 5040 valuation block. -/
theorem sigma_5040_mul_of_coprime {n : ℕ} (hn : n.Coprime 210) :
    ArithmeticFunction.sigma 1 (5040 * n) =
      19344 * ArithmeticFunction.sigma 1 n := by
  have hmul :
      ArithmeticFunction.sigma 1 (n * 5040) =
        ArithmeticFunction.sigma 1 n * ArithmeticFunction.sigma 1 5040 :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (coprime_5040_of_coprime_210 hn)
  calc
    ArithmeticFunction.sigma 1 (5040 * n) =
        ArithmeticFunction.sigma 1 (n * 5040) := by
          exact congrArg (ArithmeticFunction.sigma 1) (Nat.mul_comm 5040 n)
    _ = ArithmeticFunction.sigma 1 n * ArithmeticFunction.sigma 1 5040 := hmul
    _ = 19344 * ArithmeticFunction.sigma 1 n := by rw [sigma_5040]; ring

/-- The normalized sigma ratio splits into the exact finite 5040 factor `403/105`
and the unrestricted residual ratio. -/
theorem normalized_sigma_5040_mul_of_coprime {n : ℕ} (hn0 : n ≠ 0)
    (hn : n.Coprime 210) :
    (ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) =
      (403 / 105 : ℝ) *
        ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
  have hnorm := normalized_sigma_mul (coprime_5040_of_coprime_210 hn)
  have h5040 : (ArithmeticFunction.sigma 1 5040 : ℝ) / 5040 = 403 / 105 := by
    norm_num [sigma_5040]
  calc
    (ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / ((5040 : ℝ) * (n : ℝ)) =
        (ArithmeticFunction.sigma 1 (n * 5040) : ℝ) / ((n : ℝ) * (5040 : ℝ)) := by
          rw [Nat.mul_comm 5040 n, mul_comm (5040 : ℝ) (n : ℝ)]
    _ = ((ArithmeticFunction.sigma 1 n : ℝ) / n) *
        ((ArithmeticFunction.sigma 1 5040 : ℝ) / 5040) := by
          convert hnorm using 1 <;> norm_num [Nat.cast_mul]
    _ = (403 / 105 : ℝ) * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
          rw [h5040]
          ring

/-- The normalized factorization applies directly to the exact 5040 valuation fibre.
The fibre theorem supplies both nonzeroness and the residual coprimality. -/
theorem normalized_sigma_of_jointFiber5040 {W n : ℕ}
    (hW : ∀ p ∈ _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040,
      p.Coprime W)
    (hfibre : jointFiber
      _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040
      profile5040 W (5040 * n)) :
    (ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) =
      (403 / 105 : ℝ) *
        ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
  obtain ⟨hn0, hnW⟩ := (jointFiber5040_mul_iff hW).mp hfibre
  exact normalized_sigma_5040_mul_of_coprime hn0
    (hnW.coprime_dvd_right (by norm_num : (210 : ℕ) ∣ W * 210))

/-- A finite conditional Robin reduction on the 5040 fibre.  It consumes the
external-modulus normal form: a bound on the ordered residual representatives
propagates to every residual factor in the fibre. -/
theorem normalized_sigma_of_jointFiber5040_le_of_ordered_bound {W n : ℕ}
    (hW : ∀ p ∈ _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040,
      p.Coprime W)
    (hfibre : jointFiber
      _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040
      profile5040 W (5040 * n))
    (B : ℝ)
    (hbound : ∀ m : ℕ, 1 ≤ m → m.Coprime 210 → AllowedOrdered 210 m →
      (ArithmeticFunction.sigma 1 m : ℝ) / m ≤ B) :
    (ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) ≤
      (403 / 105 : ℝ) * B := by
  obtain ⟨hn0, hnW⟩ := (jointFiber5040_mul_iff hW).mp hfibre
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hn210 : n.Coprime 210 :=
    hnW.coprime_dvd_right (by norm_num : (210 : ℕ) ∣ W * 210)
  obtain ⟨m, hm1, hmle, hmM, hmord, hratio⟩ :=
    exists_coprime_allowed_ordered_form hn1 hn210
  have hmBound := hbound m hm1 hmM hmord
  rw [normalized_sigma_5040_mul_of_coprime hn0 hn210]
  exact mul_le_mul_of_nonneg_left (hratio.trans hmBound) (by norm_num)

/- The 5040 block converts the strict abundancy threshold into an exact residual
   threshold.  This is the usable contrapositive form for excluding a whole
   valuation fibre: no analytic assertion about the residual ratio is hidden
   in the bridge. -/
theorem normalized_sigma_5040_gt_two_iff {n : ℕ} (hn0 : n ≠ 0)
    (hn : n.Coprime 210) :
    ((ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) > 2) ↔
      ((ArithmeticFunction.sigma 1 n : ℝ) / n > (210 / 403 : ℝ)) := by
  rw [normalized_sigma_5040_mul_of_coprime hn0 hn]
  constructor <;> intro h <;> nlinarith

#print axioms sigma_5040_mul_of_coprime
#print axioms normalized_sigma_5040_mul_of_coprime
#print axioms normalized_sigma_of_jointFiber5040
#print axioms normalized_sigma_of_jointFiber5040_le_of_ordered_bound
#print axioms normalized_sigma_5040_gt_two_iff

end D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma
