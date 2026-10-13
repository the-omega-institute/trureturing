/- GID: D5/S3/Arith/ModularForms/IntegralDiscriminant
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/IntegralDiscriminant
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Integer divisor-sum construction of the actual analytic discriminant. -/

import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries
open scoped BigOperators ArithmeticFunction.sigma

namespace D5.S3.Arith.ModularForms

/-- Positive-divisor power sum, with value zero at index zero. -/
def divisorPowerSum (r n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) ^ r

private lemma divisorPowerSum_eq_sigma (r n : ℕ) :
    divisorPowerSum r n = (σ r n : ℤ) := by
  simp [divisorPowerSum, ArithmeticFunction.sigma_apply]

private lemma twelve_dvd_divisor_polynomial (d : ℤ) :
    (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have h3 : (3 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have h : ∀ x : ZMod 3, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide +kernel
    simpa using h (d : ZMod 3)
  have h4 : (4 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have h : ∀ x : ZMod 4, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide +kernel
    simpa using h (d : ZMod 4)
  exact (show IsCoprime (3 : ℤ) 4 from by norm_num).mul_dvd h3 h4

private lemma twelve_dvd_divisor_sums (n : ℕ) :
    (12 : ℤ) ∣ 5 * divisorPowerSum 3 n + 7 * divisorPowerSum 5 n := by
  rw [divisorPowerSum, divisorPowerSum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.dvd_sum (fun d _ => twelve_dvd_divisor_polynomial d)

/-- Exact integral quotient used in the discriminant construction. -/
def discriminantQuotientCoeff (n : ℕ) : ℤ :=
  (5 * divisorPowerSum 3 n + 7 * divisorPowerSum 5 n) / 12

private lemma discriminantQuotientCoeff_exact (n : ℕ) :
    12 * discriminantQuotientCoeff n =
      5 * divisorPowerSum 3 n + 7 * divisorPowerSum 5 n := by
  rw [discriminantQuotientCoeff, mul_comm, Int.ediv_mul_cancel (twelve_dvd_divisor_sums n)]

noncomputable section

/-- Integral positive-divisor series. -/
def divisorSeries (r : ℕ) : PowerSeries ℤ := PowerSeries.mk (divisorPowerSum r)

/-- Integral quotient series. -/
def discriminantQuotient : PowerSeries ℤ := PowerSeries.mk discriminantQuotientCoeff

/-- The denominator-cleared integral series for the modular discriminant. -/
def integralDiscriminant : PowerSeries ℤ :=
  discriminantQuotient + PowerSeries.C 100 * divisorSeries 3 ^ 2 -
    PowerSeries.C 147 * divisorSeries 5 ^ 2 + PowerSeries.C 8000 * divisorSeries 3 ^ 3

/-- Integral normalized Eisenstein series of weight four. -/
def integralEisensteinFour : PowerSeries ℤ := 1 + PowerSeries.C 240 * divisorSeries 3

/-- Integral normalized Eisenstein series of weight six. -/
def integralEisensteinSix : PowerSeries ℤ := 1 - PowerSeries.C 504 * divisorSeries 5

private lemma quotient_series_exact :
    PowerSeries.C 12 * discriminantQuotient =
      PowerSeries.C 5 * divisorSeries 3 + PowerSeries.C 7 * divisorSeries 5 := by
  ext n
  simpa only [discriminantQuotient, divisorSeries, PowerSeries.coeff_C_mul,
    map_add, PowerSeries.coeff_mk] using discriminantQuotientCoeff_exact n

private lemma integralDiscriminant_identity :
    PowerSeries.C 1728 * integralDiscriminant =
      integralEisensteinFour ^ 3 - integralEisensteinSix ^ 2 := by
  have h := quotient_series_exact
  dsimp [integralDiscriminant, integralEisensteinFour, integralEisensteinSix]
  simp only [map_ofNat] at h ⊢
  linear_combination 144 * h

/-- The integer weight-four series maps to the actual normalized analytic Eisenstein series. -/
theorem integralEisensteinFour_map :
    PowerSeries.map (Int.castRingHom ℂ) integralEisensteinFour = qExpansion 1 E₄ := by
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by decide : 3 ≤ 4) ⟨2, rfl⟩]
  simp only [integralEisensteinFour, map_add, PowerSeries.coeff_C_mul,
    divisorSeries, PowerSeries.coeff_mk, divisorPowerSum_eq_sigma,
    PowerSeries.coeff_one]
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]
  split_ifs with hn <;> simp_all

/-- The integer weight-six series maps to the actual normalized analytic Eisenstein series. -/
theorem integralEisensteinSix_map :
    PowerSeries.map (Int.castRingHom ℂ) integralEisensteinSix = qExpansion 1 E₆ := by
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by decide : 3 ≤ 6) ⟨3, rfl⟩]
  simp only [integralEisensteinSix, map_sub, PowerSeries.coeff_C_mul,
    divisorSeries, PowerSeries.coeff_mk, divisorPowerSum_eq_sigma,
    PowerSeries.coeff_one]
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]
  split_ifs with hn <;> simp_all

private lemma analytic_discriminant_identity :
    PowerSeries.C (1728 : ℂ) * qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  let f : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) -
    ModularForm.mcast (by decide) (E₆.pow 2)
  have hf : (1728 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12) = f := by
    ext z
    change (1728 : ℂ) * ModularForm.discriminant z = E₄ z ^ 3 - E₆ z ^ 2
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have hq := congrArg (fun g : ModularForm 𝒮ℒ 12 => qExpansion 1 g) hf
  change qExpansion 1 ((1728 : ℂ) • (CuspForm.discriminant : ℍ → ℂ)) =
    qExpansion 1 f at hq
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL] at hq
  simpa only [f, FunLike.coe_sub, ModularForm.coe_mcast, CuspForm.coe_discriminant,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.smul_eq_C_mul] using hq

/-- The constructed integer series represents the actual analytic modular discriminant. -/
theorem integralDiscriminant_map :
    PowerSeries.map (Int.castRingHom ℂ) integralDiscriminant =
      qExpansion 1 ModularForm.discriminant := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) integralDiscriminant_identity
  simp only [map_mul, map_sub, map_pow, PowerSeries.map_C, integralEisensteinFour_map,
    integralEisensteinSix_map] at h
  exact mul_left_cancel₀ (by
    intro hz
    have hc := congrArg PowerSeries.constantCoeff hz
    norm_num at hc : PowerSeries.C (1728 : ℂ) ≠ 0)
    (h.trans analytic_discriminant_identity.symm)

end

/-- Finite convolution at one coefficient, implemented entirely over integers. -/
def integerConvolution (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

/-- Executable integer coefficient of the analytic discriminant. -/
def discriminantCoefficient (n : ℕ) : ℤ :=
  discriminantQuotientCoeff n +
    100 * integerConvolution (divisorPowerSum 3) (divisorPowerSum 3) n -
    147 * integerConvolution (divisorPowerSum 5) (divisorPowerSum 5) n +
    8000 * integerConvolution
      (integerConvolution (divisorPowerSum 3) (divisorPowerSum 3)) (divisorPowerSum 3) n

noncomputable section

private lemma coeff_mul_integerConvolution (a b : PowerSeries ℤ) (n : ℕ) :
    (a * b).coeff n = integerConvolution (fun i => a.coeff i) (fun i => b.coeff i) n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private lemma integralDiscriminant_coeff_algorithm (n : ℕ) :
    integralDiscriminant.coeff n = discriminantCoefficient n := by
  have hs (r i : ℕ) : (divisorSeries r ^ 2).coeff i =
      integerConvolution (divisorPowerSum r) (divisorPowerSum r) i := by
    rw [pow_two, coeff_mul_integerConvolution]
    simp only [divisorSeries, PowerSeries.coeff_mk]
  have hc : (divisorSeries 3 ^ 3).coeff n =
      integerConvolution (integerConvolution (divisorPowerSum 3) (divisorPowerSum 3))
        (divisorPowerSum 3) n := by
    rw [show divisorSeries 3 ^ 3 = divisorSeries 3 ^ 2 * divisorSeries 3 by ring,
      coeff_mul_integerConvolution]
    simp_rw [hs]
    simp only [divisorSeries, PowerSeries.coeff_mk]
  simp only [integralDiscriminant, map_add, map_sub, PowerSeries.coeff_C_mul,
    discriminantQuotient, PowerSeries.coeff_mk, hs, hc, discriminantCoefficient]

/-- Every coefficient of the actual analytic discriminant is the output of the integer algorithm. -/
theorem discriminantCoefficient_correct (n : ℕ) :
    (qExpansion 1 ModularForm.discriminant).coeff n = (discriminantCoefficient n : ℂ) := by
  rw [← integralDiscriminant_map, PowerSeries.coeff_map, integralDiscriminant_coeff_algorithm]
  rfl


end

end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.integralEisensteinFour_map
#print axioms D5.S3.Arith.ModularForms.integralEisensteinSix_map
#print axioms D5.S3.Arith.ModularForms.integralDiscriminant_map
#print axioms D5.S3.Arith.ModularForms.discriminantCoefficient_correct
