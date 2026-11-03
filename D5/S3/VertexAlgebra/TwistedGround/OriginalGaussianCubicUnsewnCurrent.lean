import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
UNCOMPILED SOURCE. No elaboration, kernel or official acceptance is claimed.
The imported original supplier is preserved byte for byte and is UNCOMPILED.

This file binds the literal unsewn TT cubic to the literal original currentRow
at every positive index. The external hb is arbitrary. The proof first takes
the actual outer constant coefficient, then differentiates the native series
binomialSeries(1/2)/(b-X). Its finite coefficient convolution is proved below;
neither original object is defined by the desired identity. No all-degree
finite reconstruction or full sewn-cubic identification is asserted here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/-- The actual degree-zero Laurent series, expanded in a at zero.
The only external restriction is b != 0; no relation on hb is used. -/
theorem cubic_tt_degree_zero (b hb : ℂ) (hb0 : b ≠ 0) :
    PowerSeries.coeff 0 (cubicTTSeries b hb) =
      (halfSeries : LaurentSeries ℂ) * HahnSeries.C hb *
        (HahnSeries.single 1 1 + HahnSeries.C b + 2) *
          (2 * (HahnSeries.single 1 1 - HahnSeries.C b) ^ 2)⁻¹ := by
  let a : LaurentSeries ℂ := HahnSeries.single 1 1
  let B : LaurentSeries ℂ := HahnSeries.C b
  have hscalar : PowerSeries.constantCoeff scalarCSeries = 0 := by
    simp [scalarCSeries]
  have hmap : PowerSeries.constantCoeff
      (PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries) = 0 := by
    change HahnSeries.C (PowerSeries.constantCoeff scalarCSeries) = 0
    rw [hscalar, map_zero]
  have homega : PowerSeries.constantCoeff formalOmega =
      HahnSeries.single (-1) 1 * (halfSeries : LaurentSeries ℂ) := by
    simp [formalOmega, omegaCoefficient, halfBinomial]
  have hexternal : PowerSeries.constantCoeff (formalExternalOmega b hb) =
      HahnSeries.C (hb / b) := by
    simp [formalExternalOmega, halfBinomial]
  have ha : (HahnSeries.single (-1) 1 : LaurentSeries ℂ) * a = 1 := by
    simp [a, HahnSeries.single_mul_single]
  have hB : HahnSeries.C (hb / b) * B = HahnSeries.C hb := by
    change HahnSeries.C (hb / b) * HahnSeries.C b = HahnSeries.C hb
    rw [← map_mul]
    congr 1
    exact div_mul_cancel₀ hb hb0
  change PowerSeries.constantCoeff
    (formalOmega * formalExternalOmega b hb *
      ((PowerSeries.C a * PowerSeries.C B * (PowerSeries.C a + PowerSeries.C B) +
          2 * (1 + PowerSeries.X) * PowerSeries.C a * PowerSeries.C B +
          PowerSeries.X * (PowerSeries.C a + PowerSeries.C B)) *
        (2 * (PowerSeries.C a - PowerSeries.C B) ^ 2)⁻¹ +
        PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries)) = _
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
    PowerSeries.constantCoeff_inv, homega, hexternal, hmap,
    add_zero, zero_add, one_mul, zero_mul]
  calc
    _ = (halfSeries : LaurentSeries ℂ) * (HahnSeries.single (-1) 1 * a) *
        (HahnSeries.C (hb / b) * B) * (a + B + 2) *
          (2 * (a - B) ^ 2)⁻¹ := by ring
    _ = _ := by rw [ha, hB]; ring

private abbrev currentRoot : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)

private lemma half_binomial_series :
    halfSeries = PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) := by
  ext n
  simp [halfSeries, PowerSeries.binomialSeries_coeff, halfBinomial_choose]

private lemma root_eq_one_add_mul_half :
    currentRoot = (1 + PowerSeries.X) * halfSeries := by
  have hone : PowerSeries.binomialSeries ℂ (1 : ℂ) =
      (1 + PowerSeries.X : PowerSeries ℂ) := by
    simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
  rw [half_binomial_series, ← hone, ← PowerSeries.binomialSeries_add,
    show (1 : ℂ) + -1 / 2 = 1 / 2 by norm_num]

private lemma root_derivative :
    PowerSeries.derivative currentRoot = PowerSeries.C (1 / 2 : ℂ) * halfSeries := by
  ext n
  simp only [PowerSeries.coeff_derivative, currentRoot, PowerSeries.binomialSeries_coeff,
    smul_eq_mul, mul_one, PowerSeries.coeff_C_mul, halfSeries,
    PowerSeries.coeff_mk, halfBinomial_choose]
  have h : (n + 1 : ℂ) * Ring.choose (1 / 2 : ℂ) (n + 1) =
      (1 / 2 : ℂ) * Ring.choose (-1 / 2 : ℂ) n := by
    simpa only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
      Nat.cast_one, Nat.cast_add, Nat.add_sub_cancel,
      show (1 / 2 : ℂ) - 1 = -1 / 2 by norm_num] using
      (Ring.choose_smul_choose (1 / 2 : ℂ)
        (n := n + 1) (k := 1) (by omega))
  simpa only [mul_comm] using h

private lemma pole_inverse_coeff (b : ℂ) (hb0 : b ≠ 0) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.C b - PowerSeries.X : PowerSeries ℂ)⁻¹) =
      (b ^ (n + 1))⁻¹ := by
  have hc : PowerSeries.constantCoeff
      (PowerSeries.C b - PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    simpa using hb0
  have heq : PowerSeries.invUnitsSub (Units.mk0 b hb0) =
      (PowerSeries.C b - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one hc).mpr
    exact PowerSeries.invUnitsSub_mul_sub (Units.mk0 b hb0)
  simpa only [PowerSeries.coeff_invUnitsSub, one_divp,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] using
    congrArg (PowerSeries.coeff n) heq.symm

/- This is the finite convolution payment, for arbitrary n. The exponent
identity is used only under k <= n, supplied by the actual finite range. -/
private lemma root_over_pole_coeff (b : ℂ) (hb0 : b ≠ 0) (n : ℕ) :
    PowerSeries.coeff n
      (currentRoot * (PowerSeries.C b - PowerSeries.X)⁻¹) =
      ∑ k ∈ Finset.range (n + 1),
        Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (n + 1) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [currentRoot, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
    pole_inverse_coeff b hb0]
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hp : b ^ k * b ^ (n - k + 1) = b ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  apply (eq_div_iff (pow_ne_zero _ hb0)).mpr
  rw [← hp]
  calc
    _ = (Ring.choose (1 / 2 : ℂ) k * b ^ k) *
        ((b ^ (n - k + 1))⁻¹ * b ^ (n - k + 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hb0), mul_one]

private lemma current_denominator_constant (b : ℂ) (hb0 : b ≠ 0) :
    PowerSeries.constantCoeff
      (2 * (PowerSeries.X - PowerSeries.C b : PowerSeries ℂ) ^ 2) ≠ 0 := by
  simpa using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (pow_ne_zero 2 (neg_ne_zero.mpr hb0))

private lemma current_generating_derivative (b hb : ℂ) (hb0 : b ≠ 0) :
    PowerSeries.C hb * PowerSeries.derivative
        (currentRoot * (PowerSeries.C b - PowerSeries.X)⁻¹) =
      halfSeries * PowerSeries.C hb * (PowerSeries.X + PowerSeries.C b + 2) *
        (2 * (PowerSeries.X - PowerSeries.C b) ^ 2)⁻¹ := by
  let J : PowerSeries ℂ := (PowerSeries.C b - PowerSeries.X)⁻¹
  have hc : PowerSeries.constantCoeff
      (PowerSeries.C b - PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    simpa using hb0
  have hJ : (PowerSeries.C b - PowerSeries.X) * J = 1 :=
    PowerSeries.mul_inv_cancel _ hc
  have hJ2 : (PowerSeries.C b - PowerSeries.X) * J ^ 2 = J := by
    calc
      _ = ((PowerSeries.C b - PowerSeries.X) * J) * J := by ring
      _ = J := by rw [hJ, one_mul]
  have hhalf : (2 : PowerSeries ℂ) * PowerSeries.C (1 / 2 : ℂ) = 1 := by
    rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by simp, ← map_mul]
    norm_num
  have hdJ : PowerSeries.derivative J = J ^ 2 := by
    dsimp only [J]
    rw [PowerSeries.derivative_inv']
    simp
  have hd : PowerSeries.derivative (currentRoot * J) =
      halfSeries * PowerSeries.C (1 / 2 : ℂ) *
        (PowerSeries.X + PowerSeries.C b + 2) * J ^ 2 := by
    rw [PowerSeries.derivative.leibniz, hdJ, root_derivative]
    simp only [smul_eq_mul]
    calc
      _ = halfSeries * ((1 + PowerSeries.X) * J ^ 2 +
          PowerSeries.C (1 / 2 : ℂ) *
            ((PowerSeries.C b - PowerSeries.X) * J ^ 2)) := by
        rw [hJ2, root_eq_one_add_mul_half]
        ring
      _ = _ := by
        linear_combination
          -(halfSeries * (1 + PowerSeries.X) * J ^ 2) * hhalf
  have hden : (2 * (PowerSeries.X - PowerSeries.C b) ^ 2)⁻¹ =
      PowerSeries.C (1 / 2 : ℂ) * J ^ 2 := by
    symm
    apply (PowerSeries.eq_inv_iff_mul_eq_one (current_denominator_constant b hb0)).mpr
    calc
      _ = ((2 : PowerSeries ℂ) * PowerSeries.C (1 / 2 : ℂ)) *
          ((PowerSeries.C b - PowerSeries.X) * J) ^ 2 := by ring
      _ = 1 := by rw [hhalf, hJ]; simp
  change PowerSeries.C hb * PowerSeries.derivative (currentRoot * J) = _
  rw [hd, hden]
  ring

/- The embedding preserves the inverse only after proving the original
power-series denominator has nonzero constant coefficient. -/
private lemma current_coe_inverse (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = (f : LaurentSeries ℂ)⁻¹ := by
  have hmul : (f : LaurentSeries ℂ) * ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = 1 := by
    change HahnSeries.ofPowerSeries ℤ ℂ f * HahnSeries.ofPowerSeries ℤ ℂ f⁻¹ = 1
    rw [← map_mul, PowerSeries.mul_inv_cancel f hf, map_one]
  have hne : (f : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  exact mul_left_cancel₀ hne (hmul.trans (mul_inv_cancel₀ hne).symm)

private lemma cubic_tt_zero_as_derivative (b hb : ℂ) (hb0 : b ≠ 0) :
    PowerSeries.coeff 0 (cubicTTSeries b hb) =
      ((PowerSeries.C hb * PowerSeries.derivative
        (currentRoot * (PowerSeries.C b - PowerSeries.X)⁻¹) : PowerSeries ℂ) :
          LaurentSeries ℂ) := by
  rw [cubic_tt_degree_zero b hb hb0, current_generating_derivative b hb hb0]
  change _ = HahnSeries.ofPowerSeries ℤ ℂ
    (halfSeries * PowerSeries.C hb * (PowerSeries.X + PowerSeries.C b + 2) *
      (2 * (PowerSeries.X - PowerSeries.C b) ^ 2)⁻¹)
  rw [map_mul, current_coe_inverse _ (current_denominator_constant b hb0)]
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]

/-- Actual original unsewn binding at ALL positive indices, including s=1.
The two original definitions are unchanged; hb is an arbitrary complex scalar.
This UNCOMPILED proof term asserts no sewn or higher-modulus-degree identity. -/
theorem cubic_tt_degree_zero_currentRow (b hb : ℂ) (hb0 : b ≠ 0)
    (s : ℕ) (hs : 0 < s) :
    (PowerSeries.coeff 0 (cubicTTSeries b hb)).coeff ((s : ℤ) - 1) =
      currentRow b hb s := by
  cases s with
  | zero => omega
  | succ n =>
      have he : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      rw [Nat.succ_eq_add_one, he, cubic_tt_zero_as_derivative b hb hb0,
        LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_derivative, root_over_pole_coeff b hb0, currentRow]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
