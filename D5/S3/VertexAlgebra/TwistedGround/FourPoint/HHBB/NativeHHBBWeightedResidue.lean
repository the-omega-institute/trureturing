import D5.S3.VertexAlgebra.CollisionRationalExpansions
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBTwoVariableRational

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra

open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.PolynomialCollision (constantR finite_numerator_collision iotaZX_x)
open CollisionLaurentKernels.RationalFusedResidue (fused_residue_commutes)
open CollisionRationalExpansions.RationalCoefficientCollision (rationalX xPolynomial
  rational_coefficient_collision)
open CollisionRationalExpansions.SpectatorPole (rationalZ zPolynomial separated_rational_collision)
open CollisionRationalExpansions.PartialFractionCollision (Compatible compatible_add compatible_sum)

namespace TwistedGround.FourPoint.NativeHHBBWeightedResidue

section LaurentMonomials

variable (K : Type*) [Field K]

private theorem x_nonzero : x K ≠ 0 := by
  intro h
  simpa only [iotaZX_x, map_zero, HahnSeries.single_eq_zero_iff, one_ne_zero] using
    congrArg (iotaZX K) h

private theorem z_nonzero : z K ≠ 0 := by
  intro h
  simpa only [iotaXZ_z, map_zero, HahnSeries.single_eq_zero_iff, one_ne_zero] using
    congrArg (iotaXZ K) h

private theorem x_sub_z_nonzero : x K - z K ≠ 0 := by
  intro h
  have hd : diagonal K = 0 := sub_eq_zero.mpr (sub_eq_zero.mp h).symm
  simpa only [iotaFused_diagonal, map_zero, HahnSeries.single_eq_zero_iff, one_ne_zero] using
    congrArg (iotaFused K) hd

private theorem rationalX_X : rationalX K (RatFunc.X : RatFunc K) = x K := by
  rw [RatFunc.X, rationalX, IsFractionRing.lift_algebraMap]
  rfl

private theorem rationalZ_X : rationalZ K (RatFunc.X : RatFunc K) = z K := by
  rw [RatFunc.X, rationalZ, IsFractionRing.lift_algebraMap]
  simp [zPolynomial, z]

private theorem rationalX_C (a : K) : rationalX K (RatFunc.C a) = constantR K a := by
  rw [← RatFunc.algebraMap_C, rationalX, IsFractionRing.lift_algebraMap]
  rfl

-- The repository's fused coordinate is z-x.
private theorem x_sub_z_zpow (r : ℤ) :
    (x K - z K) ^ r = (-1 : Rational K) ^ r * diagonal K ^ r := by
  rw [show x K - z K = (-1 : Rational K) * diagonal K by simp [diagonal], mul_zpow]

private theorem compatible_nonnegative_z (h : RatFunc K) (m : ℕ) (r : ℤ) :
    Compatible K (rationalX K h * (z K ^ m * (x K - z K) ^ r)) := by
  have hcol := rational_coefficient_collision K (h * (-1 : RatFunc K) ^ r) m 0 r
  dsimp only at hcol
  rw [← fused_residue_commutes] at hcol
  have hnormal : rationalX K (h * (-1 : RatFunc K) ^ r) * (z K ^ m * diagonal K ^ r) =
      rationalX K h * (z K ^ m * (x K - z K) ^ r) := by
    simp only [map_mul, map_zpow₀, map_neg, map_one, x_sub_z_zpow]
    ring
  simpa only [Compatible, Int.natCast_zero, sub_zero, hnormal] using hcol.symm

private theorem compatible_nonnegative_x_sub_z (h : RatFunc K) (p : ℤ) (n : ℕ) :
    Compatible K (rationalX K h * (z K ^ p * (x K - z K) ^ n)) := by
  rw [sub_pow, Finset.mul_sum, Finset.mul_sum]
  apply compatible_sum K
  intro i _
  let hx : RatFunc K := h * (-1) ^ (i + n) * RatFunc.X ^ i * (n.choose i : RatFunc K)
  let gz : RatFunc K := RatFunc.X ^ (p + ((n - i : ℕ) : ℤ))
  have hcol := separated_rational_collision K gz hx
  dsimp only at hcol
  rw [← fused_residue_commutes] at hcol
  have hnormal : rationalX K hx * rationalZ K gz =
      rationalX K h * (z K ^ p *
        ((-1) ^ (i + n) * x K ^ i * z K ^ (n - i) * (n.choose i : Rational K))) := by
    simp only [hx, gz, map_mul, map_pow, map_zpow₀, map_natCast, map_neg, map_one,
      rationalX_X, rationalZ_X, zpow_add₀ (z_nonzero K), zpow_natCast]
    ring
  simpa only [Compatible, hnormal] using hcol.symm

/-- A rational x-coefficient times any integer powers of z and x-z satisfies the
formal collision identity. Simultaneous poles are split by x = z + (x-z). -/
theorem rationalX_laurent_monomial_collision (h : RatFunc K) (p r : ℤ) :
    Compatible K (rationalX K h * (z K ^ p * (x K - z K) ^ r)) := by
  by_cases hp : 0 ≤ p
  · rw [← Int.toNat_of_nonneg hp, zpow_natCast]
    exact compatible_nonnegative_z K h p.toNat r
  by_cases hr : 0 ≤ r
  · rw [← Int.toNat_of_nonneg hr, zpow_natCast]
    exact compatible_nonnegative_x_sub_z K h p r.toNat
  have hX : rationalX K (h / RatFunc.X) * x K = rationalX K h := by
    rw [map_div₀, rationalX_X, div_mul_cancel₀ _ (x_nonzero K)]
  have hsplit : rationalX K h * (z K ^ p * (x K - z K) ^ r) =
      rationalX K (h / RatFunc.X) * (z K ^ (p + 1) * (x K - z K) ^ r) +
      rationalX K (h / RatFunc.X) * (z K ^ p * (x K - z K) ^ (r + 1)) := by
    calc
      _ = (rationalX K (h / RatFunc.X) * x K) * (z K ^ p * (x K - z K) ^ r) := by rw [hX]
      _ = rationalX K (h / RatFunc.X) *
          (z K * (z K ^ p * (x K - z K) ^ r) +
            (x K - z K) * (z K ^ p * (x K - z K) ^ r)) := by
        rw [← add_mul, add_sub_cancel]
        ring
      _ = _ := by
        rw [zpow_add_one₀ (z_nonzero K), zpow_add_one₀ (x_sub_z_nonzero K)]
        ring
  rw [hsplit]
  exact compatible_add K
    (rationalX_laurent_monomial_collision (h / RatFunc.X) (p + 1) r)
    (rationalX_laurent_monomial_collision (h / RatFunc.X) p (r + 1))
termination_by (-p).toNat + (-r).toNat
decreasing_by all_goals omega

end LaurentMonomials

open NativeHHBBTwoVariableRational (commonRational homogenizedNumerator denominator)

private theorem constantR_mul_neg_one_zpow (a : ℂ) (r : ℤ) :
    constantR ℂ (a * (-1) ^ r) = constantR ℂ a * (-1 : Rational ℂ) ^ r := by
  let f : ℂ →+* Rational ℂ := (rationalX ℂ).comp RatFunc.C
  have hf (s : ℂ) : f s = constantR ℂ s := rationalX_C ℂ s
  rw [← hf, ← hf, map_mul, map_zpow₀, map_neg, map_one]

/-- Every integer Laurent test monomial gives the residue jump for the exact
homogenized HHBB rational function with its grade-dependent denominator. -/
theorem commonRational_weighted_collision (P : Polynomial ℂ) (degree M K L : ℕ)
    (q p r : ℤ) :
    Compatible ℂ (x ℂ ^ q * z ℂ ^ p * (x ℂ - z ℂ) ^ r * commonRational P degree M K L) := by
  let a : ℕ := (5 + K + L) / 2
  let b : ℕ := (6 + M + K) / 2
  let c : ℕ := (M + L + 7) / 2
  let qj (j : ℕ) : ℤ := q + ((degree - j : ℕ) : ℤ) - c
  let pj (j : ℕ) : ℤ := p + (j : ℤ) - a
  let t : ℤ := r - b
  have hsum : x ℂ ^ q * z ℂ ^ p * (x ℂ - z ℂ) ^ r * commonRational P degree M K L =
      ∑ j ∈ Finset.range (degree + 1),
        constantR ℂ (P.coeff j) * (x ℂ ^ qj j * (z ℂ ^ pj j * (x ℂ - z ℂ) ^ t)) := by
    simp only [commonRational, homogenizedNumerator, denominator, map_sum, map_mul, map_pow, map_sub]
    change x ℂ ^ q * z ℂ ^ p * (x ℂ - z ℂ) ^ r *
        ((∑ j ∈ Finset.range (degree + 1),
          constantR ℂ (P.coeff j) * x ℂ ^ (degree - j) * z ℂ ^ j) /
          (x ℂ ^ c * z ℂ ^ a * (x ℂ - z ℂ) ^ b)) = _
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [qj, pj, t, zpow_sub₀ (x_nonzero ℂ), zpow_sub₀ (z_nonzero ℂ),
      zpow_sub₀ (x_sub_z_nonzero ℂ), zpow_add₀ (x_nonzero ℂ), zpow_add₀ (z_nonzero ℂ),
      zpow_natCast, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsum]
  by_cases hp : 0 ≤ p - (a : ℤ)
  · -- All z exponents are natural, so the finite numerator kernel applies directly.
    let m (j : ℕ) : ℕ := (p - (a : ℤ)).toNat + j
    have hm (j : ℕ) : (m j : ℤ) = pj j := by
      dsimp [m, pj]
      omega
    have hcol : Compatible ℂ (∑ j ∈ Finset.range (degree + 1),
        constantR ℂ (P.coeff j * (-1 : ℂ) ^ t) *
          (x ℂ ^ qj j * (z ℂ ^ m j * diagonal ℂ ^ (t - (0 : ℕ))))) :=
      finite_numerator_collision ℂ _ (fun j => P.coeff j * (-1 : ℂ) ^ t) qj m 0 t
    convert hcol using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← hm j, zpow_natCast, x_sub_z_zpow, constantR_mul_neg_one_zpow]
    simp only [Int.natCast_zero, sub_zero]
    ring
  · apply compatible_sum ℂ
    intro j _
    have hcol := rationalX_laurent_monomial_collision ℂ
      (RatFunc.C (P.coeff j) * RatFunc.X ^ qj j) (pj j) t
    rw [map_mul, map_zpow₀, rationalX_X, rationalX_C, mul_assoc] at hcol
    exact hcol

end TwistedGround.FourPoint.NativeHHBBWeightedResidue
end D5.S3.VertexAlgebra
