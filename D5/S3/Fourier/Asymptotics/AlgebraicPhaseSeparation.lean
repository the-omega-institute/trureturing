/- GID: D5/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A field norm bounds the separation of products of unit-modulus phases. -/

import Mathlib.NumberTheory.NumberField.House
import Mathlib.Tactic.Positivity
import OmegaBuild.Commands

/-! Denominator clearing for signed products of algebraic phases. -/

compile_only_with_mathlib

namespace D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation

open scoped BigOperators NumberField

private theorem integral_norm_lower {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (ha : a ≠ 0) (σ : K →+* ℂ) :
    1 ≤ ‖σ (a : K)‖ * NumberField.house (a : K) ^ (Module.finrank ℚ K - 1) := by
  have hK : (a : K) ≠ 0 := fun h => ha (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)
  have hq : Algebra.norm ℚ (a : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hK
  have hnorm : Algebra.norm ℤ a ≠ 0 := by
    intro h
    apply hq
    rw [← Algebra.coe_norm_int, h, Int.cast_zero]
  have hRat : (1 : ℝ) ≤ ‖Algebra.norm ℚ (a : K)‖ := by
    rw [← Rat.norm_cast_real, Real.norm_eq_abs, ← Algebra.coe_norm_int]
    exact_mod_cast Int.one_le_abs hnorm
  exact hRat.trans (NumberField.norm_norm_le_norm_mul_house_pow (a : K) σ)

private theorem house_sub_one_le_two {K : Type*} [Field K] [NumberField K] (w : K)
    (hunit : ∀ τ : K →+* ℂ, ‖τ w‖ = 1) : NumberField.house (w - 1) ≤ 2 := by
  rw [NumberField.house_eq_sup']
  change ((Finset.univ.sup' Finset.univ_nonempty
    (fun τ : K →+* ℂ => ‖τ (w - 1)‖₊) : NNReal) : ℝ) ≤ 2
  exact_mod_cast (Finset.sup'_le _ _ (fun τ _ => by
    change ‖τ (w - 1)‖₊ ≤ 2
    apply NNReal.coe_le_coe.mp
    change ‖τ (w - 1)‖ ≤ 2
    rw [map_sub, map_one]
    calc
      ‖τ w - 1‖ ≤ ‖τ w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hunit, norm_one]; norm_num))

private theorem embedding_bound {K : Type*} [Field K] [NumberField K]
    (w : K) (B : ℕ) (hB : B ≠ 0) (hw : w ≠ 1) (hclear : IsIntegral ℤ ((B : K) * w))
    (hunit : ∀ τ : K →+* ℂ, ‖τ w‖ = 1) (σ : K →+* ℂ) :
    1 ≤ ‖σ w - 1‖ * ((B : ℝ) * (2 * B) ^ (Module.finrank ℚ K - 1)) := by
  have hint : IsIntegral ℤ ((B : K) * (w - 1)) := by
    rw [mul_sub, mul_one]
    exact hclear.sub (isIntegral_natCast (R := ℤ) B)
  let a : 𝓞 K := ⟨(B : K) * (w - 1), hint⟩
  have ha : a ≠ 0 := by
    intro he
    apply mul_ne_zero (Nat.cast_ne_zero.mpr hB) (sub_ne_zero.mpr hw)
    exact congrArg (fun a : 𝓞 K => (a : K)) he
  have hc := integral_norm_lower a ha σ
  change 1 ≤ ‖σ ((B : K) * (w - 1))‖ *
      NumberField.house ((B : K) * (w - 1)) ^ (Module.finrank ℚ K - 1) at hc
  rw [map_mul, map_natCast, map_sub, map_one, norm_mul, Complex.norm_natCast,
    NumberField.house_nat_mul] at hc
  refine hc.trans ?_
  rw [mul_comm (B : ℝ) ‖σ w - 1‖, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (mul_nonneg (by positivity) (NumberField.house_nonneg _)) ?_ _
  rw [mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (house_sub_one_le_two w hunit) (by positivity)

private theorem integral_scaled_product {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (phase : ι → K) (n : ι → ℤ) (D : ℕ)
    (hpos : ∀ i ∈ s, IsIntegral ℤ ((D : K) * phase i))
    (hneg : ∀ i ∈ s, IsIntegral ℤ ((D : K) * (phase i)⁻¹)) :
    IsIntegral ℤ ((D : K) ^ (∑ i ∈ s, (n i).natAbs) * ∏ i ∈ s, phase i ^ n i) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine IsIntegral.prod _ ?_
  intro i hi
  generalize n i = k
  cases k with
  | ofNat l =>
      simpa only [Int.ofNat_eq_natCast, Int.natAbs_natCast, zpow_natCast, mul_pow] using
        (hpos i hi).pow l
  | negSucc l =>
      simpa only [Int.natAbs_negSucc, zpow_negSucc, inv_pow, mul_pow] using (hneg i hi).pow (l + 1)

/-- A nontrivial signed product stays away from one at every complex embedding.
The clearing factor is the common denominator raised to the sum of absolute exponents. -/
theorem signed_product_separation {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (s : Finset ι) (phase : ι → K) (n : ι → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpos : ∀ i ∈ s, IsIntegral ℤ ((D : K) * phase i))
    (hneg : ∀ i ∈ s, IsIntegral ℤ ((D : K) * (phase i)⁻¹))
    (hunit : ∀ (τ : K →+* ℂ) (i : ι), i ∈ s → ‖τ (phase i)‖ = 1)
    (hnontrivial : (∏ i ∈ s, phase i ^ n i) ≠ 1) (σ : K →+* ℂ) :
    let B := D ^ (∑ i ∈ s, (n i).natAbs)
    1 ≤ ‖σ (∏ i ∈ s, phase i ^ n i) - 1‖ *
      ((B : ℝ) * (2 * B) ^ (Module.finrank ℚ K - 1)) := by
  dsimp only
  refine embedding_bound _ _ (pow_ne_zero _ hD) hnontrivial ?_ ?_ σ
  · rw [Nat.cast_pow]
    exact integral_scaled_product s phase n D hpos hneg
  · intro τ
    rw [map_prod, norm_prod]
    apply Finset.prod_eq_one
    intro i hi
    rw [map_zpow₀, norm_zpow, hunit τ i hi, one_zpow]

end D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
