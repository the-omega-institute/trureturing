/- GID: D5/S3/Quantum/Semigroups/WuCubicGibbsIsospectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicGibbsIsospectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp cubic entropy-squared coercivity on the two-mode Gibbs isospectral orbit. -/

import D5.S3.Quantum.Semigroups.WuCubicBalancedRepeatedPairs
import OmegaBuild.Commands

/-! Cubic coercivity on the unitary orbit of the two-mode Gibbs density. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsIsospectral

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight frameWeight_eq_jumpWeight
  jumpWeight emptyProbability fullProbability evenProbability)
open private row_normSq column_normSq frameWeight_marginals inFrame_charge_re odd_eq_one_sub_even
  jumpWeight_self lowering_amplitudes from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

private abbrev a (U : unitary Mat) (i : Fin 4) := emptyProbability (frameVector U i)
private abbrev b (U : unitary Mat) (i : Fin 4) := fullProbability (frameVector U i)
private abbrev e (U : unitary Mat) (i : Fin 4) := evenProbability (frameVector U i)
private abbrev d (U : unitary Mat) (i : Fin 4) := a U i - b U i
private abbrev u (U : unitary Mat) := 1 - e U 0
private abbrev v (U : unitary Mat) := 1 - e U 3
private abbrev p (U : unitary Mat) := b U 0
private abbrev q (U : unitary Mat) := a U 3
private abbrev A (R : ℝ) := (R - 1)^2 * (R + 1)
private abbrev J (R : ℝ) := (R^2 - 1)^2 * (R^2 + 1)
private abbrev extra (R : ℝ) := (R - 1)^2 * (1 + R^3) * R^2

def gibbsRoots (R : ℝ) : Fin 4 → ℝ := ![1, R, R, R^2]

def moment (R : ℝ) (U : unitary Mat) : ℝ :=
  R^6 - 1 + ∑ i, (gibbsRoots R i)^3 * d U i

def deficit (R : ℝ) (U : unitary Mat) : ℝ :=
  (∑ i, ∑ j, frameWeight U i j *
    (R * gibbsRoots R i - gibbsRoots R j)^2 * (R * gibbsRoots R i + gibbsRoots R j)) -
      A R * (R^3 + 1) / (R^3 - 1) * moment R U

private theorem occupation_rows (U : unitary Mat) :
    (∑ i, a U i) = 1 ∧ (∑ i, b U i) = 1 := by
  have hu : (U : Mat) * (U : Mat)ᴴ = 1 := Unitary.coe_mul_star_self U
  constructor
  · simpa only [a, emptyProbability, frameVector, hu, Matrix.one_apply_eq, Complex.one_re]
      using row_normSq (U : Mat) 0
  · simpa only [b, fullProbability, frameVector, hu, Matrix.one_apply_eq, Complex.one_re]
      using row_normSq (U : Mat) 3

private theorem even_eq (U : unitary Mat) (i : Fin 4) : e U i = a U i + b U i := rfl

private theorem middle_even (U : unitary Mat) : e U 1 + e U 2 = u U + v U := by
  obtain ⟨ha, hb⟩ := occupation_rows U
  simp only [Fin.sum_univ_four] at ha hb
  change e U 1 + e U 2 = (1 - e U 0) + (1 - e U 3)
  change a U 1 + b U 1 + (a U 2 + b U 2) =
    (1 - (a U 0 + b U 0)) + (1 - (a U 3 + b U 3))
  linarith only [ha, hb]

private theorem diagonal_weight (U : unitary Mat) (i : Fin 4) :
    frameWeight U i i = e U i * (1 - e U i) := by
  rw [frameWeight_eq_jumpWeight, jumpWeight_self, odd_eq_one_sub_even]

private theorem reverse_totals (U : unitary Mat) :
    frameWeight U 1 0 + frameWeight U 2 0 + frameWeight U 3 0 = u U^2 + 2 * p U ∧
    frameWeight U 3 1 + frameWeight U 3 2 + frameWeight U 3 0 = v U^2 + 2 * q U := by
  have hlo := (frameWeight_marginals U 0).2
  have hhi := (frameWeight_marginals U 3).1
  simp only [inFrame_charge_re, Fin.sum_univ_four, diagonal_weight] at hlo hhi
  change e U 0 * (1 - e U 0) + _ + _ + _ = 1 + (b U 0 - a U 0) at hlo
  change _ + _ + _ + e U 3 * (1 - e U 3) = 1 - (b U 3 - a U 3) at hhi
  simp only [even_eq] at hlo hhi
  constructor <;> simp only [u, v, even_eq, p, q]
  · linear_combination hlo
  · linear_combination hhi

theorem moment_eq (R : ℝ) (U : unitary Mat) :
    moment R U = (R^3 - 1) * (u U + 2 * p U) +
      R^3 * (R^3 - 1) * (v U + 2 * q U) := by
  obtain ⟨ha, hb⟩ := occupation_rows U
  simp only [Fin.sum_univ_four] at ha hb
  have hd : d U 1 + d U 2 = -d U 0 - d U 3 := by
    change (a U 1 - b U 1) + (a U 2 - b U 2) =
      -(a U 0 - b U 0) - (a U 3 - b U 3)
    linarith only [ha, hb]
  norm_num [moment, Fin.sum_univ_four, gibbsRoots, u, v, even_eq]
  linear_combination R^3 * hd

private theorem kernel_sum (R : ℝ) (W : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, W i j *
      (R * gibbsRoots R i - gibbsRoots R j)^2 * (R * gibbsRoots R i + gibbsRoots R j)) =
      A R * (W 0 0 + R^3 * W 1 1 + R^3 * W 2 2 + R^6 * W 3 3) +
      J R * (W 1 0 + W 2 0 + W 3 0) + R^3 * J R * (W 3 1 + W 3 2 + W 3 0) +
      R^3 * A R * (W 0 3 + W 1 2 + W 2 1) + extra R * W 3 0 := by
  norm_num [gibbsRoots, Fin.sum_univ_four]
  ring

theorem deficit_eq (R : ℝ) (hR : 1 < R) (U : unitary Mat) :
    deficit R U = (J R - A R) * u U^2 + R^3 * (J R - A R * R^3) * v U^2 -
      A R * R^3 * (e U 1^2 + e U 2^2) +
      2 * A R * (R^2 + R) * (p U + R^3 * q U) +
      R^3 * A R * (frameWeight U 0 3 + frameWeight U 1 2 + frameWeight U 2 1) +
      extra R * frameWeight U 3 0 := by
  have hT : 1 < R^3 := one_lt_pow₀ hR (by decide)
  obtain ⟨hlo, hhi⟩ := reverse_totals U
  rw [deficit, kernel_sum, hlo, hhi, moment_eq]
  simp only [diagonal_weight]
  have hdiag :
      e U 0 * (1 - e U 0) + R^3 * (e U 1 * (1 - e U 1)) +
          R^3 * (e U 2 * (1 - e U 2)) + R^6 * (e U 3 * (1 - e U 3)) =
        (1 + R^3) * u U + R^3 * (1 + R^3) * v U -
          (u U^2 + R^3 * (e U 1^2 + e U 2^2) + R^6 * v U^2) := by
    linear_combination R^3 * middle_even U
  rw [hdiag]
  field_simp [(sub_ne_zero.mpr hT.ne')]
  ring

private theorem empty_nonneg (U : unitary Mat) (i : Fin 4) : 0 ≤ a U i :=
  Complex.normSq_nonneg _
private theorem full_nonneg (U : unitary Mat) (i : Fin 4) : 0 ≤ b U i :=
  Complex.normSq_nonneg _

private theorem even_nonneg (U : unitary Mat) (i : Fin 4) : 0 ≤ e U i :=
  add_nonneg (empty_nonneg U i) (full_nonneg U i)

private theorem even_le_one (U : unitary Mat) (i : Fin 4) : e U i ≤ 1 := by
  apply sub_nonneg.mp
  rw [← odd_eq_one_sub_even]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

private theorem weight_nonneg (U : unitary Mat) (i j : Fin 4) : 0 ≤ frameWeight U i j :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

private theorem deficit_ge_occupation (R : ℝ) (hR : 1 < R) (U : unitary Mat) :
    (A R * (R^2 + R) / 2) * ((u U + 2 * p U)^2 + R^3 * (v U + 2 * q U)^2) ≤
      deficit R U := by
  have hR0 : 0 < R := by linarith
  have hA : 0 < A R := mul_pos (sq_pos_of_pos (sub_pos.mpr hR)) (by linarith)
  have hm : e U 1^2 + e U 2^2 ≤ (u U + v U)^2 := by
    rw [← middle_even U]
    nlinarith only [mul_nonneg (even_nonneg U 1) (even_nonneg U 2)]
  have hlow : (u U + 2 * p U)^2 ≤ u U^2 + 4 * p U := by
    have h := mul_nonneg (full_nonneg U 0) (empty_nonneg U 0)
    have heq : 1 - u U - p U = a U 0 := by simp only [u, p, even_eq]; ring
    rw [← heq] at h
    nlinarith only [h]
  have hhigh : (v U + 2 * q U)^2 ≤ v U^2 + 4 * q U := by
    have h := mul_nonneg (empty_nonneg U 3) (full_nonneg U 3)
    have heq : 1 - v U - q U = b U 3 := by
      change 1 - (1 - (a U 3 + b U 3)) - a U 3 = _
      ring
    rw [← heq] at h
    nlinarith only [h]
  have hsum :
      (A R * (R^2 + R) / 2) * ((u U + 2 * p U)^2 + R^3 * (v U + 2 * q U)^2) ≤
        (A R * (R^2 + R) / 2) * (u U^2 + 4 * p U + R^3 * (v U^2 + 4 * q U)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add hlow (mul_le_mul_of_nonneg_left hhigh (by positivity))) (by positivity)
  have hJ : J R - A R = A R * (R^3 + R^2 + R) := by ring
  have hJT : J R - A R * R^3 = A R * (1 + R^2 + R) := by ring
  rw [deficit_eq R hR, hJ, hJT]
  refine hsum.trans ?_
  have hdiff :
      A R * (R^3 + R^2 + R) * u U^2 + R^3 * (A R * (1 + R^2 + R)) * v U^2 -
        A R * R^3 * (e U 1^2 + e U 2^2) +
        2 * A R * (R^2 + R) * (p U + R^3 * q U) -
        (A R * (R^2 + R) / 2) * (u U^2 + 4 * p U + R^3 * (v U^2 + 4 * q U)) =
      A R * (R * (u U - R^2 * v U)^2 / 2 + R^2 * (u U - R * v U)^2 / 2 +
        R^3 * ((u U + v U)^2 - (e U 1^2 + e U 2^2))) := by ring
  have hrest : 0 ≤ A R * (R * (u U - R^2 * v U)^2 / 2 + R^2 * (u U - R * v U)^2 / 2 +
        R^3 * ((u U + v U)^2 - (e U 1^2 + e U 2^2))) := by
    have := sub_nonneg.mpr hm
    positivity
  have hedges : 0 ≤ R^3 * A R *
        (frameWeight U 0 3 + frameWeight U 1 2 + frameWeight U 2 1) +
        extra R * frameWeight U 3 0 := by
    have := weight_nonneg U 0 3
    have := weight_nonneg U 1 2
    have := weight_nonneg U 2 1
    have := weight_nonneg U 3 0
    positivity
  linarith only [hdiff, hrest, hedges]

theorem deficit_ge_moment_sq (R : ℝ) (hR : 1 < R) (U : unitary Mat) :
    A R * (R^2 + R) * moment R U^2 / (2 * (R^3 - 1)^2 * (1 + R^3)) ≤ deficit R U := by
  have hR0 : 0 < R := by linarith
  have hT : 1 < R^3 := one_lt_pow₀ hR (by decide)
  refine le_trans ?_ (deficit_ge_occupation R hR U)
  rw [moment_eq, div_le_iff₀ (by positivity)]
  have hdiff :
      (A R * (R^2 + R) / 2) * ((u U + 2 * p U)^2 + R^3 * (v U + 2 * q U)^2) *
          (2 * (R^3 - 1)^2 * (1 + R^3)) -
        A R * (R^2 + R) * ((R^3 - 1) * (u U + 2 * p U) +
          R^3 * (R^3 - 1) * (v U + 2 * q U))^2 =
      A R * (R^2 + R) * (R^3 - 1)^2 * R^3 * ((u U + 2 * p U) - (v U + 2 * q U))^2 := by ring
  have hnonneg : 0 ≤ A R * (R^2 + R) * (R^3 - 1)^2 * R^3 *
      ((u U + 2 * p U) - (v U + 2 * q U))^2 := by positivity
  linarith only [hdiff, hnonneg]

open WuCubicOccupationEnvelope (scaledCubicEnergy spectrumOf)
open WuCubicBalancedRepeatedPairs (cubicMass cubicEnergy relativeEntropy sharpCoefficient
  normalizedCubicDeficit thermalFactor)
open private K from D5.S3.Quantum.Semigroups.WuCubicBalancedRepeatedPairs

private theorem gibbs_mass (R : ℝ) : cubicMass (gibbsRoots R) = (1 + R^3)^2 := by
  norm_num [cubicMass, gibbsRoots, Fin.sum_univ_four]
  ring

private theorem exp_products {h R : ℝ} (hR : R = Real.exp (2 * h / 3)) :
    Real.exp h * Real.exp h = R^3 ∧ Real.exp h * Real.exp (-h) = 1 ∧
    Real.exp h * Real.exp (h / 3) = R^2 ∧ Real.exp h * Real.exp (-(h / 3)) = R := by
  rw [hR]
  simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_ofNat, add_neg_cancel, Real.exp_zero]
  exact ⟨congrArg Real.exp (by ring), trivial, congrArg Real.exp (by ring),
    congrArg Real.exp (by ring)⟩

private theorem gibbs_partition {h R : ℝ} (hR : R = Real.exp (2 * h / 3)) :
    2 * Real.exp h * Real.cosh h = 1 + R^3 := by
  obtain ⟨h₁, h₂, _, _⟩ := exp_products hR
  rw [Real.cosh_eq]
  linear_combination h₁ + h₂

theorem relativeEntropy_eq_moment {h R : ℝ} (hR : R = Real.exp (2 * h / 3))
    (U : unitary Mat) :
    relativeEntropy h (gibbsRoots R) (frameWeight U) =
      2 * h * moment R U / (1 + R^3)^2 := by
  have hr : 0 < R := hR ▸ Real.exp_pos _
  have hz : 0 < (1 + R^3)^2 := by positivity
  have hlogR : Real.log R = 2 * h / 3 := by rw [hR, Real.log_exp]
  have hlogBase : Real.log (1 + R^3) = h + Real.log (2 * Real.cosh h) := by
    rw [← gibbs_partition hR, mul_right_comm,
      Real.log_mul (by positivity : (2 * Real.cosh h : ℝ) ≠ 0) (Real.exp_pos h).ne',
      Real.log_exp]
    ring
  rw [WuCubicBalancedRepeatedPairs.relativeEntropy_eq_frameGibbs h (gibbsRoots R) U
    (gibbs_mass R ▸ hz), gibbs_mass]
  norm_num [Fin.sum_univ_four, spectrumOf, gibbsRoots, moment]
  simp only [Real.log_div (pow_ne_zero 3 hr.ne') hz.ne',
    Real.log_div (pow_ne_zero 3 (pow_ne_zero 2 hr.ne')) hz.ne',
    Real.log_pow, hlogR, hlogBase]
  field_simp [hz.ne']
  ring

private theorem scaled_thermalFactor {h R : ℝ} (hR : R = Real.exp (2 * h / 3))
    (hr : 1 < R) :
    2 * Real.exp h * thermalFactor h = A R * (R^3 + 1) / (R^3 - 1) := by
  have hT : 1 < R^3 := one_lt_pow₀ hr (by decide)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := exp_products hR
  have hc : 2 * Real.exp h * Real.cosh (h / 3) = R^2 + R := by
    rw [Real.cosh_eq]
    linear_combination h₃ + h₄
  have hs : 2 * Real.exp h * Real.sinh h = R^3 - 1 := by
    rw [Real.sinh_eq]
    linear_combination h₁ - h₂
  have hdiff : 2 * Real.exp h * (Real.cosh h - Real.cosh (h / 3)) = A R := by
    linear_combination gibbs_partition hR - hc
  have hs0 : Real.sinh h ≠ 0 := by
    intro he
    rw [he, mul_zero] at hs
    exact (sub_pos.mpr hT).ne' hs.symm
  unfold thermalFactor
  apply (eq_div_iff (sub_pos.mpr hT).ne').2
  rw [← hs, add_comm (R^3) 1, ← gibbs_partition hR, ← hdiff]
  field_simp [hs0]

theorem deficit_eq_normalizedCubicDeficit {h : ℝ} (hh : 0 < h) (U : unitary Mat) :
    let R := Real.exp (2 * h / 3)
    deficit R U = 2 * Real.exp h * (1 + R^3)^2 *
      normalizedCubicDeficit h (gibbsRoots R) (frameWeight U) := by
  let R := Real.exp (2 * h / 3)
  have hr : 1 < R := Real.one_lt_exp_iff.mpr (by positivity)
  have hz : 0 < (1 + R^3)^2 := by have : 0 < R := Real.exp_pos _; positivity
  obtain ⟨h₁, h₂, h₃, h₄⟩ := exp_products (rfl : R = Real.exp (2 * h / 3))
  have henergy :
      2 * Real.exp h * cubicMass (gibbsRoots R) *
        scaledCubicEnergy (Real.cosh h) (Real.sinh h)
          (Real.cosh (h / 3)) (Real.sinh (h / 3)) (gibbsRoots R)
          (cubicMass (gibbsRoots R)) (frameWeight U) =
      ∑ i, ∑ j, frameWeight U i j *
        (R * gibbsRoots R i - gibbsRoots R j)^2 *
        (R * gibbsRoots R i + gibbsRoots R j) := by
    unfold scaledCubicEnergy
    simp only [gibbs_mass, spectrumOf, Real.cosh_add_sinh, Real.cosh_sub_sinh, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    field_simp [hz.ne']
    linear_combination
      frameWeight U i j * (gibbsRoots R i)^3 * h₁ +
      frameWeight U i j * (gibbsRoots R j)^3 * h₂ -
      frameWeight U i j * (gibbsRoots R i)^2 * gibbsRoots R j * h₃ -
      frameWeight U i j * gibbsRoots R i * (gibbsRoots R j)^2 * h₄
  change deficit R U = _
  rw [deficit, normalizedCubicDeficit, relativeEntropy_eq_moment (rfl : R = _),
    ← gibbs_mass R, mul_sub, henergy, gibbs_mass, ← scaled_thermalFactor (rfl : R = _) hr]
  unfold K
  field_simp [hz.ne', hh.ne']

theorem ordinaryTrace_ge_moment_sq {h : ℝ} (hh : 0 < h) (U : unitary Mat) :
    let R := Real.exp (2 * h / 3)
    A R * (R^2 + R) * moment R U^2 /
      ((2 * (R^3 - 1)^2 * (1 + R^3)) * (2 * Real.exp h * (1 + R^3)^2 * (4 * Real.cosh h / 9))) ≤
      cubicEnergy h (gibbsRoots R) (frameWeight U) -
        sharpCoefficient h * relativeEntropy h (gibbsRoots R) (frameWeight U) := by
  let R := Real.exp (2 * h / 3)
  have hr : 1 < R := Real.one_lt_exp_iff.mpr (by positivity)
  have hscale : 0 < 2 * Real.exp h * (1 + R^3)^2 * (4 * Real.cosh h / 9) := by
    have : 0 < R := Real.exp_pos _
    positivity
  have h := deficit_ge_moment_sq R hr U
  rw [deficit_eq_normalizedCubicDeficit hh,
    WuCubicBalancedRepeatedPairs.normalizedCubicDeficit_eq hh, ← mul_assoc] at h
  dsimp only
  rw [← div_div]
  exact (div_le_iff₀ hscale).mpr (h.trans_eq (mul_comm _ _))

def gibbsDensity (R : ℝ) : Mat :=
  diagonal (fun i => (spectrumOf (gibbsRoots R) ((1 + R^3)^2) i : ℂ))

private theorem weight_eq_amplitudes (U : unitary Mat) (i j : Fin 4) :
    frameWeight U i j =
      Complex.normSq (star (frameVector U i 0) * frameVector U j 2 +
        star (frameVector U i 1) * frameVector U j 3) +
      Complex.normSq (-(star (frameVector U i 0) * frameVector U j 1) +
        star (frameVector U i 2) * frameVector U j 3) := by
  obtain ⟨h₀, h₁⟩ := lowering_amplitudes (frameVector U i) (frameVector U j)
  rw [frameWeight_eq_jumpWeight, jumpWeight, Fin.sum_univ_two, h₀, h₁]

def gibbsEndpointSwap : unitary Mat := by
  let W : Mat := !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]
  refine ⟨W, Unitary.mem_iff.mpr ?_⟩
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [W, Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem gibbsEndpointSwap_moment_sq_attained (R : ℝ) (hR : 1 < R) :
    let U := gibbsEndpointSwap
    deficit R U = 2 * A R * (R^2 + R) * (1 + R^3) ∧
    moment R U = 2 * (R^6 - 1) ∧ 0 < moment R U ∧
    A R * (R^2 + R) * moment R U^2 / (2 * (R^3 - 1)^2 * (1 + R^3)) = deficit R U := by
  let U := gibbsEndpointSwap
  have huv : u U = 0 ∧ v U = 0 ∧ e U 1 = 0 ∧ e U 2 = 0 ∧ p U = 1 ∧ q U = 1 := by
    norm_num [u, v, p, q, even_eq, a, b, emptyProbability, fullProbability, frameVector,
      U, gibbsEndpointSwap]
  have hw : frameWeight U 0 3 = 0 ∧ frameWeight U 1 2 = 0 ∧
      frameWeight U 2 1 = 0 ∧ frameWeight U 3 0 = 0 := by
    simp only [weight_eq_amplitudes]
    norm_num [frameVector, U, gibbsEndpointSwap]
  obtain ⟨hu, hv, he₁, he₂, hp, hq⟩ := huv
  obtain ⟨hw₀₃, hw₁₂, hw₂₁, hw₃₀⟩ := hw
  have hd : deficit R U = 2 * A R * (R^2 + R) * (1 + R^3) := by
    rw [deficit_eq R hR, hu, hv, he₁, he₂, hp, hq, hw₀₃, hw₁₂, hw₂₁, hw₃₀]
    ring
  have hm : moment R U = 2 * (R^6 - 1) := by
    rw [moment_eq, hu, hv, hp, hq]
    ring
  have hR0 : 0 < R := by linarith
  have hT : 1 < R^3 := one_lt_pow₀ hR (by decide)
  have hR6 : 1 < R^6 := one_lt_pow₀ hR (by decide)
  refine ⟨hd, hm, by rw [hm]; positivity, ?_⟩
  rw [hm, hd]
  apply (div_eq_iff (by positivity)).2
  ring

theorem ordinaryTrace_moment_sq_attained {h : ℝ} (hh : 0 < h) :
    let R := Real.exp (2 * h / 3)
    let U := gibbsEndpointSwap
    0 < moment R U ∧
    A R * (R^2 + R) * moment R U^2 /
      ((2 * (R^3 - 1)^2 * (1 + R^3)) * (2 * Real.exp h * (1 + R^3)^2 * (4 * Real.cosh h / 9))) =
      cubicEnergy h (gibbsRoots R) (frameWeight U) -
        sharpCoefficient h * relativeEntropy h (gibbsRoots R) (frameWeight U) := by
  let R := Real.exp (2 * h / 3)
  have hr : 1 < R := Real.one_lt_exp_iff.mpr (by positivity)
  have hscale : 0 < 2 * Real.exp h * (1 + R^3)^2 * (4 * Real.cosh h / 9) := by
    have : 0 < R := Real.exp_pos _
    positivity
  obtain ⟨_, _, hm, hs⟩ := gibbsEndpointSwap_moment_sq_attained R hr
  rw [deficit_eq_normalizedCubicDeficit hh,
    WuCubicBalancedRepeatedPairs.normalizedCubicDeficit_eq hh, ← mul_assoc] at hs
  refine ⟨hm, ?_⟩
  rw [← div_div]
  exact (div_eq_iff hscale.ne').2 (hs.trans (mul_comm _ _))

private def respectsGibbsBlocks (R : ℝ) (U : unitary Mat) : Prop :=
  ∀ i j, gibbsRoots R i ≠ gibbsRoots R j → (U : Mat) i j = 0

private theorem conjugate_gibbs_eq_iff {R : ℝ} (hR : 1 < R) (U : unitary Mat) :
    Unitary.conjStarAlgAut ℂ Mat U (gibbsDensity R) = gibbsDensity R ↔ respectsGibbsBlocks R U := by
  have hR0 : 0 < R := by linarith
  have hpos (i : Fin 4) : 0 < gibbsRoots R i := by fin_cases i <;> norm_num [gibbsRoots, hR0]
  have hz : (1 + R^3)^2 ≠ 0 := by positivity
  let D := gibbsDensity R
  let weights := fun i => (spectrumOf (gibbsRoots R) ((1 + R^3)^2) i : ℂ)
  let Q : Mat := U
  have hQ₁ : Qᴴ * Q = 1 := Unitary.coe_star_mul_self U
  have hQ₂ : Q * Qᴴ = 1 := Unitary.coe_mul_star_self U
  change Q * D * Qᴴ = D ↔ _
  have hcomm : Q * D * Qᴴ = D ↔ Q * D = D * Q := by
    constructor
    · intro he
      simpa only [Matrix.mul_assoc, hQ₁, mul_one] using congrArg (· * Q) he
    · intro he
      rw [he, Matrix.mul_assoc, hQ₂, mul_one]
  rw [hcomm]
  constructor
  · intro he i j hij
    have hp : Q i j * weights j = weights i * Q i j := by
      simpa only [D, gibbsDensity, Matrix.mul_diagonal, Matrix.diagonal_mul] using
        congrArg (fun M : Mat => M i j) he
    have hne : weights j - weights i ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he'
      apply hij
      have ht := Complex.ofReal_injective he'.symm
      change (gibbsRoots R i)^3 / _ = (gibbsRoots R j)^3 / _ at ht
      exact (pow_left_inj₀ (hpos i).le (hpos j).le (by decide)).1
        ((div_left_inj' hz).1 ht)
    have hp' : Q i j * (weights j - weights i) = 0 := by linear_combination hp
    exact (mul_eq_zero.mp hp').resolve_right hne
  · intro he
    ext i j
    change (Q * diagonal weights) i j = (diagonal weights * Q) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : gibbsRoots R i = gibbsRoots R j
    · simp only [weights, spectrumOf, hij, mul_comm]
    · simp [Q, he i j hij]

private theorem normSq_support {f : Fin 4 → ℂ} {k i : Fin 4}
    (hsum : (∑ j, Complex.normSq (f j)) = 1) (hk : Complex.normSq (f k) = 1)
    (hi : i ≠ k) : f i = 0 := by
  have hz := Finset.sum_erase_add Finset.univ (fun j => Complex.normSq (f j)) (Finset.mem_univ k)
  rw [hsum, hk] at hz
  have hle := Finset.single_le_sum (f := fun j => Complex.normSq (f j))
    (fun j _ => Complex.normSq_nonneg (f j)) (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact Complex.normSq_eq_zero.mp
    (le_antisymm (by linarith only [hle, hz]) (Complex.normSq_nonneg _))

private theorem endpoint_probabilities_of_zero {R : ℝ} (hR : 1 < R) {U : unitary Mat}
    (hzero : deficit R U = 0) : a U 0 = 1 ∧ b U 3 = 1 := by
  have hR0 : 0 < R := by linarith
  have hA : 0 < A R := mul_pos (sq_pos_of_pos (sub_pos.mpr hR)) (by linarith)
  have hcoef : 0 < A R * (R^2 + R) / 2 := by positivity
  have hgap := deficit_ge_occupation R hR U
  rw [hzero] at hgap
  have h := nonpos_of_mul_nonpos_right hgap hcoef
  have htail : 0 ≤ R^3 * (v U + 2 * q U)^2 := by positivity
  have hlo : u U + 2 * p U = 0 := by
    have : (u U + 2 * p U)^2 ≤ 0 := by linarith only [h, htail]
    exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
  have hhi : v U + 2 * q U = 0 := by
    have ht : R^3 * (v U + 2 * q U)^2 ≤ 0 := by linarith only [h, sq_nonneg (u U + 2 * p U)]
    exact sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right ht (pow_pos hR0 3))
      (sq_nonneg _))
  simp only [u, v, even_eq, p, q] at hlo hhi
  have he₀ := even_le_one U 0
  have he₃ := even_le_one U 3
  simp only [even_eq] at he₀ he₃
  exact ⟨by linarith only [hlo, he₀, full_nonneg U 0],
    by linarith only [hhi, he₃, empty_nonneg U 3]⟩

private theorem respectsGibbsBlocks_of_endpoints (R : ℝ) (U : unitary Mat)
    (h₀ : a U 0 = 1) (h₃ : b U 3 = 1) : respectsGibbsBlocks R U := by
  have hrow (k : Fin 4) : (∑ j, Complex.normSq ((U : Mat) k j)) = 1 := by
    rw [row_normSq, show (U : Mat) * (U : Mat)ᴴ = 1 from Unitary.coe_mul_star_self U,
      Matrix.one_apply_eq, Complex.one_re]
  have hcol (k : Fin 4) : (∑ j, Complex.normSq ((U : Mat) j k)) = 1 := by
    rw [column_normSq, show (U : Mat)ᴴ * (U : Mat) = 1 from Unitary.coe_star_mul_self U,
      Matrix.one_apply_eq, Complex.one_re]
  have hr₀ : ∀ i : Fin 4, i ≠ 0 → (U : Mat) 0 i = 0 :=
    fun _ hi => normSq_support (f := (U : Mat) 0) (hrow 0) h₀ hi
  have hr₃ : ∀ i : Fin 4, i ≠ 3 → (U : Mat) 3 i = 0 :=
    fun _ hi => normSq_support (f := (U : Mat) 3) (hrow 3) h₃ hi
  have hc₀ : ∀ i : Fin 4, i ≠ 0 → (U : Mat) i 0 = 0 :=
    fun _ hi => normSq_support (f := fun j => (U : Mat) j 0) (hcol 0) h₀ hi
  have hc₃ : ∀ i : Fin 4, i ≠ 3 → (U : Mat) i 3 = 0 :=
    fun _ hi => normSq_support (f := fun j => (U : Mat) j 3) (hcol 3) h₃ hi
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | exact hr₀ _ (by decide)
    | exact hr₃ _ (by decide)
    | exact hc₀ _ (by decide)
    | exact hc₃ _ (by decide)

private theorem deficit_zero_of_respectsGibbsBlocks {R : ℝ} (hR : 1 < R) {U : unitary Mat}
    (hblock : respectsGibbsBlocks R U) : deficit R U = 0 := by
  have hR0 : 0 < R := by linarith
  have hr₂ : R < R^2 := by simpa only [one_mul, pow_two] using mul_lt_mul_of_pos_right hR hR0
  have h₀ (i : Fin 4) (hi : i ≠ 0) : a U i = 0 := by
    change Complex.normSq ((U : Mat) 0 i) = 0
    apply Complex.normSq_eq_zero.mpr
    apply hblock
    fin_cases i
    · exact (hi rfl).elim
    · exact hR.ne
    · exact hR.ne
    · exact (lt_trans hR hr₂).ne
  have h₃ (i : Fin 4) (hi : i ≠ 3) : b U i = 0 := by
    change Complex.normSq ((U : Mat) 3 i) = 0
    apply Complex.normSq_eq_zero.mpr
    apply hblock
    fin_cases i
    · exact (lt_trans hR hr₂).ne'
    · exact hr₂.ne'
    · exact hr₂.ne'
    · exact (hi rfl).elim
  obtain ⟨ha, hb⟩ := occupation_rows U
  simp only [Fin.sum_univ_four, h₀ 1 (by decide), h₀ 2 (by decide), h₀ 3 (by decide), add_zero] at ha
  simp only [Fin.sum_univ_four, h₃ 0 (by decide), h₃ 1 (by decide), h₃ 2 (by decide), zero_add] at hb
  have hm : moment R U = 0 := by
    rw [moment_eq]
    simp [u, v, even_eq, p, q, ha, hb, h₀ 3 (by decide), h₃ 0 (by decide)]
  have hcost (i j : Fin 4) :
      frameWeight U i j * (R * gibbsRoots R i - gibbsRoots R j)^2 *
        (R * gibbsRoots R i + gibbsRoots R j) = 0 := by
    by_cases he : R * gibbsRoots R i = gibbsRoots R j
    · simp [he]
    have hp (s t : Fin 4) (hst : R * gibbsRoots R s = gibbsRoots R t) :
        star (frameVector U i s) * frameVector U j t = 0 := by
      by_cases hs : gibbsRoots R s = gibbsRoots R i
      · have ht : gibbsRoots R t ≠ gibbsRoots R j := by
          intro ht
          rw [hs, ht] at hst
          exact he hst
        simp [frameVector, hblock t j ht]
      · simp [frameVector, hblock s i hs]
    rw [weight_eq_amplitudes, hp 0 2 (by simp [gibbsRoots]),
      hp 1 3 (by simp [gibbsRoots, pow_two]), hp 0 1 (by simp [gibbsRoots]),
      hp 2 3 (by simp [gibbsRoots, pow_two])]
    simp
  simp [deficit, hm, hcost]

theorem deficit_eq_zero_iff (R : ℝ) (hR : 1 < R) (U : unitary Mat) :
    deficit R U = 0 ↔ Unitary.conjStarAlgAut ℂ Mat U (gibbsDensity R) = gibbsDensity R := by
  rw [conjugate_gibbs_eq_iff hR]
  refine ⟨fun hz => ?_, deficit_zero_of_respectsGibbsBlocks hR⟩
  obtain ⟨h₀, h₃⟩ := endpoint_probabilities_of_zero hR hz
  exact respectsGibbsBlocks_of_endpoints R U h₀ h₃

theorem ordinaryTrace_eq_zero_iff {h : ℝ} (hh : 0 < h) (U : unitary Mat) :
    let R := Real.exp (2 * h / 3)
    cubicEnergy h (gibbsRoots R) (frameWeight U) -
        sharpCoefficient h * relativeEntropy h (gibbsRoots R) (frameWeight U) = 0 ↔
      Unitary.conjStarAlgAut ℂ Mat U (gibbsDensity R) = gibbsDensity R := by
  let R := Real.exp (2 * h / 3)
  have hr : 1 < R := Real.one_lt_exp_iff.mpr (by positivity)
  have hz : 2 * Real.exp h * (1 + R^3)^2 ≠ 0 := by
    have : 0 < R := Real.exp_pos _
    positivity
  have hc : (4 * Real.cosh h / 9 : ℝ) ≠ 0 := by positivity
  change _ ↔ Unitary.conjStarAlgAut ℂ Mat U (gibbsDensity R) = gibbsDensity R
  rw [← deficit_eq_zero_iff R hr, deficit_eq_normalizedCubicDeficit hh,
    WuCubicBalancedRepeatedPairs.normalizedCubicDeficit_eq hh,
    mul_eq_zero, or_iff_right hz, mul_eq_zero, or_iff_right hc]

private def rotationMatrix (c s : ℝ) : Mat :=
  !![(c : ℂ), -(s : ℂ), 0, 0; (s : ℂ), (c : ℂ), 0, 0;
      0, 0, (c : ℂ), -(s : ℂ); 0, 0, (s : ℂ), (c : ℂ)]

def secondModeRotation (θ : ℝ) : unitary Mat := by
  refine ⟨rotationMatrix (Real.cos θ) (Real.sin θ), Unitary.mem_iff.mpr ?_⟩
  have hsq : (Real.sin θ : ℂ)^2 + (Real.cos θ : ℂ)^2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotationMatrix, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply, Complex.star_def,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    first | (ring; done) | linear_combination hsq

theorem secondModeRotation_deficit_moment (R : ℝ) (hR : 1 < R) (θ : ℝ) :
    deficit R (secondModeRotation θ) =
      A R * (1 + R^3) * (R^2 + R) * (Real.sin θ)^4 ∧
    moment R (secondModeRotation θ) = (R^6 - 1) * (Real.sin θ)^2 := by
  let U := secondModeRotation θ
  let s := Real.sin θ
  have huv : u U = s^2 ∧ v U = s^2 ∧ e U 1 = s^2 ∧ e U 2 = s^2 ∧ p U = 0 ∧ q U = 0 := by
    norm_num [u, v, p, q, even_eq, a, b, emptyProbability, fullProbability, frameVector,
      U, rotationMatrix, secondModeRotation, Complex.normSq_ofReal, s, ← pow_two,
      -Complex.ofReal_cos, -Complex.ofReal_sin]
    have hs := Real.sin_sq_add_cos_sq θ
    linarith only [hs]
  have hw₀₃ : frameWeight U 0 3 = 0 := by
    rw [weight_eq_amplitudes]
    norm_num [frameVector, U, rotationMatrix, secondModeRotation, Complex.star_def,
      mul_comm (Real.cos θ : ℂ) (Real.sin θ : ℂ), -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hw₁₂ : frameWeight U 1 2 = 0 := by
    rw [weight_eq_amplitudes]
    norm_num [frameVector, U, rotationMatrix, secondModeRotation, Complex.star_def,
      mul_comm (Real.cos θ : ℂ) (Real.sin θ : ℂ), -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hw₂₁ : frameWeight U 2 1 = 0 := by
    rw [weight_eq_amplitudes]
    norm_num [frameVector, U, rotationMatrix, secondModeRotation, Complex.star_def]
  have hw₃₀ : frameWeight U 3 0 = 0 := by
    rw [weight_eq_amplitudes]
    norm_num [frameVector, U, rotationMatrix, secondModeRotation, Complex.star_def]
  obtain ⟨hu, hv, he₁, he₂, hp, hq⟩ := huv
  change deficit R U = _ ∧ moment R U = _
  constructor
  · rw [deficit_eq R hR, hu, hv, he₁, he₂, hp, hq, hw₀₃, hw₁₂, hw₂₁, hw₃₀]
    dsimp only [s]
    ring
  · rw [moment_eq, hu, hv, hp, hq]
    dsimp only [s]
    ring

theorem secondModeRotation_quadraticEntropy {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    let R := Real.exp (2 * h / 3)
    let U := secondModeRotation θ
    (2 * h * (R^6 - 1) / (1 + R^3)^2)^2 * deficit R U =
      A R * (1 + R^3) * (R^2 + R) * (relativeEntropy h (gibbsRoots R) (frameWeight U))^2 := by
  let R := Real.exp (2 * h / 3)
  have hr : 1 < R := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨hd, hm⟩ := secondModeRotation_deficit_moment R hr θ
  change _ * deficit R (secondModeRotation θ) = _
  rw [hd, relativeEntropy_eq_moment (rfl : R = _), hm]
  ring

end D5.S3.Quantum.Semigroups.WuCubicGibbsIsospectral
