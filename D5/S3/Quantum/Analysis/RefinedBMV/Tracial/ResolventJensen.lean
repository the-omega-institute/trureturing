/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/ResolventJensen
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-cycle comparison of an inverse arithmetic mean with the product of inverses. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceWord

/-! The radial Gamma identity gives a cyclic Jensen comparison for the
fourth power of the reciprocal on a positive diagonal spectrum. -/

namespace RefinedBMV.Tracial

open Matrix MeasureTheory Set FourCopyGap

open private contract eigenDiagonal gapTrace gapTrace_diagonal monomial
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private gamma_trace_weight gamma_trace_integrable
  from D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceFourth
open private orthantMoment orthantMoment_eq_gaps fourRates raisedGap
  from D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceWord

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem zero_gaps : gaps 0 = {(0, 0, 0, 0)} := by
  ext ⟨a, b, c, d⟩
  simp only [mem_gaps, Finset.mem_singleton, Prod.mk.injEq]
  omega

private theorem orthant_at_zero_eq_prod_inv {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    orthantMoment 0 (fourRates a b c d) = a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ := by
  rw [orthantMoment_eq_gaps 0 ha hb hc hd]
  norm_num [zero_gaps, monomial, raisedGap]

private theorem trace_laplace_cycle_expansion (a : ι → ℝ) (B : Matrix ι ι ℂ) (s : ℝ) :
    (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re =
      ∑ i, ∑ j, ∑ k, ∑ l, Real.exp (-(((a i + a j + a k + a l) / 4) * s)) *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  have h := congrArg Complex.re (gapTrace_diagonal id
    (fun i ↦ Real.exp (-(s * a i / 4))) B (1, 1, 1, 1))
  simp only [gapTrace, eigenDiagonal, id_eq, pow_one, monomial,
    contract, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum, Complex.re_ofReal_mul] at h
  simp only [fourthLaplaceWeight, one_mul, pow_succ, pow_zero]
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- At order three the balanced Gamma integral is the cyclic contraction
of the inverse fourth power of the arithmetic spectral mean. -/
theorem fourth_laplace_gamma_eq_inverse_mean (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) :
    (∫ s in Ioi (0 : ℝ), s ^ (3 : ℝ) *
      (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re) =
      6 * ∑ i, ∑ j, ∑ k, ∑ l, ((a i + a j + a k + a l) / 4)⁻¹ ^ (4 : ℕ) *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  let q (i j k l : ι) := (a i + a j + a k + a l) / 4
  let c (i j k l : ι) := (cycleTrace (spectralBlock id B) i j k l).re
  let f (i j k l : ι) (s : ℝ) := (s ^ (3 : ℝ) * Real.exp (-(q i j k l * s))) * c i j k l
  have hq (i j k l : ι) : 0 < q i j k l :=
    div_pos (add_pos (add_pos (add_pos (ha i) (ha j)) (ha k)) (ha l)) (by norm_num)
  have hf (i j k l : ι) : IntegrableOn (f i j k l) (Ioi 0) :=
    (gamma_trace_integrable 3 (by norm_num) (hq i j k l)).mul_const (c i j k l)
  have hfun (s : ℝ) : s ^ (3 : ℝ) *
      (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re =
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l s := by
    rw [trace_laplace_cycle_expansion]
    simp only [Finset.mul_sum, f, q, c, mul_assoc]
  simp_rw [hfun]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  have hgamma : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = ↑(3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [f]
  rw [MeasureTheory.integral_mul_const, gamma_trace_weight 3 (by norm_num) (hq i j k l),
    show (3 : ℝ) + 1 = 4 by norm_num, hgamma, one_div,
    show (4 : ℝ) = ↑(4 : ℕ) by norm_num, Real.rpow_natCast]
  change (q i j k l)⁻¹ ^ (4 : ℕ) * 6 * c i j k l = _
  dsimp only [q, c]
  ring

/-- The orthant Laplace integral at degree zero has the product of the
four inverse rates as its cyclic kernel. -/
theorem fourth_orthant_zero_eq_product_inverse (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) :
    (fourthOrthantLaplaceMoment 0 a B).re =
      ∑ i, ∑ j, ∑ k, ∑ l, (a i)⁻¹ * (a j)⁻¹ * (a k)⁻¹ * (a l)⁻¹ *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  simp only [fourthOrthantLaplaceMoment, contract, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [orthant_at_zero_eq_prod_inv (ha i) (ha j) (ha k) (ha l)]

/-- For positive diagonal spectral data and a Hermitian factor, the cyclic
contraction of the inverse fourth power of the arithmetic spectral mean
is bounded by the contraction of the product of the four inverse rates. -/
theorem fourth_cycle_inv_mean_le_product_inverse (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (∑ i, ∑ j, ∑ k, ∑ l, ((a i + a j + a k + a l) / 4)⁻¹ ^ (4 : ℕ) *
      (cycleTrace (spectralBlock id B) i j k l).re) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, (a i)⁻¹ * (a j)⁻¹ * (a k)⁻¹ * (a l)⁻¹ *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  have h := fourth_laplace_moment_le_orthant_of_word_bound 0 a ha B hB (by
    simp only [Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero, Complex.ofReal_one,
      Matrix.diagonal_one, one_mul, wordMean_eq_gaps, zero_gaps, Finset.sum_singleton,
      Finset.card_singleton, Nat.cast_one, div_one, gapTrace, pow_zero]
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul])
  simp only [Nat.cast_zero, zero_add, fourth_laplace_gamma_eq_inverse_mean a ha B,
    fourth_orthant_zero_eq_product_inverse a ha B] at h
  exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < 6 by norm_num)).mp h

end

end RefinedBMV.Tracial
