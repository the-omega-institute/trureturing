/- GID: D5/S3/Quantum/Subentropy/SpectralFormula
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/SpectralFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: The determinant integral equals the subentropy spectral formula at distinct positive probabilities. -/

import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.UniformIntegrals
import Mathlib.LinearAlgebra.Lagrange

/-! Lagrange residues identify the determinant integral on positive simple spectra. -/
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace D5.S3.Quantum.Subentropy.SpectralFormula
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.UniformIntegrals

/-- The residue coefficient in the simple-spectrum subentropy formula. -/
def spectralCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (i : ι) : ℝ :=
  p i ^ Fintype.card ι / ∏ j ∈ Finset.univ.erase i, (p i - p j)

private def defectPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : ℝ[X] :=
  Lagrange.nodal Finset.univ (fun i => -p i) - X ^ Fintype.card ι

private theorem degree_defect_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : (defectPolynomial p).degree < Fintype.card ι := by
  have hdeg : (Lagrange.nodal Finset.univ (fun i => -p i)).degree =
      (X ^ Fintype.card ι : ℝ[X]).degree := by simp
  have h := Polynomial.degree_sub_lt_left hdeg
    (Lagrange.nodal_ne_zero (s := Finset.univ) (v := fun i => -p i))
    (show (Lagrange.nodal Finset.univ (fun i => -p i)).leadingCoeff =
      (X ^ Fintype.card ι : ℝ[X]).leadingCoeff by
      rw [(Lagrange.nodal_monic (s := Finset.univ) (v := fun i => -p i)).leadingCoeff,
        (monic_X_pow _).leadingCoeff])
  simpa [defectPolynomial] using h

private theorem negated_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (i : ι) :
    (-( -p i) ^ Fintype.card ι) /
        (∏ j ∈ Finset.univ.erase i, (-p i - -p j)) = spectralCoefficient p i := by
  have hc : Fintype.card ι = (Finset.univ.erase i).card + 1 := by
    simpa using (Finset.card_erase_add_one (Finset.mem_univ i)).symm
  have hn : -(-p i) ^ Fintype.card ι =
      (-1 : ℝ) ^ (Finset.univ.erase i).card * p i ^ Fintype.card ι := by
    rw [neg_pow, hc, pow_succ]
    ring
  have hd : (∏ j ∈ Finset.univ.erase i, (-p i - -p j)) =
      (-1 : ℝ) ^ (Finset.univ.erase i).card *
        ∏ j ∈ Finset.univ.erase i, (p i - p j) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase i, (-1 : ℝ) * (p i - p j) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hn, hd, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))]
  rfl

private theorem defect_at_node {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (i : ι) :
    (defectPolynomial p).eval (-p i) = -(-p i) ^ Fintype.card ι := by
  rw [defectPolynomial, Polynomial.eval_sub,
    Lagrange.eval_nodal_at_node (v := fun j => -p j) (Finset.mem_univ i)]
  simp

private theorem residue_polynomial_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hpinj : Function.Injective p) :
    defectPolynomial p =
      ∑ i, C (spectralCoefficient p i) *
        (∏ j ∈ Finset.univ.erase i, (X + C (p j))) := by
  have hinj : Set.InjOn (fun i => -p i) (Finset.univ : Finset ι) := by
    intro i _ j _ h
    exact hpinj (neg_injective h)
  rw [Lagrange.eq_interpolate hinj (degree_defect_lt p), Lagrange.interpolate_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [defect_at_node, negated_residue]
  simp only [map_neg, sub_neg_eq_add]

private theorem residue_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℝ) (hpinj : Function.Injective p) :
    ∑ i, spectralCoefficient p i = ∑ i, p i := by
  have hinj : Set.InjOn (fun i => -p i) (Finset.univ : Finset ι) := by
    intro i _ j _ h
    exact hpinj (neg_injective h)
  have h := Lagrange.coeff_eq_sum hinj (degree_defect_lt p)
  simp_rw [defect_at_node, negated_residue] at h
  rw [← h]
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hcoeff := Polynomial.prod_X_sub_C_coeff_card_pred Finset.univ
    (fun i => -p i) (by simpa using hn)
  simp only [defectPolynomial, Polynomial.coeff_sub, Lagrange.nodal]
  rw [hcoeff]
  simp only [Finset.sum_neg_distrib, neg_neg]
  rw [Polynomial.coeff_X_pow]
  simp [show Fintype.card ι - 1 ≠ Fintype.card ι by omega]

private theorem kernel_partial_fractions {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hpinj : Function.Injective p)
    (t : ℝ) (ht : 0 < t) :
    subentropyKernel (diagonal (fun i => (p i : ℂ))) t =
      ∑ i, spectralCoefficient p i * (1 / (t + p i) - 1 / (t + 1)) := by
  have htp : ∀ i, t + p i ≠ 0 := fun i => (add_pos ht (hp i)).ne'
  have hprod : (∏ i, (t + p i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => htp i)
  have heval := congrArg (Polynomial.eval t) (residue_polynomial_identity p hpinj)
  simp only [defectPolynomial, Lagrange.nodal, Polynomial.eval_sub, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_neg_eq_add, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_add] at heval
  have hratio (i : ι) :
      (∏ j ∈ Finset.univ.erase i, (t + p j)) / (∏ j, (t + p j)) =
        1 / (t + p i) := by
    apply (div_eq_div_iff hprod (htp i)).mpr
    simpa [mul_comm] using
      (Finset.mul_prod_erase Finset.univ (fun j => t + p j) (Finset.mem_univ i))
  have hdiv := congrArg (fun a : ℝ => a / (∏ i, (t + p i))) heval
  rw [sub_div, div_self hprod, Finset.sum_div] at hdiv
  simp_rw [mul_div_assoc, hratio, mul_one_div] at hdiv
  have hr : ∑ i, spectralCoefficient p i = 1 := (residue_sum p hpinj).trans hsum
  have heq : (∑ i, spectralCoefficient p i * (1 / (t + p i) - 1 / (t + 1))) =
      (∑ i, spectralCoefficient p i / (t + p i)) - 1 / (t + 1) := by
    simp_rw [mul_sub, mul_one_div]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hr]
  rw [kernel_diagonal p t ht.ne', heq]
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [← hdiv]
  have hbase : t / (1 + t) = 1 - 1 / (t + 1) := by
    field_simp [show 1 + t ≠ 0 by linarith, show t + 1 ≠ 0 by linarith]
    <;> ring
  rw [hbase]
  ring

/-- For positive distinct probabilities, the determinant integral is the
finite spectral formula, with the exponent equal to the full cardinality. -/
theorem matrixSubentropy_diagonal_eq_distinct_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hpinj : Function.Injective p) :
    matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
      -(∑ i, p i ^ Fintype.card ι * Real.log (p i) /
        (∏ j ∈ Finset.univ.erase i, (p i - p j))) := by
  have hi : Nonempty ι := by
    by_contra he
    haveI : IsEmpty ι := not_nonempty_iff.mp he
    simp at hsum
  letI : Nonempty ι := hi
  have hle (i : ι) : p i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ i)
  have hrec (i : ι) := reciprocal_difference (p i) 1 (hp i) (hle i)
  unfold matrixSubentropy
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => kernel_partial_fractions p hp hsum hpinj t ht)]
  rw [integral_finsetSum _ (fun i _ => (hrec i).1.const_mul (spectralCoefficient p i))]
  calc
    _ = ∑ i, spectralCoefficient p i * (Real.log 1 - Real.log (p i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, (hrec i).2]
    _ = _ := by simp [spectralCoefficient, div_mul_eq_mul_div]

end D5.S3.Quantum.Subentropy.SpectralFormula
