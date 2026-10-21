/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeFiniteEnergy
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The actual reciprocal P and Q energies realize the finite Hermitian matrix in the original normalized head coordinates. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
import D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteAlgebra
import D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
import D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
import D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open scoped Interval
open ActualThreeNodeSourceHeadBridge ActualPairedReciprocal ActualNodalCoercivity
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds
local notation "U₃" => ActualThreeNodeFiniteAlgebra.U
local notation "T₃" => ActualThreeNodeFiniteAlgebra.T
local notation "C₃" => ActualThreeNodeFiniteAlgebra.C
local notation "O₃" => ActualThreeNodeFiniteAlgebra.O

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteEnergy

lemma nodes_distinct {n : ℤ} (hn : n ≠ 0) :
    -n ≠ 0 ∧ -n ≠ n ∧ (0 : ℤ) ≠ n := by
  refine ⟨neg_ne_zero.mpr hn, ?_, Ne.symm hn⟩
  omega

lemma threeNodes_card {n : ℤ} (hn : n ≠ 0) : (threeNodes n).card = 3 := by
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  simp [threeNodes, hn, hm0, hmp, h0p]

lemma actual_symbol_zero (c : ℕ) : arithmeticBoundarySymbol c 0 = 0 := by
  have h := arithmetic_boundary_symbol_neg c 0
  simp only [neg_zero] at h
  linarith

/-- Exact D/P/Q of the literal signed set; there is no positivity assumption on n. -/
lemma actual_three_nodal {n : ℤ} (hn : n ≠ 0) (c : ℕ) (v : ℤ → ℂ) :
    D (threeNodes n) = X * (X ^ 2 - C ((n : ℂ) ^ 2)) ∧
    Q (threeNodes n) v =
      C (v (-n) + v 0 + v n) * X ^ 2 +
        C ((n : ℂ) * (v n - v (-n))) * X - C ((n : ℂ) ^ 2 * v 0) ∧
    P c (threeNodes n) v =
      C ((arithmeticBoundarySymbol c n : ℂ) * (v n - v (-n))) * X ^ 2 +
        C ((arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (v n + v (-n))) * X := by
  classical
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  have h0 := actual_symbol_zero c
  constructor
  · simp [D, threeNodes, Lagrange.nodal, hn, hm0, hmp, h0p]
    ring
  constructor
  · simp [Q, threeNodes, Lagrange.nodal, hn, hm0, hmp, hmp.symm, h0p,
      Finset.erase_insert_of_ne, hm0.symm, h0p.symm,
      map_add, map_sub, map_mul, map_pow]
    ring
  · simp [P, threeNodes, Lagrange.nodal, hn, hm0, hmp, hmp.symm, h0p,
      Finset.erase_insert_of_ne, hm0.symm, h0p.symm,
      arithmetic_boundary_symbol_neg, h0, map_add, map_sub, map_mul, map_pow]
    ring

/-- Unnormalized coordinates are used only inside the finite algebra. -/
def rawHead (n : ℤ) (p q s : ℂ) : ℤ → ℂ :=
  p • (singletonHead (-n) + singletonHead 0 + singletonHead n) +
  q • (-singletonHead (-n) + singletonHead n) +
  s • (singletonHead (-n) - 2 • singletonHead 0 + singletonHead n)

lemma rawHead_nodes {n : ℤ} (hn : n ≠ 0) (p q s : ℂ) :
    rawHead n p q s (-n) = p - q + s ∧
    rawHead n p q s 0 = p - 2 * s ∧
    rawHead n p q s n = p + q + s := by
  rcases nodes_distinct hn with ⟨hm0, hmp, h0p⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [rawHead, singletonHead, Pi.single_apply, hn, hm0, hmp, hmp.symm,
      h0p, h0p.symm, hm0.symm, smul_eq_mul] <;> ring

lemma sourceHead_eq_rawHead (n : ℤ) (x : Fin 3 → ℂ) :
    sourceHead n x = rawHead n (x 0 / (Real.sqrt 3 : ℂ))
      (x 1 / (Real.sqrt 2 : ℂ)) (x 2 / (Real.sqrt 6 : ℂ)) := by
  funext k
  simp [sourceHead, normalizedHead, headE, headO, headS, rawHead,
    Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  <;> ring

/-- These are evaluations of the genuine reciprocal polynomials, not premises. -/
def rawA (a r : ℝ) (p q s : ℂ) : ℂ[X] :=
  C (2 * (a : ℂ) * q) + C (2 * (a : ℂ) * (r : ℂ) * (p + s)) * X

def rawB (r : ℝ) (p q s : ℂ) : ℂ[X] :=
  C (3 * p) + C (2 * (r : ℂ) * q) * X +
    C ((r : ℂ) ^ 2 * (-p + 2 * s)) * X ^ 2

lemma reciprocal_three (N : ℕ) (b0 b1 b2 : ℂ) :
    reciprocalPolynomial 3 N (C b0 + C b1 * X + C b2 * X ^ 2) =
      C b2 + C (b1 / (N : ℂ)) * X + C (b0 / (N : ℂ) ^ 2) * X ^ 2 := by
  simp [reciprocalPolynomial, Finset.sum_range_succ, Polynomial.coeff_X]
  <;> ring

lemma actual_raw_reciprocals {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (p q s : ℂ) :
    reciprocalPolynomial 3 N (P c (threeNodes n) (rawHead n p q s)) =
      rawA (arithmeticBoundarySymbol c n) ((n : ℝ) / N) p q s ∧
    reciprocalPolynomial 3 N (Q (threeNodes n) (rawHead n p q s)) =
      rawB ((n : ℝ) / N) p q s := by
  rcases actual_three_nodal hn c (rawHead n p q s) with ⟨_hD, hQ, hP⟩
  rcases rawHead_nodes hn p q s with ⟨hm, hz, hp⟩
  simp only [hm, hz, hp] at hQ hP
  have hPc : P c (threeNodes n) (rawHead n p q s) =
      C 0 + C (2 * (arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (p + s)) * X +
        C (2 * (arithmeticBoundarySymbol c n : ℂ) * q) * X ^ 2 := by
    rw [hP]
    simp [map_add, map_sub, map_mul, map_neg, Polynomial.C_ofNat]
    ring
  have hQc : Q (threeNodes n) (rawHead n p q s) =
      C ((n : ℂ) ^ 2 * (-p + 2 * s)) + C (2 * (n : ℂ) * q) * X + C (3 * p) * X ^ 2 := by
    rw [hQ]
    simp [map_add, map_sub, map_mul, map_neg, Polynomial.C_ofNat]
    ring
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : 2 * (arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (p + s) / (N : ℂ) =
      2 * (arithmeticBoundarySymbol c n : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) * (p + s) := by
    push_cast
    field_simp [hnC] <;> ring
  have h2 : (2 * (n : ℂ) * q) / (N : ℂ) =
      2 * (((n : ℝ) / N : ℝ) : ℂ) * q := by
    push_cast
    field_simp [hnC] <;> ring
  have h3 : ((n : ℂ) ^ 2 * (-p + 2 * s)) / (N : ℂ) ^ 2 =
      (((n : ℝ) / N : ℝ) : ℂ) ^ 2 * (-p + 2 * s) := by
    push_cast
    field_simp [hnC] <;> ring
  constructor
  · rw [hPc, reciprocal_three, h1]
    simp [rawA]
  · rw [hQc, reciprocal_three, h2, h3]
    rfl

def mixed (p s : ℂ) : ℝ := (conj p * s).re

def rawIntegrand (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) : ℝ :=
  ‖value (rawA a r p q s) t + (g : ℂ) * value (rawB r p q s) t‖ ^ 2 +
  ‖value (rawA a r p q s) (-t) - (g : ℂ) * value (rawB r p q s) (-t)‖ ^ 2 +
  mu * (‖value (rawB r p q s) t‖ ^ 2 + ‖value (rawB r p q s) (-t)‖ ^ 2)

/-- The cancellation is exact for arbitrary complex p/q/s, including zero. -/
def quarticCoeffs (g mu a r : ℝ) (p q s : ℂ) : Fin 5 → ℝ :=
  ![18 * (g ^ 2 + mu) * ‖p‖ ^ 2 + 8 * a ^ 2 * ‖q‖ ^ 2,
    24 * g * a * r * (‖p‖ ^ 2 + mixed p s) + 16 * a * g * r * ‖q‖ ^ 2,
    (8 * a ^ 2 - 12 * (g ^ 2 + mu)) * r ^ 2 * ‖p‖ ^ 2 +
      8 * (g ^ 2 + mu) * r ^ 2 * ‖q‖ ^ 2 + 8 * a ^ 2 * r ^ 2 * ‖s‖ ^ 2 +
      (16 * a ^ 2 + 24 * (g ^ 2 + mu)) * r ^ 2 * mixed p s,
    8 * a * g * r ^ 3 * (-‖p‖ ^ 2 + 2 * ‖s‖ ^ 2 + mixed p s),
    2 * (g ^ 2 + mu) * r ^ 4 * (‖p‖ ^ 2 + 4 * ‖s‖ ^ 2 - 4 * mixed p s)]

lemma rawIntegrand_parity_pair (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :
    rawIntegrand g mu a r p q s t =
      2 * ‖value (rawA a r p 0 s) t + (g : ℂ) * value (rawB r p 0 s) t‖ ^ 2 +
      2 * ‖value (rawA a r 0 q 0) t + (g : ℂ) * value (rawB r 0 q 0) t‖ ^ 2 +
      2 * mu * (‖value (rawB r p 0 s) t‖ ^ 2 + ‖value (rawB r 0 q 0) t‖ ^ 2) := by
  unfold rawIntegrand
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [rawIntegrand, rawA, rawB, value,
    Complex.mul_re, Complex.mul_im, pow_two]
  <;> ring

lemma rawIntegrand_quartic (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :
    rawIntegrand g mu a r p q s t =
      ∑ i : Fin 5, quarticCoeffs g mu a r p q s i * t ^ (i : ℕ) := by
  rw [rawIntegrand_parity_pair]
  unfold quarticCoeffs
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [rawA, rawB, value, quarticCoeffs, mixed, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, pow_two]
  <;> ring

lemma integral_fin5_monomials (b : Fin 5 → ℝ) :
    (∫ t in (0 : ℝ)..1, ∑ i : Fin 5, b i * t ^ (i : ℕ)) =
      ∑ i : Fin 5, b i / (((i : ℕ) : ℝ) + 1) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [intervalIntegral.integral_const_mul, integral_pow, div_eq_mul_inv]
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ => b i * t ^ (i : ℕ))).intervalIntegrable 0 1

lemma raw_pairedEnergy (c : ℕ) (a r : ℝ) (p q s : ℂ) :
    pairedEnergy c (rawA a r p q s) (rawB r p q s) =
      U₃ (Real.pi / 4) (mean c) a r * ‖p‖ ^ 2 +
      2 * O₃ (Real.pi / 4) (mean c) a r * ‖q‖ ^ 2 +
      C₃ (Real.pi / 4) (mean c) a r * ‖s‖ ^ 2 +
      2 * T₃ (Real.pi / 4) (mean c) a r * mixed p s := by
  rw [pairedEnergy_integral]
  change (∫ t in (0 : ℝ)..1, rawIntegrand (Real.pi / 4) (mean c) a r p q s t) = _
  calc
    _ = ∫ t in (0 : ℝ)..1,
        ∑ i : Fin 5, quarticCoeffs (Real.pi / 4) (mean c) a r p q s i * t ^ (i : ℕ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact rawIntegrand_quartic _ _ _ _ _ _ _ _
    _ = ∑ i : Fin 5,
        quarticCoeffs (Real.pi / 4) (mean c) a r p q s i / (((i : ℕ) : ℝ) + 1) :=
      integral_fin5_monomials _
    _ = _ := by
      simp [quarticCoeffs, Fin.sum_univ_succ, ActualThreeNodeFiniteAlgebra.U,
        ActualThreeNodeFiniteAlgebra.T, ActualThreeNodeFiniteAlgebra.C,
        ActualThreeNodeFiniteAlgebra.O]
      <;> ring

lemma mixed_div_real (p s : ℂ) (u v : ℝ) :
    mixed (p / (u : ℂ)) (s / (v : ℂ)) = mixed p s / (u * v) := by
  simp [mixed, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.mul_im]
  <;> ring

lemma norm_div_sqrt_sq (p : ℂ) {d : ℝ} (hd : 0 ≤ d) :
    ‖p / (Real.sqrt d : ℂ)‖ ^ 2 = ‖p‖ ^ 2 / d := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd]

def finiteForm (g mu a r : ℝ) (x : Fin 3 → ℂ) : ℝ :=
  U₃ g mu a r / 3 * ‖x 0‖ ^ 2 + O₃ g mu a r * ‖x 1‖ ^ 2 +
    C₃ g mu a r / 6 * ‖x 2‖ ^ 2 +
    2 * (T₃ g mu a r / Real.sqrt 18) * mixed (x 0) (x 2)

def finiteMatrix (g mu a r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((U₃ g mu a r / 3 : ℝ) : ℂ), 0, ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ);
      0, (O₃ g mu a r : ℂ), 0;
      ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ), 0, ((C₃ g mu a r / 6 : ℝ) : ℂ)]

lemma finiteMatrix_form (g mu a r : ℝ) (x : Fin 3 → ℂ) :
    star x ⬝ᵥ (finiteMatrix g mu a r *ᵥ x) = (finiteForm g mu a r x : ℂ) := by
  apply Complex.ext
  all_goals
    simp [finiteMatrix, finiteForm, mixed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.star_apply, Complex.star_def, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring

lemma finiteMatrix_isHermitian (g mu a r : ℝ) :
    (finiteMatrix g mu a r).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteMatrix, Matrix.conjTranspose_apply]

/-- Physical finite-energy realization in the ORIGINAL orthonormal metric. -/
theorem actual_finite_energy_form {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (x : Fin 3 → ℂ) :
    pairedEnergy c
        (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))
        (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) =
      finiteForm (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
  rw [sourceHead_eq_rawHead]
  rcases actual_raw_reciprocals hn c N hN
      (x 0 / (Real.sqrt 3 : ℂ)) (x 1 / (Real.sqrt 2 : ℂ))
      (x 2 / (Real.sqrt 6 : ℂ)) with ⟨hA, hB⟩
  rw [hA, hB, raw_pairedEnergy]
  rw [norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 3),
    norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 2),
    norm_div_sqrt_sq _ (by norm_num : (0 : ℝ) ≤ 6), mixed_div_real]
  have hs : Real.sqrt (3 : ℝ) * Real.sqrt 6 = Real.sqrt 18 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hs]
  unfold finiteForm
  ring

theorem actual_finite_matrix_realization {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)
    (x : Fin 3 → ℂ) :
    star x ⬝ᵥ (finiteMatrix (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) *ᵥ x) =
      (pairedEnergy c
        (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))
        (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) : ℂ) := by
  rw [finiteMatrix_form, actual_finite_energy_form hn c N hN]

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteEnergy
