/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactBernstein
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bernstein lower bounds for sparse polynomials on the compact Taylor box. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Data.Rat.Cast.Lemmas

/-! Bernstein bounds for integer-coefficient polynomials in three normalized coordinates. -/

namespace RefinedBMV.PositiveCenter.CompactBernstein

open Finset Polynomial
open scoped Polynomial
open DimThree (evalTerms)
open DimThree.Certificate (Term)

private noncomputable def basis (D i : ℕ) (s : ℝ) : ℝ :=
  (D.choose i : ℝ) * s ^ i * (1 - s) ^ (D - i)

private theorem basis_nonneg {D i : ℕ} {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s ≤ 1) :
    0 ≤ basis D i s := by unfold basis; positivity

private theorem basis_sum (D : ℕ) (s : ℝ) : ∑ i ∈ range (D + 1), basis D i s = 1 := by
  have h := congrArg (Polynomial.eval s) (bernsteinPolynomial.sum ℝ D)
  simpa only [eval_finsetSum, bernsteinPolynomial, eval_mul, eval_pow, eval_natCast,
    eval_X, eval_sub, eval_one, basis] using h

private theorem basis_term {D j k : ℕ} (h : k + j ≤ D) (s : ℝ) :
    (((k + j).choose k : ℝ) / D.choose k) * basis D (k + j) s =
      s ^ k * basis (D - k) j s := by
  have hk : k ≤ D := by omega
  have hk' : (D.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have he : (((k + j).choose k : ℝ) / D.choose k) * (D.choose (k + j) : ℝ) =
      ((D - k).choose j : ℝ) := by
    have hb : (D.choose (k + j) : ℝ) * ((k + j).choose k : ℝ) =
        (D.choose k : ℝ) * ((D - k).choose j : ℝ) := by
      exact_mod_cast (by simpa using (Nat.choose_mul (Nat.le_add_right k j)))
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff hk').2 (by simpa only [mul_comm] using hb)
  calc
    _ = ((((k + j).choose k : ℝ) / D.choose k) * (D.choose (k + j) : ℝ)) *
        (s ^ (k + j) * (1 - s) ^ (D - (k + j))) := by unfold basis; ring
    _ = _ := by
      rw [he, pow_add, show D - (k + j) = D - k - j by omega]
      unfold basis
      ring

private theorem power_eq_bernstein {D k : ℕ} (hk : k ≤ D) (s : ℝ) :
    s ^ k = ∑ i ∈ range (D + 1), ((i.choose k : ℝ) / D.choose k) * basis D i s := by
  symm
  rw [show D + 1 = k + (D - k + 1) by omega, sum_range_add]
  have hzero : (∑ i ∈ range k, ((i.choose k : ℝ) / D.choose k) * basis D i s) = 0 := by
    exact sum_eq_zero fun i hi ↦ by simp [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
  rw [hzero, zero_add, ← mul_one (s ^ k), ← basis_sum (D - k) s, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjD : k + j ≤ D := by have := mem_range.mp hj; omega
  simpa only [add_comm j k] using basis_term hjD s

/-- Exact Bernstein coefficient of the shifted monomial `(2 * s - 1) ^ k`. -/
def shiftedCoefficient (D i k : ℕ) : ℚ :=
  ∑ j ∈ range (k + 1),
    (-1 : ℚ) ^ (k - j) * 2 ^ j * (k.choose j : ℚ) * (i.choose j : ℚ) / D.choose j

private theorem shiftedPower_eq_bernstein {D k : ℕ} (hk : k ≤ D) (s : ℝ) :
    (2 * s - 1) ^ k = ∑ i ∈ range (D + 1), (shiftedCoefficient D i k : ℝ) * basis D i s := by
  rw [sub_eq_add_neg, add_pow]
  simp only [shiftedCoefficient, Rat.cast_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hjD := (Nat.le_of_lt_succ (mem_range.mp hj)).trans hk
  rw [mul_pow, power_eq_bernstein hjD s]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro i _
  push_cast
  ring

/-- A coefficient in the tensor Bernstein representation on `[-1, 1]^3`. -/
def tensorCoefficient (terms : List Term) (D i j k : ℕ) : ℚ :=
  (terms.map fun a ↦ (a.coefficient : ℚ) *
    shiftedCoefficient D i a.exponents.1 *
    shiftedCoefficient D j a.exponents.2.1 *
    shiftedCoefficient D k a.exponents.2.2).sum

private noncomputable def tensorBasis (D i j k : ℕ) (s t u : ℝ) : ℝ :=
  basis D i s * basis D j t * basis D k u

private theorem tensorBasis_sum (D : ℕ) (s t u : ℝ) :
    (∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1), ∑ k ∈ range (D + 1),
      tensorBasis D i j k s t u) = 1 := by
  simp only [tensorBasis, ← mul_sum, basis_sum, mul_one]

private theorem tensor_eval_eq (terms : List Term) {D : ℕ}
    (hD : ∀ a ∈ terms, a.exponents.1 ≤ D ∧ a.exponents.2.1 ≤ D ∧ a.exponents.2.2 ≤ D)
    (s t u : ℝ) :
    evalTerms (2 * s - 1) (2 * t - 1) (2 * u - 1) terms =
      ∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1), ∑ k ∈ range (D + 1),
        (tensorCoefficient terms D i j k : ℝ) * tensorBasis D i j k s t u := by
  induction terms with
  | nil => simp [tensorCoefficient, evalTerms]
  | cons a terms ih =>
    have ha := hD a (List.mem_cons_self)
    have ht : ∀ b ∈ terms, b.exponents.1 ≤ D ∧ b.exponents.2.1 ≤ D ∧ b.exponents.2.2 ≤ D :=
      fun b hb ↦ hD b (List.mem_cons_of_mem a hb)
    have hc (i j k : ℕ) : tensorCoefficient (a :: terms) D i j k =
        (a.coefficient : ℚ) * shiftedCoefficient D i a.exponents.1 *
          shiftedCoefficient D j a.exponents.2.1 * shiftedCoefficient D k a.exponents.2.2 +
        tensorCoefficient terms D i j k := rfl
    change a.eval (2 * s - 1) (2 * t - 1) (2 * u - 1) +
      evalTerms (2 * s - 1) (2 * t - 1) (2 * u - 1) terms = _
    simp only [hc, Rat.cast_add, add_mul, sum_add_distrib]
    rw [ih ht]
    congr 1
    unfold Term.eval
    rw [shiftedPower_eq_bernstein ha.1, shiftedPower_eq_bernstein ha.2.1,
      shiftedPower_eq_bernstein ha.2.2]
    simp only [mul_sum, sum_mul, tensorBasis, Rat.cast_mul, Rat.cast_intCast]
    rw [sum_comm]
    conv_lhs =>
      arg 2
      ext j
      rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    ring

/-- The minimum tensor Bernstein coefficient bounds the polynomial on the centered unit box. -/
theorem le_evalTerms_of_coefficients (terms : List Term) {D : ℕ} {L : ℚ}
    (hD : ∀ a ∈ terms, a.exponents.1 ≤ D ∧ a.exponents.2.1 ≤ D ∧ a.exponents.2.2 ≤ D)
    (hL : ∀ i ≤ D, ∀ j ≤ D, ∀ k ≤ D, L ≤ tensorCoefficient terms D i j k)
    {s t u : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) (hu : |u| ≤ 1) :
    (L : ℝ) ≤ evalTerms s t u terms := by
  let x : ℝ := (s + 1) / 2
  let y : ℝ := (t + 1) / 2
  let z : ℝ := (u + 1) / 2
  rw [show s = 2 * x - 1 by dsimp [x]; ring,
    show t = 2 * y - 1 by dsimp [y]; ring,
    show u = 2 * z - 1 by dsimp [z]; ring, tensor_eval_eq terms hD]
  calc
    (L : ℝ) = ∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1), ∑ k ∈ range (D + 1),
        (L : ℝ) * tensorBasis D i j k x y z := by
      simp only [← mul_sum, tensorBasis_sum, mul_one]
    _ ≤ _ := by
      refine sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ sum_le_sum fun k hk ↦ ?_
      have hn : 0 ≤ tensorBasis D i j k x y z := by
        unfold tensorBasis
        obtain ⟨hs₀, hs₁⟩ := abs_le.mp hs
        obtain ⟨ht₀, ht₁⟩ := abs_le.mp ht
        obtain ⟨hu₀, hu₁⟩ := abs_le.mp hu
        exact mul_nonneg (mul_nonneg (basis_nonneg (by dsimp [x]; linarith)
          (by dsimp [x]; linarith)) (basis_nonneg (by dsimp [y]; linarith)
          (by dsimp [y]; linarith))) (basis_nonneg (by dsimp [z]; linarith)
          (by dsimp [z]; linarith))
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hL i (by simpa using hi) j (by simpa using hj) k (by simpa using hk)) hn

end RefinedBMV.PositiveCenter.CompactBernstein
