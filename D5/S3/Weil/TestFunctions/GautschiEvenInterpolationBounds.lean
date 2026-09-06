/- GID: D5/S3/Weil/TestFunctions/GautschiEvenInterpolationBounds
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/GautschiEvenInterpolationBounds
   mirror-E: none(waiver:finite-interpolation-conditioning)
   anchors: []
   digest: Bound the existing Lagrange basis on squared complex nodes using explicit nodal radii and certified squared-node gaps. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Gautschi-type bounds for the actual even interpolation polynomial

Reference: W. Gautschi, On inverses of Vandermonde and confluent Vandermonde
matrices, Numerische Mathematik 4 (1962), 117-123, Section 2 (2.1) and
Theorem 1 (3.1). The same product of numerator radii and inverse node gaps
bounds the Lagrange basis used by the existing Weil interpolation owner.

This specialization uses nodes z_i^2. Consequently separation from both
z_j and -z_j is necessary. All bounds below are estimates for Mathlib's
Lagrange.basis/interpolate, rather than a parallel interpolation definition.
No uniform conditioning near colliding squared nodes is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.TestFunctions.GautschiEvenInterpolationBounds

open Polynomial
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- A finite arithmetic product; rational radii and gaps give a rational bound. -/
def squaredNodeBudget (s : Finset ι) (radius : ι → ℝ)
    (gap : ι → ι → ℝ) (R : ℝ) (i : ι) : ℝ :=
  ∏ j ∈ s.erase i, (R ^ 2 + radius j ^ 2) / gap i j

private theorem divisor_norm_le
    (x y w : ℂ) (R A d : ℝ)
    (hw : ‖w‖ ≤ R) (hy : ‖y‖ ≤ A)
    (hd : 0 < d) (hgap : d ≤ ‖x ^ 2 - y ^ 2‖) :
    ‖(Lagrange.basisDivisor (x ^ 2) (y ^ 2)).eval (w ^ 2)‖ ≤
      (R ^ 2 + A ^ 2) / d := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have hA : 0 ≤ A := (norm_nonneg _).trans hy
  have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg w) hR).2 hw
  have hy2 : ‖y‖ ^ 2 ≤ A ^ 2 := (sq_le_sq₀ (norm_nonneg y) hA).2 hy
  have hnum : ‖w ^ 2 - y ^ 2‖ ≤ R ^ 2 + A ^ 2 := by
    calc
      _ ≤ ‖w ^ 2‖ + ‖y ^ 2‖ := norm_sub_le _ _
      _ = ‖w‖ ^ 2 + ‖y‖ ^ 2 := by rw [norm_pow, norm_pow]
      _ ≤ _ := add_le_add hw2 hy2
  have heval : (Lagrange.basisDivisor (x ^ 2) (y ^ 2)).eval (w ^ 2) =
      (w ^ 2 - y ^ 2) / (x ^ 2 - y ^ 2) := by
    simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
    ring
  rw [heval, norm_div]
  calc
    _ ≤ (R ^ 2 + A ^ 2) / ‖x ^ 2 - y ^ 2‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd hgap

/-- Actual cardinal polynomial control on any closed complex disk. -/
theorem lagrange_squared_basis_norm_le
    (s : Finset ι) (z : ι → ℂ) (radius : ι → ℝ)
    (gap : ι → ι → ℝ) (R : ℝ) (i : ι) (w : ℂ)
    (hw : ‖w‖ ≤ R)
    (hradius : ∀ j ∈ s, ‖z j‖ ≤ radius j)
    (hgapPos : ∀ j ∈ s.erase i, 0 < gap i j)
    (hgap : ∀ j ∈ s.erase i, gap i j ≤ ‖z i ^ 2 - z j ^ 2‖) :
    ‖(Lagrange.basis s (fun j => z j ^ 2) i).eval (w ^ 2)‖ ≤
      squaredNodeBudget s radius gap R i := by
  rw [Lagrange.basis, eval_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro j _
    exact norm_nonneg _
  · intro j hj
    exact divisor_norm_le (z i) (z j) w R (radius j) (gap i j) hw
      (hradius j (Finset.mem_of_mem_erase hj)) (hgapPos j hj) (hgap j hj)

/-- The product bound makes polynomial growth explicit outside the unit disk. -/
theorem squaredNodeBudget_le_growth
    (s : Finset ι) (radius : ι → ℝ) (gap : ι → ι → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (i : ι)
    (hgap : ∀ j ∈ s.erase i, 0 < gap i j) :
    squaredNodeBudget s radius gap R i ≤
      (R ^ 2) ^ (s.erase i).card * squaredNodeBudget s radius gap 1 i := by
  unfold squaredNodeBudget
  calc
    _ ≤ ∏ j ∈ s.erase i, R ^ 2 * ((1 ^ 2 + radius j ^ 2) / gap i j) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact div_nonneg (by positivity) (hgap j hj).le
      · intro j hj
        have hR2 : 1 ≤ R ^ 2 := by nlinarith
        have hprod := mul_nonneg (sub_nonneg.mpr hR2) (sq_nonneg (radius j))
        calc
          (R ^ 2 + radius j ^ 2) / gap i j ≤
              (R ^ 2 * (1 ^ 2 + radius j ^ 2)) / gap i j :=
            div_le_div_of_nonneg_right (by nlinarith) (hgap j hj).le
          _ = _ := by ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- An explicit bound for the existing interpolant after seed normalization. -/
theorem lagrange_squared_interpolate_norm_le
    (s : Finset ι) (z values seed : ι → ℂ) (radius : ι → ℝ)
    (gap : ι → ι → ℝ) (R mu : ℝ) (hmu : 0 < mu) (w : ℂ)
    (hw : ‖w‖ ≤ R)
    (hradius : ∀ j ∈ s, ‖z j‖ ≤ radius j)
    (hseed : ∀ i ∈ s, mu ≤ ‖seed i‖)
    (hgapPos : ∀ i ∈ s, ∀ j ∈ s.erase i, 0 < gap i j)
    (hgap : ∀ i ∈ s, ∀ j ∈ s.erase i, gap i j ≤ ‖z i ^ 2 - z j ^ 2‖) :
    ‖(Lagrange.interpolate s (fun j => z j ^ 2)
      (fun i => values i / seed i)).eval (w ^ 2)‖ ≤
      ∑ i ∈ s, (‖values i‖ / mu) * squaredNodeBudget s radius gap R i := by
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  calc
    _ ≤ ∑ i ∈ s, ‖(C (values i / seed i) *
        Lagrange.basis s (fun j => z j ^ 2) i).eval (w ^ 2)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [eval_mul, eval_C, norm_mul, norm_div]
      apply mul_le_mul
        (div_le_div_of_nonneg_left (norm_nonneg _) hmu (hseed i hi))
        (lagrange_squared_basis_norm_le s z radius gap R i w hw hradius
          (hgapPos i hi) (hgap i hi)) (norm_nonneg _) (by positivity)

/-- Squared-node separation factors through direct and reflected distances. -/
theorem squared_gap_factorization (z w : ℂ) :
    ‖z ^ 2 - w ^ 2‖ = ‖z - w‖ * ‖z + w‖ := by
  rw [show z ^ 2 - w ^ 2 = (z - w) * (z + w) by ring, norm_mul]

/-- Certified positive direct and reflected gaps give the gap used above. -/
theorem squared_gap_lower_bound (z w : ℂ) (d e : ℝ)
    (hd : 0 ≤ d) (he : 0 ≤ e)
    (hdist : d ≤ ‖z - w‖) (hreflect : e ≤ ‖z + w‖) :
    d * e ≤ ‖z ^ 2 - w ^ 2‖ := by
  rw [squared_gap_factorization]
  exact mul_le_mul hdist hreflect he (norm_nonneg _)

#print axioms lagrange_squared_basis_norm_le
#print axioms squaredNodeBudget_le_growth
#print axioms lagrange_squared_interpolate_norm_le
#print axioms squared_gap_factorization
#print axioms squared_gap_lower_bound

end D5.S3.Weil.TestFunctions.GautschiEvenInterpolationBounds
