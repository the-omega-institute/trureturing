/- GID: D5/S3/Geometry/Hyperideal/LengthGramUnitNormals
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramUnitNormals
   mirror-E: none(waiver:unit-normal)
   anchors: []
   utility: none
   digest: Inverse-Gram dual normals become unit Lorentz normals after positive normalization. -/

import D5.S3.Geometry.Hyperideal.LengthGramDualMetric
import D5.S3.Geometry.Hyperideal.LengthGramInverseDiagonal
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramDualPairing
open D5.S3.Geometry.Hyperideal.LengthGramDualMetric
open D5.S3.Geometry.Hyperideal.LengthGramInverseDiagonal
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramUnitNormals

def unitDualNormal (G M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun k => (-1 / Real.sqrt (G⁻¹ i i)) * dualVector G M i k

theorem dual_unit_normal
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j,
      lorentz (M i) (M j) = lengthGram l i j)
    (hl : ∀ k, 0 < l k) (hdet : (lengthGram l).det < 0) (i : Fin 4) :
    lorentz (unitDualNormal (lengthGram l) M i)
      (unitDualNormal (lengthGram l) M i) = 1 := by
  have hd : 0 < (lengthGram l)⁻¹ i i :=
    inverse_diagonal_pos l hl hdet i
  have hs : 0 < Real.sqrt ((lengthGram l)⁻¹ i i) := Real.sqrt_pos.mpr hd
  have hs_sq : (Real.sqrt ((lengthGram l)⁻¹ i i)) ^ 2 = (lengthGram l)⁻¹ i i :=
    Real.sq_sqrt hd.le
  have hscale (x y : Fin 4 → ℝ) (c d : ℝ) :
      lorentz (fun k => c * x k) (fun k => d * y k) =
        c * d * lorentz x y := by
    unfold lorentz
    calc
      ∑ k, ![(1 : ℝ), 1, 1, -1] k * (c * x k) * (d * y k) =
          ∑ k, c * d * (![ (1 : ℝ), 1, 1, -1] k * x k * y k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = c * d * ∑ k, ![(1 : ℝ), 1, 1, -1] k * x k * y k := by
        rw [Finset.mul_sum]
  calc
    lorentz (unitDualNormal (lengthGram l) M i)
        (unitDualNormal (lengthGram l) M i) =
      (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) *
          (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) *
          lorentz (dualVector (lengthGram l) M i)
            (dualVector (lengthGram l) M i) := by
      apply hscale
    _ = (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) *
          (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) *
          (lengthGram l)⁻¹ i i := by
      rw [dual_metric l M hM hdet i i]
    _ = 1 := by
      field_simp [ne_of_gt hs]
      nlinarith

/- The cap rows are unit directly from the diagonal of the realizing Gram matrix.
   This is kept as a local exact consequence of the realizing hypothesis rather
   than a second tracked specialization. -/
example
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j,
      lorentz (M i) (M j) = lengthGram l i j) (i : Fin 4) :
    lorentz (M i) (M i) = 1 := by
  calc
    lorentz (M i) (M i) = lengthGram l i i := hM i i
    _ = 1 := by fin_cases i <;> simp [lengthGram]

#print axioms dual_unit_normal
end D5.S3.Geometry.Hyperideal.LengthGramUnitNormals
