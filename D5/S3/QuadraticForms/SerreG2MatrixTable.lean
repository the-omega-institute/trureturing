/- GID: D5/S3/QuadraticForms/SerreG2MatrixTable
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SerreG2MatrixTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/QuadraticForms/SerreG2MatrixImage.serreMap_surjective; premises=D5/S3/QuadraticForms/SerreG2MatrixTable.bracket
   digest: Integral matrix relations for the seven-dimensional G2 representation. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility numeric-reduction: the integral bracket identities are discharged by kernel
reduction of scalar entries and consumed by actual Serre surjectivity, through
scalar extension, Lie closure, the Serre relations and the fourteen word images. These are classical G2 matrices. The evolution
algebra application credits Haobo Ma, then Wenlin Zhang; no priority is claimed.
-/

import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.SerreG2MatrixTable
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Two coroots and twelve root matrices with integral entries. -/
def basisMatrix (i : Fin 14) : Matrix (Fin 7) (Fin 7) ℤ :=
  ![
    !![1,0,0,0,0,0,0; 0,-1,0,0,0,0,0; 0,0,2,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,-2,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,-1],
    !![0,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,-1,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,-1,0; 0,0,0,0,0,0,0],
    !![0,1,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,2,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,1; 0,0,0,0,0,0,0],
    !![0,0,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0],
    !![0,0,1,0,0,0,0; 0,0,0,-2,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,-1; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0],
    !![0,0,0,-4,0,0,0; 0,0,0,0,2,0,0; 0,0,0,0,0,2,0; 0,0,0,0,0,0,-2; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0],
    !![0,0,0,0,6,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,-6; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0],
    !![0,0,0,0,0,-6,0; 0,0,0,0,0,0,-6; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0],
    !![0,0,0,0,0,0,0; 1,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,2,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,1,0],
    !![0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,0,0],
    !![0,0,0,0,0,0,0; 0,0,0,0,0,0,0; -1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,-2,0,0,0; 0,0,0,0,1,0,0],
    !![0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; -2,0,0,0,0,0,0; 0,2,0,0,0,0,0; 0,0,2,0,0,0,0; 0,0,0,-4,0,0,0],
    !![0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; -6,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,6,0,0,0,0],
    !![0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; 0,0,0,0,0,0,0; -6,0,0,0,0,0,0; 0,-6,0,0,0,0,0]
  ] i


/-- Integral structure constants in the displayed matrix basis. -/
def coefficients (i j : Fin 14) : Fin 14 → ℤ :=
  ![
    ![![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,2,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,-3,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,-1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,3,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,-2,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,3,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,-1,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,-3,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,-1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,2,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,-1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,-2,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,-1,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,-1]],
    ![![0,0,-2,0,0,0,0,0,0,0,0,0,0,0],![0,0,1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,3,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,4,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,3,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,3,0,0,0,0,0,0,0,0,0,0],![0,0,0,-2,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,-1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,1,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,-1,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0]],
    ![![0,0,0,0,1,0,0,0,0,0,0,0,0,0],![0,0,0,0,-1,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,-1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,-1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,-3,0,0,0,0,0,0,0,0,0,0],![0,0,1,0,0,0,0,0,0,0,0,0,0,0],![-1,-3,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,4,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,3,0,0]],
    ![![0,0,0,0,0,-1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,-1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,-4,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,-4,0,0,0,0,0,0,0,0,0,0,0],![8,12,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,-12,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,12,0,0,0]],
    ![![0,0,0,0,0,0,-3,0,0,0,0,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,-1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,-3,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,12,0,0,0,0,0,0,0,0,0,0,0],![-36,-36,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,36,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,-1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,-1,0,0,0,0,0,0,0],![0,0,0,0,0,-3,0,0,0,0,0,0,0,0],![0,0,0,0,-12,0,0,0,0,0,0,0,0,0],![0,0,0,-36,0,0,0,0,0,0,0,0,0,0],![36,72,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,2,0,0,0,0,0],![0,0,0,0,0,0,0,0,-1,0,0,0,0,0],![-1,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,3,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,4,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,3,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,-3,0,0,0,0],![0,0,0,0,0,0,0,0,0,2,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,-1,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,-1,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,-1,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,-1,0,0,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0],![0,0,0,0,0,0,0,0,0,-3,0,0,0,0],![0,0,0,0,0,0,0,0,1,0,0,0,0,0],![1,3,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,4,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,3,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,-1,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,-1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,-4,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,-4,0,0,0,0,0],![-8,-12,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,-12,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,12,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,-1,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,0,0,3,0],![0,0,0,0,0,0,0,0,0,0,0,0,-1,0],![0,0,0,0,0,0,0,0,0,0,0,-3,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,12,0,0,0,0,0],![36,36,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,36,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,-1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
    ![![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,1],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,-1,0],![0,0,0,0,0,0,0,0,0,0,0,-3,0,0],![0,0,0,0,0,0,0,0,0,0,-12,0,0,0],![0,0,0,0,0,0,0,0,0,-36,0,0,0,0],![-36,-72,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
  ] i j


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row0 (j : Fin 14) :
    ⁅basisMatrix 0, basisMatrix j⁆ =
      ∑ t, coefficients 0 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row1 (j : Fin 14) :
    ⁅basisMatrix 1, basisMatrix j⁆ =
      ∑ t, coefficients 1 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row2 (j : Fin 14) :
    ⁅basisMatrix 2, basisMatrix j⁆ =
      ∑ t, coefficients 2 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row3 (j : Fin 14) :
    ⁅basisMatrix 3, basisMatrix j⁆ =
      ∑ t, coefficients 3 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row4 (j : Fin 14) :
    ⁅basisMatrix 4, basisMatrix j⁆ =
      ∑ t, coefficients 4 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row5 (j : Fin 14) :
    ⁅basisMatrix 5, basisMatrix j⁆ =
      ∑ t, coefficients 5 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row6 (j : Fin 14) :
    ⁅basisMatrix 6, basisMatrix j⁆ =
      ∑ t, coefficients 6 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row7 (j : Fin 14) :
    ⁅basisMatrix 7, basisMatrix j⁆ =
      ∑ t, coefficients 7 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row8 (j : Fin 14) :
    ⁅basisMatrix 8, basisMatrix j⁆ =
      ∑ t, coefficients 8 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row9 (j : Fin 14) :
    ⁅basisMatrix 9, basisMatrix j⁆ =
      ∑ t, coefficients 9 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row10 (j : Fin 14) :
    ⁅basisMatrix 10, basisMatrix j⁆ =
      ∑ t, coefficients 10 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row11 (j : Fin 14) :
    ⁅basisMatrix 11, basisMatrix j⁆ =
      ∑ t, coefficients 11 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row12 (j : Fin 14) :
    ⁅basisMatrix 12, basisMatrix j⁆ =
      ∑ t, coefficients 12 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem bracket_row13 (j : Fin 14) :
    ⁅basisMatrix 13, basisMatrix j⁆ =
      ∑ t, coefficients 13 j t • basisMatrix t := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;> decide


/-- The full integral bracket table, proved by kernel reduction of scalar entries. -/
theorem bracket (i j : Fin 14) :
    ⁅basisMatrix i, basisMatrix j⁆ = ∑ t, coefficients i j t • basisMatrix t := by
  fin_cases i
  · exact bracket_row0 j
  · exact bracket_row1 j
  · exact bracket_row2 j
  · exact bracket_row3 j
  · exact bracket_row4 j
  · exact bracket_row5 j
  · exact bracket_row6 j
  · exact bracket_row7 j
  · exact bracket_row8 j
  · exact bracket_row9 j
  · exact bracket_row10 j
  · exact bracket_row11 j
  · exact bracket_row12 j
  · exact bracket_row13 j

end D5.S3.QuadraticForms.SerreG2MatrixTable
