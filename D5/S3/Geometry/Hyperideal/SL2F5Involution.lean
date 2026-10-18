/- GID: D5/S3/Geometry/Hyperideal/SL2F5Involution
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/SL2F5Involution
   mirror-E: none(waiver:finite-field-involution)
   anchors: []
   utility: none
   digest: In determinant-one two by two matrices over ZMod 5, a square-one element is I or -I. -/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Defs

open scoped MatrixGroups

namespace D5.S3.Geometry.Hyperideal.SL2F5Involution

/-! The finite-field calculation behind the center-lift obstruction in CFMP §124.2. -/

theorem sl2_zmod5_square_one_eq_one_or_neg_one :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5),
      A ^ 2 = 1 → A = 1 ∨ A = -1 := by
  set_option maxRecDepth 100000 in
    decide

end D5.S3.Geometry.Hyperideal.SL2F5Involution
