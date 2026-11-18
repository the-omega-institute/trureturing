import D5.S3.Arith.Lattices.CofactorKernel

/-! Positive source laws for expansion along the adjoined row and for right
multiplication of the signed cofactor vector. The telescope includes every
commutative ring at the source universe, every dimension, and the full
matrices and row. The dependent realization and enrolled readout across
the ring family, exact reconstruction, source selection, whole-family
variation, sensitivity and dependence remain open under issue #31456. -/

namespace Reg.D5.S3.Arith.Lattices.CofactorKernel

universe u

abbrev det_topRow_scope.{u} :=
  type_of% (@_root_.D5.S3.Arith.Lattices.CofactorKernel.det_topRow.{u})

theorem det_topRow_actual.{u} : det_topRow_scope.{u} :=
  @_root_.D5.S3.Arith.Lattices.CofactorKernel.det_topRow.{u}

abbrev cofactor_mul_right_cross_scope.{u} :=
  type_of% (@_root_.D5.S3.Arith.Lattices.CofactorKernel.cofactor_mul_right_cross.{u})

theorem cofactor_mul_right_cross_actual.{u} : cofactor_mul_right_cross_scope.{u} :=
  @_root_.D5.S3.Arith.Lattices.CofactorKernel.cofactor_mul_right_cross.{u}

end Reg.D5.S3.Arith.Lattices.CofactorKernel
