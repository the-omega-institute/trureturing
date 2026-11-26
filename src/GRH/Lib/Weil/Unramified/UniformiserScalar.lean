import GRH.Lib.ClassField.HeckeL.AutCharLFunction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Scalar by which a uniformiser acts in the Weil representation. -/

/-- The complex number χ(ϖ_w)·q_w^{k/2}, where χ = `AutChar.spaceChar` a k is the Hecke character x
↦ a(x/x̄)υ(x)^{−k} and ϖ_w the chosen uniformiser at w. -/
noncomputable def AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E) n
    [Fintype n] w := (a.spaceChar (Fintype.card n)).atUnif w * √w.q ^ Fintype.card n
