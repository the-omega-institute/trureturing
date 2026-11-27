/- GID: D5/S3/Zeros/GRH/Lib/Weil/Unramified/UniformiserScalar
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Unramified/UniformiserScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Unramified.UniformiserScalar. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Unramified/UniformiserScalar.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeL.AutCharLFunction
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Scalar by which a uniformiser acts in the Weil representation. -/

/-- The complex number χ(ϖ_w)·q_w^{k/2}, where χ = `AutChar.spaceChar` a k is the Hecke character x
↦ a(x/x̄)υ(x)^{−k} and ϖ_w the chosen uniformiser at w. -/
noncomputable def AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E) n
    [Fintype n] w := (a.spaceChar (Fintype.card n)).atUnif w * √w.q ^ Fintype.card n
