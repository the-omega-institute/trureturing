/- GID: D5/S3/Quantum/Matrix/Spectral/TraceNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Spectral/TraceNorm
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: The canonical unnormalized finite matrix trace norm and its Hermitian Jordan mass. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
The trace norm definition is from the attributed Physlib transplant,
revision 6a09b2d1761a0d4430083045a247eb121d8da260, by Alex Meiburg,
released under Apache-2.0. The complete license is retained in
`D5/S3/Quantum/Foundation/FiniteTraceDistance.lean`.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Foundation.FiniteTraceDistance
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator Classical
variable {m n R : Type*} [Fintype m] [Fintype n] [RCLike R]
/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace


section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem trace_norm_jordan_mass (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceNorm A = (Matrix.trace (posPart A)).re + (Matrix.trace (negPart A)).re := by
  have h := congrArg (fun B : Matrix ι ι ℂ => (Matrix.trace B).re)
    (CFC.posPart_add_negPart A hA)
  simpa [Matrix.trace_add, CFC.abs, Matrix.star_eq_conjTranspose, traceNorm] using h.symm

end
end D5.S3.Quantum.Foundation.FiniteTraceDistance
