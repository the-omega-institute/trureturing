/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Control/Operator
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Fourier/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Core/Base/Control/Operator.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Matrix.Block

/-!
# Metadata-free controlled unitary operators

The constructions in this module depend only on certified mathematical operators.
Physical placement and resource annotations are added separately in `Control.Gate`.
-/

section

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}

/-- Reindexing both axes of a square matrix by one equivalence preserves
unitarity. -/
private lemma reindex_matrix_mem_unitaryGroup {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hM, Matrix.submatrix_one_equiv]

private lemma reindex_mem_unitaryGroup (e : R.Index ≃ S.Index)
    (U : UnitaryOperator R) :
    Matrix.reindex e e (U : HilbertOperator R) ∈
      Matrix.unitaryGroup S.Index ℂ := by
  exact reindex_matrix_mem_unitaryGroup e U U.property

/-- Transport a certified unitary operator along a register-index equivalence. -/
public def reindex (e : R.Index ≃ S.Index) (U : UnitaryOperator R) : UnitaryOperator S :=
  ofMatrix (Matrix.reindex e e (U : HilbertOperator R))
    (reindex_mem_unitaryGroup e U)


end

end QuantumAlg.UnitaryOperator

end
