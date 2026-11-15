/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified
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
Original file: QuantumAlg/Core/Base/Tensor/Certified.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary

/-!
# Invariant-preserving tensor products

Tensoring normalized vectors preserves normalization, and tensoring unitary
operators preserves unitarity.  The certified values in this module carry no
physical placement or resource metadata.
-/

section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace NormalizedVector

noncomputable section


end

end NormalizedVector

namespace HilbertVector

noncomputable section


end

end HilbertVector

namespace NormalizedVector

noncomputable section


end

end NormalizedVector

namespace UnitaryOperator

noncomputable section

/-- Tensor product over arbitrary finite registers, indexed by their product register. -/
public def prodTensor {R S : Register} (U : UnitaryOperator R) (V : UnitaryOperator S) :
    UnitaryOperator (Register.prod R S) :=
  ofMatrix
    (Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
      ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S))) (by
    have hU := U.property
    have hV := V.property
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU hV ⊢
    rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
      ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv])


@[simp]
lemma prodTensor_apply {R S : Register} (U : UnitaryOperator R)
    (V : UnitaryOperator S) (i j : (Register.prod R S).Index) :
    prodTensor U V i j = U i.1 j.1 * V i.2 j.2 := by
  change
    (Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
      ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S))) i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-- Every product-register entry is the product of the two actual subsystem entries. -/
public lemma unitaryOperator_prodTensor_apply {R S : Register} (U : UnitaryOperator R)
    (V : UnitaryOperator S) (i j : (Register.prod R S).Index) :
    prodTensor U V i j = U i.1 j.1 * V i.2 j.2 :=
  prodTensor_apply U V i j


end

end UnitaryOperator

end QuantumAlg

end
