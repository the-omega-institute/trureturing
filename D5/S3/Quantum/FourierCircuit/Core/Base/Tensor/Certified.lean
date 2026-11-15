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
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Core/Base/Tensor/Certified.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import D5.S3.Quantum.FourierCircuit.Core.Base.Tensor.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Tensor.Basic

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
ne_mul])
 (Qubits m))
        (φ : HilbertVector (Qubits n)) := rfl
.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl
 y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

    · rw [if_neg h2, mul_zero]
s m))‖ * ‖(φ : HilbertVector (Qubits n))‖
  rw [HilbertVector.norm_tensor]
 n)) (φ' : HilbertVector (Qubits n))
  rw [HilbertVector.inner_tensor_tensor]

end

end NormalizedVector

namespace HilbertVector

noncomputable section
fun index => left index.1 * right index.2
rodTensor left right index = left index.1 * right index.2 :=
  rfl
 fun rightIndex _ => ?_
  rw [norm_mul, mul_pow]
    · simp [NormalizedVector.ket_apply, same, rightDifferent]

end

end HilbertVector

namespace NormalizedVector

noncomputable section
rm_prodTensor, left.norm_eq_one, right.norm_eq_one, one_mul])
rodTensor left right index = left index.1 * right index.2 :=
  rfl

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
dexEquiv R S)
        ((U : HilbertOperator R) ⊗ₖ (V : HilbertOperator S)) := rfl

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
o sourceRight _
  ring
, hU, hV,
        Matrix.one_kronecker_one, Matrix.submatrix_one_equiv])
or (Qubits m))
        (V : HilbertOperator (Qubits n)) := rfl
  V (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl
 (U : HilbertOperator (Qubits m))
    (V : HilbertOperator (Qubits n)) ψ φ
w [HilbertOperator.tensor_applyVec_tensor]

end

end UnitaryOperator

end QuantumAlg

end
