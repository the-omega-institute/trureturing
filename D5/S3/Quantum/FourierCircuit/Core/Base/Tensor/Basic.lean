/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Basic
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Tensor/Basic
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
Original file: QuantumAlg/Core/Base/Tensor/Basic.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Util.FinPow
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Raw tensor products

This module defines tensor products for unrestricted state vectors and Hilbert
operators.  It makes no normalization or unitarity claim.
-/

section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace HilbertVector

noncomputable section
uiv.symm i).1 * φ (prodEquiv.symm i).2
ensor ψ φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl
 y := by
  rw [tensor_apply, Equiv.symm_apply_apply]
(ψ + ψ') φ i = (tensor ψ φ + tensor ψ' φ) i
  simp [add_mul]
(ψ - ψ') φ i = (tensor ψ φ - tensor ψ' φ) i
  simp [sub_mul]
 • ψ) φ i = (c • tensor ψ φ) i
  simp [mul_assoc]
ψ (φ + φ') i = (tensor ψ φ + tensor ψ φ') i
  simp [mul_add]
ψ (φ - φ') i = (tensor ψ φ - tensor ψ φ') i
  simp [mul_sub]
 φ) i = (c • tensor ψ φ) i
  simp [mul_left_comm]
φ i = (-tensor ψ φ) i
  simp [tensor_apply]
) i = (-tensor ψ φ) i
  simp [tensor_apply]
HilbertVector (Qubits m)) φ i = (0 : HilbertVector (Qubits (m + n))) i
  simp [tensor_apply]
: HilbertVector (Qubits n)) i = (0 : HilbertVector (Qubits (m + n))) i
  simp [tensor_apply]
fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]
ensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]

end

end HilbertVector

namespace HilbertOperator

noncomputable section
rix.reindex prodEquiv prodEquiv (G ⊗ₖ K)
* K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl
sor_apply]
sor_apply]
, add_mul]
, mul_add]
x.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]
   Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]
ker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]
ilbertVector.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]

end

end HilbertOperator

end QuantumAlg

end
