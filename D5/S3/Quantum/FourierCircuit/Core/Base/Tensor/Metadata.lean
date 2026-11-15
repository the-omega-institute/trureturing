/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Metadata
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Tensor/Metadata
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
Original file: QuantumAlg/Core/Base/Tensor/Metadata.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Pure
import all D5.S3.Quantum.FourierCircuit.Core.Base.Tensor.Certified

/-!
# Metadata-aware tensor adapters

Placed states reuse the certified mathematical tensor product while composing
their physical placement metadata. Preparation resources stay with executable
preparation evidence.
-/

section

namespace QuantumAlg

variable {m n : ℕ}

namespace PureState

noncomputable section

/-- Tensor product of placed pure states. -/
def tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    PureState (Qubits (m + n)) :=
  ofNormalized (ψ.state.tensor φ.state)
    (ψ.system_idx ++ φ.system_idx)

@[simp]
lemma coe_tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    ((ψ.tensor φ : PureState (Qubits (m + n))) : HilbertVector (Qubits (m + n))) =
      HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)) := rfl

@[simp]
lemma tensor_system_idx (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    (ψ.tensor φ).system_idx = ψ.system_idx ++ φ.system_idx := rfl

@[simp]
lemma tensor_apply (ψ : PureState (Qubits m)) (φ : PureState (Qubits n))
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

lemma tensor_apply_prod (ψ : PureState (Qubits m)) (φ : PureState (Qubits n))
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

/-- Placed basis states tensor by composing their labels and placements. -/
lemma tensor_basis (x : Fin (2 ^ m)) (y : Fin (2 ^ n))
    (leftSystem rightSystem : List Nat) :
    (basis x leftSystem).tensor (basis y rightSystem) =
      basis (prodEquiv (x, y)) (leftSystem ++ rightSystem) := by
  apply PureState.ext
  · intro i
    change (NormalizedVector.ket x).tensor (NormalizedVector.ket y) i =
      NormalizedVector.ket (prodEquiv (x, y)) i
    rw [NormalizedVector.tensor_ket]
  · rfl

lemma norm_tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  change
    ‖HilbertVector.tensor (ψ : HilbertVector (Qubits m))
      (φ : HilbertVector (Qubits n))‖ =
      ‖(ψ : HilbertVector (Qubits m))‖ * ‖(φ : HilbertVector (Qubits n))‖
  rw [HilbertVector.norm_tensor]

lemma inner_tensor_tensor (ψ ψ' : PureState (Qubits m))
    (φ φ' : PureState (Qubits n)) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ') =
      inner ℂ ψ ψ' * inner ℂ φ φ' := by
  change inner ℂ
      (HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)))
      (HilbertVector.tensor (ψ' : HilbertVector (Qubits m))
        (φ' : HilbertVector (Qubits n))) =
    inner ℂ (ψ : HilbertVector (Qubits m)) (ψ' : HilbertVector (Qubits m)) *
      inner ℂ (φ : HilbertVector (Qubits n)) (φ' : HilbertVector (Qubits n))
  rw [HilbertVector.inner_tensor_tensor]

end

end PureState

end QuantumAlg

end
