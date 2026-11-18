/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive
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
Original file: QuantumAlg/Primitives/QFT/Primitive.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.QubitRegister
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.QubitRegister
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Swap.QubitRegister
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap.QubitRegister

/-!
# Native realizations of QFT subroutines

Controlled phases and swaps keep their original addressed target operators.
Their executable realizations retain the complete native expansion.
-/

namespace QuantumAlg

noncomputable section

/-- The only non-Hadamard primitive kinds used by the recursive QFT circuit. -/
public inductive QFTPrimitive (n : Nat) where
  /-- One addressed controlled phase with its semantic angle. -/
  | controlledPhase (control target : Fin n) (angle : Real)
      (hne : control ≠ target)
  /-- One addressed wire swap. -/
  | swap (left right : Fin n) (hne : left ≠ right)

namespace QFTPrimitive

/-- Certified operator denoted by one QFT primitive. -/
public def operator {n : Nat} : QFTPrimitive n → UnitaryOperator (Qubits n)
  | .controlledPhase control target angle _ =>
      qftControlledPhaseOperator control target angle
  | .swap left right hne => qftSwapOperator left right hne

/-- The same canonical ordered qubit register for both QFT subroutines. -/
@[expose, implicit_reducible]
public def layout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

end QFTPrimitive

end

end QuantumAlg
