/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive
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
Original file: QuantumAlg/Primitives/QFT/Source/Primitive.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.GateModel.Fourier
import all D5.S3.Quantum.FourierCircuit.Components.GateModel.Fourier
public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Construction
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization.Native
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.QubitRegister
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap.QubitRegister

/-!
# Addressed native Fourier instructions

Every source instruction selects its actual physical wires. The matrix laws
identify the full addressed operators, including every spectator coordinate.
-/

namespace QuantumAlg.QFTPrimitive
noncomputable section

private def positions {n : Nat} (first second : Fin n) (distinct : first ≠ second) :
    Fin 2 ↪ Fin n where
  toFun := ![first, second]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

/-- One actual native source instruction on the declared pair of qubits. -/
public def sourceCircuit {n : Nat} (primitive : QFTPrimitive n) (oracles : OracleModel) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  match primitive with
  | .controlledPhase control target angle distinct =>
      .native (GateModel.Application.ofPositions FourierGate.model (.controlledPhase angle)
        (layout n) (positions control target distinct) (fun _ => rfl))
  | .swap left right distinct =>
      .native (GateModel.Application.ofPositions FourierGate.model .swap
        (layout n) (positions left right distinct) (fun _ => rfl))

/-- The primitive source gate has exactly the original addressed QFT operator. -/
public lemma qftPrimitive_sourceCircuit_matrix (oracles : OracleModel) {n : Nat}
    (primitive : QFTPrimitive n)
    (environment : oracles.Interpretation) :
    ((primitive.sourceCircuit oracles).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm primitive.operator := by
  cases primitive with
  | controlledPhase control target angle distinct =>
      rw [sourceCircuit, UnitaryCircuit.native_matrix,
        ← UnitaryCircuit.nativeApplication_operatorAt]
      exact Gate.ControlledPhase.controlledPhase_qubitOperator_matrix
        control target distinct angle
  | swap left right distinct =>
      rw [sourceCircuit, UnitaryCircuit.native_matrix,
        ← UnitaryCircuit.nativeApplication_operatorAt]
      exact Gate.Swap.swap_qubitOperator_matrix left right distinct

end
end QuantumAlg.QFTPrimitive
