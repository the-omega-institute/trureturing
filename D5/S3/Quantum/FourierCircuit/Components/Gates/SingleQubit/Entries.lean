/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/SingleQubit/Entries
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/SingleQubit/Entries
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
Original file: QuantumAlg/Components/Gates/SingleQubit/Entries.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit

/-!
# Exact entries of a native one-qubit operation

The supplied operator acts on the selected dimension-two system. Every other
system remains unchanged, with no dimension or initialization restriction.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- Every native one-qubit entry retains the exact selected operator and full complement. -/
public lemma singleQubitAt_matrix_entry {count : Nat} (ambient : QuantumLayout count)
    (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (ambient.wire target).dimension = 2)
    (row column : ambient.Basis) (environment : oracles.Interpretation) :
    ((singleQubitAt ambient oracles operator target qubit).matrix environment) row column =
      operator
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (row target))
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (column target)) *
          (if ((singleQubitApplication ambient operator target qubit).basisEquiv row).2 =
            ((singleQubitApplication ambient operator target qubit).basisEquiv column).2
              then 1 else 0) := by
  let application := singleQubitApplication ambient operator target qubit
  have selected (basis : ambient.Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 =
        Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
    have coordinates : (application.basisEquiv basis).1 =
        fun _ => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) = bit
    fin_cases bit <;> rfl
  change application.operator row column = _
  rw [application.application_operator_entry]
  change operator
    (QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv row).1)
    (QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv column).1) *
      (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [selected row, selected column]
  rfl

end

end QuantumAlg.Gate
