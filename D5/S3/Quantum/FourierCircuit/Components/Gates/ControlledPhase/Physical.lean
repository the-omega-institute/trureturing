/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Physical
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Physical
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
Original file: QuantumAlg/Components/Gates/ControlledPhase/Physical.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase.Construction
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Exact native ControlledPhase placement

The independently defined local operator acts on the selected two physical wires.
Every spectator keeps its original coordinate and dimension.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

variable {count : Nat} (ambient : QuantumLayout count)
variable (control target : Fin count) (distinct : control ≠ target)
variable (controlQubit : (ambient.wire control).dimension = 2)
variable (targetQubit : (ambient.wire target).dimension = 2)

private def positions : Fin 2 ↪ Fin count where
  toFun := ![control, target]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

include controlQubit targetQubit in
private lemma dimensions (index : Fin 2) :
    (layout.wire index).dimension =
      (ambient.wire (positions control target distinct index)).dimension := by
  fin_cases index
  · exact controlQubit.symm
  · exact targetQubit.symm

/-- Place the independent exact controlled-phase target on the two requested physical wires. -/
public def placedOperator (angle : Real) : UnitaryOperator ambient.register :=
  UnitaryCircuit.operatorAt layout ambient (positions control target distinct)
    (dimensions ambient control target distinct controlQubit targetQubit) (operator angle)

end

end QuantumAlg.Gate.ControlledPhase
