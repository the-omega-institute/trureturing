/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical
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
Original file: QuantumAlg/Components/Gates/Swap/Physical.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.Swap
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Swap
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Exact native Swap placement

The independently defined local operator acts on the selected two physical wires.
Every spectator keeps its original coordinate and dimension.
-/

namespace QuantumAlg.Gate.Swap

noncomputable section

variable {count : Nat} (ambient : QuantumLayout count)
variable (left right : Fin count) (distinct : left ≠ right)
variable (leftQubit : (ambient.wire left).dimension = 2)
variable (rightQubit : (ambient.wire right).dimension = 2)

private def positions : Fin 2 ↪ Fin count where
  toFun := ![left, right]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

include leftQubit rightQubit in
private lemma dimensions (index : Fin 2) :
    (layout.wire index).dimension =
      (ambient.wire (positions left right distinct index)).dimension := by
  fin_cases index
  · exact leftQubit.symm
  · exact rightQubit.symm

/-- Place the independent exact SWAP target on the two requested physical wires. -/
public def placedOperator : UnitaryOperator ambient.register :=
  UnitaryCircuit.operatorAt layout ambient (positions left right distinct)
    (dimensions ambient left right distinct leftQubit rightQubit) operator

end

end QuantumAlg.Gate.Swap
