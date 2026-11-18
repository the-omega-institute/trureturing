/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source
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
Original file: QuantumAlg/Primitives/QFT/Source.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Reverse
public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Primitive
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Primitive
public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
public import D5.S3.Quantum.FourierCircuit.Components.Gates.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Construction
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement

/-!
# The canonical recursive QFT in its natural gate model

Each stage executes one native Hadamard, its native controlled phases, and
the recursively placed tail. The final bit-reversal network consists of native
SWAP instructions. Compilation is a separate verified transformation of this
same source circuit.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

open QFTPrimitive (layout)

/-- Rotation angle at the supplied separation in one recursive QFT stage. -/
public def phaseAngle (offset : Nat) : Real :=
  2 * Real.pi / (2 : Real) ^ (offset + 2)

/-- One native controlled phase on the leading qubit and selected tail qubit. -/
public def phaseStep (oracles : OracleModel) (n : Nat) (offset : Fin n) :
    UnitaryCircuit FourierGate.model oracles (layout (n + 1)) :=
  (QFTPrimitive.controlledPhase 0 offset.succ (phaseAngle offset.val)
    (by intro same; have value := congrArg Fin.val same; simp at value)).sourceCircuit oracles

/-- The first supplied number of controlled phases, in their original order. -/
public def phasePrefix (oracles : OracleModel) (n : Nat) :
    (count : Nat) → count ≤ n → UnitaryCircuit FourierGate.model oracles (layout (n + 1))
  | 0, _ => UnitaryCircuit.identity FourierGate.model oracles (layout (n + 1))
  | count + 1, bounded =>
      (phasePrefix oracles n count (Nat.le_of_succ_le bounded)).seq
        (phaseStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩)

/-- The full controlled-phase layer of a recursive stage. -/
public def phaseLayer (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit FourierGate.model oracles (layout (n + 1)) :=
  phasePrefix oracles n n le_rfl

/-- One native Hadamard instruction on the leading register position. -/
public def leadingHadamard (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit FourierGate.model oracles (layout (n + 1)) :=
  UnitaryCircuit.native (GateModel.Application.ofPositions FourierGate.model .hadamard
    (layout (n + 1))
    ⟨fun _ : Fin 1 => 0, fun _ _ _ => Subsingleton.elim (α := Fin 1) _ _⟩
    (fun _ => rfl))

/-- Place an existing tail circuit after the leading qubit without allocating any system. -/
public def tailLayer (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (layout n)) :
    UnitaryCircuit FourierGate.model oracles (layout (n + 1)) :=
  UnitaryCircuit.placeAt (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) body

/-- Recursive construction before its final wire reversal. -/
public def noSwap (oracles : OracleModel) :
    (n : Nat) → UnitaryCircuit FourierGate.model oracles (layout n)
  | 0 => UnitaryCircuit.identity FourierGate.model oracles (layout 0)
  | n + 1 => (leadingHadamard oracles n).seq
      ((phaseLayer oracles n).seq (tailLayer oracles n (noSwap oracles n)))

/-- The complete canonical source circuit, including the final wire reversal. -/
public def circuit (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  (noSwap oracles n).seq (bitReverse oracles n)

end

end QuantumAlg.QuantumFourierTransform.Source
