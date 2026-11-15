/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Realization.lean.
Authors: QudeLeap Team
-/
module
import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Construction
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.OperatorNorm
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.OperatorNorm
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
/-!
# Realizations in a declared target language
A realization contains an actual target-model circuit on the specified physical
layout and its exact-phase equality or operator-norm error bound. Every resource
observation is derived from that circuit. Sequencing and repetition reuse real
constructions. Adjoint realization additionally consumes an actual target-model
implementation of the adjoint, with no automatic inverse-gate capability.
-/
section
namespace QuantumAlg
namespace UnitaryCircuit
noncomputable section
variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}


namespace ExactRealization
variable {target : oracles.Interpretation → UnitaryOperator layout.register}


end ExactRealization
namespace ApproxRealization
variable {target : oracles.Interpretation → UnitaryOperator layout.register} {ε : ℝ}


end ApproxRealization
end
end UnitaryCircuit
end QuantumAlg
end
