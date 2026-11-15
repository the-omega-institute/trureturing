/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Macros
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Macros
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Placement/Macros.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Physical
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence

/-!
# Descriptive macro counts under composition and placement

These observations count names in the actual construction tree. They neither
replace the retained native expansion nor determine its resource cost.
-/

namespace QuantumAlg.UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}


end QuantumAlg.UnitaryCircuit
