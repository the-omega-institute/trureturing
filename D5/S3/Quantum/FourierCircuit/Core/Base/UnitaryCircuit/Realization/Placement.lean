/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Realization/Placement.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Physical
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
public import D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Model

import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Construction
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Exact realizations on a larger physical layout

Embedding an actual native word preserves its operator equality and all native
occurrences. The target operator acts by identity on the complementary systems.
No initialized-spectator assumption or additional native capability is needed.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- The embedded circuit acts by the physical embedding of its original operator. -/
public lemma embed_matrix (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) (environment : oracles.Interpretation) :
    ((body.embed placement).matrix environment) = placement.liftOperator (body.matrix environment)
      := by
  simp only [embed, matrix, UnitarySequence.toUnitary]

/-- Embedding retains every native occurrence, including expanded macro bodies. -/
public lemma embed_eventTrace (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) :
    (body.embed placement).eventTrace = body.eventTrace := by
  simp only [embed, eventTrace, UnitarySequence.eventTrace]


namespace ExactRealization


end ExactRealization

end

end QuantumAlg.UnitaryCircuit
