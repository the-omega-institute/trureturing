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

/-- Sequential execution retains every descriptive macro occurrence of both operands. -/
public lemma macroCount_seq (name : String) (left right : UnitaryCircuit gates oracles layout) :
    (left.seq right).macroCount name = left.macroCount name + right.macroCount name := by
  simp only [macroCount, seq, UnitarySequence.macroTrace, List.count_append]

/-- Parallel words retain the descriptive macro occurrences of both disjoint operands. -/
public lemma macroCount_parallel {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (name : String)
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    (parallel left right leftPlacement rightPlacement disjoint).macroCount name =
      left.macroCount name + right.macroCount name := by
  simp only [macroCount, parallel, UnitarySequence.macroTrace, List.count_append]

/-- Extending by untouched systems retains all descriptive occurrences of the actual word. -/
public lemma macroCount_embed {small large : Nat}
    {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) (name : String) :
    (body.embed placement).macroCount name = body.macroCount name := by
  simp only [macroCount, embed, UnitarySequence.macroTrace]

/-- Placing a complete word preserves its descriptive macro counts as well as its native events. -/
public lemma placeAt_macroCount {small large : Nat}
    (source : QuantumLayout small) (target : QuantumLayout large)
    (position : Fin small ↪ Fin large)
    (dimensions : ∀ index,
      (source.wire index).dimension = (target.wire (position index)).dimension)
    (body : UnitaryCircuit gates oracles source) (name : String) :
    (placeAt source target position dimensions body).macroCount name = body.macroCount name := by
  rw [placeAt, macroCount_embed, relabel_macroCount]

end QuantumAlg.UnitaryCircuit
