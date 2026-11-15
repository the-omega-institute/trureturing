/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Placement/Entries.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Selection

/-!
# Actual basis entries of a placed native word

The entry formula reads the requested ambient positions in their original
argument order and retains equality of every complementary coordinate. The
auxiliary extension of physical addresses has no observable role in this
formula. Spectator values need not be initialized or separable.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable {gates : GateModel} {oracles : OracleModel}
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

/-- Read the selected coordinates, casting only by their certified dimension equalities. -/
public def selectedInput (basis : target.Basis) : source.Basis :=
  fun index => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (dimensions index).symm)
    (basis (position index))

/-- Every placed matrix entry has exactly the original action and the untouched complement. -/
public lemma operatorAt_entry (operator : UnitaryOperator source.register)
    (row column : target.Basis) :
    operatorAt source target position dimensions operator row column =
      operator (selectedInput source target position dimensions row)
        (selectedInput source target position dimensions column) *
          (if target.restrictComplementBasis (Finset.univ.map position) row =
            target.restrictComplementBasis (Finset.univ.map position) column then 1 else 0) := by
  have selected (basis : target.Basis) :
      ((relocatedPlacement source target position dimensions).splitBasis basis).1 =
        selectedInput source target position dimensions basis := by
    funext index
    apply Fin.ext
    rfl
  refine ((relocatedPlacement source target position dimensions).liftOperator_entry
    operator row column).trans ?_
  rw [selected row, selected column]
  rfl


end

end QuantumAlg.UnitaryCircuit
