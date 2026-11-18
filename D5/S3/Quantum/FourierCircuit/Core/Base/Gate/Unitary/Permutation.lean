/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation
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
Original file: QuantumAlg/Core/Base/Gate/Unitary/Permutation.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator

/-!
# Exact permutation-operator calculus

Permutation matrices retain exact phase under composition and basis transport.
These mathematical identities introduce no executable gate, resource coordinate
or automatic inverse operation in a selected native language.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}

/-- A permutation matrix compares the image of the row with the column. -/
public lemma ofPerm_entry (permutation : Equiv.Perm R.Index) (row column : R.Index) :
    ofPerm permutation row column = if permutation row = column then 1 else 0 := by
  simp [ofPerm, ofMatrix, Equiv.toPEquiv_apply]

/-- Operator multiplication reverses the row-permutation composition order. -/
public lemma ofPerm_mul (first second : Equiv.Perm R.Index) :
    ofPerm first * ofPerm second = ofPerm (second * first) := by
  apply Subtype.ext
  exact (Matrix.permMatrix_mul second first).symm

end

end QuantumAlg.UnitaryOperator
