/- GID: D5/S3/Quantum/FourierCircuit/Components/BinaryLabelEncoding
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/BinaryLabelEncoding
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
Original file: QuantumAlg/Components/BinaryLabelEncoding.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
public import D5.S3.Quantum.FourierCircuit.Util.FinPow
import all D5.S3.Quantum.FourierCircuit.Util.ResidueEncoding
public import Mathlib.Algebra.Order.Monoid.NatCast

/-!
# Binary computational-basis encodings

This Components-layer module defines faithful binary encodings shared by the
sealed qubit gate set and its encoded-bit lemma libraries.  Model-independent
wire-address operations live in Core.
-/

section

namespace QuantumAlg

noncomputable section


namespace BinaryLabelEncoding


end BinaryLabelEncoding

end

end QuantumAlg

end
