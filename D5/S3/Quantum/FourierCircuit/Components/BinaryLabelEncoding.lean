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
t basis labels. -/
  encode_injective : Function.Injective encode

namespace BinaryLabelEncoding
imp at h <;> rfl
:= layout.injective
encoding.encode_injective h
belEncoding (Fin (2 ^ n)) :=
  ofEquiv (Equiv.refl (Fin (2 ^ n)))
grArg E.decode h
    simpa using hdecode
grArg E.decode h
    simpa using hdecode
      (right.encode_injective (congrArg Prod.snd hpair))
grArg Fin.val h
    simpa using hval
a ≃ Fin (2 ^ n)) : (ofEquiv layout).width = n := rfl
: Data) : (ofEquiv layout).encode x = layout x := rfl
 Data) :
    (encoding.relabel layout).width = encoding.width := rfl
er) :
    (encoding.relabel layout).encode x = encoding.encode (layout x) := rfl
l
at) (x : Fin (2 ^ n)) :
    (finIdentity n).encode x = x := rfl
l
l
l
 : Nat} (E : BinaryResidueEncoding N n) :
    (ofResidueEncoding E).width = n := rfl
Encoding N n)
    (z : ZMod N) : (ofResidueEncoding E).encode z = E.encode z := rfl
t).width = left.width + right.width := rfl
code x = prodEquiv (left.encode x.1, right.encode x.2) := rfl
g.encode x = encoding.encode y) : x = y :=
  encoding.encode_injective h

end BinaryLabelEncoding

end

end QuantumAlg

end
