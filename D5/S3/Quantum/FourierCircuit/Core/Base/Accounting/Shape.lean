/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/Shape
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Accounting/Shape
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
Original file: QuantumAlg/Core/Base/Accounting/Shape.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import Mathlib.Data.PNat.Defs
import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Log

/-!
# Closed classical storage shapes

`CShape` is the closed vocabulary from which proof-level classical storage is
derived.  Constructors carry only structural dimensions.  In particular, the
residue and elliptic-curve constructors describe canonical encodings; modulus,
curve, and value semantics belong to their later typed carriers rather than to
an arbitrary caller-supplied footprint.
-/

section

namespace QuantumAlg

/-- Closed shapes admitted by typed classical storage and instructions. -/
public inductive CShape where
  /-- No runtime bits. -/
  | unit
  /-- The canonical one-bit proof-level storage unit. -/
  | bit
  /-- One finite classical value; positivity provides an initial value. -/
  | finite (cardinality : ℕ+)
  /-- A fixed sequence of bits. -/
  | bits (count : Nat)
  /-- An unsigned fixed-width word. -/
  | unsignedWord (width : Nat)
  /-- A bounded signed fixed-width word. -/
  | boundedSignedWord (width : Nat)
  /-- A tag bit followed by storage reserved for the fixed payload encoding. -/
  | option (payload : CShape)
  /-- Adjacent encodings of two values. -/
  | product (left right : CShape)
  /-- A fixed-length vector of one fixed element shape. -/
  | fixedVector (length : Nat) (element : CShape)
  /-- A canonical residue encoded in the stated word width. -/
  | canonicalResidue (modulusWidth : Nat)
  /-- A proof-carrying unit residue; the proof is erased at runtime. -/
  | unitResidue (modulusWidth : Nat)
  /-- An infinity tag and two fixed-width affine coordinates. -/
  | ellipticCurvePoint (fieldWidth : Nat)
deriving DecidableEq

namespace CShape


end CShape


end QuantumAlg

end
