/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling
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
Original file: QuantumAlg/Core/Base/Layout/Quantum/Relabeling.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum
public import Mathlib.Logic.Embedding.Basic

/-!
# Injective placement of existing finite-dimensional systems

A physical embedding changes the addresses at which the same systems are
placed. Every dimension, logical position and finite basis value is retained,
and distinct physical identities remain distinct. Native circuit placement
must use the same embedding; this descriptor performs no runtime operation.
-/

namespace QuantumAlg

namespace QuantumWire

/-- Place the same finite-dimensional system at its prescribed injective physical address. -/
@[expose] public def relabel (physical : Nat ↪ Nat) (wire : QuantumWire) : QuantumWire where
  identity := physical wire.identity
  dimension := wire.dimension


end QuantumWire

namespace QuantumLayout

variable {count : Nat}

/-- Every existing logical position receives its own injectively mapped physical identity. -/
@[expose] public def relabel (layout : QuantumLayout count)
    (physical : Nat ↪ Nat) : QuantumLayout count where
  wire index := QuantumWire.relabel physical (layout.wire index)
  identityInjective := fun _ _ equal => layout.identityInjective (physical.injective equal)


/-- Logical basis values retain the same finite dimension at every original position. -/
@[expose] public def relabelBasis (layout : QuantumLayout count) (physical : Nat ↪ Nat) :
    layout.register.Index ≃ (layout.relabel physical).register.Index := Equiv.refl _


end QuantumLayout

end QuantumAlg
