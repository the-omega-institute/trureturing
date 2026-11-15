/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/State/Basic
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/State/Basic
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
Original file: QuantumAlg/Core/Base/State/Basic.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Register
import all D5.S3.Quantum.FourierCircuit.Core.Base.Register
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Raw Hilbert-space vectors over finite registers

`HilbertVector R` is the unrestricted complex Hilbert-space vector type.  Linear
combinations and intermediate vectors live here even when they are not normalized.
-/

section

namespace QuantumAlg

/-- Raw Hilbert-space vector for a finite quantum register. -/
public abbrev HilbertVector (R : Register) : Type := EuclideanSpace ℂ R.Index

end QuantumAlg

end
