/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/Kind
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Accounting/Kind
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
Original file: QuantumAlg/Core/Base/Accounting/Kind.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import Mathlib.Data.PNat.Defs

/-!
# Computation kinds and classical and storage coordinates

These types classify mathematical state and storage without selecting quantum
operations. Classical opcodes are closed typed machine operations. Quantum gate
and query coordinates are supplied separately by an execution model.
-/

namespace QuantumAlg


namespace Resource


end Resource


namespace SpaceAxis


end SpaceAxis

end QuantumAlg
