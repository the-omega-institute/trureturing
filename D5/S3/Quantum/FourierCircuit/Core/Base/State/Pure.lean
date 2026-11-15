/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/State/Pure
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/State/Pure
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
Original file: QuantumAlg/Core/Base/State/Pure.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized

/-!
# Prepared pure states

`PureState R` adds physical placement to an already normalized mathematical
vector. Mathematical normalization is owned by `NormalizedVector`; preparation
resources belong to `KnownPreparation` and executable runs rather than to this
state value.
-/

section

namespace QuantumAlg

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false


attribute [nolint defsWithUnderscore] PureState.system_idx

namespace PureState

noncomputable section

variable {R : Register}


end

end PureState

end QuantumAlg

end
