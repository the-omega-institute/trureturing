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
ndices occupied by the state. -/
  system_idx : List Nat

attribute [nolint defsWithUnderscore] PureState.system_idx

namespace PureState

noncomputable section

variable {R : Register}
⟩
instance : CoeOut (PureState R) (HilbertVector R) := ⟨fun ψ => ψ.state.vec⟩
tate R) (fun _ => R.Index → ℂ) :=
  ⟨fun ψ => ψ.state.vec⟩
⟩
bertVector R) (φ : HilbertVector R)⟩
) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) + (φ : HilbertVector R)⟩
) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) - (φ : HilbertVector R)⟩
tVector R) :=
  ⟨fun c ψ => c • (ψ : HilbertVector R)⟩
idx := system_idx
ofNormalized state system_idx : PureState R) : HilbertVector R) = state := rfl
_idx : List Nat) :
    (ofNormalized state system_idx).system_idx = system_idx := rfl
: PureState R) : ‖(ψ : HilbertVector R)‖ = 1 :=
  ψ.state.norm_eq_one
es hsystem
  rfl
PureState R :=
  ofNormalized (NormalizedVector.ket x) system_idx
= x then 1 else 0 :=
  NormalizedVector.ket_apply x i
ve
  exact congrArg PureState.state hxy
Vector R)‖ = 1 :=
  (basis x system_idx).norm_eq_one

end

end PureState

end QuantumAlg

end
