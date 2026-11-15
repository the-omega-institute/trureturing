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

/-- A normalized state with physical placement and no accounting metadata. -/
public structure PureState (R : Register) where
  private mk ::
  /-- Metadata-free normalized mathematical state. -/
  state : NormalizedVector R
  /-- Physical system indices occupied by the state. -/
  system_idx : List Nat

attribute [nolint defsWithUnderscore] PureState.system_idx

namespace PureState

noncomputable section

variable {R : Register}

instance : Coe (PureState R) (HilbertVector R) := ⟨fun ψ => ψ.state.vec⟩
instance : CoeTail (PureState R) (HilbertVector R) := ⟨fun ψ => ψ.state.vec⟩
instance : CoeOut (PureState R) (HilbertVector R) := ⟨fun ψ => ψ.state.vec⟩

instance : CoeFun (PureState R) (fun _ => R.Index → ℂ) :=
  ⟨fun ψ => ψ.state.vec⟩

instance : Norm (PureState R) := ⟨fun ψ => ‖(ψ : HilbertVector R)‖⟩

instance : Inner ℂ (PureState R) :=
  ⟨fun ψ φ => inner ℂ (ψ : HilbertVector R) (φ : HilbertVector R)⟩

instance : HAdd (PureState R) (PureState R) (HilbertVector R) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) + (φ : HilbertVector R)⟩

instance : HSub (PureState R) (PureState R) (HilbertVector R) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) - (φ : HilbertVector R)⟩

instance : HSMul ℂ (PureState R) (HilbertVector R) :=
  ⟨fun c ψ => c • (ψ : HilbertVector R)⟩

/-- Attach physical placement to an already normalized vector. -/
def ofNormalized (state : NormalizedVector R) (system_idx : List Nat) : PureState R where
  state := state
  system_idx := system_idx

@[simp]
lemma coe_ofNormalized (state : NormalizedVector R) (system_idx : List Nat) :
    ((ofNormalized state system_idx : PureState R) : HilbertVector R) = state := rfl

@[simp]
lemma ofNormalized_system_idx (state : NormalizedVector R) (system_idx : List Nat) :
    (ofNormalized state system_idx).system_idx = system_idx := rfl

/-- Prepared pure states are normalized because their mathematical state is. -/
lemma norm_eq_one (ψ : PureState R) : ‖(ψ : HilbertVector R)‖ = 1 :=
  ψ.state.norm_eq_one

@[ext]
lemma ext {ψ φ : PureState R} (hvec : ∀ i, ψ i = φ i)
    (hsystem : ψ.system_idx = φ.system_idx) : ψ = φ := by
  have hstate : ψ.state = φ.state := NormalizedVector.ext hvec
  cases ψ
  cases φ
  cases hstate
  cases hsystem
  rfl

/-- Place a computational-basis state on explicit physical systems. -/
def basis (x : R.Index) (system_idx : List Nat) : PureState R :=
  ofNormalized (NormalizedVector.ket x) system_idx

@[simp]
lemma basis_apply (x i : R.Index) (system_idx : List Nat) :
    basis x system_idx i = if i = x then 1 else 0 :=
  NormalizedVector.ket_apply x i

lemma basis_injective (system_idx : List Nat) :
    Function.Injective (fun x => basis (R := R) x system_idx) := by
  intro x y hxy
  apply NormalizedVector.ket_injective
  exact congrArg PureState.state hxy

lemma norm_basis (x : R.Index) (system_idx : List Nat) :
    ‖(basis x system_idx : HilbertVector R)‖ = 1 :=
  (basis x system_idx).norm_eq_one

end

end PureState

end QuantumAlg

end
