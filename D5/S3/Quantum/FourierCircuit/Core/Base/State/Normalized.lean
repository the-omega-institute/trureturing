/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/State/Normalized
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
Original file: QuantumAlg/Core/Base/State/Normalized.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Basic

/-!
# Metadata-free normalized vectors

`NormalizedVector R` carries only the mathematical invariant `‖ψ‖ = 1`.  It has
no physical placement or preparation cost and deliberately has no additive or
arbitrary scalar-action structure, since those operations do not preserve norm one.
-/

section

namespace QuantumAlg

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- A unit vector over a finite register, with no preparation metadata. -/
public structure NormalizedVector (R : Register) where
  private mk ::
  /-- Underlying raw Hilbert-space vector. -/
  vec : HilbertVector R
  /-- The vector has norm one. -/
  norm_eq_one : ‖vec‖ = 1

namespace NormalizedVector

noncomputable section

variable {R : Register}

instance : Coe (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩
instance : CoeTail (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩
instance : CoeOut (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩

instance : CoeFun (NormalizedVector R) (fun _ => R.Index → ℂ) :=
  ⟨fun ψ => ψ.vec⟩


/-- Certify a raw vector once its norm-one proof is available. -/
@[expose] public def ofVector (vec : HilbertVector R)
    (norm_eq_one : ‖vec‖ = 1) : NormalizedVector R where
  vec := vec
  norm_eq_one := norm_eq_one


@[ext]
lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ := by
  have hv : ψ.vec = φ.vec := by
    apply WithLp.ofLp_injective
    funext i
    exact hvec i
  cases ψ
  cases φ
  cases hv
  rfl

/-- Computational-basis ket as a metadata-free normalized vector. -/
public def ket (x : R.Index) : NormalizedVector R :=
  ofVector (PiLp.single 2 x 1) (by simp)

@[simp]
public lemma ket_apply (x i : R.Index) :
    ket x i = if i = x then 1 else 0 := by
  simp [ket, ofVector]


end

end NormalizedVector

end QuantumAlg

end
