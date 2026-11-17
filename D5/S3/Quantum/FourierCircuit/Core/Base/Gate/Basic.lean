/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic
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
Original file: QuantumAlg/Core/Base/Gate/Basic.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized

/-!
# Raw Hilbert operators

`HilbertOperator R` is the unrestricted complex matrix over `R`. Observables,
projectors, block-encoding targets, sums, scalar multiples, and polynomials live at
this layer even when they are not unitary.
-/

section

namespace QuantumAlg

/-- Raw linear operator over a finite quantum register. -/
public abbrev HilbertOperator (R : Register) : Type := Matrix R.Index R.Index ℂ

namespace HilbertOperator

noncomputable section

variable {R : Register}

/-- Matrix-vector multiplication on raw state vectors. -/
def applyVec (A : HilbertOperator R) (ψ : HilbertVector R) : HilbertVector R :=
  WithLp.toLp 2 (A.mulVec ψ.ofLp)


@[simp]
lemma one_applyVec (ψ : HilbertVector R) : applyVec (1 : HilbertOperator R) ψ = ψ := by
  unfold applyVec
  rw [Matrix.one_mulVec]

lemma mul_applyVec (A B : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (A * B) ψ = applyVec A (applyVec B ψ) := by
  unfold applyVec
  rw [show (WithLp.toLp 2 (B.mulVec ψ.ofLp)).ofLp = B.mulVec ψ.ofLp from rfl,
    Matrix.mulVec_mulVec]


end

end HilbertOperator

end QuantumAlg

end
