/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/OperatorNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/OperatorNorm
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
Original file: QuantumAlg/Core/Base/Gate/OperatorNorm.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm on finite-register Hilbert operators

`HilbertOperator R` is an abbreviation for ordinary `Matrix`, where Mathlib
deliberately avoids choosing a default norm. `HilbertOperator.opNorm` fixes the
L2 operator norm as one plain real-valued function, so downstream statements
(approximate circuit realizations, product-formula error bounds, compiled
circuit error composition) never install a global matrix norm instance. Proofs
open the scoped `Matrix.Norms.L2Operator` instances locally and export only
norm facts about the plain function.

The unitary-invariance and telescoping lemmas are the two facts every error
composition argument in the library reduces to: multiplying by a unitary does
not change the norm, and `‖U₁ U₂ - V₁ V₂‖ ≤ ‖U₁ - V₁‖ + ‖U₂ - V₂‖` when
`U₂` and `V₁` are unitary.
-/

@[expose] public section

namespace QuantumAlg

namespace HilbertOperator

noncomputable section

variable {R : Register}


/-! ## Unitary invariance -/


/-! ## Telescoping -/


end

end HilbertOperator

end QuantumAlg

end

/-!
## Vector action

`HilbertOperator.applyVec` is module-private in `Gate/Basic`, so the bound on the
vector action is exported at the same visibility: downstream modules reach it
through `import all QuantumAlg.Core.Base.Gate.OperatorNorm`.
-/

section

namespace QuantumAlg.HilbertOperator

variable {R : Register}


end QuantumAlg.HilbertOperator

end
