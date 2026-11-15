/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Marginal
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Marginal
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
Original file: QuantumAlg/Core/Base/Marginal.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
import all D5.S3.Quantum.FourierCircuit.Core.Base.Tensor
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
public import Mathlib.Data.Real.Basic

/-!
# Leading-qubit marginal weights and probabilities

Circuit- and measurement-object-independent marginal helpers for finite
vectors. A raw vector has only a Born weight; the probability name is reserved
for the wrapper whose input carries unit normalization intrinsically.
-/

section

namespace QuantumAlg
namespace HilbertVector

noncomputable section
), ‖ψ (prodEquiv (b, y))‖ ^ 2
.sum_nonneg fun _ _ => sq_nonneg _
.smul_apply, smul_eq_mul, norm_mul, mul_pow]

end

end HilbertVector

namespace NormalizedVector

noncomputable section
ertVector (Qubits (1 + n))) b
onneg
      (ψ : HilbertVector (Qubits (1 + n))) b

end

end NormalizedVector
end QuantumAlg

end
