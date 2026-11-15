/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Basic
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Tensor/Basic
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
Original file: QuantumAlg/Core/Base/Tensor/Basic.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Util.FinPow
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Raw tensor products

This module defines tensor products for unrestricted state vectors and Hilbert
operators.  It makes no normalization or unitarity claim.
-/

section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace HilbertVector

noncomputable section


end

end HilbertVector

namespace HilbertOperator

noncomputable section


end

end HilbertOperator

end QuantumAlg

end
