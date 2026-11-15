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
n scoped Matrix.Norms.L2Operator in
  ‖A‖
rix.Norms.L2Operator in
  exact norm_zero
Norms.L2Operator in
  exact norm_nonneg A
.Norms.L2Operator in
  exact norm_eq_zero
ix.Norms.L2Operator in
  exact norm_neg A
rms.L2Operator in
  exact norm_add_le A B
rms.L2Operator in
  exact norm_sub_le A B
ms.L2Operator in
  exact norm_sub_rev A B
t norm_sub_le_norm_sub_add_norm_sub A B C
xact (opNorm_add_le _ _).trans (add_le_add_right ih _)
Norms.L2Operator in
  exact norm_smul c A
x.Norms.L2Operator in
  exact norm_star A
q_conjTranspose]
  exact opNorm_star A
trix.Norms.L2Operator in
  exact norm_one
rator in
  exact Matrix.l2_opNorm_mul A B
or in
  exact Matrix.l2_opNorm_mulVec A ψ

/-! ## Unitary invariance -/

  exact CStarRing.norm_of_mem_unitary hU
exact CStarRing.norm_mem_unitary_mul A hU
exact CStarRing.norm_mul_mem_unitary A hU
R) = 1 :=
  opNorm_of_mem_unitaryGroup U.2
r R) * A) = opNorm A :=
  opNorm_unitaryGroup_mul A U.2
rator R)) = opNorm A :=
  opNorm_mul_unitaryGroup A U.2
perator R) := opNorm_sub_le _ _
    _ = 2 := by rw [opNorm_unitary, opNorm_unitary]; norm_num

/-! ## Telescoping -/
unitaryGroup _ hA₂, opNorm_unitaryGroup_mul _ hB₁]
erator R))
    (B₁ := (V₁ : HilbertOperator R)) (B₂ := (V₂ : HilbertOperator R)) U₂.2 V₁.2
arith [hstep, ih]

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
pNorm A * ‖ψ‖ :=
  opNorm_mulVec_le A ψ

end QuantumAlg.HilbertOperator

end
