/- GID: D5/S3/Quantum/FourierCircuit/Components/Kets
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Kets
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
Original file: QuantumAlg/Components/Kets.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.Marginal

/-!
# Named one-qubit kets

The standard one-qubit computational- and Hadamard-basis kets, as Components-layer
instances of the generic basis ket `QuantumAlg.NormalizedVector.ket`:

`|0>`, `|1>`, `|+> = (|0> + |1>)/sqrt 2`, and
`|-> = (|0> - |1>)/sqrt 2`.

Linear combinations are formed at the raw `HilbertVector` layer and then certified
as metadata-free `NormalizedVector` values once their unit norm has been proved.
-/

section

namespace QuantumAlg

namespace NormalizedVector

noncomputable section
f ket0 : NormalizedVector (Qubits 1) := ket 0
ef ket1 : NormalizedVector (Qubits 1) := ket 1
exact ket_apply (R := Qubits 1) 0 index

/-- `(sqrt 2)^-1 : ℂ`, the ubiquitous normalization scalar. -/
@[expose] public def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp]
public lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
 ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq, invSqrt2_mul_self]
invSqrt2_mul_self]
    _ = (2 : ℂ)⁻¹ * z := by ring

@[simp]
public lemma star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
mpr <|
    Real.sqrt_ne_zero'.mpr (by norm_num)
, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
‖ψ i‖ ^ 2)
1, ← two_mul, norm_sq_invSqrt2]
      norm_num)
1, norm_neg, ← two_mul, norm_sq_invSqrt2]
      norm_num)
   ((ket0 : HilbertVector (Qubits 1)) + (ket1 : HilbertVector (Qubits 1))) :=
  rfl
   ((ket0 : HilbertVector (Qubits 1)) - (ket1 : HilbertVector (Qubits 1))) :=
  rfl
pply, smul_eq_mul]
pply, smul_eq_mul]
us‖ = 1 := by
  exact ketPlus.norm_eq_one
nus‖ = 1 := by
  exact ketMinus.norm_eq_one
how (0 : Fin (2 ^ 1)) ≠ 1 by decide), one_mul, zero_mul,
    add_zero]
how (1 : Fin (2 ^ 1)) ≠ 0 by decide), one_mul, zero_mul,
    zero_add]

end

end NormalizedVector

end QuantumAlg

end
