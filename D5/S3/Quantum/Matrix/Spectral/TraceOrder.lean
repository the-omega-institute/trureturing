/- GID: D5/S3/Quantum/Matrix/Spectral/TraceOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Spectral/TraceOrder
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Positive matrix products have nonnegative real trace and positive weights preserve trace order. -/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
The positive product trace proof is from the attributed Zeta23 transplant,
revision 3635e74826a4c1fcece7d1cd2b6fa75e43a00510, by Anthropic, PBC,
released under Apache-2.0. The public name and proof are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `tr(AB) ≥ 0` when `A, B ⪰ 0`. Proof: diagonalise `A = U D Uᴴ`; then
`tr(AB) = tr((UᴴBU)D) = ∑ᵢ λᵢ · (UᴴBU)ᵢᵢ`, where each `λᵢ ≥ 0` (PSD
eigenvalues) and each `(UᴴBU)ᵢᵢ ≥ 0` (diagonal of a PSD matrix). -/
lemma trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A * B).trace := by
  -- Reduce `tr(AB)` to `tr((UᴴBU)D)` by the spectral theorem + trace cycling.
  rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc,
    trace_mul_comm, ← mul_assoc]
  set M := star (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) * B *
    (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hM_def
  -- `M = UᴴBU` is PSD.
  have hM : M.PosSemidef := hB.conjTranspose_mul_mul_same _
  -- Now `0 ≤ re tr(M * diag λ) = ∑ᵢ λᵢ · re Mᵢᵢ`.
  simp only [trace, diag_apply, mul_diagonal, Function.comp_apply, map_sum,
    RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (RCLike.nonneg_iff.mp hM.diag_nonneg).1 (hA.eigenvalues_nonneg i)

end RHLinalg
namespace D5.S3.Quantum.Lieb.TraceInverseConvexity
variable {d : Type*} [Fintype d] [DecidableEq d]

lemma weighted_trace_re_mono (C : Matrix d d ℂ) (hC : C.PosSemidef)
    {A B : Matrix d d ℂ} (h : A ≤ B) :
    (Matrix.trace (C * A)).re ≤ (Matrix.trace (C * B)).re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp h
  have htr : 0 ≤ (Matrix.trace (C * (B - A))).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hC hpsd
  rw [Matrix.mul_sub, Matrix.trace_sub] at htr
  exact sub_nonneg.mp htr

end D5.S3.Quantum.Lieb.TraceInverseConvexity
