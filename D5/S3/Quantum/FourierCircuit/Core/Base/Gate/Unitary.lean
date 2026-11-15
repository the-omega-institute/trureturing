/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary
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
Original file: QuantumAlg/Core/Base/Gate/Unitary.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Metadata-free unitary operators

`UnitaryOperator R` reuses Mathlib's unitary matrix group and carries no placement,
resource, or depth metadata.
-/

section

namespace QuantumAlg

/-- A unitary Hilbert operator over `R`, with no implementation metadata. -/
public abbrev UnitaryOperator (R : Register) : Type := Matrix.unitaryGroup R.Index ℂ

namespace UnitaryOperator

noncomputable section

variable {R : Register}

/-- Certify a raw matrix once its unitarity proof is available. -/
@[expose]
public def ofMatrix (op : HilbertOperator R) (unitary : op ∈ Matrix.unitaryGroup R.Index ℂ) :
    UnitaryOperator R := ⟨op, unitary⟩


/-- A unitary operator still acts linearly on arbitrary raw vectors. -/
public def applyVec (U : UnitaryOperator R) (ψ : HilbertVector R) : HilbertVector R :=
  HilbertOperator.applyVec (U : HilbertOperator R) ψ


@[simp]
lemma one_applyVec (ψ : HilbertVector R) :
    (1 : UnitaryOperator R).applyVec ψ = ψ :=
  HilbertOperator.one_applyVec ψ

lemma mul_applyVec (U V : UnitaryOperator R) (ψ : HilbertVector R) :
    (U * V).applyVec ψ = U.applyVec (V.applyVec ψ) :=
  HilbertOperator.mul_applyVec (U : HilbertOperator R)
    (V : HilbertOperator R) ψ

/-- Unitary operators preserve inner products on arbitrary vectors. -/
lemma inner_applyVec_applyVec (U : UnitaryOperator R) (ψ φ : HilbertVector R) :
    inner ℂ (U.applyVec ψ) (U.applyVec φ) = inner ℂ ψ φ := by
  have hUU : (U : HilbertOperator R).conjTranspose * (U : HilbertOperator R) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  simp only [PiLp.inner_apply, RCLike.inner_apply, applyVec, HilbertOperator.applyVec]
  calc ∑ i, (∑ k, U i k * φ k) * starRingEnd ℂ (∑ j, U i j * ψ j)
      = ∑ i, ∑ k, ∑ j, (U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (1 : HilbertOperator R) j k * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hUU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (U i j) = starRingEnd ℂ (U i j) from rfl, mul_comm]
    _ = ∑ k, φ k * starRingEnd ℂ (ψ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        exact Fintype.sum_ite_eq' k fun j => φ k * starRingEnd ℂ (ψ j)

/-- Unitary operators preserve norms on arbitrary vectors. -/
lemma norm_applyVec (U : UnitaryOperator R) (ψ : HilbertVector R) :
    ‖U.applyVec ψ‖ = ‖ψ‖ := by
  have h := U.inner_applyVec_applyVec ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖U.applyVec ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  calc ‖U.applyVec ψ‖ = Real.sqrt (‖U.applyVec ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖ψ‖ ^ 2) := by rw [h2]
    _ = ‖ψ‖ := Real.sqrt_sq (norm_nonneg _)

/-- A unitary operator maps normalized vectors to normalized vectors. -/
public def apply (U : UnitaryOperator R) (ψ : NormalizedVector R) : NormalizedVector R :=
  NormalizedVector.ofVector (U.applyVec (ψ : HilbertVector R)) (by
    rw [U.norm_applyVec, ψ.norm_eq_one])


/-- Unitary permutation operator on computational-basis labels. -/
@[expose]
public def ofPerm (σ : Equiv.Perm R.Index) : UnitaryOperator R :=
  ofMatrix (σ.permMatrix ℂ) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one])

/-- A certified permutation operator sends a basis ket to the inverse image
of its label. -/
lemma ofPerm_applyVec (σ : Equiv.Perm R.Index) (ψ : HilbertVector R)
    (i : R.Index) :
    (ofPerm σ).applyVec ψ i = ψ (σ i) := by
  change HilbertOperator.applyVec (σ.permMatrix ℂ) ψ i = ψ (σ i)
  unfold HilbertOperator.applyVec
  rw [Matrix.permMatrix_mulVec]
  rfl

lemma ofPerm_applyVec_ket (σ : Equiv.Perm R.Index) (x : R.Index) :
    (ofPerm σ).applyVec (NormalizedVector.ket x : HilbertVector R) =
      (NormalizedVector.ket (σ⁻¹ x) : HilbertVector R) := by
  apply WithLp.ofLp_injective
  funext i
  rw [ofPerm_applyVec, NormalizedVector.ket_apply,
    NormalizedVector.ket_apply]
  by_cases h : σ i = x
  · rw [if_pos h, if_pos (by
      rw [← h]
      exact (Equiv.symm_apply_apply σ i).symm)]
  · rw [if_neg h, if_neg (fun hi => h (by
      rw [hi]
      exact Equiv.apply_symm_apply σ x))]

/-- A certified permutation preserves normalization while relabelling a ket. -/
@[simp]
lemma ofPerm_apply_ket (σ : Equiv.Perm R.Index) (x : R.Index) :
    (ofPerm σ).apply (NormalizedVector.ket x) =
      NormalizedVector.ket (σ⁻¹ x) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector R => ψ i)
    (ofPerm_applyVec_ket σ x)


end

end UnitaryOperator

end QuantumAlg

end
