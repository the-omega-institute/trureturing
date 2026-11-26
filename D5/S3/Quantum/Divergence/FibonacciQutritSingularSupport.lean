/- GID: D5/S3/Quantum/Divergence/FibonacciQutritSingularSupport
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/FibonacciQutritSingularSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact qubit reduction with ambient null-reference loss and preserved trace pairings. -/

import D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination
import D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Divergence.SingularWeightedLogIncrement

/-! Common qubit compression of a singular weighted qutrit comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination.Block (blockHom log_block)
open D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport.Transport
  (coordinates coordinates_posSemidef coordinates_le coordinates_trace
    coordinates_divergence divergence trace_blocks)

namespace D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport

private abbrev Mat (n : Type*) := Matrix n n ℂ
private abbrev Qubit := Mat (Fin 2)
private abbrev Block := Mat (Fin 2 ⊕ Unit)

private abbrev matrix {n : Type*} [Fintype n] [DecidableEq n] (X : DensityState n) : Mat n :=
  CStarMatrix.ofMatrix.symm X.1

private lemma zero_eigenindex {C : Mat (Fin 3)} (hC : C.PosSemidef)
    (hs : ¬ C.PosDef ∨ C.rank ≤ 2) : ∃ i, hC.isHermitian.eigenvalues i = 0 := by
  classical
  by_contra! h
  rcases hs with hs | hs
  · exact hs (hC.isHermitian.posDef_iff_eigenvalues_pos.mpr fun i =>
      lt_of_le_of_ne (hC.eigenvalues_nonneg i) (h i).symm)
  · let f : {i // hC.isHermitian.eigenvalues i ≠ 0} ≃ Fin 3 :=
      ⟨Subtype.val, fun i => ⟨i, h i⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hC.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_congr f, Fintype.card_fin] at hs
    omega

/-- A zero diagonal entry of a positive matrix removes its entire row and column. -/
private lemma block_of_zero_diagonal {M : Block} (hM : M.PosSemidef)
    (hz : M (Sum.inr ()) (Sum.inr ()) = 0) :
    M = fromBlocks M.toBlocks₁₁ 0 0 (0 : Mat Unit) := by
  classical
  have hk : M *ᵥ Pi.single (Sum.inr ()) 1 = 0 := hM.dotProduct_mulVec_zero_iff.mp (by
    simp [Pi.star_single, single_dotProduct, hz])
  have hcol (i : Fin 2 ⊕ Unit) : M i (Sum.inr ()) = 0 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun hk i
  have hrow (j : Fin 2 ⊕ Unit) : M (Sum.inr ()) j = 0 := by
    have h := congrArg (fun N : Block => N (Sum.inr ()) j) hM.isHermitian.eq
    simpa [Matrix.conjTranspose_apply, hcol] using h.symm
  ext (i | ⟨⟩) (j | ⟨⟩)
  · rfl
  · exact hcol _
  · exact hrow _
  · exact hz

set_option maxHeartbeats 1000000 in
/-- A singular qutrit reference compresses every positive class into one common qubit.
The null-class loss is the ambient weighted log increment, and the compression
preserves all Hilbert–Schmidt pairings of positive classes. -/
theorem singular_support_reduction {ι : Type*} [Fintype ι]
    (X : ι → DensityState (Fin 3)) (X₀ : DensityState (Fin 3)) (p q : ι → ℝ) (e : ℝ)
    (hq : ∀ i, 0 < q i)
    (hp : ∀ i, (4 / 3 : ℝ) * q i ≤ p i ∧ p i ≤ (7 / 3 : ℝ) * q i) (he : 0 < e) :
    let C := ∑ i, q i • matrix (X i)
    let A := ∑ i, p i • matrix (X i)
    let B := C + e • matrix X₀
    let Δ := (A * (CFC.log B - CFC.log C)).trace.re
    (¬ C.PosDef ∨ C.rank ≤ 2) →
    ∃ Y : ι → DensityState (Fin 2),
      let C₂ := ∑ i, q i • matrix (Y i)
      let A₂ := ∑ i, p i • matrix (Y i)
      (A * (CFC.log A - CFC.log B)).trace.re =
        (A₂ * (CFC.log A₂ - CFC.log C₂)).trace.re - Δ ∧
      0 ≤ Δ ∧ (Δ = 0 ↔ C * matrix X₀ = 0) ∧
      ∀ i j, (matrix (Y i) * matrix (Y j)).trace.re =
        (matrix (X i) * matrix (X j)).trace.re := by
  classical
  let C := ∑ i, q i • matrix (X i)
  let A := ∑ i, p i • matrix (X i)
  let B := C + e • matrix X₀
  let Δ := (A * (CFC.log B - CFC.log C)).trace.re
  change (¬ C.PosDef ∨ C.rank ≤ 2) → ∃ Y : ι → DensityState (Fin 2), _
  intro hs
  have hC : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ => ((density_posSemidef (X i)).smul (hq i).le).nonneg)
  have hlo : (4 / 3 : ℝ) • C ≤ A := by
    simp only [A, C, Finset.smul_sum, smul_smul]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_smul_of_nonneg_right (hp i).1 (density_posSemidef (X i)).nonneg
  have hhi : A ≤ (7 / 3 : ℝ) • C := by
    simp only [A, C, Finset.smul_sum, smul_smul]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_smul_of_nonneg_right (hp i).2 (density_posSemidef (X i)).nonneg
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (((hC.smul (by norm_num : (0 : ℝ) ≤ 4 / 3)).nonneg).trans hlo)
  have hgap : 0 ≤ Δ ∧ (Δ = 0 ↔ C * matrix X₀ = 0) :=
    SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff
      hC (density_posSemidef X₀) (by norm_num) (by norm_num) he hlo hhi

  let h := hC.isHermitian
  obtain ⟨k, hk⟩ := zero_eigenindex hC hs
  let g : Fin 2 ⊕ Unit ≃ Fin 3 := Fintype.equivFinOfCardEq (by decide)
  let f : Fin 3 ≃ Fin 2 ⊕ Unit := (g.trans (Equiv.swap (g (Sum.inr ())) k)).symm
  have hfk : f.symm (Sum.inr ()) = k := Equiv.swap_apply_left _ _
  let U := star h.eigenvectorUnitary
  let E := coordinates U f
  let d (j : Fin 2 ⊕ Unit) := h.eigenvalues (f.symm j)
  have hdiag : E C = diagonal (fun j => (d j : ℂ)) := by
    change Matrix.reindex f f (Unitary.conjStarAlgAut ℂ (Mat (Fin 3)) U C) = _
    rw [h.conjStarAlgAut_star_eigenvectorUnitary, Matrix.reindex_apply,
      Matrix.submatrix_diagonal_equiv]
    rfl
  have hzC : E C (Sum.inr ()) (Sum.inr ()) = 0 := by
    simp [hdiag, d, hfk, hk]

  let M (i : ι) := E (matrix (X i))
  have hM (i : ι) : (M i).PosSemidef :=
    (coordinates_posSemidef U f _).mpr (density_posSemidef (X i))
  have hz (i : ι) : M i (Sum.inr ()) (Sum.inr ()) = 0 := by
    have hle : q i • matrix (X i) ≤ C :=
      Finset.single_le_sum (f := fun j => q j • matrix (X j))
        (fun j _ => ((density_posSemidef (X j)).smul (hq j).le).nonneg) (Finset.mem_univ i)
    have hEle : q i • M i ≤ E C := by
      simpa only [M, map_smul] using (coordinates_le U f _ _).mpr hle
    have hnonneg := Complex.nonneg_iff.mp ((hM i).diag_nonneg (i := Sum.inr ()))
    have hdom := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hEle).diag_nonneg
      (i := Sum.inr ()))).1
    change 0 ≤ (E C (Sum.inr ()) (Sum.inr ()) - q i • M i (Sum.inr ()) (Sum.inr ())).re
      at hdom
    rw [hzC, zero_sub, Complex.neg_re, neg_nonneg, Complex.real_smul, Complex.re_ofReal_mul]
      at hdom
    exact Complex.ext (le_antisymm (nonpos_of_mul_nonpos_right hdom (hq i)) hnonneg.1)
      (by simpa using hnonneg.2.symm)

  let N (i : ι) : Qubit := (M i).toBlocks₁₁
  have hblocks (i : ι) : M i = fromBlocks (N i) 0 0 (0 : Mat Unit) :=
    block_of_zero_diagonal (hM i) (hz i)
  let Y (i : ι) : DensityState (Fin 2) :=
    ⟨CStarMatrix.ofMatrix (N i),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((hM i).submatrix Sum.inl).nonneg,
      by
        change (N i).trace = 1
        have htr := (trace_blocks (M i)).symm.trans (coordinates_trace U f (matrix (X i)))
        simpa only [N, hz, add_zero] using htr.trans (X i).2.2⟩
  let C₂ := ∑ i, q i • N i
  let A₂ := ∑ i, p i • N i
  have hsum (w : ι → ℝ) :
      E (∑ i, w i • matrix (X i)) = fromBlocks (∑ i, w i • N i) 0 0 (0 : Mat Unit) := by
    let J : Qubit →ₗ[ℝ] Block := blockHom.toLinearMap.comp (LinearMap.inl ℝ Qubit (Mat Unit))
    change E (∑ i, w i • matrix (X i)) = J (∑ i, w i • N i)
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, map_smul]
      change w i • M i = w i • fromBlocks (N i) 0 0 (0 : Mat Unit)
      rw [hblocks i]
  have hAC : (A * (CFC.log A - CFC.log C)).trace.re =
      (A₂ * (CFC.log A₂ - CFC.log C₂)).trace.re := by
    have hA₂ := ((coordinates_posSemidef U f A).mpr hA).submatrix
      (Sum.inl : Fin 2 → Fin 2 ⊕ Unit)
    have hC₂ := ((coordinates_posSemidef U f C).mpr hC).submatrix
      (Sum.inl : Fin 2 → Fin 2 ⊕ Unit)
    rw [hsum p] at hA₂
    rw [hsum q] at hC₂
    have hA₂' : A₂.IsHermitian := hA₂.isHermitian
    have hC₂' : C₂.IsHermitian := hC₂.isHermitian
    change divergence A C = _
    rw [← coordinates_divergence U f A C]
    change ((E A) * (CFC.log (E A) - CFC.log (E C))).trace.re = _
    rw [hsum p, hsum q, log_block A₂ 0 hA₂' Matrix.isHermitian_zero,
      log_block C₂ 0 hC₂' Matrix.isHermitian_zero]
    have hsub :
        fromBlocks (CFC.log A₂) 0 0 (CFC.log (0 : Mat Unit)) -
            fromBlocks (CFC.log C₂) 0 0 (CFC.log (0 : Mat Unit)) =
          fromBlocks (CFC.log A₂ - CFC.log C₂) 0 0 (0 : Mat Unit) := by
      ext (i | i) (j | j) <;> simp
    rw [hsub, fromBlocks_multiply, trace_blocks]
    simp [Matrix.toBlocks₁₁] <;> rfl
  refine ⟨Y, ?_, hgap.1, hgap.2, ?_⟩
  · change (A * (CFC.log A - CFC.log B)).trace.re =
      (A₂ * (CFC.log A₂ - CFC.log C₂)).trace.re - Δ
    rw [← hAC]
    simp only [Δ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    ring
  · intro i j
    change (N i * N j).trace.re = (matrix (X i) * matrix (X j)).trace.re
    have ht := coordinates_trace U f (matrix (X i) * matrix (X j))
    rw [map_mul] at ht
    change (M i * M j).trace = _ at ht
    rw [hblocks i, hblocks j, fromBlocks_multiply, trace_blocks] at ht
    simp [Matrix.toBlocks₁₁] at ht
    change (N i * N j).trace = _ at ht
    exact congrArg Complex.re ht

#print axioms singular_support_reduction

namespace Preparation

export _root_.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport (matrix)

end Preparation

end D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
