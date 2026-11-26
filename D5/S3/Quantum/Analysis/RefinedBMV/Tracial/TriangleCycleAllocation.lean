/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleCycleAllocation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three weighted edge allocations certify the signed Hermitian cyclic trace. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram

/-! Three quadratic edge allocations for the triangle terms of a Hermitian
four-copy trace. -/

namespace RefinedBMV.Tracial

open Matrix FourCopyGap ThreeBlockGram
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open private trace_mask_product trace_mul_nonneg_of_posSemidef contract
  rootDiagonal eigenDiagonal diagonal_gap_scaled gaps_card_pos gapDefect_diagonal
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectralBlock_conjTranspose (label : n → Fin 3) {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (i j : Fin 3) :
    (spectralBlock label B i j)ᴴ = spectralBlock label B j i := by
  have hmask (k : Fin 3) : (spectralMask label k)ᴴ = spectralMask label k := by
    rw [spectralMask, diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : label a = k <;> simp [h]
  simp only [spectralBlock, conjTranspose_mul, hmask, hB.eq, mul_assoc]

/-- The edge Gram vectors are the length-two paths between its endpoints.
The three possible intermediate labels give the two diagonal-block terms
and the backtrack available to pay for the triangle terms. -/
private theorem edge_gram_nonneg (label : n → Fin 3) (B : Matrix n n ℂ)
    (hB : B.IsHermitian) (i j k : Fin 3) (G : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : G.PosSemidef) :
    0 ≤ gramContraction (fun r ↦ spectralMask label r * B) i j k G := by
  let C := spectralBlock label B
  let q : Fin 3 → Fin 3 := ![i, j, k]
  let V (u : Fin 3) := C i (q u) * C (q u) j
  let W : Matrix (n × n) (Fin 3) ℂ := fun ab u ↦ V u ab.1 ab.2
  have hv (u v : Fin 3) :
      trace (V u * (V v)ᴴ) =
        trace4 (fun r ↦ spectralMask label r * B) i (q u) j (q v) := by
    rw [show trace4 (fun r ↦ spectralMask label r * B) i (q u) j (q v) =
        cycleTrace C i (q u) j (q v) from trace_mask_product label B _ _ _ _]
    simp only [V, C, conjTranspose_mul, spectralBlock_conjTranspose label hB, cycleTrace,
      mul_assoc]
  have hk (u v : Fin 3) :
      (Wᴴ * W) v u = trace4 (fun r ↦ spectralMask label r * B) i (q u) j (q v) := by
    rw [← hv]
    change (∑ ab : n × n, star (V v ab.1 ab.2) * V u ab.1 ab.2) =
      ∑ a : n, ∑ b : n, V u a b * star (V v a b)
    rw [Fintype.sum_prod_type]
    simp only [mul_comm]
  have heq : gramContraction (fun r ↦ spectralMask label r * B) i j k G =
      trace (G * (Wᴴ * W)) := by
    simp only [gramContraction, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply (M := G) (N := Wᴴ * W), hk, q]
  rw [heq]
  exact trace_mul_nonneg_of_posSemidef hG (posSemidef_conjTranspose_mul_self W)

private theorem alternating_block_trace_nonneg (label : n → Fin 3) (B : Matrix n n ℂ)
    (hB : B.IsHermitian) (i j : Fin 3) :
    0 ≤ trace4 (fun r ↦ spectralMask label r * B) i j i j := by
  let V := spectralBlock label B i j * spectralBlock label B j i
  have hV : Vᴴ = V := by
    simp only [V, conjTranspose_mul, spectralBlock_conjTranspose label hB]
  have h := trace_mask_product label B i j i j
  change trace4 (fun r ↦ spectralMask label r * B) i j i j = _ at h
  rw [h]
  change 0 ≤ trace (V * spectralBlock label B i j * spectralBlock label B j i)
  rw [mul_assoc, ← hV]
  exact (posSemidef_conjTranspose_mul_self V).trace_nonneg

/-- For arbitrary Hermitian block data in a spectral labeling, three PSD
edge allocations control the symmetric four-slot kernel on three labels. -/
theorem triangle_cycle_sum_nonneg (d : Kernel) (label : n → Fin 3)
    (B : Matrix n n ℂ) (hB : B.IsHermitian) (alloc : Fin 3 → Fin 3 → ℝ)
    (h01 : ∀ i j k l, d i j k l = d j i k l)
    (h12 : ∀ i j k l, d i j k l = d i k j l)
    (h23 : ∀ i j k l, d i j k l = d i j l k)
    (hd : ∀ i, d i i i i = 0) (hn : ∀ i j, 0 ≤ g d i j)
    (hAlloc : Allocation d alloc) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, (d i j k l : ℂ) * cycleTrace (spectralBlock label B) i j k l := by
  let X (i : Fin 3) := spectralMask label i * B
  have ht (i j k l : Fin 3) : trace4 X i j k l =
      cycleTrace (spectralBlock label B) i j k l := trace_mask_product label B i j k l
  change 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, (d i j k l : ℂ) * _
  simp_rw [← ht]
  change 0 ≤ gapSum d X
  obtain ⟨hr0, hr1, hr2, hG01, hG02, hG12⟩ := hAlloc
  rw [gapSum_eq_grams d X alloc h01 h12 h23 hd hr0 hr1 hr2]
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg
      (edge_gram_nonneg label B hB 0 1 2 _ hG01)
      (edge_gram_nonneg label B hB 0 2 1 _ hG02))
      (edge_gram_nonneg label B hB 1 2 0 _ hG12)))
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg
      (mul_nonneg (Complex.zero_le_real.mpr (hn 0 1))
        (alternating_block_trace_nonneg label B hB 0 1))
      (mul_nonneg (Complex.zero_le_real.mpr (hn 0 2))
        (alternating_block_trace_nonneg label B hB 0 2)))
      (mul_nonneg (Complex.zero_le_real.mpr (hn 1 2))
        (alternating_block_trace_nonneg label B hB 1 2))))

/-- The actual word mean in the spectral basis under a three-label allocation
for the four-copy deficit and a Hermitian second factor. -/
theorem diagonal_word_bound_of_triangle_allocation (p : ℕ) (label : n → Fin 3)
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i) (B : Matrix n n ℂ) (hB : B.IsHermitian)
    (alloc : Fin 3 → Fin 3 → ℝ) (hAlloc : Allocation (spectralDefect p x) alloc) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  have h := triangle_cycle_sum_nonneg (spectralDefect p x) label B hB alloc
    (fun i j k l ↦ gapDefect_swap01 p (x i) (x j) (x k) (x l))
    (fun i j k l ↦ gapDefect_swap12 p (x i) (x j) (x k) (x l))
    (fun i j k l ↦ gapDefect_swap23 p (x i) (x j) (x k) (x l))
    (fun i ↦ gapDefect_diagonal p (x i) (hx i))
    (fun i j ↦ gapDefect_nonneg p (hx i) (hx i) (hx j) (hx j)) hAlloc
  have heq :
      ((gaps p).card : ℂ) *
        (FourCopyGap.wordMean p (eigenDiagonal label x) B -
          trace ((rootDiagonal label x p * B) ^ 4)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (spectralDefect p x i j k l : ℂ) *
        cycleTrace (spectralBlock label B) i j k l := by
    rw [diagonal_gap_scaled]
    rfl
  rw [← heq] at h
  have hc : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp h
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hre),
    (sub_eq_zero.mp ((mul_eq_zero.mp him.symm).resolve_left hc.ne')).symm⟩

end

end RefinedBMV.Tracial
