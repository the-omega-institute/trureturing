/- GID: D5/S3/Quantum/StationaryPreparation/PaddingRanks
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact individual and aggregate ranks of the actual padding Gram. -/

import D5.S3.Quantum.StationaryPreparation.PaddingBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingRanks
open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement
open D5.S3.Quantum.StationaryPreparation.PaddingMemory
open D5.S3.Quantum.StationaryPreparation.PaddingBlocks
variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem block_rank_diagonal (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    (paddingBlock head a b).rank =
      (Matrix.diagonal (fun j : Fin (a.count head + 1) =>
        (blockDifference head a b j.val : ℂ))).rank := by
  rw [padding_block_factorization,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by
      rw [Matrix.det_transpose, lower_ones_det]
      norm_num),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by rw [lower_ones_det]; norm_num)]

theorem padding_block_rank_zero (head : A) (a : Multiset A) :
    (paddingBlock head a (zeroTail _)).rank = 1 := by
  classical
  rw [block_rank_diagonal, Matrix.rank_diagonal]
  have hn (j : Fin (a.count head + 1)) :
      (blockDifference head a (zeroTail _) j.val : ℂ) ≠ 0 ↔ j = 0 := by
    simp [block_difference_zero_tail]
  simp only [hn]
  exact Fintype.card_subtype_eq (0 : Fin (a.count head + 1))

theorem padding_block_rank_positive (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (hb : b ≠ zeroTail _) :
    (paddingBlock head a b).rank = a.count head + 1 := by
  classical
  rw [block_rank_diagonal, Matrix.rank_diagonal]
  have hn (j : Fin (a.count head + 1)) : (blockDifference head a b j.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (block_difference_pos head a b hb j.val).ne'
  simp [hn]

private theorem difference_zero_iff (head : A) (a : Multiset A)
    (p : Fin (a.count head + 1) × TailBox (fun i : TailAlphabet head => a.count i.val)) :
    (blockDifference head a p.2 p.1.val : ℂ) = 0 ↔ p.2 = zeroTail _ ∧ p.1 ≠ 0 := by
  by_cases hb : p.2 = zeroTail _
  · rw [hb, block_difference_zero_tail]
    simp
  · have hn := Complex.ofReal_ne_zero.mpr (block_difference_pos head a p.2 hb p.1.val).ne'
    simp [hb, hn]

/-- The actual occupation matrix is transported to its tail blocks, then to the
prescribed diagonal. Its only zero pivots are the nonzero pure-head indices. -/
theorem padding_gram_rank (head : A) (a : Multiset A) :
    (paddingGram head a).rank = (∏ i : A, (a.count i + 1)) - a.count head := by
  classical
  let T := TailBox (fun i : TailAlphabet head => a.count i.val)
  let P := Fin (a.count head + 1) × T
  let L : Matrix P P ℂ := Matrix.blockDiagonal (fun _ : T => lowerOnes (a.count head))
  let w : P → ℂ := fun p => blockDifference head a p.2 p.1.val
  have hf : Matrix.blockDiagonal (paddingBlock head a) = L * Matrix.diagonal w * L.transpose := by
    change Matrix.blockDiagonal (fun b : T => paddingBlock head a b) = _
    simp_rw [padding_block_factorization]
    rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_diagonal]
    rw [← Matrix.blockDiagonal_transpose]
  have hL : L.det ≠ 0 := by
    dsimp [L]
    rw [Matrix.det_blockDiagonal]
    simp [lower_ones_det]
  have hr : (paddingGram head a).rank = Fintype.card {p : P // w p ≠ 0} := by
    rw [← Matrix.rank_reindex (occupationSplit head a) (occupationSplit head a),
      padding_gram_blocks, hf,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by rwa [Matrix.det_transpose]),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hL, Matrix.rank_diagonal]
  have hz : Fintype.card {p : P // w p = 0} = a.count head := by
    let e : {p : P // w p = 0} ≃ {j : Fin (a.count head + 1) // j ≠ 0} :=
      { toFun := fun p => ⟨p.val.1, ((difference_zero_iff head a p.val).mp p.property).2⟩
        invFun := fun j => ⟨(j.val, zeroTail _),
          (difference_zero_iff head a _).mpr ⟨rfl, j.property⟩⟩
        left_inv := by
          intro p
          apply Subtype.ext
          change (p.val.1, zeroTail _) = p.val
          have hb := ((difference_zero_iff head a p.val).mp p.property).1
          exact congrArg (fun b : T => (p.val.1, b)) hb.symm
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun j : Fin (a.count head + 1) => j=0)]
    simp
  rw [hr, Fintype.card_subtype_compl (fun p : P => w p = 0), hz]
  congr 1
  calc
    Fintype.card P = Fintype.card (TailBox a.count) :=
      (Fintype.card_congr (occupationSplit head a)).symm
    _ = ∏ i : A, (a.count i + 1) := by simp [TailBox, Fintype.card_pi]

theorem normalized_padding_gram_rank (head : A) (a : Multiset A) :
    (normalizedPaddingGram head a).rank = (∏ i : A, (a.count i + 1)) - a.count head := by
  rw [← padding_gram_rank_eq, padding_gram_rank]

theorem maximal_padding_gram_rank (head : A) (a : Multiset A)
    (hh : a.count head = Finset.univ.sup a.count) :
    (normalizedPaddingGram head a).rank =
      (∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count := by
  rw [normalized_padding_gram_rank, hh]

theorem zero_padding_gram_rank (head : A) :
    (normalizedPaddingGram head (0 : Multiset A)).rank = 1 := by
  rw [normalized_padding_gram_rank]
  simp

theorem occupation_5040_padding_gram_rank :
    (paddingGram (none : Option (Fin 3)) CoherentHistorySchmidt.occupation5040).rank = 1 + 11 * 5 ∧
      (normalizedPaddingGram (none : Option (Fin 3)) CoherentHistorySchmidt.occupation5040).rank =
        56 := by
  rw [padding_gram_rank, normalized_padding_gram_rank]
  norm_num [CoherentHistorySchmidt.occupation5040, OccupancyWordSectors.capacity_occupation_count,
    Fintype.prod_option, tailCapacities5040, Fin.prod_univ_succ]

open D5.S3.Quantum.StationaryPreparation
open StationaryOccupationPadding ResidualCalculus
variable [Nonempty A]

theorem physical_source_moments (a r : Multiset A) (hr : r ≤ a) :
    NormalizedResiduals.sourceMoment a (maximalHead a) (physicalGate a) (paddingInitial a)
      (physicalFinal a) r = if tailCount (maximalHead a) r = 0 then 1 else 0 := by
  rw [padding_source_moment_identification a r hr, PaddingGram.padding_moment _ _ _ hr]

theorem physical_source_gram_rank (a : Multiset A) :
    (NormalizedGram.normalizedGram a (maximalHead a) (physicalGate a) (paddingInitial a)).rank =
      (∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count := by
  rw [padding_normalized_gram_identification]
  exact maximal_padding_gram_rank _ _ (maximal_head_spec a)

end D5.S3.Quantum.StationaryPreparation.PaddingRanks
