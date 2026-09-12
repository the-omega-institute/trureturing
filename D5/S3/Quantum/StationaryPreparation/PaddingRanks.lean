/- GID: D5/S3/Quantum/StationaryPreparation/PaddingRanks
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact individual and aggregate ranks of the actual padding Gram. -/

import D5.S3.Quantum.StationaryPreparation.PaddingBlocks
import Mathlib.Analysis.InnerProductSpace.TensorProduct

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

open SequentialRegisterCircuit PhysicalGram NormalizedResiduals OccupancyWordSectors
open StationaryOccupationResidualCircuit StationaryOccupationResidualStep
open scoped TensorProduct

/-- The actual fixed emission, transported through the letter-first tensor basis,
has the normalized occupation amplitudes. -/
theorem physical_normalized_emission
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (a r : Multiset A) (hr : r ≤ a) (hr0 : r ≠ 0) :
    let V : Space (Fin (proposedDimension a)) →ₗᵢ[ℂ]
        (Space A ⊗[ℂ] Space (Fin (proposedDimension a))) :=
      (((EuclideanSpace.basisFun A ℂ).tensorProduct
        (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr.symm.toLinearIsometry).comp
        (emission (maximalHead a) (physicalGate a))
    V (normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r) =
      ∑ i : A, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
        ((basis i : Space A) ⊗ₜ[ℂ]
          normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) (r.erase i)) := by
  classical
  have hs : ResidualStep a := by
    intro b hb hb0 i k
    by_cases ht : 0 < tailCount (maximalHead a) b
    · by_cases hi : i ∈ b
      · rw [if_pos hi]
        exact positive_residual_step a b hb ht i hi k
      · rw [if_neg hi]
        exact physical_residual_step_absent a b hb hb0 i hi k
    · exact physical_residual_step_tail_free a b hb hb0 (by omega) i k
  have hout : ∀ w k, circuit (fun _ => physicalGate a) a.card 0
      (initialized (maximalHead a) a.card (paddingInitial a)) (w,k) =
        sectorVector a.card a w * physicalFinal a k := physical_residual_output a hs
  let B := (EuclideanSpace.basisFun A ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)
  change B.repr.symm (emission (maximalHead a) (physicalGate a) _) = _
  apply B.repr.injective
  rw [B.repr.apply_symm_apply]
  ext ⟨i, k⟩
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, B,
    OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
    basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hletter : letter (maximalHead a) (physicalGate a) i
      (normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r) =
      (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
        normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) (r.erase i) := by
    by_cases hi : i ∈ r
    · exact normalized_letter_of_mem a _ _ _ (physicalFinal a) hout r hr hr0 i hi
    · rw [normalized_letter_of_not_mem a _ _ _ (physicalFinal a) hout r hr hr0 i hi,
        Multiset.count_eq_zero.mpr hi]
      simp
  exact congrArg (fun x : Space (Fin (proposedDimension a)) => x k) hletter

/-- The actual terminal memory emits the chosen head and remains fixed. -/
theorem physical_normalized_terminal_emission
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (a : Multiset A) :
    let V : Space (Fin (proposedDimension a)) →ₗᵢ[ℂ]
        (Space A ⊗[ℂ] Space (Fin (proposedDimension a))) :=
      (((EuclideanSpace.basisFun A ℂ).tensorProduct
        (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr.symm.toLinearIsometry).comp
        (emission (maximalHead a) (physicalGate a))
    V (normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) 0) =
      (basis (maximalHead a) : Space A) ⊗ₜ[ℂ]
        normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) 0 := by
  classical
  have hz := normalized_padding_identification a 0 (Multiset.zero_le a)
  rw [PaddingGram.normalized_padding_zero] at hz
  have he := coordinate_embedding_basis (physicalMemoryEquiv a).toEmbedding none
  change coordinateEmbedding _ (basis none) = basis (physicalMemoryEquiv a none) at he
  rw [he] at hz
  dsimp only
  rw [hz]
  let B := (EuclideanSpace.basisFun A ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)
  change B.repr.symm (emission (maximalHead a) (physicalGate a) _) = _
  apply B.repr.injective
  rw [B.repr.apply_symm_apply, emission_basis, physical_gate_sink]
  ext ⟨i, k⟩
  simp only [B, OrthonormalBasis.tensorProduct_repr_tmul_apply,
    EuclideanSpace.basisFun_repr, basis_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The prescribed tensor images preserve every finite dependence among legal
residuals, including the terminal branch. -/
theorem physical_normalized_dependencies
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {J : Type*} [Fintype J]
    (a : Multiset A) (r : J → Multiset A) (c : J → ℂ)
    (hr : ∀ j, r j ≤ a)
    (hdep : (∑ j : J, c j •
      normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) (r j)) = 0) :
    (∑ j : J, c j •
      (if r j = 0 then
        (basis (maximalHead a) : Space A) ⊗ₜ[ℂ]
          normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) 0
       else
        ∑ i : A, (Real.sqrt (((r j).count i : ℝ) / ((r j).card : ℝ)) : ℂ) •
          ((basis i : Space A) ⊗ₜ[ℂ]
            normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a)
              ((r j).erase i)))) = 0 := by
  classical
  let V := (((EuclideanSpace.basisFun A ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr.symm.toLinearIsometry).comp
      (emission (maximalHead a) (physicalGate a))
  have hmap := congrArg V hdep
  rw [map_sum, map_zero] at hmap
  simp only [map_smul] at hmap
  convert hmap using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  by_cases hj : r j = 0
  · rw [if_pos hj, hj]
    exact (physical_normalized_terminal_emission a).symm
  · rw [if_neg hj]
    exact (physical_normalized_emission a (r j) (hr j) hj).symm

/-- The actual normalized Gram has the full physical memory dimension as rank,
so the legal normalized residuals span that memory space. -/
theorem physical_normalized_span
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (a : Multiset A) :
    Submodule.span ℂ
      {v : Space (Fin (proposedDimension a)) |
        ∃ r : Multiset A, r ≤ a ∧ v = normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r} = ⊤ := by
  classical
  let S := Submodule.span ℂ
    {v : Space (Fin (proposedDimension a)) | ∃ r : Multiset A, r ≤ a ∧
      v = normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r}
  let v : TailBox a.count → S := fun r =>
    ⟨normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) (boxOccupation a r),
      Submodule.subset_span ⟨boxOccupation a r, box_occupation_le a r, rfl⟩⟩
  have hgram : Matrix.gram ℂ v =
      NormalizedGram.normalizedGram a (maximalHead a) (physicalGate a) (paddingInitial a) := by
    ext r s
    exact (Submodule.coe_inner S (v r) (v s)).symm
  have hbound : (Matrix.gram ℂ v).rank ≤ Module.finrank ℂ S := by
    rw [Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℂ S) v]
    exact (Matrix.rank_mul_le_right _ _).trans (by
      simpa using Matrix.rank_le_card_height
        (Matrix.of fun i r => (stdOrthonormalBasis ℂ S).repr (v r) i))
  rw [hgram, physical_source_gram_rank] at hbound
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le S)
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin (proposedDimension a))) ≤ _
  rw [finrank_euclideanSpace_fin]
  exact hbound

/-- A legal head singleton has exactly the same normalized memory as zero. -/
theorem physical_normalized_zero_eq_head
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (a : Multiset A)
    (hhead : 0 < a.count (maximalHead a)) :
    normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) 0 =
      normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) (Multiset.replicate 1 (maximalHead a)) := by
  have hlegal : Multiset.replicate 1 (maximalHead a) ≤ a := by
    simpa only [Multiset.replicate_one, Multiset.singleton_le] using
      (Multiset.count_pos.mp hhead)
  rw [normalized_padding_identification a 0 (Multiset.zero_le a),
    normalized_padding_identification a _ hlegal, PaddingGram.normalized_padding_zero,
    PaddingGram.normalized_padding_axis _ _ 1 hhead]

/-- With positive head count, the head singleton replaces the zero generator
without changing the full physical memory span. -/
theorem physical_normalized_nonterminal_span
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (a : Multiset A)
    (hhead : 0 < a.count (maximalHead a)) :
    Submodule.span ℂ
      {v : Space (Fin (proposedDimension a)) |
        ∃ r : Multiset A, r ≤ a ∧ r ≠ 0 ∧
          v = normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r} = ⊤ := by
  classical
  have hlegal : Multiset.replicate 1 (maximalHead a) ≤ a := by
    simpa only [Multiset.replicate_one, Multiset.singleton_le] using
      (Multiset.count_pos.mp hhead)
  rw [← top_le_iff, ← physical_normalized_span a]
  apply Submodule.span_le.mpr
  rintro v ⟨r, hr, rfl⟩
  apply Submodule.subset_span
  by_cases hr0 : r = 0
  · exact ⟨Multiset.replicate 1 (maximalHead a), hlegal, by simp,
      hr0 ▸ physical_normalized_zero_eq_head a hhead⟩
  · exact ⟨r, hr, hr0, rfl⟩

end D5.S3.Quantum.StationaryPreparation.PaddingRanks
