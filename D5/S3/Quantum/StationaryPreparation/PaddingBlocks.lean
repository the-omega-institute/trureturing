/- GID: D5/S3/Quantum/StationaryPreparation/PaddingBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual padding occupation blocks and their prescribed difference factorization. -/

import D5.S3.Quantum.StationaryPreparation.PaddingGram
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingBlocks
open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.StationaryPreparation
open PaddingMemory ResidualCalculus StationaryOccupationResidualCircuit
open PaddingGram PhysicalGram NormalizedResiduals
variable {A : Type*} [Fintype A] [DecidableEq A]

def occupationSplit (head : A) (a : Multiset A) :
    TailBox a.count ≃ Fin (a.count head + 1) ×
      TailBox (fun i : TailAlphabet head => a.count i.val) := Equiv.piSplitAt head _

def blockOccupation (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : Multiset A :=
  headSlice head (boxOccupation a ((occupationSplit head a).symm (0, b))) j

theorem block_occupation_index (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (j : Fin (a.count head + 1)) : blockOccupation head a b j.val =
      boxOccupation a ((occupationSplit head a).symm (j, b)) := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i
    simp [blockOccupation, occupationSplit, Equiv.piSplitAt]
  · simp [blockOccupation, head_slice_count_tail, hi, occupationSplit, Equiv.piSplitAt]

theorem block_occupation_tail (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) :
    tailCount head (blockOccupation head a b j) = tailSum b := by
  rw [blockOccupation, head_slice_tail_count]
  unfold tailCount tailSum
  apply Finset.sum_congr rfl
  intro i _
  simp [occupationSplit, Equiv.piSplitAt, i.property]

private theorem block_occupation_slice (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j k : ℕ) :
    headSlice head (blockOccupation head a b j) k = blockOccupation head a b k := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i; simp [blockOccupation]
  · simp [blockOccupation, head_slice_count_tail, hi]

private theorem block_filter_eq_iff (head : A) (a : Multiset A)
    (b c : TailBox (fun i : TailAlphabet head => a.count i.val)) (j k : ℕ) :
    (blockOccupation head a b j).filter (fun i => i ≠ head) =
      (blockOccupation head a c k).filter (fun i => i ≠ head) ↔ b = c := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have hc := congrArg (Multiset.count i.val) h
    simpa [blockOccupation, Multiset.count_filter, i.property,
      head_slice_count_tail, occupationSplit, Equiv.piSplitAt] using hc
  · rintro rfl
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · simp [blockOccupation, head_slice_count_tail, hi]

def blockMass (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : ℝ :=
  multiplicity (blockOccupation head a b j).card (blockOccupation head a b j)

def blockDifference (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : ℝ :=
  if j = 0 then blockMass head a b 0 else blockMass head a b j - blockMass head a b (j - 1)

/-- The prescribed factor has literal ones on and below its diagonal. -/
def lowerOnes (H : ℕ) : Matrix (Fin (H + 1)) (Fin (H + 1)) ℂ :=
  fun j k => if k ≤ j then 1 else 0

def paddingBlock (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    Matrix (Fin (a.count head + 1)) (Fin (a.count head + 1)) ℂ :=
  Matrix.gram ℂ (fun j => paddingResidual head a (blockOccupation head a b j.val))

def paddingGram (head : A) (a : Multiset A) : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => paddingResidual head a (boxOccupation a r))

def normalizedPaddingGram (head : A) (a : Multiset A) :
    Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => normalizedPadding head a (boxOccupation a r))

theorem padding_gram_eq_diagonal (head : A) (a : Multiset A) : paddingGram head a =
    NormalizedGram.normalizationDiagonal a * normalizedPaddingGram head a *
      NormalizedGram.normalizationDiagonal a := by
  classical
  ext r s
  simp only [paddingGram, normalizedPaddingGram, NormalizedGram.normalizationDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply,
    normalizedPadding, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
  field_simp [scale_ne_zero (boxOccupation a r), scale_ne_zero (boxOccupation a s)]

theorem padding_gram_rank_eq (head : A) (a : Multiset A) :
    (paddingGram head a).rank = (normalizedPaddingGram head a).rank := by
  classical
  rw [padding_gram_eq_diagonal,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (NormalizedGram.diagonal_det_ne_zero a),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (NormalizedGram.diagonal_det_ne_zero a)]

theorem padding_block_entry (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (j k : Fin (a.count head + 1)) :
    paddingBlock head a b j k = (blockMass head a b (min j.val k.val) : ℂ) := by
  have hj : blockOccupation head a b j.val ≤ a := by
    rw [block_occupation_index]; exact box_occupation_le a _
  have hk : blockOccupation head a b k.val ≤ a := by
    rw [block_occupation_index]; exact box_occupation_le a _
  rw [paddingBlock, Matrix.gram_apply, padding_residual_inner head a _ _ hj hk,
    if_pos ((block_filter_eq_iff head a b b j.val k.val).mpr rfl)]
  have hjc : (blockOccupation head a b j.val).count head = j.val := by
    simp [blockOccupation]
  have hkc : (blockOccupation head a b k.val).count head = k.val := by
    simp [blockOccupation]
  simp only [hjc, hkc, block_occupation_slice, blockMass, Complex.ofReal_natCast]

theorem padding_gram_blocks (head : A) (a : Multiset A) :
    (paddingGram head a).reindex (occupationSplit head a) (occupationSplit head a) =
      Matrix.blockDiagonal (paddingBlock head a) := by
  classical
  ext ⟨j,b⟩ ⟨k,c⟩
  change inner ℂ (paddingResidual head a (boxOccupation a ((occupationSplit head a).symm (j,b))))
    (paddingResidual head a (boxOccupation a ((occupationSplit head a).symm (k,c)))) = _
  rw [← block_occupation_index, ← block_occupation_index, Matrix.blockDiagonal_apply']
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl]
    rfl
  · rw [if_neg hbc, padding_residual_inner head a _ _]
    · rw [if_neg (fun h => hbc ((block_filter_eq_iff head a b c j.val k.val).mp h))]
    all_goals rw [block_occupation_index]; exact box_occupation_le a _

theorem lower_ones_det (H : ℕ) : (lowerOnes H).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    exact if_neg (not_le.mpr hij))]
  simp [lowerOnes]

theorem padding_block_factorization (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    paddingBlock head a b = lowerOnes (a.count head) *
      Matrix.diagonal (fun j : Fin (a.count head + 1) => (blockDifference head a b j.val : ℂ)) *
        (lowerOnes (a.count head)).transpose := by
  ext j k
  rw [padding_block_entry]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  let m := min j.val k.val
  have hm : m + 1 ≤ a.count head + 1 := by dsimp [m]; omega
  have ht : (∑ l : Fin (a.count head + 1), lowerOnes (a.count head) j l *
      (blockDifference head a b l.val : ℂ) * lowerOnes (a.count head) k l) =
      ∑ l ∈ Finset.range (a.count head + 1),
        if l ≤ m then (blockDifference head a b l : ℂ) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hjl : l ≤ j
    · by_cases hkl : l ≤ k
      · have hl : l.val ≤ m := le_min hjl hkl
        simp only [lowerOnes, if_pos hjl, if_pos hkl, if_pos hl, one_mul, mul_one]
      · have hl : ¬l.val ≤ m := by dsimp [m]; intro h; exact hkl (le_trans h (min_le_right _ _))
        simp only [lowerOnes, if_pos hjl, if_neg hkl, if_neg hl, mul_zero]
    · have hl : ¬l.val ≤ m := by dsimp [m]; intro h; exact hjl (le_trans h (min_le_left _ _))
      simp only [lowerOnes, if_neg hjl, if_neg hl, zero_mul]
  rw [ht]
  symm
  calc
    _ = ∑ l ∈ Finset.range (m + 1),
        if l ≤ m then (blockDifference head a b l : ℂ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hm)
      intro l _ hl
      rw [if_neg (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)]
    _ = ∑ l ∈ Finset.range (m + 1), (blockDifference head a b l : ℂ) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [if_pos (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)]
    _ = (blockMass head a b m : ℂ) := by
      simp only [blockDifference, apply_ite (Complex.ofReal), Complex.ofReal_sub]
      exact (Finset.eq_sum_range_sub' (fun n => (blockMass head a b n : ℂ)) m).symm

theorem block_difference_pos (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (hb : b ≠ zeroTail _) (j : ℕ) : 0 < blockDifference head a b j := by
  have hr : 0 < tailCount head (blockOccupation head a b 0) := by
    rw [block_occupation_tail]
    exact positive_tail_sum _ ⟨b, hb⟩
  have h := last_tail_mass_head_slice head (blockOccupation head a b 0) hr j
  rw [block_occupation_slice, block_occupation_slice, block_occupation_slice] at h
  change lastTailMass head (blockOccupation head a b j) = blockDifference head a b j at h
  rw [← h]
  apply last_tail_mass_pos
  rw [block_occupation_tail]
  exact positive_tail_sum _ ⟨b, hb⟩

theorem block_mass_strict (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (hb : b ≠ zeroTail _) (j : ℕ) (hj : 0 < j) :
    blockMass head a b (j - 1) < blockMass head a b j := by
  have h := block_difference_pos head a b hb j
  simpa only [blockDifference, if_neg (Nat.ne_of_gt hj), sub_pos] using h

theorem block_difference_zero_tail (head : A) (a : Multiset A) (j : ℕ) :
    blockDifference head a (zeroTail _) j = if j=0 then 1 else 0 := by
  have hm (n : ℕ) : blockMass head a (zeroTail _) n = 1 := by
    have hv : blockOccupation head a (zeroTail _) n = Multiset.replicate n head := by
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp [blockOccupation]
      · simp [blockOccupation, head_slice_count_tail, hi, occupationSplit,
          Equiv.piSplitAt, zeroTail, Multiset.count_replicate, Ne.symm hi]
    rw [blockMass, hv, Multiset.card_replicate,
      multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
    simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
    simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Nat.div_self (Nat.factorial_pos n), Nat.cast_one]
  simp [blockDifference, hm]

open StationaryOccupationPadding StationaryOccupationResidualStep
variable [Nonempty A]

/-- The initial vector used by the actual C fixed-unitary construction. -/
def paddingInitial (a : Multiset A) : Space (Fin (proposedDimension a)) :=
  (residualScale a : ℂ)⁻¹ • physicalResidual a a

/-- Prefix-derived physical residuals are the actual chosen padding residuals,
with no unidentified-vector premise. -/
theorem padding_residual_identification (a r : Multiset A) (hr : r ≤ a) :
    residualMemory a (maximalHead a) (physicalGate a) (paddingInitial a) r =
      physicalResidual a r := by
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
        sectorVector a.card a w * physicalFinal a k :=
    physical_residual_output a hs
  apply suffix_injective (maximalHead a) (physicalGate a) r.card
  intro w
  rw [residual_output a (maximalHead a) (physicalGate a) (paddingInitial a)
    (physicalFinal a) hout r hr _ List.length_ofFn]
  ext k
  rw [← circuit_fixed_coefficients (maximalHead a) (physicalGate a) r.card 0]
  have hc := circuit_output_of_residuals (maximalHead a) (physicalGate a) a
    (physicalResidual a) (physicalFinal a) (physical_residual_zero a) hs
    r.card 0 r rfl hr w k
  rw [hc]
  by_cases hw : occupation w = r <;> simp [occupation] at hw ⊢ <;> simp [hw]

theorem normalized_padding_identification (a r : Multiset A) (hr : r ≤ a) :
    normalizedResidual a (maximalHead a) (physicalGate a) (paddingInitial a) r =
      coordinateEmbedding (physicalMemoryEquiv a).toEmbedding
        (normalizedPadding (maximalHead a) a r) := by
  rw [normalizedResidual, padding_residual_identification a r hr,
    normalizedPadding, map_smul]
  rfl

theorem padding_source_moment_identification (a r : Multiset A) (hr : r ≤ a) :
    sourceMoment a (maximalHead a) (physicalGate a) (paddingInitial a) (physicalFinal a) r =
      paddingMoment (maximalHead a) a r := by
  have hf : physicalFinal a =
      coordinateEmbedding (physicalMemoryEquiv a).toEmbedding (basis none) :=
    (coordinate_embedding_basis (physicalMemoryEquiv a).toEmbedding none).symm
  rw [sourceMoment, normalized_padding_identification a r hr, hf,
    (coordinateEmbedding (physicalMemoryEquiv a).toEmbedding).inner_map_map]
  rfl

theorem padding_normalized_gram_identification (a : Multiset A) :
    NormalizedGram.normalizedGram a (maximalHead a) (physicalGate a) (paddingInitial a) =
      normalizedPaddingGram (maximalHead a) a := by
  ext r s
  simp only [NormalizedGram.normalizedGram, normalizedPaddingGram, Matrix.gram_apply,
    normalized_padding_identification a _ (box_occupation_le a _),
    (coordinateEmbedding (physicalMemoryEquiv a).toEmbedding).inner_map_map]

end D5.S3.Quantum.StationaryPreparation.PaddingBlocks
