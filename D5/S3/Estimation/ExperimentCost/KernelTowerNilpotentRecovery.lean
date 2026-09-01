/- GID: D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel increments and finite towers recover block profiles, including zero and one. -/
/- Library-search audit trail (2026-08-25):
   * Read the actual declarations in `IntegerRecoveryStructureSeparation` (FPOD 188.1).
     Its `power_trace_similarity_residual_witness` exposes equal characteristic
     polynomials and failed conjugacy for a two-dimensional zero/square-zero pair.
   * Repository searches found three Jordan mentions and six `IsNilpotent` mentions;
     none supplies a Jordan normal form or a nilpotent similarity classifier.
   * Pinned Mathlib's `IsNilpotent` is the generic `exists n, x ^ n = 0` predicate.
     Searches of all `Mathlib/LinearAlgebra` sources found Jordan-Chevalley decomposition,
     but no Jordan canonical-form existence or uniqueness theorem.
   * `Module.End.ker_pow_eq_ker_pow_finrank_of_le` is an exact hit and proves that the
     actual matrix kernel tower stabilizes by the ambient dimension.
   * `LinearMap.finrank_range_add_finrank_ker`, `Matrix.rank`, `LinearMap.ker`, and
     `Module.finrank` are used with their checked signatures below.
   * Path B is selected: positive block profiles are recovered up to multiset equality,
     a decidable equivalence. Matrix conjugacy is not claimed without the missing Jordan
     classifier. Paths C and D are unnecessary; Path A's classification endpoint is omitted.
   * This complements rather than repeats FPOD 188.1: that module proves charpoly is too
     weak, while `kernel_tower_separates_charpoly_residual` proves its exact witness is
     separated by the first kernel dimension. No prime parameter or algebraic closure is used.
     The tower definition needs only a commutative semiring; the matrix stabilization API and
     imported characteristic-polynomial residual are stated over fields.
   * The selected directory had two Lean files before this module and has three after it.
-/

import D5.S3.Observer.ProbabilisticClosure.IntegerRecoveryStructureSeparation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery

open scoped BigOperators

/- A block size is positive by construction. Thus no separate positivity hypothesis can
   be forgotten, and the zero-dimensional profile contains no blocks. -/

/-- The positive size of one abstract nilpotent Jordan block. -/
abbrev PositiveBlockSize := {size : Nat // 0 < size}

/-- An unordered finite family of positive block sizes. -/
abbrev BlockMultiset := Multiset PositiveBlockSize

/-- The ambient dimension represented by a block multiset. -/
def blockProfileDimension (blocks : BlockMultiset) : Nat :=
  (blocks.map Subtype.val).sum

/-- A nilpotent block profile whose block dimensions sum to `n`. -/
abbrev NilpotentBlockProfile (n : Nat) :=
  {blocks : BlockMultiset // blockProfileDimension blocks = n}

/-- The abstract kernel dimension `a_k`, computed directly from positive block sizes. -/
def blockKernelTower (blocks : BlockMultiset) (k : Nat) : Nat :=
  (blocks.map fun size => min k size.1).sum

/-- The named increment `b_k = a_k - a_(k-1)` from FPOD 186.1. -/
def kernelIncrement (blocks : BlockMultiset) (k : Nat) : Nat :=
  blockKernelTower blocks k - blockKernelTower blocks k.pred

/-- The number of blocks whose positive size is at least `k`. -/
def blockCountAtLeast (blocks : BlockMultiset) (k : Nat) : Nat :=
  blocks.countP fun size => k <= size.1

/-- The number of blocks whose positive size is exactly `k`. -/
def blockCountExactly (blocks : BlockMultiset) (k : Nat) : Nat :=
  blocks.countP fun size => size.1 = k

private theorem min_succ_eq_add_indicator (k size : Nat) :
    min (k + 1) size = min k size + if k + 1 <= size then 1 else 0 := by
  by_cases h : k + 1 <= size
  · rw [if_pos h, Nat.min_eq_left h, Nat.min_eq_left (by omega)]
  · rw [if_neg h, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    simp

private theorem countP_replicate_eq {A : Type*} (predicate : A -> Prop)
    [DecidablePred predicate] (n : Nat) (value : A) :
    (Multiset.replicate n value).countP predicate =
      if predicate value then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
      by_cases h : predicate value <;> simp [h]

private theorem block_kernel_tower_succ (blocks : BlockMultiset) (k : Nat) :
    blockKernelTower blocks (k + 1) =
      blockKernelTower blocks k + blockCountAtLeast blocks (k + 1) := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower, blockCountAtLeast]
  | @cons size blocks ih =>
      simp only [blockKernelTower, Multiset.map_cons, Multiset.sum_cons,
        blockCountAtLeast, Multiset.countP_cons]
      have ih' : (blocks.map fun size => min (k + 1) size.1).sum =
          (blocks.map fun size => min k size.1).sum +
            blocks.countP (fun size => k + 1 <= size.1) := by
        simpa [blockKernelTower, blockCountAtLeast] using ih
      rw [min_succ_eq_add_indicator, ih']
      split <;> omega

/-- FPOD theorem 186.1: the positive-index kernel increment counts blocks of size
at least that index. Writing the index as `k + 1` makes positivity definitional. -/
theorem kernel_increment_counts_blocks_at_least (blocks : BlockMultiset) (k : Nat) :
    kernelIncrement blocks (k + 1) = blockCountAtLeast blocks (k + 1) := by
  rw [kernelIncrement, Nat.pred_eq_of_eq_succ rfl, block_kernel_tower_succ]
  omega

#print axioms kernel_increment_counts_blocks_at_least

private theorem block_count_at_least_decomposition (blocks : BlockMultiset) (k : Nat) :
    blockCountAtLeast blocks k =
      blockCountExactly blocks k + blockCountAtLeast blocks (k + 1) := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockCountAtLeast, blockCountExactly]
  | @cons size blocks ih =>
      change Multiset.countP (fun size => k <= size.1) blocks =
        Multiset.countP (fun size => size.1 = k) blocks +
          Multiset.countP (fun size => k + 1 <= size.1) blocks at ih
      simp only [blockCountAtLeast, blockCountExactly, Multiset.countP_cons]
      rw [ih]
      by_cases heq : size.1 = k
      · simp [heq, add_assoc, add_comm]
      · by_cases hsucc : k + 1 <= size.1
        · have hle : k <= size.1 := by omega
          simp [heq, hsucc, hle, add_left_comm, add_comm]
        · have hle : Not (k <= size.1) := by omega
          simp [heq, hsucc, hle]

/-- FPOD corollary 186.1's formula: exact size `k` is `b_k - b_(k+1)`. -/
theorem exact_block_count_from_successive_increments (blocks : BlockMultiset) (k : Nat) :
    blockCountExactly blocks k =
      kernelIncrement blocks k - kernelIncrement blocks (k + 1) := by
  cases k with
  | zero =>
      have hzero : blockCountExactly blocks 0 = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro size _ hsize
        exact (Nat.ne_of_gt size.property) hsize
      simp [kernelIncrement, blockKernelTower, hzero]
  | succ k =>
      rw [kernel_increment_counts_blocks_at_least,
        kernel_increment_counts_blocks_at_least]
      have h := block_count_at_least_decomposition blocks (k + 1)
      omega

#print axioms exact_block_count_from_successive_increments

private theorem all_kernel_towers_recover_block_multiset
    {left right : BlockMultiset}
    (towerEqual : forall k, blockKernelTower left k = blockKernelTower right k) :
    left = right := by
  apply Multiset.ext.mpr
  intro size
  have hLeft := exact_block_count_from_successive_increments left size.1
  have hRight := exact_block_count_from_successive_increments right size.1
  calc
    left.count size = blockCountExactly left size.1 := by
      simp [Multiset.count, blockCountExactly, Subtype.ext_iff, eq_comm]
    _ = kernelIncrement left size.1 - kernelIncrement left (size.1 + 1) := hLeft
    _ = kernelIncrement right size.1 - kernelIncrement right (size.1 + 1) := by
      simp [kernelIncrement, towerEqual]
    _ = blockCountExactly right size.1 := hRight.symm
    _ = right.count size := by
      simp [Multiset.count, blockCountExactly, Subtype.ext_iff, eq_comm]

private theorem block_kernel_tower_eq_dimension_of_le
    (blocks : BlockMultiset) {k : Nat} (bound : blockProfileDimension blocks <= k) :
    blockKernelTower blocks k = blockProfileDimension blocks := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower, blockProfileDimension]
  | @cons size blocks ih =>
      have hdim : blockProfileDimension (size ::ₘ blocks) =
          size.1 + blockProfileDimension blocks := by
        simp [blockProfileDimension]
      rw [hdim] at bound
      have hsize : size.1 <= k := by omega
      have htail : blockProfileDimension blocks <= k := by omega
      simp only [blockKernelTower, Multiset.map_cons, Multiset.sum_cons,
        blockProfileDimension]
      have ih' : (blocks.map fun size => min k size.1).sum =
          (blocks.map Subtype.val).sum := by
        simpa [blockKernelTower, blockProfileDimension] using ih htail
      rw [Nat.min_eq_right hsize, ih']

/-- The finite tower `(a_1, ..., a_n)` recovers an `n`-dimensional positive block
profile exactly. Multiset equality is the Path B decidable block-profile equivalence. -/
theorem finite_kernel_tower_recovers_block_profile {n : Nat}
    (left right : NilpotentBlockProfile n)
    (towerEqual : forall k, 0 < k -> k <= n ->
      blockKernelTower left.1 k = blockKernelTower right.1 k) :
    left = right := by
  apply Subtype.ext
  apply all_kernel_towers_recover_block_multiset
  intro k
  by_cases hkzero : k = 0
  · simp [hkzero, blockKernelTower]
  by_cases hk : k <= n
  · exact towerEqual k (Nat.pos_of_ne_zero hkzero) hk
  · have hnle : n <= k := by omega
    rw [block_kernel_tower_eq_dimension_of_le left.1
        (by simpa [left.2] using hnle),
      block_kernel_tower_eq_dimension_of_le right.1
        (by simpa [right.2] using hnle), left.2, right.2]

#print axioms finite_kernel_tower_recovers_block_profile

/-- The actual matrix invariant `a_k = dim ker(N^k)`. -/
noncomputable def matrixKernelDimensionTower {K : Type*} [CommSemiring K] {n : Nat}
    (N : Matrix (Fin n) (Fin n) K) (k : Nat) : Nat :=
  Module.finrank K (LinearMap.ker (N.mulVecLin ^ k))

/-- Every actual matrix kernel tower stabilizes by dimension `n`, so the nilpotent
case needs no values beyond `a_n`. Nilpotence is not needed for this stronger bound. -/
theorem matrix_kernel_tower_stabilizes_at_dimension
    {K : Type*} [Field K] {n k : Nat}
    (N : Matrix (Fin n) (Fin n) K) (bound : n <= k) :
    matrixKernelDimensionTower N k = matrixKernelDimensionTower N n := by
  have hfinrank : Module.finrank K (Fin n -> K) = n := by simp
  unfold matrixKernelDimensionTower
  rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := N.mulVecLin)
    (by simpa [hfinrank] using bound), hfinrank]

#print axioms matrix_kernel_tower_stabilizes_at_dimension

/-- The unique positive block size one. -/
def unitBlockSize : PositiveBlockSize := ⟨1, by omega⟩

/-- The profile of the `n`-dimensional zero matrix: `n` blocks of size one. -/
def zeroMatrixBlockProfile (n : Nat) : NilpotentBlockProfile n :=
  ⟨Multiset.replicate n unitBlockSize, by
    simp only [blockProfileDimension, Multiset.map_replicate,
      Multiset.sum_replicate, unitBlockSize]
    change n * 1 = n
    omega⟩

/-- The profile consisting of one positive nilpotent block. -/
def singleNilpotentBlockProfile (size : PositiveBlockSize) :
    NilpotentBlockProfile size.1 :=
  ⟨{size}, by simp [blockProfileDimension]⟩

/-- For the zero matrix profile, every positive kernel dimension is `n`, only
`b_1` is nonzero, and exactly `n` blocks have size one. -/
theorem zero_matrix_block_profile_audit (n : Nat) :
    blockCountExactly (zeroMatrixBlockProfile n).1 1 = n ∧
      (forall k, 0 < k -> blockKernelTower (zeroMatrixBlockProfile n).1 k = n) ∧
      kernelIncrement (zeroMatrixBlockProfile n).1 1 = n ∧
      forall k, 2 <= k -> kernelIncrement (zeroMatrixBlockProfile n).1 k = 0 := by
  constructor
  · simp only [zeroMatrixBlockProfile, blockCountExactly]
    rw [countP_replicate_eq]
    change (if (1 : Nat) = 1 then n else 0) = n
    simp
  constructor
  · intro k hk
    simp only [zeroMatrixBlockProfile, blockKernelTower,
      Multiset.map_replicate, Multiset.sum_replicate, unitBlockSize]
    change n * min k 1 = n
    rw [Nat.min_eq_right hk]
    omega
  constructor
  · rw [kernel_increment_counts_blocks_at_least]
    simp only [zeroMatrixBlockProfile, blockCountAtLeast]
    rw [countP_replicate_eq]
    change (if (1 : Nat) <= 1 then n else 0) = n
    simp
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [kernel_increment_counts_blocks_at_least]
    simp only [zeroMatrixBlockProfile, blockCountAtLeast]
    rw [countP_replicate_eq]
    change (if j + 1 <= 1 then n else 0) = 0
    simp [show Not (j + 1 <= 1) by omega]

#print axioms zero_matrix_block_profile_audit

/-- A single positive block has `a_k = min(k, size)` and the expected one-or-zero
counts for sizes at least and exactly `k`. -/
theorem single_nilpotent_block_profile_audit (size : PositiveBlockSize) (k : Nat) :
    blockKernelTower (singleNilpotentBlockProfile size).1 k = min k size.1 ∧
      blockCountAtLeast (singleNilpotentBlockProfile size).1 k =
        (if k <= size.1 then 1 else 0) ∧
      blockCountExactly (singleNilpotentBlockProfile size).1 k =
        (if size.1 = k then 1 else 0) := by
  constructor
  · simp [singleNilpotentBlockProfile, blockKernelTower]
  constructor
  · simp only [singleNilpotentBlockProfile, blockCountAtLeast]
    rw [show ({size} : BlockMultiset) = size ::ₘ 0 by rfl,
      Multiset.countP_cons]
    simp
  · simp only [singleNilpotentBlockProfile, blockCountExactly]
    rw [show ({size} : BlockMultiset) = size ::ₘ 0 by rfl,
      Multiset.countP_cons]
    simp

#print axioms single_nilpotent_block_profile_audit

private theorem block_profile_dimension_eq_zero_iff (blocks : BlockMultiset) :
    blockProfileDimension blocks = 0 ↔ blocks = 0 := by
  constructor
  · intro hzero
    induction blocks using Multiset.induction_on with
    | empty => rfl
    | @cons size blocks _ =>
        have hdim : blockProfileDimension (size ::ₘ blocks) =
            size.1 + blockProfileDimension blocks := by
          simp [blockProfileDimension]
        rw [hdim] at hzero
        omega
  · rintro rfl
    simp [blockProfileDimension]

/-- In dimension zero the only positive block profile is empty and its tower is zero. -/
theorem zero_dimensional_block_profile_audit (profile : NilpotentBlockProfile 0) :
    profile.1 = 0 ∧ forall k, blockKernelTower profile.1 k = 0 := by
  have hempty : profile.1 = 0 := by
    exact block_profile_dimension_eq_zero_iff profile.1 |>.mp profile.2
  simp [hempty, blockKernelTower]

#print axioms zero_dimensional_block_profile_audit

/-- In dimension one the only positive profile is one block of size one. -/
theorem one_dimensional_block_profile_audit (profile : NilpotentBlockProfile 1) :
    profile = zeroMatrixBlockProfile 1 := by
  apply finite_kernel_tower_recovers_block_profile
  intro k hk hkn
  have hkone : k = 1 := by omega
  subst k
  rw [block_kernel_tower_eq_dimension_of_le profile.1 (by simp [profile.2]),
    block_kernel_tower_eq_dimension_of_le (zeroMatrixBlockProfile 1).1
      (by simp [(zeroMatrixBlockProfile 1).2]), profile.2,
    (zeroMatrixBlockProfile 1).2]

#print axioms one_dimensional_block_profile_audit

/-- The positive-index restriction in theorem 186.1 is necessary: at index zero,
the singleton size-one profile has increment zero but one block of size at least zero. -/
theorem positive_index_is_necessary :
    kernelIncrement (singleNilpotentBlockProfile unitBlockSize).1 0 ≠
      blockCountAtLeast (singleNilpotentBlockProfile unitBlockSize).1 0 := by
  norm_num [kernelIncrement, blockKernelTower, blockCountAtLeast,
    singleNilpotentBlockProfile, unitBlockSize]
  change 0 ≠ Multiset.card ({unitBlockSize} : BlockMultiset)
  rw [Multiset.card_singleton]
  omega

#print axioms positive_index_is_necessary

/-- Equality of the finite tower is necessary for recovery: in dimension two, one
size-two block and two size-one blocks already differ at `a_1`. -/
theorem kernel_tower_equality_is_necessary :
    exists left right : NilpotentBlockProfile 2,
      left ≠ right ∧ blockKernelTower left.1 1 ≠ blockKernelTower right.1 1 := by
  let twoBlock : PositiveBlockSize := ⟨2, by omega⟩
  have htower : blockKernelTower (singleNilpotentBlockProfile twoBlock).1 1 ≠
      blockKernelTower (zeroMatrixBlockProfile 2).1 1 := by
    have hsingle := (single_nilpotent_block_profile_audit twoBlock 1).1
    have hzero := (zero_matrix_block_profile_audit 2).2.1 1 (by omega)
    have htwo : twoBlock.1 = 2 := rfl
    conv at hsingle => rhs; rw [htwo]
    norm_num at hsingle
    omega
  exact ⟨singleNilpotentBlockProfile twoBlock, zeroMatrixBlockProfile 2,
    fun equalProfiles => htower (congrArg (fun profile => blockKernelTower profile.1 1)
      equalProfiles), htower⟩

#print axioms kernel_tower_equality_is_necessary

/-- The kernel tower distinguishes FPOD 188.1's exact residual witness: both matrices
are nilpotent with equal charpoly and are not conjugate, but their first kernels have
dimensions two and one. The square-zero tower then reaches dimension two. -/
theorem kernel_tower_separates_charpoly_residual {K : Type*} [Field K] :
    let A : Matrix (Fin 2) (Fin 2) K := 0
    let N : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 1 1
    A.charpoly = N.charpoly ∧ IsNilpotent A ∧ IsNilpotent N ∧
      (¬(exists P : (Matrix (Fin 2) (Fin 2) K)ˣ,
        (P : Matrix (Fin 2) (Fin 2) K) * A *
          (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = N)) ∧
      matrixKernelDimensionTower A 1 = 2 ∧
      matrixKernelDimensionTower N 1 = 1 ∧
      matrixKernelDimensionTower N 2 = 2 := by
  dsimp only
  let N : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 1 1
  have hResidual :=
    D5.S0.Observation.PowerTraceSimilarityCountermodel.power_traces_do_not_determine_similarity
      (K := K)
  dsimp only at hResidual
  rcases hResidual with ⟨_, hCharA, hCharN, _, hRankN, hNotConjugate, _⟩
  have hN2 : N ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, N, Matrix.mul_apply, Fin.sum_univ_two]
  have hTowerA : matrixKernelDimensionTower
      (0 : Matrix (Fin 2) (Fin 2) K) 1 = 2 := by
    have hnullity := LinearMap.finrank_range_add_finrank_ker
      ((0 : Matrix (Fin 2) (Fin 2) K).mulVecLin ^ 1)
    have hrange : Module.finrank K
        (LinearMap.range ((0 : Matrix (Fin 2) (Fin 2) K).mulVecLin ^ 1)) = 0 := by
      simp
    rw [hrange, show Module.finrank K (Fin 2 -> K) = 2 by simp] at hnullity
    unfold matrixKernelDimensionTower
    omega
  have hTowerN1 : matrixKernelDimensionTower N 1 = 1 := by
    have hnullity := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [show Module.finrank K (Fin 2 -> K) = 2 by simp] at hnullity
    change N.rank + Module.finrank K (LinearMap.ker N.mulVecLin) = 2 at hnullity
    rw [hRankN] at hnullity
    change Module.finrank K (LinearMap.ker (N.mulVecLin ^ 1)) = 1
    rw [pow_one]
    omega
  have hTowerN2 : matrixKernelDimensionTower N 2 = 2 := by
    have hlin2 : N.mulVecLin ^ 2 = 0 := by
      change N.toLin' ^ 2 = 0
      rw [← Matrix.toLin'_pow, hN2]
      exact Matrix.mulVecLin_zero
    have hnullity := LinearMap.finrank_range_add_finrank_ker (N.mulVecLin ^ 2)
    have hrange : Module.finrank K (LinearMap.range (N.mulVecLin ^ 2)) = 0 := by
      rw [hlin2]
      simp
    rw [hrange, show Module.finrank K (Fin 2 -> K) = 2 by simp] at hnullity
    unfold matrixKernelDimensionTower
    omega
  exact ⟨hCharA.trans hCharN.symm, IsNilpotent.zero, ⟨2, hN2⟩,
    hNotConjugate, hTowerA, hTowerN1, hTowerN2⟩

#print axioms kernel_tower_separates_charpoly_residual

/-- The lower bound `n <= k` in the stabilization theorem cannot be dropped uniformly:
the two-dimensional square-zero block has kernel dimensions one and two at steps one and two. -/
theorem dimension_bound_is_necessary :
    exists N : Matrix (Fin 2) (Fin 2) ℚ,
      matrixKernelDimensionTower N 1 ≠ matrixKernelDimensionTower N 2 := by
  let N : Matrix (Fin 2) (Fin 2) ℚ := Matrix.single 0 1 1
  have h := kernel_tower_separates_charpoly_residual (K := ℚ)
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, hN1, hN2⟩
  have hN1' : matrixKernelDimensionTower N 1 = 1 := by simpa [N] using hN1
  have hN2' : matrixKernelDimensionTower N 2 = 2 := by simpa [N] using hN2
  exact ⟨N, by omega⟩

#print axioms dimension_bound_is_necessary

end D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery
