/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Thick108WeightExclusion
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Positive weights exclude the thick 108-vertex Q9 support from a saturated pair. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangIntegralSwitching
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.ZMod.Basic

/-! Integer parity Gram defects for the thick Q9 support. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Thick108WeightExclusion

open scoped BigOperators Matrix
open Matrix
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced IsSwitching)
open Q9MixedBoundaryCollisions (Separated)
open Q9WeightedHuangSaturation (weightedHuang supportedWeightedEigenSpace)
open private mem_supported_iff switched_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents

set_option autoImplicit false
set_option maxRecDepth 8000

private abbrev L := Fin 18
private abbrev R := Fin 3 × Fin 4
private abbrev Layer := Fin 3
private abbrev Left := L × Layer
private abbrev Right := (R × Layer) ⊕ L

private def lcode (i : L) : BitVec 9 :=
  ![0, 6, 10, 12, 15, 17, 20, 23, 27, 30, 33, 39, 40, 45, 46, 48, 53, 58] i

/-- The four horizontal blocks are grouped by the two inactive bits in Q6. -/
private def rcode (i : R) : BitVec 9 :=
  (![![1, 2, 19], ![11, 13, 28], ![38, 52, 55], ![41, 56, 62]] i.2) i.1

private def leaf (k : Layer) : BitVec 9 := BitVec.ofNat 9 (2 ^ (6 + k.val))

private def leftCode (i : Left) : BitVec 9 := lcode i.1 ||| leaf i.2

private def rightCode : Right → BitVec 9
  | .inl (i, k) => rcode i ||| leaf k
  | .inr i => lcode i

private def listedCode : Left ⊕ Right → BitVec 9 := Sum.elim leftCode rightCode

private theorem listedCode_card : (Finset.univ.image listedCode).card = 108 := by
  decide +kernel

private theorem listedCode_injective : Function.Injective listedCode := by
  have h : (Finset.univ.image listedCode).card = (Finset.univ : Finset (Left ⊕ Right)).card :=
    listedCode_card.trans (by decide)
  exact fun _ _ he => Finset.card_image_iff.mp h (Finset.mem_univ _) (Finset.mem_univ _) he

/-- The 108 vertices in the external example, with coordinate zero the low bit. -/
def support : Finset (Q 9) :=
  (Finset.univ.image listedCode).map (cubeBitVec 9).toEmbedding

private theorem mem_support {x : Q 9} :
    x ∈ support ↔ ∃ i, cubeBitVec 9 (listedCode i) = x := by
  rw [support, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩

theorem card_support : support.card = 108 := by
  rw [support, Finset.card_map, listedCode_card]

private def shortDirections (m : BitVec 9) : Bool :=
  m == 1 || m == 2 || m == 4 || m == 16

private def longDirections (m : BitVec 9) : Bool :=
  m == 8 || m == 32 || m == 64 || m == 128 || m == 256

private def edgeWeight (m : BitVec 9) : ℤ :=
  if shortDirections m then 1 else if longDirections m then 3 else 0

private def weight (i : Fin 9) : ℤ := if i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 then 1 else 3

private theorem weight_pos (i : Fin 9) : 0 < (weight i : ℝ) := by
  unfold weight
  split <;> norm_num

private theorem weight_root : Real.sqrt (∑ i : Fin 9, (weight i : ℝ) ^ 2) = 7 := by
  have h : (∑ i : Fin 9, weight i ^ 2) = 49 := by decide +kernel
  have hr : (∑ i : Fin 9, (weight i : ℝ) ^ 2) = 49 := by exact_mod_cast h
  rw [hr, show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private def adjacency : Matrix Left Right ℤ := fun i j =>
  edgeWeight (leftCode i ^^^ rightCode j)

private def horizontal : Matrix L R ℤ := fun i j =>
  if shortDirections (lcode i ^^^ rcode j) then 1 else 0

private def blocks (k : Fin 4) : Matrix (Fin 3) (Fin 3) ℤ :=
  (![!![2, -1, -1; -1, 2, 0; -1, 0, 2],
     !![1, -1, 0; -1, 2, -1; 0, -1, 2],
     !![3, 0, -1; 0, 2, -1; -1, -1, 2],
     !![2, -1, 0; -1, 2, -1; 0, -1, 2]] k)

private theorem horizontal_blocks :
    (4 : ℤ) • (1 : Matrix R R ℤ) - horizontalᵀ * horizontal = blockDiagonal blocks := by
  have h : ∀ i j : R,
      ((4 : ℤ) • (1 : Matrix R R ℤ) - horizontalᵀ * horizontal) i j =
        blockDiagonal blocks i j := by
    simp only [Prod.forall]
    decide +kernel
  exact Matrix.ext h

private theorem block_determinants (k : Fin 4) :
    (blocks k).det = ![(4 : ℤ), 1, 7, 4] k := by
  fin_cases k <;> norm_num [blocks, Matrix.det_fin_three]

private def gramDefect {I J : Type*} [Fintype I] [DecidableEq J] {K : Type*} [Ring K]
    (q : K) (A : Matrix I J K) : Matrix J J K :=
  q • 1 - Aᵀ * A

private theorem map_gramDefect {I J : Type*} [Fintype I] [DecidableEq J]
    {K T : Type*} [CommRing K] [CommRing T]
    (f : K →+* T) (q : K) (A : Matrix I J K) :
    (gramDefect q A).map f = gramDefect (f q) (A.map f) := by
  ext i j
  simp only [gramDefect, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    map_sub, map_mul, Matrix.one_apply]
  rw [apply_ite f]
  simp only [map_one, map_zero]
  congr 1
  exact congrArg (fun M : Matrix J J T => M i j)
    (Matrix.map_mul (L := Aᵀ) (M := A) (f := f))

private def modThree : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)

private def horizontalMod : Matrix L R (ZMod 3) := horizontal.map modThree

private theorem horizontalMod_det : (gramDefect 1 horizontalMod).det = 1 := by
  have hfour : modThree 4 = 1 := by decide
  calc
    (gramDefect 1 horizontalMod).det = modThree ((gramDefect 4 horizontal).det) := by
      rw [RingHom.map_det]
      change _ = ((gramDefect 4 horizontal).map modThree).det
      rw [map_gramDefect, hfour, horizontalMod]
    _ = 1 := ?_
  rw [gramDefect, horizontal_blocks, Matrix.det_blockDiagonal, map_prod]
  have h : ∀ k : Fin 4, modThree ((blocks k).det) = 1 := by
    intro k
    rw [block_determinants]
    revert k
    decide +kernel
  simp [h]

private def horizontalLayers : Matrix Left (R × Layer) (ZMod 3) :=
  blockDiagonal (fun _ : Layer => horizontalMod)

private def reducedAdjacency : Matrix Left Right (ZMod 3) := fun i j =>
  j.elim (horizontalLayers i) (fun _ => 0)

private theorem adjacency_modThree : adjacency.map modThree = reducedAdjacency := by
  have h : ∀ i : Left, ∀ j : Right, modThree (adjacency i j) = reducedAdjacency i j := by
    simp only [Sum.forall, Prod.forall]
    decide +kernel
  exact Matrix.ext h

private theorem layer_gram :
    gramDefect 1 horizontalLayers =
      blockDiagonal (fun _ : Layer => gramDefect 1 horizontalMod) := by
  simp only [horizontalLayers, gramDefect, one_smul, blockDiagonal_transpose]
  rw [← blockDiagonal_mul, ← Matrix.blockDiagonal_one, ← blockDiagonal_sub]
  rfl

private theorem reduced_gram :
    gramDefect 1 reducedAdjacency =
      fromBlocks (gramDefect 1 horizontalLayers) 0 0 (1 : Matrix L L (ZMod 3)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gramDefect, reducedAdjacency, Matrix.mul_apply, Matrix.one_apply]

private theorem right_gram_map_det : (gramDefect 1 (adjacency.map modThree)).det = 1 := by
  rw [adjacency_modThree, reduced_gram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    layer_gram, Matrix.det_blockDiagonal]
  simp [horizontalMod_det]

private theorem right_gram_cast : modThree ((gramDefect 49 adjacency).det) = 1 := by
  rw [RingHom.map_det]
  change ((gramDefect 49 adjacency).map modThree).det = 1
  rw [map_gramDefect, show modThree 49 = 1 by decide]
  exact right_gram_map_det

private theorem emod_eq_one_of_cast {m : ℤ} (h : modThree m = 1) : m % 3 = 1 := by
  have hc := congrArg (fun a : ZMod 3 => (a.val : ℤ)) h
  change ((m : ZMod 3).val : ℤ) = 1 at hc
  rwa [ZMod.val_intCast] at hc

private theorem gramDefect_unit_transpose_det {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {K : Type*} [CommRing K] (A : Matrix I J K) :
    (gramDefect 1 Aᵀ).det = (gramDefect 1 A).det := by
  simp only [gramDefect, one_smul, Matrix.transpose_transpose]
  exact Matrix.det_one_sub_mul_comm A Aᵀ

/-- Both parity Gram defects of the positive-weight graph have determinant one modulo three. -/
theorem gram_determinants_modThree :
    (gramDefect 49 adjacency).det % 3 = 1 ∧ (gramDefect 49 adjacencyᵀ).det % 3 = 1 := by
  refine ⟨emod_eq_one_of_cast right_gram_cast, emod_eq_one_of_cast ?_⟩
  rw [RingHom.map_det]
  change ((gramDefect 49 adjacencyᵀ).map modThree).det = 1
  rw [map_gramDefect, show modThree 49 = 1 by decide]
  change (gramDefect 1 (adjacency.map modThree)ᵀ).det = 1
  exact (gramDefect_unit_transpose_det (adjacency.map modThree)).trans right_gram_map_det

/-- A mod-prime determinant certificate for an integer matrix rules out a real kernel. -/
private theorem real_mulVec_injective_of_modThree {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (h : (A.map modThree).det ≠ 0) :
    Function.Injective (A.map (Int.castRingHom ℝ)).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (((Int.castRingHom ℝ).mapMatrix A).det)
  rw [← RingHom.map_det, isUnit_iff_ne_zero]
  change (A.det : ℝ) ≠ 0
  rw [Int.cast_ne_zero]
  intro hz
  apply h
  change (modThree.mapMatrix A).det = 0
  rw [← RingHom.map_det, hz, map_zero]

private theorem left_right_real_kernel {u : Left → ℝ} {v : Right → ℝ}
    (hu : (adjacency.map (Int.castRingHom ℝ)).mulVec v = (7 : ℝ) • u)
    (hv : (adjacency.map (Int.castRingHom ℝ))ᵀ.mulVec u = (7 : ℝ) • v) :
    u = 0 ∧ v = 0 := by
  let A := adjacency.map (Int.castRingHom ℝ)
  have hinj : Function.Injective (gramDefect (49 : ℝ) A).mulVec := by
    rw [← show (Int.castRingHom ℝ) 49 = 49 by norm_num, ← map_gramDefect]
    apply real_mulVec_injective_of_modThree
    change (modThree.mapMatrix (gramDefect 49 adjacency)).det ≠ 0
    rw [← RingHom.map_det, right_gram_cast]
    exact one_ne_zero
  have hgram : (Aᵀ * A).mulVec v = (49 : ℝ) • v := by
    rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hv, smul_smul]
    norm_num
  have hw : v = 0 := hinj (by
    rw [gramDefect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hgram,
      sub_self, Matrix.mulVec_zero])
  rw [hw, Matrix.mulVec_zero, eq_comm, smul_eq_zero_iff_right (by norm_num)] at hu
  exact ⟨hu, hw⟩

private def directionMask (i : Fin 9) : BitVec 9 := BitVec.ofNat 9 (2 ^ i.val)

private theorem mask_weights (m : BitVec 9) :
    edgeWeight m = ∑ i : Fin 9, if m = directionMask i then weight i else 0 := by
  revert m
  decide +kernel

private theorem nonzero_direction (i : Fin 9) : edgeWeight (directionMask i) ≠ 0 := by
  revert i
  decide +kernel

private theorem left_internal_zero (i j : Left) :
    edgeWeight (leftCode i ^^^ leftCode j) = 0 := by
  revert i j
  decide +kernel

private theorem right_internal_zero (i j : Right) :
    edgeWeight (rightCode i ^^^ rightCode j) = 0 := by
  revert i j
  simp only [Sum.forall, Prod.forall]
  decide +kernel

private theorem xor_eq_mask (x y : BitVec 9) (i : Fin 9) :
    x ^^^ y = directionMask i ↔ y = x ^^^ directionMask i := by
  have h := @BitVec.xor_right_inj 9 (x ^^^ y) (directionMask i) x
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using h.symm

private theorem edge_of_flip (x : BitVec 9) (i : Fin 9) :
    edgeWeight (x ^^^ (x ^^^ directionMask i)) ≠ 0 := by
  simpa [← BitVec.xor_assoc] using nonzero_direction i

private theorem weighted_row_sum {J : Type*} [Fintype J] (code : J → BitVec 9)
    (hinj : Function.Injective code) (x : BitVec 9) (g : BitVec 9 → ℝ)
    (hzero : ∀ i : Fin 9, (∀ j, code j ≠ x ^^^ directionMask i) →
      g (x ^^^ directionMask i) = 0) :
    (∑ i : Fin 9, (weight i : ℝ) * g (x ^^^ directionMask i)) =
      ∑ j, (edgeWeight (x ^^^ code j) : ℝ) * g (code j) := by
  classical
  simp_rw [mask_weights, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ∃ j, code j = x ^^^ directionMask i
  · obtain ⟨j, hj⟩ := h
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left ((xor_eq_mask _ _ _).mpr hj), hj]
    · intro k _ hkj
      have hk : ¬ x ^^^ code k = directionMask i :=
        fun he => hkj (hinj (((xor_eq_mask _ _ _).mp he).trans hj.symm))
      simp [hk]
    · simp
  · rw [hzero i (not_exists.mp h), mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬ x ^^^ code j = directionMask i :=
      fun he => h ⟨j, (xor_eq_mask _ _ _).mp he⟩
    simp [hj]

open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_true_prefix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangIntegralSwitching
open private theta theta_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
open BalancedCubeComponentBoundary (directions)
open private directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private induced_degree_eq_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

private local instance : Fintype (BitVec 9) :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (show Fin (2 ^ 9) ≃ BitVec 9 from
    ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun x => by cases x; rfl⟩)

/-- A bit mask for testing membership in the explicitly listed support. -/
private def occupied (x : BitVec 9) : Bool :=
  (0x45b163c2589abc47000000000000000045b163c2589abc4745b163c2589abc470421618248929441 :
    ℕ).testBit x.toNat

private theorem occupied_iff (x : BitVec 9) :
    occupied x = true ↔ cubeBitVec 9 x ∈ support := by
  let codes := Finset.univ.image listedCode
  let mask := Finset.univ.filter (fun t : BitVec 9 => occupied t = true)
  have deep : ∀ i : Left ⊕ Right, occupied (listedCode i) = true := by
    simp only [Sum.forall, Prod.forall]
    decide +kernel
  have hm : mask.card = 108 := by
    change (Finset.univ.filter (fun t : BitVec 9 => occupied t = true)).card = 108
    decide +kernel
  have heq : codes = mask := Finset.eq_of_subset_of_card_le (by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, deep i⟩)
    (hm.trans listedCode_card.symm).le
  calc
    occupied x = true ↔ x ∈ mask := by simp [mask]
    _ ↔ cubeBitVec 9 x ∈ support := by
      rw [← heq, support, Finset.mem_map]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, he⟩ =>
        (cubeBitVec 9).injective he ▸ hy⟩

private theorem cube_flip_code (x : BitVec 9) (i : Fin 9) :
    cubeBitVec 9 (x ^^^ directionMask i) =
      BalancedCriticalSpectrum.flip (cubeBitVec 9 x) i :=
  cubeBitVec_xor_single x i

private def signAt (x : BitVec 9) : ℤ :=
  if (0x53160c200128c40 : ℕ).testBit (x.toNat % 64) then -1 else 1

private theorem signAt_unit (x : BitVec 9) : signAt x = 1 ∨ signAt x = -1 := by
  unfold signAt
  split <;> simp

private theorem signAt_edge (x : BitVec 9) (i : Fin 9)
    (h : occupied x = true) (h' : occupied (x ^^^ directionMask i) = true) :
    truePrefixSign (cubeBitVec 9 x) i = signAt x * signAt (x ^^^ directionMask i) := by
  revert x i
  decide +kernel

/-- The external switching certificate, transported to the repository's Huang signing. -/
theorem support_balanced : IsBalanced support := by
  let s (x : Q 9) : ℝ := theta x * (signAt ((cubeBitVec 9).symm x) : ℝ)
  refine ⟨s, fun x _ => ?_, ?_⟩
  · rcases theta_unit x with ht | ht <;> rcases signAt_unit ((cubeBitVec 9).symm x) with hs | hs
    all_goals simp [s, ht, hs]
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    let a := (cubeBitVec 9).symm x
    have ha : cubeBitVec 9 a = x := (cubeBitVec 9).apply_symm_apply x
    have hb : cubeBitVec 9 (a ^^^ directionMask i) = BalancedCriticalSpectrum.flip x i := by
      rw [cube_flip_code, ha]
    have h := signAt_edge a i ((occupied_iff _).mpr (ha ▸ hx))
      ((occupied_iff _).mpr (hb ▸ hy))
    have hb' : a ^^^ directionMask i = (cubeBitVec 9).symm
        (BalancedCriticalSpectrum.flip x i) := (Equiv.eq_symm_apply _).mpr hb
    rw [ha, hb'] at h
    rw [matrix_true_prefix, h]
    push_cast
    unfold s
    ring

private theorem count_neighbors (x : BitVec 9) (hx : occupied x = true) :
    (Finset.univ.filter (fun i : Fin 9 => occupied (x ^^^ directionMask i) = true)).card = 3 := by
  revert x
  decide +kernel

open scoped Classical in
/-- Every vertex of the example has exactly three neighbors in the example. -/
theorem support_cubic :
    ((hypercube 9).induce (support : Set (Q 9))).IsRegularOfDegree 3 := by
  classical
  intro x
  rw [induced_degree_eq_neighbor_card]
  have hfilter : (hypercube 9).neighborFinset x.val ∩ support =
      support.filter (fun y => (hypercube 9).Adj x.val y) := by
    ext y
    simp [and_comm]
  rw [hfilter, ← directions_card]
  let a := (cubeBitVec 9).symm x.val
  have ha : cubeBitVec 9 a = x.val := (cubeBitVec 9).apply_symm_apply x.val
  have hd : directions support x.val =
      Finset.univ.filter (fun i : Fin 9 => occupied (a ^^^ directionMask i) = true) := by
    ext i
    simp [directions, occupied_iff, cube_flip_code, ha]
  rw [hd]
  exact count_neighbors a ((occupied_iff _).mpr (ha ▸ x.property))

/-- Distance layers from zero in the support graph, encoded as membership masks. -/
private def depthMasks : List ℕ :=
  [0x1,
   0x10000000000000000000000000000000100000000000000010000000000000000,
   0x60000000000000000000000000000000600000000000000060000000000000000,
   0x2000204400000000000000000000000020002044000000002000204400000000000000000,
   0x240000808000000000000000000000002400008080000000240000808000000000200020440,
   0x6180088080000000000000000000000061800880800000006180088080000000000000000000,
   0x41800000000020000000000000000000418000000000200041800000000020000000618008808000,
   0x4210000400010000000000000000000042100004000100004210000400010000000000000000000,
   0x100000100000000000000000000000001000001000000000100000100000000421000040001000,
   0x1000000000000000000000000000000010000000000000001000000000000000000000,
   0x100000]

private def depth (x : BitVec 9) : ℕ := depthMasks.findIdx (fun m => m.testBit x.toNat)

private theorem descent (x : BitVec 9) (hx : occupied x = true) (hne : x ≠ 0) :
    ∃ i : Fin 9, occupied (x ^^^ directionMask i) = true ∧
      depth (x ^^^ directionMask i) < depth x := by
  revert x
  decide +kernel

/-- The certified depth decreases to the zero vertex along induced cube edges. -/
theorem support_connected : ((hypercube 9).induce (support : Set (Q 9))).Connected := by
  let G := (hypercube 9).induce (support : Set (Q 9))
  let vertex (x : BitVec 9) (hx : occupied x = true) : (support : Set (Q 9)) :=
    ⟨cubeBitVec 9 x, (occupied_iff _).mp hx⟩
  let root := vertex 0 (by decide)
  change G.Connected
  letI : Nonempty (support : Set (Q 9)) := ⟨root⟩
  refine ⟨?_⟩
  have path (d : ℕ) : ∀ x : BitVec 9, ∀ hx : occupied x = true, depth x = d →
      G.Reachable root (vertex x hx) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x hx hd
      by_cases h : x = 0
      · subst x
        exact SimpleGraph.Reachable.refl root
      · obtain ⟨i, hi, hlt⟩ := descent x hx h
        have hp := ih _ (hlt.trans_eq hd) _ hi rfl
        have hadj : G.Adj (vertex x hx) (vertex (x ^^^ directionMask i) hi) := by
          change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 (x ^^^ directionMask i))
          rw [cube_flip_code]
          exact flip_adj _ _
        exact hp.trans hadj.symm.reachable
  have reach (w : (support : Set (Q 9))) : G.Reachable root w := by
    let a := (cubeBitVec 9).symm w.val
    have ha : cubeBitVec 9 a = w.val := (cubeBitVec 9).apply_symm_apply w.val
    have hw : occupied a = true := (occupied_iff _).mpr (ha ▸ w.property)
    rw [← show vertex a hw = w from Subtype.ext ha]
    exact path _ a hw rfl
  exact fun u v => (reach u).symm.trans (reach v)

/-- A supported eigenvector at the positive weighted bound vanishes on the explicit
108-point support. The checked switching signs turn the induced rows into unsigned weighted rows. -/
theorem supported_eigenvector_eq_zero {z : Q 9 → ℝ}
    (hz : z ∈ supportedWeightedEigenSpace (fun i => (weight i : ℝ)) support) :
    z = 0 := by
  obtain ⟨s, hs⟩ := support_balanced
  obtain ⟨heq, hout⟩ := (mem_supported_iff _ _ z).mp hz
  rw [weight_root] at heq
  let g (x : BitVec 9) := s (cubeBitVec 9 x) * z (cubeBitVec 9 x)
  have hrow (x : BitVec 9) (hx : cubeBitVec 9 x ∈ support) :
      (∑ i : Fin 9, (weight i : ℝ) * g (x ^^^ directionMask i)) = 7 * g x := by
    have h := switched_row (t := fun i => (weight i : ℝ)) hs hout hx
    have he := congrFun heq (cubeBitVec 9 x)
    change weightedHuang _ z (cubeBitVec 9 x) = 7 * z (cubeBitVec 9 x) at he
    rw [he] at h
    simp only [g, directionMask, cubeBitVec_xor_single]
    unfold BalancedCriticalSpectrum.flip at h
    rw [← h]
    ring
  have zero_outside (x : BitVec 9) (hl : ∀ i, leftCode i ≠ x)
      (hr : ∀ j, rightCode j ≠ x) : g x = 0 := by
    have hx : cubeBitVec 9 x ∉ support := by
      rintro hm
      obtain ⟨i, hi⟩ := mem_support.mp hm
      have hi' := (cubeBitVec 9).injective hi
      cases i with
      | inl i => exact hl i hi'
      | inr j => exact hr j hi'
    simp [g, hout _ hx]
  let u : Left → ℝ := g ∘ leftCode
  let v : Right → ℝ := g ∘ rightCode
  have hu : (adjacency.map (Int.castRingHom ℝ)).mulVec v = (7 : ℝ) • u := by
    funext i
    have hr := hrow (leftCode i) (mem_support.mpr ⟨.inl i, rfl⟩)
    have hsum := weighted_row_sum rightCode
      (fun _ _ h => Sum.inr.inj (listedCode_injective h)) (leftCode i) g
      (fun j hj => zero_outside _ (fun k hk => edge_of_flip (leftCode i) j
        (hk ▸ left_internal_zero i k)) hj)
    rw [hsum] at hr
    exact hr
  have hv : (adjacency.map (Int.castRingHom ℝ))ᵀ.mulVec u = (7 : ℝ) • v := by
    funext i
    have hr := hrow (rightCode i) (mem_support.mpr ⟨.inr i, rfl⟩)
    have hsum := weighted_row_sum leftCode
      (fun _ _ h => Sum.inl.inj (listedCode_injective h)) (rightCode i) g
      (fun j hj => zero_outside _ hj (fun k hk => edge_of_flip (rightCode i) j
        (hk ▸ right_internal_zero i k)))
    rw [hsum] at hr
    change (∑ j, (edgeWeight (leftCode j ^^^ rightCode i) : ℝ) * g (leftCode j)) =
      7 * g (rightCode i)
    simpa only [BitVec.xor_comm (rightCode i)] using hr
  obtain ⟨hu, hv⟩ := left_right_real_kernel hu hv
  funext x
  by_cases hx : x ∈ support
  · obtain ⟨i, rfl⟩ := mem_support.mp hx
    have hg : g (listedCode i) = 0 := by
      cases i with
      | inl i => exact congrFun hu i
      | inr i => exact congrFun hv i
    exact (mul_eq_zero.mp hg).resolve_left (by
      rcases hs.1 _ hx with h | h <;> rw [h] <;> norm_num)
  · exact hout x hx

/-- The given thick support cannot be one component of a separated connected
balanced pair covering 258 cube vertices. -/
theorem no_saturated_pair (D : Finset (Q 9))
    (hcard : (support ∪ D).card = 258) (hsep : Separated support D)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbD : IsBalanced D) : False := by
  obtain ⟨⟨z, hz, hne⟩, _⟩ := Q9WeightedHuangComponents.exists_supported_eigenvectors
    (fun i => (weight i : ℝ)) weight_pos hcard hsep support_connected hd support_balanced hbD
  exact hne (supported_eigenvector_eq_zero hz)

#print axioms card_support
#print axioms support_balanced
#print axioms support_cubic
#print axioms support_connected
#print axioms gram_determinants_modThree
#print axioms supported_eigenvector_eq_zero
#print axioms no_saturated_pair

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Thick108WeightExclusion
