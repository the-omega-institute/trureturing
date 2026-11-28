/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: The cooling-code optimum on 58 coordinates at weight six and deletion size two is 57. -/

import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.GroupDivisibleDesign
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Configuration
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # The exact cooling-code optimum at length 58

The lines of the projective plane of order seven supply 57 classes. Attaining the
finite upper bound of 58 would give a group divisible design whose incidence
Gram determinant is not a square.
-/

namespace CPECCBridge.Length58

noncomputable section

section ProjectivePlane

open scoped LinearAlgebra.Projectivization

private local instance primeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Points and lines both use projective coordinates. Incidence is orthogonality. -/
private abbrev Point := ℙ (ZMod 7) (Fin 3 → ZMod 7)

private local instance pointFintype : Fintype Point := Fintype.ofFinite Point

private theorem point_card : Fintype.card Point = 57 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (ℙ (ZMod 7) (Fin 3 → ZMod 7)) = 57
  rw [Projectivization.card'' (ZMod 7) (Fin 3 → ZMod 7), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
  decide

private theorem order_eq : Configuration.ProjectivePlane.order Point Point = 7 := by
  let q := Configuration.ProjectivePlane.order Point Point
  have hcard : q ^ 2 + q + 1 = 57 :=
    (Configuration.ProjectivePlane.card_points Point Point).symm.trans point_card
  have hstep (a b : ℕ) (hab : a < b) : a ^ 2 + a + 1 < b ^ 2 + b + 1 := by
    have hsq := Nat.pow_le_pow_left hab.le 2
    omega
  rcases lt_trichotomy q 7 with h | h | h
  · have := hstep q 7 h
    omega
  · exact h
  · have := hstep 7 q h
    omega

private theorem coordinate_card : Fintype.card (Option Point) = 58 := by
  rw [Fintype.card_option, point_card]

private def pointToCoordinate : Point ↪ Fin 58 :=
  (⟨some, Option.some_injective Point⟩ : Point ↪ Option Point).trans
    (Fintype.equivFinOfCardEq coordinate_card).toEmbedding

private def indexToLine : Fin 57 ≃ Point := (Fintype.equivFinOfCardEq point_card).symm

private def linePoints (l : Point) : Finset Point := by
  classical
  exact Finset.univ.filter (· ∈ l)

private theorem mem_linePoints (p l : Point) : p ∈ linePoints l ↔ p ∈ l := by
  classical
  simp [linePoints]

private theorem linePoints_card (l : Point) : (linePoints l).card = 8 := by
  classical
  let : Fintype {p : Point // p ∈ l} := Fintype.ofFinite _
  rw [linePoints, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  change Configuration.pointCount Point l = 8
  rw [Configuration.ProjectivePlane.pointCount_eq Point l, order_eq]

/-- The eight coordinates of a projective line, indexed by `Fin 57`. -/
private def block (i : Fin 57) : Finset (Fin 58) :=
  (linePoints (indexToLine i)).map pointToCoordinate

private theorem block_card (i : Fin 57) : (block i).card = 8 := by
  rw [block, Finset.card_map, linePoints_card]

private theorem block_inter_le_one {i j : Fin 57} (hij : i ≠ j) :
    ((block i) ∩ (block j)).card ≤ 1 := by
  classical
  simp only [block, ← Finset.map_inter, Finset.card_map]
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
  obtain ⟨hqi, hqj⟩ := Finset.mem_inter.mp hq
  have h := Configuration.Nondegenerate.eq_or_eq
    ((mem_linePoints _ _).mp hpi) ((mem_linePoints _ _).mp hqi)
    ((mem_linePoints _ _).mp hpj) ((mem_linePoints _ _).mp hqj)
  exact h.resolve_right (fun heq => hij (indexToLine.injective heq))

/-- All six-element subsets of the block are the words in an information class. -/
private def informationClass (i : Fin 57) : Finset (Finset (Fin 58)) :=
  (block i).powersetCard 6

private theorem word_card (i : Fin 57) (A : Finset (Fin 58)) (hA : A ∈ informationClass i) :
    A.card = 6 :=
  (Finset.mem_powersetCard.mp hA).2

private theorem avoids_hot (i : Fin 57) (D : Finset (Fin 58)) (hD : D.card = 2) :
    ∃ A ∈ informationClass i, Disjoint D A := by
  have hremain : 6 ≤ ((block i) \ D).card := by
    have h := Finset.le_card_sdiff D (block i)
    rw [hD, block_card] at h
    exact h
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq hremain
  refine ⟨A, Finset.mem_powersetCard.mpr ⟨hA.trans Finset.sdiff_subset, hcard⟩, ?_⟩
  exact Finset.disjoint_left.mpr (fun _ hpD hpA => (Finset.mem_sdiff.mp (hA hpA)).2 hpD)

private theorem cross_inter_le_one {i j : Fin 57} (hij : i ≠ j)
    (A : Finset (Fin 58)) (hA : A ∈ informationClass i)
    (B : Finset (Fin 58)) (hB : B ∈ informationClass j) :
    (A ∩ B).card ≤ 1 :=
  (Finset.card_le_card (Finset.inter_subset_inter
    (Finset.mem_powersetCard.mp hA).1 (Finset.mem_powersetCard.mp hB).1)).trans
      (block_inter_le_one hij)

end ProjectivePlane

section DesignObstruction

open Matrix Finset SimpleGraph
open scoped BigOperators

private abbrev GramIndex := Fin 29 × Fin 2

/-- The all-ones matrix. -/
private def onesMatrix (R : Type*) [One R] : Matrix GramIndex GramIndex R :=
  Matrix.of fun _ _ => 1

/-- The entry is one precisely when both indices belong to the same group. -/
private def groupMatrix (R : Type*) [Zero R] [One R] : Matrix GramIndex GramIndex R :=
  Matrix.of fun i j => if i.1 = j.1 then 1 else 0

private def gramBase : Matrix GramIndex GramIndex ℚ :=
  (8 : ℚ) • (1 : Matrix GramIndex GramIndex ℚ) - groupMatrix ℚ

private def pairBlock : Matrix (Fin 2) (Fin 2) ℚ :=
  (8 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) - Matrix.of (fun _ _ => 1)

private theorem det_gramBase : gramBase.det = (48 : ℚ) ^ 29 := by
  let swap : (Fin 2 × Fin 29) ≃ GramIndex := Equiv.prodComm _ _
  have hB : gramBase = Matrix.reindex swap swap
      (Matrix.blockDiagonal (fun _ : Fin 29 => pairBlock)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [gramBase, pairBlock, groupMatrix, swap, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Matrix.blockDiagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  have hblock : pairBlock.det = 48 := by
    rw [Matrix.det_fin_two]
    norm_num [pairBlock, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [hB, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp only [hblock, Fin.prod_const]

private def column : Matrix GramIndex Unit ℚ := Matrix.of fun _ _ => 1
private def row : Matrix Unit GramIndex ℚ := Matrix.of fun _ _ => 1 / 6

private theorem groupMatrix_mul_column :
    groupMatrix ℚ * column = (2 : ℚ) • column := by
  ext i j
  simp only [groupMatrix, column, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, one_add_one_eq_two]

private theorem gramBase_mul_column : gramBase * column = (6 : ℚ) • column := by
  rw [gramBase, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, groupMatrix_mul_column, ← sub_smul]
  norm_num

private theorem onesMatrix_factor : gramBase * (column * row) = onesMatrix ℚ := by
  rw [← Matrix.mul_assoc, gramBase_mul_column, Matrix.smul_mul]
  ext i j
  norm_num [onesMatrix, column, row, Matrix.smul_apply, Matrix.mul_apply]

private theorem det_rank_one :
    (1 + column * row).det = (1 : ℚ) + 58 / 6 := by
  rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
  norm_num [column, row, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Fintype.card_prod]

/-- Factor the Gram matrix as the pair-block matrix times a rank-one update. -/
private theorem det_gram_rat :
    ((8 : ℚ) • (1 : Matrix GramIndex GramIndex ℚ) + onesMatrix ℚ - groupMatrix ℚ).det =
      (2 : ℚ) ^ 121 * 3 ^ 28 := by
  have h :
      (8 : ℚ) • (1 : Matrix GramIndex GramIndex ℚ) + onesMatrix ℚ - groupMatrix ℚ =
        gramBase * (1 + column * row) := by
    rw [Matrix.mul_add, Matrix.mul_one, onesMatrix_factor, gramBase, sub_add_eq_add_sub]
  rw [h, Matrix.det_mul, det_gramBase, det_rank_one]
  norm_num

private theorem det_gram_int :
    ((8 : ℤ) • (1 : Matrix GramIndex GramIndex ℤ) + onesMatrix ℤ - groupMatrix ℤ).det =
      (2 : ℤ) ^ 121 * 3 ^ 28 := by
  let G : Matrix GramIndex GramIndex ℤ := (8 : ℤ) • 1 + onesMatrix ℤ - groupMatrix ℤ
  have hG : (Int.castRingHom ℚ).mapMatrix G =
      (8 : ℚ) • (1 : Matrix GramIndex GramIndex ℚ) + onesMatrix ℚ - groupMatrix ℚ := by
    ext i j
    simp only [G, onesMatrix, groupMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
      map_sub, map_add, map_mul, map_ofNat, apply_ite, map_one, map_zero]
    by_cases h : i.1 = j.1 <;> simp only [h, ite_true, ite_false]
  have hdet := (Int.castRingHom ℚ).map_det G
  rw [hG, det_gram_rat] at hdet
  change (↑G.det : ℚ) = _ at hdet
  change G.det = _
  exact_mod_cast hdet

private theorem not_square (z : ℤ) : z ^ 2 ≠ (2 : ℤ) ^ 121 * 3 ^ 28 := by
  intro h
  have habs := congrArg Int.natAbs h
  simp only [Int.natAbs_pow, Int.natAbs_mul] at habs
  have hval := congrArg (fun n : ℕ => n.factorization 2) habs
  change (z.natAbs ^ 2).factorization 2 = (2 ^ 121 * 3 ^ 28 : ℕ).factorization 2 at hval
  have hthree : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_pow 3, Finsupp.smul_apply, hthree, smul_zero, add_zero,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] at hval
  omega

/-- An integer Gram matrix cannot have diagonal entries 8, zero off-diagonal
entries within each pair, and entries 1 between different pairs. -/
private theorem gram_impossible (A : Matrix (Fin 29 × Fin 2) (Fin 29 × Fin 2) ℤ) :
    A * Aᵀ ≠ (8 : ℤ) • (1 : Matrix GramIndex GramIndex ℤ) + onesMatrix ℤ - groupMatrix ℤ := by
  intro h
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two, det_gram_int] at hdet
  exact not_square A.det hdet

attribute [local instance] Classical.propDecidable

private abbrev V := Fin 58
private abbrev GDD := GroupDivisibleDesign V 8 2

private def groupPartition (G : GDD) : Finpartition (Finset.univ : Finset V) :=
  @Finpartition.ofSetoid V _ _ G.groups (Classical.decRel _)

private theorem parts_card_two (G : GDD) :
    ∀ t : (groupPartition G).parts, t.1.card = 2 := by
  intro t
  obtain ⟨x, hx⟩ := Finpartition.nonempty_of_mem_parts (groupPartition G) t.property
  have hxt := Finpartition.part_eq_of_mem (groupPartition G) t.property hx
  have hcard : ((groupPartition G).part x).card = 2 := by
    rw [← Set.ncard_coe_finset]
    have hs : ((groupPartition G).part x : Set V) = {u | G.groups.r x u} := by
      ext u
      change u ∈ (groupPartition G).part x ↔ _
      simp [groupPartition, Finpartition.mem_part_ofSetoid_iff_rel]
    rw [hs, G.group_card]
  rw [← hxt, hcard]

private theorem parts_card_29 (G : GDD) :
    Fintype.card (groupPartition G).parts = 29 := by
  have hsum := (groupPartition G).sum_card_parts
  have hsum58 : (∑ t ∈ (groupPartition G).parts, t.card) = 58 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hsum
  have hsum2 : (∑ t ∈ (groupPartition G).parts, 2) = 58 := by
    calc
      (∑ t ∈ (groupPartition G).parts, 2) = ∑ t ∈ (groupPartition G).parts, t.card := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (parts_card_two G ⟨t, ht⟩).symm
      _ = 58 := hsum58
  have hcard_sum : (∑ t ∈ (groupPartition G).parts, 2) = 2 * (groupPartition G).parts.card := by
    simp [Finset.sum_const, Nat.mul_comm]
  rw [hcard_sum] at hsum2
  have hc : 2 * Fintype.card (groupPartition G).parts = 58 := by
    simpa only [Fintype.card_coe] using hsum2
  omega

private theorem enum_group (G : GDD) :
    ∃ e : (Fin 29 × Fin 2) ≃ V,
      ∀ i j, G.groups.r (e i) (e j) ↔ i.1 = j.1 := by
  let QG := groupPartition G
  have hparts : Fintype.card QG.parts = 29 := parts_card_29 G
  have hpart (x y : V) : QG.part x = QG.part y ↔ G.groups.r x y := by
    constructor
    · intro h
      have hy : y ∈ QG.part y := QG.mem_part (by simp)
      rw [← h] at hy
      change y ∈ (groupPartition G).part x at hy
      exact (show y ∈ (groupPartition G).part x ↔ G.groups.r x y by
        simp [groupPartition, Finpartition.mem_part_ofSetoid_iff_rel]).mp hy
    · intro h
      apply Finset.ext
      intro z
      change z ∈ (groupPartition G).part x ↔ z ∈ (groupPartition G).part y
      simp only [groupPartition, Finpartition.mem_part_ofSetoid_iff_rel]
      exact ⟨fun hz => G.groups.trans' (G.groups.symm' h) hz,
        fun hz => G.groups.trans' h hz⟩
  obtain ⟨f, hf⟩ := QG.exists_enumeration
  let u : V ≃ (Finset.univ : Finset V) :=
    { toFun := fun x => ⟨x, by simp⟩
      invFun := fun x => x.1
      left_inv := by intro x; rfl
      right_inv := by intro x; simp }
  let f' : V ≃ Σ t : QG.parts, Fin t.1.card := u.trans f
  let eq : QG.parts ≃ Fin 29 := Fintype.equivFinOfCardEq hparts
  let ec : (Fin 29 × Fin 2) ≃ (Σ t : QG.parts, Fin t.1.card) :=
    (Equiv.sigmaEquivProd (Fin 29) (Fin 2)).symm.trans
      (eq.symm.sigmaCongr (fun t => by
        exact (Fintype.equivFinOfCardEq (by simpa using parts_card_two G (eq.symm t))).symm))
  let e : (Fin 29 × Fin 2) ≃ V := ec.trans f'.symm
  refine ⟨e, ?_⟩
  intro i j
  have hrel : QG.part (e i) = QG.part (e j) ↔
      (f' (e i)).fst = (f' (e j)).fst := by
    change QG.part (e i) = QG.part (e j) ↔
      (f (u (e i))).fst = (f (u (e j))).fst
    have hh := hf (u (e i)) (u (e j))
    dsimp [u] at hh
    exact hh
  have hfirst : (f' (e i)).fst = (f' (e j)).fst ↔ i.1 = j.1 := by
    have hfi : f' (e i) = ec i := by simp [e]
    have hfj : f' (e j) = ec j := by simp [e]
    rw [hfi, hfj]
    change (eq.symm i.1) = (eq.symm j.1) ↔ i.1 = j.1
    exact eq.symm.injective.eq_iff
  exact (hpart (e i) (e j)).symm.trans (hrel.trans hfirst)

private theorem packed_neighbors_card (G : GDD) (v : V) :
    ((packedGraph G.blocks id).neighborSet v).ncard = 56 := by
  let H := packedGraph G.blocks id
  change (H.neighborSet v).ncard = 56
  have hneighbors : H.neighborSet v = ({u | G.groups.r v u} : Set V)ᶜ := by
    ext u
    change H.Adj v u ↔ ¬ G.groups.r v u
    rw [packedGraph_adj_iff]
    constructor
    · rintro ⟨B, hB, hv, hu⟩
      obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
      exact G.within_group B hB hv hu hne.symm
    · intro h
      obtain ⟨B, ⟨hB, hv, hu⟩, _⟩ := G.cross_group h
      have hne : u ≠ v := fun he => h (he ▸ G.groups.refl v)
      exact ⟨B, hB, hv, Finset.mem_erase.mpr ⟨hne, hu⟩⟩
  rw [hneighbors, Set.ncard_compl, G.group_card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The 56 cross-group neighbors of a point are partitioned into sevens by its blocks. -/
private theorem point_block_count (G : GDD) (v : V) :
    (G.blocks.filter (fun B => v ∈ B)).card = 8 := by
  let H := packedGraph G.blocks id
  let : Fintype (H.neighborSet v) := Fintype.ofFinite _
  have hpack := packedGraph_degree G.blocks id 8 G.block_card
    (CPECCBridge.design_blocks_inter_le_one G) v
  rw [← SimpleGraph.ncard_neighborSet, packed_neighbors_card G v] at hpack
  change 56 = 7 * (G.blocks.filter (fun B => v ∈ B)).card at hpack
  omega

private theorem incidence_count (G : GDD) (u v : V) :
    (G.blocks.filter (fun B => u ∈ B ∧ v ∈ B)).card =
      if u = v then 8 else if G.groups.r u v then 0 else 1 := by
  by_cases huv : u = v
  · subst v
    simp only [ite_true, and_self]
    exact point_block_count G u
  · by_cases hgroup : G.groups.r u v
    · have hempty : G.blocks.filter (fun B => u ∈ B ∧ v ∈ B) = ∅ := by
        rw [Finset.filter_eq_empty_iff.mpr]
        intro B hB h
        exact (G.within_group B hB h.1 h.2 huv) hgroup
      rw [ite_eq_right huv, ite_eq_left hgroup]
      exact Finset.card_eq_zero.mpr hempty
    · obtain ⟨B0, hB0, huniq⟩ := G.cross_group hgroup
      have hfilter : G.blocks.filter (fun B => u ∈ B ∧ v ∈ B) = {B0} := by
        ext B
        constructor
        · intro hB
          apply Finset.mem_singleton.mpr
          exact huniq B ⟨(Finset.mem_filter.mp hB).1, (Finset.mem_filter.mp hB).2.1,
            (Finset.mem_filter.mp hB).2.2⟩
        · intro hB
          have : B = B0 := Finset.mem_singleton.mp hB
          subst B
          exact Finset.mem_filter.mpr ⟨hB0.1, hB0.2.1, hB0.2.2⟩
      rw [ite_eq_right huv, ite_eq_right hgroup, hfilter]
      simp

private abbrev DesignBlock (G : GDD) := {B // B ∈ G.blocks}

private def incidenceMatrix (G : GDD) (eV : GramIndex ≃ V)
    (eB : GramIndex ≃ DesignBlock G) : Matrix GramIndex GramIndex ℤ :=
  Matrix.of fun i j => if eV i ∈ (eB j).1 then 1 else 0

private theorem inc_gram_entry (G : GDD) (eV : GramIndex ≃ V) (eB : GramIndex ≃ DesignBlock G)
    (i j : GramIndex) :
    (incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ) i j =
      (G.blocks.filter (fun B => eV i ∈ B ∧ eV j ∈ B)).card := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidenceMatrix, Matrix.of_apply]
  have hsumb :
      (∑ k : GramIndex,
        (if eV i ∈ (eB k).1 then (1 : ℤ) else 0) *
          (if eV j ∈ (eB k).1 then (1 : ℤ) else 0)) =
      ∑ B : DesignBlock G,
        (if eV i ∈ B.1 then (1 : ℤ) else 0) *
          (if eV j ∈ B.1 then (1 : ℤ) else 0) := by
    apply Fintype.sum_equiv eB
    intro k
    rfl
  rw [hsumb]
  have hco := Finset.sum_coe_sort G.blocks
    (fun B => (if eV i ∈ B then (1 : ℤ) else 0) *
      (if eV j ∈ B then (1 : ℤ) else 0))
  rw [hco]
  have hsumif :
      (∑ B ∈ G.blocks,
        (if eV i ∈ B then (1 : ℤ) else 0) *
          (if eV j ∈ B then (1 : ℤ) else 0)) =
      ∑ B ∈ G.blocks, if eV i ∈ B ∧ eV j ∈ B then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hi : eV i ∈ B <;> by_cases hj : eV j ∈ B <;> simp [hi, hj]
  rw [hsumif]
  have hcast :
      (∑ B ∈ G.blocks, if eV i ∈ B ∧ eV j ∈ B then (1 : ℤ) else 0) =
        ((G.blocks.filter (fun B => eV i ∈ B ∧ eV j ∈ B)).card : ℤ) := by
    rw [Finset.card_filter]
    norm_num
  exact hcast

private theorem inc_gram_entry_value (G : GDD) (eV : GramIndex ≃ V) (eB : GramIndex ≃ DesignBlock G)
    (heV : ∀ i j, G.groups.r (eV i) (eV j) ↔ i.1 = j.1)
    (i j : GramIndex) :
    (incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ) i j =
      if i = j then 8 else if i.1 = j.1 then 0 else 1 := by
  rw [inc_gram_entry, incidence_count]
  by_cases hij : i = j
  · subst j
    simp
  · have hneq : eV i ≠ eV j := by
      intro h
      exact hij (eV.injective h)
    simp only [ite_eq_right hij, ite_eq_right hneq]
    by_cases hfirst : i.1 = j.1
    · simp [hfirst, (heV i j).mpr hfirst]
    · simp [hfirst, (heV i j).not.mpr hfirst]

/-- A design with eight-point blocks and two-point groups on 58 points is impossible. -/
theorem no_group_divisible_design :
    ¬ Nonempty (GroupDivisibleDesign (Fin 58) 8 2) := by
  rintro ⟨G⟩
  obtain ⟨eV, heV⟩ := enum_group G
  have hBcard : Fintype.card (DesignBlock G) = 58 := by
    rw [Fintype.card_coe]
    simpa using CPECCBridge.design_block_count G (by decide)
  let idxFin : GramIndex ≃ Fin 58 := Fintype.equivFin GramIndex
  let eB : GramIndex ≃ DesignBlock G := idxFin.trans (Fintype.equivFinOfCardEq hBcard).symm
  let A : Matrix GramIndex GramIndex ℤ := incidenceMatrix G eV eB
  have hgram : A * Aᵀ =
      (8 : ℤ) • (1 : Matrix GramIndex GramIndex ℤ) + onesMatrix ℤ - groupMatrix ℤ := by
    ext i j
    change (incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ) i j = _
    rw [inc_gram_entry_value G eV eB heV]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, onesMatrix, groupMatrix, Matrix.of_apply]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hfirst : i.1 = j.1
      · simp [hij, hfirst]
      · simp [hij, hfirst]
  exact gram_impossible A hgram

/-- The finite leave bound specialized to the 58-coordinate support model. -/
private theorem support_upper_bound_58 (m : ℕ) (P : Fin m → Finset (Finset (Fin 58)))
    (hP : IsSupportFamily P 6 2) : m ≤ 58 := by
  obtain ⟨hsize, hdel, hcross⟩ := hP
  have h := finite_cpecc_support_upper_bound P 58 6 2 2 8
    (Fintype.card_fin 58) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hsize hdel hcross (by decide)
  simpa only [Fintype.card_fin] using h

private theorem support_upper_bound (m : ℕ) (P : Fin m → Finset (Finset (Fin 58)))
    (hP : IsSupportFamily P 6 2) : m ≤ 57 := by
  have h58 := support_upper_bound_58 m P hP
  by_contra h
  have hm : m = 58 := by omega
  subst m
  have hmax : IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset (Fin 58)),
      IsSupportFamily P 6 2} 58 := by
    refine ⟨⟨P, hP⟩, ?_⟩
    rintro m ⟨P', hP'⟩
    exact support_upper_bound_58 m P' hP'
  have hiff := even_residue_optimum_iff_groupDivisibleDesign
    (V := Fin 58) (n := 58) (w := 6) (t := 2) (Fintype.card_fin 58)
    (by decide) (by decide) (by decide) (by exact ⟨1, rfl⟩) (by decide)
  exact no_group_divisible_design (hiff.mp hmax)

end DesignObstruction

/-- On 58 coordinates, the greatest number of information classes for weight six
and deletion size two is 57 in the support model for correction radius four. -/
theorem support_optimum :
    IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset (Fin 58)), IsSupportFamily P 6 2} 57 := by
  refine ⟨⟨informationClass, word_card, avoids_hot, fun _ _ hij => cross_inter_le_one hij⟩, ?_⟩
  rintro m ⟨P, hP⟩
  exact support_upper_bound m P hP

end

end CPECCBridge.Length58
