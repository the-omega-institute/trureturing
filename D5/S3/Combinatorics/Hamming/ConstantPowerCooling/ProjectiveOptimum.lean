/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ProjectiveOptimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/ProjectiveOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement, mathlib/module/Mathlib.LinearAlgebra.Projectivization.Cardinality]
   utility: none
   digest: The projective-plane progression has exact cooling-code optimum n - 1 under the parity and nonsquare condition. -/

import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.GroupDivisibleDesign
import OmegaBuild.Commands
import Mathlib.Combinatorics.Configuration
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

compile_only_with_mathlib

/-! # The exact cooling-code optimum in the projective-plane progression

Projective lines give one information class per line. The residue-two
criterion turns equality in the finite upper bound into a design with pairs
as groups. A determinant obstruction excludes that design under either
parity and nonsquare hypothesis.
-/

namespace CPECCBridge.ProjectiveOptimum

open Matrix Finset SimpleGraph
open scoped BigOperators LinearAlgebra.Projectivization

noncomputable section

section GramDeterminant

private abbrev GramIndex (m : ℕ) := Fin m × Fin 2

private def onesMatrix (m : ℕ) (R : Type*) [One R] : Matrix (GramIndex m) (GramIndex m) R :=
  Matrix.of fun _ _ => 1

private def groupMatrix (m : ℕ) (R : Type*) [Zero R] [One R] :
    Matrix (GramIndex m) (GramIndex m) R :=
  Matrix.of fun i j => if i.1 = j.1 then 1 else 0

private def gramBase (m : ℕ) (a : ℚ) : Matrix (GramIndex m) (GramIndex m) ℚ :=
  a • 1 - groupMatrix m ℚ

private def pairBlock (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  a • 1 - Matrix.of (fun _ _ => 1)

private theorem det_gramBase (m : ℕ) (a : ℚ) :
    (gramBase m a).det = (a * (a - 2)) ^ m := by
  let swap : (Fin 2 × Fin m) ≃ GramIndex m := Equiv.prodComm _ _
  have hB : gramBase m a = Matrix.reindex swap swap
      (Matrix.blockDiagonal (fun _ : Fin m => pairBlock a)) := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp only [gramBase, pairBlock, groupMatrix, swap, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Matrix.blockDiagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  have hblock : (pairBlock a).det = a * (a - 2) := by
    rw [Matrix.det_fin_two]
    norm_num [pairBlock, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    ring
  rw [hB, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp only [hblock, Fin.prod_const]

private def column (m : ℕ) : Matrix (GramIndex m) Unit ℚ := Matrix.of fun _ _ => 1
private def row (m : ℕ) (a : ℚ) : Matrix Unit (GramIndex m) ℚ :=
  Matrix.of fun _ _ => 1 / (a - 2)

private theorem groupMatrix_mul_column (m : ℕ) :
    groupMatrix m ℚ * column m = (2 : ℚ) • column m := by
  ext i j
  simp only [groupMatrix, column, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, one_add_one_eq_two]

private theorem gramBase_mul_column (m : ℕ) (a : ℚ) :
    gramBase m a * column m = (a - 2) • column m := by
  rw [gramBase, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, groupMatrix_mul_column, ← sub_smul]

private theorem onesMatrix_factor (m : ℕ) (a : ℚ) (ha : a - 2 ≠ 0) :
    gramBase m a * (column m * row m a) = onesMatrix m ℚ := by
  rw [← Matrix.mul_assoc, gramBase_mul_column, Matrix.smul_mul]
  ext i j
  simp [onesMatrix, column, row, Matrix.smul_apply, Matrix.mul_apply, div_eq_inv_mul, ha]

private theorem det_rank_one (m : ℕ) (a : ℚ) :
    (1 + column m * row m a).det = 1 + (2 * (m : ℚ)) / (a - 2) := by
  rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [column, row, Matrix.add_apply, Matrix.mul_apply, Fintype.card_prod,
    nsmul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A uniform pair-block matrix plus the all-ones matrix has a scalar rank-one update. -/
private theorem det_pair_gram_rat (m : ℕ) (a : ℚ) (hm : 0 < m) (ha : a - 2 ≠ 0) :
    (a • (1 : Matrix (GramIndex m) (GramIndex m) ℚ) + onesMatrix m ℚ - groupMatrix m ℚ).det =
      a ^ m * (a - 2) ^ (m - 1) * (a - 2 + 2 * (m : ℚ)) := by
  have h :
      a • (1 : Matrix (GramIndex m) (GramIndex m) ℚ) + onesMatrix m ℚ - groupMatrix m ℚ =
        gramBase m a * (1 + column m * row m a) := by
    rw [Matrix.mul_add, Matrix.mul_one, onesMatrix_factor m a ha, gramBase, sub_add_eq_add_sub]
  rw [h, Matrix.det_mul, det_gramBase, det_rank_one, mul_pow,
    show (a - 2) ^ m = (a - 2) ^ (m - 1) * (a - 2) by
      rw [← pow_succ, Nat.sub_add_cancel hm]]
  field_simp

/-- The determinant for the parameter progression in the registered problem. -/
private theorem det_pair_gram_int (q m : ℕ) (hq : 1 < q)
    (hm : 2 * m = q * (q + 1) + 2) :
    (((q + 1 : ℕ) : ℤ) • (1 : Matrix (GramIndex m) (GramIndex m) ℤ) +
      onesMatrix m ℤ - groupMatrix m ℤ).det =
      ((q + 1 : ℕ) : ℤ) ^ (m + 2) * ((q - 1 : ℕ) : ℤ) ^ (m - 1) := by
  let G : Matrix (GramIndex m) (GramIndex m) ℤ :=
    ((q + 1 : ℕ) : ℤ) • 1 + onesMatrix m ℤ - groupMatrix m ℤ
  have hG : (Int.castRingHom ℚ).mapMatrix G =
      ((q + 1 : ℕ) : ℚ) • (1 : Matrix (GramIndex m) (GramIndex m) ℚ) +
        onesMatrix m ℚ - groupMatrix m ℚ := by
    ext i j
    simp only [G, onesMatrix, groupMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, map_sub, map_add, map_mul, apply_ite, map_one, map_zero, map_natCast]
    by_cases h : i.1 = j.1 <;> simp only [h, ite_true, ite_false]
  have htwo : (2 : ℚ) * (m : ℚ) = (q : ℚ) * ((q : ℚ) + 1) + 2 := by
    exact_mod_cast hm
  have ha : (((q + 1 : ℕ) : ℚ) - 2) ≠ 0 := by
    have hq' : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    push_cast
    linarith
  have hpred : (((q + 1 : ℕ) : ℚ) - 2) = ((q - 1 : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hq.le]
    ring
  have hlast : (((q + 1 : ℕ) : ℚ) - 2) + 2 * (m : ℚ) =
      ((q + 1 : ℕ) : ℚ) ^ 2 := by
    rw [htwo]
    push_cast
    ring
  have hdet := (Int.castRingHom ℚ).map_det G
  rw [hG, det_pair_gram_rat m _ (by omega) ha, hlast, hpred] at hdet
  change (↑G.det : ℚ) = _ at hdet
  rw [pow_add]
  have hdet' : (↑G.det : ℚ) =
      ((q + 1 : ℕ) : ℚ) ^ m * ((q + 1 : ℕ) : ℚ) ^ 2 * ((q - 1 : ℕ) : ℚ) ^ (m - 1) := by
    simpa only [mul_right_comm] using hdet
  exact_mod_cast hdet'

/-- Prime multiplicities in the determinant isolate the factor with odd exponent. -/
private theorem determinant_not_square (q m : ℕ) (hq : 1 < q) (hm : 0 < m)
    (h : (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1))) :
    ¬ IsSquare ((q + 1) ^ (m + 2) * (q - 1) ^ (m - 1)) := by
  intro hs
  have hval (p : ℕ) (hp : p.Prime) :
      Even ((m + 2) * (q + 1).factorization p + (m - 1) * (q - 1).factorization p) := by
    have hsq := Nat.isSquare_iff_even_factorization.mp hs p hp
    have hpos : 0 < q - 1 := by omega
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      nsmul_eq_mul, nsmul_eq_mul] at hsq
    exact hsq
  rcases h with ⟨ho, hns⟩ | ⟨he, hns⟩
  · apply hns
    apply Nat.isSquare_iff_even_factorization.mpr
    intro p hp
    have he₁ : ¬ Even (m + 2) := Nat.not_even_iff_odd.mpr (ho.add_even (by decide))
    have he₂ : Even (m - 1) := (Nat.even_sub hm).mpr (by
      simp [Nat.not_even_iff_odd.mpr ho])
    have hright : Even ((m - 1) * (q - 1).factorization p) := Nat.even_mul.mpr (Or.inl he₂)
    have hleft := (Nat.even_add.mp (hval p hp)).mpr hright
    exact (Nat.even_mul.mp hleft).resolve_left he₁
  · apply hns
    apply Nat.isSquare_iff_even_factorization.mpr
    intro p hp
    have he₁ : Even (m + 2) := he.add (by decide)
    have he₂ : ¬ Even (m - 1) := Nat.not_even_iff_odd.mpr ((Nat.odd_sub hm).mpr (by
      simp [Nat.not_odd_iff_even.mpr he]))
    have hleft : Even ((m + 2) * (q + 1).factorization p) := Nat.even_mul.mpr (Or.inl he₁)
    have hright := (Nat.even_add.mp (hval p hp)).mp hleft
    exact (Nat.even_mul.mp hright).resolve_left he₂

private theorem pair_gram_impossible (q m : ℕ) (hq : 1 < q)
    (hm : 2 * m = q * (q + 1) + 2)
    (h : (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1)))
    (A : Matrix (GramIndex m) (GramIndex m) ℤ) :
    A * Aᵀ ≠ ((q + 1 : ℕ) : ℤ) • 1 + onesMatrix m ℤ - groupMatrix m ℤ := by
  intro heq
  have hdet := congrArg Matrix.det heq
  rw [Matrix.det_mul, Matrix.det_transpose, det_pair_gram_int q m hq hm] at hdet
  have habs := congrArg Int.natAbs hdet
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at habs
  exact determinant_not_square q m hq (by omega) h ⟨A.det.natAbs, habs.symm⟩

end GramDeterminant

section DesignIncidence

attribute [local instance] Classical.propDecidable

private def groupPartition {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) : Finpartition (Finset.univ : Finset V) :=
  @Finpartition.ofSetoid V _ _ G.groups (Classical.decRel _)

private theorem parts_card_two {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) :
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

private theorem parts_card {V : Type*} [Fintype V] [DecidableEq V] {k m : ℕ}
    (G : GroupDivisibleDesign V k 2) (hm : 2 * m = Fintype.card V) :
    Fintype.card (groupPartition G).parts = m := by
  have hsum : (∑ t ∈ (groupPartition G).parts, t.card) = 2 * m := by
    simpa only [Finset.card_univ, ← hm] using (groupPartition G).sum_card_parts
  have hconst : (∑ _t ∈ (groupPartition G).parts, (2 : ℕ)) =
      2 * (groupPartition G).parts.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hsum' : (∑ t ∈ (groupPartition G).parts, t.card) =
      ∑ _t ∈ (groupPartition G).parts, (2 : ℕ) := by
    exact Finset.sum_congr rfl fun t ht => parts_card_two G ⟨t, ht⟩
  rw [hsum', hconst] at hsum
  rw [Fintype.card_coe]
  omega

private theorem enum_group {V : Type*} [Fintype V] [DecidableEq V] {k m : ℕ}
    (G : GroupDivisibleDesign V k 2) (hm : 2 * m = Fintype.card V) :
    ∃ e : (Fin m × Fin 2) ≃ V,
      ∀ i j, G.groups.r (e i) (e j) ↔ i.1 = j.1 := by
  let QG := groupPartition G
  have hparts : Fintype.card QG.parts = m := parts_card G hm
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
  let eq : QG.parts ≃ Fin m := Fintype.equivFinOfCardEq hparts
  let ec : (Fin m × Fin 2) ≃ (Σ t : QG.parts, Fin t.1.card) :=
    (Equiv.sigmaEquivProd (Fin m) (Fin 2)).symm.trans
      (eq.symm.sigmaCongr (fun t => by
        exact (Fintype.equivFinOfCardEq (by simpa using parts_card_two G (eq.symm t))).symm))
  let e : (Fin m × Fin 2) ≃ V := ec.trans f'.symm
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

private theorem packed_neighbors_card {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : GroupDivisibleDesign V k 2) (v : V) :
    ((packedGraph G.blocks id).neighborSet v).ncard = Fintype.card V - 2 := by
  let H := packedGraph G.blocks id
  change (H.neighborSet v).ncard = Fintype.card V - 2
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
  rw [hneighbors, Set.ncard_compl, G.group_card, Nat.card_eq_fintype_card]

private theorem point_block_count {q n : ℕ} (hq : 1 < q)
    (hn : n = q * (q + 1) + 2) (G : GroupDivisibleDesign (Fin n) (q + 1) 2)
    (v : Fin n) : (G.blocks.filter (fun B => v ∈ B)).card = q + 1 := by
  let H := packedGraph G.blocks id
  let : Fintype (H.neighborSet v) := Fintype.ofFinite _
  have hpack := packedGraph_degree G.blocks id (q + 1) G.block_card
    (CPECCBridge.design_blocks_inter_le_one G) v
  have hlen : n - 2 = q * (q + 1) := by omega
  rw [← SimpleGraph.ncard_neighborSet, packed_neighbors_card G v, Fintype.card_fin,
    hlen, Nat.add_sub_cancel] at hpack
  exact Nat.mul_left_cancel (by omega) hpack.symm

private theorem incidence_count {V : Type*} [DecidableEq V] {k : ℕ}
    (G : GroupDivisibleDesign V k 2)
    (hdegree : ∀ v : V, (G.blocks.filter (fun B => v ∈ B)).card = k) (u v : V) :
    (G.blocks.filter (fun B => u ∈ B ∧ v ∈ B)).card =
      if u = v then k else if G.groups.r u v then 0 else 1 := by
  by_cases huv : u = v
  · subst v
    simp only [ite_true, and_self]
    exact hdegree u
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

private abbrev DesignBlock {V : Type*} [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) := {B // B ∈ G.blocks}

private def incidenceMatrix {V : Type*} [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) {m : ℕ} (eV : GramIndex m ≃ V)
    (eB : GramIndex m ≃ DesignBlock G) : Matrix (GramIndex m) (GramIndex m) ℤ :=
  Matrix.of fun i j => if eV i ∈ (eB j).1 then 1 else 0

private theorem inc_gram_entry {V : Type*} [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) {m : ℕ} (eV : GramIndex m ≃ V) (eB : GramIndex m ≃ DesignBlock G)
    (i j : GramIndex m) :
    (incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ) i j =
      (G.blocks.filter (fun B => eV i ∈ B ∧ eV j ∈ B)).card := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidenceMatrix, Matrix.of_apply]
  have hsumb :
      (∑ a : GramIndex m,
        (if eV i ∈ (eB a).1 then (1 : ℤ) else 0) *
          (if eV j ∈ (eB a).1 then (1 : ℤ) else 0)) =
      ∑ B : DesignBlock G,
        (if eV i ∈ B.1 then (1 : ℤ) else 0) *
          (if eV j ∈ B.1 then (1 : ℤ) else 0) := by
    apply Fintype.sum_equiv eB
    intro a
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

private theorem inc_gram_entry_value {V : Type*} [DecidableEq V] {k : ℕ} (G : GroupDivisibleDesign V k 2) {m : ℕ} (eV : GramIndex m ≃ V) (eB : GramIndex m ≃ DesignBlock G)
    (hdegree : ∀ v : V, (G.blocks.filter (fun B => v ∈ B)).card = k)
    (heV : ∀ i j, G.groups.r (eV i) (eV j) ↔ i.1 = j.1)
    (i j : GramIndex m) :
    (incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ) i j =
      if i = j then (k : ℤ) else if i.1 = j.1 then 0 else 1 := by
  rw [inc_gram_entry, incidence_count G hdegree]
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

/-- For the registered progression, either parity-indexed nonsquare hypothesis rules out the design. -/
private theorem no_pair_group_design (q m : ℕ) (hq : 1 < q)
    (hm : 2 * m = q * (q + 1) + 2)
    (h : (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1))) :
    ¬ Nonempty (GroupDivisibleDesign (Fin (q * (q + 1) + 2)) (q + 1) 2) := by
  rintro ⟨G⟩
  obtain ⟨eV, heV⟩ := enum_group G (hm.trans (Fintype.card_fin _).symm)
  have hBcard : Fintype.card (DesignBlock G) = q * (q + 1) + 2 := by
    rw [Fintype.card_coe, CPECCBridge.design_block_count G (by omega), Fintype.card_fin,
      Nat.add_sub_cancel, Nat.add_sub_cancel, mul_comm (q + 1) q]
    exact Nat.mul_div_cancel _ (by positivity)
  let eB : GramIndex m ≃ DesignBlock G := eV.trans
    ((Fintype.equivFinOfCardEq (Fintype.card_fin _)).trans (Fintype.equivFinOfCardEq hBcard).symm)
  have hgram : incidenceMatrix G eV eB * (incidenceMatrix G eV eB)ᵀ =
      ((q + 1 : ℕ) : ℤ) • 1 + onesMatrix m ℤ - groupMatrix m ℤ := by
    ext i j
    rw [inc_gram_entry_value G eV eB (point_block_count hq rfl G) heV]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, onesMatrix, groupMatrix, Matrix.of_apply]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hfirst : i.1 = j.1 <;> simp [hij, hfirst]
  exact pair_gram_impossible q m hq hm h (incidenceMatrix G eV eB) hgram

end DesignIncidence

section ProjectiveConstruction

private theorem projective_card_division (q : ℕ) (hq : 1 < q) :
    (q ^ 3 - 1) / (q - 1) = q * (q + 1) + 1 := by
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have hpow : 1 ≤ q ^ 3 := Nat.pow_pos (by omega)
  zify [hq.le, hpow]
  ring

variable (F : Type*) [Field F] [Finite F]

private abbrev Point := ℙ F (Fin 3 → F)

local instance pointFintype : Fintype (Point F) := Fintype.ofFinite _

private theorem point_card :
    Fintype.card (Point F) = Nat.card F * (Nat.card F + 1) + 1 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (ℙ F (Fin 3 → F)) = _
  rw [Projectivization.card'' F (Fin 3 → F), Nat.card_fun, Nat.card_fin]
  exact projective_card_division _ Finite.one_lt_card

attribute [local instance] Classical.decEq Classical.propDecidable

private theorem order_eq : Configuration.ProjectivePlane.order (Point F) (Point F) = Nat.card F := by
  let r := Configuration.ProjectivePlane.order (Point F) (Point F)
  let q := Nat.card F
  have hcard : r ^ 2 + r + 1 = q ^ 2 + q + 1 := by
    calc
      _ = Fintype.card (Point F) := (Configuration.ProjectivePlane.card_points _ _).symm
      _ = _ := by rw [point_card F]; change q * (q + 1) + 1 = _; ring
  have hstep (a b : ℕ) (hab : a < b) : a ^ 2 + a + 1 < b ^ 2 + b + 1 := by
    have hsq := Nat.pow_le_pow_left hab.le 2
    omega
  rcases lt_trichotomy r q with h | h | h
  · exact (hstep r q h).ne hcard |>.elim
  · exact h
  · exact (hstep q r h).ne hcard.symm |>.elim

private theorem coordinate_card :
    Fintype.card (Option (Point F)) = Nat.card F * (Nat.card F + 1) + 2 := by
  rw [Fintype.card_option, point_card]

private def pointToCoordinate : Point F ↪ Fin (Nat.card F * (Nat.card F + 1) + 2) :=
  (⟨some, Option.some_injective (Point F)⟩ : Point F ↪ Option (Point F)).trans
    (Fintype.equivFinOfCardEq (coordinate_card F)).toEmbedding

private def indexToLine : Fin (Nat.card F * (Nat.card F + 1) + 1) ≃ Point F :=
  (Fintype.equivFinOfCardEq (point_card F)).symm

private def linePoints (l : Point F) : Finset (Point F) :=
  Finset.univ.filter (· ∈ l)

private theorem mem_linePoints (p l : Point F) : p ∈ linePoints F l ↔ p ∈ l := by
  simp [linePoints]

private theorem linePoints_card (l : Point F) : (linePoints F l).card = Nat.card F + 1 := by
  let : Fintype {p : Point F // p ∈ l} := Fintype.ofFinite _
  rw [linePoints, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  change Configuration.pointCount (Point F) l = _
  rw [Configuration.ProjectivePlane.pointCount_eq (Point F) l, order_eq F]

private def block (i : Fin (Nat.card F * (Nat.card F + 1) + 1)) :
    Finset (Fin (Nat.card F * (Nat.card F + 1) + 2)) :=
  (linePoints F (indexToLine F i)).map (pointToCoordinate F)

private theorem block_card (i : Fin (Nat.card F * (Nat.card F + 1) + 1)) :
    (block F i).card = Nat.card F + 1 := by
  rw [block, Finset.card_map, linePoints_card]

private theorem block_inter_le_one {i j : Fin (Nat.card F * (Nat.card F + 1) + 1)}
    (hij : i ≠ j) : (block F i ∩ block F j).card ≤ 1 := by
  simp only [block, ← Finset.map_inter, Finset.card_map]
  apply Finset.card_le_one.mpr
  intro p hp r hr
  obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
  obtain ⟨hri, hrj⟩ := Finset.mem_inter.mp hr
  have h := Configuration.Nondegenerate.eq_or_eq
    ((mem_linePoints F _ _).mp hpi) ((mem_linePoints F _ _).mp hri)
    ((mem_linePoints F _ _).mp hpj) ((mem_linePoints F _ _).mp hrj)
  exact h.resolve_right (fun heq => hij ((indexToLine F).injective heq))

/-- The projective construction uses the points plus one additional coordinate. -/
private theorem projective_support_family :
    let q := Nat.card F
    ∃ P : Fin (q * (q + 1) + 1) → Finset (Finset (Fin (q * (q + 1) + 2))),
      IsSupportFamily P (q - 1) 2 := by
  dsimp
  refine ⟨fun i => (block F i).powersetCard (Nat.card F - 1), ?_, ?_, ?_⟩
  · intro i A hA
    exact (Finset.mem_powersetCard.mp hA).2
  · intro i D hD
    have hremain := Finset.le_card_sdiff D (block F i)
    rw [hD, block_card] at hremain
    have hweight : Nat.card F - 1 ≤ ((block F i) \ D).card := by omega
    obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq hweight
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨hA.trans Finset.sdiff_subset, hcard⟩, ?_⟩
    exact Finset.disjoint_left.mpr (fun _ hpD hpA => (Finset.mem_sdiff.mp (hA hpA)).2 hpD)
  · intro i j hij A hA B hB
    exact (Finset.card_le_card (Finset.inter_subset_inter
      (Finset.mem_powersetCard.mp hA).1 (Finset.mem_powersetCard.mp hB).1)).trans
        (block_inter_le_one F hij)

end ProjectiveConstruction

section Optimum

private theorem threshold (w : ℕ) (hw : 6 ≤ w) :
    (w + 2) * (w + 2 + 2 - 2) ≤ 2 * AppendixA.B w 2 := by
  have hchoose (a : ℕ) : 2 * a.choose 2 = a * (a - 1) := by
    rw [mul_comm, Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd]
  change (w + 2) * (w + 2 + 2 - 2) ≤ 2 * (w.choose 2 + (w + 1).choose 2)
  rw [Nat.add_sub_cancel, Nat.mul_add 2, hchoose, hchoose, Nat.add_sub_cancel]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hw
  rw [show 6 + r - 1 = 5 + r by omega]
  nlinarith

/-- For every finite field of odd order q ≥ 7, under either stated nonsquare
condition, the support-model optimum at weight q - 1 and deletion size two is n - 1. -/
theorem support_optimum (F : Type*) [Field F] [Finite F]
    (hq7 : 7 ≤ Nat.card F) (hqOdd : Odd (Nat.card F))
    (h : let q := Nat.card F
         let n := q * (q + 1) + 2
         let m := n / 2
         (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1))) :
    let q := Nat.card F
    let n := q * (q + 1) + 2
    IsGreatest {s : ℕ | ∃ P : Fin s → Finset (Finset (Fin n)), IsSupportFamily P (q - 1) 2}
      (n - 1) := by
  classical
  let q := Nat.card F
  let n := q * (q + 1) + 2
  let m := n / 2
  change 7 ≤ q at hq7
  change Odd q at hqOdd
  change (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1)) at h
  change IsGreatest {s : ℕ | ∃ P : Fin s → Finset (Finset (Fin n)),
    IsSupportFamily P (q - 1) 2} (n - 1)
  have hq : 1 < q := by omega
  have hn2 : 2 * m = n := by
    have hkEven : Even (q + 1) := Nat.even_add.mpr (by
      simp [Nat.not_even_iff_odd.mpr hqOdd])
    have hnEven : Even n := (Nat.even_mul.mpr (Or.inr hkEven)).add (by decide)
    obtain ⟨r, hr⟩ := hnEven
    dsimp only [m]
    omega
  have hkdef : q + 1 = (q - 1) + 2 := by omega
  have hkN : q + 1 ≤ n := by
    have hle := Nat.mul_le_mul_right (q + 1) (show 1 ≤ q by omega)
    simp only [one_mul] at hle
    exact hle.trans (Nat.le_add_right _ _)
  have hlen : n - 2 = q * (q + 1) := Nat.add_sub_cancel _ _
  have hmul : (q + 1) * (q + 1 - 1) = q * (q + 1) := by
    rw [Nat.add_sub_cancel, Nat.mul_comm]
  have hRdiv : q + 1 - 1 ∣ n - 2 := by
    rw [Nat.add_sub_cancel, hlen]
    exact ⟨q + 1, rfl⟩
  have hJdiv : (q + 1) * (q + 1 - 1) ∣ n * (n - 2) := by
    rw [hmul, hlen]
    exact ⟨n, Nat.mul_comm _ _⟩
  have hJ : n * (n - 2) / ((q + 1) * (q + 1 - 1)) = n := by
    rw [hlen, hmul]
    exact Nat.mul_div_cancel _ (by positivity)
  have hresidue : n % (((q - 1) + 2) * ((q - 1) + 2 - 1)) = 2 := by
    rw [← hkdef, hmul, show n = 2 + q * (q + 1) by exact Nat.add_comm _ _,
      Nat.add_mod_right, Nat.mod_eq_of_lt]
    have hle := Nat.mul_le_mul_right (q + 1) (show 1 ≤ q by omega)
    simp only [one_mul] at hle
    omega
  have hbound (s : ℕ) (P : Fin s → Finset (Finset (Fin n)))
      (hP : IsSupportFamily P (q - 1) 2) : s ≤ n := by
    obtain ⟨hsize, hdel, hcross⟩ := hP
    have hthreshold := threshold (q - 1) (by omega)
    rw [← hkdef] at hthreshold
    have hu := finite_cpecc_support_upper_bound P n (q - 1) 2 2 (q + 1)
      (Fintype.card_fin n) hkdef hkN (by decide) (by omega) (by decide) (by omega)
      hRdiv hJdiv hsize hdel hcross hthreshold
    simpa only [Fintype.card_fin, hJ] using hu
  refine ⟨?_, ?_⟩
  · have hp := projective_support_family F
    change ∃ P : Fin (q * (q + 1) + 1) → Finset (Finset (Fin n)),
      IsSupportFamily P (q - 1) 2 at hp
    have hind : n - 1 = q * (q + 1) + 1 := by dsimp [n]
    rwa [hind]
  · rintro s ⟨P, hP⟩
    have hsn := hbound s P hP
    by_contra hlt
    have hseq : s = n := by omega
    subst s
    have hgreatest : IsGreatest {s : ℕ | ∃ P : Fin s → Finset (Finset (Fin n)),
        IsSupportFamily P (q - 1) 2} n := by
      refine ⟨⟨P, hP⟩, ?_⟩
      rintro s ⟨P', hP'⟩
      exact hbound s P' hP'
    have hiff := even_residue_optimum_iff_groupDivisibleDesign
      (V := Fin n) (n := n) (w := q - 1) (t := 2) (Fintype.card_fin n)
      (hkdef ▸ hkN) (by decide) (by omega) (by decide) hresidue
    simp only [← hkdef, hJ] at hiff
    exact no_pair_group_design q m hq hn2 h (hiff.mp hgreatest)

end Optimum

end

end CPECCBridge.ProjectiveOptimum
