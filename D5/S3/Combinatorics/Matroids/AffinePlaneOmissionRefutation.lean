/- GID: D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.claim; result=D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.result; claim=D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.claim
   digest: Affine lines give eleven independent elements killed by three in the rank-three lifting obstruction. -/

import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
import Mathlib.Data.ZMod.Basic
import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors

/-! Finite certificate for the rank-three affine-plane omissions. -/

noncomputable section

namespace D5.S3.Combinatorics.Matroids.AffinePlaneOmissionRefutation

open Finset
open D5.S3.Combinatorics.Matroids
open ParallelCircuitObstruction
open _root_.D5.S3.Combinatorics.Matroids.RationalJointCircuitImage (RationalResidue)
open _root_.D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod)
open _root_.D5.S3.Combinatorics.Matroids.JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open scoped Matroid
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

private abbrev V := Fin 9
private abbrev I := Fin 11

private def holes : Finset (Finset V) := {{0, 1, 2}, {0, 3, 6}, {0, 4, 8}, {0, 5, 7}, {1, 3, 8}, {1, 4, 7}, {1, 5, 6}, {2, 3, 7}, {2, 4, 6}, {2, 5, 8}, {3, 4, 5}, {6, 7, 8}}

private def positiveNegative : I → List ℕ × List ℕ
  | 0 => ([11, 19, 35, 67, 131, 259, 14, 22, 38, 70, 134, 262], [13, 21, 37, 69, 133, 261])
  | 1 => ([19, 67, 37, 133, 97, 289, 385, 38, 134, 26, 42, 74, 138, 52, 148, 276, 196, 324], [11, 259, 13, 261, 41, 137, 49, 145, 193, 22, 70, 274, 290, 322, 386, 28, 76, 100])
  | 2 => ([35, 67, 13, 133, 49, 81, 145, 14, 134, 162, 290, 194, 322, 28, 44, 76, 268, 388], [19, 259, 21, 261, 25, 265, 289, 321, 385, 38, 70, 42, 74, 50, 82, 148, 164, 196])
  | 3 => ([11, 131, 13, 69, 137, 81, 289, 193, 385, 22, 134, 138, 50, 82, 290, 322, 28, 44, 88, 152, 280, 104, 168, 296], [19, 67, 37, 133, 41, 265, 49, 145, 97, 321, 38, 70, 26, 74, 274, 162, 194, 386])
  | 4 => ([67, 69, 25, 41, 137, 265, 81, 97, 74, 76, 200, 328], [11, 13, 193, 321, 88, 104])
  | 5 => ([35, 67, 137, 49, 81, 145, 138, 162, 290, 194, 322, 392], [19, 259, 13, 21, 261, 25, 265, 289, 321, 385, 14, 38, 70, 42, 74, 50, 82, 28, 44, 76, 268, 152, 168, 200])
  | 6 => ([11, 131, 13, 69, 25, 41, 137, 81, 289, 193, 385, 22, 134, 138, 82, 290, 322, 52, 112, 176, 304], [19, 67, 37, 133, 265, 145, 97, 321, 38, 70, 42, 74, 50, 274, 162, 194, 386, 28, 88, 152, 280])
  | 7 => ([19, 67, 21, 37, 133, 81, 97, 289, 385, 38, 70, 134, 26, 42, 74, 138, 82, 28, 88, 208, 336], [11, 259, 13, 69, 261, 41, 137, 49, 145, 193, 274, 290, 322, 386, 52, 148, 276, 112])
  | 8 => ([19, 145, 134, 138, 50, 82, 274, 162, 194, 148, 152, 400], [131, 22, 26, 386, 176, 208])
  | 9 => ([35, 97, 70, 74, 82, 162, 290, 100, 104, 112, 224, 352], [67, 38, 42, 50, 194, 322])
  | 10 => ([131, 133, 137, 145, 97, 289, 193, 162, 164, 168, 176, 416], [35, 37, 41, 49, 385, 224])

private def readSite : I → Finset V
  | 0 => {1, 2, 8}
  | 1 => {2, 6, 8}
  | 2 => {2, 7, 8}
  | 3 => {3, 5, 8}
  | 4 => {3, 6, 8}
  | 5 => {3, 7, 8}
  | 6 => {4, 5, 8}
  | 7 => {4, 6, 8}
  | 8 => {4, 7, 8}
  | 9 => {5, 6, 8}
  | 10 => {5, 7, 8}

private def mask (F : Finset V) : ℕ :=
  ∑ i ∈ F, 2 ^ i.val

private def coeff (j : I) (F : Finset V) : ZMod 3 :=
  if F.card = 3 ∧ F ∉ holes then
    if mask F ∈ (positiveNegative j).1 then 1
    else if mask F ∈ (positiveNegative j).2 then 2
    else 0
  else 0

private def lower : Finset (Finset V) := (univ : Finset V).powersetCard 2
private def upper : Finset (Finset V) := (univ : Finset V).powersetCard 4

private def deletion (j : I) (F : Finset V) : ZMod 3 :=
  ∑ i ∈ univ \ F, insertionSign F i • coeff j (insert i F)

private def extension (j : I) (F : Finset V) : ZMod 3 :=
  ∑ i ∈ F, CircuitCycleDecomposition.restrictionSign F i ∅ • coeff j (F.erase i)

private abbrev rowsWithZero (j : I) : Prop :=
  (∀ F : lower, deletion j F.val = 0) ∧ (∀ F : upper, extension j F.val = 0)

private def rowsDecidable (j : I) : Decidable (rowsWithZero j) := by
  unfold rowsWithZero
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem all_rows_zero : ∀ j : I, rowsWithZero j := by
  intro j
  fin_cases j <;> exact of_decide_eq_true (inst := rowsDecidable _) (by rfl)

set_option maxRecDepth 8192 in
private theorem coordinates_identity :
    ∀ i j : I, coeff j (readSite i) = if i = j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide


private theorem hole_size : ∀ H ∈ holes, H.card = 3 := by
  simp only [holes, forall_mem_insert, mem_singleton, forall_eq]
  decide

private theorem sparse : (↑holes : Set (Finset V)).Pairwise
    (fun H J => (H ∩ J).card + 2 ≤ 3) := by
  change ∀ H ∈ holes, ∀ J ∈ holes, H ≠ J → _
  simp only [holes, forall_mem_insert, mem_singleton, forall_eq]
  repeat' apply And.intro
  all_goals decide

private theorem core_exists : ∃ M : Matroid V, M.E = Set.univ ∧
    ∀ F : Finset V, M.IsBase (F : Set V) ↔ F.card = 3 ∧ F ∉ holes :=
  SparsePavingCircuitCoordinates.exists_sparse_paving_core
    (holes := (↑holes : Set (Finset V))) (by decide) (by decide) sparse

private noncomputable def core : Matroid V := core_exists.choose
private theorem core_ground : core.E = Set.univ := core_exists.choose_spec.1
private theorem core_base (F : Finset V) :
    core.IsBase (F : Set V) ↔ F.card = 3 ∧ F ∉ holes :=
  core_exists.choose_spec.2 F

private def embed (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) : ZMod 3 →ₗ[ℤ] RationalResidue :=
  (ResidueTorsion 3).subtype.comp e.symm.toLinearMap

private theorem id_weight (i : V) : (univ.filter (fun x : V => id x = i)).card = 1 := by
  rw [show univ.filter (fun x : V => id x = i) = {i} by ext x; simp]
  exact card_singleton i

private theorem all_deletion_zero (j : I) (F : Finset V) : deletion j F = 0 := by
  by_cases hF : F.card = 2
  · have hmem : F ∈ lower := mem_powersetCard.mpr ⟨subset_univ F, hF⟩
    exact (all_rows_zero j).1 ⟨F, hmem⟩
  · unfold deletion
    apply sum_eq_zero
    intro i hi
    have hi' : i ∉ F := (mem_sdiff.mp hi).2
    have hb : (insert i F).card ≠ 3 := by
      rw [card_insert_of_notMem hi']
      omega
    simp [coeff, hb]

private theorem is_residue (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (j : I) :
    (fun F => embed e (coeff j F)) ∈ weightedCircuitResidues core (id : V → V) := by
  rw [SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff _
    (by decide : 3 < Fintype.card V) hole_size sparse core_ground core_base]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F bad
    simp [coeff, bad]
  · intro F omitted
    have hF : F ∈ holes := omitted
    simp [coeff, hF]
  · intro F
    unfold weightedBoundary
    simp only [id_weight, one_nsmul, ← map_zsmul, ← map_sum]
    change embed e (deletion j F) = 0
    rw [all_deletion_zero, map_zero]
  · intro F hF
    unfold circuitReadout
    simp only [empty_union, ← map_zsmul, ← map_sum]
    change embed e (extension j F) = 0
    have hmem : F ∈ upper := mem_powersetCard.mpr ⟨subset_univ F, hF⟩
    rw [(all_rows_zero j).2 ⟨F,hmem⟩, map_zero]

private abbrev R := weightedCircuitResidues core (id : V → V)

private def basisResidue (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (i : I) : R :=
  ⟨_, is_residue e i⟩

private theorem killed (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (i : I) :
    (3 : ℤ) • basisResidue e i = 0 := by
  apply Subtype.ext
  funext F
  exact (Submodule.mem_torsionBy_iff _ _).mp (e.symm (coeff i F)).prop

private def familyResidue (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (u : I → ZMod 3) : R :=
  ∑ i, ((u i).val : ℤ) • basisResidue e i

private theorem family_killed (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (u : I → ZMod 3) :
    (3 : ℤ) • familyResidue e u = 0 := by
  rw [familyResidue, smul_sum]
  apply sum_eq_zero
  intro i _
  rw [smul_comm (3 : ℤ), killed, smul_zero]

private theorem family_read (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) (u : I → ZMod 3) (j : I) :
    (familyResidue e u).val (readSite j) = embed e (u j) := by
  let f := (LinearMap.proj (readSite j)).comp R.subtype
  change f (familyResidue e u) = _
  rw [familyResidue, map_sum, sum_eq_single_of_mem j (mem_univ j)]
  · rw [map_zsmul]
    change ((u j).val : ℤ) • embed e (coeff j (readSite j)) = _
    rw [coordinates_identity, ite_eq_left rfl, ← map_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  · intro i _ hi
    rw [map_zsmul]
    change ((u i).val : ℤ) • embed e (coeff i (readSite j)) = 0
    rw [coordinates_identity, ite_eq_right hi.symm, map_zero, smul_zero]

private theorem family_injective (e : ResidueTorsion 3 ≃ₗ[ℤ] ZMod 3) :
    Function.Injective (familyResidue e) := by
  intro u v h
  funext j
  have hh := congrArg (fun a : R => a.val (readSite j)) h
  rw [family_read, family_read] at hh
  apply e.symm.injective
  exact Subtype.ext hh

private abbrev componentThree := {t : ZMod 9 // (3 : ℤ) • t = 0}

private theorem no_residue_equiv :
    ¬ Nonempty (R ≃ₗ[ℤ] (Fin 9 → ZMod 9)) := by
  rintro ⟨comparison⟩
  obtain ⟨e⟩ := residueTorsion_equiv_zmod 3 (by decide)
  let lift (u : I → ZMod 3) (i : Fin 9) : componentThree :=
    ⟨comparison (familyResidue e u) i, by
      have h : (3 : ℤ) • comparison (familyResidue e u) = 0 := by
        rw [← map_zsmul, family_killed, map_zero]
      exact congrFun h i⟩
  have hle := Fintype.card_le_of_injective lift (fun u v h =>
    family_injective e (comparison.injective (funext fun i => congrArg Subtype.val (congrFun h i))))
  have hcard : Fintype.card componentThree = 3 := by decide
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, hcard] at hle
  omega

private theorem no_lifting_equiv :
    ¬ Nonempty ((JointSaturatedImage (core.comap (id : V → V)) ⧸
      JointImageInSaturation (core.comap (id : V → V))) ≃ₗ[ℤ] (Fin 9 → ZMod 9)) := by
  rintro ⟨e⟩
  have hn (i : V) : core.IsNonloop i := by
    rw [← Matroid.indep_singleton, ← Finset.coe_singleton,
      SparsePavingCircuitCoordinates.indep_iff_card_and_allowed (by decide) hole_size sparse core_base]
    refine ⟨by simp, ?_⟩
    intro h
    have hsize := hole_size {i} h
    simp at hsize
  obtain ⟨comparison, _⟩ := parallel_lifting_obstruction Function.surjective_id (fun {_ _} h => h) hn
  exact no_residue_equiv ⟨comparison.symm.trans e⟩



/-- Independent cyclic-factor replacement for the rank-three affine lines. -/
def claim : Prop :=
  ∀ S : Matroid (Fin 9),
    (∀ B : Finset (Fin 9), S.IsBase (B : Set (Fin 9)) ↔ B.card = 3 ∧ B ∉ holes) →
    Nonempty ((JointSaturatedImage (S.comap (id : Fin 9 → Fin 9)) ⧸
      JointImageInSaturation (S.comap (id : Fin 9 → Fin 9))) ≃ₗ[ℤ] (Fin 9 → ZMod 9))

/-- The twelve affine lines give a rank-three counterexample. -/
theorem result : ¬ claim :=
  fun predicted => no_lifting_equiv (predicted core core_base)

end D5.S3.Combinatorics.Matroids.AffinePlaneOmissionRefutation
