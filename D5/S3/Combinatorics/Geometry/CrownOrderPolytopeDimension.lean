/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Affine.AddTorsorBases, mathlib/module/Mathlib.LinearAlgebra.Dimension.Constructions]
   utility: none
   digest: Crown face dimension equals its number of quotient blocks minus two. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCCP
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytope

private abbrev FreeBlock {n : ℕ} (P : CrownConnectedCompatiblePartition n) :=
  {C : Quotient P.toSetoid // C ≠ crownPartitionBottomBlock P ∧
    C ≠ crownPartitionTopBlock P}

open Classical in
private noncomputable def freeVariation {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    (FreeBlock P → ℝ) →ₗ[ℝ] (Fin (2 * n) → ℝ) where
  toFun v i :=
    if h : Quotient.mk'' (CrownAugmentedVertex.vertex i) = crownPartitionBottomBlock P ∨
        Quotient.mk'' (CrownAugmentedVertex.vertex i) = crownPartitionTopBlock P then 0
    else v ⟨Quotient.mk'' (CrownAugmentedVertex.vertex i),
      ⟨fun hb => h (Or.inl hb), fun ht => h (Or.inr ht)⟩⟩
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    by_cases h : Quotient.mk'' (CrownAugmentedVertex.vertex i) =
        crownPartitionBottomBlock P ∨ Quotient.mk'' (CrownAugmentedVertex.vertex i) =
        crownPartitionTopBlock P <;> simp [h]
  map_smul' r v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : Quotient.mk'' (CrownAugmentedVertex.vertex i) =
        crownPartitionBottomBlock P ∨ Quotient.mk'' (CrownAugmentedVertex.vertex i) =
        crownPartitionTopBlock P <;> simp [h]

private noncomputable def partitionPoint {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (v : FreeBlock P → ℝ) : Fin (2 * n) → ℝ :=
  crownPartitionRankPoint P + freeVariation P v

private theorem partitionFace_point_parameterized {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
    {x : Fin (2 * n) → ℝ} (hx : x ∈ (crownPartitionFace P).1) :
    ∃ v : FreeBlock P → ℝ, partitionPoint P v = x := by
  have crownPartitionBlockRank_injective {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) :
      Function.Injective (crownPartitionBlockRank P) := by
    intro C D h
    letI := P.blockPartialOrder
    unfold crownPartitionBlockRank at h
    have hCD : toLinearExtension C = toLinearExtension D :=
      OrderIso.injective _ (Fin.ext h)
    exact hCD
  have crownPartition_bottom_le {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid (crownPartitionBottomBlock P) C := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    exact ⟨.bottom, v, rfl, rfl, by simp [crownAugmentedLE]⟩
  have crownPartitionBlockRank_mono {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      {C D : Quotient P.toSetoid} (hCD : crownPartitionBlockLE P.toSetoid C D) :
      crownPartitionBlockRank P C ≤ crownPartitionBlockRank P D := by
    letI := P.blockPartialOrder
    letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
    letI : Fintype (LinearExtension (Quotient P.toSetoid)) :=
        Fintype.ofEquiv (Quotient P.toSetoid)
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
    have hlinear : toLinearExtension C ≤ toLinearExtension D := toLinearExtension.monotone hCD
    have hfin : e.symm (toLinearExtension C) ≤ e.symm (toLinearExtension D) :=
      e.symm.monotone hlinear
    change (e.symm (toLinearExtension C)).val ≤ (e.symm (toLinearExtension D)).val
    exact hfin
  have crownPartition_rank_denominator_pos {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
      (0 : ℝ) < (crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
        crownPartitionBlockRank P (crownPartitionBottomBlock P) := by
    have hle := crownPartitionBlockRank_mono P
      (crownPartition_bottom_le P (crownPartitionTopBlock P))
    have hne : crownPartitionBlockRank P (crownPartitionBottomBlock P) ≠
        crownPartitionBlockRank P (crownPartitionTopBlock P) :=
      fun h => hendpoints (crownPartitionBlockRank_injective P h)
    have hlt := lt_of_le_of_ne hle hne
    have hltR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) <
        crownPartitionBlockRank P (crownPartitionTopBlock P) := by
      exact_mod_cast hlt
    linarith
  have augmentedCoordinate_crownPartitionRankPoint {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        ((crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) := by
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    cases u with
    | bottom => simp [augmentedCoordinate, crownPartitionBottomBlock]
    | vertex i => rfl
    | top =>
        simp only [augmentedCoordinate, crownPartitionTopBlock]
        exact (div_self hden).symm
  have augmentedCoordinate_crownPartitionRankPoint_eq_iff {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u v : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        augmentedCoordinate (crownPartitionRankPoint P) v ↔ P.toSetoid.r u v := by
    rw [augmentedCoordinate_crownPartitionRankPoint P hendpoints u,
      augmentedCoordinate_crownPartitionRankPoint P hendpoints v]
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    constructor
    · intro h
      have hnum : (crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P) =
          (crownPartitionBlockRank P (Quotient.mk'' v) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P) :=
        (div_left_inj' hden).mp h
      have hrank : crownPartitionBlockRank P (Quotient.mk'' u) =
          crownPartitionBlockRank P (Quotient.mk'' v) := by
        exact_mod_cast (sub_left_inj.mp hnum)
      exact Quotient.exact (crownPartitionBlockRank_injective P hrank)
    · intro huv
      exact congrArg (fun C =>
        ((crownPartitionBlockRank P C : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P))) (Quotient.sound huv)
  classical
  let r := crownPartitionRankPoint P
  let v : FreeBlock P → ℝ := fun C =>
    augmentedCoordinate x (Quotient.out C.1) -
      augmentedCoordinate r (Quotient.out C.1)
  have hxblocks := (mem_crownPartitionFaceSet_iff P x).1 hx |>.2
  have hrblocks (u w : CrownAugmentedVertex n) (huw : P.toSetoid.r u w) :
      augmentedCoordinate r u = augmentedCoordinate r w :=
    (augmentedCoordinate_crownPartitionRankPoint_eq_iff P hendpoints u w).2 huw
  refine ⟨v, funext fun i => ?_⟩
  let C : Quotient P.toSetoid := Quotient.mk'' (.vertex i)
  have hrep : P.toSetoid.r (.vertex i) (Quotient.out C) := by
    apply Quotient.exact
    exact (Quotient.out_eq C).symm
  by_cases h : C = crownPartitionBottomBlock P ∨ C = crownPartitionTopBlock P
  · rcases h with hb | ht
    · have heq : P.toSetoid.r (.vertex i) .bottom := Quotient.exact hb
      have hx0 : x i = 0 := by
        simpa [augmentedCoordinate] using hxblocks _ _ heq
      have hr0 : r i = 0 := by
        simpa [augmentedCoordinate] using hrblocks _ _ heq
      change r i + (if h' : C = crownPartitionBottomBlock P ∨
        C = crownPartitionTopBlock P then 0 else v ⟨C,
          ⟨fun hb' => h' (Or.inl hb'), fun ht' => h' (Or.inr ht')⟩⟩) = x i
      simp [hb, hx0, hr0]
    · have heq : P.toSetoid.r (.vertex i) .top := Quotient.exact ht
      have hx1 : x i = 1 := by
        simpa [augmentedCoordinate] using hxblocks _ _ heq
      have hr1 : r i = 1 := by
        simpa [augmentedCoordinate] using hrblocks _ _ heq
      change r i + (if h' : C = crownPartitionBottomBlock P ∨
        C = crownPartitionTopBlock P then 0 else v ⟨C,
          ⟨fun hb' => h' (Or.inl hb'), fun ht' => h' (Or.inr ht')⟩⟩) = x i
      simp [ht, hx1, hr1]
  · have hfree : C ≠ crownPartitionBottomBlock P ∧
        C ≠ crownPartitionTopBlock P := ⟨fun hb => h (Or.inl hb), fun ht => h (Or.inr ht)⟩
    have hv' : v ⟨C, hfree⟩ = x i - r i := by
      simp only [v]
      rw [← hxblocks _ _ hrep, ← hrblocks _ _ hrep]
      rfl
    change r i + (if h' : C = crownPartitionBottomBlock P ∨
      C = crownPartitionTopBlock P then 0 else v ⟨C,
        ⟨fun hb' => h' (Or.inl hb'), fun ht' => h' (Or.inr ht')⟩⟩) = x i
    simp only [dif_neg h]
    convert congrArg (fun t : ℝ => r i + t) hv' using 1
    ring
private def strictParameters {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Set (FreeBlock P → ℝ) :=
  {v | ∀ u w : CrownAugmentedVertex n, crownAugmentedLE u w →
    Quotient.mk'' u ≠ (Quotient.mk'' w : Quotient P.toSetoid) →
      augmentedCoordinate (partitionPoint P v) u <
        augmentedCoordinate (partitionPoint P v) w}

private noncomputable def partitionAffineMap {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    (FreeBlock P → ℝ) →ᵃ[ℝ] (Fin (2 * n) → ℝ) where
  toFun := partitionPoint P
  linear := freeVariation P
  map_vadd' v w := by
    simp only [vadd_eq_add, partitionPoint, map_add]
    abel

/-- The direction of the genuine affine span of a nonempty CCP face is exactly the
    space of independent variations on its nonendpoint quotient blocks. -/
private theorem crownPartitionFace_affineSpan_direction {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
    (affineSpan ℝ (crownPartitionFace P).1).direction =
      LinearMap.range (freeVariation P) := by
  classical
  have augmentedCoordinate_mono {n : ℕ} {x : Fin (2 * n) → ℝ}
      (hx : x ∈ crownOrderPolytope n) {u v : CrownAugmentedVertex n}
      (huv : crownAugmentedLE u v) : augmentedCoordinate x u ≤ augmentedCoordinate x v := by
    cases u with
    | bottom =>
        cases v with
        | bottom => simp [augmentedCoordinate]
        | vertex j => exact (hx.1 j).1
        | top => norm_num [augmentedCoordinate]
    | top =>
        cases v with
        | bottom => simp [crownAugmentedLE] at huv
        | vertex j => simp [crownAugmentedLE] at huv
        | top => simp [augmentedCoordinate]
    | vertex i =>
        cases v with
        | bottom => simp [crownAugmentedLE] at huv
        | top => exact (hx.1 i).2
        | vertex j =>
            rcases huv with hij | hij
            · simpa [hij]
            · exact hx.2 i j hij
  have crownPartition_bottom_le {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid (crownPartitionBottomBlock P) C := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    exact ⟨.bottom, v, rfl, rfl, by simp [crownAugmentedLE]⟩
  have crownPartition_le_top {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid C (crownPartitionTopBlock P) := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    refine ⟨v, .top, rfl, rfl, ?_⟩
    cases v <;> simp [crownAugmentedLE]
  have crownPartitionBlockRank_mono {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      {C D : Quotient P.toSetoid} (hCD : crownPartitionBlockLE P.toSetoid C D) :
      crownPartitionBlockRank P C ≤ crownPartitionBlockRank P D := by
    letI := P.blockPartialOrder
    letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
    letI : Fintype (LinearExtension (Quotient P.toSetoid)) :=
        Fintype.ofEquiv (Quotient P.toSetoid)
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
    have hlinear : toLinearExtension C ≤ toLinearExtension D := toLinearExtension.monotone hCD
    have hfin : e.symm (toLinearExtension C) ≤ e.symm (toLinearExtension D) :=
      e.symm.monotone hlinear
    change (e.symm (toLinearExtension C)).val ≤ (e.symm (toLinearExtension D)).val
    exact hfin
  have crownPartitionBlockRank_injective {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) :
      Function.Injective (crownPartitionBlockRank P) := by
    intro C D h
    letI := P.blockPartialOrder
    unfold crownPartitionBlockRank at h
    have hCD : toLinearExtension C = toLinearExtension D :=
      OrderIso.injective _ (Fin.ext h)
    exact hCD
  have crownPartition_rank_denominator_pos {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
      (0 : ℝ) < (crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
        crownPartitionBlockRank P (crownPartitionBottomBlock P) := by
    have hle := crownPartitionBlockRank_mono P
      (crownPartition_bottom_le P (crownPartitionTopBlock P))
    have hne : crownPartitionBlockRank P (crownPartitionBottomBlock P) ≠
        crownPartitionBlockRank P (crownPartitionTopBlock P) :=
      fun h => hendpoints (crownPartitionBlockRank_injective P h)
    have hlt := lt_of_le_of_ne hle hne
    have hltR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) <
        crownPartitionBlockRank P (crownPartitionTopBlock P) := by
      exact_mod_cast hlt
    linarith
  have crownPartition_block_le_of_augmentedLE {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) {u v : CrownAugmentedVertex n}
      (huv : crownAugmentedLE u v) :
      crownPartitionBlockLE P.toSetoid (Quotient.mk'' u) (Quotient.mk'' v) := by
    exact
      Relation.ReflTransGen.single ⟨u, v, rfl, rfl, huv⟩
  have crownPartitionRankPoint_mem {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
      crownPartitionRankPoint P ∈ crownOrderPolytope n := by
    have hden := crownPartition_rank_denominator_pos P hendpoints
    constructor
    · intro i
      have hbottom := crownPartitionBlockRank_mono P
        (crownPartition_bottom_le P (Quotient.mk'' (.vertex i)))
      have htop := crownPartitionBlockRank_mono P
        (crownPartition_le_top P (Quotient.mk'' (.vertex i)))
      have hbottomR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) ≤
          crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) := by
        exact_mod_cast hbottom
      have htopR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
          crownPartitionBlockRank P (crownPartitionTopBlock P) := by
        exact_mod_cast htop
      constructor
      · apply div_nonneg
        · exact sub_nonneg.mpr hbottomR
        · exact le_of_lt hden
      · apply (div_le_one hden).2
        linarith
    · intro i j hij
      have hmono := crownPartitionBlockRank_mono P
        (crownPartition_block_le_of_augmentedLE P
          (u := CrownAugmentedVertex.vertex i) (v := CrownAugmentedVertex.vertex j) (Or.inr hij))
      have hmonoR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
          crownPartitionBlockRank P (Quotient.mk'' (.vertex j)) := by
        exact_mod_cast hmono
      apply (div_le_div_iff_of_pos_right hden).2
      linarith
  have augmentedCoordinate_crownPartitionRankPoint {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        ((crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) := by
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    cases u with
    | bottom => simp [augmentedCoordinate, crownPartitionBottomBlock]
    | vertex i => rfl
    | top =>
        simp only [augmentedCoordinate, crownPartitionTopBlock]
        exact (div_self hden).symm
  have augmentedCoordinate_crownPartitionRankPoint_eq_iff {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u v : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        augmentedCoordinate (crownPartitionRankPoint P) v ↔ P.toSetoid.r u v := by
    rw [augmentedCoordinate_crownPartitionRankPoint P hendpoints u,
      augmentedCoordinate_crownPartitionRankPoint P hendpoints v]
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    constructor
    · intro h
      have hnum : (crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P) =
          (crownPartitionBlockRank P (Quotient.mk'' v) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P) :=
        (div_left_inj' hden).mp h
      have hrank : crownPartitionBlockRank P (Quotient.mk'' u) =
          crownPartitionBlockRank P (Quotient.mk'' v) := by
        exact_mod_cast (sub_left_inj.mp hnum)
      exact Quotient.exact (crownPartitionBlockRank_injective P hrank)
    · intro huv
      exact congrArg (fun C =>
        ((crownPartitionBlockRank P C : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P))) (Quotient.sound huv)
  have strictParameters_isOpen {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
      IsOpen (strictParameters P) := by
    classical
    have hcont : Continuous (partitionPoint P) := by
      exact continuous_const.add (freeVariation P).continuous_of_finiteDimensional
    have hcoord (u : CrownAugmentedVertex n) :
        Continuous (fun v : FreeBlock P → ℝ => augmentedCoordinate (partitionPoint P v) u) := by
      cases u with
      | bottom => exact continuous_const
      | top => exact continuous_const
      | vertex i => exact (continuous_apply i).comp hcont
    change IsOpen {v | ∀ u w, crownAugmentedLE u w →
      Quotient.mk'' u ≠ (Quotient.mk'' w : Quotient P.toSetoid) →
        augmentedCoordinate (partitionPoint P v) u <
          augmentedCoordinate (partitionPoint P v) w}
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro u
    apply isOpen_iInter_of_finite
    intro w
    by_cases h : crownAugmentedLE u w ∧
        Quotient.mk'' u ≠ (Quotient.mk'' w : Quotient P.toSetoid)
    · simpa [h, and_imp] using isOpen_lt (hcoord u) (hcoord w)
    · have h' : ¬crownAugmentedLE u w ∨
          ¬(Quotient.mk'' u ≠ (Quotient.mk'' w : Quotient P.toSetoid)) := not_and_or.mp h
      rcases h' with horder | hblocks
      · simp [horder]
      · simp [hblocks]
  have partitionPoint_coordinate {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (v : FreeBlock P → ℝ) (u : CrownAugmentedVertex n) :
      augmentedCoordinate (partitionPoint P v) u =
        ((crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) +
        (if h : Quotient.mk'' u = crownPartitionBottomBlock P ∨
            Quotient.mk'' u = crownPartitionTopBlock P then 0
         else v ⟨Quotient.mk'' u, ⟨fun hb => h (Or.inl hb),
           fun ht => h (Or.inr ht)⟩⟩) := by
    rw [← augmentedCoordinate_crownPartitionRankPoint P hendpoints u]
    cases u with
    | bottom => simp [augmentedCoordinate, crownPartitionBottomBlock]
    | top => simp [augmentedCoordinate, crownPartitionTopBlock]
    | vertex i => simp [partitionPoint, augmentedCoordinate, freeVariation, Pi.add_apply]
  have strictParameters_mem_face {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      {v : FreeBlock P → ℝ} (hv : v ∈ strictParameters P) :
      partitionPoint P v ∈ (crownPartitionFace P).1 := by
    classical
    have hblock {u w : CrownAugmentedVertex n} (huw : P.toSetoid.r u w) :
        augmentedCoordinate (partitionPoint P v) u =
          augmentedCoordinate (partitionPoint P v) w := by
      rw [partitionPoint_coordinate P hendpoints v u,
        partitionPoint_coordinate P hendpoints v w]
      have heq : Quotient.mk'' u = Quotient.mk'' w := Quotient.sound huw
      simp only [heq]
    apply (mem_crownPartitionFaceSet_iff P _).2
    have hmono (u w : CrownAugmentedVertex n) (huw : crownAugmentedLE u w) :
        augmentedCoordinate (partitionPoint P v) u ≤
          augmentedCoordinate (partitionPoint P v) w := by
      by_cases h : Quotient.mk'' u = (Quotient.mk'' w : Quotient P.toSetoid)
      · exact le_of_eq (hblock (Quotient.exact h))
      · exact le_of_lt (hv u w huw h)
    refine ⟨?_, fun u w huw => hblock huw⟩
    constructor
    · intro i
      exact ⟨by simpa [augmentedCoordinate] using hmono .bottom (.vertex i) (by trivial),
        by simpa [augmentedCoordinate] using hmono (.vertex i) .top (by trivial)⟩
    · intro i j hij
      exact hmono (.vertex i) (.vertex j) (Or.inr hij)
  classical
  let A := partitionAffineMap P
  have hzero : (0 : FreeBlock P → ℝ) ∈ strictParameters P := by
    intro u w huw hblocks
    have hzeroPoint : partitionPoint P (0 : FreeBlock P → ℝ) =
        crownPartitionRankPoint P := by simp [partitionPoint]
    rw [hzeroPoint]
    have hle := augmentedCoordinate_mono (crownPartitionRankPoint_mem P hendpoints) huw
    exact lt_of_le_of_ne hle (fun he => hblocks (Quotient.sound
      ((augmentedCoordinate_crownPartitionRankPoint_eq_iff P hendpoints u w).1 he)))
  have hopen : affineSpan ℝ (strictParameters P) = ⊤ :=
    (strictParameters_isOpen P).affineSpan_eq_top ⟨0, hzero⟩
  have hspan : affineSpan ℝ (crownPartitionFace P).1 =
      (⊤ : AffineSubspace ℝ (FreeBlock P → ℝ)).map A := by
    apply le_antisymm
    · rw [← AffineSubspace.span_univ, AffineSubspace.map_span]
      apply affineSpan_mono
      intro x hx
      obtain ⟨v, rfl⟩ := partitionFace_point_parameterized P hendpoints hx
      exact ⟨v, Set.mem_univ _, rfl⟩
    · rw [← hopen, AffineSubspace.map_span]
      apply affineSpan_mono
      rintro x ⟨v, hv, rfl⟩
      exact strictParameters_mem_face P hendpoints hv
  rw [hspan, AffineSubspace.map_direction, AffineSubspace.direction_top,
    Submodule.map_top]
  rfl
open Classical in
/-- The affine dimension of a nonempty actual CCP face equals its number of blocks minus two. -/
theorem crownPartitionFace_finrank_direction {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
    Module.finrank ℝ (affineSpan ℝ (crownPartitionFace P).1).direction =
      Fintype.card (Quotient P.toSetoid) - 2 := by
  have freeVariation_injective {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      : Function.Injective (freeVariation P) := by
    classical
    intro v w hv
    funext C
    obtain ⟨u, hu⟩ := Quot.exists_rep C.1
    have hcoord : ∀ z : FreeBlock P → ℝ,
        augmentedCoordinate (freeVariation P z) u = z C := by
      intro z
      cases u with
      | bottom => exact False.elim (C.2.1 (hu.symm.trans rfl))
      | top => exact False.elim (C.2.2 (hu.symm.trans rfl))
      | vertex i =>
          simp only [augmentedCoordinate, freeVariation, LinearMap.coe_mk, AddHom.coe_mk]
          split_ifs with h
          · exact False.elim (h.elim (fun hb => C.2.1 (hu.symm.trans hb))
              (fun ht => C.2.2 (hu.symm.trans ht)))
          · congr 1
            exact Subtype.ext hu
    calc
      v C = augmentedCoordinate (freeVariation P v) u := (hcoord v).symm
      _ = augmentedCoordinate (freeVariation P w) u := by rw [hv]
      _ = w C := hcoord w
  classical
  have hfin : Module.finrank ℝ (affineSpan ℝ (crownPartitionFace P).1).direction =
      Fintype.card (FreeBlock P) := by
    rw [crownPartitionFace_affineSpan_direction P hendpoints,
      LinearMap.finrank_range_of_inj (freeVariation_injective P)]
    exact Module.finrank_fintype_fun_eq_card ℝ
  rw [hfin, Fintype.card_subtype]
  have heq : ({C : Quotient P.toSetoid |
      C ≠ crownPartitionBottomBlock P ∧ C ≠ crownPartitionTopBlock P} : Finset _) =
      ({crownPartitionBottomBlock P, crownPartitionTopBlock P} : Finset _)ᶜ := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [heq, Finset.card_compl]
  simp [hendpoints]
open Classical in
/-- Every nonempty actual exposed face has affine dimension equal to the number of its
    recovered tight components minus the two distinct endpoint components. -/
theorem crownExposedFace_finrank_direction {n : ℕ} (F : CrownExposedFace n)
    (hF : F.1.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ F.1).direction =
      Fintype.card (Quotient (crownFacePartition F).toSetoid) - 2 := by
  have crownPartition_bottom_le {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid (crownPartitionBottomBlock P) C := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    exact ⟨.bottom, v, rfl, rfl, by simp [crownAugmentedLE]⟩
  have crownPartition_le_top {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid C (crownPartitionTopBlock P) := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    refine ⟨v, .top, rfl, rfl, ?_⟩
    cases v <;> simp [crownAugmentedLE]
  have crownPartitionBlockRank_mono {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      {C D : Quotient P.toSetoid} (hCD : crownPartitionBlockLE P.toSetoid C D) :
      crownPartitionBlockRank P C ≤ crownPartitionBlockRank P D := by
    letI := P.blockPartialOrder
    letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
    letI : Fintype (LinearExtension (Quotient P.toSetoid)) :=
        Fintype.ofEquiv (Quotient P.toSetoid)
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
    have hlinear : toLinearExtension C ≤ toLinearExtension D := toLinearExtension.monotone hCD
    have hfin : e.symm (toLinearExtension C) ≤ e.symm (toLinearExtension D) :=
      e.symm.monotone hlinear
    change (e.symm (toLinearExtension C)).val ≤ (e.symm (toLinearExtension D)).val
    exact hfin
  have crownPartitionBlockRank_injective {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) :
      Function.Injective (crownPartitionBlockRank P) := by
    intro C D h
    letI := P.blockPartialOrder
    unfold crownPartitionBlockRank at h
    have hCD : toLinearExtension C = toLinearExtension D :=
      OrderIso.injective _ (Fin.ext h)
    exact hCD
  have crownPartition_rank_denominator_pos {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
      (0 : ℝ) < (crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
        crownPartitionBlockRank P (crownPartitionBottomBlock P) := by
    have hle := crownPartitionBlockRank_mono P
      (crownPartition_bottom_le P (crownPartitionTopBlock P))
    have hne : crownPartitionBlockRank P (crownPartitionBottomBlock P) ≠
        crownPartitionBlockRank P (crownPartitionTopBlock P) :=
      fun h => hendpoints (crownPartitionBlockRank_injective P h)
    have hlt := lt_of_le_of_ne hle hne
    have hltR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) <
        crownPartitionBlockRank P (crownPartitionTopBlock P) := by
      exact_mod_cast hlt
    linarith
  have crownPartition_block_le_of_augmentedLE {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) {u v : CrownAugmentedVertex n}
      (huv : crownAugmentedLE u v) :
      crownPartitionBlockLE P.toSetoid (Quotient.mk'' u) (Quotient.mk'' v) := by
    exact
      Relation.ReflTransGen.single ⟨u, v, rfl, rfl, huv⟩
  have crownPartitionRankPoint_mem {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
      crownPartitionRankPoint P ∈ crownOrderPolytope n := by
    have hden := crownPartition_rank_denominator_pos P hendpoints
    constructor
    · intro i
      have hbottom := crownPartitionBlockRank_mono P
        (crownPartition_bottom_le P (Quotient.mk'' (.vertex i)))
      have htop := crownPartitionBlockRank_mono P
        (crownPartition_le_top P (Quotient.mk'' (.vertex i)))
      have hbottomR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) ≤
          crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) := by
        exact_mod_cast hbottom
      have htopR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
          crownPartitionBlockRank P (crownPartitionTopBlock P) := by
        exact_mod_cast htop
      constructor
      · apply div_nonneg
        · exact sub_nonneg.mpr hbottomR
        · exact le_of_lt hden
      · apply (div_le_one hden).2
        linarith
    · intro i j hij
      have hmono := crownPartitionBlockRank_mono P
        (crownPartition_block_le_of_augmentedLE P
          (u := CrownAugmentedVertex.vertex i) (v := CrownAugmentedVertex.vertex j) (Or.inr hij))
      have hmonoR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
          crownPartitionBlockRank P (Quotient.mk'' (.vertex j)) := by
        exact_mod_cast hmono
      apply (div_le_div_iff_of_pos_right hden).2
      linarith
  have augmentedCoordinate_crownPartitionRankPoint {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        ((crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) := by
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    cases u with
    | bottom => simp [augmentedCoordinate, crownPartitionBottomBlock]
    | vertex i => rfl
    | top =>
        simp only [augmentedCoordinate, crownPartitionTopBlock]
        exact (div_self hden).symm
  have augmentedCoordinate_crownPartitionRankPoint_eq_iff {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
      (u v : CrownAugmentedVertex n) :
      augmentedCoordinate (crownPartitionRankPoint P) u =
        augmentedCoordinate (crownPartitionRankPoint P) v ↔ P.toSetoid.r u v := by
    rw [augmentedCoordinate_crownPartitionRankPoint P hendpoints u,
      augmentedCoordinate_crownPartitionRankPoint P hendpoints v]
    have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
    constructor
    · intro h
      have hnum : (crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P) =
          (crownPartitionBlockRank P (Quotient.mk'' v) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P) :=
        (div_left_inj' hden).mp h
      have hrank : crownPartitionBlockRank P (Quotient.mk'' u) =
          crownPartitionBlockRank P (Quotient.mk'' v) := by
        exact_mod_cast (sub_left_inj.mp hnum)
      exact Quotient.exact (crownPartitionBlockRank_injective P hrank)
    · intro huv
      exact congrArg (fun C =>
        ((crownPartitionBlockRank P C : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
          ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
            crownPartitionBlockRank P (crownPartitionBottomBlock P))) (Quotient.sound huv)
  have crownPartition_all_related_of_endpoints_eq {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P = crownPartitionTopBlock P)
      (u v : CrownAugmentedVertex n) : P.toSetoid.r u v := by
    apply Quotient.exact
    apply P.compatible
    · exact (crownPartition_le_top P (Quotient.mk'' u)).trans <|
        hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' v)
    · exact (crownPartition_le_top P (Quotient.mk'' v)).trans <|
        hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' u)
  have crownPartitionFace_nonempty_iff {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
      (crownPartitionFace P).1.Nonempty ↔
        crownPartitionBottomBlock P ≠ crownPartitionTopBlock P := by
    constructor
    · rintro ⟨x, hx⟩ hendpoints
      have hall := crownPartition_all_related_of_endpoints_eq P hendpoints
        CrownAugmentedVertex.bottom CrownAugmentedVertex.top
      have heq := (mem_crownPartitionFaceSet_iff P x).1 hx |>.2 _ _ hall
      norm_num [augmentedCoordinate] at heq
    · intro hendpoints
      refine ⟨crownPartitionRankPoint P, ?_⟩
      exact (mem_crownPartitionFaceSet_iff P _).2
        ⟨crownPartitionRankPoint_mem P hendpoints,
          fun u v huv => (augmentedCoordinate_crownPartitionRankPoint_eq_iff
            P hendpoints u v).2 huv⟩
  have hendpoints : crownPartitionBottomBlock (crownFacePartition F) ≠
      crownPartitionTopBlock (crownFacePartition F) :=
    (crownPartitionFace_nonempty_iff (crownFacePartition F)).1
      (by simpa only [crownPartitionFace_crownFacePartition] using hF)
  have hdim := crownPartitionFace_finrank_direction (crownFacePartition F) hendpoints
  rw [crownPartitionFace_crownFacePartition F] at hdim
  exact hdim
end D5.S3.Combinatorics.Geometry.CrownOrderPolytope
