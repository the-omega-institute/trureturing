/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual geometric crown face counts follow from the odd-profile enumeration. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeSelectionCounts
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeTwoExceptions
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope
open scoped BigOperators

/-- The number of actual nonempty exposed faces of affine dimension `d`. -/
noncomputable def crownGeometricFaceCount (n d : ℕ) : ℕ :=
  Nat.card {F : CrownExposedFace n // F.val.Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ F.val).direction = d}

/-- The geometric face-count formula for every `n ≥ 2` and every nonnegative
    dimension, with the two exceptional vertices and the one-block edge included.
    The formula is derived from the actual face/CCP correspondence and actual
    selected-block counts, without a face-count formula as a premise. -/
theorem crownGeometricFaceCount_eq (n d : ℕ) (hn : 2 ≤ n) :
    crownGeometricFaceCount n d = (if d = 0 then 2 else 0) +
      (if d = 1 then 1 else 0) +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 2 (2 * n)},
          ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (i.val / 2)},
            ((2 * n * Nat.choose i.val (2 * m.val) *
              Nat.choose (n + m.val - 1) (i.val - 1)) *
                (if d ≤ i.val then Nat.choose (2 * m.val) (i.val - d) else 0)) / i.val := by
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
  classical
  letI : NeZero (2 * n) := ⟨by omega⟩
  let A := {P : CrownConnectedCompatiblePartition n // Nat.card (Quotient P.toSetoid) = d + 2}
  let B := {F : CrownExposedFace n // F.val.Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ F.val).direction = d}
  have hsep (P : A) : crownPartitionBottomBlock P.val ≠ crownPartitionTopBlock P.val := by
    intro hbt
    have hall (u : CrownAugmentedVertex n) : P.val.toSetoid.r .bottom u := by
      apply Quotient.exact
      apply P.val.compatible
      · exact Relation.ReflTransGen.single
          ⟨.bottom, u, rfl, rfl, by cases u <;> trivial⟩
      · exact Relation.ReflTransGen.single
          ⟨u, .top, rfl, hbt.symm, by cases u <;> trivial⟩
    have hs : Function.Surjective
        (fun _ : Unit => (Quotient.mk'' .bottom : Quotient P.val.toSetoid)) := by
      intro C
      obtain ⟨u, rfl⟩ := Quotient.exists_rep C
      exact ⟨(), Quotient.sound (hall u)⟩
    have hc := Nat.card_le_card_of_surjective _ hs
    have hu : Nat.card Unit = 1 := by simp
    rw [hu, P.property] at hc
    omega
  let f : A → B := fun P =>
    ⟨crownPartitionFace P.val, (crownPartitionFace_nonempty_iff P.val).mpr (hsep P), by
      have h := crownPartitionFace_finrank_direction P.val (hsep P)
      rw [← Nat.card_eq_fintype_card, P.property] at h
      simpa using h⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro P Q h
      have hface : crownPartitionFace P.val = crownPartitionFace Q.val := congrArg Subtype.val h
      have hs : P.val.toSetoid = Q.val.toSetoid := by
        apply Setoid.ext
        intro u v
        rw [← crownPartitionFace_tightComponent_iff P.val u v,
          ← crownPartitionFace_tightComponent_iff Q.val u v, hface]
      have hext (R S : CrownConnectedCompatiblePartition n)
          (h : R.toSetoid = S.toSetoid) : R = S := by
        cases R
        cases S
        cases h
        rfl
      exact Subtype.ext (hext _ _ hs)
    · intro F
      let P := crownFacePartition F.val
      have hpface : crownPartitionFace P = F.val := crownPartitionFace_crownFacePartition F.val
      have hends : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P :=
        (crownPartitionFace_nonempty_iff P).mp (by rw [hpface]; exact F.property.1)
      let g : Bool → Quotient P.toSetoid := fun b =>
        if b then crownPartitionTopBlock P else crownPartitionBottomBlock P
      have hg : Function.Injective g := by
        intro b c h
        cases b <;> cases c <;> simp_all [g]
      have htwo : 2 ≤ Nat.card (Quotient P.toSetoid) := by
        simpa using Nat.card_le_card_of_injective g hg
      have hdim := crownExposedFace_finrank_direction F.val F.property.1
      rw [← Nat.card_eq_fintype_card, F.property.2] at hdim
      have hcard : Nat.card (Quotient P.toSetoid) = d + 2 := by
        change d = Nat.card (Quotient P.toSetoid) - 2 at hdim
        omega
      exact ⟨⟨P, hcard⟩, Subtype.ext hpface⟩
  have hfaces : crownGeometricFaceCount n d = Nat.card A :=
    (Nat.card_congr (Equiv.ofBijective f hbij)).symm
  have hpartitions : Nat.card A =
      Nat.card (CrownOddBlockSelectionOfCard n (d + 2)) + (if d = 0 then 2 else 0) := by
    by_cases hd : d = 0
    · subst d
      simpa [A] using (crownOddBlockMerge_two_card hn).2
    · have hk : 3 ≤ d + 2 := by omega
      have h := Nat.card_congr (Equiv.ofBijective
        (crownOddBlockMerge hn (by omega : 2 ≤ d + 2)) (crownOddBlockMerge_bijective hn hk))
      simpa [A, hd] using h.symm
  rw [hfaces, hpartitions, crownOddBlockSelection_card n d hn]
  omega
end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
