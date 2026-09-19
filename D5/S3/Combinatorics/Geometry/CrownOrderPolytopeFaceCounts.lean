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
