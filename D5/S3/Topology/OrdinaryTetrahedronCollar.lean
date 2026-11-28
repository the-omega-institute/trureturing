/- GID: D5/S3/Topology/OrdinaryTetrahedronCollar
   generality: I
   mirror-B: D5/B/S3/Topology/OrdinaryTetrahedronCollar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The tetrahedral lists compute both ordinary colour cuts. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.OrdinarySubdivisionMap
import D5.S3.Topology.TetrahedronCollar16

/-! Interpret the chamber certificate's two cuts on the actual ordinary subdivision. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TetrahedronCollar16

open D5.S3.Topology
open private asFinset mem_asFinset asFinset_nonempty cut₁ cut₂ boundedFace
  from D5.S3.Topology.TetrahedronCollar16
open private limit_of_shape shape₁ shape₂ shape₃ literalFace₁Embedding literalFace₂Embedding
  from D5.S3.Topology.TetrahedronCollar16

noncomputable section

/-- Recover the old colour in the ordered chamber. -/
def hasColour (c : Color) (a : Fin 4) : Bool :=
  a.val == low c || a.val == high c

private def flagFinset (l : List (List Nat)) : Finset (Finset (Fin 4)) :=
  (l.map (asFinset 4)).toFinset

private theorem mem_flagFinset {l : List (List Nat)} {s : Finset (Fin 4)} :
    s ∈ flagFinset l ↔ ∃ a ∈ l, asFinset 4 a = s := by
  simp only [flagFinset, List.mem_toFinset, List.mem_map]

private theorem flagFinset_nonempty (l : List (List Nat)) :
    (flagFinset l).Nonempty ↔ l ≠ [] := by
  cases l <;> simp [flagFinset]

private theorem cut_literalFace₁ (c : Color) (j : V₁) :
    OrdinarySubdivisionMap.cutFace (hasColour c) (literalFace₁ j) =
      asFinset 4 (cut₁ c j.val) := by
  let _ : DecidableEq Bool := Classical.decEq _
  ext a
  unfold OrdinarySubdivisionMap.cutFace
  rw [Finset.mem_filter]
  simp only [literalFace₁, mem_asFinset, cut₁, boundedFace, j.isLt, ↓reduceIte, face₁,
    List.mem_filter, hasColour]

private theorem cut₁_nonempty (c : Color) (j : V₁) :
    (asFinset 4 (cut₁ c j.val)).Nonempty ↔ cut₁ c j.val ≠ [] := by
  constructor
  · rintro ⟨a, ha⟩ h
    exact List.not_mem_nil (a := a.val) (h ▸ mem_asFinset.mp ha)
  · intro hn
    apply asFinset_nonempty hn
    intro x hx
    have hrow : x ∈ face₁ j := by
      have h := (List.mem_filter.mp hx).1
      simpa only [boundedFace, j.isLt, ↓reduceIte, face₁] using h
    exact limit_of_shape (shape₁ j) x hrow

private theorem cut_literalFace₂ (c : Color) (j : V₂) :
    OrdinarySubdivisionMap.cutFlag (hasColour c) (literalFace₂ j) =
      flagFinset (cut₂ c j.val) := by
  let _ : DecidableEq (Finset (Fin 4)) := Classical.decEq _
  ext s
  unfold OrdinarySubdivisionMap.cutFlag
  rw [Finset.mem_image]
  simp only [Finset.mem_filter, mem_flagFinset, cut₂, boundedFace, j.isLt, ↓reduceIte,
    List.mem_eraseDups, List.mem_filter, List.mem_map, bne_iff_ne]
  constructor
  · rintro ⟨q, ⟨hq, hn⟩, he⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp (show q ∈
      (asFinset 15 (face₂ j)).map literalFace₁Embedding from hq)
    change (OrdinarySubdivisionMap.cutFace (hasColour c) (literalFace₁ k)).Nonempty at hn
    change OrdinarySubdivisionMap.cutFace (hasColour c) (literalFace₁ k) = s at he
    rw [cut_literalFace₁] at hn he
    exact ⟨cut₁ c k.val, ⟨⟨k.val, mem_asFinset.mp hk, rfl⟩, (cut₁_nonempty c k).mp hn⟩, he⟩
  · rintro ⟨s, ⟨⟨k, hk, rfl⟩, hn⟩, he⟩
    let k' : V₁ := ⟨k, limit_of_shape (shape₂ j) k hk⟩
    refine ⟨literalFace₁ k', ⟨Finset.mem_map.mpr ⟨k', mem_asFinset.mpr hk, rfl⟩, ?_⟩, ?_⟩
    · rw [cut_literalFace₁]
      exact (cut₁_nonempty c k').mpr hn
    · exact (cut_literalFace₁ c k').trans he

/-- The certificate's collar test is the actual two-cut condition
in the ordinary third subdivision. -/
theorem literalFace₃_inCollar (c : Color) (i : V₃) :
    OrdinarySubdivisionMap.inTwoCutCollar (hasColour c) (literalFace₃ i) ↔ InCollar c i := by
  unfold OrdinarySubdivisionMap.inTwoCutCollar InCollar
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    let j' : V₂ := ⟨j, limit_of_shape (shape₃ i) j hj⟩
    have hcut := h (literalFace₂ j') (Finset.mem_map.mpr ⟨j', mem_asFinset.mpr hj, rfl⟩)
    rw [cut_literalFace₂, flagFinset_nonempty] at hcut
    exact bne_iff_ne.mpr hcut
  · intro h q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (show q ∈
      (asFinset 149 (face₃ i)).map literalFace₂Embedding from hq)
    change (OrdinarySubdivisionMap.cutFlag (hasColour c) (literalFace₂ j)).Nonempty
    rw [cut_literalFace₂, flagFinset_nonempty]
    exact bne_iff_ne.mp (h j.val (mem_asFinset.mp hj))

/-- The certificate's nested list represents the actual image of the
ordinary two-cut retraction, including the endpoints of its interval. -/
theorem literalFace₃_retract (c : Color) (i : V₃) :
    OrdinarySubdivisionMap.twoCutImage (hasColour c) (literalFace₃ i) =
      ((retract c i).map flagFinset).toFinset := by
  let _ : DecidableEq (Finset (Finset (Fin 4))) := Classical.decEq _
  ext s
  unfold OrdinarySubdivisionMap.twoCutImage
  rw [Finset.mem_image]
  simp only [List.mem_toFinset, retract, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (show q ∈
      (asFinset 149 (face₃ i)).map literalFace₂Embedding from hq)
    exact ⟨cut₂ c j.val, ⟨j.val, mem_asFinset.mp hj, rfl⟩, (cut_literalFace₂ c j).symm.trans h⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, h⟩
    let j' : V₂ := ⟨j, limit_of_shape (shape₃ i) j hj⟩
    exact ⟨literalFace₂ j', Finset.mem_map.mpr ⟨j', mem_asFinset.mpr hj, rfl⟩,
      (cut_literalFace₂ c j').trans h⟩

end

end TetrahedronCollar16
