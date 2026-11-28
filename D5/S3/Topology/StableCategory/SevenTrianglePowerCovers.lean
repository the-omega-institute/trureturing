/- GID: D5/S3/Topology/StableCategory/SevenTrianglePowerCovers
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/SevenTrianglePowerCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The one-step subdivided powers of a fixed disk have unbounded category. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import D5.S3.Topology.StableCategory.HalesJewettCategoricalCover
import D5.S3.Topology.StableCategory.ProductStableLower

/-! # Powers of the seven-triangle disk face poset -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Topology.StableCategory.SevenTrianglePowerCovers

open ConnectedCategoryGraft (HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open HalesJewettCategoricalCover (exists_no_categorical_cover hasCategoricalCover_one_iff)

open BarycentricGraphDistance (Face)
open D5.S3.Topology.ProductRigidCores (Factor P VertexLabel facets)
open ProductStableLower (id_contiguity_of_face_poset_contraction
  subdivision_not_contiguous_to_constant)

open private mem_generated from D5.S3.Topology.StableCategory.ProductRigidCores
open private subdivisionFace transport_lower_cover from
  D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer

private theorem facetCard : ∀ t ∈ facets, (t : Finset VertexLabel).card = 3 := by
  decide +kernel

private theorem faceCardBounds (a : Factor) : 0 < a.val.card ∧ a.val.card ≤ 3 := by
  obtain ⟨ha, t, ht, hat⟩ := mem_generated.mp a.property
  have hc := Finset.card_le_card hat
  rw [facetCard t ht] at hc
  exact ⟨ha.card_pos, hc⟩

private def faceRank : Factor →o Fin 3 where
  toFun a := ⟨a.val.card - 1, by
    have hcard := (faceCardBounds a).2
    omega⟩
  monotone' := fun a b hab => Fin.le_iff_val_le_val.mpr
    (Nat.sub_le_sub_right (Finset.card_le_card (show a.val ⊆ b.val from hab)) 1)

private abbrev FaceFlag :=
  {f : Fin 3 → Factor // Monotone f ∧ ∀ i, (f i).val.card = i.val + 1}

local instance : Finite Factor :=
  Finite.of_injective (fun f : Factor => f.val) Subtype.val_injective

local instance : Finite FaceFlag :=
  Finite.of_injective (fun f : FaceFlag => f.val) Subtype.val_injective

private def flagLetter (f : FaceFlag) : Fin 3 ↪o Factor :=
  OrderEmbedding.ofMapLEIff f.val (by
    intro i j
    refine ⟨?_, fun hij => f.property.1 hij⟩
    intro hij
    have h := Finset.card_le_card (show (f.val i).val ⊆ (f.val j).val from hij)
    rw [f.property.2 i, f.property.2 j] at h
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_add_le_add_right h))

private theorem rank_flagLetter (f : FaceFlag) (i : Fin 3) :
    faceRank (flagLetter f i) = i := by
  apply Fin.ext
  change (f.val i).val.card - 1 = i.val
  simp only [f.property.2 i, Nat.add_sub_cancel]

private theorem faceEqOfLeOfCardLe {a b : Factor} (hab : a ≤ b)
    (hcard : b.val.card ≤ a.val.card) : a = b :=
  Subtype.ext (Finset.eq_of_subset_of_card_le hab hcard)

private theorem chainLeOfCardLe (s : NonemptyFiniteChains Factor) {a b : Factor}
    (ha : a ∈ s.finset) (hb : b ∈ s.finset) (hcard : a.val.card ≤ b.val.card) : a ≤ b := by
  rcases s.comparable ⟨a, ha⟩ ⟨b, hb⟩ with hab | hba
  · exact hab
  · exact le_of_eq (faceEqOfLeOfCardLe hba hcard).symm

/-- Fill the ranks missing from a chain of nonempty faces. -/
private theorem extendFaceChain (s : NonemptyFiniteChains Factor) :
    ∃ f, ∀ x ∈ s.finset, x ∈ Set.range (flagLetter f) := by
  obtain ⟨small, hsmall, hmin⟩ :=
    Finset.exists_min_image s.finset (fun x : Factor => x.val.card) s.nonempty
  obtain ⟨large, hlarge, hmax⟩ :=
    Finset.exists_max_image s.finset (fun x : Factor => x.val.card) s.nonempty
  obtain ⟨v, hv⟩ := (P.isRelLowerSet_faces small.property).1
  let a : Factor := ⟨{v}, (P.isRelLowerSet_faces small.property).2
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)⟩
  have haCard : a.val.card = 1 := Finset.card_singleton _
  have ha (x : Factor) (hx : x ∈ s.finset) : a ≤ x :=
    Finset.singleton_subset_iff.mpr (chainLeOfCardLe s hsmall hx (hmin x hx) hv)
  obtain ⟨_, top, htop, hLargeTop⟩ := mem_generated.mp large.property
  have htCard : top.card = 3 := facetCard top htop
  have htNonempty : top.Nonempty := Finset.card_pos.mp (by omega)
  let t : Factor := ⟨top, mem_generated.mpr ⟨htNonempty, top, htop, fun _ hx => hx⟩⟩
  have ht (x : Factor) (hx : x ∈ s.finset) : x ≤ t :=
    (chainLeOfCardLe s hx hlarge (hmax x hx)).trans (show large ≤ t from hLargeTop)
  have hat : a ≤ t := (ha large hlarge).trans (ht large hlarge)
  have hex : ∃ e : Factor, a ≤ e ∧ e ≤ t ∧ e.val.card = 2 ∧
      ∀ x ∈ s.finset, x.val.card = 2 → x = e := by
    by_cases h : ∃ e ∈ s.finset, e.val.card = 2
    · obtain ⟨e, he, hcard⟩ := h
      refine ⟨e, ha e he, ht e he, hcard, fun x hx hxCard => ?_⟩
      have hxe : x.val.card = e.val.card := hxCard.trans hcard.symm
      exact faceEqOfLeOfCardLe (chainLeOfCardLe s hx he (le_of_eq hxe)) (le_of_eq hxe.symm)
    · have haBound : a.val.card ≤ 2 := by simp [haCard]
      have htBound : 2 ≤ t.val.card := by
        change 2 ≤ top.card
        simp [htCard]
      obtain ⟨edge, hae, het, hEdgeCard⟩ :=
        Finset.exists_subsuperset_card_eq (show a.val ⊆ t.val from hat) haBound htBound
      have heNonempty : edge.Nonempty := Finset.card_pos.mp (by omega)
      let e : Factor := ⟨edge, (P.isRelLowerSet_faces t.property).2 het heNonempty⟩
      exact ⟨e, hae, het, hEdgeCard, fun x hx hxCard => (h ⟨x, hx, hxCard⟩).elim⟩
  obtain ⟨e, hae, het, heCard, he⟩ := hex
  let f : Fin 3 → Factor := ![a, e, t]
  have hfMonotone : Monotone f := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · exact hae
    · exact het
  have hfCard (i : Fin 3) : (f i).val.card = i.val + 1 := by
    fin_cases i
    · exact haCard
    · exact heCard
    · exact htCard
  refine ⟨⟨f, hfMonotone, hfCard⟩, ?_⟩
  intro x hx
  have hb := faceCardBounds x
  have hc : x.val.card = 1 ∨ x.val.card = 2 ∨ x.val.card = 3 := by omega
  rcases hc with hc | hc | hc
  · refine ⟨0, ?_⟩
    change a = x
    exact faceEqOfLeOfCardLe (ha x hx) (le_of_eq (hc.trans haCard.symm))
  · exact ⟨1, show e = x from (he x hx hc).symm⟩
  · refine ⟨2, ?_⟩
    change t = x
    exact (faceEqOfLeOfCardLe (ht x hx) (le_of_eq (htCard.trans hc.symm))).symm

private theorem factorNoOneCover : ¬ HasCategoricalCover (NonemptyFiniteChains Factor) 1 := by
  intro cover
  obtain ⟨c, hc⟩ := hasCategoricalCover_one_iff.mp
    (transport_lower_cover (subdivisionFace P).symm cover)
  obtain ⟨b, hb⟩ := id_contiguity_of_face_poset_contraction c hc
  exact subdivision_not_contiguous_to_constant 0 b hb

/-- For the seven-triangle face poset, no fixed number of categorical lower
sets covers the one-step subdivisions of all finite powers. -/
theorem seven_triangles_exists_no_categorical_cover (k : ℕ) :
    ∃ n : ℕ, ¬ HasCategoricalCover (NonemptyFiniteChains (Fin n → Factor)) k :=
  exists_no_categorical_cover faceRank flagLetter rank_flagLetter extendFaceChain factorNoOneCover k

end D5.S3.Topology.StableCategory.SevenTrianglePowerCovers
