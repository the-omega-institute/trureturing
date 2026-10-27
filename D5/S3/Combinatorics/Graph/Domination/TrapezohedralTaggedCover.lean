/- GID: D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Reversible apex-tag encoding of all actual labelled minimal connected dominating subsets. -/

import D5.S3.Combinatorics.Graph.Domination.TrapezohedralApexClassification
import Mathlib.SetTheory.Cardinal.Finite

/-! The two apex branches are related by an actual graph automorphism. The map
swaps the apices and sends a(i) to b(i), b(i) to a(i+1); its inverse is explicit. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TrapezohedralTaggedCover

open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralApexClassification

open Vertex

/-- One rim step, including the induced exchange of the two apices. -/
def turn (n : ℕ) : graph n ≃g graph n where
  toFun
    | alpha => beta
    | beta => alpha
    | a i => b i
    | b i => a (finRotate n i)
  invFun
    | alpha => beta
    | beta => alpha
    | a i => b ((finRotate n).symm i)
    | b i => a i
  left_inv := by
    intro v
    cases v with
    | alpha => rfl
    | beta => rfl
    | a i => rfl
    | b i => exact congrArg b ((finRotate n).symm_apply_apply i)
  right_inv := by
    intro v
    cases v with
    | alpha => rfl
    | beta => rfl
    | b i => rfl
    | a i => exact congrArg a ((finRotate n).apply_symm_apply i)
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;>
      simp [graph, adjacent, (finRotate n).injective.eq_iff, eq_comm, or_comm]

private theorem admissible_image {n : ℕ} (e : graph n ≃g graph n)
    {S : Set (Vertex n)} (hS : Admissible S) : Admissible (e '' S) := by
  classical
  have hm := (minimalDominating_iff_proper (graph n) S).mpr hS.1
  obtain ⟨hd, hp⟩ := (minimalDominating_iff_private (graph n) S).mp hm
  refine ⟨(minimalDominating_iff_proper (graph n) _).mp
    ((minimalDominating_iff_private (graph n) _).mpr ⟨?_, ?_⟩), ?_⟩
  · have he := (DominatingSetAverage.dominating_map_iff e S.toFinset).mpr (by simpa using hd)
    rw [Finset.coe_map, Set.coe_toFinset] at he
    convert he using 1 <;> rfl
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨w, hw, hu⟩ := hp s hs
    refine ⟨e w, ?_, ?_⟩
    · rcases hw with h | h
      · exact Or.inl (congrArg e h)
      · exact Or.inr (e.map_adj_iff.mpr h)
    · rintro _ ⟨t, ht, rfl⟩ hwt
      apply congrArg e
      apply hu t ht
      rcases hwt with h | h
      · exact Or.inl (e.injective h)
      · exact Or.inr (e.map_adj_iff.mp h)
  · exact ((e.induce e.injective.bijOn_image).connected_iff).mp hS.2

private theorem mem_image_iso {n : ℕ} (e : graph n ≃g graph n)
    (S : Set (Vertex n)) (v : Vertex n) : v ∈ e '' S ↔ e.symm v ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨e.symm v, h, e.apply_symm_apply v⟩

/-- A cut cover together with the label of the removed edge. -/
def CoverData (n : ℕ) :=
  (j : Fin n) × {C : Set (Fin n) // MinimalCutCover j C ∧
    (j ∈ C ∨ finRotate n j ∈ C)}

/-- False selects alpha; true selects its image under the literal graph automorphism. -/
def taggedSet {n : ℕ} (tag : Bool) (d : CoverData n) : Set (Vertex n) :=
  if tag then turn n '' alphaSet d.1 d.2.val else alphaSet d.1 d.2.val

private theorem tagged_admissible {n : ℕ} (hn : 3 ≤ n) (tag : Bool) (d : CoverData n) :
    Admissible (taggedSet tag d) := by
  have h := (alphaSet_admissible_iff hn d.1 d.2.val).mpr d.2.property
  cases tag with
  | false => exact h
  | true => exact admissible_image (turn n) h

private theorem tagged_has_alpha {n : ℕ} (tag : Bool) (d : CoverData n) :
    alpha ∈ taggedSet tag d ↔ tag = false := by
  cases tag with
  | false => change True ↔ false = false; simp
  | true =>
    rw [taggedSet, ite_eq_left rfl, mem_image_iso]
    change False ↔ true = false
    simp

private theorem alphaSet_injective {n : ℕ} {j k : Fin n} {C D : Set (Fin n)}
    (h : alphaSet j C = alphaSet k D) : j = k ∧ C = D := by
  have hj : b j ∈ alphaSet k D := h ▸ (show b j ∈ alphaSet j C from rfl)
  refine ⟨hj, ?_⟩
  ext i
  exact congrArg (fun S : Set (Vertex n) => a i ∈ S) h |>.to_iff

private theorem tagged_injective {n : ℕ} :
    Function.Injective (fun p : Bool × CoverData n => taggedSet p.1 p.2) := by
  rintro ⟨t, ⟨j, C, hC⟩⟩ ⟨u, ⟨k, D, hD⟩⟩ heq
  have htag : t = u := by
    have h := congrArg (fun S : Set (Vertex n) => alpha ∈ S) heq
    have hiff : (t = false) ↔ (u = false) :=
      (tagged_has_alpha t _).symm.trans (h.to_iff.trans (tagged_has_alpha u _))
    cases t <;> cases u <;> simp_all
  subst u
  have hCD : alphaSet j C = alphaSet k D := by
    cases t with
    | false => exact heq
    | true =>
      have h := congrArg (fun S : Set (Vertex n) => (turn n).symm '' S) heq
      simpa only [taggedSet, Bool.true_eq, ↓reduceIte, Set.image_image,
        (turn n).symm_apply_apply, Set.image_id'] using h
  obtain ⟨rfl, rfl⟩ := alphaSet_injective hCD
  rfl

private theorem tagged_surjective {n : ℕ} (hn : 3 ≤ n) (S : Set (Vertex n))
    (hS : Admissible S) : ∃ p : Bool × CoverData n, taggedSet p.1 p.2 = S := by
  rcases exactly_one_apex hn hS with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · obtain ⟨j, heq, _⟩ := alpha_reconstruction hS ha hb
    have hc := (alphaSet_admissible_iff hn j {i | a i ∈ S}).mp (heq ▸ hS)
    exact ⟨(false, ⟨j, ⟨_, hc⟩⟩), heq.symm⟩
  · let T := (turn n).symm '' S
    have hT : Admissible T := admissible_image (turn n).symm hS
    have haT : alpha ∈ T := by
      apply (mem_image_iso (turn n).symm S alpha).mpr
      exact hb
    have hbT : beta ∉ T := by
      intro h
      have hh := (mem_image_iso (turn n).symm S beta).mp h
      exact ha hh
    obtain ⟨j, heq, _⟩ := alpha_reconstruction hT haT hbT
    have hc := (alphaSet_admissible_iff hn j {i | a i ∈ T}).mp (heq ▸ hT)
    refine ⟨(true, ⟨j, ⟨_, hc⟩⟩), ?_⟩
    change turn n '' alphaSet j {i | a i ∈ T} = S
    rw [← heq]
    change turn n '' ((turn n).symm '' S) = S
    simp only [Set.image_image, (turn n).apply_symm_apply, Set.image_id']

/-- The complete actual-subset encoding has an inverse, including both apex branches. -/
noncomputable def actualTaggedEquiv {n : ℕ} (hn : 3 ≤ n) :
    {S : Set (Vertex n) // Admissible S} ≃ Bool × CoverData n :=
  (Equiv.ofBijective
    (fun p : Bool × CoverData n => ⟨taggedSet p.1 p.2, tagged_admissible hn p.1 p.2⟩)
    ⟨fun _ _ h => tagged_injective (congrArg Subtype.val h),
      fun S => by
        obtain ⟨p, hp⟩ := tagged_surjective hn S.val S.property
        exact ⟨p, Subtype.ext hp⟩⟩).symm

end D5.S3.Combinatorics.Graph.Domination.TrapezohedralTaggedCover
