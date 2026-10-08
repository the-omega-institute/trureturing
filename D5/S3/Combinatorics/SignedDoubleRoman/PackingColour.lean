/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingColour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingColour
   mirror-E: none(waiver:largest-colour-class)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: A largest class of a three-colouring solves the pure-colour packing case. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtension
import D5.S3.Combinatorics.SignedDoubleRoman.SubcubicThreeColouring
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingColour

open Finset MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A colour class of size at least one third is independent and domination-limited. -/
theorem packing_of_colourable (C D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (hD : D = ⊥) (hc : (C.induce (S : Set V)).Colorable 3) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  obtain ⟨c⟩ := hc
  let f : V → Fin 3 := fun v => if hv : v ∈ S then c ⟨v, hv⟩ else 0
  let F : Fin 3 → Finset V := fun i => S.filter (fun v => f v = i)
  have hsum : S.card = ∑ i : Fin 3, (F i).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => (F i).card) Finset.univ_nonempty
  have hbound : S.card ≤ 3 * (F i).card := by
    calc
      S.card = ∑ j : Fin 3, (F j).card := hsum
      _ ≤ ∑ _j : Fin 3, (F i).card := Finset.sum_le_sum (fun j hj => hi j hj)
      _ = 3 * (F i).card := by simp
  refine ⟨F i, Finset.filter_subset _ _, ⟨?_, ?_⟩, hbound⟩
  · intro a ha b hb hab hadj
    obtain ⟨haS, ha⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbS, hb⟩ := Finset.mem_filter.mp hb
    have hf : f a = f b := ha.trans hb.symm
    simp only [f, dif_pos haS, dif_pos hbS] at hf
    exact c.valid (v := ⟨a, haS⟩) (w := ⟨b, hbS⟩) hadj hf
  · subst D
    intro v
    have hsmall := Finset.card_le_card
      (Finset.inter_subset_left : (insert v ((⊥ : SimpleGraph V).neighborFinset v)) ∩
        F i ⊆ insert v ((⊥ : SimpleGraph V).neighborFinset v))
    simpa using hsmall.trans (by simp)

/-- With no domination edges, elementary subcubic colouring supplies a large packing. -/
theorem pure_colour_case (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S : Finset V) (hdegree : DegreeBound C D S) (hno : C.CliqueFreeOn (S : Set V) 4)
    (hD : D = ⊥) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let H := C.induce (S : Set V)
  have hdeg : ∀ v : S, (H.neighborFinset v).card ≤ 3 := by
    intro v
    have hh : (H.neighborFinset v).card ≤ (C.neighborFinset v.val).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro w hw
        exact (C.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hw)
      · exact Subtype.val_injective.injOn
    have hd := hdegree v.val v.property
    change (C.neighborFinset v.val).card + (D.neighborFinset v.val).card ≤ 3 at hd
    change (H.neighborFinset v).card ≤ 3
    omega
  have hfree : H.CliqueFree 4 :=
    (SimpleGraph.cliqueFree_induce_iff C (S : Set V) 4).mpr hno
  exact packing_of_colourable C D S hD
    (SubcubicColouring.colorable_of_subcubic_cliqueFree H hdeg hfree)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingColour
