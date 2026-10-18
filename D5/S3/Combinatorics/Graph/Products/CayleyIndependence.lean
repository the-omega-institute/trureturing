/- GID: D5/S3/Combinatorics/Graph/Products/CayleyIndependence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/CayleyIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Cayley, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Layer bounds and the independence number of finite abelian Cayley Cartesian squares. -/

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open SimpleGraph Finset
open scoped BigOperators

namespace CayleySquare

variable {V W : Type*} [Finite W]

/-- An independent set supported on specified rows has at most alpha vertices per row. -/
theorem card_le_layer_bound (G : SimpleGraph V) (H : SimpleGraph W)
    (I : Finset (V × W)) (R : Finset V) (hI : (G □ H).IsIndepSet I)
    (hR : ∀ p ∈ I, p.1 ∈ R) : I.card ≤ R.card * H.indepNum := by
  classical
  have hf (a : V) : (I.filter (fun p => p.1 = a)).card ≤ H.indepNum := by
    let J := I.filter (fun p => p.1 = a)
    have hi : H.IsIndepSet (J.image Prod.snd) := by
      intro x hx y hy hxy hadj
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
      obtain ⟨hpI, hpa⟩ := mem_filter.mp hp
      obtain ⟨hqI, hqa⟩ := mem_filter.mp hq
      exact hI hpI hqI (fun e => hxy (congrArg Prod.snd e))
        (Or.inr ⟨hadj, hpa.trans hqa.symm⟩)
    have hj : Set.InjOn Prod.snd (J : Set (V × W)) := by
      intro p hp q hq he
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
    calc
      (I.filter (fun p => p.1 = a)).card = (J.image Prod.snd).card :=
        (card_image_of_injOn hj).symm
      _ ≤ H.indepNum := hi.card_le_indepNum
  calc
    I.card = ∑ a ∈ R, (I.filter (fun p => p.1 = a)).card :=
      card_eq_sum_card_fiberwise (fun p hp => hR p hp)
    _ ≤ ∑ _a ∈ R, H.indepNum := sum_le_sum (fun a _ => hf a)
    _ = R.card * H.indepNum := by simp

variable {A : Type*} [Fintype A] [AddCommGroup A]

omit [Fintype A] in
private theorem cayley_adj_iff (S : Set A) (hzero : (0 : A) ∉ S)
    (hneg : ∀ a ∈ S, -a ∈ S) (x y : A) :
    (addCayley S).Adj x y ↔ y - x ∈ S := by
  rw [addCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · simpa [sub_eq_add_neg, add_comm] using h
    · simpa [sub_eq_add_neg, add_comm] using hneg _ h
  · intro h
    refine ⟨?_, Or.inl ?_⟩
    · intro e
      subst y
      exact hzero (by simpa using h)
    · simpa [sub_eq_add_neg, add_comm] using h

/-- No connectivity assumption is needed for the finite abelian Cayley square equality. -/
theorem indepNum_addCayley_square (S : Set A) (hzero : (0 : A) ∉ S)
    (hneg : ∀ a ∈ S, -a ∈ S) :
    ((addCayley S) □ (addCayley S)).indepNum = Fintype.card A * (addCayley S).indepNum := by
  classical
  let G := addCayley S
  apply Nat.le_antisymm
  · obtain ⟨I, hI⟩ := (G □ G).maximumIndepSet_exists
    rw [← (G □ G).maximumIndepSet_card_eq_indepNum I hI]
    simpa using card_le_layer_bound G G I univ hI.isIndepSet (by simp)
  · obtain ⟨B, hB⟩ := G.maximumIndepSet_exists
    let f : A × A → A × A := fun p => (p.1, p.1 + p.2)
    let I := (univ.product B).image f
    have hf : Function.Injective f := by
      intro p q h
      apply Prod.ext
      · simpa only [f] using congrArg Prod.fst h
      · have hfst := congrArg Prod.fst h
        have hsnd := congrArg Prod.snd h
        dsimp [f] at hfst hsnd
        rw [hfst] at hsnd
        exact add_left_cancel hsnd
    have hi : (G □ G).IsIndepSet I := by
      intro p hp q hq hpq hadj
      obtain ⟨⟨x,b⟩, hxb, rfl⟩ := mem_image.mp hp
      obtain ⟨⟨y,c⟩, hyc, rfl⟩ := mem_image.mp hq
      have hb : b ∈ B := (mem_product.mp hxb).2
      have hc : c ∈ B := (mem_product.mp hyc).2
      rcases hadj with ⟨hxy, he⟩ | ⟨hxy, he⟩
      · have he' : x + b = y + c := he
        have hbc : b ≠ c := by
          intro e
          subst c
          exact hxy.ne (add_right_cancel he')
        apply hB.isIndepSet hc hb hbc.symm
        apply (cayley_adj_iff S hzero hneg c b).mpr
        have hstep := (cayley_adj_iff S hzero hneg x y).mp hxy
        have hid : b - c = y - x := by
          apply (sub_eq_sub_iff_add_eq_add).mpr
          simpa [add_comm] using he'
        rwa [hid]
      · have he' : x = y := he
        have hbc : b ≠ c := by
          intro e
          exact hpq (by simp [f, he', e])
        apply hB.isIndepSet hb hc hbc
        apply (cayley_adj_iff S hzero hneg b c).mpr
        have hstep := (cayley_adj_iff S hzero hneg (x+b) (y+c)).mp hxy
        simpa [he', add_sub_add_left_eq_sub] using hstep
    calc
      Fintype.card A * G.indepNum = (univ.product B).card := by
        simp only [Finset.product_eq_sprod, Finset.card_product, card_univ,
          G.maximumIndepSet_card_eq_indepNum B hB]
      _ = I.card := (card_image_of_injective _ hf).symm
      _ ≤ (G □ G).indepNum := hi.card_le_indepNum

end CayleySquare
