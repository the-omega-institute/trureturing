/- GID: D5/S3/Combinatorics/Graph/DUFCharging
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFCharging
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Singleton common links give a global charge for saturated link components. -/

import D5.S3.Combinatorics.Graph.DUFComponentCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFCharging

open Finset DUFStructure DUFCounting DUFComponents DUFComponentCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An additional neighbor of a block cross pair has a singleton common link
with the block center. -/
theorem singleton_common_link (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (c : V) (A S : Finset V) (hb : CompleteBlock H c A S)
    (a : V) (ha : a ∈ A) (b : V) (hbS : b ∈ S)
    (x : V) (hx : x ∈ neighbors H {a, b}) (hxc : x ≠ c) :
    common H {c, x} = {{a, b}} := by
  classical
  have hab : a ≠ b := by
    intro he; subst b; exact disjoint_left.mp hb.2.2.2.2.1 ha hbS
  have hcN : c ∈ neighbors H {a, b} := by
    simp only [neighbors, mem_filter, mem_univ, true_and]
    refine ⟨?_, hb.2.2.2.2.2 a ha b hbS⟩
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact hb.2.2.1 ha
    · exact hb.2.2.2.1 hbS
  have hp : ({a, b} : Finset V) ∈ common H {c, x} := by
    exact mem_filter.mpr ⟨by simp [pairs, hab], by
      simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hcN hx⟩
  have shared (A S : Finset V) (hb : CompleteBlock H c A S)
      (a : V) (ha : a ∈ A) (b : V) (hbS : b ∈ S)
      (hx : x ∈ neighbors H {a, b}) (y : V)
      (hy : ({a, y} : Finset V) ∈ common H {c, x}) : y = b := by
    by_contra hyb
    have hay : a ≠ y := by
      have := (mem_powersetCard.mp (mem_filter.mp hy).1).2
      by_contra he; subst y; simp at this
    have hyc := (mem_filter.mp hy).2 (mem_insert_self c {x})
    have hyx := (mem_filter.mp hy).2 (mem_insert_of_mem (mem_singleton_self x))
    have hyS : y ∈ S := by
      rw [← (block_component H hc c A S hb).1.1 a ha]
      simp only [neighbors, mem_filter, mem_univ, true_and] at hyc ⊢
      refine ⟨?_, ?_⟩
      · simp only [mem_insert, mem_singleton, not_or] at hyc ⊢
        exact ⟨Ne.symm hyc.1.2, hay.symm⟩
      · simpa only [insert_comm y c, pair_comm y a] using hyc.2
    obtain ⟨a', ha', ha'ax⟩ := exists_mem_notMem_of_card_lt_card
      (show ({a, x} : Finset V).card < A.card by
        rw [hb.1]; have := card_insert_le a ({x} : Finset V);
        simp only [card_singleton] at this; omega)
    have ha'a : a' ≠ a := fun he => ha'ax (by simp [he])
    have ha'x : a' ≠ x := fun he => ha'ax (by simp [he])
    have hca' : c ≠ a' := fun he => hb.2.2.1 (he.symm ▸ ha')
    have hca : c ≠ a := fun he => hb.2.2.1 (he.symm ▸ ha)
    have hax : a ≠ x := by
      intro he; subst x; exact (mem_filter.mp hx).2.1 (by simp)
    have haxK : ({a, x} : Finset V) ∈ common H {b, y} := by
      refine mem_filter.mpr ⟨by simp [pairs, hax], ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff]
      constructor
      · simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
          mem_singleton, not_or] at hx ⊢
        have hba : b ≠ a := by intro he; subst b; exact disjoint_left.mp hb.2.2.2.2.1 ha hbS
        exact ⟨⟨hba, Ne.symm hx.1.2⟩, by
          have he : insert b ({a, x} : Finset V) = insert x {a, b} := by
            ext t; simp only [mem_insert, mem_singleton]; tauto
          rw [he]; exact hx.2⟩
      · simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
          mem_singleton, not_or] at hyx ⊢
        exact ⟨⟨hay.symm, Ne.symm hyx.1.2⟩, by
          have he : insert y ({a, x} : Finset V) = insert x {a, y} := by
            ext t; simp only [mem_insert, mem_singleton]; tauto
          rw [he]; exact hyx.2⟩
    have hcaK : ({c, a'} : Finset V) ∈ common H {b, y} := by
      refine mem_filter.mpr ⟨by simp [pairs, hca'], ?_⟩
      rw [(block_component H hc c A S hb).1.1 a' ha']
      simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hbS hyS
    apply common_intersecting H hd {b, y} (by simp [Ne.symm hyb]) _ haxK _ hcaK
    simp [disjoint_left, hca.symm, hxc, ha'a.symm, ha'x.symm]
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hp, ?_⟩
  intro p hpK
  have hmeet := common_intersecting H hd {c, x} (by simp [hxc.symm])
    {a, b} hp p hpK
  have hp2 := (mem_powersetCard.mp (mem_filter.mp hpK).1).2
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hp2
  have hm : a = u ∨ a = v ∨ b = u ∨ b = v := by
    simp only [disjoint_left, mem_insert, mem_singleton] at hmeet
    by_contra hn
    apply hmeet
    intro t ht
    rcases ht with rfl | rfl <;> tauto
  have hswap : CompleteBlock H c S A := by
    refine ⟨hb.2.1, hb.1, hb.2.2.2.1, hb.2.2.1, hb.2.2.2.2.1.symm, ?_⟩
    intro s hs a ha
    simpa only [pair_comm] using hb.2.2.2.2.2 a ha s hs
  rcases hm with rfl | rfl | rfl | rfl
  · rw [shared A S hb a ha b hbS hx v hpK]
  · have hv := shared A S hb a ha b hbS hx u (by simpa [pair_comm] using hpK)
    simp [hv, pair_comm]
  · have hv := shared S A hswap b hbS a ha (by simpa [pair_comm] using hx) v hpK
    simp [hv, pair_comm]
  · have hu := shared S A hswap b hbS a ha (by simpa [pair_comm] using hx) u
      (by simpa [pair_comm] using hpK)
    simp [hu]

/-- Component cross-pair incidences have global capacities one at degree-one pairs
and two at singleton common links. The charge strengthens the cap-four bound. -/
theorem mixed_incidence_bound (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
    (hd : DUF H) (hc : CapFour H) :
    16 * B H ≤ h H 1 + 2 * q H 1 ∧
      H.card + 2 * B H ≤ (Fintype.card V).choose 2 := by
  classical
  let C (z : V × Finset V) := z.2.powersetCard 2 |>.filter fun p => insert z.1 p ∈ H
  have hC_image (z : V × Finset V) (A S : Finset V)
      (hb : CompleteBlock H z.1 A S) (hU : z.2 = A ∪ S) :
      C z = (A ×ˢ S).image (fun ab => ({ab.1, ab.2} : Finset V)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hps, hpH⟩ := mem_filter.mp hp
      obtain ⟨hps, hp2⟩ := mem_powersetCard.mp hps
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hp2
      have haU : a ∈ A ∪ S := by rw [← hU]; exact hps (by simp)
      have hcU : z.1 ∉ A ∪ S := by simp [hb.2.2.1, hb.2.2.2.1]
      have hcP : z.1 ∉ ({a, b} : Finset V) := fun h => hcU (hU ▸ hps h)
      have hadj : (link H z.1).Adj a b := ⟨hab, hcP, hpH⟩
      rcases ((block_component H hc z.1 A S hb).2.1 a haU b).mp hadj with h | h
      · exact mem_image.mpr ⟨(a, b), mem_product.mpr h, rfl⟩
      · exact mem_image.mpr ⟨(b, a), mem_product.mpr ⟨h.2, h.1⟩, pair_comm b a⟩
    · intro hp
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hp
      obtain ⟨ha, hbS⟩ := mem_product.mp hab
      have hab : a ≠ b := by
        intro he; subst b; exact disjoint_left.mp hb.2.2.2.2.1 ha hbS
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, by simp [hab]⟩,
        hb.2.2.2.2.2 a ha b hbS⟩
      rw [hU]
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro (mem_union_left S ha) (mem_union_right A hbS)
  have hC_card : ∀ z ∈ blocks H, (C z).card = 16 := by
    intro z hz
    obtain ⟨A, S, hb, hU⟩ := (mem_filter.mp hz).2
    rw [hC_image z A S hb hU, card_image_iff.mpr, card_product, hb.1, hb.2.1]
    · intro u hu v hv he
      change ({u.1, u.2} : Finset V) = {v.1, v.2} at he
      obtain ⟨huA, huS⟩ := mem_product.mp hu
      obtain ⟨hvA, hvS⟩ := mem_product.mp hv
      have hu1 : u.1 ∈ ({v.1, v.2} : Finset V) := by rw [← he]; simp
      have hu2 : u.2 ∈ ({v.1, v.2} : Finset V) := by rw [← he]; simp
      have hu1v2 : u.1 ≠ v.2 := by
        intro he; exact disjoint_left.mp hb.2.2.2.2.1 huA (he ▸ hvS)
      have hu2v1 : u.2 ≠ v.1 := by
        intro he; exact disjoint_left.mp hb.2.2.2.2.1 (he ▸ hvA) huS
      exact Prod.ext (by simpa [hu1v2] using hu1) (by simpa [hu2v1] using hu2)
  have hC_data : ∀ z ∈ blocks H, ∀ p ∈ C z,
      z.1 ∈ neighbors H p ∧
        ∀ x ∈ neighbors H p, x ≠ z.1 → common H {z.1, x} = {p} := by
    intro z hz p hp
    obtain ⟨A, S, hb, hU⟩ := (mem_filter.mp hz).2
    rw [hC_image z A S hb hU] at hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hp
    obtain ⟨ha, hbS⟩ := mem_product.mp hab
    refine ⟨?_, fun x hx hxc => singleton_common_link H hd hc z.1 A S hb a ha b hbS x hx hxc⟩
    simp only [neighbors, mem_filter, mem_univ, true_and]
    refine ⟨?_, hb.2.2.2.2.2 a ha b hbS⟩
    simp only [mem_insert, mem_singleton]
    rintro (he | he)
    · exact hb.2.2.1 (he.symm ▸ ha)
    · exact hb.2.2.2.1 (he.symm ▸ hbS)
  have howner (z w : V × Finset V) (hz : z ∈ blocks H) (hw : w ∈ blocks H)
      (p : Finset V) (hpz : p ∈ C z) (hpw : p ∈ C w) (hcenter : z.1 = w.1) :
      z = w := by
    obtain ⟨A, S, hb, hU⟩ := (mem_filter.mp hz).2
    obtain ⟨D, T, hb', hU'⟩ := (mem_filter.mp hw).2
    obtain ⟨K, hK⟩ := (block_component H hc z.1 A S hb).2.2
    obtain ⟨L, hL⟩ := (block_component H hc z.1 D T (hcenter ▸ hb')).2.2
    obtain ⟨hps, hp2⟩ := mem_powersetCard.mp (mem_filter.mp hpz).1
    have hps' := (mem_powersetCard.mp (mem_filter.mp hpw).1).1
    obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < p.card)
    have hKL : K = L := SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (by rw [hK, ← hU]; exact hps ha) (by rw [hL, ← hU']; exact hps' ha)
    apply Prod.ext hcenter
    apply coe_injective
    rw [hU, hU', ← hK, ← hL, hKL]
  let I := (blocks H).sigma C
  have hIcard : I.card = 16 * B H := by
    rw [card_sigma, sum_congr rfl hC_card]
    simp [B, Nat.mul_comm]
  have hIpair : ∀ i ∈ I, i.2 ∈ (pairs : Finset (Finset V)) := by
    intro i hi
    exact mem_powersetCard.mpr ⟨subset_univ _,
      (mem_powersetCard.mp (mem_filter.mp (mem_sigma.mp hi).2).1).2⟩
  have hIdata : ∀ i ∈ I, i.1.1 ∈ neighbors H i.2 ∧
      ∀ x ∈ neighbors H i.2, x ≠ i.1.1 → common H {i.1.1, x} = {i.2} := by
    intro i hi
    exact hC_data i.1 (mem_sigma.mp hi).1 i.2 (mem_sigma.mp hi).2
  have hIinj : ∀ i ∈ I, ∀ j ∈ I, i.1.1 = j.1.1 → i.2 = j.2 → i = j := by
    intro i hi j hj hcenter hp
    have hz := howner i.1 j.1 (mem_sigma.mp hi).1 (mem_sigma.mp hj).1
      i.2 (mem_sigma.mp hi).2 (hp ▸ (mem_sigma.mp hj).2) hcenter
    exact Sigma.ext hz (heq_of_eq hp)
  let I₁ := I.filter fun i => (neighbors H i.2).card = 1
  let I₂ := I.filter fun i => (neighbors H i.2).card ≠ 1
  have hI₁ : I₁.card ≤ h H 1 := by
    apply card_le_card_of_injOn (fun i => i.2)
    · intro i hi
      exact mem_filter.mpr ⟨hIpair i (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩
    · intro i hi j hj hp
      change i.2 = j.2 at hp
      have hi' : i ∈ I ∧ (neighbors H i.2).card = 1 := mem_filter.mp hi
      have hj' : j ∈ I ∧ (neighbors H j.2).card = 1 := mem_filter.mp hj
      apply hIinj i hi'.1 j hj'.1 ?_ hp
      have hsmall : (neighbors H i.2).card ≤ 1 := hi'.2.le
      exact card_le_one.mp hsmall _ (hIdata i hi'.1).1 _
        (hp ▸ (hIdata j hj'.1).1)
  let Q := pairs.filter fun q => (common H q).card = 1
  let r (i : Σ _ : V × Finset V, Finset V) (q : Finset V) :=
    q ⊆ neighbors H i.2 ∧ i.1.1 ∈ q
  have hleft : ∀ i ∈ I₂, 1 ≤ (Q.bipartiteAbove r i).card := by
    intro i hi
    have hiI := (mem_filter.mp hi).1
    have hci := (hIdata i hiI).1
    have hdeg : 1 < (neighbors H i.2).card := by
      have := card_pos.mpr ⟨i.1.1, hci⟩
      have := (mem_filter.mp hi).2
      omega
    obtain ⟨x, hx, hxc⟩ := exists_mem_ne hdeg i.1.1
    apply card_pos.mpr
    refine ⟨{i.1.1, x}, mem_filter.mpr ⟨?_, ?_⟩⟩
    · refine mem_filter.mpr ⟨by simp [pairs, hxc.symm], ?_⟩
      rw [(hIdata i hiI).2 x hx hxc, card_singleton]
    · exact ⟨by simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro hci hx, by simp⟩
  have hright : ∀ q ∈ Q, (I₂.bipartiteBelow r q).card ≤ 2 := by
    intro q hq
    have hq2 : q.card = 2 := (mem_powersetCard.mp (mem_filter.mp hq).1).2
    rw [← hq2]
    apply card_le_card_of_injOn (fun i => i.1.1)
    · intro i hi
      exact (mem_filter.mp hi).2.2
    · intro i hi j hj hcenter
      have hiI := (mem_filter.mp (mem_filter.mp hi).1).1
      have hjI := (mem_filter.mp (mem_filter.mp hj).1).1
      apply hIinj i hiI j hjI hcenter
      apply card_le_one.mp (le_of_eq (mem_filter.mp hq).2)
      · exact mem_filter.mpr ⟨hIpair i hiI, (mem_filter.mp hi).2.1⟩
      · exact mem_filter.mpr ⟨hIpair j hjI, (mem_filter.mp hj).2.1⟩
  have hI₂ : I₂.card ≤ 2 * q H 1 := by
    have hh := card_nsmul_le_card_nsmul r hleft hright
    simpa only [smul_eq_mul, Nat.mul_one, Nat.one_mul, Nat.mul_comm, Q, q] using hh
  have hsplit : I₁.card + I₂.card = I.card :=
    card_filter_add_card_filter_not (s := I)
      (fun i : Σ _ : V × Finset V, Finset V => (neighbors H i.2).card = 1)
  have hcharge : 16 * B H ≤ h H 1 + 2 * q H 1 := by
    calc
      16 * B H = I₁.card + I₂.card := hIcard.symm.trans hsplit.symm
      _ ≤ h H 1 + 2 * q H 1 := Nat.add_le_add hI₁ hI₂
  refine ⟨hcharge, ?_⟩
  have hid := (component_counting H hu hd hc).2.2.1
  clear * - hid hcharge
  omega

end D5.S3.Combinatorics.Graph.DUFCharging
