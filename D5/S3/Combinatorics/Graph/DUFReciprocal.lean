/- GID: D5/S3/Combinatorics/Graph/DUFReciprocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFReciprocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Sigma]
   utility: none
   digest: Reciprocal incidence weights of finite triple families. -/

import D5.S3.Combinatorics.Graph.DUFStructure
import D5.S3.Combinatorics.Graph.ThreeColorReciprocal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFReciprocal

open Finset DUFStructure
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local reciprocal weight, expressed in the original triple family. -/
def weight (H : Finset (Finset V)) (e : Finset V) : ℚ :=
  (∑ a ∈ e, 1 / ((neighbors H (e.erase a)).card : ℚ)) +
    (1 / 2 : ℚ) * ∑ a ∈ e, ∑ x ∈ (neighbors H (e.erase a)).erase a,
      1 / ((common H {a, x}).card : ℚ)

/-- Vertices of the graph attached to a triple: a replaced coordinate and its new value. -/
def localVertices (H : Finset (Finset V)) (e : Finset V) : Finset (V × V) :=
  univ.filter fun v => v.1 ∈ e ∧ v.2 ∉ e ∧ insert v.2 (e.erase v.1) ∈ H

/-- Adjacency is the third triple on the two new values and the remaining coordinate. -/
def adjacent (H : Finset (Finset V)) (e : Finset V) (v w : V × V) : Prop :=
  v.1 ≠ w.1 ∧ v.2 ≠ w.2 ∧ insert v.2 (insert w.2 ((e.erase v.1).erase w.1)) ∈ H

/-- The actual neighbors within the local vertex set. -/
def localNeighbors (H : Finset (Finset V)) (e : Finset V)
    (v : V × V) : Finset (V × V) :=
  @Finset.filter _ (adjacent H e v) (fun w => by unfold adjacent; infer_instance)
    (localVertices H e)

/-- The common-link correspondence and the degree of every mixed local vertex. -/
theorem local_correspondence (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3)
    (v : V × V) (hv : v ∈ localVertices H e) :
    (localNeighbors H e v).card + 1 = (common H {v.1, v.2}).card ∧
      ((∃ w ∈ localNeighbors H e v, ∃ z ∈ localNeighbors H e v, w.1 ≠ z.1) →
        (localNeighbors H e v).card = 2) := by
  rcases v with ⟨a, x⟩
  obtain ⟨ha, hx, hxH⟩ := (mem_filter.mp hv).2
  have hp2 : (e.erase a).card = 2 := by rw [card_erase_of_mem ha, he3]
  obtain ⟨b, c, hbc, hp⟩ := card_eq_two.mp hp2
  have hab : a ≠ b := by
    have : a ∉ e.erase a := by simp
    rw [hp] at this
    exact (not_or.mp (show ¬ (a = b ∨ a = c) by simpa using this)).1
  have hac : a ≠ c := by
    have : a ∉ e.erase a := by simp
    rw [hp] at this
    exact (not_or.mp (show ¬ (a = b ∨ a = c) by simpa using this)).2
  have heq : e = {a, b, c} := by
    rw [← insert_erase ha, hp]
  subst e
  have hxa : x ≠ a := fun h => hx (by simp [h])
  have hxb : x ≠ b := fun h => hx (by simp [h])
  have hxc : x ≠ c := fun h => hx (by simp [h])
  simp only [hp] at hxH
  let L : Finset V := univ.filter fun y =>
    y ∉ ({a, b, c} : Finset V) ∧ y ≠ x ∧
      ({a, c, y} : Finset V) ∈ H ∧ ({x, c, y} : Finset V) ∈ H
  let R : Finset V := univ.filter fun y =>
    y ∉ ({a, b, c} : Finset V) ∧ y ≠ x ∧
      ({a, b, y} : Finset V) ∈ H ∧ ({x, b, y} : Finset V) ∈ H
  have ln : localNeighbors H {a, b, c} (a, x) =
      L.image (fun y => (b, y)) ∪ R.image (fun y => (c, y)) := by
    ext w
    rcases w with ⟨d, y⟩
    simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and,
      mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hd, hy, hyH⟩, had, hxy, hxyH⟩
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact (had rfl).elim
      · left
        refine ⟨y, ?_, rfl, rfl⟩
        simp only [L, mem_filter, mem_univ, true_and]
        refine ⟨hy, hxy.symm, ?_, ?_⟩
        · convert hyH using 1
          ext t
          simp [hab, hbc, erase_insert_of_ne, insert_comm, pair_comm]
          tauto
        · simpa [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, erase_insert, erase_insert_of_ne, insert_comm, pair_comm] using hxyH
      · right
        refine ⟨y, ?_, rfl, rfl⟩
        simp only [R, mem_filter, mem_univ, true_and]
        refine ⟨hy, hxy.symm, ?_, ?_⟩
        · convert hyH using 1
          ext t
          simp [hac, hbc.symm, erase_insert_of_ne, insert_comm, pair_comm]
          tauto
        · simpa [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, erase_insert, erase_insert_of_ne, insert_comm, pair_comm] using hxyH
    · rintro (⟨z, hz, hd, rfl⟩ | ⟨z, hz, hd, rfl⟩) <;> subst d
      · obtain ⟨hy, hyx, hyH, hxyH⟩ := (mem_filter.mp hz).2
        refine ⟨⟨by simp, hy, ?_⟩, hab, hyx.symm, ?_⟩
        · convert hyH using 1
          ext t
          simp [hab, hbc.symm, erase_insert_of_ne, insert_comm, pair_comm]
          tauto
        · simpa [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, erase_insert, erase_insert_of_ne, insert_comm, pair_comm] using hxyH
      · obtain ⟨hy, hyx, hyH, hxyH⟩ := (mem_filter.mp hz).2
        refine ⟨⟨by simp, hy, ?_⟩, hac, hyx.symm, ?_⟩
        · convert hyH using 1
          ext t
          simp [hac, hbc.symm, erase_insert_of_ne, insert_comm, pair_comm]
          tauto
        · simpa [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, erase_insert, erase_insert_of_ne, insert_comm, pair_comm] using hxyH
  have base : ({b, c} : Finset V) ∈ common H {a, x} := by
    simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
      insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
    exact ⟨by simp [hbc], ⟨by simp [hab, hac], he⟩,
      ⟨by simp [hxb, hxc], hxH⟩⟩
  have hi := common_intersecting H hd {a, x} (by simp [hxa.symm])
  have left_common (y : V) (hy : y ∈ L) : ({c, y} : Finset V) ∈ common H {a, x} := by
    obtain ⟨hy, hyx, hyH, hxyH⟩ := (mem_filter.mp hy).2
    have hya : y ≠ a := fun h => hy (by simp [h])
    have hyc : y ≠ c := fun h => hy (by simp [h])
    simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
      insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
    exact ⟨by simp [hyc.symm], ⟨by simp [hac, hya.symm], hyH⟩,
      ⟨by simp [hxc, hyx.symm], hxyH⟩⟩
  have right_common (y : V) (hy : y ∈ R) : ({b, y} : Finset V) ∈ common H {a, x} := by
    obtain ⟨hy, hyx, hyH, hxyH⟩ := (mem_filter.mp hy).2
    have hya : y ≠ a := fun h => hy (by simp [h])
    have hyb : y ≠ b := fun h => hy (by simp [h])
    simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
      insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
    exact ⟨by simp [hyb.symm], ⟨by simp [hab, hya.symm], hyH⟩,
      ⟨by simp [hxb, hyx.symm], hxyH⟩⟩
  have kl : (common H {a, x}).erase {b, c} =
      L.image (fun y => ({c, y} : Finset V)) ∪
        R.image (fun y => ({b, y} : Finset V)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpne, hpK⟩ := mem_erase.mp hp
      have hdata := mem_filter.mp hpK
      have hp2 : p.card = 2 := (mem_powersetCard.mp hdata.1).2
      have hap : a ∉ p := (mem_filter.mp (hdata.2 (by simp : a ∈ ({a, x} : Finset V)))).2.1
      have hxp : x ∉ p := (mem_filter.mp (hdata.2 (by simp : x ∈ ({a, x} : Finset V)))).2.1
      have haH : insert a p ∈ H := (mem_filter.mp (hdata.2 (by simp))).2.2
      have hxH : insert x p ∈ H := (mem_filter.mp (hdata.2 (by simp))).2.2
      have meet : b ∈ p ∨ c ∈ p := by
        by_contra hn
        push Not at hn
        apply hi {b, c} base p hpK
        simp [disjoint_insert_left, hn.1, hn.2]
      have extract (d : V) (hdp : d ∈ p) : ∃ y, d ≠ y ∧ p = {d, y} := by
        obtain ⟨u, z, huz, rfl⟩ := card_eq_two.mp hp2
        simp only [mem_insert, mem_singleton] at hdp
        rcases hdp with rfl | rfl
        · exact ⟨z, huz, rfl⟩
        · exact ⟨u, huz.symm, pair_comm _ _⟩
      rcases meet with hb | hc
      · obtain ⟨y, hby, rfl⟩ := extract b hb
        have hyc : y ≠ c := by intro h; subst y; exact hpne rfl
        have hya : y ≠ a := by intro h; subst y; exact hap (by simp)
        have hyx : y ≠ x := by intro h; subst y; exact hxp (by simp)
        apply mem_union_right
        apply mem_image.mpr
        exact ⟨y, mem_filter.mpr ⟨mem_univ _, by simp [hya, hby.symm, hyc], hyx, haH, hxH⟩, rfl⟩
      · obtain ⟨y, hcy, rfl⟩ := extract c hc
        have hyb : y ≠ b := by intro h; subst y; exact hpne (pair_comm _ _)
        have hya : y ≠ a := by intro h; subst y; exact hap (by simp)
        have hyx : y ≠ x := by intro h; subst y; exact hxp (by simp)
        apply mem_union_left
        apply mem_image.mpr
        exact ⟨y, mem_filter.mpr ⟨mem_univ _, by simp [hya, hyb, hcy.symm], hyx, haH, hxH⟩, rfl⟩
    · intro hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
        apply mem_erase.mpr
        refine ⟨?_, left_common y hy⟩
        intro heq
        have hb : b ∈ ({c, y} : Finset V) := heq.symm ▸ (by simp)
        have hyb : y ≠ b := fun h => (mem_filter.mp hy).2.1 (by simp [h])
        simp [hbc, hyb.symm] at hb
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
        apply mem_erase.mpr
        refine ⟨?_, right_common y hy⟩
        intro heq
        have hc : c ∈ ({b, y} : Finset V) := heq.symm ▸ (by simp)
        have hyc : y ≠ c := fun h => (mem_filter.mp hy).2.1 (by simp [h])
        simp [hbc.symm, hyc.symm] at hc
  have lnc : (localNeighbors H {a, b, c} (a, x)).card = L.card + R.card := by
    rw [ln, card_union_of_disjoint]
    · rw [card_image_of_injective _ (fun y z h => (Prod.mk.inj h).2),
        card_image_of_injective _ (fun y z h => (Prod.mk.inj h).2)]
    · apply disjoint_left.mpr
      intro w hw hz
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
      obtain ⟨z, hz, h⟩ := mem_image.mp hz
      exact hbc (congrArg Prod.fst h).symm
  have kc : ((common H {a, x}).erase {b, c}).card = L.card + R.card := by
    rw [kl, card_union_of_disjoint]
    · congr 1
      · apply card_image_iff.mpr
        intro y hy z hz heq
        have hyc : y ≠ c := fun h => (mem_filter.mp hy).2.1 (by simp [h])
        have : y ∈ ({c, z} : Finset V) := by
          change ({c, y} : Finset V) = {c, z} at heq
          rw [← heq]; simp
        simpa [hyc] using this
      · apply card_image_iff.mpr
        intro y hy z hz heq
        have hyb : y ≠ b := fun h => (mem_filter.mp hy).2.1 (by simp [h])
        have : y ∈ ({b, z} : Finset V) := by
          change ({b, y} : Finset V) = {b, z} at heq
          rw [← heq]; simp
        simpa [hyb] using this
    · apply disjoint_left.mpr
      intro p hp hq
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
      obtain ⟨z, hz, heq⟩ := mem_image.mp hq
      have : b ∈ ({c, y} : Finset V) := heq ▸ (by simp)
      have hyb : y ≠ b := fun h => (mem_filter.mp hy).2.1 (by simp [h])
      simp [hbc, hyb.symm] at this
  constructor
  · have := card_erase_add_one base
    dsimp only
    omega
  · intro hm
    have hboth : L.Nonempty ∧ R.Nonempty := by
      obtain ⟨w, hw, z, hz, hne⟩ := hm
      rw [ln] at hw hz
      rcases mem_union.mp hw with hw | hw <;> rcases mem_union.mp hz with hz | hz
      · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
        obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
        exact (hne rfl).elim
      · exact ⟨by obtain ⟨u, hu, _⟩ := mem_image.mp hw; exact ⟨u, hu⟩,
          by obtain ⟨t, ht, _⟩ := mem_image.mp hz; exact ⟨t, ht⟩⟩
      · exact ⟨by obtain ⟨u, hu, _⟩ := mem_image.mp hz; exact ⟨u, hu⟩,
          by obtain ⟨t, ht, _⟩ := mem_image.mp hw; exact ⟨t, ht⟩⟩
      · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
        obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
        exact (hne rfl).elim
    obtain ⟨u, hu⟩ := hboth.1
    obtain ⟨z, hz⟩ := hboth.2
    have all_eq : ∀ y ∈ L, ∀ z ∈ R, y = z := by
      intro y hy z hz
      have h := hi {c, y} (left_common y hy) {b, z} (right_common z hz)
      have hyb : y ≠ b := fun h => (mem_filter.mp hy).2.1 (by simp [h])
      have hzc : z ≠ c := fun h => (mem_filter.mp hz).2.1 (by simp [h])
      simpa [disjoint_left, hbc.symm, hyb, hzc.symm] using h
    have hL : L = {u} := by
      ext y
      simp only [mem_singleton]
      exact ⟨fun hy => (all_eq y hy z hz).trans (all_eq u hu z hz).symm,
        fun h => h.symm ▸ hu⟩
    have hR : R = {z} := by
      ext y
      simp only [mem_singleton]
      exact ⟨fun hy => (all_eq u hu y hy).symm.trans (all_eq u hu z hz),
        fun h => h.symm ▸ hz⟩
    rw [lnc, hL, hR]
    simp

set_option maxHeartbeats 2000000 in
/-- Every finite three-uniform disjoint-union-free family has size at most 24/23 times the number of ground pairs. -/
theorem reciprocal_bound (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3) (hd : DUF H)
    :
    23 * H.card ≤ 24 * (Fintype.card V).choose 2 := by
  have local_weight (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) :
      weight H e =
        (∑ a ∈ e, 1 / (((localVertices H e).filter fun v => v.1 = a).card + 1 : ℚ)) +
          (1 / 2 : ℚ) * ∑ v ∈ localVertices H e,
            1 / ((localNeighbors H e v).card + 1 : ℚ) := by
    have mem (a x : V) (ha : a ∈ e) :
        (a, x) ∈ localVertices H e ↔ x ∈ (neighbors H (e.erase a)).erase a := by
      simp only [localVertices, neighbors, mem_filter, mem_univ, true_and, mem_erase]
      have hx : x ∈ e ↔ x = a ∨ x ∈ e.erase a := by
        conv_lhs => rw [← insert_erase ha]
        exact mem_insert
      simp only [ha, true_and, hx, not_or]
      tauto
    have sizes (a : V) (ha : a ∈ e) :
        ((localVertices H e).filter fun v => v.1 = a).card + 1 =
          (neighbors H (e.erase a)).card := by
      have hcard : ((localVertices H e).filter fun v => v.1 = a).card =
          ((neighbors H (e.erase a)).erase a).card := by
        symm
        apply card_bij (fun x _ => (a, x))
        · intro x hx
          exact mem_filter.mpr ⟨(mem a x ha).mpr hx, rfl⟩
        · intro x hx y hy h
          exact (Prod.mk.inj h).2
        · rintro ⟨b, x⟩ hx
          obtain ⟨hv, hb⟩ := mem_filter.mp hx
          change b = a at hb
          subst b
          exact ⟨x, (mem a x ha).mp hv, rfl⟩
      rw [hcard]
      apply card_erase_add_one
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨by simp, (insert_erase ha).symm ▸ he⟩
    have sumv : (∑ v ∈ localVertices H e,
        1 / ((common H {v.1, v.2}).card : ℚ)) =
        ∑ a ∈ e, ∑ x ∈ (neighbors H (e.erase a)).erase a,
          1 / ((common H {a, x}).card : ℚ) := by
      apply sum_finset_product
      intro v
      rcases v with ⟨a, x⟩
      constructor
      · intro hv
        have ha := (mem_filter.mp hv).2.1
        exact ⟨ha, (mem a x ha).mp hv⟩
      · rintro ⟨ha, hx⟩
        exact (mem a x ha).mpr hx
    unfold weight
    congr 1
    · apply sum_congr rfl
      intro a ha
      have hs := sizes a ha
      have hs' : (((localVertices H e).filter fun v => v.1 = a).card : ℚ) + 1 =
          ((neighbors H (e.erase a)).card : ℚ) := by exact_mod_cast hs
      rw [hs']
    · congr 1
      rw [← sumv]
      apply sum_congr rfl
      intro v hv
      have hs := (local_correspondence H hd e he he3 v hv).1
      have hs' : ((localNeighbors H e v).card : ℚ) + 1 =
          ((common H {v.1, v.2}).card : ℚ) := by exact_mod_cast hs
      rw [hs']

  have reciprocal_identity (H : Finset (Finset V))
      (hu : ∀ e ∈ H, e.card = 3) :
      (∑ e ∈ H, weight H e) =
        ((pairs.filter fun p => (neighbors H p).Nonempty).card : ℚ) +
        ((pairs.filter fun q => (common H q).Nonempty).card : ℚ) := by
    have reindex (f : Finset V → V → ℚ) :
        (∑ e ∈ H, ∑ a ∈ e, f (e.erase a) a) =
          ∑ p ∈ pairs, ∑ a ∈ neighbors H p, f p a := by
      rw [sum_sigma', sum_sigma']
      apply sum_bij (fun z _ => ⟨z.1.erase z.2, z.2⟩)
      · rintro ⟨e, a⟩ hz
        obtain ⟨he, ha⟩ := mem_sigma.mp hz
        apply mem_sigma.mpr
        refine ⟨?_, ?_⟩
        · simp [pairs, card_erase_of_mem ha, hu e he]
        · simp only [neighbors, mem_filter, mem_univ, true_and]
          exact ⟨by simp, (insert_erase ha).symm ▸ he⟩
      · rintro ⟨e, a⟩ hz ⟨f, b⟩ hw h
        obtain ⟨he, ha⟩ := mem_sigma.mp hz
        obtain ⟨hf, hb⟩ := mem_sigma.mp hw
        have hab : a = b := congrArg Sigma.snd h
        subst b
        have hef : e.erase a = f.erase a := congrArg Sigma.fst h
        have : e = f := (insert_erase ha).symm.trans ((congrArg (insert a) hef).trans (insert_erase hb))
        subst f
        rfl
      · rintro ⟨p, a⟩ hz
        obtain ⟨hp, ha⟩ := mem_sigma.mp hz
        obtain ⟨hap, hH⟩ := (mem_filter.mp ha).2
        refine ⟨⟨insert a p, a⟩, mem_sigma.mpr ⟨hH, mem_insert_self _ _⟩, ?_⟩
        simp [erase_insert hap]
      · intro z hz
        rfl
    have ordered (S : Finset V) (f : Finset V → ℚ) :
        (∑ a ∈ S, ∑ x ∈ S.erase a, f {a, x}) =
          2 * ∑ q ∈ S.powersetCard 2, f q := by
      have hh : (∑ z ∈ S.offDiag, f {z.1, z.2}) =
          ∑ a ∈ S, ∑ x ∈ S.erase a, f {a, x} := by
        apply sum_finset_product
        intro z
        simp only [mem_offDiag, mem_erase]
        tauto
      rw [← hh, ← sum_fiberwise_of_maps_to' (t := S.powersetCard 2)
        (g := fun z : V × V => ({z.1, z.2} : Finset V))
        (fun z hz => by
          obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp hz
          simp [mem_powersetCard, insert_subset_iff, ha, hb, hab]) f]
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      obtain ⟨hqS, hq2⟩ := mem_powersetCard.mp hq
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hq2
      have ha : a ∈ S := hqS (by simp)
      have hb : b ∈ S := hqS (by simp)
      have he : (S.offDiag.filter fun z => ({z.1, z.2} : Finset V) = {a, b}) =
          {(a, b), (b, a)} := by
        ext z
        simp only [mem_filter, mem_offDiag, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨hz1, hz2, hne⟩, he⟩
          have h1 : z.1 = a ∨ z.1 = b := by
            have : z.1 ∈ ({a, b} : Finset V) := he ▸ (by simp)
            simpa using this
          have h2 : z.2 = a ∨ z.2 = b := by
            have : z.2 ∈ ({a, b} : Finset V) := he ▸ (by simp)
            simpa using this
          rcases z with ⟨u, v⟩
          simp only at *
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all
        · rintro (rfl | rfl) <;> simp [ha, hb, hab, hab.symm, pair_comm]
      rw [he]
      simp [hab, hab.symm, two_mul]
    have first : (∑ e ∈ H, ∑ a ∈ e,
        1 / ((neighbors H (e.erase a)).card : ℚ)) =
          ((pairs.filter fun p => (neighbors H p).Nonempty).card : ℚ) := by
      rw [reindex (fun p _ => 1 / ((neighbors H p).card : ℚ))]
      simp only [sum_const, nsmul_eq_mul]
      rw [← sum_boole]
      apply sum_congr rfl
      intro p hp
      by_cases h : (neighbors H p).Nonempty
      · have hn : ((neighbors H p).card : ℚ) ≠ 0 := by
          exact_mod_cast (card_pos.mpr h).ne'
        simp [h, hn]
      · simp [not_nonempty_iff_eq_empty.mp h]
    have second : (∑ e ∈ H, ∑ a ∈ e,
        ∑ x ∈ (neighbors H (e.erase a)).erase a,
          1 / ((common H {a, x}).card : ℚ)) =
        2 * ((pairs.filter fun q => (common H q).Nonempty).card : ℚ) := by
      rw [reindex (fun p a => ∑ x ∈ (neighbors H p).erase a,
        1 / ((common H {a, x}).card : ℚ))]
      simp_rw [ordered _ (fun q => 1 / ((common H q).card : ℚ))]
      rw [← mul_sum]
      congr 1
      have hp (S : Finset V) : S.powersetCard 2 = pairs.filter fun q => q ⊆ S := by
        ext q
        simp [pairs, and_comm]
      simp_rw [hp, sum_filter]
      rw [sum_comm]
      have ht : (∑ q ∈ pairs, ∑ p ∈ pairs,
          if q ⊆ neighbors H p then 1 / ((common H q).card : ℚ) else 0) =
          ∑ q ∈ pairs, ((common H q).card : ℚ) *
            (1 / ((common H q).card : ℚ)) := by
        apply sum_congr rfl
        intro q hq
        rw [← sum_filter]
        simp [common]
      rw [ht, ← sum_boole]
      apply sum_congr rfl
      intro q hq
      by_cases h : (common H q).Nonempty
      · have hn : ((common H q).card : ℚ) ≠ 0 := by
          exact_mod_cast (card_pos.mpr h).ne'
        simp [h, hn]
      · simp [not_nonempty_iff_eq_empty.mp h]
    simp only [weight, sum_add_distrib, ← mul_sum]
    rw [first, second]
    ring

  have local_bound (e : Finset V) (he : e ∈ H) : (23/12 : ℚ) ≤ weight H e := by
    let f : e ≃ Fin 3 := Fintype.equivOfCardEq (by simp [hu e he])
    let color (v : V × V) : Fin 3 := if hv : v.1 ∈ e then f ⟨v.1,hv⟩ else 0
    have mem (v : V × V) (hv : v ∈ localVertices H e) : v.1 ∈ e := (mem_filter.mp hv).2.1
    have ce (v : V × V) (hv : v ∈ localVertices H e) : color v = f ⟨v.1,mem v hv⟩ := dif_pos _
    have hs : ∀ u ∈ localVertices H e, ∀ v ∈ localVertices H e, adjacent H e u v → adjacent H e v u := by
      intro u hu v hv h
      exact ⟨h.1.symm,h.2.1.symm,by simpa only [erase_right_comm, insert_comm] using h.2.2⟩
    have hc : ∀ u ∈ localVertices H e, ∀ v ∈ localVertices H e, adjacent H e u v → color u ≠ color v := by
      intro u hu v hv h heq
      rw [ce u hu,ce v hv] at heq
      exact h.1 (congrArg Subtype.val (f.injective heq))
    have hn (v : V × V) : ThreeColorReciprocal.neighborhood (localVertices H e) (adjacent H e) v =
        localNeighbors H e v := by
      ext w
      simp only [ThreeColorReciprocal.neighborhood, localNeighbors, mem_filter]
    have hm : ∀ v ∈ localVertices H e, ThreeColorReciprocal.Mixed (localVertices H e) (adjacent H e) color v →
        (ThreeColorReciprocal.neighborhood (localVertices H e) (adjacent H e) v).card = 2 := by
      intro v hv h
      unfold ThreeColorReciprocal.Mixed at h
      simp_rw [hn] at h ⊢
      apply (local_correspondence H hd e he (hu e he) v hv).2
      obtain ⟨w,hw,z,hz,hne⟩ := h
      refine ⟨w,hw,z,hz,?_⟩
      simp only [localNeighbors, mem_filter] at hw hz
      intro heq
      apply hne
      have hwe := mem w hw.1
      have hze := mem z hz.1
      rw [ce w hw.1, ce z hz.1]
      congr 1
      exact Subtype.ext heq
    have hg := ThreeColorReciprocal.reciprocal_bound (localVertices H e) (adjacent H e) color hs hc hm
    have fiber (a : e) :
        (localVertices H e).filter (fun v => color v=f a) =
        (localVertices H e).filter (fun v => v.1=a.val) := by
      ext v
      simp only [mem_filter]
      constructor
      · rintro ⟨hv,hc⟩
        rw [ce v hv] at hc
        exact ⟨hv,congrArg Subtype.val (f.injective hc)⟩
      · rintro ⟨hv,ha⟩
        refine ⟨hv,?_⟩
        rw [ce v hv]
        congr 1
        exact Subtype.ext ha
    have classes : (∑ i : Fin 3,
        1 / (((localVertices H e).filter fun v => color v=i).card + 1 : ℚ)) =
        ∑ a ∈ e, 1 / (((localVertices H e).filter fun v => v.1=a).card + 1 : ℚ) := by
      rw [← Equiv.sum_comp f (fun i : Fin 3 =>
        1 / (((localVertices H e).filter fun v => color v=i).card + 1 : ℚ))]
      simp_rw [fiber]
      exact sum_coe_sort e (fun a => 1 / (((localVertices H e).filter fun v => v.1=a).card + 1 : ℚ))
    unfold ThreeColorReciprocal.potential at hg
    rw [classes] at hg
    rw [local_weight H hd e he (hu e he)]
    simpa only [hn] using hg
  have lower := sum_le_sum (s := H) (fun e he => local_bound e he)
  rw [reciprocal_identity H hu] at lower
  simp only [sum_const, nsmul_eq_mul] at lower
  have hp : (pairs : Finset (Finset V)).card = (Fintype.card V).choose 2 := by
    simp [pairs]
  have hs := card_le_card (filter_subset (fun p => (neighbors H p).Nonempty) pairs)
  have ht := card_le_card (filter_subset (fun p => (common H p).Nonempty) pairs)
  rw [hp] at hs ht
  have hsq : (((pairs : Finset (Finset V)).filter fun p => (neighbors H p).Nonempty).card : ℚ) ≤
      ((Fintype.card V).choose 2 : ℚ) := by exact_mod_cast hs
  have htq : (((pairs : Finset (Finset V)).filter fun p => (common H p).Nonempty).card : ℚ) ≤
      ((Fintype.card V).choose 2 : ℚ) := by exact_mod_cast ht
  have result : (23 : ℚ) * H.card ≤ 24 * (Fintype.card V).choose 2 := by linarith
  exact_mod_cast result

end D5.S3.Combinatorics.Graph.DUFReciprocal
