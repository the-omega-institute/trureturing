/- GID: D5/S3/Combinatorics/Graph/DUFPacketOwnership
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFPacketOwnership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Exact marked exchanges force unique common-link packets and unique packet rows. -/

import D5.S3.Combinatorics.Graph.DUFStructure

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFPacketOwnership

open Finset DUFStructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership of a triple in a specified row of an actual common-link packet.
Disjointness of the row pair and triangle is forced by the common link. -/
def PacketRow (H : Finset (Finset V)) (q T : Finset V) (i : V) (e : Finset V) : Prop :=
  q.card = 2 ∧ T.card = 3 ∧ common H q = T.powersetCard 2 ∧
    i ∈ q ∧ ∃ p ∈ T.powersetCard 2, e = insert i p

/-- Either endpoint of an exact marked exchange has only the designated packet
and row. The intersection identifies its row element intrinsically. -/
theorem marked_endpoint_ownership (H : Finset (Finset V)) (u v a b c : V)
    (hd : [u, v, a, b, c].Pairwise (· ≠ ·))
    (hn : neighbors H {u, b} = {a, c})
    (hk : common H {a, c} = {{u, b}, {v, b}})
    (q T e : Finset V) (i : V)
    (he : e = {u, a, b} ∨ e = {u, b, c})
    (hr : PacketRow H q T i e) :
    q = {u, v} ∧ T = {a, b, c} ∧ i = u ∧ q ∩ e = {i} := by
  have first : ∀ (u v a b c : V),
      [u, v, a, b, c].Pairwise (· ≠ ·) →
      neighbors H {u, b} = {a, c} →
      common H {a, c} = {{u, b}, {v, b}} →
      PacketRow H q T i {u, a, b} →
      q = {u, v} ∧ T = {a, b, c} ∧ i = u := by
    clear hd hn hk hr he u v a b c e
    intro u v a b c hd hn hk hr
    have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
        (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [List.pairwise_cons] using hd
    obtain ⟨⟨huv, hua, hub, huc⟩, ⟨hva, hvb, hvc⟩, ⟨hab, hac⟩, hbc⟩ := hd'
    obtain ⟨hq, hT, hK, hiq, p, hp, hep⟩ := hr
    obtain ⟨hpT, hp2⟩ := mem_powersetCard.mp hp
    have extend (r : Finset V) (hr : r ∈ T.powersetCard 2) (j : V) (hj : j ∈ q) :
        j ∉ r ∧ insert j r ∈ H := by
      have hm : r ∈ common H q := hK.symm ▸ hr
      have := (mem_filter.mp hm).2 hj
      simpa only [neighbors, mem_filter, mem_univ, true_and] using this
    have hdis : Disjoint q T := by
      obtain ⟨r, s, t, hrs, hrt, hst, htri⟩ := card_eq_three.mp hT
      have hrsT : ({r, s} : Finset V) ∈ T.powersetCard 2 := by
        simp [htri, mem_powersetCard, hrs]
      have hrtT : ({r, t} : Finset V) ∈ T.powersetCard 2 := by
        simp [htri, mem_powersetCard, hrt]
      apply disjoint_left.mpr
      intro j hj hjT
      rw [htri] at hjT
      simp only [mem_insert, mem_singleton] at hjT
      rcases hjT with hjr | hjs | hjt
      · subst j; exact (extend {r, s} hrsT r hj).1 (by simp)
      · subst j; exact (extend {r, s} hrsT s hj).1 (by simp)
      · subst j; exact (extend {r, t} hrtT t hj).1 (by simp)
    have hiT : i ∉ T := fun h => disjoint_left.mp hdis hiq h
    have hip : i ∉ p := fun h => hiT (hpT h)
    obtain ⟨x, hx⟩ := card_eq_one.mp (show (q.erase i).card = 1 by
      rw [card_erase_of_mem hiq, hq])
    have hxi : x ≠ i := (mem_erase.mp (hx.symm ▸ mem_singleton_self x)).1
    have hxq : x ∈ q := (mem_erase.mp (hx.symm ▸ mem_singleton_self x)).2
    have hqx : q = {i, x} := by rw [← hx, insert_erase hiq]
    have hxT : x ∉ T := fun h => disjoint_left.mp hdis hxq h
    obtain ⟨y, hy⟩ := card_eq_one.mp (show (T \ p).card = 1 by
      rw [card_sdiff_of_subset hpT, hT, hp2])
    have hyT : y ∈ T := (mem_sdiff.mp (hy.symm ▸ mem_singleton_self y)).1
    have hyp : y ∉ p := (mem_sdiff.mp (hy.symm ▸ mem_singleton_self y)).2
    have hyi : y ≠ i := fun h => hiT (h ▸ hyT)
    have hTy : T = insert y p := by
      rw [← singleton_union, ← hy, sdiff_union_of_subset hpT]
    have hxe : x ∉ ({u, a, b} : Finset V) := by
      rw [hep]
      simp only [mem_insert, not_or]
      exact ⟨hxi, fun h => hxT (hpT h)⟩
    have hye : y ∉ ({u, a, b} : Finset V) := by rw [hep]; simp [hyi, hyp]
    have hie : i ∈ ({u, a, b} : Finset V) := by rw [hep]; simp
    have hpE : p = ({u, a, b} : Finset V).erase i := by rw [hep, erase_insert hip]
    simp only [mem_insert, mem_singleton] at hie
    rcases hie with hi | hi | hi
    · subst i
      have hpab : p = {a, b} := by simp [hpE, hua, hub]
      have hyc : y = c := by
        have hby : ({b, y} : Finset V) ∈ T.powersetCard 2 := by
          simp only [mem_powersetCard]
          constructor
          · simp [hTy, hpab, insert_subset_iff]
          · have : b ≠ y := by intro h; exact hye (by simp [← h])
            simp [this]
        have huy := (extend {b, y} hby u hiq).2
        have hyn : y ∈ neighbors H {u, b} := by
          simp only [neighbors, mem_filter, mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · have hyu : y ≠ u := fun h => hye (by simp [h])
            have hyb : y ≠ b := fun h => hye (by simp [h])
            simp [hyu, hyb]
          · convert huy using 1; ext z; simp [or_comm, or_left_comm]
        rw [hn] at hyn
        have hya : y ≠ a := fun h => hye (by simp [h])
        simpa [hya] using hyn
      subst y
      have hTabc : T = {a, b, c} := by rw [hTy, hpab]; ext; simp [or_comm, or_left_comm]
      have hxab := (extend p hp x hxq).2
      have hbcT : ({b, c} : Finset V) ∈ T.powersetCard 2 := by
        simp [hTabc, mem_powersetCard, hbc]
      have hxbc := (extend {b, c} hbcT x hxq).2
      have hbxK : ({b, x} : Finset V) ∈ common H {a, c} := by
        have hxb : x ≠ b := fun h => hxe (by simp [h])
        have hxa : x ≠ a := fun h => hxe (by simp [h])
        have hxc : x ≠ c := fun h => hxT (by simp [hTabc, h])
        simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
          insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
        refine ⟨by simp [hxb.symm], ?_, ?_⟩
        · exact ⟨by simp [hab, hxa.symm], by
            rw [hpab] at hxab
            convert hxab using 1; ext z; simp [or_comm, or_left_comm]⟩
        · exact ⟨by simp [Ne.symm hbc, hxc.symm], by
            convert hxbc using 1; ext z; simp [or_comm, or_left_comm]⟩
      rw [hk] at hbxK
      simp only [mem_insert, mem_singleton] at hbxK
      have hxv : x = v := by
        have hxm : x ∈ ({b, x} : Finset V) := by simp
        rcases hbxK with hh | hh <;> rw [hh] at hxm
        · simp only [mem_insert, mem_singleton] at hxm
          rcases hxm with hh | hh <;> exact False.elim (hxe (by simp [hh]))
        · have hxb : x ≠ b := fun h => hxe (by simp [h])
          simpa [hxb] using hxm
      exact ⟨by simpa [hxv] using hqx, hTabc, rfl⟩
    · subst i
      have hpub : p = {u, b} := by
        rw [hpE, erase_insert_of_ne hua, erase_insert (by simp [hab])]
      have hxn : x ∈ neighbors H {u, b} := by
        have hx := extend p hp x hxq
        simpa [neighbors, hpub] using hx
      rw [hn] at hxn
      have hxa : x ≠ a := fun h => hxe (by simp [h])
      have hxc : x = c := by simpa [hxa] using hxn
      have hqac : q = {a, c} := by simpa [hxc] using hqx
      have hcard := congrArg card (hK.symm.trans (by rw [hqac, hk]))
      rw [card_powersetCard, hT] at hcard
      have hne : ({u, b} : Finset V) ≠ {v, b} := by
        intro hh
        have : u ∈ ({v, b} : Finset V) := hh ▸ (by simp)
        simp [huv, hub] at this
      simp [hne] at hcard
    · subst i
      have hpua : p = {u, a} := by
        rw [hpE, erase_insert_of_ne hub, erase_insert_of_ne hab, erase_singleton]
        simp
      have hyc : y = c := by
        have huyT : ({u, y} : Finset V) ∈ T.powersetCard 2 := by
          have huy : u ≠ y := fun h => hye (by simp [← h])
          simp [mem_powersetCard, hTy, hpua, huy, insert_subset_iff]
        have hbuy := (extend {u, y} huyT b hiq).2
        have hyn : y ∈ neighbors H {u, b} := by
          have hyu : y ≠ u := fun h => hye (by simp [h])
          have hyb : y ≠ b := fun h => hye (by simp [h])
          simp only [neighbors, mem_filter, mem_univ, true_and]
          exact ⟨by simp [hyu, hyb], by
            convert hbuy using 1; ext z; simp [or_comm, or_left_comm]⟩
        rw [hn] at hyn
        have hya : y ≠ a := fun h => hye (by simp [h])
        simpa [hya] using hyn
      subst y
      have hxu := (extend p hp x hxq).2
      have hucT : ({u, c} : Finset V) ∈ T.powersetCard 2 := by
        simp [mem_powersetCard, hTy, hpua, huc, insert_subset_iff]
      have hxuc := (extend {u, c} hucT x hxq).2
      have huxK : ({u, x} : Finset V) ∈ common H {a, c} := by
        have hxu' : x ≠ u := fun h => hxe (by simp [h])
        have hxa : x ≠ a := fun h => hxe (by simp [h])
        have hxc : x ≠ c := fun h => hxT (by simp [hTy, h])
        simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
          insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
        refine ⟨by simp [hxu'.symm], ?_, ?_⟩
        · exact ⟨by simp [Ne.symm hua, hxa.symm], by
            rw [hpua] at hxu
            convert hxu using 1; ext z; simp [or_comm, or_left_comm]⟩
        · exact ⟨by simp [Ne.symm huc, hxc.symm], by
            convert hxuc using 1; ext z; simp [or_comm, or_left_comm]⟩
      rw [hk] at huxK
      simp only [mem_insert, mem_singleton] at huxK
      rcases huxK with hh | hh
      · have : x ∈ ({u, b} : Finset V) := hh ▸ (by simp)
        exact False.elim (hxe (by simp only [mem_insert, mem_singleton] at this ⊢; tauto))
      · have : u ∈ ({v, b} : Finset V) := hh ▸ (by simp)
        simp [huv, hub] at this
  have howner : q = {u, v} ∧ T = {a, b, c} ∧ i = u := by
    rcases he with rfl | rfl
    · exact first u v a b c hd hn hk hr
    · have hd' : [u, v, c, b, a].Pairwise (· ≠ ·) := by
        clear first hr hn hk
        simp [List.pairwise_cons] at hd ⊢
        grind
      have hh := first u v c b a hd' (by simpa [pair_comm] using hn)
        (by simpa [pair_comm] using hk) (by rw [pair_comm c b]; exact hr)
      refine ⟨hh.1, hh.2.1.trans ?_, hh.2.2⟩
      ext z; simp [or_comm, or_left_comm]
  obtain ⟨rfl, rfl, rfl⟩ := howner
  clear first hr hn hk
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [List.pairwise_cons] at hd
  rcases he with rfl | rfl <;> ext z <;> simp only [mem_inter, mem_insert, mem_singleton] <;>
    grind

end D5.S3.Combinatorics.Graph.DUFPacketOwnership
