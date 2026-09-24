/- GID: D5/S3/Combinatorics/Graph/DUFRowPayment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFRowPayment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sole-mark deficits are paid by recipient debt; multiple marks pay internally. -/

import D5.S3.Combinatorics.Graph.DUFRowGeometry
import D5.S3.Combinatorics.Graph.ColoredSingletonLeaf

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph
open DUFStructure DUFReciprocal DUFPacketOwnership DUFLocalPackets DUFMarkedStars
open ColoredReciprocalDeletion
open DUFRowGeometry

namespace D5.S3.Combinatorics.Graph.DUFRowPayment

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def rowDelta (H : Finset (Finset V)) (r : Row V) : ℚ :=
  max (2 * ((internalGroup H r).card : ℚ) - ∑ e ∈ internalGroup H r, weight H e) 0

/-- Actual one-mark and multiple-mark row payment inequalities. -/
theorem result :
    (∀ (H : Finset (Finset V)) (hd : DUF H)
    (r : Row V) (hr : Valid H r) (hone : (marks H r).card = 1),
      ∃ b ∈ marks H r, marks H r = {b} ∧
      (internalGroup H r).card = 2 ∧ recipient r b ∉ internalGroup H r ∧
      recipient r b ∈ H ∧ ∃ he3 : (recipient r b).card = 3,
      ∃ w : U H (recipient r b), w.val = assigned r ∧
      ColoredReciprocalDeletion.Mixed (graph H (recipient r b))
        (coloring H (recipient r b) he3) w ∧
      rowDelta H r ≤ max (ColoredReciprocalDeletion.debt (graph H (recipient r b)) w) 0 ∧
      (0 < rowDelta H r → 0 < ColoredReciprocalDeletion.debt (graph H (recipient r b)) w ∧
        rowDelta H r ≤ ColoredReciprocalDeletion.debt (graph H (recipient r b)) w))
    ∧ (∀ (H : Finset (Finset V)) (hd : DUF H)
    (r : Row V) (hr : Valid H r) (hmany : 2 ≤ (marks H r).card),
      (6 : ℚ) ≤ ∑ e ∈ rowMembers r, weight H e ∧
    (6 : ℚ) ≤ ∑ e ∈ internalGroup H r, weight H e ∧ rowDelta H r = 0) := by
  obtain ⟨color_eq_iff, neighbor_transport, degree_transport, mixed_iff, mixed_degree,
    potential_transport, leaf_iff, row_disjoint, row_i_notMem, row_members_facts, recipient_mem,
    internal_subset, internal_zero, internal_one, internal_many, other_spec, internal_owner,
    internal_disjoint, assigned_actual, assigned_mixed, assigned_injective,
    configuration_coverage⟩ :=
    DUFRowGeometry.result (V := V)
  have packet_geometry (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdi : [u, v, a, b, c].Pairwise (· ≠ ·))
      (hp : common H {u, v} = ({a, b, c} : Finset V).powersetCard 2) :
      ({u, a, b} : Finset V) ∈ H ∧ ({u, a, b} : Finset V).card = 3 ∧
      (u, v) ∈ localVertices H {u, a, b} ∧
      (a, c) ∈ localVertices H {u, a, b} ∧
      (b, c) ∈ localVertices H {u, a, b} ∧
      localNeighbors H {u, a, b} (u, v) = {(a, c), (b, c)} := by
    have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
        (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [List.pairwise_cons] using hdi
    obtain ⟨⟨huv, hua, hub, huc⟩, ⟨hva, hvb, hvc⟩, ⟨hab, hac⟩, hbc⟩ := hd'
    have extend (p : Finset V) (hpt : p ∈ ({a, b, c} : Finset V).powersetCard 2)
        (i : V) (hi : i ∈ ({u, v} : Finset V)) : i ∉ p ∧ insert i p ∈ H := by
      have hm : p ∈ common H {u, v} := hp.symm ▸ hpt
      simpa only [neighbors, mem_filter, mem_univ, true_and] using (mem_filter.mp hm).2 hi
    have huab := extend {a,b} (by simp [mem_powersetCard, hab]) u (by simp)
    have hvab := extend {a,b} (by simp [mem_powersetCard, hab]) v (by simp)
    have huac := extend {a,c} (by simp [mem_powersetCard, hac]) u (by simp)
    have hvac := extend {a,c} (by simp [mem_powersetCard, hac]) v (by simp)
    have hubc := extend {b,c} (by simp [mem_powersetCard, hbc]) u (by simp)
    have hvbc := extend {b,c} (by simp [mem_powersetCard, hbc]) v (by simp)
    have he3 : ({u,a,b} : Finset V).card = 3 := by simp [hua,hub,hab]
    have hw : (u,v) ∈ localVertices H {u,a,b} := by
      simp only [localVertices, mem_filter, mem_univ, true_and]
      exact ⟨by simp, by simp [huv.symm,hva,hvb], by simpa [hua,hub] using hvab.2⟩
    have hl : (a,c) ∈ localNeighbors H {u,a,b} (u,v) := by
      simp only [localNeighbors,localVertices,adjacent,mem_filter,mem_univ,true_and]
      refine ⟨⟨by simp, by simp [huc.symm,hac.symm,hbc.symm], ?_⟩, hua,hvc,?_⟩
      · convert hubc.2 using 1
        ext t
        simp [hua,hab,erase_insert_of_ne,or_comm,or_left_comm]
      · convert hvbc.2 using 1
        ext t
        simp [hua,hub,hab,or_comm]
    have hz : (b,c) ∈ localNeighbors H {u,a,b} (u,v) := by
      simp only [localNeighbors,localVertices,adjacent,mem_filter,mem_univ,true_and]
      refine ⟨⟨by simp, by simp [huc.symm,hac.symm,hbc.symm], ?_⟩, hub,hvc,?_⟩
      · convert huac.2 using 1
        ext t
        simp [hub,hab,erase_insert_of_ne,or_comm,or_left_comm]
      · convert hvac.2 using 1
        ext t
        simp [hua,hub,hab,erase_insert_of_ne,or_comm]
    have hlV : (a,c) ∈ localVertices H {u,a,b} := by
      have h := hl
      simp only [localNeighbors,mem_filter] at h
      exact h.1
    have hzV : (b,c) ∈ localVertices H {u,a,b} := by
      have h := hz
      simp only [localNeighbors,mem_filter] at h
      exact h.1
    refine ⟨huab.2,he3,hw,hlV,hzV,?_⟩
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨hl,hz⟩
    · have hc := (local_correspondence H hd {u,a,b} huab.2 he3 (u,v) hw).2
        ⟨(a,c),hl,(b,c),hz,hab⟩
      simp [hc,hab]
  have graph_neighbors_pair (H : Finset (Finset V)) (e : Finset V)
      (w l z : U H e) (h : localNeighbors H e w.val = {l.val,z.val}) :
      (graph H e).neighborFinset w = {l,z} := by
    apply (Finset.image_injective Subtype.val_injective)
    simpa only [neighbor_transport, image_insert, image_singleton] using h
  have marked_leaf (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdi : [u,v,a,b,c].Pairwise (· ≠ ·))
      (hn : neighbors H {u,b} = {a,c})
      (hk : common H {a,c} = {{u,b},{v,b}})
      (e : Finset V) (heq : e = {u,a,b}) (he : e ∈ H) (he3 : e.card = 3)
      (w l : U H e) (hw : w.val = (u,v)) (hl : l.val = (a,c))
      (hwl : (graph H e).Adj w l) :
      (univ.filter fun x => coloring H e he3 x = coloring H e he3 l) = {l} ∧
      (graph H e).neighborFinset l = {w} := by
    subst e
    have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
        (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [List.pairwise_cons] using hdi
    obtain ⟨⟨huv,hua,hub,huc⟩,⟨hva,hvb,hvc⟩,⟨hab,hac⟩,hbc⟩ := hd'
    constructor
    · ext x
      simp only [mem_filter,mem_univ,true_and,color_eq_iff,mem_singleton]
      constructor
      · intro hx
        apply Subtype.ext
        have hxa : x.val.1 = a := by simpa only [hl] using hx
        have hV := (mem_filter.mp x.property).2
        have hN : x.val.2 ∈ neighbors H {u,b} := by
          simp only [neighbors,mem_filter,mem_univ,true_and]
          refine ⟨fun h => hV.2.1 ?_, ?_⟩
          · simp only [mem_insert,mem_singleton] at h ⊢; tauto
          · simpa [hxa,hua,hab,erase_insert_of_ne] using hV.2.2
        rw [hn] at hN
        have hxc : x.val.2 = c := by
          simp only [mem_insert,mem_singleton] at hN
          exact hN.resolve_left (fun h => hV.2.1 (by simp [h]))
        rw [hl]; exact Prod.ext hxa hxc
      · rintro rfl; rfl
    · apply (leaf_iff H {u,a,b} w l hwl).mp
      have hc := (local_correspondence H hd {u,a,b} he he3 l.val l.property).1
      rw [hl, hk] at hc
      have hne : ({u,b} : Finset V) ≠ {v,b} := by
        intro h
        have hm : u ∈ ({v,b} : Finset V) := h ▸ (by simp)
        simp [huv,hub] at hm
      simp only [card_pair hne] at hc
      rw [degree_transport,hl]
      omega
  have pointwise_lower (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) : (23/12 : ℚ) ≤ weight H e := by
    let G := graph H e
    let col := coloring H e he3
    have hN (x : U H e) : ThreeColorReciprocal.neighborhood univ G.Adj x = G.neighborFinset x := by
      ext y; simp [ThreeColorReciprocal.neighborhood]
    have hm : ∀ x ∈ (univ : Finset (U H e)),
        ThreeColorReciprocal.Mixed univ G.Adj col x →
        (ThreeColorReciprocal.neighborhood univ G.Adj x).card = 2 := by
      intro x _ hx
      obtain ⟨y,hy,z,hz,hc⟩ := hx
      simp only [hN,SimpleGraph.mem_neighborFinset] at hy hz
      rw [hN,SimpleGraph.card_neighborFinset_eq_degree]
      exact mixed_degree H hd e he he3 x ⟨y,z,hy,hz,hc⟩
    have hb := ThreeColorReciprocal.reciprocal_bound univ G.Adj col
      (by intro x _ y _ h; exact h.symm)
      (by intro x _ y _ h; exact col.valid h) hm
    change (23/12 : ℚ) ≤ ThreeColorReciprocal.potential univ G.Adj col at hb
    have ht : ThreeColorReciprocal.potential univ G.Adj col =
        ColoredReciprocalDeletion.potential G col := by
      simp only [ThreeColorReciprocal.potential,ColoredReciprocalDeletion.potential,hN,
        SimpleGraph.card_neighborFinset_eq_degree]
    rw [ht,potential_transport H hd e he he3] at hb
    exact hb
  have endpoint_estimate (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdi : [u,v,a,b,c].Pairwise (· ≠ ·))
      (hp : common H {u,v} = ({a,b,c} : Finset V).powersetCard 2)
      (hn : neighbors H {u,b} = {a,c}) (hk : common H {a,c} = {{u,b},{v,b}}) :
      (23/12 : ℚ) + 1 / (2 * ((common H {b,c}).card : ℚ)) ≤ weight H {u,a,b} := by
    obtain ⟨he,he3,hw,hl,hz,hN⟩ := packet_geometry H hd u v a b c hdi hp
    let w : U H {u,a,b} := ⟨(u,v),hw⟩
    let l : U H {u,a,b} := ⟨(a,c),hl⟩
    let z : U H {u,a,b} := ⟨(b,c),hz⟩
    let col := coloring H {u,a,b} he3
    have hN' := graph_neighbors_pair H {u,a,b} w l z hN
    have hwl : (graph H {u,a,b}).Adj w l := by
      apply ((graph H {u,a,b}).mem_neighborFinset w l).mp
      rw [hN']; simp
    have hleaf := marked_leaf H hd u v a b c hdi hn hk {u,a,b} rfl he he3 w l rfl rfl hwl
    have hd' : u ≠ a ∧ u ≠ b ∧ a ≠ b := by
      simp [List.pairwise_cons] at hdi; tauto
    have hca : col w ≠ col l := fun h => hd'.1 ((color_eq_iff H _ he3 w l).mp h)
    have hcb : col w ≠ col z := fun h => hd'.2.1 ((color_eq_iff H _ he3 w z).mp h)
    have hab : col l ≠ col z := fun h => hd'.2.2 ((color_eq_iff H _ he3 l z).mp h)
    have hb := ColoredSingletonLeaf.singleton_leaf_reciprocal_bound (graph H {u,a,b}) col
      (by intro x y h; exact col.valid h) w l z hca hcb hab hleaf.1 hleaf.2 hN'
    let k := (univ.filter fun x => col x = col w).card - 1
    have hk0 : (0 : ℚ) ≤ k / (2 * ((k : ℚ)+1) * ((k : ℚ)+2)) := by positivity
    have ht := potential_transport H hd {u,a,b} he he3
    change ColoredReciprocalDeletion.potential (graph H {u,a,b}) col = weight H {u,a,b} at ht
    change (23/12 : ℚ) + k / (2 * ((k : ℚ)+1) * ((k : ℚ)+2)) +
      1 / (2 * (((graph H {u,a,b}).degree z : ℚ)+1)) ≤
      ColoredReciprocalDeletion.potential (graph H {u,a,b}) col at hb
    have hdeg := (local_correspondence H hd {u,a,b} he he3 (b,c) hz).1
    have hdeg' : ((graph H {u,a,b}).degree z : ℚ)+1 = (common H {b,c}).card := by
      rw [degree_transport]
      exact_mod_cast hdeg
    rw [hdeg',ht] at hb
    linarith only [hb,hk0]
  have coordinate_charge (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdi : [u,v,a,b,c].Pairwise (· ≠ ·))
      (hp : common H {u,v} = ({a,b,c} : Finset V).powersetCard 2)
      (hn : neighbors H {u,b} = {a,c}) (hk : common H {a,c} = {{u,b},{v,b}}) :
      ({u,a,b} : Finset V) ∈ H ∧ ({u,a,b} : Finset V).card = 3 ∧
      ({u,b,c} : Finset V) ∈ H ∧ ({u,b,c} : Finset V).card = 3 ∧
      ({u,a,c} : Finset V) ∈ H ∧ ∃ he3 : ({u,a,c} : Finset V).card = 3,
      ∃ w : U H {u,a,c}, w.val = (u,v) ∧
      ColoredReciprocalDeletion.Mixed (graph H {u,a,c}) (coloring H {u,a,c} he3) w ∧
      4 - weight H {u,a,b} - weight H {u,b,c} ≤ ColoredReciprocalDeletion.debt (graph H {u,a,c}) w ∧
      max (4 - weight H {u,a,b} - weight H {u,b,c}) 0 ≤
        max (ColoredReciprocalDeletion.debt (graph H {u,a,c}) w) 0 ∧
      (0 < max (4 - weight H {u,a,b} - weight H {u,b,c}) 0 →
        0 < ColoredReciprocalDeletion.debt (graph H {u,a,c}) w ∧
        max (4 - weight H {u,a,b} - weight H {u,b,c}) 0 ≤
          ColoredReciprocalDeletion.debt (graph H {u,a,c}) w) := by
    have hswap : [u,v,c,b,a].Pairwise (· ≠ ·) := by
      simp [List.pairwise_cons] at hdi ⊢; grind
    have hrec : [u,v,a,c,b].Pairwise (· ≠ ·) := by
      simp [List.pairwise_cons] at hdi ⊢; grind
    have htri : ({c,b,a} : Finset V) = {a,b,c} := by ext x; simp [or_comm,or_left_comm]
    have hp' : common H {u,v} = ({c,b,a} : Finset V).powersetCard 2 := by rw [htri]; exact hp
    have hrecp : common H {u,v} = ({a,c,b} : Finset V).powersetCard 2 := by
      rw [pair_comm c b]; exact hp
    have h1 := endpoint_estimate H hd u v a b c hdi hp hn hk
    have h2 := endpoint_estimate H hd u v c b a hswap hp'
      (by simpa only [pair_comm] using hn) (by simpa only [pair_comm] using hk)
    rw [pair_comm c b] at h2
    obtain ⟨he1,he13,_⟩ := packet_geometry H hd u v a b c hdi hp
    obtain ⟨he2,he23,_⟩ := packet_geometry H hd u v c b a hswap hp'
    rw [pair_comm c b] at he2 he23
    obtain ⟨he3,he33,hw,hr,hz,hN⟩ := packet_geometry H hd u v a c b hrec hrecp
    let w : U H {u,a,c} := ⟨(u,v),hw⟩
    let r : U H {u,a,c} := ⟨(a,b),hr⟩
    let z : U H {u,a,c} := ⟨(c,b),hz⟩
    have hac : a ≠ c := by simp [List.pairwise_cons] at hdi; tauto
    have hrz : r ≠ z := fun h => hac (congrArg (fun x : U H {u,a,c} => x.val.1) h)
    have hN' := graph_neighbors_pair H {u,a,c} w r z hN
    have hm : ColoredReciprocalDeletion.Mixed (graph H {u,a,c}) (coloring H {u,a,c} he33) w := by
      apply (mixed_iff H {u,a,c} he33 w).mpr
      refine ⟨(a,b),?_,(c,b),?_,hac⟩ <;> rw [hN] <;> simp
    have hdr := (local_correspondence H hd {u,a,c} he3 he33 (a,b) hr).1
    have hdz := (local_correspondence H hd {u,a,c} he3 he33 (c,b) hz).1
    have hdr' : ((graph H {u,a,c}).degree r : ℚ)+1 = (common H {b,a}).card := by
      rw [degree_transport]
      exact_mod_cast (by simpa only [pair_comm a b] using hdr)
    have hdz' : ((graph H {u,a,c}).degree z : ℚ)+1 = (common H {b,c}).card := by
      rw [degree_transport]
      exact_mod_cast (by simpa only [pair_comm c b] using hdz)
    have hdebt : ColoredReciprocalDeletion.debt (graph H {u,a,c}) w =
        1/6 - 1/(2*((common H {b,a}).card : ℚ)) - 1/(2*((common H {b,c}).card : ℚ)) := by
      unfold ColoredReciprocalDeletion.debt
      rw [hN',sum_pair hrz,hdr',hdz']
      ring
    have hpay : 4 - weight H {u,a,b} - weight H {u,b,c} ≤
        ColoredReciprocalDeletion.debt (graph H {u,a,c}) w := by rw [hdebt]; linarith only [h1,h2]
    refine ⟨he1,he13,he2,he23,he3,he33,w,rfl,hm,hpay,max_le_max hpay le_rfl,?_⟩
    intro hpos
    have hraw : 0 < 4 - weight H {u,a,b} - weight H {u,b,c} :=
      (lt_max_iff.mp hpos).resolve_right (lt_irrefl _)
    exact ⟨hraw.trans_le hpay, by rw [max_eq_left hraw.le]; exact hpay⟩
  have two_marks_central (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdi : [u,v,a,b,c].Pairwise (· ≠ ·))
      (hp : common H {u,v} = ({a,b,c} : Finset V).powersetCard 2)
      (hnb : neighbors H {u,b} = {a,c}) (hkb : common H {a,c} = {{u,b},{v,b}})
      (hna : neighbors H {u,a} = {b,c}) (hka : common H {b,c} = {{u,a},{v,a}}) :
      (13/6 : ℚ) ≤ weight H {u,a,b} := by
    obtain ⟨he,he3,hw,hl,hz,hN⟩ := packet_geometry H hd u v a b c hdi hp
    let w : U H {u,a,b} := ⟨(u,v),hw⟩
    let l : U H {u,a,b} := ⟨(a,c),hl⟩
    let z : U H {u,a,b} := ⟨(b,c),hz⟩
    let col := coloring H {u,a,b} he3
    have hN' := graph_neighbors_pair H {u,a,b} w l z hN
    have hwl : (graph H {u,a,b}).Adj w l := by
      apply ((graph H {u,a,b}).mem_neighborFinset w l).mp
      rw [hN']; simp
    have hwz : (graph H {u,a,b}).Adj w z := by
      apply ((graph H {u,a,b}).mem_neighborFinset w z).mp
      rw [hN']; simp
    have hleaf := marked_leaf H hd u v a b c hdi hnb hkb {u,a,b} rfl he he3 w l rfl rfl hwl
    have hswap : [u,v,b,a,c].Pairwise (· ≠ ·) := by
      simp [List.pairwise_cons] at hdi ⊢; grind
    have heq : ({u,b,a} : Finset V) = {u,a,b} := by rw [pair_comm b a]
    have hzleaf' := marked_leaf H hd u v b a c hswap hna hka
      {u,a,b} heq.symm he he3 w z rfl rfl hwz
    have hd' : u ≠ a ∧ u ≠ b ∧ a ≠ b := by
      simp [List.pairwise_cons] at hdi; tauto
    have hca : col w ≠ col l := fun h => hd'.1 ((color_eq_iff H _ he3 w l).mp h)
    have hcb : col w ≠ col z := fun h => hd'.2.1 ((color_eq_iff H _ he3 w z).mp h)
    have hab : col l ≠ col z := fun h => hd'.2.2 ((color_eq_iff H _ he3 l z).mp h)
    have hb := (ColoredSingletonLeaf.two_singleton_leaves_internal_payment (graph H {u,a,b}) col
      (by intro x y h; exact col.valid h) w l z hca hcb hab hleaf.1 hzleaf'.1
      hleaf.2 hzleaf'.2 hN').2
    change (13/6 : ℚ) ≤ ColoredReciprocalDeletion.potential (graph H {u,a,b}) col at hb
    rw [potential_transport H hd {u,a,b} he he3] at hb
    exact hb
  have mark_coordinates (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      (b : V) (hb : b ∈ marks H r) :
      ∃ a c : V, [r.i,other r.q r.i,a,b,c].Pairwise (· ≠ ·) ∧ r.T = {a,b,c} ∧
        neighbors H {r.i,b} = {a,c} ∧
        common H {a,c} = {{r.i,b},{other r.q r.i,b}} := by
    obtain ⟨hbT,hn,hk⟩ := mem_filter.mp hb
    obtain ⟨a,c,hac,hacset⟩ := card_eq_two.mp (show (r.T.erase b).card = 2 by
      rw [card_erase_of_mem hbT,hr.2.1])
    have haE : a ∈ r.T.erase b := hacset.symm ▸ (by simp)
    have hcE : c ∈ r.T.erase b := hacset.symm ▸ (by simp)
    have hab := (mem_erase.mp haE).1
    have hcb := (mem_erase.mp hcE).1
    have hT : r.T = {a,b,c} := by
      rw [← insert_erase hbT,hacset,insert_comm b a]
    have ho := other_spec H r hr
    have hdis := disjoint_left.mp (row_disjoint H r hr)
    have hi : r.i ∉ r.T := row_i_notMem H r hr
    have hv : other r.q r.i ∉ r.T := fun h => hdis ho.2.1 h
    have hia : r.i ≠ a := fun h => hi (h.symm ▸ mem_of_mem_erase haE)
    have hib : r.i ≠ b := fun h => hi (h.symm ▸ hbT)
    have hic : r.i ≠ c := fun h => hi (h.symm ▸ mem_of_mem_erase hcE)
    have hva : other r.q r.i ≠ a := fun h => hv (h.symm ▸ mem_of_mem_erase haE)
    have hvb : other r.q r.i ≠ b := fun h => hv (h.symm ▸ hbT)
    have hvc : other r.q r.i ≠ c := fun h => hv (h.symm ▸ mem_of_mem_erase hcE)
    refine ⟨a,c,?_,hT,?_,?_⟩
    · simp [List.pairwise_cons,ho.1.symm,hia,hib,hic,hva,hvb,hvc,hab,hac,hcb.symm]
    · simpa only [hacset] using hn
    · rw [hacset,ho.2.2,image_insert,image_singleton] at hk
      exact hk
  have row_coordinates (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      (a b c : V) (hT : r.T = {a,b,c})
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      rowMembers r = {{r.i,a,b},{r.i,b,c},{r.i,a,c}} ∧
      recipient r b = {r.i,a,c} ∧
      (rowMembers r).erase (recipient r b) = {{r.i,a,b},{r.i,b,c}} := by
    have hi := row_i_notMem H r hr
    have hia : r.i ≠ a := fun h => hi (by simp [hT,h])
    have hib : r.i ≠ b := fun h => hi (by simp [hT,h])
    have hic : r.i ≠ c := fun h => hi (by simp [hT,h])
    have hp : ({a,b,c} : Finset V).powersetCard 2 = {{a,b},{b,c},{a,c}} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · intro p hp
        simp only [mem_insert,mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> simp [mem_powersetCard,hab,hac,hbc]
      · have habbc : ({a,b} : Finset V) ≠ {b,c} := by
          intro h; have := h ▸ (mem_insert_self a {b}); simp [hab,hac] at this
        have habac : ({a,b} : Finset V) ≠ {a,c} := by
          intro h; have := h ▸ (show b ∈ ({a,b} : Finset V) by simp); simp [hab.symm,hbc] at this
        have hbcac : ({b,c} : Finset V) ≠ {a,c} := by
          intro h; have := h ▸ (mem_insert_self b {c}); simp [hab.symm,hbc] at this
        simp [card_powersetCard,hab,hac,hbc,habbc,habac,hbcac]
    have hm : rowMembers r = {{r.i,a,b},{r.i,b,c},{r.i,a,c}} := by
      simp only [rowMembers,hT,hp,image_insert,image_singleton]
    have hrb : recipient r b = {r.i,a,c} := by
      simp [recipient,hT,hab,hbc,erase_insert_of_ne]
    have h13 : ({r.i,a,b} : Finset V) ≠ {r.i,a,c} := by
      intro h; have := h ▸ (show b ∈ ({r.i,a,b} : Finset V) by simp)
      simp [hib.symm,hab.symm,hbc] at this
    have h23 : ({r.i,b,c} : Finset V) ≠ {r.i,a,c} := by
      intro h; have := h ▸ (show b ∈ ({r.i,b,c} : Finset V) by simp)
      simp [hib.symm,hab.symm,hbc] at this
    exact ⟨hm,hrb,by simp [hm,hrb,h13,h23,erase_insert_of_ne]⟩
  have actual_mark_charge (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) (b : V) (hb : b ∈ marks H r) :
      recipient r b ∈ H ∧ ∃ he3 : (recipient r b).card = 3,
      ∃ w : U H (recipient r b), w.val = assigned r ∧
        ColoredReciprocalDeletion.Mixed (graph H (recipient r b))
          (coloring H (recipient r b) he3) w ∧
        4 - (∑ e ∈ (rowMembers r).erase (recipient r b), weight H e) ≤
          ColoredReciprocalDeletion.debt (graph H (recipient r b)) w ∧
        max (4 - (∑ e ∈ (rowMembers r).erase (recipient r b), weight H e)) 0 ≤
          max (ColoredReciprocalDeletion.debt (graph H (recipient r b)) w) 0 ∧
        (0 < max (4 - (∑ e ∈ (rowMembers r).erase (recipient r b), weight H e)) 0 →
          0 < ColoredReciprocalDeletion.debt (graph H (recipient r b)) w ∧
          max (4 - (∑ e ∈ (rowMembers r).erase (recipient r b), weight H e)) 0 ≤
            ColoredReciprocalDeletion.debt (graph H (recipient r b)) w) := by
    obtain ⟨a,c,hdi,hT,hn,hk⟩ := mark_coordinates H r hr b hb
    have hp : common H {r.i,other r.q r.i} = ({a,b,c} : Finset V).powersetCard 2 := by
      rw [← (other_spec H r hr).2.2,← hT]; exact hr.2.2.1
    have hh := coordinate_charge H hd r.i (other r.q r.i) a b c hdi hp hn hk
    have hd' : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ r.i := by
      simp [List.pairwise_cons] at hdi; grind
    have hcoords := row_coordinates H r hr a b c hT hd'.1 hd'.2.1 hd'.2.2.1
    have h12 : ({r.i,a,b} : Finset V) ≠ {r.i,b,c} := by
      intro h; have hm := h ▸ (show a ∈ ({r.i,a,b} : Finset V) by simp)
      simp [hd'.2.2.2,hd'.1,hd'.2.1] at hm
    have hs : (∑ e ∈ (rowMembers r).erase (recipient r b), weight H e) =
        weight H {r.i,a,b} + weight H {r.i,b,c} := by
      rw [hcoords.2.2,sum_pair h12]
    rw [hs,hcoords.2.1]
    simpa only [assigned,sub_add_eq_sub_sub] using hh.2.2.2.2
  have sole_mark_payment (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) (hone : (marks H r).card = 1) :
      ∃ b ∈ marks H r, marks H r = {b} ∧
        (internalGroup H r).card = 2 ∧ recipient r b ∉ internalGroup H r ∧
        recipient r b ∈ H ∧ ∃ he3 : (recipient r b).card = 3,
        ∃ w : U H (recipient r b), w.val = assigned r ∧
        ColoredReciprocalDeletion.Mixed (graph H (recipient r b))
          (coloring H (recipient r b) he3) w ∧
        rowDelta H r ≤ max (ColoredReciprocalDeletion.debt (graph H (recipient r b)) w) 0 ∧
        (0 < rowDelta H r → 0 < ColoredReciprocalDeletion.debt (graph H (recipient r b)) w ∧
          rowDelta H r ≤ ColoredReciprocalDeletion.debt (graph H (recipient r b)) w) := by
    obtain ⟨b,hb,hm,hg,_,hc,ho⟩ := internal_one H r hr hone
    obtain ⟨he,he3,w,hw,hwm,_,hpay,hpos⟩ := actual_mark_charge H hd r hr b hb
    have hδ : rowDelta H r = max (4 - ∑ e ∈ (rowMembers r).erase (recipient r b), weight H e) 0 := by
      unfold rowDelta
      rw [hc,hg]
      norm_num
    exact ⟨b,hb,hm,hc,ho,he,he3,w,hw,hwm,by rw [hδ]; exact hpay,
      by rw [hδ]; exact hpos⟩
  have multi_mark_payment (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) (hmany : 2 ≤ (marks H r).card) :
      (6 : ℚ) ≤ ∑ e ∈ rowMembers r, weight H e ∧
      (6 : ℚ) ≤ ∑ e ∈ internalGroup H r, weight H e ∧ rowDelta H r = 0 := by
    obtain ⟨b,hb,a,ha,hba⟩ := one_lt_card.mp (show 1 < (marks H r).card by omega)
    have hbT := (mem_filter.mp hb).1
    have haT := (mem_filter.mp ha).1
    have hab : a ≠ b := hba.symm
    have hpab : ({a,b} : Finset V) ⊆ r.T := by simp [insert_subset_iff,haT,hbT]
    obtain ⟨c,hc⟩ := card_eq_one.mp (show (r.T \ {a,b}).card = 1 by
      rw [card_sdiff_of_subset hpab,hr.2.1]; simp [hab])
    have hcT := (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).1
    have hcab := (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).2
    have hac : a ≠ c := by intro h; apply hcab; simp [← h]
    have hbc : b ≠ c := by intro h; apply hcab; simp [← h]
    have hT : r.T = {a,b,c} := by
      have ht : r.T = insert c {a,b} := by
        rw [← singleton_union,← hc,sdiff_union_of_subset hpab]
      rw [ht]; ext x; simp [or_comm,or_left_comm]
    let v := other r.q r.i
    have ho := other_spec H r hr
    have hi := row_i_notMem H r hr
    have hvT : v ∉ r.T := fun h => disjoint_left.mp (row_disjoint H r hr) ho.2.1 h
    have hia : r.i ≠ a := fun h => hi (h.symm ▸ haT)
    have hib : r.i ≠ b := fun h => hi (h.symm ▸ hbT)
    have hic : r.i ≠ c := fun h => hi (h.symm ▸ hcT)
    have hva : v ≠ a := fun h => hvT (h.symm ▸ haT)
    have hvb : v ≠ b := fun h => hvT (h.symm ▸ hbT)
    have hvc : v ≠ c := fun h => hvT (h.symm ▸ hcT)
    have hdi : [r.i,v,a,b,c].Pairwise (· ≠ ·) := by
      simp [List.pairwise_cons,ho.1.symm,hia,hib,hic,hva,hvb,hvc,hab,hac,hbc,v]
    have hp : common H {r.i,v} = ({a,b,c} : Finset V).powersetCard 2 := by
      rw [← ho.2.2,← hT]; exact hr.2.2.1
    have hTb : r.T.erase b = {a,c} := by simp [hT,hab,hbc,erase_insert_of_ne]
    have hTa : r.T.erase a = {b,c} := by simp [hT,hab,hac]
    have hnb := (mem_filter.mp hb).2.1
    have hkb := (mem_filter.mp hb).2.2
    have hna := (mem_filter.mp ha).2.1
    have hka := (mem_filter.mp ha).2.2
    rw [hTb] at hnb hkb
    rw [hTa] at hna hka
    rw [ho.2.2,image_insert,image_singleton] at hkb hka
    have hcentral := two_marks_central H hd r.i v a b c hdi hp hnb hkb hna hka
    have hcoords := row_coordinates H r hr a b c hT hab hac hbc
    have h12 : ({r.i,a,b} : Finset V) ≠ {r.i,b,c} := by
      intro h; have hm := h ▸ (show a ∈ ({r.i,a,b} : Finset V) by simp)
      simp [hia.symm,hab,hac] at hm
    have h13 : ({r.i,a,b} : Finset V) ≠ {r.i,a,c} := by
      intro h; have hm := h ▸ (show b ∈ ({r.i,a,b} : Finset V) by simp)
      simp [hib.symm,hab.symm,hbc] at hm
    have h23 : ({r.i,b,c} : Finset V) ≠ {r.i,a,c} := by
      intro h; have hm := h ▸ (show b ∈ ({r.i,b,c} : Finset V) by simp)
      simp [hib.symm,hab.symm,hbc] at hm
    have hf2 := (row_members_facts H r hr).2 {r.i,b,c} (by rw [hcoords.1]; simp)
    have hf3 := (row_members_facts H r hr).2 {r.i,a,c} (by rw [hcoords.1]; simp)
    have h2 := pointwise_lower H hd {r.i,b,c} hf2.1 hf2.2.1
    have h3 := pointwise_lower H hd {r.i,a,c} hf3.1 hf3.2.1
    have hpay : (6 : ℚ) ≤ ∑ e ∈ rowMembers r, weight H e := by
      rw [hcoords.1]
      simp only [sum_insert (show ({r.i,a,b} : Finset V) ∉ {{r.i,b,c},{r.i,a,c}} by simp [h12,h13]),
        sum_pair h23]
      linarith only [hcentral,h2,h3]
    have hgroup := internal_many H r hr hmany
    refine ⟨hpay,by rw [hgroup]; exact hpay,?_⟩
    unfold rowDelta
    rw [hgroup,(row_members_facts H r hr).1]
    apply max_eq_right
    norm_num
    linarith only [hpay]
  exact ⟨sole_mark_payment, multi_mark_payment⟩

end D5.S3.Combinatorics.Graph.DUFRowPayment
