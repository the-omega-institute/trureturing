/- GID: D5/S3/Combinatorics/Graph/DUFGlobalAllocation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFGlobalAllocation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual incoming-row deletion and finite global balance for DUF triple families. -/

import D5.S3.Combinatorics.Graph.DUFRowPayment
import D5.S3.Combinatorics.Graph.ColoredPrivateResidual

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph
open DUFStructure DUFReciprocal DUFPacketOwnership DUFLocalPackets DUFMarkedStars
open ColoredReciprocalDeletion
open DUFRowGeometry DUFRowPayment

namespace D5.S3.Combinatorics.Graph.DUFGlobalAllocation

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable instance rowFintype : Fintype (Row V) :=
  Fintype.ofInjective (fun r : Row V => (r.q, r.T, r.i)) (by
    intro r s h
    cases r; cases s
    simpa using h)

abbrev Incoming (H : Finset (Finset V)) (e : Finset V) :=
  {r : Row V // Valid H r ∧ ∃ b, marks H r = {b} ∧ e = recipient r b}

def incomingVertex (H : Finset (Finset V)) (e : Finset V)
    (r : Incoming H e) : U H e :=
  ⟨assigned r.val, by
    obtain ⟨color_eq_iff, neighbor_transport, degree_transport, mixed_iff, mixed_degree,
      potential_transport, leaf_iff, row_disjoint, row_i_notMem, row_members_facts, recipient_mem,
      internal_subset, internal_zero, internal_one, internal_many, other_spec, internal_owner,
      internal_disjoint, assigned_actual, assigned_mixed, assigned_injective,
      configuration_coverage⟩ :=
      DUFRowGeometry.result (V := V)
    have marked_recipient_facts (H : Finset (Finset V)) (r : Row V)
        (hr : Valid H r) (b : V) (hb : b ∈ marks H r) :
        recipient r b ∈ H ∧ (recipient r b).card = 3 ∧
          assigned r ∈ localVertices H (recipient r b) := by
      have hm := recipient_mem H r hr (mem_filter.mp hb).1
      have hf := (row_members_facts H r hr).2 _ hm
      exact ⟨hf.1, hf.2.1, assigned_actual H r hr hm⟩
    obtain ⟨b, hb, he⟩ := r.property.2
    simpa only [← he] using (marked_recipient_facts H r.val r.property.1 b
      (hb.symm ▸ mem_singleton_self b)).2.2⟩

def rowDebt (H : Finset (Finset V)) (e : Finset V) (r : Incoming H e) : ℚ :=
  debt (graph H e) (incomingVertex H e r)

def selectedRows (H : Finset (Finset V)) (e : Finset V) : Finset (Incoming H e) :=
  univ.filter fun r => 0 < rowDebt H e r

def selectedVertices (H : Finset (Finset V)) (e : Finset V) : Finset (U H e) :=
  (selectedRows H e).image (incomingVertex H e)

def residualColoring (H : Finset (Finset V)) (e : Finset V) (he3 : e.card = 3) :
    ((graph H e).induce {w | w ∉ selectedVertices H e}).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun w => coloring H e he3 w.val) (by
    intro w z h
    exact (coloring H e he3).valid h)

def expense (H : Finset (Finset V)) (e : Finset V) : ℚ :=
  ∑ r : Incoming H e, rowDelta H r.val

abbrev ActualRow (H : Finset (Finset V)) := {r : Row V // Valid H r}

abbrev SoleRow (H : Finset (Finset V)) :=
  {r : Row V // Valid H r ∧ (marks H r).card = 1}

def soleMark (H : Finset (Finset V)) (r : SoleRow H) : V :=
  (card_eq_one.mp r.property.2).choose

def soleRecipient (H : Finset (Finset V)) (r : SoleRow H) : Finset V :=
  recipient r.val (soleMark H r)

def fiberIncomingEquiv (H : Finset (Finset V)) (e : Finset V) :
    {r : SoleRow H // soleRecipient H r = e} ≃ Incoming H e where
  toFun r := ⟨r.val.val, r.val.property.1,
    ⟨soleMark H r.val, (card_eq_one.mp r.val.property.2).choose_spec, r.property.symm⟩⟩
  invFun r := by
    let s : SoleRow H := ⟨r.val, r.property.1, by
      obtain ⟨b, hb, _⟩ := r.property.2
      simp [hb]⟩
    refine ⟨s, ?_⟩
    obtain ⟨b, hb, he⟩ := r.property.2
    have hm : soleMark H s = b := singleton_injective (((card_eq_one.mp s.property.2).choose_spec).symm.trans hb)
    exact (congrArg (recipient r.val) hm).trans he.symm
  left_inv r := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv r := by apply Subtype.ext; rfl

def internalUnion (H : Finset (Finset V)) : Finset (Finset V) :=
  univ.biUnion fun r : ActualRow H => internalGroup H r.val

noncomputable def remainingScore
    (H : Finset (Finset V))
    (hu : ∀ e ∈ H, e.card = 3)
    (e : Finset V) : ℚ :=
  if he : e ∈ H then
    if hW : (selectedVertices H e).Nonempty then
      potential ((graph H e).induce {w | w ∉ selectedVertices H e})
        (residualColoring H e (hu e he))
    else weight H e
  else 0

/-- Actual residual mixed degrees, exclusion of singleton leaves, and global balance. -/
theorem result :
    (∀ (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3)
    (hW : (selectedVertices H e).Nonempty),
      (∀ v : {w : U H e // w ∉ selectedVertices H e},
      Mixed ((graph H e).induce {w | w ∉ selectedVertices H e})
        (residualColoring H e he3) v →
      ((graph H e).induce {w | w ∉ selectedVertices H e}).degree v = 2) ∧
    (∀ v : {w : U H e // w ∉ selectedVertices H e},
      (univ.filter fun x : {w : U H e // w ∉ selectedVertices H e} =>
        residualColoring H e he3 x = residualColoring H e he3 v) = {v} →
      ((graph H e).induce {w | w ∉ selectedVertices H e}).degree v ≠ 1))
    ∧ (∀ (H : Finset (Finset V)),
      internalUnion H ⊆ H)
    ∧ (∀ (H : Finset (Finset V))
    (hu : ∀ e ∈ H, e.card = 3)
    (e : Finset V) (he : e ∈ H),
      remainingScore H hu e =
      if hW : (selectedVertices H e).Nonempty then
        potential ((graph H e).induce {w | w ∉ selectedVertices H e})
          (residualColoring H e (hu e he))
      else weight H e)
    ∧ (∀ (H : Finset (Finset V))
    (hu : ∀ e ∈ H, e.card = 3)
    (hd : DUF H),
      2 * ((internalUnion H).card : ℚ) +
        ∑ e ∈ H \ internalUnion H, remainingScore H hu e ≤
      ∑ e ∈ H, weight H e) := by
  obtain ⟨color_eq_iff, neighbor_transport, degree_transport, mixed_iff, mixed_degree,
    potential_transport, leaf_iff, row_disjoint, row_i_notMem, row_members_facts, recipient_mem,
    internal_subset, internal_zero, internal_one, internal_many, other_spec, internal_owner,
    internal_disjoint, assigned_actual, assigned_mixed, assigned_injective,
    configuration_coverage⟩ :=
    DUFRowGeometry.result (V := V)
  obtain ⟨sole_mark_payment, multi_mark_payment⟩ :=
    DUFRowPayment.result (V := V)
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
  have marked_recipient (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
      (hdistinct : [u, v, a, b, c].Pairwise (· ≠ ·))
      (hp : common H {u, v} = ({a, b, c} : Finset V).powersetCard 2)
      (hn : neighbors H {u, b} = {a, c})
      (hk : common H {a, c} = {{u, b}, {v, b}}) :
      let e : Finset V := {u, a, c}
      let w : V × V := (u, v)
      let r : V × V := (a, b)
      let z : V × V := (c, b)
      let mixed := fun t : V × V =>
        ∃ p ∈ localNeighbors H e t, ∃ q ∈ localNeighbors H e t, p.1 ≠ q.1
      w ∈ localVertices H e ∧ localNeighbors H e w = {r, z} ∧
        localNeighbors H e r =
          ((neighbors H {b, c} ∩ neighbors H {a, c}).erase u).image (fun x => (u, x)) ∧
        localNeighbors H e z =
          ((neighbors H {a, b} ∩ neighbors H {a, c}).erase u).image (fun x => (u, x)) ∧
        ∀ y ∈ localNeighbors H e w, ¬ mixed y ∧
          ∀ x ∈ localNeighbors H e y, mixed x → x = w := by
    classical
    have side : ∀ (a c : V),
        [u, v, a, b, c].Pairwise (· ≠ ·) →
        common H {u, v} = ({a, b, c} : Finset V).powersetCard 2 →
        neighbors H {u, b} = {a, c} →
        common H {a, c} = {{u, b}, {v, b}} →
        (u, v) ∈ localVertices H {u, a, c} ∧
        (a, b) ∈ localNeighbors H {u, a, c} (u, v) ∧
        localNeighbors H {u, a, c} (a, b) =
          ((neighbors H {b, c} ∩ neighbors H {a, c}).erase u).image (fun x => (u, x)) ∧
        ∀ x ∈ localNeighbors H {u, a, c} (a, b),
          (∃ p ∈ localNeighbors H {u, a, c} x,
            ∃ q ∈ localNeighbors H {u, a, c} x, p.1 ≠ q.1) → x = (u, v) := by
      clear hdistinct hp hn hk a c
      intro a c hdistinct hp hn hk
      have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
          (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
        simpa [List.pairwise_cons] using hdistinct
      obtain ⟨⟨huv, hua, hub, huc⟩, ⟨hva, hvb, hvc⟩, ⟨hab, hac⟩, hbc⟩ := hd'
      have extend (p : Finset V) (hpt : p ∈ ({a, b, c} : Finset V).powersetCard 2)
          (i : V) (hi : i ∈ ({u, v} : Finset V)) : i ∉ p ∧ insert i p ∈ H := by
        have hm : p ∈ common H {u, v} := hp.symm ▸ hpt
        simpa only [neighbors, mem_filter, mem_univ, true_and] using
          (mem_filter.mp hm).2 hi
      have huac := extend {a, c} (by simp [mem_powersetCard, hac]) u (by simp)
      have hvac := extend {a, c} (by simp [mem_powersetCard, hac]) v (by simp)
      have hubc := extend {b, c} (by simp [mem_powersetCard, hbc]) u (by simp)
      have hvbc := extend {b, c} (by simp [mem_powersetCard, hbc]) v (by simp)
      have he3 : ({u, a, c} : Finset V).card = 3 := by simp [hua, huc, hac]
      have hw : (u, v) ∈ localVertices H {u, a, c} := by
        simp only [localVertices, mem_filter, mem_univ, true_and]
        exact ⟨by simp, by simp [huv.symm, hva, hvc], by simpa [hua, huc] using hvac.2⟩
      have hr : (a, b) ∈ localNeighbors H {u, a, c} (u, v) := by
        simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and]
        refine ⟨⟨by simp, by simp [hub.symm, hab.symm, hbc], ?_⟩, hua, hvb, ?_⟩
        · simpa [hua, hac, erase_insert_of_ne, insert_comm] using hubc.2
        · simpa [hua, huc, hac] using hvbc.2
      have hs := (marked_common_stars H hd u v a b c hdistinct hp hn hk).1
      have hN : localNeighbors H {u, a, c} (a, b) =
          ((neighbors H {b, c} ∩ neighbors H {a, c}).erase u).image (fun x => (u, x)) := by
        ext t
        rcases t with ⟨d, x⟩
        constructor
        · intro ht
          simp only [localNeighbors, mem_filter, adjacent] at ht
          obtain ⟨htV, had, hbx, htH⟩ := ht
          obtain ⟨hdE, hxE, hxH⟩ := (mem_filter.mp htV).2
          have hxu : x ≠ u := fun h => hxE (by simp [h])
          have hxa : x ≠ a := fun h => hxE (by simp [h])
          have hxc : x ≠ c := fun h => hxE (by simp [h])
          simp only [mem_insert, mem_singleton] at hdE
          rcases hdE with hdu | hda | hdc
          · subst d
            apply mem_image.mpr
            refine ⟨x, mem_erase.mpr ⟨hxu, mem_inter.mpr ⟨?_, ?_⟩⟩, rfl⟩
            · simp only [neighbors, mem_filter, mem_univ, true_and]
              refine ⟨by simp [hbx.symm, hxc], ?_⟩
              simpa [hua, huc, hac, erase_insert_of_ne, insert_comm] using htH
            · simp only [neighbors, mem_filter, mem_univ, true_and]
              exact ⟨by simp [hxa, hxc], by simpa [hua, huc] using hxH⟩
          · exact (had hda.symm).elim
          · subst d
            have hux : ({u, x} : Finset V) ∈ common H {a, b} := by
              simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
                insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
              refine ⟨by simp [hxu.symm], ⟨by simp [hua.symm, hxa.symm], ?_⟩,
                ⟨by simp [hub.symm, hbx], ?_⟩⟩
              · simpa [huc, hac, hac.symm, erase_insert_of_ne, insert_comm, pair_comm]
                  using hxH
              · simpa [hua, huc, huc.symm, hac, hac.symm, erase_insert_of_ne,
                  insert_comm, pair_comm] using htH
            rw [hs] at hux
            obtain ⟨y, _, hy⟩ := mem_image.mp hux
            have hcux : c ∈ ({u, x} : Finset V) := hy ▸ (by simp)
            simp [huc.symm, hxc.symm] at hcux
        · intro ht
          obtain ⟨y, hy, ht⟩ := mem_image.mp ht
          cases ht
          obtain ⟨hyu, hy⟩ := mem_erase.mp hy
          obtain ⟨hybc, hyac⟩ := mem_inter.mp hy
          simp only [neighbors, mem_filter, mem_univ, true_and] at hybc hyac
          have hyb : x ≠ b := fun h => hybc.1 (by simp [h])
          have hya : x ≠ a := fun h => hyac.1 (by simp [h])
          have hyc : x ≠ c := fun h => hyac.1 (by simp [h])
          simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and]
          refine ⟨⟨by simp, by simp [hyu, hya, hyc], ?_⟩, hua.symm, hyb.symm, ?_⟩
          · simpa [hua, huc] using hyac.2
          · simpa [hua, huc, hac, erase_insert_of_ne, insert_comm] using hybc.2
      refine ⟨hw, hr, hN, ?_⟩
      intro t ht hm
      have htV : t ∈ localVertices H {u, a, c} := by
        have h := ht
        simp only [localNeighbors, mem_filter] at h
        exact h.1
      rw [hN] at ht
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
      obtain ⟨hxu, hx⟩ := mem_erase.mp hx
      obtain ⟨hxbc, hxac⟩ := mem_inter.mp hx
      obtain ⟨T, hT, _⟩ :=
        (mixed_packet_correspondence H hd {u, a, c} huac.2 he3 (u, x) htV).mp hm
      have hacK : ({a, c} : Finset V) ∈ common H {u, x} := by
        simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
          insert_subset_iff, singleton_subset_iff]
        exact ⟨by simp [hac], by simpa [neighbors] using huac, hxac⟩
      have hbcK : ({b, c} : Finset V) ∈ common H {u, x} := by
        simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
          insert_subset_iff, singleton_subset_iff]
        exact ⟨by simp [hbc], by simpa [neighbors] using hubc, hxbc⟩
      have hacT : ({a, c} : Finset V) ⊆ T :=
        (mem_powersetCard.mp (hT.2.2.1 ▸ hacK)).1
      have hbcT : ({b, c} : Finset V) ⊆ T :=
        (mem_powersetCard.mp (hT.2.2.1 ▸ hbcK)).1
      have hTeq : T = {a, b, c} := by
        apply (eq_of_subset_of_card_le ?_ ?_).symm
        · simp only [insert_subset_iff, singleton_subset_iff]
          exact ⟨hacT (by simp), hbcT (by simp), hacT (by simp)⟩
        · simp [hT.2.1, hab, hac, hbc]
      have hrow : PacketRow H {u, x} T u {u, a, b} :=
        ⟨hT.1, hT.2.1, hT.2.2.1, by simp,
          {a, b}, by simp [hTeq, mem_powersetCard, hab], rfl⟩
      have hpair := (marked_endpoint_ownership H u v a b c hdistinct hn hk
        {u, x} T {u, a, b} u (Or.inl rfl) hrow).1
      have hxv : x = v := by
        have hxm : x ∈ ({u, v} : Finset V) := hpair ▸ (by simp)
        simpa [hxu] using hxm
      simp [hxv]
    have ha := side a c hdistinct hp hn hk
    have hswap : [u, v, c, b, a].Pairwise (· ≠ ·) := by
      clear side ha hp hn hk hd
      simp [List.pairwise_cons] at hdistinct ⊢
      grind
    have hp' : common H {u, v} = ({c, b, a} : Finset V).powersetCard 2 := by
      rw [hp]
      congr 1
      ext t
      simp [or_comm, or_left_comm]
    have hc := side c a hswap hp' (by simpa [pair_comm] using hn)
      (by simpa [pair_comm] using hk)
    have heq : ({u, c, a} : Finset V) = {u, a, c} := by rw [pair_comm c a]
    rw [heq] at hc
    dsimp only
    have hd3 : u ≠ a ∧ u ≠ c ∧ a ≠ c := by
      simp [List.pairwise_cons] at hdistinct
      tauto
    have hac := hd3.2.2
    have he3 : ({u, a, c} : Finset V).card = 3 := by
      simp [hd3.1, hd3.2.1, hac]
    have heH : ({u, a, c} : Finset V) ∈ H := by
      have hm : ({a, c} : Finset V) ∈ common H {u, v} := by
        rw [hp]; simp [mem_powersetCard, hac]
      exact (mem_filter.mp ((mem_filter.mp hm).2 (by simp : u ∈ ({u, v} : Finset V)))).2.2
    have hNw : localNeighbors H {u, a, c} (u, v) = {(a, b), (c, b)} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨ha.2.1, hc.2.1⟩
      · have hcard := (local_correspondence H hd {u, a, c} heH he3 (u, v) ha.1).2
          ⟨(a, b), ha.2.1, (c, b), hc.2.1, hac⟩
        simp [hcard, hac]
    refine ⟨ha.1, hNw, ha.2.2.1, ?_, ?_⟩
    · simpa [pair_comm, inter_comm] using hc.2.2.1
    · intro y hy
      have one_coordinate (A : Finset V)
          (hA : localNeighbors H {u, a, c} y = A.image (fun x => (u, x))) :
          ¬ (∃ p ∈ localNeighbors H {u, a, c} y,
            ∃ q ∈ localNeighbors H {u, a, c} y, p.1 ≠ q.1) := by
        rintro ⟨p, hp, q, hq, hpq⟩
        rw [hA] at hp hq
        obtain ⟨s, _, rfl⟩ := mem_image.mp hp
        obtain ⟨t, _, rfl⟩ := mem_image.mp hq
        exact hpq rfl
      rw [hNw] at hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨one_coordinate _ ha.2.2.1, ha.2.2.2⟩
      · exact ⟨one_coordinate _ hc.2.2.1, hc.2.2.2⟩
  have marked_recipient_facts (H : Finset (Finset V)) (r : Row V)
      (hr : Valid H r) (b : V) (hb : b ∈ marks H r) :
      recipient r b ∈ H ∧ (recipient r b).card = 3 ∧
        assigned r ∈ localVertices H (recipient r b) := by
    have hm := recipient_mem H r hr (mem_filter.mp hb).1
    have hf := (row_members_facts H r hr).2 _ hm
    exact ⟨hf.1, hf.2.1, assigned_actual H r hr hm⟩
  have actual_recipient_privacy (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) (b : V) (hb : b ∈ marks H r)
      (e : Finset V) (heq : e = recipient r b) (he3 : e.card = 3)
      (w : U H e) (hw : w.val = assigned r) :
      ∀ y, (graph H e).Adj w y →
        ¬ Mixed (graph H e) (coloring H e he3) y ∧
          ∀ x, (graph H e).Adj y x →
            Mixed (graph H e) (coloring H e he3) x → x = w := by
    obtain ⟨a, c, hdist, hT, hn, hk⟩ := mark_coordinates H r hr b hb
    let v := other r.q r.i
    have hass : assigned r = (r.i, v) := rfl
    have hpair : r.T.erase b = {a, c} := by
      have hn' : a ≠ b ∧ b ≠ c := by
        simp [List.pairwise_cons] at hdist
        tauto
      simp [hT, hn'.1, hn'.2, erase_insert_of_ne]
    have hrec : recipient r b = {r.i, a, c} := by simp only [recipient, hpair]
    have hp : common H {r.i, v} = ({a, b, c} : Finset V).powersetCard 2 := by
      rw [← (other_spec H r hr).2.2, ← hT]
      exact hr.2.2.1
    have he : e = {r.i, a, c} := heq.trans hrec
    have hw' : w.val = (r.i, v) := hw.trans hass
    have hgeom := (marked_recipient H hd r.i v a b c hdist hp hn hk).2.2.2.2
    have hlocal : ∀ y ∈ localNeighbors H e w.val,
        ¬ (∃ p ∈ localNeighbors H e y, ∃ q ∈ localNeighbors H e y, p.1 ≠ q.1) ∧
        ∀ x ∈ localNeighbors H e y,
          (∃ p ∈ localNeighbors H e x, ∃ q ∈ localNeighbors H e x, p.1 ≠ q.1) →
          x = w.val := by
      simpa only [he, hw'] using hgeom
    intro y hy
    have hyN : y.val ∈ localNeighbors H e w.val := by
      simpa only [localNeighbors, mem_filter, graph] using And.intro y.property hy
    refine ⟨fun hm => (hlocal y.val hyN).1 ((mixed_iff H e he3 y).mp hm), ?_⟩
    intro x hx hm
    have hxN : x.val ∈ localNeighbors H e y.val := by
      simpa only [localNeighbors, mem_filter, graph] using And.intro x.property hx
    exact Subtype.ext ((hlocal y.val hyN).2 x.val hxN ((mixed_iff H e he3 x).mp hm))
  have sole_mark_exclusion (H : Finset (Finset V)) (r : Row V)
      (hr : Valid H r) (b : V) (hb : marks H r = {b})
      (e : Finset V) (heq : e = recipient r b) :
      ∀ s : Row V, Valid H s → e ∉ internalGroup H s := by
    have hbm : b ∈ marks H r := hb.symm ▸ mem_singleton_self b
    have hp := ((row_members_facts H r hr).2 _
      (recipient_mem H r hr (mem_filter.mp hbm).1)).2.2
    intro s hs he
    have ho := internal_owner H s hs he r.q r.T r.i (heq.symm ▸ hp)
    have hrs : r = s := by cases r; cases s; simp_all
    subst s
    obtain ⟨b', _, hb', _, _, _, hout⟩ := internal_one H r hr (by simp [hb])
    have hbb : b' = b := singleton_injective (hb'.symm.trans hb)
    exact hout (by simpa only [hbb, heq] using he)
  have incomingVertex_injective (H : Finset (Finset V)) (e : Finset V) :
      Function.Injective (incomingVertex H e) := by
    intro r s h
    exact Subtype.ext (assigned_injective H r.val s.val r.property.1 s.property.1
      (congrArg Subtype.val h))
  have mem_selectedVertices (H : Finset (Finset V)) (e : Finset V) (w : U H e) :
      w ∈ selectedVertices H e ↔
        ∃ r : Incoming H e, 0 < debt (graph H e) (incomingVertex H e r) ∧
          incomingVertex H e r = w := by
    rw [selectedVertices, mem_image]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, (mem_filter.mp hr).2, h⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨r, mem_filter.mpr ⟨mem_univ _, hr⟩, h⟩
  have incoming_exclusion (H : Finset (Finset V)) (e : Finset V)
      (r : Incoming H e) : ∀ s : Row V, Valid H s → e ∉ internalGroup H s := by
    obtain ⟨b, hb, he⟩ := r.property.2
    exact sole_mark_exclusion H r.val r.property.1 b hb e he
  have incoming_geometry (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (r : Incoming H e) :
      Mixed (graph H e) (coloring H e he3) (incomingVertex H e r) ∧
      (graph H e).degree (incomingVertex H e r) = 2 ∧
      ∀ y, (graph H e).Adj (incomingVertex H e r) y →
        ¬ Mixed (graph H e) (coloring H e he3) y ∧
        ∀ x, (graph H e).Adj y x →
          Mixed (graph H e) (coloring H e he3) x → x = incomingVertex H e r := by
    obtain ⟨b, hb, heq⟩ := r.property.2
    have hbm : b ∈ marks H r.val := hb.symm ▸ mem_singleton_self b
    have hem : e ∈ rowMembers r.val := by
      simpa only [← heq] using recipient_mem H r.val r.property.1 (mem_filter.mp hbm).1
    have hm := (mixed_iff H e he3 (incomingVertex H e r)).mpr
      (assigned_mixed H hd r.val r.property.1 hem)
    exact ⟨hm, mixed_degree H hd e he he3 _ hm,
      actual_recipient_privacy H hd r.val r.property.1 b hbm e heq he3 _ rfl⟩
  have selected_properties (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) :
      ∀ w ∈ selectedVertices H e,
        0 < debt (graph H e) w ∧
        Mixed (graph H e) (coloring H e he3) w ∧
        (graph H e).degree w = 2 ∧
        ∀ y, (graph H e).Adj w y →
          ¬ Mixed (graph H e) (coloring H e he3) y ∧
          ∀ x, (graph H e).Adj y x → Mixed (graph H e) (coloring H e he3) x → x = w := by
    intro w hw
    obtain ⟨r, hp, rfl⟩ := (mem_selectedVertices H e w).mp hw
    exact ⟨hp, incoming_geometry H hd e he he3 r⟩
  have selected_sum (H : Finset (Finset V)) (e : Finset V) :
      (∑ r ∈ selectedRows H e, rowDebt H e r) =
        ∑ w ∈ selectedVertices H e, debt (graph H e) w := by
    rw [selectedVertices, sum_image]
    · rfl
    · intro r _ s _ h
      exact incomingVertex_injective H e h
  have incoming_deletion (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) :
      (∑ r ∈ selectedRows H e, rowDebt H e r) ≤ weight H e -
        potential ((graph H e).induce {w | w ∉ selectedVertices H e})
          (residualColoring H e he3) := by
    rw [selected_sum]
    have hp := selected_properties H hd e he he3
    have hdel := weighted_induced_deletion (graph H e) (coloring H e he3)
      (selectedVertices H e) (fun w hw => (hp w hw).2.1)
      (fun w hw => (hp w hw).2.2.1) (fun w hw => (hp w hw).2.2.2)
      (fun w hw => (hp w hw).1)
    rw [potential_transport H hd e he he3] at hdel
    exact hdel
  have incoming_residual (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3)
      (hW : (selectedVertices H e).Nonempty) :
      (∀ v : {w : U H e // w ∉ selectedVertices H e},
        Mixed ((graph H e).induce {w | w ∉ selectedVertices H e})
          (residualColoring H e he3) v →
        ((graph H e).induce {w | w ∉ selectedVertices H e}).degree v = 2) ∧
      (∀ v : {w : U H e // w ∉ selectedVertices H e},
        (univ.filter fun x : {w : U H e // w ∉ selectedVertices H e} =>
          residualColoring H e he3 x = residualColoring H e he3 v) = {v} →
        ((graph H e).induce {w | w ∉ selectedVertices H e}).degree v ≠ 1) := by
    have hp := selected_properties H hd e he he3
    exact ColoredPrivateResidual.positive_private_residual (graph H e) (coloring H e he3)
      (selectedVertices H e) hW (fun w hw => (hp w hw).2.1)
      (mixed_degree H hd e he he3) (fun w hw => (hp w hw).2.2.2)
      (fun w hw => (hp w hw).1)
  have incoming_payment (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (r : Incoming H e) :
      rowDelta H r.val ≤ max (rowDebt H e r) 0 ∧
        (0 < rowDelta H r.val → 0 < rowDebt H e r ∧ rowDelta H r.val ≤ rowDebt H e r) := by
    rcases r with ⟨r, hr, b, hb, rfl⟩
    obtain ⟨b', _, hb', _, _, _, _, w, hw, _, hpay, hpos⟩ :=
      sole_mark_payment H hd r hr (by simp [hb])
    have hbb : b' = b := singleton_injective (hb'.symm.trans hb)
    subst b'
    have hwi : w = incomingVertex H (recipient r b) ⟨r, hr, b, hb, rfl⟩ := Subtype.ext hw
    simpa only [hwi, rowDebt] using And.intro hpay hpos
  have unselected_delta_zero (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (r : Incoming H e) (hr : r ∉ selectedRows H e) :
      rowDelta H r.val = 0 := by
    have hdebt : rowDebt H e r ≤ 0 := by simpa [selectedRows, not_lt] using hr
    have hp := (incoming_payment H hd e r).1
    rw [max_eq_right hdebt] at hp
    exact le_antisymm hp (le_max_right _ _)
  have expense_le_selected (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) : expense H e ≤ ∑ r ∈ selectedRows H e, rowDebt H e r := by
    have hs : expense H e = ∑ r ∈ selectedRows H e, rowDelta H r.val := by
      symm
      apply sum_subset (subset_univ _)
      intro r _ hr
      exact unselected_delta_zero H hd e r hr
    rw [hs]
    apply sum_le_sum
    intro r hr
    have hp : 0 < rowDebt H e r := (mem_filter.mp hr).2
    simpa only [max_eq_left hp.le] using (incoming_payment H hd e r).1
  have expense_deletion (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) :
      expense H e ≤ weight H e -
        potential ((graph H e).induce {w | w ∉ selectedVertices H e})
          (residualColoring H e he3) :=
    (expense_le_selected H hd e).trans (incoming_deletion H hd e he he3)
  have zero_mark_delta (H : Finset (Finset V)) (r : Row V)
      (hzero : (marks H r).card = 0) : rowDelta H r = 0 := by
    simp [rowDelta, internal_zero H r hzero]
  have nonsingle_delta (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) (hne : (marks H r).card ≠ 1) : rowDelta H r = 0 := by
    by_cases hz : (marks H r).card = 0
    · exact zero_mark_delta H r hz
    · exact (multi_mark_payment H hd r hr (by omega)).2.2
  have soleMark_spec (H : Finset (Finset V)) (r : SoleRow H) :
      marks H r.val = {soleMark H r} := (card_eq_one.mp r.property.2).choose_spec
  have soleRecipient_mem (H : Finset (Finset V)) (r : SoleRow H) :
      soleRecipient H r ∈ H := by
    have hb : soleMark H r ∈ marks H r.val := (soleMark_spec H r).symm ▸ mem_singleton_self _
    exact ((row_members_facts H r.val r.property.1).2 _
      (recipient_mem H r.val r.property.1 (mem_filter.mp hb).1)).1
  have global_deficit_grouping (H : Finset (Finset V)) (hd : DUF H) :
      (∑ r : ActualRow H, rowDelta H r.val) = ∑ e ∈ H, expense H e := by
    have hsole : (∑ r : SoleRow H, rowDelta H r.val) =
        ∑ r : ActualRow H, rowDelta H r.val := by
      apply Fintype.sum_of_injective (fun r : SoleRow H => (⟨r.val, r.property.1⟩ : ActualRow H))
      · intro r s h
        exact Subtype.ext (congrArg (fun r : ActualRow H => r.val) h)
      · intro r hr
        apply nonsingle_delta H hd r.val r.property
        intro hone
        exact hr ⟨⟨r.val, r.property, hone⟩, rfl⟩
      · intro r
        rfl
    rw [← hsole, ← sum_fiberwise_of_maps_to (s := (univ : Finset (SoleRow H)))
      (t := H) (g := soleRecipient H) (fun r _ => soleRecipient_mem H r)]
    apply sum_congr rfl
    intro e _
    rw [sum_subtype _ (p := fun r : SoleRow H => soleRecipient H r = e) (by simp)]
    exact (fiberIncomingEquiv H e).sum_comp (fun r : Incoming H e => rowDelta H r.val)
  have internalGroups_disjoint (H : Finset (Finset V)) :
      Set.PairwiseDisjoint ((univ : Finset (ActualRow H)) : Set (ActualRow H))
        (fun r : ActualRow H => internalGroup H r.val) := by
    intro r _ s _ hne
    exact internal_disjoint H r.val s.val r.property s.property
      (fun h => hne (Subtype.ext h))
  have internalUnion_subset (H : Finset (Finset V)) : internalUnion H ⊆ H := by
    intro e he
    obtain ⟨r, _, her⟩ := mem_biUnion.mp he
    exact ((row_members_facts H r.val r.property).2 e (internal_subset H r.val her)).1
  have internalUnion_sum (H : Finset (Finset V)) :
      (∑ e ∈ internalUnion H, weight H e) =
        ∑ r : ActualRow H, ∑ e ∈ internalGroup H r.val, weight H e := by
    exact sum_biUnion (internalGroups_disjoint H)
  have internalUnion_card (H : Finset (Finset V)) :
      (internalUnion H).card = ∑ r : ActualRow H, (internalGroup H r.val).card := by
    simpa only [internalUnion, sum_const, smul_eq_mul, mul_one] using
      (sum_biUnion (f := fun _ : Finset V => (1 : ℕ)) (internalGroups_disjoint H))
  have internalUnion_balance (H : Finset (Finset V)) :
      2 * ((internalUnion H).card : ℚ) - ∑ e ∈ internalUnion H, weight H e =
        ∑ r : ActualRow H,
          (2 * ((internalGroup H r.val).card : ℚ) - ∑ e ∈ internalGroup H r.val, weight H e) := by
    rw [internalUnion_card, internalUnion_sum, Nat.cast_sum, mul_sum, sum_sub_distrib]
  have expense_nonneg (H : Finset (Finset V)) (e : Finset V) :
      0 ≤ expense H e := by
    unfold expense
    apply Fintype.sum_nonneg
    intro r
    exact le_max_right _ _
  have selectedRows_empty_of_selectedVertices_empty
      (H : Finset (Finset V)) (e : Finset V)
      (hW : selectedVertices H e = ∅) :
      selectedRows H e = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hw : incomingVertex H e r ∈ selectedVertices H e := by
      apply mem_image.mpr
      exact ⟨r, hr, rfl⟩
    rw [hW] at hw
    simpa using hw
  have expense_zero_of_selectedVertices_empty
      (H : Finset (Finset V)) (hd : DUF H) (e : Finset V)
      (hW : selectedVertices H e = ∅) :
      expense H e = 0 := by
    have hs := selectedRows_empty_of_selectedVertices_empty H e hW
    have hle := expense_le_selected H hd e
    rw [hs] at hle
    exact le_antisymm (by simpa using hle) (expense_nonneg H e)
  have remainingScore_of_mem
      (H : Finset (Finset V))
      (hu : ∀ e ∈ H, e.card = 3)
      (e : Finset V) (he : e ∈ H) :
      remainingScore H hu e =
        if hW : (selectedVertices H e).Nonempty then
          potential ((graph H e).induce {w | w ∉ selectedVertices H e})
            (residualColoring H e (hu e he))
        else weight H e := by
    simp [remainingScore, he]
  have remainingScore_le
      (H : Finset (Finset V)) (hd : DUF H)
      (hu : ∀ e ∈ H, e.card = 3)
      (e : Finset V) (he : e ∈ H) :
      remainingScore H hu e ≤ weight H e - expense H e := by
    rw [remainingScore_of_mem H hu e he]
    by_cases hW : (selectedVertices H e).Nonempty
    · simp only [dif_pos hW]
      have hdel := expense_deletion H hd e he (hu e he)
      linarith
    · simp only [dif_neg hW]
      have hzero : selectedVertices H e = ∅ :=
        not_nonempty_iff_eq_empty.mp hW
      rw [expense_zero_of_selectedVertices_empty H hd e hzero]
      linarith
  have expense_zero_on_internalUnion
      (H : Finset (Finset V)) (hd : DUF H)
      {e : Finset V} (he : e ∈ internalUnion H) :
      expense H e = 0 := by
    unfold expense
    apply Fintype.sum_eq_zero
    intro r
    obtain ⟨s, hs, hse⟩ := mem_biUnion.mp he
    exact ((incoming_exclusion H e r s.val s.property) hse).elim
  have internal_expense_sum_zero
      (H : Finset (Finset V)) (hd : DUF H) :
      (∑ e ∈ internalUnion H, expense H e) = 0 := by
    apply sum_eq_zero
    intro e he
    exact expense_zero_on_internalUnion H hd he
  have raw_deficit_le_rowDelta
      (H : Finset (Finset V)) (r : ActualRow H) :
      2 * ((internalGroup H r.val).card : ℚ) -
          ∑ e ∈ internalGroup H r.val, weight H e ≤
        rowDelta H r.val := by
    exact le_max_left _ _
  have raw_deficit_sum_le_expense
      (H : Finset (Finset V)) (hd : DUF H) :
      (∑ r : ActualRow H,
          (2 * ((internalGroup H r.val).card : ℚ) -
            ∑ e ∈ internalGroup H r.val, weight H e)) ≤
        ∑ e ∈ H, expense H e := by
    calc
      (∑ r : ActualRow H,
          (2 * ((internalGroup H r.val).card : ℚ) -
            ∑ e ∈ internalGroup H r.val, weight H e)) ≤
          ∑ r : ActualRow H, rowDelta H r.val := by
        apply Finset.sum_le_sum
        intro r hr
        exact raw_deficit_le_rowDelta H r
      _ = ∑ e ∈ H, expense H e := global_deficit_grouping H hd
  have expense_partition
      (H : Finset (Finset V)) :
      (∑ e ∈ H, expense H e) =
        (∑ e ∈ internalUnion H, expense H e) +
          ∑ e ∈ H \ internalUnion H, expense H e := by
    have h := Finset.sum_union
      (f := fun e : Finset V => expense H e)
      (Finset.disjoint_sdiff : Disjoint (internalUnion H) (H \ internalUnion H))
    rw [Finset.union_sdiff_of_subset (internalUnion_subset H)] at h
    exact h
  have weight_partition
      (H : Finset (Finset V)) :
      (∑ e ∈ H, weight H e) =
        (∑ e ∈ internalUnion H, weight H e) +
          ∑ e ∈ H \ internalUnion H, weight H e := by
    have h := Finset.sum_union
      (f := fun e : Finset V => weight H e)
      (Finset.disjoint_sdiff : Disjoint (internalUnion H) (H \ internalUnion H))
    rw [Finset.union_sdiff_of_subset (internalUnion_subset H)] at h
    exact h
  have outside_remaining_sum_le
      (H : Finset (Finset V)) (hd : DUF H)
      (hu : ∀ e ∈ H, e.card = 3) :
      (∑ e ∈ H \ internalUnion H, remainingScore H hu e) ≤
        ∑ e ∈ H \ internalUnion H, (weight H e - expense H e) := by
    apply Finset.sum_le_sum
    intro e he
    exact remainingScore_le H hd hu e (mem_sdiff.mp he).1
  have global_balance
      (H : Finset (Finset V))
      (hu : ∀ e ∈ H, e.card = 3)
      (hd : DUF H) :
      2 * ((internalUnion H).card : ℚ) +
          ∑ e ∈ H \ internalUnion H, remainingScore H hu e ≤
        ∑ e ∈ H, weight H e := by
    have hbase :
        2 * ((internalUnion H).card : ℚ) -
            ∑ e ∈ internalUnion H, weight H e ≤
          ∑ e ∈ H, expense H e := by
      calc
        2 * ((internalUnion H).card : ℚ) -
              ∑ e ∈ internalUnion H, weight H e =
            ∑ r : ActualRow H,
              (2 * ((internalGroup H r.val).card : ℚ) -
                ∑ e ∈ internalGroup H r.val, weight H e) :=
          internalUnion_balance H
        _ ≤ ∑ e ∈ H, expense H e := raw_deficit_sum_le_expense H hd
    have hbase_outside :
        2 * ((internalUnion H).card : ℚ) -
            ∑ e ∈ internalUnion H, weight H e ≤
          ∑ e ∈ H \ internalUnion H, expense H e := by
      calc
        2 * ((internalUnion H).card : ℚ) -
              ∑ e ∈ internalUnion H, weight H e ≤
            ∑ e ∈ H, expense H e := hbase
        _ = (∑ e ∈ internalUnion H, expense H e) +
            ∑ e ∈ H \ internalUnion H, expense H e := expense_partition H
        _ = ∑ e ∈ H \ internalUnion H, expense H e := by
          rw [internal_expense_sum_zero H hd]
          simp
    have hscore := outside_remaining_sum_le H hd hu
    rw [sum_sub_distrib] at hscore
    have hsum :
        2 * ((internalUnion H).card : ℚ) +
            ∑ e ∈ H \ internalUnion H, remainingScore H hu e ≤
          (∑ e ∈ internalUnion H, weight H e) +
            ∑ e ∈ H \ internalUnion H, weight H e := by
      linarith
    rw [weight_partition H]
    exact hsum
  exact ⟨incoming_residual, internalUnion_subset, remainingScore_of_mem, global_balance⟩

end D5.S3.Combinatorics.Graph.DUFGlobalAllocation
