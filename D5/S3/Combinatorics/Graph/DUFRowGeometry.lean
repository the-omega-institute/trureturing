/- GID: D5/S3/Combinatorics/Graph/DUFRowGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFRowGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual local graph geometry and disjoint ownership of marked triangle rows. -/

import D5.S3.Combinatorics.Graph.DUFLocalPackets
import D5.S3.Combinatorics.Graph.DUFMarkedStars
import D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph
open DUFStructure DUFReciprocal DUFPacketOwnership DUFLocalPackets DUFMarkedStars
open ColoredReciprocalDeletion

namespace D5.S3.Combinatorics.Graph.DUFRowGeometry

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev U (H : Finset (Finset V)) (e : Finset V) :=
  {w : V × V // w ∈ localVertices H e}

def graph (H : Finset (Finset V)) (e : Finset V) : SimpleGraph (U H e) where
  Adj w z := adjacent H e w.val z.val
  symm := ⟨by
    intro w z h
    exact ⟨h.1.symm, h.2.1.symm, by
      simpa only [erase_right_comm, insert_comm] using h.2.2⟩⟩
  loopless := ⟨by intro w h; exact h.1 rfl⟩

def colorEquiv (e : Finset V) (he3 : e.card = 3) : e ≃ Fin 3 :=
  Finset.equivFinOfCardEq he3

def coloring (H : Finset (Finset V)) (e : Finset V) (he3 : e.card = 3) :
    (graph H e).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk
    (fun w => colorEquiv e he3 ⟨w.val.1, (mem_filter.mp w.property).2.1⟩)
    (by
      intro w z h hc
      exact h.1 (congrArg Subtype.val ((colorEquiv e he3).injective hc)))

structure Row (V : Type*) where
  q : Finset V
  T : Finset V
  i : V
  deriving DecidableEq

def Valid (H : Finset (Finset V)) (r : Row V) : Prop :=
  r.q.card = 2 ∧ r.T.card = 3 ∧ common H r.q = r.T.powersetCard 2 ∧ r.i ∈ r.q

def rowMembers (r : Row V) : Finset (Finset V) :=
  (r.T.powersetCard 2).image (insert r.i)

def recipient (r : Row V) (b : V) : Finset V := insert r.i (r.T.erase b)

def marks (H : Finset (Finset V)) (r : Row V) : Finset V :=
  r.T.filter fun b => neighbors H {r.i, b} = r.T.erase b ∧
    common H (r.T.erase b) = r.q.image (fun j => {j, b})

def internalGroup (H : Finset (Finset V)) (r : Row V) :
    Finset (Finset V) :=
  (marks H r).biUnion fun b => (rowMembers r).erase (recipient r b)

noncomputable def other (q : Finset V) (i : V) : V :=
  if h : (q.erase i).Nonempty then h.choose else i

noncomputable def assigned (r : Row V) : V × V := (r.i, other r.q r.i)

/-- Local graph transport, singleton-leaf marks, and disjoint ownership for actual rows. -/
theorem result :
    (∀ (H : Finset (Finset V)) (e : Finset V)
    (he3 : e.card = 3) (w z : U H e),
      coloring H e he3 w = coloring H e he3 z ↔ w.val.1 = z.val.1)
    ∧ (∀ (H : Finset (Finset V)) (e : Finset V) (w : U H e),
      ((graph H e).neighborFinset w).image Subtype.val = localNeighbors H e w.val)
    ∧ (∀ (H : Finset (Finset V)) (e : Finset V) (w : U H e),
      (graph H e).degree w = (localNeighbors H e w.val).card)
    ∧ (∀ (H : Finset (Finset V)) (e : Finset V)
    (he3 : e.card = 3) (w : U H e),
      ColoredReciprocalDeletion.Mixed (graph H e) (coloring H e he3) w ↔
      ∃ r ∈ localNeighbors H e w.val, ∃ z ∈ localNeighbors H e w.val, r.1 ≠ z.1)
    ∧ (∀ (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (w : U H e)
    (hm : ColoredReciprocalDeletion.Mixed (graph H e) (coloring H e he3) w),
      (graph H e).degree w = 2)
    ∧ (∀ (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3),
      ColoredReciprocalDeletion.potential (graph H e) (coloring H e he3) = weight H e)
    ∧ (∀ (H : Finset (Finset V)) (e : Finset V) (w l : U H e)
    (hwl : (graph H e).Adj w l),
      (graph H e).degree l = 1 ↔ (graph H e).neighborFinset l = {w})
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r),
      Disjoint r.q r.T)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r),
      r.i ∉ r.T)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r),
      (rowMembers r).card = 3 ∧ ∀ e ∈ rowMembers r, e ∈ H ∧ e.card = 3 ∧
      PacketRow H r.q r.T r.i e)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
    {b : V} (hb : b ∈ r.T),
      recipient r b ∈ rowMembers r)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V),
      internalGroup H r ⊆ rowMembers r)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V)
    (h : (marks H r).card = 0),
      internalGroup H r = ∅)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
    (h : (marks H r).card = 1),
      ∃ b ∈ marks H r, marks H r = {b} ∧
      internalGroup H r = (rowMembers r).erase (recipient r b) ∧
      internalGroup H r = (r.T.erase b).image (recipient r) ∧
      (internalGroup H r).card = 2 ∧ recipient r b ∉ internalGroup H r)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
    (h : 2 ≤ (marks H r).card),
      internalGroup H r = rowMembers r)
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r),
      other r.q r.i ≠ r.i ∧ other r.q r.i ∈ r.q ∧ r.q = {r.i, other r.q r.i})
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
    {e : Finset V} (he : e ∈ internalGroup H r)
    (q T : Finset V) (i : V) (hs : PacketRow H q T i e),
      q = r.q ∧ T = r.T ∧ i = r.i)
    ∧ (∀ (H : Finset (Finset V)) (r s : Row V)
    (hr : Valid H r) (hs : Valid H s) (hne : r ≠ s),
      Disjoint (internalGroup H r) (internalGroup H s))
    ∧ (∀ (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
    {e : Finset V} (he : e ∈ rowMembers r),
      assigned r ∈ localVertices H e)
    ∧ (∀ (H : Finset (Finset V)) (hd : DUF H)
    (r : Row V) (hr : Valid H r) {e : Finset V} (he : e ∈ rowMembers r),
      ∃ x ∈ localNeighbors H e (assigned r),
      ∃ y ∈ localNeighbors H e (assigned r), x.1 ≠ y.1)
    ∧ (∀ (H : Finset (Finset V)) (r s : Row V)
    (hr : Valid H r) (hs : Valid H s) (h : assigned r = assigned s),
      r = s)
    ∧ (∀ (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (w l : U H e)
    (hm : Mixed (graph H e) (coloring H e he3) w)
    (hwl : (graph H e).Adj w l)
    (hclass : (univ.filter fun z : U H e =>
      coloring H e he3 z = coloring H e he3 l) = {l})
    (hl : (graph H e).degree l = 1),
      ∃ r : Row V, ∃ b : V, Valid H r ∧ b ∈ marks H r ∧
      e ∈ internalGroup H r ∧ PacketRow H r.q r.T r.i e ∧
      w.val = assigned r ∧
      neighbors H {r.i, b} = r.T.erase b ∧
      common H (r.T.erase b) = r.q.image (fun j => {j, b}) ∧
      (∀ q T i, PacketRow H q T i e → q = r.q ∧ T = r.T ∧ i = r.i)) := by
  have color_eq_iff (H : Finset (Finset V)) (e : Finset V)
      (he3 : e.card = 3) (w z : U H e) :
      coloring H e he3 w = coloring H e he3 z ↔ w.val.1 = z.val.1 := by
    change colorEquiv e he3 _ = colorEquiv e he3 _ ↔ _
    rw [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]
  have neighbor_transport (H : Finset (Finset V)) (e : Finset V) (w : U H e) :
      ((graph H e).neighborFinset w).image Subtype.val = localNeighbors H e w.val := by
    ext z
    simp only [mem_image, SimpleGraph.mem_neighborFinset, localNeighbors, mem_filter]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hz, ha⟩
      exact ⟨⟨z, hz⟩, ha, rfl⟩
  have degree_transport (H : Finset (Finset V)) (e : Finset V) (w : U H e) :
      (graph H e).degree w = (localNeighbors H e w.val).card := by
    rw [← neighbor_transport H e w, card_image_of_injective _ Subtype.val_injective]
    rfl
  have color_fiber_transport (H : Finset (Finset V)) (e : Finset V)
      (he3 : e.card = 3) (a : e) :
      (univ.filter fun w : U H e => coloring H e he3 w = colorEquiv e he3 a).card =
        ((localVertices H e).filter fun w => w.1 = a.val).card := by
    apply card_bij (fun w _ => w.val)
    · intro w hw
      have hc := (mem_filter.mp hw).2
      have ha : w.val.1 = a.val := congrArg Subtype.val ((colorEquiv e he3).injective hc)
      exact mem_filter.mpr ⟨w.property, ha⟩
    · intro w hw z hz h
      exact Subtype.ext h
    · intro w hw
      obtain ⟨hw, ha⟩ := mem_filter.mp hw
      refine ⟨⟨w, hw⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      change colorEquiv e he3 _ = colorEquiv e he3 a
      congr 1
      exact Subtype.ext ha
  have mixed_iff (H : Finset (Finset V)) (e : Finset V)
      (he3 : e.card = 3) (w : U H e) :
      ColoredReciprocalDeletion.Mixed (graph H e) (coloring H e he3) w ↔
        ∃ r ∈ localNeighbors H e w.val, ∃ z ∈ localNeighbors H e w.val, r.1 ≠ z.1 := by
    constructor
    · rintro ⟨r, z, hr, hz, hc⟩
      refine ⟨r.val, ?_, z.val, ?_, fun h => hc ((color_eq_iff H e he3 r z).mpr h)⟩
      · simpa only [localNeighbors, mem_filter, graph] using And.intro r.property hr
      · simpa only [localNeighbors, mem_filter, graph] using And.intro z.property hz
    · rintro ⟨r, hr, z, hz, hne⟩
      simp only [localNeighbors, mem_filter] at hr hz
      obtain ⟨hrV, hr⟩ := hr
      obtain ⟨hzV, hz⟩ := hz
      refine ⟨⟨r, hrV⟩, ⟨z, hzV⟩, hr, hz, ?_⟩
      exact fun h => hne ((color_eq_iff H e he3 _ _).mp h)
  have mixed_degree (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (w : U H e)
      (hm : ColoredReciprocalDeletion.Mixed (graph H e) (coloring H e he3) w) :
      (graph H e).degree w = 2 := by
    rw [degree_transport]
    exact (local_correspondence H hd e he he3 w.val w.property).2
      ((mixed_iff H e he3 w).mp hm)
  have potential_transport (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) :
      ColoredReciprocalDeletion.potential (graph H e) (coloring H e he3) = weight H e := by

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

    rw [local_weight H hd e he he3]
    unfold ColoredReciprocalDeletion.potential
    congr 1
    · calc
        _ = ∑ a : e, 1 / (((localVertices H e).filter fun w => w.1 = a.val).card + 1 : ℚ) := by
          symm
          apply Fintype.sum_equiv (colorEquiv e he3)
          intro a
          rw [color_fiber_transport H e he3 a]
        _ = _ := Finset.sum_coe_sort e
          (fun a : V => 1 / (((localVertices H e).filter fun v => v.1 = a).card + 1 : ℚ))
    · congr 1
      apply sum_bij (fun w _ => w.val)
      · intro w _; exact w.property
      · intro w _ z _ h; exact Subtype.ext h
      · intro w hw; exact ⟨⟨w, hw⟩, mem_univ _, rfl⟩
      · intro w _; rw [degree_transport]
  have leaf_iff (H : Finset (Finset V)) (e : Finset V) (w l : U H e)
      (hwl : (graph H e).Adj w l) :
      (graph H e).degree l = 1 ↔ (graph H e).neighborFinset l = {w} := by
    constructor
    · intro h
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simp only [singleton_subset_iff, SimpleGraph.mem_neighborFinset]
        exact (graph H e).adj_symm hwl
      · simpa only [card_singleton, SimpleGraph.card_neighborFinset_eq_degree] using h.le
    · intro h
      rw [← SimpleGraph.card_neighborFinset_eq_degree, h, card_singleton]
  have singleton_leaf_mark (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (w l : U H e)
      (hm : ColoredReciprocalDeletion.Mixed (graph H e) (coloring H e he3) w)
      (hwl : (graph H e).Adj w l)
      (hclass : (univ.filter fun z : U H e =>
        coloring H e he3 z = coloring H e he3 l) = {l})
      (hl : (graph H e).degree l = 1) :
      ∃ u v a b c0 : V,
        [u, v, a, b, c0].Pairwise (· ≠ ·) ∧
        w.val = (u, v) ∧ l.val = (a, c0) ∧ e = {u, a, b} ∧
        common H {u, v} = ({a, b, c0} : Finset V).powersetCard 2 ∧
        neighbors H {u, b} = {a, c0} ∧
        common H {a, c0} = {{u, b}, {v, b}} ∧
        localNeighbors H e (u, v) = {(a, c0), (b, c0)} ∧
        PacketRow H {u, v} {a, b, c0} u e := by
    obtain ⟨⟨u, v⟩, hw⟩ := w
    obtain ⟨⟨a, c0⟩, hlV⟩ := l
    obtain ⟨hu, hv, hvH⟩ := (mem_filter.mp hw).2
    obtain ⟨ha, hcE, hcH⟩ := (mem_filter.mp hlV).2
    obtain ⟨hua, hvc, hvcH⟩ := hwl
    change u ≠ a at hua
    change v ≠ c0 at hvc
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    have hcard : ((e.erase u).erase a).card = 1 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨hua.symm, ha⟩), card_erase_of_mem hu, he3]
    obtain ⟨b, hb⟩ := card_eq_one.mp hcard
    have hbE : b ∈ e := mem_of_mem_erase (mem_of_mem_erase
      (hb.symm ▸ mem_singleton_self b))
    have hub : u ≠ b := by
      have := (mem_erase.mp (mem_of_mem_erase (hb.symm ▸ mem_singleton_self b))).1
      exact this.symm
    have hab : a ≠ b := by
      have := (mem_erase.mp (hb.symm ▸ mem_singleton_self b)).1
      exact this.symm
    have heq : e = {u, a, b} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨hu, ha, hbE⟩
      · simp [he3, hua, hub, hab]
    have huc : u ≠ c0 := fun h => hcE (h ▸ hu)
    have hac : a ≠ c0 := fun h => hcE (h ▸ ha)
    have hbc : b ≠ c0 := fun h => hcE (h ▸ hbE)
    have hva : v ≠ a := fun h => hv (h.symm ▸ ha)
    have hvb : v ≠ b := fun h => hv (h.symm ▸ hbE)
    have hdist : [u, v, a, b, c0].Pairwise (· ≠ ·) := by
      simp [List.pairwise_cons, huv, hua, hub, huc, hva, hvb, hvc, hab, hac, hbc]
    obtain ⟨T, hrow, _⟩ :=
      (mixed_packet_correspondence H hd e he he3 (u, v) hw).mp
        ((mixed_iff H e he3 ⟨(u, v), hw⟩).mp hm)
    have hbcK : ({b, c0} : Finset V) ∈ common H {u, v} := by
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      refine ⟨by simp [hbc], ⟨by simp [hub, huc], ?_⟩,
        ⟨by simp [hvb, hvc], ?_⟩⟩
      · convert hcH using 1
        ext t
        simp [heq, hua, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [heq, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hvcH
    have hTeq : T = {a, b, c0} := by
      obtain ⟨_, hT3, hK, _, p, hp, hep⟩ := hrow
      have hpT := (mem_powersetCard.mp hp).1
      have haT : a ∈ T := hpT (by
        have h := hep ▸ ha
        simpa [hua.symm] using h)
      have hbT : b ∈ T := hpT (by
        have h := hep ▸ hbE
        simpa [hub.symm] using h)
      have hcT : c0 ∈ T := (mem_powersetCard.mp (hK ▸ hbcK)).1 (by simp)
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨haT, hbT, hcT⟩
      · simp [hT3, hab, hac, hbc]
    subst T
    have hK := hrow.2.2.1
    have extend (p : Finset V) (hp : p ∈ ({a, b, c0} : Finset V).powersetCard 2)
        (i : V) (hi : i ∈ ({u, v} : Finset V)) : i ∉ p ∧ insert i p ∈ H := by
      have hpK : p ∈ common H {u, v} := hK.symm ▸ hp
      simpa only [neighbors, mem_filter, mem_univ, true_and] using (mem_filter.mp hpK).2 hi
    have huab := extend {a, b} (by simp [mem_powersetCard, hab]) u (by simp)
    have hubc := extend {b, c0} (by simp [mem_powersetCard, hbc]) u (by simp)
    have hvab := extend {a, b} (by simp [mem_powersetCard, hab]) v (by simp)
    have hvbc := extend {b, c0} (by simp [mem_powersetCard, hbc]) v (by simp)
    have huac := extend {a, c0} (by simp [mem_powersetCard, hac]) u (by simp)
    have hvac := extend {a, c0} (by simp [mem_powersetCard, hac]) v (by simp)
    have hz : (b, c0) ∈ localNeighbors H e (u, v) := by
      simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and]
      refine ⟨⟨hbE, hcE, ?_⟩, hub, hvc, ?_⟩
      · convert huac.2 using 1
        ext t
        simp [heq, hub, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [heq, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hvac.2
    have hln : localNeighbors H e (u, v) = {(a, c0), (b, c0)} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simp only [insert_subset_iff, singleton_subset_iff]
        refine ⟨?_, hz⟩
        simpa only [localNeighbors, mem_filter, adjacent] using
          And.intro hlV (And.intro hua (And.intro hvc hvcH))
      · have hdeg := mixed_degree H hd e he he3 ⟨(u, v), hw⟩ hm
        rw [degree_transport] at hdeg
        simp [hdeg, hab]
    have hn : neighbors H {u, b} = {a, c0} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxub, hxH⟩ := (mem_filter.mp hx).2
        by_cases hxa : x = a
        · simp [hxa]
        have hxE : x ∉ e := by
          simpa [heq, hxa, or_comm, or_left_comm] using hxub
        have hxV : (a, x) ∈ localVertices H e := by
          simp only [localVertices, mem_filter, mem_univ, true_and]
          refine ⟨ha, hxE, ?_⟩
          simpa [heq, hua, hab, erase_insert_of_ne] using hxH
        have hsame : coloring H e he3 ⟨(a, x), hxV⟩ =
            coloring H e he3 ⟨(a, c0), hlV⟩ := (color_eq_iff H e he3 _ _).mpr rfl
        have hxclass : (⟨(a, x), hxV⟩ : U H e) ∈ ({⟨(a, c0), hlV⟩} : Finset (U H e)) := by
          rw [← hclass]
          exact mem_filter.mpr ⟨mem_univ _, hsame⟩
        have hxc : x = c0 := congrArg (fun z : U H e => z.val.2) (mem_singleton.mp hxclass)
        simp [hxc]
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp only [neighbors, mem_filter, mem_univ, true_and]
          exact ⟨by simp [hua.symm, hab], by
            simpa only [insert_comm] using huab.2⟩
        · simp only [neighbors, mem_filter, mem_univ, true_and]
          exact ⟨by simp [huc.symm, hbc.symm], by
            convert hubc.2 using 1
            ext t
            simp only [mem_insert, mem_singleton]
            tauto⟩
    have hkcard : (common H {a, c0}).card = 2 := by
      have hc := (local_correspondence H hd e he he3 (a, c0) hlV).1
      rw [← degree_transport H e ⟨(a, c0), hlV⟩, hl] at hc
      exact hc.symm
    have hk : common H {a, c0} = {{u, b}, {v, b}} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · intro p hp
        simp only [mem_insert, mem_singleton] at hp
        rcases hp with rfl | rfl
        · simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
            insert_subset_iff, singleton_subset_iff]
          exact ⟨by simp [hub], hn.symm ▸ (by simp), hn.symm ▸ (by simp)⟩
        · simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
            insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
          refine ⟨by simp [hvb], ⟨by simp [hva.symm, hab], ?_⟩,
            ⟨by simp [hvc.symm, hbc.symm], ?_⟩⟩
          · simpa only [insert_comm] using hvab.2
          · convert hvbc.2 using 1
            ext t
            simp only [mem_insert, mem_singleton]
            tauto
      · have hpne : ({u, b} : Finset V) ≠ {v, b} := by
          intro h
          have hum : u ∈ ({v, b} : Finset V) := h ▸ (by simp)
          simp [huv, hub] at hum
        simp [hkcard, hpne]
    exact ⟨u, v, a, b, c0, hdist, rfl, rfl, heq, hK, hn, hk, hln, hrow⟩
  have extend (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {p : Finset V} (hp : p ∈ r.T.powersetCard 2) {j : V} (hj : j ∈ r.q) :
      j ∉ p ∧ insert j p ∈ H := by
    have hm : p ∈ common H r.q := hr.2.2.1.symm ▸ hp
    have := (mem_filter.mp hm).2 hj
    simpa only [neighbors, mem_filter, mem_univ, true_and] using this
  have row_disjoint (H : Finset (Finset V)) (r : Row V) (hr : Valid H r) :
      Disjoint r.q r.T := by
    apply disjoint_left.mpr
    intro j hj hjT
    have hU : (r.T.powersetCard 2).biUnion id = r.T :=
      powersetCard_biUnion (by decide) (by rw [hr.2.1]; decide)
    obtain ⟨p, hp, hjp⟩ := mem_biUnion.mp (hU.symm ▸ hjT)
    exact (extend H r hr hp hj).1 hjp
  have row_i_notMem (H : Finset (Finset V)) (r : Row V) (hr : Valid H r) :
      r.i ∉ r.T := fun hi => disjoint_left.mp (row_disjoint H r hr) hr.2.2.2 hi
  have insert_pair_injective (H : Finset (Finset V)) (r : Row V)
      (hr : Valid H r) : Set.InjOn (fun p : Finset V => insert r.i p) (r.T.powersetCard 2) := by
    intro p hp s hs heq
    have hp' : r.i ∉ p := fun h => row_i_notMem H r hr ((mem_powersetCard.mp hp).1 h)
    have hs' : r.i ∉ s := fun h => row_i_notMem H r hr ((mem_powersetCard.mp hs).1 h)
    simpa only [erase_insert hp', erase_insert hs'] using congrArg (fun e => e.erase r.i) heq
  have row_members_facts (H : Finset (Finset V)) (r : Row V) (hr : Valid H r) :
      (rowMembers r).card = 3 ∧ ∀ e ∈ rowMembers r, e ∈ H ∧ e.card = 3 ∧
        PacketRow H r.q r.T r.i e := by
    constructor
    · rw [rowMembers, (card_image_iff.mpr (insert_pair_injective H r hr)),
        card_powersetCard, hr.2.1]
      decide
    · intro e he
      obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      have hx := extend H r hr hp hr.2.2.2
      refine ⟨hx.2, ?_, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, p, hp, rfl⟩
      rw [card_insert_of_notMem hx.1, (mem_powersetCard.mp hp).2]
  have recipient_mem (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {b : V} (hb : b ∈ r.T) : recipient r b ∈ rowMembers r := by
    apply mem_image.mpr
    refine ⟨r.T.erase b, mem_powersetCard.mpr ⟨erase_subset _ _, ?_⟩, rfl⟩
    rw [card_erase_of_mem hb, hr.2.1]
  have recipient_injective (H : Finset (Finset V)) (r : Row V) (hr : Valid H r) :
      Set.InjOn (recipient r) r.T := by
    intro b hb c hc h
    have hi : r.i ∉ r.T := row_i_notMem H r hr
    have hi' (x : V) : r.i ∉ r.T.erase x := fun h => hi (mem_of_mem_erase h)
    have hh : r.T.erase b = r.T.erase c := by
      simpa only [recipient, erase_insert (hi' b), erase_insert (hi' c)] using
        congrArg (fun e => e.erase r.i) h
    exact (erase_inj r.T hb).mp hh
  have endpoints_eq (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {b : V} (hb : b ∈ r.T) :
      (rowMembers r).erase (recipient r b) = (r.T.erase b).image (recipient r) := by
    have hsub : (r.T.erase b).image (recipient r) ⊆
        (rowMembers r).erase (recipient r b) := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := mem_image.mp he
      exact mem_erase.mpr ⟨fun hh => (mem_erase.mp ha).1
        (recipient_injective H r hr (mem_of_mem_erase ha) hb hh),
        recipient_mem H r hr (mem_of_mem_erase ha)⟩
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [card_erase_of_mem (recipient_mem H r hr hb), (row_members_facts H r hr).1,
      card_image_iff.mpr ((recipient_injective H r hr).mono (erase_subset b r.T)),
      card_erase_of_mem hb, hr.2.1]
  have internal_subset (H : Finset (Finset V)) (r : Row V) :
      internalGroup H r ⊆ rowMembers r := by
    intro e he
    obtain ⟨b, _, hb⟩ := mem_biUnion.mp he
    exact mem_of_mem_erase hb
  have internal_zero (H : Finset (Finset V)) (r : Row V)
      (h : (marks H r).card = 0) : internalGroup H r = ∅ := by
    simp [internalGroup, card_eq_zero.mp h]
  have internal_one (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      (h : (marks H r).card = 1) :
      ∃ b ∈ marks H r, marks H r = {b} ∧
        internalGroup H r = (rowMembers r).erase (recipient r b) ∧
        internalGroup H r = (r.T.erase b).image (recipient r) ∧
        (internalGroup H r).card = 2 ∧ recipient r b ∉ internalGroup H r := by
    obtain ⟨b, hb⟩ := card_eq_one.mp h
    have hbm : b ∈ marks H r := hb.symm ▸ mem_singleton_self b
    have hbT : b ∈ r.T := (mem_filter.mp hbm).1
    have hg : internalGroup H r = (rowMembers r).erase (recipient r b) := by
      simp [internalGroup, hb]
    refine ⟨b, hbm, hb, hg, hg.trans (endpoints_eq H r hr hbT), ?_, ?_⟩
    · rw [hg, card_erase_of_mem (recipient_mem H r hr hbT), (row_members_facts H r hr).1]
    · rw [hg]; exact notMem_erase _ _
  have internal_many (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      (h : 2 ≤ (marks H r).card) : internalGroup H r = rowMembers r := by
    apply Subset.antisymm (internal_subset H r)
    obtain ⟨b, hb, c, hc, hbc⟩ := one_lt_card.mp (show 1 < (marks H r).card by omega)
    have hne : recipient r b ≠ recipient r c := fun heq =>
      hbc (recipient_injective H r hr (mem_filter.mp hb).1 (mem_filter.mp hc).1 heq)
    intro e he
    by_cases heb : e = recipient r b
    · apply mem_biUnion.mpr
      exact ⟨c, hc, mem_erase.mpr ⟨by simpa [heb] using hne, he⟩⟩
    · exact mem_biUnion.mpr ⟨b, hb, mem_erase.mpr ⟨heb, he⟩⟩
  have other_spec (H : Finset (Finset V)) (r : Row V) (hr : Valid H r) :
      other r.q r.i ≠ r.i ∧ other r.q r.i ∈ r.q ∧ r.q = {r.i, other r.q r.i} := by
    obtain ⟨j, hj⟩ := card_eq_one.mp (show (r.q.erase r.i).card = 1 by
      rw [card_erase_of_mem hr.2.2.2, hr.1])
    have hn : (r.q.erase r.i).Nonempty := ⟨j, hj.symm ▸ mem_singleton_self j⟩
    have hm : other r.q r.i ∈ r.q.erase r.i := by
      simp only [other, dif_pos hn]
      exact hn.choose_spec
    have ho : other r.q r.i = j := by simpa [hj] using hm
    refine ⟨(mem_erase.mp hm).1, (mem_erase.mp hm).2, ?_⟩
    rw [ho, ← hj, insert_erase hr.2.2.2]
  have internal_endpoint (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {e : Finset V} (he : e ∈ internalGroup H r) :
      ∃ b ∈ marks H r, ∃ v a c : V,
        [r.i, v, a, b, c].Pairwise (· ≠ ·) ∧ r.q = {r.i, v} ∧ r.T = {a, b, c} ∧
        neighbors H {r.i, b} = {a, c} ∧ common H {a, c} = {{r.i, b}, {v, b}} ∧
        e = {r.i, a, b} := by
    classical
    obtain ⟨b, hbm, heb⟩ := mem_biUnion.mp he
    obtain ⟨hne, hem⟩ := mem_erase.mp heb
    obtain ⟨hbT, hn, hk⟩ := mem_filter.mp hbm
    obtain ⟨p, hp, hep⟩ := mem_image.mp hem
    obtain ⟨hpT, hp2⟩ := mem_powersetCard.mp hp
    have hbp : b ∈ p := by
      by_contra hbp
      have hsub : p ⊆ r.T.erase b := by
        intro x hx
        exact mem_erase.mpr ⟨fun hh => hbp (hh ▸ hx), hpT hx⟩
      have hpeq : p = r.T.erase b := eq_of_subset_of_card_le hsub (by
        rw [card_erase_of_mem hbT, hr.2.1, hp2])
      exact hne (by rw [← hep, hpeq]; rfl)
    obtain ⟨a, ha⟩ := card_eq_one.mp (show (p.erase b).card = 1 by
      rw [card_erase_of_mem hbp, hp2])
    have hap : a ∈ p := mem_of_mem_erase (ha.symm ▸ mem_singleton_self a)
    have hab : a ≠ b := (mem_erase.mp (ha.symm ▸ mem_singleton_self a)).1
    have hpab : p = {b, a} := by rw [← ha, insert_erase hbp]
    obtain ⟨c, hc⟩ := card_eq_one.mp (show (r.T \ p).card = 1 by
      rw [card_sdiff_of_subset hpT, hr.2.1, hp2])
    have hcT : c ∈ r.T := (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).1
    have hcp : c ∉ p := (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).2
    have hca : c ≠ a := fun h => hcp (h.symm ▸ hap)
    have hcb : c ≠ b := fun h => hcp (h.symm ▸ hbp)
    have hT : r.T = {a, b, c} := by
      have ht : r.T = insert c p := by
        rw [← singleton_union, ← hc, sdiff_union_of_subset hpT]
      rw [ht, hpab]
      ext x; simp [or_comm, or_left_comm]
    have hTb : r.T.erase b = {a, c} := by
      simp [hT, hab, hcb.symm, erase_insert_of_ne]
    let v := other r.q r.i
    have hv := other_spec H r hr
    have huv : r.i ≠ v := Ne.symm hv.1
    have hqv : r.q = {r.i, v} := hv.2.2
    have hdis := disjoint_left.mp (row_disjoint H r hr)
    have huT := row_i_notMem H r hr
    have hvT : v ∉ r.T := fun h => hdis hv.2.1 h
    have hua : r.i ≠ a := fun h => huT (h.symm ▸ hpT hap)
    have hub : r.i ≠ b := fun h => huT (h.symm ▸ hbT)
    have huc : r.i ≠ c := fun h => huT (h.symm ▸ hcT)
    have hva : v ≠ a := fun h => hvT (h.symm ▸ hpT hap)
    have hvb : v ≠ b := fun h => hvT (h.symm ▸ hbT)
    have hvc : v ≠ c := fun h => hvT (h.symm ▸ hcT)
    refine ⟨b, hbm, v, a, c, ?_, hv.2.2, hT, ?_, ?_, ?_⟩
    · simp [List.pairwise_cons, huv, hua, hub, huc, hva, hvb, hvc,
        hab, hca.symm, hcb.symm]
    · simpa only [hTb] using hn
    · simpa only [hTb, hqv, image_insert, image_singleton] using hk
    · rw [← hep, hpab, pair_comm b a]
  have internal_owner (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {e : Finset V} (he : e ∈ internalGroup H r)
      (q T : Finset V) (i : V) (hs : PacketRow H q T i e) :
      q = r.q ∧ T = r.T ∧ i = r.i := by
    obtain ⟨b, _, v, a, c, hd, hq, hT, hn, hk, heq⟩ := internal_endpoint H r hr he
    have ho := marked_endpoint_ownership H r.i v a b c hd hn hk q T e i (Or.inl heq) hs
    exact ⟨ho.1.trans hq.symm, ho.2.1.trans hT.symm, ho.2.2.1⟩
  have internal_disjoint (H : Finset (Finset V)) (r s : Row V)
      (hr : Valid H r) (hs : Valid H s) (hne : r ≠ s) :
      Disjoint (internalGroup H r) (internalGroup H s) := by
    apply disjoint_left.mpr
    intro e her hes
    have hp := ((row_members_facts H s hs).2 e (internal_subset H s hes)).2.2
    have ho := internal_owner H r hr her s.q s.T s.i hp
    apply hne
    cases r; cases s
    simp_all
  have assigned_actual (H : Finset (Finset V)) (r : Row V) (hr : Valid H r)
      {e : Finset V} (he : e ∈ rowMembers r) : assigned r ∈ localVertices H e := by
    obtain ⟨p, hp, rfl⟩ := mem_image.mp he
    have ho := other_spec H r hr
    have hi := (extend H r hr hp hr.2.2.2).1
    have hj := extend H r hr hp ho.2.1
    simp only [localVertices, mem_filter, mem_univ, true_and, assigned]
    exact ⟨mem_insert_self _ _, by simp [ho.1, hj.1], by simpa [erase_insert hi] using hj.2⟩
  have assigned_mixed (H : Finset (Finset V)) (hd : DUF H)
      (r : Row V) (hr : Valid H r) {e : Finset V} (he : e ∈ rowMembers r) :
      ∃ x ∈ localNeighbors H e (assigned r),
        ∃ y ∈ localNeighbors H e (assigned r), x.1 ≠ y.1 := by
    have hf := (row_members_facts H r hr).2 e he
    have ho := (other_spec H r hr).2.2
    have hK : common H {(assigned r).1, (assigned r).2} = r.T.powersetCard 2 := by
      simpa only [assigned, ← ho] using hr.2.2.1
    apply (mixed_packet_correspondence H hd e hf.1 hf.2.1 (assigned r)
      (assigned_actual H r hr he)).mpr
    refine ⟨r.T, ?_, ?_⟩
    · simpa only [assigned, ← ho] using hf.2.2
    · intro T hT
      exact eq_of_powersetCard_eq (r := 2) (hT.2.1.trans hr.2.1.symm) (by decide)
        (by rw [hT.2.1]; decide) (hT.2.2.1.symm.trans hK)
  have assigned_injective (H : Finset (Finset V)) (r s : Row V)
      (hr : Valid H r) (hs : Valid H s) (h : assigned r = assigned s) : r = s := by
    have hi : r.i = s.i := congrArg Prod.fst h
    have hj : other r.q r.i = other s.q s.i := congrArg Prod.snd h
    have hq : r.q = s.q := (other_spec H r hr).2.2.trans
      ((congrArg₂ (fun i j : V => ({i, j} : Finset V)) hi hj).trans
        (other_spec H s hs).2.2.symm)
    have hT : r.T = s.T := eq_of_powersetCard_eq (r := 2) (hr.2.1.trans hs.2.1.symm)
      (by decide) (by rw [hr.2.1]; decide) (by rw [← hr.2.2.1, ← hs.2.2.1, hq])
    cases r; cases s
    simp_all
  have configuration_coverage (H : Finset (Finset V)) (hd : DUF H)
      (e : Finset V) (he : e ∈ H) (he3 : e.card = 3) (w l : U H e)
      (hm : Mixed (graph H e) (coloring H e he3) w)
      (hwl : (graph H e).Adj w l)
      (hclass : (univ.filter fun z : U H e =>
        coloring H e he3 z = coloring H e he3 l) = {l})
      (hl : (graph H e).degree l = 1) :
      ∃ r : Row V, ∃ b : V, Valid H r ∧ b ∈ marks H r ∧
        e ∈ internalGroup H r ∧ PacketRow H r.q r.T r.i e ∧
        w.val = assigned r ∧
        neighbors H {r.i, b} = r.T.erase b ∧
        common H (r.T.erase b) = r.q.image (fun j => {j, b}) ∧
        (∀ q T i, PacketRow H q T i e → q = r.q ∧ T = r.T ∧ i = r.i) := by
    obtain ⟨u, v, a, b, c, hdist, hw, _, heq, hp, hn, hk, _, hpacket⟩ :=
      singleton_leaf_mark H hd e he he3 w l hm hwl hclass hl
    have hne : u ≠ v ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      simp [List.pairwise_cons] at hdist
      tauto
    let r : Row V := ⟨{u,v}, {a,b,c}, u⟩
    have hr : Valid H r := ⟨hpacket.1, hpacket.2.1, hp, by simp [r]⟩
    have hTb : r.T.erase b = {a,c} := by
      simp [r, hne.2.1, hne.2.2.2, erase_insert_of_ne]
    have hmark : b ∈ marks H r := by
      apply mem_filter.mpr
      refine ⟨by simp [r], ?_, ?_⟩
      · simpa only [hTb] using hn
      · simpa only [hTb, r, image_insert, image_singleton] using hk
    have hem : e ∈ rowMembers r := by
      obtain ⟨p, hp', hep⟩ := hpacket.2.2.2.2
      exact mem_image.mpr ⟨p, hp', hep.symm⟩
    have hbr : b ∉ recipient r b := by
      have hub : u ≠ b := by simp [List.pairwise_cons] at hdist; tauto
      simp [recipient, r, hub.symm]
    have hbe : b ∈ e := by simp [heq]
    have hei : e ∈ internalGroup H r :=
      mem_biUnion.mpr ⟨b, hmark, mem_erase.mpr ⟨fun h => hbr (h ▸ hbe), hem⟩⟩
    have hov : other r.q r.i = v := by
      have ho := other_spec H r hr
      have hmem : other r.q r.i = u ∨ other r.q r.i = v := by simpa [r] using ho.2.1
      exact hmem.resolve_left ho.1
    refine ⟨r, b, hr, hmark, hei, hpacket, ?_, (mem_filter.mp hmark).2.1,
      (mem_filter.mp hmark).2.2, ?_⟩
    · simpa only [assigned, hov] using hw
    · intro q T i hs
      exact internal_owner H r hr hei q T i hs
  exact ⟨color_eq_iff, neighbor_transport, degree_transport, mixed_iff, mixed_degree,
    potential_transport, leaf_iff, row_disjoint, row_i_notMem, row_members_facts, recipient_mem,
    internal_subset, internal_zero, internal_one, internal_many, other_spec, internal_owner,
    internal_disjoint, assigned_actual, assigned_mixed, assigned_injective,
    configuration_coverage⟩

end D5.S3.Combinatorics.Graph.DUFRowGeometry
