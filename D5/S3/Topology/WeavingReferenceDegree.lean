/- GID: D5/S3/Topology/WeavingReferenceDegree
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingReferenceDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: An interval-first ordering of the actual reference graph has forward degree at most four. -/

import D5.S3.Topology.WeavingReferenceIncidence
import D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate
import Mathlib.Logic.Equiv.Fin.Basic

/-! An interval-first ordering of the actual reference graph has forward degree at most four. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.WeavingReferenceDegree

open D5.S3.Topology.WeavingDiagramPorts
open D5.S3.Topology.WeavingMixedComponents
open D5.S3.Topology.WeavingReferenceIncidence
open D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate

abbrev G (P : Parameters) (p : ℕ) (hp : p < 2) := referenceGraph P p hp Finset.univ

def IsHub (P : Parameters) (p : ℕ) (hp : p < 2) (v : Circle P p) : Prop :=
  (vertexCode P p hp v).1 = 0 ∨ (vertexCode P p hp v).1 = P.n+1

abbrev Incident (P : Parameters) (p : ℕ) (v : Circle P p) :=
  {a : Crossing P // v = (edgeEnds P p a.1 a.2).1 ∨
    v = (edgeEnds P p a.1 a.2).2}

/-- An interval meets two row edges and at most one connector on each side.
The formula includes boundary connectors; their hub degree is irrelevant. -/
theorem interval_incident_shape (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : cup p i) (t : ZMod P.m)
    (a : Incident P p (circle P p (t,i,.bl))) :
    (a.val.2 = i ∧ (a.val.1 = t ∨ a.val.1 = t+1)) ∨
    (a.val.2.val+1 = i.val ∧ a.val.1 = t+1) ∨
    (i.val+1 = a.val.2.val ∧ a.val.1 = t) := by
  rcases a with ⟨⟨u,j⟩,ha⟩
  have hv : vertexCode P p hp (circle P p (t,i,.bl)) = (i.val+1,t) := by
    simp [vertexCode,circle,code,hi]
  by_cases hj : cup p j
  · have hc := endpointCodes_cup P p hp u j hj
    rcases ha with ha | ha
    · have he := congrArg (vertexCode P p hp) ha
      have hleft := congrArg Prod.fst hc
      change vertexCode P p hp (edgeEnds P p u j).1 = (j.val+1,u-1) at hleft
      rw [hv,hleft] at he
      have hij : j = i := Fin.ext (by have := congrArg Prod.fst he; omega)
      have htime : u = t+1 := by
        have ht := congrArg Prod.snd he
        linear_combination -ht
      exact Or.inl ⟨hij,Or.inr htime⟩
    · have he := congrArg (vertexCode P p hp) ha
      have hright := congrArg Prod.snd hc
      change vertexCode P p hp (edgeEnds P p u j).2 = (j.val+1,u) at hright
      rw [hv,hright] at he
      have hij : j = i := Fin.ext (by have := congrArg Prod.fst he; omega)
      exact Or.inl ⟨hij,Or.inl (congrArg Prod.snd he).symm⟩
  · have hc := endpointCodes_vertical P p hp u j hj
    rcases ha with ha | ha
    · have he := congrArg (vertexCode P p hp) ha
      have hleft := congrArg Prod.fst hc
      change vertexCode P p hp (edgeEnds P p u j).1 =
        (j.val,if j.val=0 then 0 else u) at hleft
      rw [hv,hleft] at he
      have hcol : i.val+1 = j.val := congrArg Prod.fst he
      have hz : j.val ≠ 0 := by omega
      have ht : t = u := by simpa [hz] using congrArg Prod.snd he
      exact Or.inr (Or.inr ⟨hcol,ht.symm⟩)
    · have he := congrArg (vertexCode P p hp) ha
      have hright := congrArg Prod.snd hc
      change vertexCode P p hp (edgeEnds P p u j).2 =
        (j.val+2,if j.val+1<P.n then u-1 else 0) at hright
      rw [hv,hright] at he
      have hcol : j.val+1 = i.val := by have := congrArg Prod.fst he; omega
      have hr : j.val+1 < P.n := by have := i.isLt; omega
      have ht : t = u-1 := by simpa [hr] using congrArg Prod.snd he
      exact Or.inr (Or.inl ⟨hcol,by linear_combination -ht⟩)

def incidentSlot (P : Parameters) (p : ℕ) (i : Fin P.n) (t : ZMod P.m)
    (a : Incident P p (circle P p (t,i,.bl))) : Fin 4 :=
  if a.val.2 = i then if a.val.1 = t then 0 else 1
  else if a.val.2.val+1 = i.val then 2 else 3

theorem incidentSlot_injective (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : cup p i) (t : ZMod P.m) :
    Function.Injective (incidentSlot P p i t) := by
  intro a b hs
  have ha := interval_incident_shape P p hp i hi t a
  have hb := interval_incident_shape P p hp i hi t b
  apply Subtype.ext
  apply Prod.ext
  · rcases ha with ⟨hai,hat | hat⟩ | ⟨hai,hat⟩ | ⟨hai,hat⟩ <;>
      rcases hb with ⟨hbi,hbt | hbt⟩ | ⟨hbi,hbt⟩ | ⟨hbi,hbt⟩ <;>
      simp only [incidentSlot] at hs <;> split_ifs at hs <;>
      simp_all [Fin.ext_iff] <;> omega
  · apply Fin.ext
    rcases ha with ⟨hai,hat | hat⟩ | ⟨hai,hat⟩ | ⟨hai,hat⟩ <;>
      rcases hb with ⟨hbi,hbt | hbt⟩ | ⟨hbi,hbt⟩ | ⟨hbi,hbt⟩ <;>
      simp only [incidentSlot] at hs <;> split_ifs at hs <;>
      simp_all [Fin.ext_iff] <;> omega

theorem interval_incident_card (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : cup p i) (t : ZMod P.m) :
    Nat.card (Incident P p (circle P p (t,i,.bl))) ≤ 4 := by
  classical
  have h := Fintype.card_le_of_injective (incidentSlot P p i t)
    (incidentSlot_injective P p hp i hi t)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h

/-- Choosing an incident crossing is injective on the neighbors of a fixed
vertex: its opposite endpoint is uniquely determined. -/
theorem neighbors_le_incident (P : Parameters) (p : ℕ) (hp : p < 2)
    (v : Circle P p) : Nat.card ((G P p hp).neighborSet v) ≤ Nat.card (Incident P p v) := by
  classical
  letI : Fintype (Circle P p) := Fintype.ofFinite _
  have hw (u : (G P p hp).neighborSet v) : ∃ a : Crossing P,
      (v = (edgeEnds P p a.1 a.2).1 ∧ u.val = (edgeEnds P p a.1 a.2).2) ∨
      (v = (edgeEnds P p a.1 a.2).2 ∧ u.val = (edgeEnds P p a.1 a.2).1) := by
    obtain ⟨a,ha,h⟩ := u.property
    exact ⟨a,h⟩
  choose edge hedge using hw
  let f : (G P p hp).neighborSet v → Incident P p v := fun u =>
    ⟨edge u,(hedge u).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  have hinj : Function.Injective f := by
    intro u w h
    have he : edge u = edge w := congrArg Subtype.val h
    have hu := hedge u
    have hh := hedge w
    rw [← he] at hh
    apply Subtype.ext
    have hd := edge_endpoints_distinct P p hp (edge u).1 (edge u).2
    rcases hu with ⟨huv,hu⟩ | ⟨huv,hu⟩ <;>
      rcases hh with ⟨hwv,hh⟩ | ⟨hwv,hh⟩ <;> simp_all
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hinj

/-- Full neighbor cardinal, before deleting hubs or restricting to later vertices. -/
theorem interval_full_degree_le_four (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : cup p i) (t : ZMod P.m) :
    Nat.card ((G P p hp).neighborSet (circle P p (t,i,.bl))) ≤ 4 :=
  (neighbors_le_incident P p hp _).trans (interval_incident_card P p hp i hi t)

theorem hubs_independent (P : Parameters) (p : ℕ) (hp : p < 2)
    (u v : Circle P p) (hu : IsHub P p hp u) (hv : IsHub P p hp v) :
    ¬ (G P p hp).Adj u v := by
  rintro ⟨⟨t,i⟩,ha,h⟩
  by_cases hi : cup p i
  · have hc := endpointCodes_cup P p hp t i hi
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      dsimp [IsHub] at hu hv <;>
      have h₁ := congrArg (fun x => x.1.1) hc <;>
      have h₂ := congrArg (fun x => x.2.1) hc <;>
      dsimp only [endpointCodes] at h₁ h₂ <;>
      rcases hu with hu | hu <;> rcases hv with hv | hv <;> have := i.isLt <;> omega
  · have hc := endpointCodes_vertical P p hp t i hi
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      dsimp [IsHub] at hu hv <;>
      have h₁ := congrArg (fun x => x.1.1) hc <;>
      have h₂ := congrArg (fun x => x.2.1) hc <;>
      dsimp only [endpointCodes] at h₁ h₂ <;>
      rcases hu with hu | hu <;> rcases hv with hv | hv <;>
      have := i.isLt <;> have := P.hn <;> omega

abbrev Interval (P : Parameters) (p : ℕ) := {i : Fin P.n // cup p i} × ZMod P.m
abbrev Hub (P : Parameters) (p : ℕ) :=
  {b : Bool // if b then ¬ cup p (⟨P.n-1,by have := P.hn; omega⟩ : Fin P.n)
    else ¬ cup p (⟨0,by have := P.hn; omega⟩ : Fin P.n)}

def vertexCount (P : Parameters) (p : ℕ) : ℕ :=
  Fintype.card (Interval P p) + Fintype.card (Hub P p)

/-- The actual Fin enumeration: every interval first, then every hub. -/
def vertexOrder (P : Parameters) (p : ℕ) (hp : p < 2) :
    Circle P p ≃ Fin (vertexCount P p) :=
  (circleEquiv P p hp).trans
    ((Equiv.sumCongr (Fintype.equivFin (Interval P p)) (Fintype.equivFin (Hub P p))).trans
      finSumFinEquiv)

def orderedGraph (P : Parameters) (p : ℕ) (hp : p < 2) :
    SimpleGraph (Fin (vertexCount P p)) := (G P p hp).comap (vertexOrder P p hp).symm

def orderedGraphIso (P : Parameters) (p : ℕ) (hp : p < 2) :
    G P p hp ≃g orderedGraph P p hp where
  toEquiv := vertexOrder P p hp
  map_rel_iff' := by simp [orderedGraph]

theorem vertexCount_eq_circle_card (P : Parameters) (p : ℕ) (hp : p < 2) :
    vertexCount P p = Nat.card (Circle P p) := by
  calc
    vertexCount P p = Nat.card (Fin (vertexCount P p)) := by simp
    _ = Nat.card (Circle P p) := (Nat.card_congr (vertexOrder P p hp)).symm

theorem orderedGraph_connected (P : Parameters) (p : ℕ) (hp : p < 2) :
    (orderedGraph P p hp).Connected :=
  (orderedGraphIso P p hp).connected_iff.mp (referenceGraph_connected P p hp)

theorem vertexCount_pos (P : Parameters) (p : ℕ) (hp : p < 2) : 0 < vertexCount P p := by
  have hn := P.hn
  let x : Circle P p := circle P p (0,⟨0,by omega⟩,.tl)
  exact lt_of_le_of_lt (Nat.zero_le _) (vertexOrder P p hp x).isLt

/-- Inverse interval labels are the original bottom-left representatives. -/
theorem interval_inverse (P : Parameters) (p : ℕ) (hp : p < 2)
    (a : Interval P p) :
    (circleEquiv P p hp).symm (.inl a) = circle P p (a.2,a.1.val,.bl) := rfl

theorem hub_inverse_isHub (P : Parameters) (p : ℕ) (hp : p < 2)
    (b : Hub P p) : IsHub P p hp ((circleEquiv P p hp).symm (.inr b)) := by
  rcases b with ⟨b,hb⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb
    left
    change (code P p (0,(⟨0,by have := P.hn; omega⟩ : Fin P.n),.tl)).1 = 0
    simp [code,hb]
  · simp only [↓reduceIte] at hb
    right
    change (code P p (0,(⟨P.n-1,by have := P.hn; omega⟩ : Fin P.n),.tr)).1 = P.n+1
    have hr : ¬ P.n-1+1 < P.n := by have := P.hn; omega
    simp [code,hb,hr]

theorem interval_before_hub (P : Parameters) (p : ℕ) (hp : p < 2)
    (a : Interval P p) (b : Hub P p) :
    vertexOrder P p hp ((circleEquiv P p hp).symm (.inl a)) <
      vertexOrder P p hp ((circleEquiv P p hp).symm (.inr b)) := by
  simp only [vertexOrder,Equiv.trans_apply,Equiv.apply_symm_apply,
    Equiv.sumCongr_apply,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
  change (Fintype.equivFin (Interval P p) a).val <
    Fintype.card (Interval P p) + (Fintype.equivFin (Hub P p) b).val
  have := (Fintype.equivFin (Interval P p) a).isLt
  omega

/-- Actual forward degree in the Fin order, with high-degree hubs LAST. -/
theorem orderedGraph_forward_degree (P : Parameters) (p : ℕ) (hp : p < 2) :
    boundedForwardDegree 4 (orderedGraph P p hp) := by
  classical
  letI : Fintype (Circle P p) := Fintype.ofFinite _
  intro u
  let v := (vertexOrder P p hp).symm u
  have he : vertexOrder P p hp v = u := (vertexOrder P p hp).apply_symm_apply u
  generalize hz : circleEquiv P p hp v = z
  cases z with
  | inl a =>
    have hv : v = circle P p (a.2,a.1.val,.bl) := by
      rw [← interval_inverse P p hp a,← hz,Equiv.symm_apply_apply]
    let f : forwardNeighbors (orderedGraph P p hp) u → (G P p hp).neighborSet v :=
      fun w => ⟨(vertexOrder P p hp).symm w.val,w.property.2⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact (vertexOrder P p hp).symm.injective (congrArg Subtype.val h)
    have hcard := Fintype.card_le_of_injective f hf
    have hdeg := interval_full_degree_le_four P p hp a.1.val a.1.property a.2
    rw [← hv] at hdeg
    have hc : Nat.card (forwardNeighbors (orderedGraph P p hp) u) ≤
        Nat.card ((G P p hp).neighborSet v) := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    exact hc.trans hdeg
  | inr b =>
    have hv : v = (circleEquiv P p hp).symm (.inr b) := by
      rw [← hz,Equiv.symm_apply_apply]
    have hempty : IsEmpty (forwardNeighbors (orderedGraph P p hp) u) := ⟨by
      rintro ⟨w,hw,hvw⟩
      let x := (vertexOrder P p hp).symm w
      generalize hxz : circleEquiv P p hp x = xz
      cases xz with
      | inl a =>
        have hx : x = (circleEquiv P p hp).symm (.inl a) := by
          rw [← hxz,Equiv.symm_apply_apply]
        have hlt := interval_before_hub P p hp a b
        rw [← hx,← hv,he] at hlt
        have hex : vertexOrder P p hp x = w := (vertexOrder P p hp).apply_symm_apply w
        rw [hex] at hlt
        exact (not_lt_of_ge (le_of_lt hlt)) hw
      | inr c =>
        have hx : x = (circleEquiv P p hp).symm (.inr c) := by
          rw [← hxz,Equiv.symm_apply_apply]
        exact hubs_independent P p hp v x
          (by rw [hv]; exact hub_inverse_isHub P p hp b)
          (by rw [hx]; exact hub_inverse_isHub P p hp c) hvw⟩
    letI := hempty
    simp

end D5.S3.Topology.WeavingReferenceDegree
