import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.List.Nodup

/-! A first-discovery ordering of a connected finite graph. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourDiscovery

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def fresh (x : V) (seen : List V) : Finset V :=
  G.neighborFinset x \ seen.toFinset

private def step (seen : List V) (position : Nat) : List V :=
  match seen[position]? with
  | none => seen
  | some vertex => seen ++ (fresh G vertex seen).toList

private def seenAfter (start : V) : Nat → List V
  | 0 => [start]
  | position + 1 => step G (seenAfter start position) position

private theorem seen_mono (seen : List V) (position : Nat) :
    seen ⊆ step G seen position := by
  unfold step
  split
  · exact fun _ h => h
  · exact fun _ hv => List.mem_append_left _ hv

private theorem no_repeat (seen : List V) (hseen : seen.Nodup) (position : Nat) :
    (step G seen position).Nodup := by
  unfold step
  split
  · exact hseen
  · rename_i vertex _
    refine hseen.append (Finset.nodup_toList _) ?_
    intro w hs hw
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hw)).2 (List.mem_toFinset.mpr hs)

private theorem seenAfter_nodup (start : V) (position : Nat) :
    (seenAfter G start position).Nodup := by
  induction position with
  | zero => simp [seenAfter]
  | succ position ih => exact no_repeat G _ ih position

private theorem start_seen (start : V) (position : Nat) :
    start ∈ seenAfter G start position := by
  induction position with
  | zero => simp [seenAfter]
  | succ position ih => exact seen_mono G _ position ih

private def ClosedThrough (seen : List V) (position : Nat) : Prop :=
  ∀ x ∈ seen.take position, ∀ y, G.Adj x y → y ∈ seen

private theorem step_closed {seen : List V} {position : Nat}
    (hclosed : ClosedThrough G seen position) :
    ClosedThrough G (step G seen position) (position + 1) := by
  unfold step
  split
  · rename_i hnone
    have hlen : seen.length ≤ position := List.getElem?_eq_none_iff.mp hnone
    intro x hx y hxy
    rw [List.take_of_length_le (by omega : seen.length ≤ position + 1)] at hx
    apply hclosed x _ y hxy
    rwa [List.take_of_length_le hlen]
  · rename_i vertex hsome
    have hlt : position < seen.length := List.getElem?_eq_some_iff.mp hsome |>.choose
    have hx : seen[position] = vertex := by
      exact (List.getElem?_eq_some_iff.mp hsome).choose_spec
    intro x hx' y hxy
    rw [List.take_append_of_le_length (by omega : position + 1 ≤ seen.length),
      List.take_succ_eq_append_getElem hlt, hx] at hx'
    rcases List.mem_append.mp hx' with hold | hnew
    · exact List.mem_append_left _ (hclosed x hold y hxy)
    · have h : x = vertex := by simpa using hnew
      subst x
      by_cases hm : y ∈ seen
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ (Finset.mem_toList.mpr
          (Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy,
            fun h => hm (List.mem_toFinset.mp h)⟩))

private theorem seenAfter_closed (start : V) (position : Nat) :
    ClosedThrough G (seenAfter G start position) position := by
  induction position with
  | zero => simp [ClosedThrough]
  | succ position ih => exact step_closed G ih

private theorem walk_closed {seen : List V}
    (hclosed : ClosedThrough G seen seen.length) {a b : V}
    (ha : a ∈ seen) (w : G.Walk a b) : b ∈ seen := by
  induction w with
  | nil => exact ha
  | cons edge rest ih =>
    apply ih
    exact hclosed _ (by simpa using ha) _ edge

/-- A breadth-first traversal of a connected finite graph always has a vertex
to process until all vertices have been processed. -/
private theorem still_available (h : G.Connected) (start : V) {position : Nat}
    (hposition : position < Fintype.card V) :
    position < (seenAfter G start position).length := by
  let seen := seenAfter G start position
  by_contra! hlen
  change seen.length ≤ position at hlen
  have hclosed : ClosedThrough G seen seen.length := by
    have hc : ClosedThrough G seen position := seenAfter_closed G start position
    intro x hx y hxy
    apply hc x _ y hxy
    rw [List.take_of_length_le hlen]
    exact List.mem_of_mem_take hx
  have hall (v : V) : v ∈ seen := by
    obtain ⟨w⟩ := h.preconnected start v
    exact walk_closed G hclosed (start_seen G start position) w
  have he : seen.toFinset = (univ : Finset V) := by
    ext v
    simp [hall]
  have hn := List.toFinset_card_of_nodup (seenAfter_nodup G start position)
  change seen.toFinset.card = seen.length at hn
  rw [he, Finset.card_univ] at hn
  omega

private theorem seen_prefix (start : V) {i j : Nat} (hij : i ≤ j) :
    seenAfter G start i <+: seenAfter G start j := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact ⟨[], by simp⟩
  | succ j ih =>
    by_cases h : i ≤ j
    · apply (ih h).trans
      change seenAfter G start j <+: step G (seenAfter G start j) j
      unfold step
      split
      · exact ⟨[], by simp⟩
      · exact List.prefix_append _ _
    · obtain rfl : i = j + 1 := by omega
      exact ⟨[], by simp⟩

private theorem seenAfter_card (h : G.Connected) (start : V) :
    (seenAfter G start (Fintype.card V)).length = Fintype.card V := by
  let seen := seenAfter G start (Fintype.card V)
  have hn := List.toFinset_card_of_nodup (seenAfter_nodup G start (Fintype.card V))
  change seen.toFinset.card = seen.length at hn
  have hle : seen.length ≤ Fintype.card V := hn.symm.trans_le (Finset.card_le_univ _)
  have hc : ClosedThrough G seen (Fintype.card V) := seenAfter_closed G start (Fintype.card V)
  have hclosed : ClosedThrough G seen seen.length := by
    intro x hx y hxy
    apply hc x _ y hxy
    rw [List.take_of_length_le hle]
    exact List.mem_of_mem_take hx
  have hm (v : V) : v ∈ seen := by
    obtain ⟨w⟩ := h.preconnected start v
    exact walk_closed G hclosed (start_seen G start (Fintype.card V)) w
  have he : seen.toFinset = univ := by
    ext v
    simp [hm]
  change seen.length = _
  rw [← hn, he, card_univ]

/-- The breadth-first discovery order gives a labeling by consecutive integers. -/
private def discoveryLabels (h : G.Connected) (start : V) : Fin (Fintype.card V) ≃ V := by
  let order := seenAfter G start (Fintype.card V)
  have hlen : order.length = Fintype.card V := seenAfter_card G h start
  let f (i : Fin (Fintype.card V)) : V := order[i.val]'(by rw [hlen]; exact i.isLt)
  have hnin : order.Nodup := seenAfter_nodup G start _
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hnin.eq_of_getElem_eq _ _ hij
  have huniv : order.toFinset = (univ : Finset V) := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ, List.toFinset_card_of_nodup hnin, hlen]
  refine Equiv.ofBijective f ⟨hf, fun v => ?_⟩
  have hv : v ∈ order := List.mem_toFinset.mp (huniv.symm ▸ mem_univ v)
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hv
  exact ⟨⟨i, hlen ▸ hi⟩, hget⟩

private theorem label_mem_seen (h : G.Connected) (start : V)
    {position : Nat} (hpos : position ≤ Fintype.card V) (i : Fin (Fintype.card V)) :
    discoveryLabels G h start i ∈ seenAfter G start position ↔
      i.val < (seenAfter G start position).length := by
  let seen := seenAfter G start position
  let final := seenAfter G start (Fintype.card V)
  have hp : seen <+: final := seen_prefix G start hpos
  have hn : final.Nodup := seenAfter_nodup G start _
  have hi : i.val < final.length :=
    (seenAfter_card G h start).symm ▸ i.isLt
  change final[i.val]'hi ∈ seen ↔ i.val < seen.length
  constructor
  · intro hm
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
    have he' : final[j]'(hj.trans_le hp.length_le) = final[i.val]'hi :=
      (hp.getElem hj).symm.trans he
    exact (hn.eq_of_getElem_eq _ _ he') ▸ hj
  · intro hm
    rw [← hp.getElem hm]
    exact List.getElem_mem hm

/-- At each step, the undiscovered neighbors receive consecutive labels
immediately after all vertices discovered so far. -/
private theorem new_neighbors_contiguous (h : G.Connected) (start : V)
    (i j : Fin (Fintype.card V)) (hj : (seenAfter G start i.val).length ≤ j.val) :
    G.Adj (discoveryLabels G h start i) (discoveryLabels G h start j) ↔
      j.val < (seenAfter G start (i.val + 1)).length := by
  let seen := seenAfter G start i.val
  let final := seenAfter G start (Fintype.card V)
  let u := discoveryLabels G h start i
  let v := discoveryLabels G h start j
  have hi : i.val < seen.length := still_available G h start i.isLt
  have hi' : i.val < final.length := (seenAfter_card G h start).symm ▸ i.isLt
  have hp : seen <+: final := seen_prefix G start i.isLt.le
  have hu : seen[i.val] = u := hp.getElem hi
  have ht : seenAfter G start (i.val + 1) = seen ++ (fresh G u seen).toList := by
    change step G seen i.val = _
    rw [step, List.getElem?_eq_getElem hi, hu]
  have hv : v ∉ seen := fun hm =>
    Nat.not_lt_of_ge hj ((label_mem_seen G h start i.isLt.le j).mp hm)
  rw [← label_mem_seen G h start i.isLt, ht]
  change G.Adj u v ↔ v ∈ seen ++ (fresh G u seen).toList
  simp [fresh, hv, SimpleGraph.mem_neighborFinset]

#print axioms new_neighbors_contiguous

#print axioms discoveryLabels
#print axioms still_available

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourDiscovery
