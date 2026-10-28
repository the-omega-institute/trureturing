/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalInitial
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalInitial
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual full Boolean cubes and the empty-history omega predecessor. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

/-! The initial finite and omega stages are the entire literal Boolean cubes.
No old row or past birth exists before the first successor at omega. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function
open scoped Ordinal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalInitial

open SignedProperLimit SignedOrdinalSuccessor

/-- Fill omitted coordinates with false; restriction recovers every input. -/
private theorem restrict_onto {b a : Ordinal.{0}} (h : b ≤ a) :
    Surjective (restrict h) := by
  classical
  intro y
  refine ⟨fun i => if hi : i.1 < b then y ⟨i.1, hi⟩ else false, ?_⟩
  funext i
  change (if hi : i.1 < b then y ⟨i.1, hi⟩ else false) = y i
  split
  · rfl
  · next hi => exact (hi i.2).elim

/-- The actual finite/omega initial segment, with literal onto restrictions. -/
def H0 : Prefix (Order.succ (ω : Ordinal.{0})) where
  carrier := fun _ => univ
  closed := fun _ => isClosed_univ
  nonempty := fun _ => ⟨fun _ => false, mem_univ _⟩
  compatible := fun _ _ _ _ => mem_univ _
  onto := by
    intro a b h y
    obtain ⟨x, hx⟩ := restrict_onto h y.1
    exact ⟨⟨x, mem_univ _⟩, hx⟩

private theorem no_old_row (r : Rows (ω : Ordinal.{0}))
    (hr : r ≠ newRow ω le_rfl) : False :=
  hr (Subtype.ext (le_antisymm r.2.2 r.2.1))

private theorem no_past_birth (b : Coord (ω : Ordinal.{0}))
    (r d : Ordinal.{0}) (hr : ω ≤ r) (hm : max r d = b.1) : False := by
  have hb : ω ≤ b.1 := hm ▸ hr.trans (le_max_left r d)
  exact (not_le_of_gt b.2) hb

/-- The first predecessor has no historical entries or old-row obligations.
Its current carrier maps onto Cube(omega) by reflexive coordinate restriction. -/
def predecessor : Predecessor H0 (le_refl (ω : Ordinal.{0})) where
  proper := Ordinal.omega0_lt_omega_one
  base_onto := by
    intro y
    refine ⟨⟨y, mem_univ _⟩, ?_⟩
    funext i
    rfl
  births := fun b r d hr hm => (no_past_birth b r d hr hm).elim
  U := fun r hr => (no_old_row r hr).elim
  Uonto := fun r hr => (no_old_row r hr).elim
  V := fun r hr => (no_old_row r hr).elim
  nu := fun r hr => (no_old_row r hr).elim
  nuonto := fun r hr => (no_old_row r hr).elim
  I := fun r hr => (no_old_row r hr).elim
  J := fun r hr => (no_old_row r hr).elim
  A := fun r hr => (no_old_row r hr).elim
  B := fun r hr => (no_old_row r hr).elim
  C := fun r hr => (no_old_row r hr).elim
  E := fun r hr => (no_old_row r hr).elim
  F := fun r hr => (no_old_row r hr).elim

end D5.S3.Topology.InverseLimit.SignedOrdinalInitial
