/- GID: D5/S3/Topology/InverseLimit/SignedSuccessorCoordinates
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedSuccessorCoordinates
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Literal Boolean successor insertion and all-stage closed-cover Prefix extension. -/

import D5.S3.Topology.InverseLimit.SignedProperLimit
import D5.S3.Topology.Measures.SignedSplitSuccessorSupport
import Mathlib.Topology.Homeomorph.Lemmas

/-! A closed product split becomes an actual successor-coordinate carrier.
All earlier stages, including stage zero, retain their literal restrictions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Topology Ordinal

namespace D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates

open SignedProperLimit
open D5.S3.Topology.Measures.SignedSplitSuccessor (splitCarrier)

def last (a : Ordinal.{0}) : Coord (Order.succ a) := ⟨a, Order.lt_succ a⟩

/-- Removing the last ordinal coordinate leaves exactly the old indices. -/
private def oldIndices (a : Ordinal.{0}) :
    {i : Coord (Order.succ a) // i ≠ last a} ≃ Coord a where
  toFun i := ⟨i.1.1, lt_of_le_of_ne (Order.le_of_lt_succ i.1.2)
    (fun h => i.2 (Subtype.ext h))⟩
  invFun i := ⟨⟨i.1, lt_trans i.2 (Order.lt_succ a)⟩,
    fun h => (ne_of_lt i.2) (congrArg Subtype.val h)⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

/-- Mathlib's function splitting, with the ordinal complement reindexed. -/
private noncomputable def cubeSplit (a : Ordinal.{0}) :
    Cube (Order.succ a) ≃ₜ Cube a × Bool := by
  classical
  exact (Homeomorph.funSplitAt Bool (last a)).trans
    (((Homeomorph.refl Bool).prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : Coord a => Bool) (oldIndices a))).trans
        (Homeomorph.prodComm Bool (Cube a)))

private theorem cubeSplit_read (a : Ordinal.{0}) (u : Cube (Order.succ a)) :
    cubeSplit a u = (restrict (Order.le_succ a) u, u (last a)) := rfl

variable {a : Ordinal.{0}} (H : Prefix (Order.succ a))
  (Y Z : Set (H.Space (last a)))

/-- The output includes equations in the original, unchanged coordinate types. -/
structure Result where
  carrier : Set (Cube (Order.succ a))
  closed : IsClosed carrier
  nonempty : carrier.Nonempty
  equiv : splitCarrier Y Z ≃ₜ carrier
  range_eq : carrier = Set.range (fun x : splitCarrier Y Z => (equiv x).1)
  insert : ∀ (x : splitCarrier Y Z) (i : Coord (Order.succ a)),
    (equiv x).1 i = if hi : i.1 < a then x.1.1.1 ⟨i.1, hi⟩ else x.1.2
  old_coord : ∀ (x : splitCarrier Y Z) (i : Coord a),
    (equiv x).1 ⟨i.1, lt_trans i.2 (Order.lt_succ a)⟩ = x.1.1.1 i
  sheet_coord : ∀ x : splitCarrier Y Z, (equiv x).1 (last a) = x.1.2
  restrict_equiv : ∀ x : splitCarrier Y Z,
    restrict (Order.le_succ a) (equiv x).1 = x.1.1.1
  inverse_old : ∀ z : carrier,
    (equiv.symm z).1.1.1 = restrict (Order.le_succ a) z.1
  inverse_sheet : ∀ z : carrier, (equiv.symm z).1.2 = z.1 (last a)
  extended : Prefix (Order.succ (Order.succ a))
  old_carrier : ∀ b : Coord (Order.succ a),
    extended.carrier ⟨b.1, lt_trans b.2 (Order.lt_succ (Order.succ a))⟩ = H.carrier b
  top_carrier : extended.carrier (last (Order.succ a)) = carrier
  restrict_inverse : ∀ (b : Ordinal.{0}) (h : b ≤ a) (z : carrier),
    restrict (h.trans (Order.le_succ a)) z.1 = restrict h (equiv.symm z).1.1.1

private def enlargedCarrier (C : Set (Cube (Order.succ a)))
    (b : Coord (Order.succ (Order.succ a))) : Set (Cube b.1) :=
  if h : b.1 < Order.succ a then H.carrier ⟨b.1, h⟩
  else (by
    have he : b.1 = Order.succ a :=
      le_antisymm (Order.le_of_lt_succ b.2) (le_of_not_gt h)
    exact he.symm ▸ C)

/-- Every closed cover gives the literal inserted carrier and a complete enlarged
Prefix. No countability, properness, separated sides, or nonempty-side condition
is imposed. The dependent old/new cases use the cover's actual first projection. -/
theorem exists_successor_coordinates (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = univ) : Nonempty (Result H Y Z) := by
  classical
  let K := H.Space (last a)
  let X := splitCarrier Y Z
  have hX : IsClosed (splitCarrier Y Z) :=
    ((hY.preimage continuous_fst).inter (isClosed_singleton.preimage continuous_snd)).union
      ((hZ.preimage continuous_fst).inter (isClosed_singleton.preimage continuous_snd))
  let : CompactSpace X := hX.isClosedEmbedding_subtypeVal.compactSpace
  have honto : Function.Surjective (fun x : X => x.1.1) := by
    intro k
    have hk : k ∈ Y ∪ Z := by rw [hcover]; exact mem_univ k
    rcases hk with hk | hk
    · exact ⟨⟨(k, false), Or.inl ⟨hk, rfl⟩⟩, rfl⟩
    · exact ⟨⟨(k, true), Or.inr ⟨hk, rfl⟩⟩, rfl⟩
  let append : X → Cube (Order.succ a) :=
    fun x => (cubeSplit a).symm (x.1.1.1, x.1.2)
  have hread (x : X) :
      (restrict (Order.le_succ a) (append x), append x (last a)) =
        (x.1.1.1, x.1.2) := by
    rw [← cubeSplit_read]
    exact (cubeSplit a).apply_symm_apply _
  have hrestrict (x : X) : restrict (Order.le_succ a) (append x) = x.1.1.1 :=
    congrArg Prod.fst (hread x)
  have hsheet (x : X) : append x (last a) = x.1.2 := congrArg Prod.snd (hread x)
  have hc : Continuous append := (cubeSplit a).symm.continuous.comp
    ((continuous_subtype_val.fst.subtype_val).prodMk continuous_subtype_val.snd)
  have hi : Function.Injective append := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (hrestrict x).symm.trans ((congrArg (restrict (Order.le_succ a)) hxy).trans
        (hrestrict y))
    · exact (hsheet x).symm.trans ((congrArg (fun u => u (last a)) hxy).trans (hsheet y))
  let C := Set.range append
  have hC : IsClosed C := (hc.isClosedEmbedding hi).isClosed_range
  have hnC : C.Nonempty := by
    obtain ⟨x, _⟩ := honto (Classical.choice (inferInstance : Nonempty K))
    exact ⟨append x, x, rfl⟩
  let e : X ≃ₜ C := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorph
  have he (x : X) : (e x).1 = append x := rfl
  have hback (z : C) : append (e.symm z) = z.1 := by
    exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
  have hlower (b : Ordinal.{0}) (h : b ≤ a) (x : X) :
      restrict (h.trans (Order.le_succ a)) (append x) = restrict h x.1.1.1 := by
    exact congrArg (restrict h) (hrestrict x)
  have hinverse (b : Ordinal.{0}) (h : b ≤ a) (z : C) :
      restrict (h.trans (Order.le_succ a)) z.1 = restrict h (e.symm z).1.1.1 := by
    rw [← hback z]
    exact hlower b h (e.symm z)
  let carrier := enlargedCarrier H C
  have hold (b : Ordinal.{0}) (hb : b < Order.succ a)
      (hb' : b < Order.succ (Order.succ a)) :
      carrier ⟨b, hb'⟩ = H.carrier ⟨b, hb⟩ := by
    dsimp only [carrier, enlargedCarrier]
    rw [dite_eq_left hb]
  have htop (hb : Order.succ a < Order.succ (Order.succ a)) :
      carrier ⟨Order.succ a, hb⟩ = C := by
    dsimp only [carrier, enlargedCarrier]
    rw [dite_eq_right (lt_irrefl (Order.succ a))]
  let HP : Prefix (Order.succ (Order.succ a)) :=
    { carrier := carrier
      closed := by
        intro ⟨b, hb⟩
        by_cases h : b < Order.succ a
        · rw [hold b h hb]
          exact H.closed ⟨b, h⟩
        · have heq : b = Order.succ a :=
            le_antisymm (Order.le_of_lt_succ hb) (le_of_not_gt h)
          subst b
          rw [htop hb]
          exact hC
      nonempty := by
        intro ⟨b, hb⟩
        by_cases h : b < Order.succ a
        · rw [hold b h hb]
          exact H.nonempty ⟨b, h⟩
        · have heq : b = Order.succ a :=
            le_antisymm (Order.le_of_lt_succ hb) (le_of_not_gt h)
          subst b
          rw [htop hb]
          exact hnC
      compatible := by
        intro ⟨b, hb⟩ ⟨c, hc⟩ h x
        change b ≤ c at h
        by_cases hcold : c < Order.succ a
        · have hbold : b < Order.succ a := lt_of_le_of_lt h hcold
          have hx : x.1 ∈ H.carrier ⟨c, hcold⟩ := by
            simpa only [hold c hcold hc] using x.2
          simpa only [hold b hbold hb] using
            H.compatible ⟨b, hbold⟩ ⟨c, hcold⟩ h ⟨x.1, hx⟩
        · have heq : c = Order.succ a :=
            le_antisymm (Order.le_of_lt_succ hc) (le_of_not_gt hcold)
          subst c
          have hx : x.1 ∈ C := by simpa only [htop hc] using x.2
          by_cases hbold : b < Order.succ a
          · have hba : b ≤ a := Order.le_of_lt_succ hbold
            rw [hold b hbold hb]
            rw [hinverse b hba ⟨x.1, hx⟩]
            exact H.compatible ⟨b, hbold⟩ (last a) hba (e.symm ⟨x.1, hx⟩).1.1
          · have heq : b = Order.succ a := le_antisymm h (le_of_not_gt hbold)
            subst b
            exact x.2
      onto := by
        intro ⟨b, hb⟩ ⟨c, hc⟩ h y
        change b ≤ c at h
        by_cases hcold : c < Order.succ a
        · have hbold : b < Order.succ a := lt_of_le_of_lt h hcold
          have hy : y.1 ∈ H.carrier ⟨b, hbold⟩ := by
            simpa only [hold b hbold hb] using y.2
          obtain ⟨x, hx⟩ := H.onto ⟨b, hbold⟩ ⟨c, hcold⟩ h ⟨y.1, hy⟩
          refine ⟨⟨x.1, ?_⟩, hx⟩
          simpa only [hold c hcold hc] using x.2
        · have heq : c = Order.succ a :=
            le_antisymm (Order.le_of_lt_succ hc) (le_of_not_gt hcold)
          subst c
          by_cases hbold : b < Order.succ a
          · have hba : b ≤ a := Order.le_of_lt_succ hbold
            have hy : y.1 ∈ H.carrier ⟨b, hbold⟩ := by
              simpa only [hold b hbold hb] using y.2
            obtain ⟨k, hk⟩ := H.onto ⟨b, hbold⟩ (last a) hba ⟨y.1, hy⟩
            obtain ⟨x, hx⟩ := honto k
            refine ⟨⟨append x, ?_⟩, ?_⟩
            · simpa only [htop hc] using (show append x ∈ C from ⟨x, rfl⟩)
            · exact (hlower b hba x).trans ((congrArg (fun k : K => restrict hba k.1) hx).trans hk)
          · have heq : b = Order.succ a := le_antisymm h (le_of_not_gt hbold)
            subst b
            exact ⟨y, rfl⟩ }
  refine ⟨{
    carrier := C
    closed := hC
    nonempty := hnC
    equiv := e
    range_eq := ?_
    insert := ?_
    old_coord := ?_
    sheet_coord := hsheet
    restrict_equiv := hrestrict
    inverse_old := ?_
    inverse_sheet := ?_
    extended := HP
    old_carrier := fun b => hold b.1 b.2 _
    top_carrier := htop _
    restrict_inverse := hinverse }⟩
  · exact Set.ext fun u => ⟨fun hu => by
      obtain ⟨x, rfl⟩ := hu
      exact ⟨x, rfl⟩, fun hu => by
      obtain ⟨x, rfl⟩ := hu
      exact ⟨x, rfl⟩⟩
  · intro x i
    rw [he x]
    split_ifs with h
    · exact congrFun (hrestrict x) ⟨i.1, h⟩
    · have ht : i = last a := Subtype.ext
        (le_antisymm (Order.le_of_lt_succ i.2) (le_of_not_gt h))
      rw [ht]
      exact hsheet x
  · intro x i
    exact congrFun (hrestrict x) i
  · intro z
    exact (hrestrict (e.symm z)).symm.trans (congrArg (restrict (Order.le_succ a)) (hback z))
  · intro z
    exact (hsheet (e.symm z)).symm.trans (congrArg (fun u => u (last a)) (hback z))

end D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates
