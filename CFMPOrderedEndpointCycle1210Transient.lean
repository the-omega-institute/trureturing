import CFMPGenericOccurrence1163Transient
import CFMPGenericCycle1181Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate (sigma)
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate
open private outgoing_slot incoming_slot from CFMPGenericCycle1181Transient
open private face_ne_of_index from CFMPGenericOccurrence1163Transient
open private sigma_face from CFMPRawFaceCapSlice1053Transient
variable {T : Type*} [Fintype T]

-- Uncompiled temporary candidate on the same original pairing and ordered component.
def fiberNext (P : RawFacePairing T) (s : Orientation P) (i : Occurrence T) :
    Equiv.Perm (OccurrenceFiber P i) where
  toFun o := ⟨s.next o.val, (next_preserves_label P s o.val).trans o.property⟩
  invFun o := ⟨s.next.symm o.val, by
    have h := next_preserves_label P s (s.next.symm o.val)
    rw [s.next.apply_symm_apply] at h
    exact h.symm.trans o.property⟩
  left_inv o := Subtype.ext (s.next.symm_apply_apply o.val)
  right_inv o := Subtype.ext (s.next.apply_symm_apply o.val)

def next (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) : Equiv.Perm (Component P d0) :=
  (componentEquivOccurrenceFiber P d0 hNR).trans
    ((fiberNext P s (occ d0.val)).trans (componentEquivOccurrenceFiber P d0 hNR).symm)

theorem next_occ (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    occ (next P s d0 hNR d).val.val = s.next (occ d.val.val) := by
  let E := componentEquivOccurrenceFiber P d0 hNR
  change (E (E.symm (fiberNext P s (occ d0.val) (E d)))).val = _
  rw [E.apply_symm_apply]
  rfl

private theorem outgoing_ne_incoming (r : Occurrence T → Bool) (i : Occurrence T) :
    outgoingFace r i ≠ incomingFace r i := by
  have h (e : Fin 6) (b : Bool) :
      (if b then (edgeFaces e).1 else (edgeFaces e).2) ≠
        (if b then (edgeFaces e).2 else (edgeFaces e).1) := by
    cases b <;> fin_cases e <;> decide
  exact h i.2 (r i)

theorem port_guards (r : Occurrence T → Bool) (d : OrderedEnd T) :
    (outgoingFace r (occ d.val) ≠ d.val.1.2 ∧
      outgoingFace r (occ d.val) ≠ d.val.2) ∧
    (incomingFace r (occ d.val) ≠ d.val.1.2 ∧
      incomingFace r (occ d.val) ≠ d.val.2) ∧
    outgoingFace r (occ d.val) ≠ incomingFace r (occ d.val) := by
  exact ⟨face_ne_of_index _ _ _ _ d.property (outgoing_slot r (occ d.val)).symm,
    face_ne_of_index _ _ _ _ d.property (incoming_slot r (occ d.val)).symm,
    outgoing_ne_incoming r (occ d.val)⟩

theorem outgoing_pair_ports (P : RawFacePairing T) (s : Orientation P)
    (i : Occurrence T) :
    P.facePair (i.1,outgoingFace s.reversed i) =
      ((s.next i).1,incomingFace s.reversed (s.next i)) ∧
    P.faceMap (i.1,outgoingFace s.reversed i) (outgoingSlot s.reversed i) =
      incomingSlot s.reversed (s.next i) := by
  have h := port_next_or_prev P s (i.1,outgoingFace s.reversed i)
    (outgoingSlot s.reversed i)
  have hi : (i.1,faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i)) = i :=
    Prod.ext rfl (outgoing_slot s.reversed i)
  dsimp only at h
  rw [hi] at h
  rcases h with ⟨_,hj,hpair,hslot⟩ | ⟨hin,_,_,_⟩
  · rw [hj] at hpair hslot
    exact ⟨hpair,hslot⟩
  · exact False.elim (outgoing_ne_incoming s.reversed i hin.1)

/-- F1 keeps the outgoing face and slot; F4 identifies its lift with the conjugate. -/
theorem next_actual_dartMove (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    (next P s d0 hNR d).val.val =
      dartMove P (outgoingFace s.reversed (occ d.val.val)) d.val.val := by
  let i := occ d.val.val
  have hi : occ d.val.val =
      (i.1,faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i)) :=
    Prod.ext rfl (outgoing_slot s.reversed i).symm
  obtain ⟨e,hfj,hfk,he,ho⟩ := edge_step_lift_port P
    (i.1,outgoingFace s.reversed i) (outgoingSlot s.reversed i) d.val hi
  let eC : Component P d0 := ⟨e,d.property.trans _ _ _
    (Relation.EqvGen.rel _ _ ⟨outgoingFace s.reversed i,hfj,hfk,he⟩)⟩
  have ho' : occ e.val = s.next i := by
    change occ e.val = rawNext P.facePair P.faceMap s.reversed i
    exact ho
  have hc : eC = next P s d0 hNR d := by
    apply componentMap_injective P d0 hNR
    apply Subtype.ext
    exact ho'.trans (next_occ P s d0 hNR d).symm
  exact (congrArg (fun a : Component P d0 => a.val.val) hc).symm.trans he

theorem next_original_port (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    DartStep P d.val.val (next P s d0 hNR d).val.val :=
  ⟨outgoingFace s.reversed (occ d.val.val),
    (port_guards s.reversed d.val).1.1,(port_guards s.reversed d.val).1.2,
    next_actual_dartMove P s d0 hNR d⟩

/-- The target face and slot are the original paired target, including loops. -/
theorem next_target_ports (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    P.facePair (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val)) =
      ((next P s d0 hNR d).val.val.1.1,
        incomingFace s.reversed (occ (next P s d0 hNR d).val.val)) ∧
    P.faceMap (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))
      (outgoingSlot s.reversed (occ d.val.val)) =
        incomingSlot s.reversed (occ (next P s d0 hNR d).val.val) := by
  have h := outgoing_pair_ports P s (occ d.val.val)
  rw [← next_occ P s d0 hNR d] at h
  exact h

private theorem port_exhaust (r : Occurrence T → Bool) (d : OrderedEnd T) (l : Fin 4) :
    l = d.val.1.2 ∨ l = d.val.2 ∨
      l = incomingFace r (occ d.val) ∨ l = outgoingFace r (occ d.val) := by
  have h (j k l : Fin 4) (hjk : j ≠ k) (b : Bool) :
      l = j ∨ l = k ∨
        l = (if b then (edgeFaces (edgeIndex j k)).2 else (edgeFaces (edgeIndex j k)).1) ∨
        l = (if b then (edgeFaces (edgeIndex j k)).1 else (edgeFaces (edgeIndex j k)).2) := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;> cases b <;>
      simp_all [edgeIndex,edgeFaces]
  exact h d.val.1.2 d.val.2 l d.property (r (occ d.val))

/-- All four actual barycentric positions have the required transport. -/
theorem next_sigma_positions (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    let e := next P s d0 hNR d
    let q := sigma P (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))
    q d.val.val.1.2 = e.val.val.1.2 ∧ q d.val.val.2 = e.val.val.2 ∧
    q (outgoingFace s.reversed (occ d.val.val)) =
      incomingFace s.reversed (occ e.val.val) ∧
    q (incomingFace s.reversed (occ d.val.val)) =
      outgoingFace s.reversed (occ e.val.val) := by
  let e := next P s d0 hNR d
  let q := sigma P (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))
  have hm := next_actual_dartMove P s d0 hNR d
  have hj : q d.val.val.1.2 = e.val.val.1.2 :=
    (congrArg (fun a : Dart T => a.1.2) hm).symm
  have hk : q d.val.val.2 = e.val.val.2 :=
    (congrArg (fun a : Dart T => a.2) hm).symm
  have ho : q (outgoingFace s.reversed (occ d.val.val)) =
      incomingFace s.reversed (occ e.val.val) := by
    exact (sigma_face P _).trans (congrArg Prod.snd (next_target_ports P s d0 hNR d).1)
  refine ⟨hj,hk,ho,?_⟩
  rcases port_exhaust s.reversed e.val
    (q (incomingFace s.reversed (occ d.val.val))) with h | h | h | h
  · exact False.elim ((port_guards s.reversed d.val).2.1.1
      (q.injective (h.trans hj.symm)))
  · exact False.elim ((port_guards s.reversed d.val).2.1.2
      (q.injective (h.trans hk.symm)))
  · exact False.elim ((port_guards s.reversed d.val).2.2
      (q.injective (h.trans ho.symm)).symm)
  · exact h

theorem incoming_reverse_actual (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    dartMove P (incomingFace s.reversed (occ (next P s d0 hNR d).val.val))
      (next P s d0 hNR d).val.val = d.val.val := by
  have ht := congrArg Prod.snd (next_target_ports P s d0 hNR d).1
  change (P.facePair (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))).2 =
    incomingFace s.reversed (occ (next P s d0 hNR d).val.val) at ht
  have hm := next_actual_dartMove P s d0 hNR d
  calc
    dartMove P (incomingFace s.reversed (occ (next P s d0 hNR d).val.val))
        (next P s d0 hNR d).val.val =
      dartMove P (P.facePair
        (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))).2
        (next P s d0 hNR d).val.val :=
      congrArg (fun f : Fin 4 => dartMove P f (next P s d0 hNR d).val.val) ht.symm
    _ = dartMove P (P.facePair
        (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))).2
        (dartMove P (outgoingFace s.reversed (occ d.val.val)) d.val.val) :=
      congrArg (dartMove P (P.facePair
        (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))).2) hm
    _ = d.val.val := dart_move_reverse P d.val.val _

abbrev sectorCount (P : RawFacePairing T) (d0 : OrderedEnd T) : ℕ :=
  (fiberFinset P (occ d0.val)).card

theorem sectorCount_pos (P : RawFacePairing T) (d0 : OrderedEnd T) :
    0 < sectorCount P d0 :=
  Finset.card_pos.mpr ⟨occ d0.val,base_mem_fiberFinset P (occ d0.val)⟩

def base (P : RawFacePairing T) (d0 : OrderedEnd T) : Component P d0 :=
  ⟨d0,Relation.EqvGen.refl _⟩

def enumeration (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) : Fin (sectorCount P d0) ≃ Component P d0 :=
  (powerEnumeration P s (occ d0.val)).trans (componentEquivOccurrenceFiber P d0 hNR).symm

theorem enumeration_occ (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (n : Fin (sectorCount P d0)) :
    occ (enumeration P s d0 hNR n).val.val = (s.next ^ n.val) (occ d0.val) := by
  let E := componentEquivOccurrenceFiber P d0 hNR
  let o : OccurrenceFiber P (occ d0.val) :=
    ⟨(powerEnumeration P s (occ d0.val) n).val,
      (powerEnumeration P s (occ d0.val) n).property⟩
  have hE : E (E.symm o) = o := E.apply_symm_apply o
  have hv : (E (E.symm o)).val = o.val :=
    congrArg (fun z : OccurrenceFiber P (occ d0.val) => z.val) hE
  exact hv.trans (powerEnumeration_apply P s (occ d0.val) n)

def nextIndex (P : RawFacePairing T) (d0 : OrderedEnd T)
    (n : Fin (sectorCount P d0)) : Fin (sectorCount P d0) :=
  ⟨(n.val+1) % sectorCount P d0,Nat.mod_lt _ (sectorCount_pos P d0)⟩

theorem enumeration_next (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (n : Fin (sectorCount P d0)) :
    next P s d0 hNR (enumeration P s d0 hNR n) =
      enumeration P s d0 hNR (nextIndex P d0 n) := by
  apply componentMap_injective P d0 hNR
  apply Subtype.ext
  change occ (next P s d0 hNR (enumeration P s d0 hNR n)).val.val =
    occ (enumeration P s d0 hNR (nextIndex P d0 n)).val.val
  have hC := powerEnumeration_next P s (occ d0.val) n
  change s.next ((s.next ^ n.val) (occ d0.val)) =
    (s.next ^ (nextIndex P d0 n).val) (occ d0.val) at hC
  exact (next_occ P s d0 hNR _).trans
    ((congrArg s.next (enumeration_occ P s d0 hNR n)).trans
      (hC.trans (enumeration_occ P s d0 hNR (nextIndex P d0 n)).symm))

theorem enumeration_next_actual (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (n : Fin (sectorCount P d0)) :
    (enumeration P s d0 hNR (nextIndex P d0 n)).val.val =
      dartMove P (outgoingFace s.reversed (occ (enumeration P s d0 hNR n).val.val))
        (enumeration P s d0 hNR n).val.val := by
  rw [← enumeration_next P s d0 hNR n]
  exact next_actual_dartMove P s d0 hNR _

theorem next_pow_occ (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (n : ℕ) (d : Component P d0) :
    occ ((next P s d0 hNR ^ n) d).val.val = (s.next ^ n) (occ d.val.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,next_occ,ih,pow_succ',Equiv.Perm.mul_apply]

theorem enumeration_actual_powers (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (n : Fin (sectorCount P d0)) :
    enumeration P s d0 hNR n = (next P s d0 hNR ^ n.val) (base P d0) := by
  apply componentMap_injective P d0 hNR
  apply Subtype.ext
  change occ (enumeration P s d0 hNR n).val.val =
    occ ((next P s d0 hNR ^ n.val) (base P d0)).val.val
  exact (enumeration_occ P s d0 hNR n).trans
    (next_pow_occ P s d0 hNR n.val (base P d0)).symm

theorem actual_period_iff (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (n : ℕ) :
    (next P s d0 hNR ^ n) (base P d0) = base P d0 ↔ sectorCount P d0 ∣ n := by
  have he : (next P s d0 hNR ^ n) (base P d0) = base P d0 ↔
      (s.next ^ n) (occ d0.val) = occ d0.val := by
    constructor
    · intro h
      have hh := congrArg (fun a : Component P d0 => occ a.val.val) h
      exact (next_pow_occ P s d0 hNR n (base P d0)).symm.trans hh
    · intro h
      apply componentMap_injective P d0 hNR
      apply Subtype.ext
      change occ ((next P s d0 hNR ^ n) (base P d0)).val.val =
        occ (base P d0).val.val
      exact (next_pow_occ P s d0 hNR n (base P d0)).trans h
  exact he.trans (period_iff_card_dvd P s (occ d0.val) n)

theorem actual_wrap (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    (next P s d0 hNR ^ sectorCount P d0) (base P d0) = base P d0 :=
  (actual_period_iff P s d0 hNR _).mpr (dvd_refl _)

theorem singleton_actual_fixed (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (hm : sectorCount P d0 = 1) :
    next P s d0 hNR (base P d0) = base P d0 := by
  have h := actual_wrap P s d0 hNR
  simpa [hm] using h

theorem two_actual_returns (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) (hm : sectorCount P d0 = 2) :
    next P s d0 hNR (next P s d0 hNR (base P d0)) = base P d0 ∧
      next P s d0 hNR (base P d0) ≠ base P d0 := by
  constructor
  · have h := actual_wrap P s d0 hNR
    simpa [hm,pow_succ,Equiv.Perm.mul_apply] using h
  · intro h
    have hd : sectorCount P d0 ∣ 1 := (actual_period_iff P s d0 hNR 1).mp (by simpa using h)
    norm_num [hm] at hd
end D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_occ,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.port_guards,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.outgoing_pair_ports,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_actual_dartMove,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_original_port,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_target_ports,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_sigma_positions,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.incoming_reverse_actual,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.sectorCount_pos,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.enumeration,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.enumeration_occ,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.enumeration_next,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.enumeration_next_actual,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next_pow_occ,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.enumeration_actual_powers,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.actual_period_iff,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.actual_wrap,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.singleton_actual_fixed,
      ``D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.two_actual_returns] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1210 ordered endpoint target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1210 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1210 CHECKED {name} axioms={axioms}"
