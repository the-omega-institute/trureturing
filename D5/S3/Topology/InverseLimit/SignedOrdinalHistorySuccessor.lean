/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistorySuccessor
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistorySuccessor
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: The actual next state consumes the same selected result and whole old births. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

/-! Successor advancement never constructs an unused ordinary result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalPredecessor

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a}

/-- Every current row uses the already selected Q, with B from its one birth. -/
noncomputable def currentPack (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha) (hB : ∀ r hr, Surjective (bornB r hr))
    (r : Rows a) : BirthPack (H.carrier (rowIndex r)) := by
  classical
  exact if hr : r = newRow a ha then (by subst r; exact newborn Q)
    else preparedOldPack Q bornB hB r hr

private theorem currentPack_U (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha) (hB : ∀ r hr, Surjective (bornB r hr)) (r : Rows a) :
    (currentPack Q bornB hB r).U = currentU (Q := Q) r := by
  classical
  unfold currentPack currentU
  split_ifs with hr
  · subst r; rfl
  · rfl

private theorem currentPack_V (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha) (hB : ∀ r hr, Surjective (bornB r hr)) (r : Rows a) :
    (currentPack Q bornB hB r).V = Q.V r := by
  classical
  by_cases hr : r = newRow a ha
  · subst r
    simp [currentPack, newborn]
  · simp [currentPack, hr, preparedOldPack]

private theorem pack_nu_heq {b : Ordinal.{0}} {C : Set (Cube b)}
    (W W' : BirthPack C) (he : W = W') : HEq W.nu W'.nu := by
  cases he
  rfl

private theorem currentPack_nu (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha) (hB : ∀ r hr, Surjective (bornB r hr)) (r : Rows a) :
    HEq (currentPack Q bornB hB r).nu (Q.nu r) := by
  classical
  by_cases hr : r = newRow a ha
  · subst r
    exact pack_nu_heq _ (newborn Q) (by simp [currentPack])
  · exact pack_nu_heq _ (preparedOldPack Q bornB hB r hr)
      (by simp only [currentPack, dite_eq_right hr])

private def initialOldB : OldClopens SignedOrdinalInitial.H0 initialStage.2 := by
  intro r hr
  exact (hr (Subtype.ext (le_antisymm r.2.2 r.2.1))).elim

/-- The actual initial state executes Q/R at omega; every old-row field is empty. -/
noncomputable def initialState (hCH : Cardinal.continuum.{0} = ℵ₁) : State initialStage where
  H := SignedOrdinalInitial.H0
  P := SignedOrdinalInitial.predecessor
  initial_carriers := fun _ _ => rfl
  incoming := .initial
  regular := by
    intro r hr
    exact (hr (Subtype.ext (le_antisymm r.2.2 r.2.1))).elim
  event := execute SignedOrdinalInitial.H0 initialStage.2 SignedOrdinalInitial.predecessor
    (scheduledLaunch SignedOrdinalInitial.H0 initialStage.2 SignedOrdinalInitial.predecessor)
    initialOldB hCH
  oldBonto := by
    intro r hr
    exact (hr (Subtype.ext (le_antisymm r.2.2 r.2.1))).elim

variable {b : Stage} (X : State b)

/-- The next old B is transported from its exact current whole pack. -/
noncomputable def nextOldPack (r : Rows (ord (nextStage b)))
    (hr : r ≠ newRow (ord (nextStage b)) (nextStage b).2) :
    BirthPack (X.event.result.coordinates.extended.carrier (rowIndex r)) :=
  BirthPack.cast (SignedOrdinalPredecessor.old_carrier X.event.result r hr).symm
    (currentPack X.event.Q X.event.oldB X.oldBonto
      (SignedOrdinalPredecessor.previousRow b.2 r hr))

noncomputable def nextOldB : OldClopens X.event.result.coordinates.extended (nextStage b).2 :=
  fun r hr => (nextOldPack X r hr).B

/-- Actual successor H/P and actual incoming regular F, followed by one new
preparation and one selected Result. No complete-history supplier occurs. -/
noncomputable def nextState (hCH : Cardinal.continuum.{0} = ℵ₁) : State (nextStage b) where
  H := X.event.result.coordinates.extended
  P := X.event.nextP
  initial_carriers := by
    intro c hc
    let c' : Coord (Order.succ (ord b)) := ⟨c.1, hc.trans_lt (b.2.trans_lt (Order.lt_succ _))⟩
    exact (X.event.result.coordinates.old_carrier c').trans (X.initial_carriers c' hc)
  incoming := .successor X.event
  regular := X.event.next_regular
  event := execute X.event.result.coordinates.extended (nextStage b).2 X.event.nextP
    (scheduledLaunch X.event.result.coordinates.extended (nextStage b).2 X.event.nextP)
    (nextOldB X) hCH
  oldBonto := fun r hr => (nextOldPack X r hr).Bonto

/-- The next current view retains the full current Q at every old row. -/
theorem next_old_readback (hCH : Cardinal.continuum.{0} = ℵ₁)
    (r : Rows (ord (nextStage b)))
    (hr : r ≠ newRow (ord (nextStage b)) (nextStage b).2) :
    (nextState X hCH).oldBirth r hr = nextOldPack X r hr := by
  apply (BirthPack.eq_cast (SignedOrdinalPredecessor.old_carrier X.event.result r hr).symm
    (currentPack X.event.Q X.event.oldB X.oldBonto (previousRow b.2 r hr))
    ((nextState X hCH).oldBirth r hr) ?_ ?_ ?_ ?_).symm
  · exact (heq_of_eq (currentPack_U _ _ _ _)).trans
      (next_U_readback X.event.result r hr).symm
  · exact (BirthPack.cast_B_heq
      (SignedOrdinalPredecessor.old_carrier X.event.result r hr).symm _).symm
  · exact (heq_of_eq (currentPack_V _ _ _ _)).trans
      (next_V_readback X.event.result r hr).symm
  · exact (currentPack_nu _ _ _ _).trans (next_nu_readback X.event.result r hr).symm

/-- Immediate successor coherence reads the same selected event and arrival. -/
theorem next_coherent (hCH : Cardinal.continuum.{0} = ℵ₁) :
    Coherent (show b < nextStage b from Order.lt_succ (ord b)) X (nextState X hCH) where
  carrier := X.event.result.coordinates.old_carrier
  birth := by
    rw [next_old_readback]
    classical
    simp [nextOldPack, previousRow, oldRow, newRow, currentPack, State.birth, newborn]
  arrival := by
    intro r d hr hm e
    change X.event.result.arrival _ r d hr hm e = _
    simp only [Result.arrival, dite_eq_right (lt_irrefl (ord b))]
  DI := by
    intro r hr
    exact Filter.Eventually.of_forall (fun _ hn => X.event.result.oldI r hr hn)
  DJ := by
    intro r hr d
    exact Filter.Eventually.of_forall (fun _ hn => X.event.result.oldJ r hr d hn)

set_option backward.isDefEq.respectTransparency false in
/-- Successor advancement preserves compatibility with every earlier state
of this exact past, rather than only its immediate predecessor. -/
theorem next_coherent_earlier {c : Stage} (h : c < b) (Y : State c)
    (hc : Coherent h Y X) (hCH : Cardinal.continuum.{0} = ℵ₁) :
    Coherent (h.trans (show b < nextStage b from Order.lt_succ (ord b)))
      Y (nextState X hCH) where
  carrier := fun d => (X.event.result.coordinates.old_carrier
    ⟨d.1, d.2.trans_le (Order.succ_le_succ (show ord c ≤ ord b from h.le))⟩).trans
      (hc.carrier d)
  birth := by
    rw [next_old_readback]
    change BirthPack.cast _
      (currentPack X.event.Q X.event.oldB X.oldBonto
        (oldRow h (newRow (ord c) c.2))) = _
    classical
    rw [currentPack, dite_eq_right (oldRow_ne h _), prepared_old_readback]
    change BirthPack.cast _ (X.oldBirth _ _) = _
    rw [hc.birth]
    exact BirthPack.cast_cast _ _ _
  arrival := by
    intro r d hr hm e
    exact (X.event.result.arrival_retains ⟨ord c, h⟩ r d hr hm e).trans
      (hc.arrival r d hr hm e)
  DI := by
    intro r hr
    filter_upwards [hc.DI r hr] with n hn
    exact fun hmem => hn (X.event.result.oldI (oldRow h r) (oldRow_ne h r) hmem)
  DJ := by
    intro r hr d
    filter_upwards [hc.DJ r hr d] with n hn
    exact fun hmem => hn (X.event.result.oldJ (oldRow h r) (oldRow_ne h r)
      ⟨d.1, d.2.trans (show ord c < ord b from h)⟩ hmem)

end D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor
