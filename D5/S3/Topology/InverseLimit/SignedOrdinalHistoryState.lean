/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryState
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryState
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual incoming and outgoing events with exact strict-past coherence. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth

/-! A state retains incoming stage evidence and the whole outgoing Q/R. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth

abbrev Stage := {a : Label // (ω : Ordinal.{0}) ≤ a.1}
abbrev ord (a : Stage) : Ordinal.{0} := a.1.1

def initialStage : Stage := ⟨⟨ω, Ordinal.omega0_lt_omega_one⟩, le_rfl⟩
def nextStage (a : Stage) : Stage :=
  ⟨⟨Order.succ (ord a), (Cardinal.isSuccLimit_omega 1).succ_lt a.1.2⟩,
    a.2.trans (Order.le_succ _)⟩

def oldRow {b a : Stage} (h : b < a) (r : Rows (ord b)) : Rows (ord a) :=
  ⟨r.1, r.2.1, r.2.2.trans h.le⟩

theorem oldRow_ne {b a : Stage} (h : b < a) (r : Rows (ord b)) :
    oldRow h r ≠ newRow (ord a) a.2 := by
  intro he
  have hv := congrArg Subtype.val he
  exact (ne_of_lt (r.2.2.trans_lt h)) hv

/-- Incoming evidence is retained separately from the outgoing birth event.
A limit record keeps the actual Ext, including its regular bounded F and DI/DJ. -/
inductive Incoming : (a : Ordinal.{0}) → (ha : ω ≤ a) →
    (H : Prefix (Order.succ a)) → Predecessor H ha → Type 2
  | initial : Incoming ω le_rfl SignedOrdinalInitial.H0 SignedOrdinalInitial.predecessor
  | successor {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
      {P : Predecessor H ha} {launch : Launch a} (E : Event H ha P launch) :
      Incoming (Order.succ a) (ha.trans (Order.le_succ a))
        E.result.coordinates.extended E.nextP
  | limit {a : Ordinal.{0}} (ha : ω ≤ a) (hl : Order.IsSuccLimit a)
      (L : Prefix a) (D : L.Data) (laws : L.Laws D) (Ext : L.Extension D)
      (H : Prefix (Order.succ a)) (P : Predecessor H ha)
      (top_read : H.carrier (top a) = L.limitCarrier)
      (old_read : ∀ r : Coord a,
        H.carrier ⟨r.1, r.2.trans (Order.lt_succ a)⟩ = L.carrier r)
      (I_read : ∀ (r : Rows a) (hr : r ≠ newRow a ha),
        P.I r hr = Ext.I ⟨r.1, lt_of_le_of_ne r.2.2
          (fun he => hr (Subtype.ext he))⟩)
      (J_read : ∀ (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a),
        P.J r hr d = Ext.J ⟨r.1, lt_of_le_of_ne r.2.2
          (fun he => hr (Subtype.ext he))⟩ d) : Incoming a ha H P

/-- This is a state type, not an existence premise. The actual recursion must
construct H, P, incoming evidence and its own single selected outgoing event. -/
structure State (a : Stage) where
  H : Prefix (Order.succ (ord a))
  P : Predecessor H a.2
  initial_carriers : ∀ (c : Coord (Order.succ (ord a))), c.1 ≤ ω → H.carrier c = univ
  incoming : Incoming (ord a) a.2 H P
  regular : RegularCurrent H a.2 P
  event : Event H a.2 P (scheduledLaunch H a.2 P)
  oldBonto : ∀ r hr, Surjective (event.oldB r hr)

namespace State

variable {a : Stage} (X : State a)

noncomputable abbrev birth : BirthPack (X.H.carrier (top (ord a))) := newborn X.event.Q

noncomputable abbrev oldBirth (r : Rows (ord a)) (hr : r ≠ newRow (ord a) a.2) :=
  predecessorPack (P := X.P) X.event.oldB X.oldBonto r hr

end State

/-- Every clause compares this same run's two actual states. In particular,
old whole births are read from the earlier canonical Q, and N from the one R
at its unique outgoing max(row,label), whose arrival is the next stage. -/
structure Coherent {b a : Stage} (h : b < a) (X : State b) (Y : State a) : Prop where
  carrier : ∀ c : Coord (Order.succ (ord b)),
    Y.H.carrier ⟨c.1, c.2.trans_le (Order.succ_le_succ (show ord b ≤ ord a from h.le))⟩ =
      X.H.carrier c
  birth : Y.oldBirth (oldRow h (newRow (ord b) b.2)) (oldRow_ne h _) =
    BirthPack.cast (carrier (top (ord b))).symm X.birth
  arrival : ∀ (r d : Ordinal.{0}) (hr : ω ≤ r) (hm : max r d = ord b) (e : Fin 2),
    Y.P.births ⟨ord b, h⟩ r d hr hm e =
      X.event.result.N ⟨r, hr, (le_max_left r d).trans hm.le⟩
        ⟨d, (le_max_right r d).trans hm.le⟩ e
  DI : ∀ (r : Rows (ord b)) (hr : r ≠ newRow (ord b) b.2),
    AlmostSubset (Y.P.I (oldRow h r) (oldRow_ne h r)) (X.P.I r hr)
  DJ : ∀ (r : Rows (ord b)) (hr : r ≠ newRow (ord b) b.2) (d : Coord (ord b)),
    AlmostSubset (Y.P.J (oldRow h r) (oldRow_ne h r)
      ⟨d.1, d.2.trans (show ord b < ord a from h)⟩) (X.P.J r hr d)

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState
