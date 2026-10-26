/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryEvent
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryEvent
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual same-preparation execution with canonical whole-birth clopen tests. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalDelayed
import D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor
import D5.S3.Topology.InverseLimit.SignedOrdinalInitial
import D5.S3.Topology.InverseLimit.CofinalTaskSchedule

/-! One actual selected event keeps its whole preparation and birth tests. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open D5.S3.Topology.Measures

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a}

/-- Each old row reads the clopen enumeration archived at its own birth. -/
abbrev OldClopens (H : Prefix (Order.succ a)) (ha : ω ≤ a) :=
  ∀ r : Rows a, r ≠ newRow a ha → ℕ → Clopens (Base H r)

/-- The source, target and support-test code are read before task projection.
The two clopens use the original row's B, rather than the current stage's B. -/
def Matches (Q : Prepared H ha P launch) (bornB : OldClopens H ha)
    (θ s t : Label) (k : ℕ) (D : DelayedTask Q) : Prop :=
  D.row.1 = θ.1 ∧ D.source.1 = s.1 ∧ D.target.1 = t.1 ∧
    D.sourceSupport = bornB D.row D.old (Nat.unpair k).1 ∧
    D.targetSupport = bornB D.row D.old (Nat.unpair k).2

/-- A local semantic test has no access to an unborn row or label. Its only
measure data are the same prepared Q and its oldNu readbacks. -/
def LocalDelayed (Q : Prepared H ha P launch) (bornB : OldClopens H ha)
    (θ s t : Label) (k : ℕ) : Prop :=
  CofinalTaskSchedule.DelayedValid ⟨a, P.proper⟩ θ s t ∧
    ∃ D : DelayedTask Q, Matches Q bornB θ s t k D

/-- Exactly one actual Result is stored, together with its delayed certificate
when that branch was selected. An ordinary witness is not constructed first. -/
inductive Selected (Q : Prepared H ha P launch) : Type 1
  | ordinary (t : Treatment a) (R : Result H ha P launch Q t)
  | delayed (D : DelayedTask Q)
      (R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩)
      (certificate : DelayedCertificate Q D R)

namespace Selected

variable {Q : Prepared H ha P launch}

def treatment : Selected Q → Treatment a
  | .ordinary t _ => t
  | .delayed D _ _ => ⟨D.row, oldCol D.target⟩

def result (S : Selected Q) : Result H ha P launch Q S.treatment :=
  match S with
  | .ordinary _ R => R
  | .delayed _ R _ => R

end Selected

private noncomputable def ordinaryTarget (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha) : Treatment a := by
  let rd := CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q bornB)
  have hv := CofinalTaskSchedule.execute_valid ⟨a, P.proper⟩ ha (LocalDelayed Q bornB)
  exact ⟨⟨rd.1.1, hv.1, hv.2.1⟩, ⟨rd.2.1, hv.2.2⟩⟩

private noncomputable def select (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha)
    (ordinary : ∀ t : Treatment a, Nonempty (Result H ha P launch Q t))
    (delayed : ∀ D : DelayedTask Q,
      ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R) :
    Selected Q := by
  classical
  exact match (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 with
  | .inl _ => .ordinary (ordinaryTarget Q bornB)
      (Classical.choice (ordinary (ordinaryTarget Q bornB)))
  | .inr (θ, s, t, k) =>
      if h : LocalDelayed Q bornB θ s t k then
        let D := Classical.choose h.2
        let R := Classical.choose (delayed D)
        .delayed D R (Classical.choose_spec (delayed D))
      else .ordinary (ordinaryTarget Q bornB)
        (Classical.choice (ordinary (ordinaryTarget Q bornB)))

private theorem select_target (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha)
    (ordinary : ∀ t : Treatment a, Nonempty (Result H ha P launch Q t))
    (delayed : ∀ D : DelayedTask Q,
      ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R) :
    ((select Q bornB ordinary delayed).treatment.row.1,
      (select Q bornB ordinary delayed).treatment.label.1) =
      ((CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q bornB)).1.1,
        (CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q bornB)).2.1) := by
  classical
  cases he : (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 with
  | inl rd =>
    simp only [select, he]
    rfl
  | inr task =>
    rcases task with ⟨θ, s, t, k⟩
    by_cases h : LocalDelayed Q bornB θ s t k
    · simp only [select, he, dite_eq_left h, Selected.treatment]
      have hm := Classical.choose_spec h.2
      have hex : CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q bornB) = (θ, t) := by
        simp [CofinalTaskSchedule.execute, he, h.1, h]
      rw [hex]
      exact Prod.ext hm.1 hm.2.2.1
    · simp only [select, he, dite_eq_right h]
      rfl

private theorem select_delayed (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha)
    (ordinary : ∀ t : Treatment a, Nonempty (Result H ha P launch Q t))
    (delayed : ∀ D : DelayedTask Q,
      ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R)
    (θ s t : Label) (k : ℕ)
    (he : (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 = .inr (θ, s, t, k))
    (h : LocalDelayed Q bornB θ s t k) :
    ∃ (D : DelayedTask Q) (R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩)
      (hc : DelayedCertificate Q D R),
      select Q bornB ordinary delayed = .delayed D R hc ∧ Matches Q bornB θ s t k D := by
  classical
  refine ⟨Classical.choose h.2, Classical.choose (delayed (Classical.choose h.2)),
    Classical.choose_spec (delayed (Classical.choose h.2)), ?_, Classical.choose_spec h.2⟩
  simp only [select, he, dite_eq_left h]

private theorem select_ordinary (Q : Prepared H ha P launch)
    (bornB : OldClopens H ha)
    (ordinary : ∀ t : Treatment a, Nonempty (Result H ha P launch Q t))
    (delayed : ∀ D : DelayedTask Q,
      ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R)
    (r d : Label)
    (he : (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 = .inl (r, d)) :
    ∃ (t : Treatment a) (R : Result H ha P launch Q t),
      select Q bornB ordinary delayed = .ordinary t R := by
  classical
  refine ⟨ordinaryTarget Q bornB, Classical.choice (ordinary (ordinaryTarget Q bornB)), ?_⟩
  simp only [select, he]

/-- Q contains U, B, V and nu on every Label. The selected event retains the
original literal F/E and oldI/oldJ proofs; arrival is used only for N. -/
structure Event (H : Prefix (Order.succ a)) (ha : ω ≤ a)
    (P : Predecessor H ha) (launch : Launch a) where
  oldB : OldClopens H ha
  Q : Prepared H ha P launch
  selected : Selected Q
  target : (selected.treatment.row.1, selected.treatment.label.1) =
    ((CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q oldB)).1.1,
      (CofinalTaskSchedule.execute ⟨a, P.proper⟩ (LocalDelayed Q oldB)).2.1)
  ordinary_run : ∀ (r d : Label),
    (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 = .inl (r, d) →
    ∃ (t : Treatment a) (R : Result H ha P launch Q t), selected = .ordinary t R
  delayed_run : ∀ (θ s t : Label) (k : ℕ),
    (CofinalTaskSchedule.reservation ⟨a, P.proper⟩).1 = .inr (θ, s, t, k) →
    LocalDelayed Q oldB θ s t k →
    ∃ (D : DelayedTask Q) (R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩)
      (hc : DelayedCertificate Q D R), selected = .delayed D R hc ∧ Matches Q oldB θ s t k D

/-- Regular bounded proper-stage F. This is deliberately stronger than the
field Predecessor.F and is discharged from the actual incoming event. -/
def RegularCurrent (H : Prefix (Order.succ a)) (ha : ω ≤ a)
    (P : Predecessor H ha) : Prop :=
  ∀ (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a)
    (s : ℕ → RegularSigned (K H)),
    (∀ n, (s n).1.map (projection H r) =
      (((P.nu r hr ⟨d.1, d.2.trans P.proper⟩).1 n).1)) →
    (∀ n, (s n).1.totalVariation univ = 1) →
    ∃ mu : RegularSigned (K H), mu.1.totalVariation.real univ ≤ 1 ∧ Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
      (along (P.J r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu.1).toWeakDual)

namespace Event

variable (E : Event H ha P launch)

abbrev result := E.selected.result

/-- This is the actual next predecessor, with the same selected Result. -/
noncomputable def nextP :
    Predecessor E.result.coordinates.extended (ha.trans (Order.le_succ a)) :=
  SignedOrdinalPredecessor.nextP E.result

/-- The regular bound is read from this event's literal_f, retaining both
Jordan regularity proofs. No missing information is inferred from nextP.F. -/
theorem next_regular : RegularCurrent E.result.coordinates.extended
    (ha.trans (Order.le_succ a)) E.nextP := by
  intro r hr d s hm hn
  obtain ⟨mu, hb, hp, hneg, hc⟩ :=
    SignedOrdinalPredecessor.next_regular_f E.result r hr d (fun n => (s n).1) hm hn
  exact ⟨⟨mu, hp, hneg⟩, hb, hc⟩

end Event

noncomputable def execute (H : Prefix (Order.succ a)) (ha : ω ≤ a)
    (P : Predecessor H ha) (launch : Launch a) (bornB : OldClopens H ha)
    (hCH : Cardinal.continuum.{0} = ℵ₁) : Event H ha P launch := by
  classical
  let prep := exists_prepared_step H ha P launch hCH
  let Q := Classical.choose prep
  exact ⟨bornB, Q,
    select Q bornB (Classical.choose_spec prep).1 (Classical.choose_spec prep).2,
    select_target Q bornB (Classical.choose_spec prep).1 (Classical.choose_spec prep).2,
    select_ordinary Q bornB (Classical.choose_spec prep).1 (Classical.choose_spec prep).2,
    select_delayed Q bornB (Classical.choose_spec prep).1 (Classical.choose_spec prep).2⟩

/-- Launch uses a fixed syntactic schedule, before Q and delayed semantics.
Every ordinary reservation also launches its support index on the same row. -/
noncomputable def scheduledLaunch (H : Prefix (Order.succ a)) (ha : ω ≤ a)
    (P : Predecessor H ha) : Launch a := by
  let rd := CofinalTaskSchedule.execute ⟨a, P.proper⟩ (fun _ _ _ _ => False)
  have hv := CofinalTaskSchedule.execute_valid ⟨a, P.proper⟩ ha (fun _ _ _ _ => False)
  exact ⟨⟨rd.1.1, hv.1, hv.2.1⟩, rd.2⟩

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent
