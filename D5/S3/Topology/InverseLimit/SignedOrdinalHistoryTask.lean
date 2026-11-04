/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryTask
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryTask
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Intrinsic delayed semantics read only the canonical whole birth pack. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

/-! A natural task code addresses a pair of clopens of the original birth B. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth
open SignedOrdinalHistoryState

/-- This is the actual fixed codec, with its inverse supplied by mathlib. -/
def decode : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm

local instance carrierMeasurable {b : Ordinal.{0}} (C : Set (Cube b)) :
    MeasurableSpace C := borel C
local instance carrierBorel {b : Ordinal.{0}} (C : Set (Cube b)) :
    BorelSpace C := ⟨rfl⟩

/-- Intrinsic semantics use one whole birth and no history, J, F or final object. -/
def Intrinsic {b : Ordinal.{0}} {C : Set (Cube b)}
    (W : BirthPack C) (s t : Label) (k : ℕ) : Prop :=
  s ≠ t ∧ Disjoint ((W.B (decode k).1 : Clopens C) : Set C) (W.B (decode k).2) ∧
    ∃ y : ℕ → C,
      (∀ n, y n ∈ W.V.clopen n) ∧
      (∀ n, y n ∈ W.B (decode k).2) ∧
      (∀ n, W.measure t n = (Measure.dirac (y n)).toSignedMeasure) ∧
      ∀ n, (W.measure s n).totalVariation (W.B (decode k).1 : Set C)ᶜ = 0

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a} (Q : Prepared H ha P launch)

/-- On the original eligible domain, the executable DelayedTask predicate is
exactly the intrinsic whole-pack predicate. This equivalence supplies no F. -/
theorem local_semantics (bornB : OldClopens H ha)
    (hB : ∀ r hr, Surjective (bornB r hr))
    (r : Rows a) (hr : r ≠ newRow a ha) (s t : Coord a) (k : ℕ) :
    LocalDelayed Q bornB ⟨r.1, r.2.2.trans_lt P.proper⟩
      ⟨s.1, s.2.trans P.proper⟩ ⟨t.1, t.2.trans P.proper⟩ k ↔
    Intrinsic (preparedOldPack Q bornB hB r hr)
      ⟨s.1, s.2.trans P.proper⟩ ⟨t.1, t.2.trans P.proper⟩ k := by
  constructor
  · rintro ⟨_, D, hm⟩
    rcases D with ⟨row, hold, source, target, hne, A, B, hdis,
      y, hinV, hinB, hdirac, hnull⟩
    rcases hm with ⟨hrow, hs, ht, hA, hB'⟩
    have hrow' : row = r := Subtype.ext hrow
    have hs' : source = s := Subtype.ext hs
    have ht' : target = t := Subtype.ext ht
    subst row
    subst source
    subst target
    dsimp only at hA hB'
    change A = bornB r hr (Nat.unpair k).1 at hA
    change B = bornB r hr (Nat.unpair k).2 at hB'
    clear hrow hs ht
    rw [hA, hB'] at hdis
    rw [hB'] at hinB
    rw [hA] at hnull
    refine ⟨?_, hdis, y, hinV, hinB, hdirac, hnull⟩
    intro he
    exact hne (Subtype.ext (congrArg (fun z : Label => z.1) he))
  · rintro ⟨hne, hdis, y, hinV, hinB, hdirac, hnull⟩
    have hne' : s ≠ t := by
      intro he
      apply hne
      exact Subtype.ext (congrArg (fun z : Coord a => z.1) he)
    let D : DelayedTask Q := {
      row := r, old := hr, source := s, target := t, distinct := hne'
      sourceSupport := bornB r hr (decode k).1
      targetSupport := bornB r hr (decode k).2
      disjoint := hdis, y := y, inSupport := hinV, inTarget := hinB
      dirac := hdirac, sourceNull := hnull }
    have hrlt : r.1 < a := lt_of_le_of_ne r.2.2 (fun he => hr (Subtype.ext he))
    exact ⟨⟨r.2.1, hrlt, s.2, t.2⟩, D, rfl, rfl, rfl, rfl, rfl⟩

theorem intrinsic_cast {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (W : BirthPack C) (s t : Label) (k : ℕ) :
    Intrinsic (BirthPack.cast h W) s t k ↔ Intrinsic W s t k := by
  subst D
  rfl

/-- Stable semantics are derived from whole-birth coherence after the local
event has been selected. They were not a premise of that event's executor. -/
theorem stable_local {b c : Stage} (h : b < c) (X : State b) (Y : State c)
    (hc : Coherent h X Y) (s t : Label) (hs : s.1 < ord c) (ht : t.1 < ord c)
    (k : ℕ) :
    LocalDelayed Y.event.Q Y.event.oldB b.1 s t k ↔ Intrinsic X.birth s t k := by
  have he := local_semantics Y.event.Q Y.event.oldB Y.oldBonto
    (oldRow h (newRow (ord b) b.2)) (oldRow_ne h _) ⟨s.1, hs⟩ ⟨t.1, ht⟩ k
  rw [prepared_old_readback] at he
  change LocalDelayed Y.event.Q Y.event.oldB b.1 s t k ↔
    Intrinsic (Y.oldBirth (oldRow h (newRow (ord b) b.2)) (oldRow_ne h _)) s t k at he
  rw [hc.birth] at he
  exact he.trans (intrinsic_cast _ _ s t k)

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask
