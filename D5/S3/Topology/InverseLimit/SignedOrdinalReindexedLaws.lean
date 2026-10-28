/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual proper-slice signed laws at decoded whole-birth measure labels. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalRealization
import D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth

/-! The same proper carriers and V/I retain every signed A–F law after decoding.
No final Data, endpoint, or alternative history is assumed or constructed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws

open SignedProperLimit SignedBirthEnumeration SignedOrdinalHistoryState
open SignedOrdinalReindexedBirth

variable (hCH : Cardinal.continuum.{0} = ℵ₁)
variable {l : Ordinal.{0}} (hl : l < ω₁)

/-- Decode the actual whole birth on born rows; retain labels on finite rows. -/
noncomputable def oldIndex (r : Coord l) (δ : Label) : Label := by
  classical
  exact if hr : ω ≤ r.1 then
    (measureIndex (SignedOrdinalRealization.wholeBirth hCH
      ⟨⟨r.1, r.2.trans hl⟩, hr⟩) δ).1 else δ

private theorem oldIndex_le (r : Coord l) (δ : Label) :
    oldIndex hCH hl r δ ≤ δ := by
  classical
  unfold oldIndex
  split_ifs with hr
  · exact (measureIndex (SignedOrdinalRealization.wholeBirth hCH
      ⟨⟨r.1, r.2.trans hl⟩, hr⟩) δ).2
  · exact le_rfl

/-- The decoded target stays in this exact slice, including its last row. -/
noncomputable def oldCoord (r d : Coord l) : Coord l :=
  ⟨(oldIndex hCH hl r ⟨d.1, d.2.trans hl⟩).1,
    (show (oldIndex hCH hl r ⟨d.1, d.2.trans hl⟩).1 ≤ d.1 from
      oldIndex_le hCH hl r ⟨d.1, d.2.trans hl⟩).trans_lt d.2⟩

private theorem oldCoord_le (r d : Coord l) : oldCoord hCH hl r d ≤ d :=
  oldIndex_le hCH hl r ⟨d.1, d.2.trans hl⟩

/-- Only nu/J/N change their label read; carriers, I and V are literal originals. -/
noncomputable def properData : (SignedOrdinalRealization.properSlice hCH hl).Data where
  proper := hl
  I := (SignedOrdinalRealization.properData hCH hl).I
  J r d a := (SignedOrdinalRealization.properData hCH hl).J r (oldCoord hCH hl r d) a
  N r d e := (SignedOrdinalRealization.properData hCH hl).N r (oldCoord hCH hl r d) e
  V := (SignedOrdinalRealization.properData hCH hl).V
  Vclopen := (SignedOrdinalRealization.properData hCH hl).Vclopen
  nu r δ := (SignedOrdinalRealization.properData hCH hl).nu r (oldIndex hCH hl r δ)
  mass r δ n hr := (SignedOrdinalRealization.properData hCH hl).mass
    r (oldIndex hCH hl r δ) n hr

private theorem oldClass_iff (r d a : Coord l) (h : r ≤ a) (n : ℕ)
    (s : RegularSigned ((SignedOrdinalRealization.properSlice hCH hl).Space a)) :
    (SignedOrdinalRealization.properSlice hCH hl).OldClass
      (properData hCH hl) r d a h n s ↔
    (SignedOrdinalRealization.properSlice hCH hl).OldClass
      (SignedOrdinalRealization.properData hCH hl) r (oldCoord hCH hl r d) a h n s := by
  rfl

/-- Every original proper-stage law, with its full every-selection signed F. -/
theorem properLaws :
    (SignedOrdinalRealization.properSlice hCH hl).Laws (properData hCH hl) := by
  let L := SignedOrdinalRealization.properLaws hCH hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r d a hr hra hda
    exact L.A r (oldCoord hCH hl r d) a hr hra
      ((oldCoord_le hCH hl r d).trans_lt hda)
  · intro r d hr
    exact L.B r (oldCoord hCH hl r d) hr
  · intro r d a e hr hra hda
    exact L.C r (oldCoord hCH hl r d) a e hr hra
      ((oldCoord_le hCH hl r d).trans_lt hda)
  · exact L.DI
  · intro r d a b hr hra hda hab
    exact L.DJ r (oldCoord hCH hl r d) a b hr hra
      ((oldCoord_le hCH hl r d).trans_lt hda) hab
  · exact L.E
  · intro r d a hra hr hda s hs
    exact L.F r (oldCoord hCH hl r d) a hra hr
      ((oldCoord_le hCH hl r d).trans_lt hda) s
      (fun n => (oldClass_iff hCH hl r d a hra.le n (s n)).mp (hs n))

/-- Every natural entry reads the identical measure of the actual whole birth.
The new label need not lie below the slice cutoff or a later carrier. -/
theorem nu_read (r : Coord l) (hr : ω ≤ r.1) (δ : Label) (n : ℕ) :
    ((properData hCH hl).nu r δ n).1 =
      (SignedOrdinalRealization.wholeBirth hCH ⟨⟨r.1, r.2.trans hl⟩, hr⟩).measure
        (measureIndex (SignedOrdinalRealization.wholeBirth hCH
          ⟨⟨r.1, r.2.trans hl⟩, hr⟩) δ).1 n := by
  classical
  change ((SignedOrdinalRealization.properData hCH hl).nu r
    (oldIndex hCH hl r δ) n).1 = _
  rw [SignedOrdinalRealization.slice_nu hCH hl r hr]
  simp only [oldIndex, dite_eq_left hr]
  rfl

/-- Any delayed support in the generic reindexing gives this same nu read. -/
theorem nu_reindexBirth (r : Coord l) (hr : ω ≤ r.1) (δ : Label) (n : ℕ)
    (delayedSupport : SupportFamily
      ((SignedOrdinalRealization.finalPrefix hCH).carrier ⟨r.1, r.2.trans hl⟩)) :
    ((properData hCH hl).nu r δ n).1 =
      (((reindexBirth (SignedOrdinalRealization.wholeBirth hCH
        ⟨⟨r.1, r.2.trans hl⟩, hr⟩) delayedSupport).nu δ).1 n).1 := by
  exact nu_read hCH hl r hr δ n

end D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws
