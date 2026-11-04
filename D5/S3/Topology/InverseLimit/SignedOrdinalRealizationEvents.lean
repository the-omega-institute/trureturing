/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Same selected ordinary and delayed events on the literal final realization. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalRawHistory

/-! Selected Results retain their quantitative clopen and delayed certificate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalHistorySuccessor SignedOrdinalHistoryTask SignedOrdinalRealization
open D5.S3.Topology.Measures

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

private theorem oldN_congr {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} (P : Predecessor H ha) {r r' : Rows a}
    {hr : r ≠ newRow a ha} {hr' : r' ≠ newRow a ha} {d d' : Coord a}
    (hrow : r = r') (hcol : d = d') (e : Fin 2) :
    P.oldN r hr d e = P.oldN r' hr' d' e := by
  subst r'
  subst d'
  rfl

/-- The actual split projection and the final restriction read the same coordinates. -/
theorem selected_projection (a : Stage) (r : Rows (ord a))
    (x : (finalPrefix hCH).LimitSpace) :
    (SignedOrdinalHistory.run hCH a).event.result.literalProjection r
      (successorHomeomorph hCH a ((finalPrefix hCH).projection (nextStage a).1 x)) =
    Homeomorph.setCongr (carrier_read hCH a (rowIndex r))
      ((finalPrefix hCH).projection
        ⟨r.1, r.2.2.trans_lt a.1.2⟩ x) := by
  apply Subtype.ext
  exact ((SignedOrdinalHistory.run hCH a).event.result.coordinates.restrict_inverse
    r.1 r.2.2 _).symm

/-- Actual successor incoming J is the same outgoing R.J, including new rows. -/
theorem successor_J (a θ : Stage) (hθ : ord θ ≤ ord a) (d : Label)
    (hd : d.1 ≤ ord a) :
    historicalJ hCH θ d
      ⟨(nextStage a).1, (max_le hθ hd).trans_lt (Order.lt_succ _)⟩ =
    (SignedOrdinalHistory.run hCH a).event.result.J
      ⟨ord θ, θ.2, hθ⟩ ⟨d.1, hd⟩ := by
  let hθs : θ < nextStage a := hθ.trans_lt (Order.lt_succ (ord a))
  change (SignedOrdinalHistory.run hCH (nextStage a)).P.J
    (oldRow hθs (newRow (ord θ) θ.2)) (oldRow_ne hθs _)
    ⟨d.1, hd.trans_lt (Order.lt_succ (ord a))⟩ = _
  rw [SignedOrdinalHistory.successor_execution]
  rfl

/-- Every old prepared whole measure is the original birth measure on the
final literal carrier, with its label and every natural index preserved. -/
theorem prepared_measure_read (θ a : Stage) (hθ : θ < a) (d : Label)
    (hd : d.1 ≤ ord a) (n : ℕ) :
    HEq ((SignedOrdinalHistory.run hCH a).event.Q.measure
      (oldRow hθ (newRow (ord θ) θ.2)) ⟨d.1, hd⟩ n)
      ((wholeBirth hCH θ).measure d n) := by
  let r := oldRow hθ (newRow (ord θ) θ.2)
  let hr := oldRow_ne hθ (newRow (ord θ) θ.2)
  have hp : HEq (preparedOldPack (SignedOrdinalHistory.run hCH a).event.Q
      (SignedOrdinalHistory.run hCH a).event.oldB
      (SignedOrdinalHistory.run hCH a).oldBonto r hr)
      (SignedOrdinalHistory.run hCH θ).birth :=
    (heq_of_eq (prepared_old_readback _ _ _ r hr)).trans
      ((heq_of_eq (SignedOrdinalHistory.coherent hCH θ a hθ).birth).trans
        (BirthPack.cast_heq _ _))
  have hm := BirthPack.heq_measure
    ((SignedOrdinalHistory.coherent hCH θ a hθ).carrier (top (ord θ)))
    _ _ hp d n
  exact hm.trans (whole_measure hCH θ d n).symm

/-- Actual ordinary cofinal treatments carry the identical literal carrier,
original whole measure and their unaltered quantitative G interface. -/
theorem ordinary_cofinal (θ : Stage) (d base : Label) :
    let f := SignedOrdinalHistory.run hCH
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ d.1 < ord a ∧
      ∃ (t : Treatment (ord a))
        (R : Result (f a).H a.2 (f a).P
          (scheduledLaunch (f a).H a.2 (f a).P) (f a).event.Q t),
        (f a).event.selected = .ordinary t R ∧
        t.row.1 = ord θ ∧ t.label.1 = d.1 ∧
        (finalPrefix hCH).carrier (nextStage a).1 = R.coordinates.carrier ∧
        ∀ n, HEq ((f a).event.Q.measure t.row t.label n)
          ((wholeBirth hCH θ).measure d n) := by
  obtain ⟨a, hb, hθ, hd, _, t, R, hs, hr, hl, hm⟩ :=
    SignedOrdinalHistory.ordinary_cofinal hCH θ d base
  refine ⟨a, hb, hθ, hd, t, R, hs, hr, hl, ?_, ?_⟩
  · have hc := successor_carrier hCH a
    change (finalPrefix hCH).carrier (nextStage a).1 =
      (Selected.result (SignedOrdinalHistory.run hCH a).event.selected).coordinates.carrier at hc
    rw [hs] at hc
    exact hc
  · intro n
    exact (hm n).trans (whole_measure hCH θ d n).symm

/-- The same literal delayed execution keeps its original B-pair support,
its same certificate, permanent source reservoirs and successor source J. -/
theorem delayed_cofinal (θ : Stage) (s t base : Label) (k : ℕ)
    (valid : Intrinsic (wholeBirth hCH θ) s t k) :
    let f := SignedOrdinalHistory.run hCH
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ s.1 < ord a ∧ t.1 < ord a ∧
      ∃ (D : DelayedTask (f a).event.Q)
        (R : Result (f a).H a.2 (f a).P
          (scheduledLaunch (f a).H a.2 (f a).P) (f a).event.Q ⟨D.row, oldCol D.target⟩)
        (certificate : DelayedCertificate (f a).event.Q D R),
        (f a).event.selected = .delayed D R certificate ∧
        Matches (f a).event.Q (f a).event.oldB θ.1 s t k D ∧
        HEq D.sourceSupport ((wholeBirth hCH θ).B (decode k).1) ∧
        HEq D.targetSupport ((wholeBirth hCH θ).B (decode k).2) ∧
        (finalPrefix hCH).carrier (nextStage a).1 = R.coordinates.carrier ∧
        (∀ n, HEq ((f a).event.Q.measure D.row (oldCol D.source) n)
          ((wholeBirth hCH θ).measure s n)) ∧
        (∀ n, HEq ((f a).event.Q.measure D.row (oldCol D.target) n)
          ((wholeBirth hCH θ).measure t n)) ∧
        (∀ e : Fin 2, R.N D.row (oldCol D.source) e =
          reservoir hCH θ s (decide (e = 1))) ∧
        ∃ helig : max θ.1 s < (nextStage a).1,
          R.J D.row (oldCol D.source) = historicalJ hCH θ s
            ⟨(nextStage a).1, helig⟩ := by
  obtain ⟨a, hb, hθ, hs, ht, _, D, R, cert, hsel, hmatch, hS, hT⟩ :=
    SignedOrdinalHistory.delayed_cofinal hCH θ s t base k
      ((intrinsic_cast (top_read hCH θ).symm _ s t k).mp valid)
  refine ⟨a, hb, hθ, hs, ht, D, R, cert, hsel, hmatch, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hS.trans (SignedOrdinalHistory.cast_B_eval (top_read hCH θ).symm
      (SignedOrdinalHistory.run hCH θ).birth (decode k).1).symm
  · exact hT.trans (SignedOrdinalHistory.cast_B_eval (top_read hCH θ).symm
      (SignedOrdinalHistory.run hCH θ).birth (decode k).2).symm
  · have hc := successor_carrier hCH a
    change (finalPrefix hCH).carrier (nextStage a).1 =
      (Selected.result (SignedOrdinalHistory.run hCH a).event.selected).coordinates.carrier at hc
    rw [hsel] at hc
    exact hc
  · intro n
    have hrow : D.row = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext hmatch.1
    have hsource : oldCol D.source = ⟨s.1, hs.le⟩ := Subtype.ext hmatch.2.1
    rw [hrow, hsource]
    exact prepared_measure_read hCH θ a hθ s hs.le n
  · intro n
    have hrow : D.row = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext hmatch.1
    have htarget : oldCol D.target = ⟨t.1, ht.le⟩ := Subtype.ext hmatch.2.2.1
    rw [hrow, htarget]
    exact prepared_measure_read hCH θ a hθ t ht.le n
  · intro e
    have hrow : D.row = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext hmatch.1
    have hsource : D.source = ⟨s.1, hs⟩ := Subtype.ext hmatch.2.1
    have hr := R.oldN D.row D.old D.source e
    refine hr.trans ((oldN_congr (SignedOrdinalHistory.run hCH a).P
      (hr' := oldRow_ne hθ _) hrow hsource e).trans ?_)
    have hn := reservoir_incoming hCH θ s a hθ hs (decide (e = 1))
    fin_cases e <;> simpa using hn.symm
  · refine ⟨(max_le (show ord θ ≤ ord a from hθ.le) hs.le).trans_lt
      (Order.lt_succ (ord a)), ?_⟩
    have hrow : D.row = ⟨ord θ, θ.2, hθ.le⟩ := Subtype.ext hmatch.1
    have hsource : oldCol D.source = ⟨s.1, hs.le⟩ := Subtype.ext hmatch.2.1
    have hj := successor_J hCH a θ hθ.le s hs.le
    change historicalJ hCH θ s _ =
      (Selected.result (SignedOrdinalHistory.run hCH a).event.selected).J _ _ at hj
    rw [hsel] at hj
    have he := congrArg₂ (fun r d => R.J r d) hrow hsource
    exact he.trans hj.symm

end D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents
