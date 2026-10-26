/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalLimit
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalLimit
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Literal proper-limit predecessor with original births and retained extension. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

/-! The proper limit is an actual next predecessor. No birth occurs at the limit;
the retained extension also supplies the regular bounded F and DI/DJ certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalLimit

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open D5.S3.Topology.Measures

abbrev BornRows (l : Ordinal.{0}) := {r : Coord l // ω ≤ r.1}

/-- Only already born whole packs and actual historical sets are inputs.
The base invariant is read at the genuine earlier stage omega. -/
structure Archive {l : Ordinal.{0}} (H : Prefix l) (hw : ω < l) where
  proper : l < ω₁
  base_onto : Surjective (fun x : H.Space ⟨ω, hw⟩ => x.1)
  pastBirths : PastBirths l
  U : (r : BornRows l) → Label → SupportFamily (H.Space r.1)
  Uonto : ∀ r, Surjective (U r)
  V : (r : BornRows l) → SupportFamily (H.Space r.1)
  nu : (r : BornRows l) → Label → BornData (V r)
  nuonto : ∀ r, Surjective (nu r)
  I : Coord l → Coord l → Set ℕ
  J : Coord l → Coord l → Coord l → Set ℕ

namespace Archive

variable {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} (A : Archive H hw)

/-- Bool is converted to the same two arrival slots; no new reservoir is chosen. -/
noncomputable def data : H.Data where
  proper := A.proper
  I := A.I
  J := A.J
  N r d e := if hr : ω ≤ r.1 then
    A.pastBirths.read r.1 d.1 hr (max_lt r.2 d.2) (if e then 1 else 0) else ∅
  V r n := if hr : ω ≤ r.1 then ((A.V ⟨r, hr⟩).clopen n : Set (H.Space r)) else ∅
  Vclopen r n := by
    classical
    by_cases hr : ω ≤ r.1
    · simpa only [dite_eq_left hr] using ((A.V ⟨r, hr⟩).clopen n).isClopen
    · simp only [dite_eq_right hr]; exact isClopen_empty
  nu r d n := if hr : ω ≤ r.1 then (A.nu ⟨r, hr⟩ d).1 n else
    ⟨0, by change Measure.Regular (0 : Measure (H.Space r)) ∧ Measure.Regular (0 : Measure (H.Space r)); exact ⟨inferInstance, inferInstance⟩⟩
  mass r d n hr := by
    classical
    simpa only [dite_eq_left hr] using ((A.nu ⟨r, hr⟩ d).2 n).1

end Archive

private def enlargedCarrier {l : Ordinal.{0}} (H : Prefix l)
    (b : Coord (Order.succ l)) : Set (Cube b.1) :=
  if h : b.1 < l then H.carrier ⟨b.1, h⟩ else (by
    have he : b.1 = l := le_antisymm (Order.le_of_lt_succ b.2) (le_of_not_gt h)
    exact he.symm ▸ H.limitCarrier)

private theorem carrier_old {l : Ordinal.{0}} (H : Prefix l)
    (b : Ordinal.{0}) (hb : b < l) (hb' : b < Order.succ l) :
    enlargedCarrier H ⟨b, hb'⟩ = H.carrier ⟨b, hb⟩ := by
  classical
  simp only [enlargedCarrier, dite_eq_left hb]

private theorem carrier_top {l : Ordinal.{0}} (H : Prefix l) (hb : l < Order.succ l) :
    enlargedCarrier H ⟨l, hb⟩ = H.limitCarrier := by
  classical
  simp only [enlargedCarrier, dite_eq_right (lt_irrefl l)]

/-- Old carriers are unchanged, and the new top is the literal limit subset. -/
noncomputable def literalPrefix {l : Ordinal.{0}} (H : Prefix l) {D : H.Data}
    (E : H.Extension D) : Prefix (Order.succ l) where
  carrier := enlargedCarrier H
  closed := by
    intro ⟨b, hb⟩
    by_cases h : b < l
    · rw [carrier_old H b h hb]; exact H.closed ⟨b, h⟩
    · have he : b = l := le_antisymm (Order.le_of_lt_succ hb) (le_of_not_gt h)
      subst b
      rw [carrier_top H hb]
      change IsClosed {x : Cube l | ∀ a : Coord l, restrict (le_of_lt a.2) x ∈ H.carrier a}
      simp only [ofPred_forall]
      exact isClosed_iInter fun a => (H.closed a).preimage (Pi.continuous_precomp' _)
  nonempty := by
    intro ⟨b, hb⟩
    by_cases h : b < l
    · rw [carrier_old H b h hb]; exact H.nonempty ⟨b, h⟩
    · have he : b = l := le_antisymm (Order.le_of_lt_succ hb) (le_of_not_gt h)
      subst b
      rw [carrier_top H hb]
      obtain ⟨x⟩ := E.inhabited
      exact ⟨x.1, x.2⟩
  compatible := by
    intro ⟨b, hb⟩ ⟨c, hc⟩ h x
    change b ≤ c at h
    by_cases hcold : c < l
    · have hbold : b < l := lt_of_le_of_lt h hcold
      have hx : x.1 ∈ H.carrier ⟨c, hcold⟩ := by
        simpa only [carrier_old H c hcold hc] using x.2
      simpa only [carrier_old H b hbold hb] using
        H.compatible ⟨b, hbold⟩ ⟨c, hcold⟩ h ⟨x.1, hx⟩
    · have he : c = l := le_antisymm (Order.le_of_lt_succ hc) (le_of_not_gt hcold)
      subst c
      have hx : x.1 ∈ H.limitCarrier := by simpa only [carrier_top H hc] using x.2
      by_cases hbold : b < l
      · rw [carrier_old H b hbold hb]; exact hx ⟨b, hbold⟩
      · have he : b = l := le_antisymm h (le_of_not_gt hbold)
        subst b
        exact x.2
  onto := by
    intro ⟨b, hb⟩ ⟨c, hc⟩ h y
    change b ≤ c at h
    by_cases hcold : c < l
    · have hbold : b < l := lt_of_le_of_lt h hcold
      have hy : y.1 ∈ H.carrier ⟨b, hbold⟩ := by
        simpa only [carrier_old H b hbold hb] using y.2
      obtain ⟨x, hx⟩ := H.onto ⟨b, hbold⟩ ⟨c, hcold⟩ h ⟨y.1, hy⟩
      refine ⟨⟨x.1, ?_⟩, hx⟩
      simpa only [carrier_old H c hcold hc] using x.2
    · have he : c = l := le_antisymm (Order.le_of_lt_succ hc) (le_of_not_gt hcold)
      subst c
      by_cases hbold : b < l
      · have hy : y.1 ∈ H.carrier ⟨b, hbold⟩ := by
          simpa only [carrier_old H b hbold hb] using y.2
        obtain ⟨x, hx⟩ := E.onto ⟨b, hbold⟩ ⟨y.1, hy⟩
        refine ⟨⟨x.1, ?_⟩, congrArg Subtype.val hx⟩
        simpa only [carrier_top H hc] using x.2
      · have he : b = l := le_antisymm h (le_of_not_gt hbold)
        subst b
        exact ⟨y, rfl⟩

/-- Identify precisely an old row of the next predecessor with its born archive row. -/
def bornRow {l : Ordinal.{0}} (hw : ω < l) (r : Rows l)
    (hr : r ≠ newRow l hw.le) : BornRows l :=
  ⟨⟨r.1, lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))⟩, r.2.1⟩

namespace Archive

variable {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} (A : Archive H hw)
  (E : H.Extension A.data)

private noncomputable def oldV (r : Rows l) (hr : r ≠ newRow l hw.le) :
    SupportFamily (Base (literalPrefix H E) r) := by
  have hrl : r.1 < l := (bornRow hw r hr).1.2
  simpa [Base, Prefix.Space, literalPrefix, rowIndex, index, enlargedCarrier, bornRow, hrl]
    using A.V (bornRow hw r hr)

private noncomputable def oldU (r : Rows l) (hr : r ≠ newRow l hw.le) :
    Label → SupportFamily (Base (literalPrefix H E) r) := by
  have hrl : r.1 < l := (bornRow hw r hr).1.2
  simpa [Base, Prefix.Space, literalPrefix, rowIndex, index, enlargedCarrier, bornRow, hrl]
    using A.U (bornRow hw r hr)

private noncomputable def oldNu (r : Rows l) (hr : r ≠ newRow l hw.le) :
    Label → BornData (A.oldV E r hr) := by
  have hrl : r.1 < l := (bornRow hw r hr).1.2
  simpa [oldV, Base, Prefix.Space, literalPrefix, rowIndex, index, enlargedCarrier, bornRow, hrl]
    using A.nu (bornRow hw r hr)

/-- The actual limit predecessor: every old whole enumeration and birth is retained. -/
noncomputable def predecessor : Predecessor (literalPrefix H E) hw.le := by
  classical
  refine {
    proper := A.proper
    base_onto := ?_
    births := A.pastBirths
    U := A.oldU E
    Uonto := ?_
    V := A.oldV E
    nu := A.oldNu E
    nuonto := ?_
    I := fun r hr => E.I (bornRow hw r hr).1
    J := fun r hr d => E.J (bornRow hw r hr).1 d
    A := fun r hr d => E.A (bornRow hw r hr).1 d r.2.1
    B := ?_
    C := ?_
    E := ?_
    F := ?_ }
  · simp [K, Prefix.Space, literalPrefix, top, enlargedCarrier]
    intro y
    obtain ⟨z, hz⟩ := A.base_onto y
    obtain ⟨x, hx⟩ := E.onto ⟨ω, hw⟩ z
    exact ⟨x, (congrArg Subtype.val hx).trans hz⟩
  · intro r hr
    have hrl : r.1 < l := (bornRow hw r hr).1.2
    simpa [oldU, Base, Prefix.Space, literalPrefix, rowIndex, index, enlargedCarrier, bornRow, hrl]
      using A.Uonto (bornRow hw r hr)
  · intro r hr
    have hrl : r.1 < l := (bornRow hw r hr).1.2
    simpa [oldNu, oldV, Base, Prefix.Space, literalPrefix, rowIndex, index,
      enlargedCarrier, bornRow, hrl] using A.nuonto (bornRow hw r hr)
  · intro r hr d
    simpa [data, bornRow, r.2.1] using E.B (bornRow hw r hr).1 d r.2.1
  · intro r hr d e
    have h := E.C (bornRow hw r hr).1 d (e == 1) r.2.1
    have he : (if (e == 1) then (1 : Fin 2) else 0) = e := by fin_cases e <;> rfl
    simpa [data, bornRow, r.2.1, he] using h
  · intro r hr c
    have hrl : r.1 < l := (bornRow hw r hr).1.2
    by_cases hc : c.1 < r.1
    · apply Eventually.of_forall
      intro n x y _ _ hxy
      exact congrArg (fun z => z.1 ⟨c.1, hc⟩) hxy
    · have h := E.E (bornRow hw r hr).1 c r.2.1 (le_of_not_gt hc)
      simpa [oldV, Base, K, projection, Prefix.map, Prefix.Space, literalPrefix,
        rowIndex, index, top, enlargedCarrier, bornRow, hrl, data, r.2.1] using h
  · intro r hr d
    have hrl : r.1 < l := (bornRow hw r hr).1.2
    simp [oldNu, oldV, Base, K, projection, Prefix.map, Prefix.Space, literalPrefix,
      rowIndex, index, top, enlargedCarrier, bornRow, hrl]
    intro s hm hn
    letI : MetricSpace H.LimitSpace := H.properMetric A.proper
    let t : ℕ → RegularSigned H.LimitSpace := fun n => ⟨s n, inferInstance, inferInstance⟩
    have ht : ∀ n, H.NewClass A.data (bornRow hw r hr).1 d n (t n) := by
      intro n
      exact ⟨hn n, by simpa [data, bornRow, r.2.1] using hm n⟩
    obtain ⟨mu, _, hconv⟩ := E.F (bornRow hw r hr).1 d r.2.1 t ht
    exact ⟨mu.1, hconv⟩

end Archive

/-- The event retains the exact extension, including DI/DJ and regular bounded F. -/
structure Result {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} (A : Archive H hw) where
  extension : H.Extension A.data

namespace Result

variable {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} {A : Archive H hw} (R : Result A)

noncomputable def extended : Prefix (Order.succ l) := literalPrefix H R.extension

noncomputable def predecessor : Predecessor R.extended hw.le := A.predecessor R.extension

end Result

/-- Execute joint proper-limit fusion once on the actual strict archive. -/
noncomputable def construct {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l}
    (A : Archive H hw) (hl : Order.IsSuccLimit l) (L : H.Laws A.data) : Result A :=
  ⟨Classical.choice (H.exists_joint_proper_limit_extension hl A.proper hw A.data L)⟩

end D5.S3.Topology.InverseLimit.SignedOrdinalLimit
