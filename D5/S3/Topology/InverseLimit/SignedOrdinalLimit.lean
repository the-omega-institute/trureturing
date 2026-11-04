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
    ⟨0, by
      simp only [SignedMeasure.toJordanDecomposition_zero]
      change Measure.Regular (0 : Measure (H.Space r)) ∧
        Measure.Regular (0 : Measure (H.Space r))
      exact ⟨inferInstance, inferInstance⟩⟩
  mass r d n hr := by
    classical
    simpa [hr] using ((A.nu ⟨r, hr⟩ d).2 n).1

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

/-- One whole born row is cast once, so its dependent V/nu pair stays together. -/
private structure SavedRow {b : Ordinal.{0}} (C : Set (Cube b)) where
  U : Label → SupportFamily C
  Uonto : Surjective U
  V : SupportFamily C
  nu : Label → @BornData C _ (borel C) V
  nuonto : Surjective nu

private def savedRow (r : BornRows l) : SavedRow (H.carrier r.1) :=
  ⟨A.U r, A.Uonto r, A.V r, A.nu r, A.nuonto r⟩

private noncomputable def oldPack (r : Rows l) (hr : r ≠ newRow l hw.le) :
    SavedRow ((literalPrefix H E).carrier (rowIndex r)) := by
  have hrl : r.1 < l := (bornRow hw r hr).1.2
  change SavedRow (enlargedCarrier H (rowIndex r))
  rw [carrier_old H r.1 hrl _]
  exact A.savedRow (bornRow hw r hr)

private theorem oldPack_heq (r : Rows l) (hr : r ≠ newRow l hw.le) :
    HEq (A.oldPack E r hr) (A.savedRow (bornRow hw r hr)) := by
  unfold oldPack
  exact cast_heq _ _

private theorem limit_e (r : BornRows l) (c : Coord l) (hc : r.1.1 ≤ c.1)
    {C : Set (Cube l)} {B : Set (Cube r.1.1)}
    (hC : C = H.limitCarrier) (hB : B = H.carrier r.1)
    (p : C(C, B)) (hp : ∀ x, (p x).1 = restrict r.1.2.le x.1)
    (Q : SavedRow B) (hQ : HEq Q (A.savedRow r)) :
    ∀ᶠ n in along (E.I r.1), ∀ x y : C,
      p x ∈ Q.V.clopen n → p y ∈ Q.V.clopen n → p x = p y → x.1 c = y.1 c := by
  subst C
  subst B
  have hQ' := eq_of_heq hQ
  subst Q
  have hp' : p = H.projection r.1 := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hp x)
  subst p
  simpa [data, savedRow, r.2] using E.E r.1 c r.2 hc

private theorem limit_f (r : BornRows l) (d : Coord l)
    {C : Set (Cube l)} [CompactSpace C] {B : Set (Cube r.1.1)}
    (hC : C = H.limitCarrier) (hB : B = H.carrier r.1)
    (p : C(C, B)) (hp : ∀ x, (p x).1 = restrict r.1.2.le x.1)
    (Q : SavedRow B) (hQ : HEq Q (A.savedRow r)) :
    letI : MeasurableSpace C := borel C
    letI : BorelSpace C := ⟨rfl⟩
    letI : MeasurableSpace B := borel B
    ∀ (s : ℕ → SignedMeasure C),
      (∀ n, (s n).map p = ((Q.nu ⟨d.1, d.2.trans A.proper⟩).1 n).1) →
      (∀ n, (s n).totalVariation univ = 1) →
      ∃ mu : SignedMeasure C, Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        (along (E.J r.1 d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  subst C
  subst B
  have hQ' := eq_of_heq hQ
  subst Q
  have hp' : p = H.projection r.1 := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hp x)
  subst p
  intro s hm hn
  let : MetricSpace H.LimitSpace := H.properMetric A.proper
  let t : ℕ → RegularSigned H.LimitSpace := fun n => ⟨s n, inferInstance, inferInstance⟩
  have ht : ∀ n, H.NewClass A.data r.1 d n (t n) := by
    intro n
    exact ⟨hn n, by simpa [data, savedRow, r.2] using hm n⟩
  obtain ⟨mu, _, hconv⟩ := E.F r.1 d r.2 t ht
  exact ⟨mu.1, hconv⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual limit predecessor: every old whole enumeration and birth is retained. -/
noncomputable def predecessor : Predecessor (literalPrefix H E) hw.le := by
  with_unfolding_all
    classical
    refine {
      proper := A.proper
      base_onto := ?_
      births := A.pastBirths
      U := fun r hr => (A.oldPack E r hr).U
      Uonto := fun r hr => (A.oldPack E r hr).Uonto
      V := fun r hr => (A.oldPack E r hr).V
      nu := fun r hr => (A.oldPack E r hr).nu
      nuonto := fun r hr => (A.oldPack E r hr).nuonto
      I := fun r hr => E.I (bornRow hw r hr).1
      J := fun r hr d => E.J (bornRow hw r hr).1 d
      A := fun r hr d => E.A (bornRow hw r hr).1 d r.2.1
      B := ?_
      C := ?_
      E := ?_
      F := ?_ }
    · change Surjective (fun x : enlargedCarrier H (top l) => restrict hw.le x.1)
      rw [carrier_top H (Order.lt_succ l)]
      intro y
      obtain ⟨z, hz⟩ := A.base_onto y
      obtain ⟨x, hx⟩ := E.onto ⟨ω, hw⟩ z
      exact ⟨x, (congrArg Subtype.val hx).trans hz⟩
    · intro r hr d
      simpa [data, bornRow, r.2.1] using E.B (bornRow hw r hr).1 d r.2.1
    · intro r hr d e
      fin_cases e
      · simpa [data, bornRow, r.2.1] using E.C (bornRow hw r hr).1 d false r.2.1
      · simpa [data, bornRow, r.2.1] using E.C (bornRow hw r hr).1 d true r.2.1
    · intro r hr c
      by_cases hc : c.1 < r.1
      · apply Eventually.of_forall
        intro n x y _ _ hxy
        exact congrArg (fun z => z.1 ⟨c.1, hc⟩) hxy
      · exact A.limit_e E (bornRow hw r hr) c (le_of_not_gt hc)
          (carrier_top H _) (carrier_old H r.1 (bornRow hw r hr).1.2 _)
          (projection (literalPrefix H E) r) (fun _ => rfl)
          (A.oldPack E r hr) (A.oldPack_heq E r hr)
    · intro r hr d
      exact @limit_f l H hw A E (bornRow hw r hr) d
        ((literalPrefix H E).carrier (top l)) ((literalPrefix H E).spaceCompact (top l))
        ((literalPrefix H E).carrier (rowIndex r))
        (carrier_top H _) (carrier_old H r.1 (bornRow hw r hr).1.2 _)
        (projection (literalPrefix H E) r) (fun _ => rfl)
        (A.oldPack E r hr) (A.oldPack_heq E r hr)

private theorem savedRow_readbacks {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (W : SavedRow C) (W' : SavedRow D) (he : HEq W W') :
    HEq W.U W'.U ∧ HEq W.V W'.V ∧ HEq W.nu W'.nu := by
  subst D
  cases eq_of_heq he
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- Whole old labels are the same archive labels on the unchanged literal carrier. -/
theorem predecessor_whole_readback (r : Rows l) (hr : r ≠ newRow l hw.le) :
    HEq ((A.predecessor E).U r hr) (A.U (bornRow hw r hr)) ∧
    HEq ((A.predecessor E).V r hr) (A.V (bornRow hw r hr)) ∧
    HEq ((A.predecessor E).nu r hr) (A.nu (bornRow hw r hr)) := by
  exact savedRow_readbacks (carrier_old H r.1 (bornRow hw r hr).1.2 _)
    (A.oldPack E r hr) (A.savedRow (bornRow hw r hr)) (A.oldPack_heq E r hr)

end Archive

/-- The event retains the exact extension, including DI/DJ and regular bounded F. -/
structure Result {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} (A : Archive H hw) where
  extension : H.Extension A.data
  old_carrier : ∀ b : Coord l,
    (literalPrefix H extension).carrier ⟨b.1, b.2.trans (Order.lt_succ l)⟩ = H.carrier b
  top_carrier : (literalPrefix H extension).carrier (top l) = H.limitCarrier
  births_eq : (A.predecessor extension).births = A.pastBirths
  I_eq : ∀ r hr, (A.predecessor extension).I r hr = extension.I (bornRow hw r hr).1
  J_eq : ∀ r hr d, (A.predecessor extension).J r hr d = extension.J (bornRow hw r hr).1 d
  data_N : ∀ (r : BornRows l) (d : Coord l) (e : Bool),
    A.data.N r.1 d e = A.pastBirths.read r.1.1 d.1 r.2
      (max_lt r.1.2 d.2) (if e then 1 else 0)
  data_V : ∀ (r : BornRows l) n, A.data.V r.1 n = ((A.V r).clopen n : Set (H.Space r.1))
  data_nu : ∀ (r : BornRows l) d n, A.data.nu r.1 d n = (A.nu r d).1 n

namespace Result

variable {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l} {A : Archive H hw} (R : Result A)

noncomputable def extended : Prefix (Order.succ l) := literalPrefix H R.extension

noncomputable def predecessor : Predecessor R.extended hw.le := A.predecessor R.extension

end Result

/-- Execute joint proper-limit fusion once on the actual strict archive. -/
noncomputable def construct {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l}
    (A : Archive H hw) (hl : Order.IsSuccLimit l) (L : H.Laws A.data) : Result A := by
  classical
  let E := Classical.choice (H.exists_joint_proper_limit_extension hl A.proper hw A.data L)
  refine {
    extension := E
    old_carrier := fun b => carrier_old H b.1 b.2 _
    top_carrier := carrier_top H (Order.lt_succ l)
    births_eq := rfl
    I_eq := fun _ _ => rfl
    J_eq := fun _ _ _ => rfl
    data_N := ?_
    data_V := ?_
    data_nu := ?_ }
  · intro r d e
    simp [Archive.data, r.2]
  · intro r n
    simp [Archive.data, r.2]
  · intro r d n
    simp [Archive.data, r.2]

end D5.S3.Topology.InverseLimit.SignedOrdinalLimit
