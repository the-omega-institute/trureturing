/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryPast
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: The literal prefix assembled from one exact coherent strict past. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

/-! The past supplies only already constructed proper-stage states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open D5.S3.Topology.Measures

local instance carrierMeasurable {b : Ordinal.{0}} (C : Set (Cube b)) :
    MeasurableSpace C := borel C
local instance carrierBorel {b : Ordinal.{0}} (C : Set (Cube b)) :
    BorelSpace C := ⟨rfl⟩

private theorem current_E {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
    (P : Predecessor H ha) (r : Rows a) (hr : r ≠ newRow a ha)
    {C : Set (Cube a)} {D : Set (Cube r.1)}
    (hC : C = H.carrier (top a)) (hD : D = H.carrier (rowIndex r))
    (W : BirthPack D) (hV : HEq W.V (P.V r hr))
    (f : C(C, D)) (hf : ∀ x, (f x).1 = restrict r.2.2 x.1) (xi : Coord a) :
    ∀ᶠ n in along (P.I r hr), ∀ x y : C,
      f x ∈ W.V.clopen n → f y ∈ W.V.clopen n → f x = f y → x.1 xi = y.1 xi := by
  subst C
  subst D
  have hv := eq_of_heq hV
  have hmap : f = projection H r := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hf x)
  simpa only [hmap, hv] using P.E r hr xi

private theorem current_F {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
    (P : Predecessor H ha) (reg : RegularCurrent H ha P)
    (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a)
    {C : Set (Cube a)} {D : Set (Cube r.1)} [CompactSpace C]
    (hC : C = H.carrier (top a)) (hD : D = H.carrier (rowIndex r))
    (W : BirthPack D)
    (hnu : ∀ n, HEq (W.measure ⟨d.1, d.2.trans P.proper⟩ n)
      (((P.nu r hr ⟨d.1, d.2.trans P.proper⟩).1 n).1))
    (f : C(C, D)) (hf : ∀ x, (f x).1 = restrict r.2.2 x.1)
    (s : ℕ → RegularSigned C)
    (hm : ∀ n, (s n).1.map f = W.measure ⟨d.1, d.2.trans P.proper⟩ n)
    (hn : ∀ n, (s n).1.totalVariation univ = 1) :
    ∃ mu : RegularSigned C, mu.1.totalVariation.real univ ≤ 1 ∧ Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
      (along (P.J r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu.1).toWeakDual) := by
  subst C
  subst D
  have hmap : f = projection H r := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hf x)
  apply reg r hr d s
  · intro n
    exact (by simpa only [hmap] using hm n).trans (eq_of_heq (hnu n))
  · exact hn

variable {l : Ordinal.{0}} (proper : l < ω₁)
  (past : ∀ b : Stage, ord b < l → State b)
  (coherent : ∀ b c (hb : ord b < l) (hc : ord c < l) (hbc : b < c),
    Coherent hbc (past b hb) (past c hc))

noncomputable def pastCarrier (c : Coord l) : Set (Cube c.1) := by
  classical
  exact if hω : ω ≤ c.1 then
    (past ⟨⟨c.1, c.2.trans proper⟩, hω⟩ c.2).H.carrier (top c.1)
  else univ

private theorem carrier_read (b : Stage) (hb : ord b < l)
    (c : Coord (Order.succ (ord b))) :
    pastCarrier proper past ⟨c.1, (Order.le_of_lt_succ c.2).trans_lt hb⟩ =
      (past b hb).H.carrier c := by
  classical
  by_cases hω : ω ≤ c.1
  · let cb : Stage := ⟨⟨c.1, ((Order.le_of_lt_succ c.2).trans_lt hb).trans proper⟩, hω⟩
    change (if hω' : ω ≤ c.1 then
      (past ⟨⟨c.1, _⟩, hω'⟩ _).H.carrier (top c.1) else univ) = _
    rw [dite_eq_left hω]
    change (past cb _).H.carrier (top (ord cb)) = _
    by_cases he : c.1 = ord b
    · have he' : cb = b := Subtype.ext (Subtype.ext he)
      rw [he']
      congr 1
      exact Subtype.ext he.symm
    · have hcb : cb < b := lt_of_le_of_ne (Order.le_of_lt_succ c.2) he
      exact ((coherent cb b _ hb hcb).carrier (top (ord cb))).symm
  · have hc : c.1 ≤ ω := (lt_of_not_ge hω).le
    exact (show pastCarrier proper past ⟨c.1, _⟩ = univ from by
      simp only [pastCarrier, dite_eq_right hω]).trans
      ((past b hb).initial_carriers c hc).symm

/-- Prefix geometry is obtained by reading actual earlier carriers. The finite
initial segment is H0, and every other projection is read inside the later
already constructed state's literal Prefix. -/
noncomputable def strictPrefix : Prefix l where
  carrier := pastCarrier proper past
  closed := by
    classical
    intro c
    by_cases hω : ω ≤ c.1
    · simpa only [pastCarrier, dite_eq_left hω] using
        (past ⟨⟨c.1, c.2.trans proper⟩, hω⟩ c.2).H.closed (top c.1)
    · simp only [pastCarrier, dite_eq_right hω]
      exact isClosed_univ
  nonempty := by
    classical
    intro c
    by_cases hω : ω ≤ c.1
    · simpa only [pastCarrier, dite_eq_left hω] using
        (past ⟨⟨c.1, c.2.trans proper⟩, hω⟩ c.2).H.nonempty (top c.1)
    · exact ⟨fun _ => false, by simp only [pastCarrier, dite_eq_right hω, mem_univ]⟩
  compatible := by
    classical
    intro c d h x
    by_cases hω : ω ≤ d.1
    · let db : Stage := ⟨⟨d.1, d.2.trans proper⟩, hω⟩
      let ci : Coord (Order.succ d.1) := ⟨c.1, h.trans_lt (Order.lt_succ d.1)⟩
      have hc := carrier_read proper past coherent db d.2 ci
      have hd := carrier_read proper past coherent db d.2 (top d.1)
      change restrict h x.1 ∈ pastCarrier proper past c
      rw [hc]
      apply (past db d.2).H.compatible ci (top d.1) h
      exact ⟨x.1, hd ▸ x.2⟩
    · have hc : ¬ ω ≤ c.1 := fun h' => hω (h'.trans h)
      simp only [pastCarrier, dite_eq_right hc, mem_univ]
  onto := by
    classical
    intro c d h y
    by_cases hω : ω ≤ d.1
    · let db : Stage := ⟨⟨d.1, d.2.trans proper⟩, hω⟩
      let ci : Coord (Order.succ d.1) := ⟨c.1, h.trans_lt (Order.lt_succ d.1)⟩
      have hc := carrier_read proper past coherent db d.2 ci
      have hd := carrier_read proper past coherent db d.2 (top d.1)
      obtain ⟨x, hx⟩ := (past db d.2).H.onto ci (top d.1) h ⟨y.1, hc ▸ y.2⟩
      exact ⟨⟨x.1, hd.symm ▸ x.2⟩, hx⟩
    · have hc : c.1 < ω := h.trans_lt (lt_of_not_ge hω)
      let ci : Coord (Order.succ (ω : Ordinal.{0})) := ⟨c.1, hc.trans (Order.lt_succ ω)⟩
      let di : Coord (Order.succ (ω : Ordinal.{0})) :=
        ⟨d.1, (lt_of_not_ge hω).trans (Order.lt_succ ω)⟩
      obtain ⟨x, hx⟩ := SignedOrdinalInitial.H0.onto ci di h ⟨y.1, mem_univ _⟩
      exact ⟨⟨x.1, by simp only [pastCarrier, dite_eq_right hω, mem_univ]⟩, hx⟩

/-- The birth pack at r is the one actual Q@r, on the identical literal carrier. -/
noncomputable def bornPack (r : Coord l) (hr : ω ≤ r.1) :
    BirthPack ((strictPrefix proper past coherent).carrier r) := by
  classical
  exact BirthPack.cast (by simp only [strictPrefix, pastCarrier, dite_eq_left hr])
    (past ⟨⟨r.1, r.2.trans proper⟩, hr⟩ r.2).birth

private def stageAt (c : Coord l) (hc : ω ≤ c.1) : Stage :=
  ⟨⟨c.1, c.2.trans proper⟩, hc⟩

private def rowAt (r c : Coord l) (hr : ω ≤ r.1) (hrc : r < c) : Rows c.1 :=
  ⟨r.1, hr, hrc.le⟩

private theorem rowAt_ne (r c : Coord l) (hr : ω ≤ r.1) (hrc : r < c) :
    rowAt r c hr hrc ≠ newRow c.1 (hr.trans hrc.le) := by
  intro he
  exact (ne_of_lt hrc) (congrArg Subtype.val he)

private theorem bornPack_read (r c : Coord l) (hr : ω ≤ r.1) (hrc : r < c) :
    HEq (bornPack proper past coherent r hr)
      ((past (stageAt proper c (hr.trans hrc.le)) c.2).oldBirth
        (rowAt r c hr hrc) (rowAt_ne r c hr hrc)) := by
  have hb := (coherent (stageAt proper r hr)
    (stageAt proper c (hr.trans hrc.le)) r.2 c.2 hrc).birth
  exact (BirthPack.cast_heq _ _).trans
    ((heq_of_eq hb).trans (BirthPack.cast_heq _ _)).symm

private noncomputable def historicalI (r c : Coord l) : Set ℕ := by
  classical
  exact if hr : ω ≤ r.1 then
    if hrc : r < c then
      (past (stageAt proper c (hr.trans hrc.le)) c.2).P.I
        (rowAt r c hr hrc) (rowAt_ne r c hr hrc)
    else ∅
  else ∅

private noncomputable def historicalJ (r d c : Coord l) : Set ℕ := by
  classical
  exact if hr : ω ≤ r.1 then
    if hrc : r < c then
      if hdc : d < c then
        (past (stageAt proper c (hr.trans hrc.le)) c.2).P.J
          (rowAt r c hr hrc) (rowAt_ne r c hr hrc) ⟨d.1, hdc⟩
      else ∅
    else ∅
  else ∅

/-- Only arrivals E_(succ m) strictly below l may be read by recursive limit
Data. IsSuccLimit l supplies that strict inequality for every m<l. -/
private noncomputable def historicalN (hl : Order.IsSuccLimit l)
    (r d : Coord l) (e : Bool) : Set ℕ := by
  classical
  exact if hr : ω ≤ r.1 then
    let m : Stage := ⟨⟨max r.1 d.1, (max_lt r.2 d.2).trans proper⟩,
      hr.trans (le_max_left _ _)⟩
    let arrival_before : Order.succ (ord m) < l := hl.succ_lt (max_lt r.2 d.2)
    (past m ((Order.lt_succ (ord m)).trans arrival_before)).event.result.N
      ⟨r.1, hr, le_max_left _ _⟩ ⟨d.1, le_max_right _ _⟩ (if e then 1 else 0)
  else ∅

private def zeroRegular (X : Type*) [TopologicalSpace X] [MeasurableSpace X] :
    RegularSigned X := ⟨0, by
      simp only [SignedMeasure.toJordanDecomposition_zero,
        JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart]
      exact ⟨inferInstance, inferInstance⟩⟩

/-- Proper-limit Data use only exact strict-past births and incoming I/J.
There is no Data at omega-one and no artificial arrival at the limit. -/
noncomputable def strictData (hl : Order.IsSuccLimit l) :
    (strictPrefix proper past coherent).Data where
  proper := proper
  I := historicalI proper past
  J := historicalJ proper past
  N := historicalN proper past hl
  V := fun r n => if hr : ω ≤ r.1 then
    ((bornPack proper past coherent r hr).V.clopen n : Set _)
    else ∅
  Vclopen := by
    classical
    intro r n
    split
    · exact ((bornPack proper past coherent r _).V.clopen n).isClopen
    · exact isClopen_empty
  nu := fun r d n => if hr : ω ≤ r.1 then
    ((bornPack proper past coherent r hr).nu d).1 n
    else zeroRegular _
  mass := by
    classical
    intro r d n hr
    simp only [dite_eq_left hr]
    exact ((bornPack proper past coherent r hr).nu d).2 n |>.1

private theorem strict_A (hl : Order.IsSuccLimit l) (r d c : Coord l)
    (hr : ω ≤ r.1) (hrc : r < c) (hdc : d < c) :
    (strictData proper past coherent hl).J r d c ⊆
      (strictData proper past coherent hl).I r c := by
  classical
  simpa only [strictData, historicalI, historicalJ, dite_eq_left hr,
    dite_eq_left hrc, dite_eq_left hdc] using
    (past (stageAt proper c (hr.trans hrc.le)) c.2).P.A
      (rowAt r c hr hrc) (rowAt_ne r c hr hrc) ⟨d.1, hdc⟩

private theorem strict_B (hl : Order.IsSuccLimit l) (r d : Coord l)
    (hr : ω ≤ r.1) :
    Disjoint ((strictData proper past coherent hl).N r d false)
      ((strictData proper past coherent hl).N r d true) := by
  classical
  let m : Stage := ⟨⟨max r.1 d.1, (max_lt r.2 d.2).trans proper⟩,
    hr.trans (le_max_left _ _)⟩
  let hm : ord m < l := (Order.lt_succ (ord m)).trans (hl.succ_lt (max_lt r.2 d.2))
  change Disjoint ((past m hm).event.result.N ⟨r.1, hr, le_max_left _ _⟩
    ⟨d.1, le_max_right _ _⟩ 0) ((past m hm).event.result.N
      ⟨r.1, hr, le_max_left _ _⟩ ⟨d.1, le_max_right _ _⟩ 1)
  exact (past m hm).event.result.B _ _

private theorem N_read (hl : Order.IsSuccLimit l) (r d c : Coord l)
    (hr : ω ≤ r.1) (hrc : r < c) (hdc : d < c) (e : Bool) :
    historicalN proper past hl r d e =
      (past (stageAt proper c (hr.trans hrc.le)) c.2).P.oldN
        (rowAt r c hr hrc) (rowAt_ne r c hr hrc) ⟨d.1, hdc⟩ (if e then 1 else 0) := by
  classical
  let m : Stage := ⟨⟨max r.1 d.1, (max_lt r.2 d.2).trans proper⟩,
    hr.trans (le_max_left _ _)⟩
  have hmc : m < stageAt proper c (hr.trans hrc.le) := max_lt hrc hdc
  simp only [historicalN, dite_eq_left hr]
  exact ((coherent m (stageAt proper c (hr.trans hrc.le)) _ c.2 hmc).arrival
    r.1 d.1 hr rfl (if e then 1 else 0)).symm

private theorem strict_C (hl : Order.IsSuccLimit l) (r d c : Coord l) (e : Bool)
    (hr : ω ≤ r.1) (hrc : r < c) (hdc : d < c) :
    ((strictData proper past coherent hl).J r d c ∩
      (strictData proper past coherent hl).N r d e).Infinite := by
  change (historicalJ proper past r d c ∩ historicalN proper past hl r d e).Infinite
  rw [N_read proper past coherent hl r d c hr hrc hdc e]
  simpa only [historicalJ, dite_eq_left hr, dite_eq_left hrc, dite_eq_left hdc] using
    (past (stageAt proper c (hr.trans hrc.le)) c.2).P.C
      (rowAt r c hr hrc) (rowAt_ne r c hr hrc) ⟨d.1, hdc⟩ (if e then 1 else 0)

private theorem strict_DI (hl : Order.IsSuccLimit l) (r a b : Coord l)
    (hr : ω ≤ r.1) (hra : r < a) (hab : a ≤ b) :
    AlmostSubset ((strictData proper past coherent hl).I r b)
      ((strictData proper past coherent hl).I r a) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    exact Filter.Eventually.of_forall (fun _ hn => hn)
  · have hrb := hra.trans hab
    simpa only [strictData, historicalI, dite_eq_left hr, dite_eq_left hra,
      dite_eq_left hrb] using
      (coherent (stageAt proper a (hr.trans hra.le))
        (stageAt proper b (hr.trans hrb.le)) a.2 b.2 hab).DI
        (rowAt r a hr hra) (rowAt_ne r a hr hra)

private theorem strict_DJ (hl : Order.IsSuccLimit l) (r d a b : Coord l)
    (hr : ω ≤ r.1) (hra : r < a) (hda : d < a) (hab : a ≤ b) :
    AlmostSubset ((strictData proper past coherent hl).J r d b)
      ((strictData proper past coherent hl).J r d a) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    exact Filter.Eventually.of_forall (fun _ hn => hn)
  · have hrb := hra.trans hab
    have hdb := hda.trans hab
    simpa only [strictData, historicalJ, dite_eq_left hr, dite_eq_left hra,
      dite_eq_left hrb, dite_eq_left hda, dite_eq_left hdb] using
      (coherent (stageAt proper a (hr.trans hra.le))
        (stageAt proper b (hr.trans hrb.le)) a.2 b.2 hab).DJ
        (rowAt r a hr hra) (rowAt_ne r a hr hra) ⟨d.1, hda⟩

private theorem strict_E (hl : Order.IsSuccLimit l) (r c : Coord l) (hrc : r < c)
    (xi : Coord c.1) (hr : ω ≤ r.1) (_ : r.1 ≤ xi.1) :
    ∀ᶠ n in along ((strictData proper past coherent hl).I r c),
      ∀ x y : (strictPrefix proper past coherent).Space c,
      (strictPrefix proper past coherent).map r c hrc.le x ∈
        (strictData proper past coherent hl).V r n →
      (strictPrefix proper past coherent).map r c hrc.le y ∈
        (strictData proper past coherent hl).V r n →
      (strictPrefix proper past coherent).map r c hrc.le x =
        (strictPrefix proper past coherent).map r c hrc.le y → x.1 xi = y.1 xi := by
  classical
  let cb := stageAt proper c (hr.trans hrc.le)
  let X := past cb c.2
  let rr := rowAt r c hr hrc
  let hrr := rowAt_ne r c hr hrc
  have hC := carrier_read proper past coherent cb c.2 (top c.1)
  have hD := carrier_read proper past coherent cb c.2 (rowIndex rr)
  have hV := BirthPack.heq_V hD _ _ (bornPack_read proper past coherent r c hr hrc)
  have he := current_E X.P rr hrr hC hD (bornPack proper past coherent r hr) hV
    ((strictPrefix proper past coherent).map r c hrc.le) (fun _ => rfl) xi
  simpa only [strictData, historicalI, dite_eq_left hr, dite_eq_left hrc] using he

private theorem strict_F (hl : Order.IsSuccLimit l) (r d c : Coord l) (hrc : r < c)
    (hr : ω ≤ r.1) (hdc : d < c)
    (s : ℕ → RegularSigned ((strictPrefix proper past coherent).Space c))
    (hs : ∀ n, (strictPrefix proper past coherent).OldClass
      (strictData proper past coherent hl) r d c hrc.le n (s n)) :
    ∃ mu : RegularSigned ((strictPrefix proper past coherent).Space c),
      mu.1.totalVariation.real univ ≤ 1 ∧ Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
        (along ((strictData proper past coherent hl).J r d c))
        (𝓝 (NormPreservingLifts.signedFunctional mu.1).toWeakDual) := by
  classical
  let cb := stageAt proper c (hr.trans hrc.le)
  let X := past cb c.2
  let rr := rowAt r c hr hrc
  let hrr := rowAt_ne r c hr hrc
  have hC := carrier_read proper past coherent cb c.2 (top c.1)
  have hD := carrier_read proper past coherent cb c.2 (rowIndex rr)
  have hnu := fun n => BirthPack.heq_measure hD _ _
    (bornPack_read proper past coherent r c hr hrc) ⟨d.1, d.2.trans proper⟩ n
  have hf := current_F X.P X.regular rr hrr ⟨d.1, hdc⟩ hC hD
    (bornPack proper past coherent r hr) hnu
    ((strictPrefix proper past coherent).map r c hrc.le) (fun _ => rfl) s
    (fun n => by simpa only [Prefix.OldClass, strictData, dite_eq_left hr] using (hs n).2)
    (fun n => (hs n).1)
  simpa only [strictData, historicalJ, dite_eq_left hr, dite_eq_left hrc,
    dite_eq_left hdc] using hf

/-- All original eligible laws hold on this exact strict-past prefix. -/
theorem strictLaws (hl : Order.IsSuccLimit l) :
    (strictPrefix proper past coherent).Laws (strictData proper past coherent hl) where
  A := strict_A proper past coherent hl
  B := strict_B proper past coherent hl
  C := strict_C proper past coherent hl
  DI := strict_DI proper past coherent hl
  DJ := strict_DJ proper past coherent hl
  E := strict_E proper past coherent hl
  F := strict_F proper past coherent hl

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast
