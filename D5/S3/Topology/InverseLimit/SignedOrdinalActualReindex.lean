/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalActualReindex
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Same-label support and measure reads for every selected actual event. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth
import D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents

/-! The original selected event supplies both reads at one new label. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Ordinal Cardinal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalHistoryTask SignedOrdinalRealization SignedOrdinalRealizationEvents
open SignedOrdinalReindexCodes SignedOrdinalReindexedBirth CofinalTaskSchedule

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

private theorem map_onto (b c : Label) (h : b ≤ c) :
    Surjective ((finalPrefix hCH).map b c h) := by
  intro y
  obtain ⟨x, hx⟩ := (finalPrefix hCH).onto b c h y
  exact ⟨x, Subtype.ext hx⟩

/-- The actual omega/zero support on the literal row carrier. -/
noncomputable def actualDelayedSupport (θ : Stage) :
    SupportFamily ((finalPrefix hCH).Space θ.1) :=
  ((wholeBirth hCH initialStage).U zeroLabel).pullback
    ((finalPrefix hCH).map initialStage.1 θ.1 θ.2) (map_onto hCH _ _ _)

/-- This uses exactly the original wholeBirth, so its measureIndex agrees
with every other adapter of that birth by definitional equality. -/
noncomputable def actualBirth (θ : Stage) :
    BirthPack ((finalPrefix hCH).carrier θ.1) :=
  reindexBirth (wholeBirth hCH θ) (actualDelayedSupport hCH θ)

private theorem actual_intrinsic {θ a : Stage} (hθ : θ < a)
    (s t : Label) (hs : s < a.1) (ht : t < a.1) (k : ℕ) :
    LocalDelayed (SignedOrdinalHistory.run hCH a).event.Q
      (SignedOrdinalHistory.run hCH a).event.oldB θ.1 s t k ↔
      Intrinsic (wholeBirth hCH θ) s t k := by
  exact (stable_local hθ _ _ (SignedOrdinalHistory.coherent hCH θ a hθ)
    s t hs ht k).trans (intrinsic_cast (top_read hCH θ).symm _ s t k).symm

/-- None records the original rejected-task fallback, without hole coloring. -/
abbrev Plan := (θ : Stage) × Option (Tag (wholeBirth hCH θ))

private def fallbackPlan : Plan hCH := ⟨initialStage, none⟩

/-- The actual reservation is decoded once, with the actual local test. -/
noncomputable def plan (a : Stage) : Plan hCH := by
  classical
  exact match (reservation a.1).1 with
  | .inl (r, d) =>
      if hv : OrdinaryValid a.1 r d then ⟨⟨r, hv.1⟩, some (.inl d)⟩
      else fallbackPlan hCH
  | .inr (r, s, t, k) =>
      if hv : LocalDelayed (SignedOrdinalHistory.run hCH a).event.Q
          (SignedOrdinalHistory.run hCH a).event.oldB r s t k then
        ⟨⟨r, hv.1.1⟩, some (.inr ⟨(s, t, k),
          (actual_intrinsic hCH hv.1.2.1 s t hv.1.2.2.1 hv.1.2.2.2 k).mp hv⟩)⟩
      else fallbackPlan hCH

private noncomputable def oldTarget (p : Plan hCH) : Label :=
  match p.2 with | none => zeroLabel | some z => target (wholeBirth hCH p.1) z

private def launchTarget (p : Plan hCH) : Label × Label :=
  match p.2 with
  | some (.inl d) => (p.1.1, d)
  | _ => fallback

private def tagOccurs (a : Label) (p : Plan hCH) : Prop :=
  match p with
  | ⟨θ, none⟩ => θ = initialStage
  | ⟨θ, some z⟩ => Occurs (wholeBirth hCH θ) z a

private def PlanLaw (a : Stage) (p : Plan hCH) : Prop :=
  p.1 ≤ a ∧
  ((SignedOrdinalHistory.run hCH a).event.selected.treatment.row.1,
    (SignedOrdinalHistory.run hCH a).event.selected.treatment.label.1) =
      (p.1.1.1, (oldTarget hCH p).1) ∧
  tagOccurs hCH a.1 p ∧
  CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False) = launchTarget hCH p

private theorem plan_law (a : Stage) : PlanLaw hCH a (plan hCH a) := by
  classical
  have htarget := (SignedOrdinalHistory.run hCH a).event.target
  unfold plan
  split
  next r d he =>
    split_ifs with hv
    · refine ⟨hv.2.1, ?_, ⟨he, hv⟩, ?_⟩
      · simpa [CofinalTaskSchedule.execute, he, hv, oldTarget, target] using htarget
      · simp [CofinalTaskSchedule.execute, he, hv, launchTarget]
    · refine ⟨a.2, ?_, rfl, ?_⟩
      · simpa [CofinalTaskSchedule.execute, he, hv, fallbackPlan, oldTarget,
          fallback, zeroLabel, initialStage] using htarget
      · simp [CofinalTaskSchedule.execute, he, hv, launchTarget, fallbackPlan]
  next r s t k he =>
    split_ifs with hv
    · refine ⟨hv.1.2.1.le, ?_, ⟨he, hv.1⟩, ?_⟩
      · simpa [CofinalTaskSchedule.execute, he, hv, hv.1, oldTarget, target] using htarget
      · simp [CofinalTaskSchedule.execute, he, launchTarget]
    · have hn : ¬ (DelayedValid a.1 r s t ∧
          LocalDelayed (SignedOrdinalHistory.run hCH a).event.Q
            (SignedOrdinalHistory.run hCH a).event.oldB r s t k) := fun h => hv h.2
      refine ⟨a.2, ?_, rfl, ?_⟩
      · simpa [CofinalTaskSchedule.execute, he, hn, fallbackPlan, oldTarget,
          fallback, zeroLabel, initialStage] using htarget
      · simp [CofinalTaskSchedule.execute, he, launchTarget, fallbackPlan]

/-- The actual treatment row, with no reselection of the event. -/
noncomputable def eventRow (a : Stage) : Stage := (plan hCH a).1

private noncomputable def planIndex (a : Label) (p : Plan hCH) : Label :=
  match p with
  | ⟨_, none⟩ => zeroLabel
  | ⟨θ, some z⟩ => eventIndex (wholeBirth hCH θ) z a

/-- One all-stage label: rejected tasks use zero directly. -/
noncomputable def eta (a : Stage) : Label := planIndex hCH a.1 (plan hCH a)

theorem eventRow_le (a : Stage) : eventRow hCH a ≤ a := (plan_law hCH a).1

theorem eta_le (a : Stage) : eta hCH a ≤ a.1 := by
  have hl := (plan_law hCH a).2.2.1
  unfold eta
  generalize hp : plan hCH a = p at hl ⊢
  rcases p with ⟨θ, z⟩
  cases z with
  | none => exact show (0 : Ordinal.{0}) ≤ a.1.1 from bot_le
  | some z => exact eventIndex_le _ z _ hl

theorem selected_target (a : Stage) :
    (SignedOrdinalHistory.run hCH a).event.selected.treatment.row.1 =
      ord (eventRow hCH a) ∧
    (SignedOrdinalHistory.run hCH a).event.selected.treatment.label.1 =
      (oldTarget hCH (plan hCH a)).1 := by
  exact ⟨congrArg Prod.fst (plan_law hCH a).2.1,
    congrArg Prod.snd (plan_law hCH a).2.1⟩

private theorem measure_read (a : Stage) (n : ℕ) :
    (actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n =
      (wholeBirth hCH (eventRow hCH a)).measure (oldTarget hCH (plan hCH a)) n := by
  unfold eta eventRow
  generalize hp : plan hCH a = p
  rcases p with ⟨θ, z⟩
  cases z with
  | none =>
    have hd : decodeTag (wholeBirth hCH θ) zeroLabel = zeroTag (wholeBirth hCH θ) := by
      rw [← code_zero (wholeBirth hCH θ)]
      exact decode_code _ _
    change (wholeBirth hCH θ).measure (target _ (decodeTag _ zeroLabel)) n = _
    rw [hd]
    rfl
  | some z =>
    have hn := (event_read (wholeBirth hCH θ) (actualDelayedSupport hCH θ) z a.1).2
    dsimp only [planIndex, oldTarget]
    exact congrArg (fun μ : BornData (wholeBirth hCH θ).V => ((μ.1 n).1)) hn

/-- Every natural-index measure is the target of the same selected Result,
including self-row events and rejected tasks. -/
theorem selected_measure (a : Stage) (n : ℕ) :
    HEq ((actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n)
      ((SignedOrdinalHistory.run hCH a).event.Q.measure
        (SignedOrdinalHistory.run hCH a).event.selected.treatment.row
        (SignedOrdinalHistory.run hCH a).event.selected.treatment.label n) := by
  rw [measure_read]
  let θ := eventRow hCH a
  let d := oldTarget hCH (plan hCH a)
  have hr := (selected_target hCH a).1
  have hd := (selected_target hCH a).2
  have hdle : d.1 ≤ ord a := by
    rw [← hd]
    exact (SignedOrdinalHistory.run hCH a).event.selected.treatment.label.2
  have hrow : (SignedOrdinalHistory.run hCH a).event.selected.treatment.row =
      ⟨ord θ, θ.2, eventRow_le hCH a⟩ := Subtype.ext hr
  have hcol : (SignedOrdinalHistory.run hCH a).event.selected.treatment.label =
      ⟨d.1, hdle⟩ := Subtype.ext hd
  rw [hrow, hcol]
  change HEq ((wholeBirth hCH θ).measure d n) _
  by_cases he : θ = a
  · have hnew : (⟨ord θ, θ.2, eventRow_le hCH a⟩ : Rows (ord a)) =
        newRow (ord a) a.2 := Subtype.ext (congrArg ord he)
    rw [hnew]
    have he' : eventRow hCH a = a := he
    have hw : HEq ((wholeBirth hCH (eventRow hCH a)).measure d n)
        ((wholeBirth hCH a).measure d n) := by rw [he']
    exact hw.trans (whole_measure hCH a d n)
  · have hlt : θ < a := lt_of_le_of_ne (eventRow_le hCH a) he
    exact (prepared_measure_read hCH θ a hlt d hdle n).symm

private theorem plan_of_occurs (θ a : Stage) (z : Tag (wholeBirth hCH θ))
    (ha : Occurs (wholeBirth hCH θ) z a.1) :
    plan hCH a = ⟨θ, some z⟩ := by
  classical
  cases z with
  | inl d =>
    have he : (reservation a.1).1 = .inl (θ.1, d) := ha.1
    have hv : OrdinaryValid a.1 θ.1 d := ha.2
    simp only [plan, he, dite_eq_left hv]
  | inr p =>
    have he : (reservation a.1).1 = .inr (θ.1, p.1.1, p.1.2.1, p.1.2.2) := ha.1
    have hv := ha.2
    have hl := (actual_intrinsic hCH hv.2.1 p.1.1 p.1.2.1
      hv.2.2.1 hv.2.2.2 p.1.2.2).mpr p.2
    simp only [plan, he, dite_eq_left hl]

/-- Every new label is attained by actual selected events cofinally on every
row. Witnesses are strictly old-row events. -/
theorem actual_cofinal (θ : Stage) (δ base : Label) :
    ∃ a : Stage, base < a.1 ∧ θ < a ∧ eventRow hCH a = θ ∧ eta hCH a = δ := by
  obtain ⟨b, hb, z, hz, he⟩ :=
    eventIndex_cofinal (wholeBirth hCH θ) δ (max base θ.1)
  have hθ : θ.1 < b := (le_max_right base θ.1).trans_lt hb
  let a : Stage := ⟨b, θ.2.trans hθ.le⟩
  have hp : plan hCH a = ⟨θ, some z⟩ := plan_of_occurs hCH θ a z hz
  refine ⟨a, (le_max_left base θ.1).trans_lt hb, hθ, ?_, ?_⟩
  · exact congrArg Sigma.fst hp
  · change planIndex hCH a.1 (plan hCH a) = δ
    rw [hp]
    exact he

private theorem pack_U_heq {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (W : BirthPack C) (W' : BirthPack D) (hw : HEq W W') (d : Label) :
    HEq (W.U d) (W'.U d) := by
  subst D
  cases eq_of_heq hw
  rfl

private theorem support_mem_heq {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (U : SupportFamily C) (V : SupportFamily D) (hu : HEq U V)
    (n : ℕ) (x : C) (y : D) (hxy : x.1 = y.1) :
    x ∈ U.clopen n ↔ y ∈ V.clopen n := by
  subst D
  have he : x = y := Subtype.ext hxy
  subst y
  cases eq_of_heq hu
  rfl

private theorem whole_currentU (θ a : Stage) (ha : θ ≤ a) (d : Label) :
    HEq ((wholeBirth hCH θ).U d)
      (SignedOrdinalPredecessor.currentU (Q := (SignedOrdinalHistory.run hCH a).event.Q)
        ⟨ord θ, θ.2, ha⟩ d) := by
  classical
  by_cases he : θ = a
  · subst θ
    change HEq ((wholeBirth hCH a).U d)
      (SignedOrdinalPredecessor.currentU (Q := (SignedOrdinalHistory.run hCH a).event.Q)
        (newRow (ord a) a.2) d)
    unfold SignedOrdinalPredecessor.currentU
    rw [dite_eq_left rfl]
    exact pack_U_heq (top_read hCH a) _ _ (wholeBirth_read hCH a) d
  · have hlt : θ < a := lt_of_le_of_ne ha he
    let r := oldRow hlt (newRow (ord θ) θ.2)
    let hr := oldRow_ne hlt (newRow (ord θ) θ.2)
    have hp : HEq (wholeBirth hCH θ) ((SignedOrdinalHistory.run hCH a).oldBirth r hr) :=
      (wholeBirth_read hCH θ).trans
        ((heq_of_eq (SignedOrdinalHistory.coherent hCH θ a hlt).birth).trans
          (BirthPack.cast_heq _ _)).symm
    have hu := pack_U_heq (carrier_read hCH a (rowIndex r)) _ _ hp d
    change HEq ((wholeBirth hCH θ).U d)
      (SignedOrdinalPredecessor.currentU (Q := (SignedOrdinalHistory.run hCH a).event.Q) r d)
    unfold SignedOrdinalPredecessor.currentU
    rw [dite_eq_right hr]
    exact hu

private theorem prepared_launch {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    (Q : Prepared H ha P launch) (n : ℕ) :
    ((Q.V (newRow a ha)).clopen n : Set (K H)) =
      projection H launch.row ⁻¹'
        ((SignedOrdinalPredecessor.currentU (Q := Q) launch.row
          launch.supportIndex).clopen n : Set (Base H launch.row)) := by
  classical
  rcases launch with ⟨r, d⟩
  by_cases hr : r = newRow a ha
  · subst r
    have hh := congrArg (fun f : ℕ → Clopens (K H) => (f n : Set (K H))) Q.launch_eq
    simpa [SignedOrdinalPredecessor.currentU] using hh
  · have hh := congrArg (fun f : ℕ → Clopens (K H) => (f n : Set (K H))) Q.launch_eq
    simpa only [SignedOrdinalPredecessor.currentU, dite_eq_right hr, Clopens.coe_mk] using hh

private theorem original_launch (a θ : Stage) (hθ : θ ≤ a) (d : Label)
    (hex : CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False) = (θ.1, d))
    (n : ℕ) :
    ((wholeBirth hCH a).V.clopen n : Set ((finalPrefix hCH).Space a.1)) =
      (finalPrefix hCH).map θ.1 a.1 hθ ⁻¹'
        ((wholeBirth hCH θ).U d).clopen n := by
  classical
  let X := SignedOrdinalHistory.run hCH a
  let r : Rows (ord a) := ⟨ord θ, θ.2, hθ⟩
  have hrow : (scheduledLaunch X.H a.2 X.P).row = r := by
    apply Subtype.ext
    change (CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False)).1.1 = ord θ
    rw [hex]
  have hi : (scheduledLaunch X.H a.2 X.P).supportIndex = d := by
    change (CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False)).2 = d
    rw [hex]
  have hl : scheduledLaunch X.H a.2 X.P = ⟨r, d⟩ :=
    congrArg₂ (fun r d => (⟨r, d⟩ : Launch (ord a))) hrow hi
  have hq : (X.birth.V.clopen n : Set (K X.H)) =
      projection X.H r ⁻¹'
        ((SignedOrdinalPredecessor.currentU (Q := X.event.Q) r d).clopen n : Set (Base X.H r)) := by
    have hh := prepared_launch X.event.Q n
    exact hh.trans (congrArg (fun l : Launch (ord a) =>
      projection X.H l.row ⁻¹'
        ((SignedOrdinalPredecessor.currentU (Q := X.event.Q) l.row
          l.supportIndex).clopen n : Set (Base X.H l.row))) hl)
  have hv := BirthPack.heq_V (top_read hCH a) _ _ (wholeBirth_read hCH a)
  have hu := whole_currentU hCH θ a hθ d
  ext x
  let y : K X.H := Homeomorph.setCongr (top_read hCH a) x
  have hm := support_mem_heq (top_read hCH a) _ _ hv n x y rfl
  change x ∈ (wholeBirth hCH a).V.clopen n ↔ _
  rw [hm]
  change y ∈ (X.birth.V.clopen n : Set (K X.H)) ↔ _
  rw [hq]
  exact (support_mem_heq (carrier_read hCH a (rowIndex r)) _ _ hu n
    ((finalPrefix hCH).map θ.1 a.1 hθ x) (projection X.H r y) rfl).symm

private noncomputable def planSupport (p : Plan hCH) :
    SupportFamily ((finalPrefix hCH).Space p.1.1) :=
  match p with
  | ⟨θ, none⟩ => (wholeBirth hCH θ).U zeroLabel
  | ⟨θ, some (.inl d)⟩ => (wholeBirth hCH θ).U d
  | ⟨θ, some (.inr _)⟩ => actualDelayedSupport hCH θ

private theorem support_read (p : Plan hCH) (a : Label) :
    (actualBirth hCH p.1).U (planIndex hCH a p) = planSupport hCH p := by
  rcases p with ⟨θ, z⟩
  cases z with
  | none =>
    dsimp only [planIndex, planSupport]
    have hd : decodeTag (wholeBirth hCH θ) zeroLabel = zeroTag (wholeBirth hCH θ) := by
      rw [← code_zero (wholeBirth hCH θ)]
      exact decode_code _ _
    simp only [actualBirth, reindexBirth, hd, zeroTag]
  | some z =>
    dsimp only [planIndex, planSupport]
    cases z with
    | inl d => exact (event_read (wholeBirth hCH θ) (actualDelayedSupport hCH θ) (.inl d) a).1
    | inr q => exact (event_read (wholeBirth hCH θ) (actualDelayedSupport hCH θ) (.inr q) a).1

private theorem plan_launch (a : Stage) (p : Plan hCH) (hb : p.1 ≤ a)
    (hf : tagOccurs hCH a.1 p)
    (hl : CofinalTaskSchedule.execute a.1 (fun _ _ _ _ => False) = launchTarget hCH p)
    (n : ℕ) :
    ((wholeBirth hCH a).V.clopen n : Set ((finalPrefix hCH).Space a.1)) =
      (finalPrefix hCH).map p.1.1 a.1 hb ⁻¹'
        ((planSupport hCH p).clopen n : Set _) := by
  rcases p with ⟨θ, z⟩
  cases z with
  | none =>
    change θ = initialStage at hf
    subst θ
    exact original_launch hCH a initialStage a.2 zeroLabel hl n
  | some z =>
    cases z with
    | inl d => exact original_launch hCH a θ hb d hl n
    | inr q =>
      have hh := original_launch hCH a initialStage a.2 zeroLabel hl n
      rw [hh]
      ext x
      rfl

/-- Universal newborn launch with the same eta as the actual selected measure.
The equality includes self-row launches and every rejected reservation. -/
theorem universal_launch (a : Stage) (n : ℕ) :
    ((actualBirth hCH a).V.clopen n : Set ((finalPrefix hCH).Space a.1)) =
      (finalPrefix hCH).map (eventRow hCH a).1 a.1 (eventRow_le hCH a) ⁻¹'
        (((actualBirth hCH (eventRow hCH a)).U (eta hCH a)).clopen n : Set _) := by
  change ((wholeBirth hCH a).V.clopen n : Set _) =
    (finalPrefix hCH).map (plan hCH a).1.1 a.1 (eventRow_le hCH a) ⁻¹'
      (((actualBirth hCH (plan hCH a).1).U (planIndex hCH a.1 (plan hCH a))).clopen n : Set _)
  rw [support_read]
  exact plan_launch hCH a (plan hCH a) (eventRow_le hCH a)
    (plan_law hCH a).2.2.1 (plan_law hCH a).2.2.2 n

end D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex
