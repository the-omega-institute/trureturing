import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
import Reg.Support.DependentFamily
import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.Functor.Const

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set Function
open _root_.D5.S1.Dynamics.Shadowing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology unitInterval

noncomputable section
namespace Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
universe u v w
attribute [local instance] Classical.propDecidable

private theorem cover_of_points {X : Type w} [TopologicalSpace X]
    (C : Finset (Opens X)) (h : ∀ x, ∃ U ∈ C, x ∈ U) :
    IsOpenCover (fun U : C => U.1) := by
  rw [IsOpenCover, eq_top_iff]
  intro x _
  obtain ⟨U, hU, hx⟩ := h x
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

private theorem constant_hasShadowing {X : Type w} [TopologicalSpace X] (c : X) :
    HasShadowing (fun _ : X => c) := by
  intro C hC
  refine ⟨C, hC, fun x hx => ⟨x 0, ?_⟩⟩
  intro n
  cases n with
  | zero =>
      obtain ⟨U, hxU⟩ := hC.exists_mem (x 0)
      exact ⟨U.1, U.2, hxU, hxU⟩
  | succ n =>
      simpa only [iterate_succ_apply'] using hx n

/-- A discontinuous jump is a genuine rejected dynamics on a space containing
the interval. The counterexample is used only for variation, never to restrict
the universally quantified source law. -/
private def jump {X : Type w} (q : X → ℝ) (s : I → X) (x : X) : X :=
  if q x = 0 then s 0 else s 1

private theorem jump_not_hasShadowing {X : Type w} [TopologicalSpace X]
    (q : X → ℝ) (hq : Continuous q) (s : I → X) (hs : Continuous s)
    (hqs : ∀ a, q (s a) = (a : ℝ)) : ¬ HasShadowing (jump q s) := by
  classical
  let U : Opens X := ⟨q ⁻¹' Iio (1 / 2), isOpen_Iio.preimage hq⟩
  let V : Opens X := ⟨q ⁻¹' Ioi (1 / 4), isOpen_Ioi.preimage hq⟩
  let C : Finset (Opens X) := {U, V}
  have hC : IsOpenCover (fun W : C => W.1) := by
    apply cover_of_points
    intro x
    by_cases h : q x < 1 / 2
    · exact ⟨U, by simp [C], h⟩
    · exact ⟨V, by simp [C], by change 1 / 4 < q x; linarith⟩
  intro h
  obtain ⟨D, hD, htrace⟩ := h C hC
  obtain ⟨W, hzW⟩ := hD.exists_mem (s 0)
  have ho : IsOpen (s ⁻¹' (W.1 : Set X)) := W.1.isOpen.preimage hs
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hzW)
  let aR : ℝ := min (ε / 2) (1 / 8)
  have ha0 : 0 < aR := lt_min (by linarith) (by norm_num)
  have ha8 : aR ≤ 1 / 8 := min_le_right _ _
  have haε : aR < ε := (min_le_left _ _).trans_lt (by linarith)
  let a : I := ⟨aR, le_of_lt ha0, by linarith⟩
  have haW : s a ∈ W.1 := hb (by
    change dist a (0 : I) < ε
    change |aR - 0| < ε
    simpa only [sub_zero, abs_of_pos ha0] using haε)
  have hj0 : jump q s (s 0) = s 0 := by simp [jump, hqs]
  have hj1 : jump q s (s 1) = s 1 := by simp [jump, hqs]
  have hja : jump q s (s a) = s 1 := by
    change (if q (s a) = 0 then s 0 else s 1) = s 1
    rw [hqs]
    exact if_neg (ne_of_gt ha0)
  let x : ℕ → X := fun n => if n = 0 then s 0 else if n = 1 then s a else s 1
  have hx : PseudoOrbit (jump q s) D x := by
    intro n
    by_cases h0 : n = 0
    · subst n
      exact ⟨W.1, W.2, by simpa [x, hj0] using hzW, by simpa [x] using haW⟩
    · have hnext : n + 1 ≠ 0 ∧ n + 1 ≠ 1 := by omega
      have he : jump q s (x n) = s 1 := by
        by_cases h1 : n = 1
        · simpa [x, h0, h1] using hja
        · simpa [x, h0, h1] using hj1
      obtain ⟨T, hT⟩ := hD.exists_mem (s 1)
      exact ⟨T.1, T.2, by simpa [he] using hT,
        by simpa [x, h0] using hT⟩
  obtain ⟨z, hz⟩ := htrace x hx
  obtain ⟨T, hT, hf, ha⟩ := hz 1
  have hqfz : q (jump q s z) < 1 / 2 := by
    have ht : T = U ∨ T = V := by simpa [C] using hT
    rcases ht with rfl | rfl
    · exact hf
    · have ht : 1 / 4 < aR := by simpa [x, V, hqs] using ha
      linarith
  have hqz : q z = 0 := by
    by_contra hn
    have he : q (jump q s z) = 1 := by simp [jump, hn, hqs]
    linarith
  have hjz : jump q s z = s 0 := by simp [jump, hqz]
  obtain ⟨T, hT, hzero, hone⟩ := hz 2
  have ht : T = U ∨ T = V := by simpa [C] using hT
  rcases ht with rfl | rfl
  · have hh : (1 : ℝ) < 1 / 2 := by simpa [x, U, hqs] using hone
    norm_num at hh
  · have hh : (1 / 4 : ℝ) < 0 := by
      simpa [iterate_succ_apply', hjz, hj0, V, hqs] using hzero
    norm_num at hh

/-- Universes are lifted so the witness exists for every original u,v. -/
private abbrev WitnessIndex := Discrete PUnit.{u + 1}
private abbrev WitnessSpace := ULift.{max u v} I
private abbrev witnessDiagram : WitnessIndex.{u} ⥤ TopCat.{max u v} :=
  (Functor.const WitnessIndex.{u}).obj (TopCat.of WitnessSpace.{u, v})
private def witnessThread (a : I) : (TopCat.limitCone witnessDiagram.{u, v}).pt :=
  ⟨fun _ => ⟨a⟩, fun {_ _} _ => rfl⟩
private def witnessCoordinate (x : (TopCat.limitCone witnessDiagram.{u, v}).pt) : ℝ :=
  ((x.1 ⟨PUnit.unit⟩).down : ℝ)
private theorem witnessThread_continuous : Continuous witnessThread.{u, v} :=
  (continuous_pi fun _ => continuous_uliftUp).subtype_mk _
private theorem witnessCoordinate_continuous : Continuous witnessCoordinate.{u, v} :=
  continuous_subtype_val.comp (continuous_uliftDown.comp
    ((continuous_apply _).comp continuous_subtype_val))
private def witnessDynamics : witnessDiagram.{u, v} ⟶ witnessDiagram.{u, v} where
  app _ := TopCat.const ⟨(0 : I)⟩
  naturality := by intro i j f; ext x; rfl

private instance witness_compact : ∀ j, CompactSpace (witnessDiagram.{u, v}.obj j) :=
  fun _ => (show CompactSpace WitnessSpace.{u, v} from inferInstance)
private instance witness_t2 : ∀ j, T2Space (witnessDiagram.{u, v}.obj j) :=
  fun _ => (show T2Space WitnessSpace.{u, v} from inferInstance)
private instance witness_nonempty : ∀ j, Nonempty (witnessDiagram.{u, v}.obj j) :=
  fun _ => (show Nonempty WitnessSpace.{u, v} from inferInstance)

abbrev dynamicsParameters := Σ J : Type u, Σ C : SmallCategory J,
  letI := C
  Σ F : J ⥤ TopCat.{max u v}, F ⟶ F

abbrev dynamicsSignature : Signature where
  Params := dynamicsParameters.{u, v}
  State p := letI := p.2.1; (TopCat.limitCone p.2.2.1).pt
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; (TopCat.limitCone p.2.2.1).pt
  Anchor := Empty
  finiteAnchor := inferInstance

def dynamicsActual : Realization dynamicsSignature.{u, v} :=
  realize dynamicsSignature (fun _ p x =>
    letI := p.2.1
    limitDynamics p.2.2.1 p.2.2.2 x) (fun e => nomatch e)

def dynamicsRejected : Realization dynamicsSignature.{u, v} :=
  realize dynamicsSignature (fun _ p x =>
    letI := p.2.1
    if h : ∃ f : (TopCat.limitCone p.2.2.1).pt → (TopCat.limitCone p.2.2.1).pt,
        ¬ HasShadowing f then h.choose x else limitDynamics p.2.2.1 p.2.2.2 x)
    (fun e => nomatch e)

/-- The entire original theorem telescope is kept. Only the terminal dynamics
function operand is observed; no compactness, ML or shadowing hypothesis moves
into a restricted parameter fiber. -/
abbrev dynamicsArena : Arena where
  signature := dynamicsSignature.{u, v}
  Law R := ∀ {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{max u v})
    [IsCofiltered J] [Quiver.IsThin J]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (d : F ⟶ F) (_hML : (F ⋙ forget TopCat).IsMittagLeffler)
    (_hshadow : ∀ j, HasShadowing (d.app j)),
      HasShadowing (fun x => R.readout () ⟨J, inferInstance, F, d⟩ x)

theorem dynamicsActual_law : dynamicsArena.{u, v}.Law dynamicsActual := by
  intro J _ F _ _ _ _ d hML hshadow
  exact shadowing_inverse_limit_of_mittag_leffler F d hML hshadow

theorem dynamicsRejected_law : ¬ dynamicsArena.{u, v}.Law dynamicsRejected := by
  intro h
  have hML : (witnessDiagram.{u, v} ⋙ forget TopCat).IsMittagLeffler := by
    apply Functor.isMittagLeffler_of_surjective
    intro i j f
    exact fun a => ⟨a, rfl⟩
  have hstage : ∀ j, HasShadowing (witnessDynamics.{u, v}.app j) :=
    fun _ => constant_hasShadowing _
  have hbad : ∃ f : (TopCat.limitCone witnessDiagram.{u, v}).pt →
      (TopCat.limitCone witnessDiagram.{u, v}).pt, ¬ HasShadowing f :=
    ⟨jump witnessCoordinate witnessThread,
      jump_not_hasShadowing _ witnessCoordinate_continuous _ witnessThread_continuous
        (fun _ => rfl)⟩
  have hh := h witnessDiagram.{u, v} witnessDynamics hML hstage
  change HasShadowing (fun x => if ht : ∃ f : (TopCat.limitCone witnessDiagram.{u, v}).pt →
      (TopCat.limitCone witnessDiagram.{u, v}).pt, ¬ HasShadowing f
    then ht.choose x else limitDynamics witnessDiagram witnessDynamics x) at hh
  simp only [dif_pos hbad] at hh
  exact hbad.choose_spec hh

def dynamicsRegistration : Registration dynamicsArena.{u, v}
    (type_of% @shadowing_inverse_limit_of_mittag_leffler.{u, v}) where
  actual := dynamicsActual
  bridge := Iff.rfl
  variation := ⟨dynamicsActual_law, dynamicsRejected, dynamicsRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨dynamicsRejected, ?_, rfl, dynamicsRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨WitnessIndex.{u}, inferInstance, witnessDiagram.{u, v}, 𝟙 _⟩,
      witnessThread 0, witnessThread 1, ?_⟩
    intro he
    have hc := congrArg witnessCoordinate he
    change (0 : ℝ) = 1 at hc
    norm_num at hc

abbrev projectionParameters := Σ J : Type u, Σ C : SmallCategory J,
  letI := C
  Σ _F : J ⥤ TopCat.{max u v}, J

abbrev projectionSignature : Signature where
  Params := projectionParameters.{u, v}
  State p := letI := p.2.1; (TopCat.limitCone p.2.2.1).pt
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; p.2.2.1.obj p.2.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature.{u, v} :=
  realize projectionSignature (fun _ p x => x.1 p.2.2.2) (fun e => nomatch e)

def projectionRejected : Realization projectionSignature.{u, v} :=
  realize projectionSignature (fun _ p x =>
    letI := p.2.1
    if h : Nonempty (TopCat.limitCone p.2.2.1).pt then
      (Classical.choice h).1 p.2.2.2 else x.1 p.2.2.2) (fun e => nomatch e)

abbrev imageArena : Arena where
  signature := projectionSignature.{u, v}
  Law R := ∀ {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{max u v})
    [IsCofiltered J] [Quiver.IsThin J] [∀ j, Nonempty (F.obj j)]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] (i : J),
      range (fun x => R.readout () ⟨J, inferInstance, F, i⟩ x) =
        (F ⋙ forget TopCat).eventualRange i

theorem projectionActual_image_law : imageArena.{u, v}.Law projectionActual := by
  intro J _ F _ _ _ _ _ i
  exact compact_projection_image F i

theorem projectionRejected_image_law : ¬ imageArena.{u, v}.Law projectionRejected := by
  intro h
  let i : WitnessIndex.{u} := ⟨PUnit.unit⟩
  have he := h witnessDiagram.{u, v} i
  have h0 : (ULift.up (0 : I) : WitnessSpace.{u, v}) ∈
      (witnessDiagram ⋙ forget TopCat).eventualRange i := by
    apply (Functor.mem_eventualRange_iff _).2
    intro j f
    exact ⟨⟨0⟩, rfl⟩
  have h1 : (ULift.up (1 : I) : WitnessSpace.{u, v}) ∈
      (witnessDiagram ⋙ forget TopCat).eventualRange i := by
    apply (Functor.mem_eventualRange_iff _).2
    intro j f
    exact ⟨⟨1⟩, rfl⟩
  rw [← he] at h0 h1
  obtain ⟨x, hx⟩ := h0
  obtain ⟨y, hy⟩ := h1
  have hne : Nonempty (TopCat.limitCone witnessDiagram.{u, v}).pt := ⟨witnessThread 0⟩
  change (if ht : Nonempty (TopCat.limitCone witnessDiagram.{u, v}).pt then
    (Classical.choice ht).1 i else x.1 i) = ULift.up (0 : I) at hx
  change (if ht : Nonempty (TopCat.limitCone witnessDiagram.{u, v}).pt then
    (Classical.choice ht).1 i else y.1 i) = ULift.up (1 : I) at hy
  simp only [dif_pos hne] at hx hy
  have hh := congrArg (fun a : WitnessSpace.{u, v} => (a.down : ℝ)) (hx.symm.trans hy)
  norm_num at hh

def imageRegistration : Registration imageArena.{u, v}
    (type_of% @compact_projection_image.{u, v}) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨projectionActual_image_law, projectionRejected, projectionRejected_image_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨projectionRejected, ?_, rfl, projectionRejected_image_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨WitnessIndex.{u}, inferInstance, witnessDiagram.{u, v}, ⟨PUnit.unit⟩⟩,
      witnessThread 0, witnessThread 1, ?_⟩
    intro he
    have hc := congrArg (fun a : WitnessSpace.{u, v} => (a.down : ℝ)) he
    change (0 : ℝ) = 1 at hc
    norm_num at hc

abbrev descentArena : Arena where
  signature := projectionSignature.{u, v}
  Law R := ∀ {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{max u v})
    [IsCofiltered J] [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (C : Finset (Opens (TopCat.limitCone F).pt))
    (_hC : IsOpenCover (fun U : C => U.1)),
    ∃ (i : J) (V : Finset (Opens (F.obj i))),
      (∀ a ∈ range ((TopCat.limitCone F).π.app i), ∃ U ∈ V, a ∈ U) ∧
      (∀ U ∈ V, ∃ W ∈ C,
        (fun x => R.readout () ⟨J, inferInstance, F, i⟩ x) ⁻¹' (U : Set (F.obj i)) ⊆
          (W : Set (TopCat.limitCone F).pt))

theorem projectionActual_descent_law : descentArena.{u, v}.Law projectionActual := by
  intro J _ F _ _ _ C hC
  exact finite_cover_descent F C hC

theorem projectionRejected_descent_law : ¬ descentArena.{u, v}.Law projectionRejected := by
  classical
  intro h
  let U : Opens (TopCat.limitCone witnessDiagram.{u, v}).pt :=
    ⟨witnessCoordinate ⁻¹' Iio (1 / 2), isOpen_Iio.preimage witnessCoordinate_continuous⟩
  let V : Opens (TopCat.limitCone witnessDiagram.{u, v}).pt :=
    ⟨witnessCoordinate ⁻¹' Ioi (1 / 4), isOpen_Ioi.preimage witnessCoordinate_continuous⟩
  let C : Finset (Opens (TopCat.limitCone witnessDiagram.{u, v}).pt) := {U, V}
  have hC : IsOpenCover (fun W : C => W.1) := by
    apply cover_of_points
    intro x
    by_cases hx : witnessCoordinate x < 1 / 2
    · exact ⟨U, by simp [C], hx⟩
    · exact ⟨V, by simp [C], by change 1 / 4 < witnessCoordinate x; linarith⟩
  obtain ⟨i, B, hB, hBC⟩ := h witnessDiagram.{u, v} C hC
  have hne : Nonempty (TopCat.limitCone witnessDiagram.{u, v}).pt := ⟨witnessThread 0⟩
  let z := Classical.choice hne
  obtain ⟨A, hA, hzA⟩ := hB (z.1 i) ⟨z, rfl⟩
  obtain ⟨W, hW, hAW⟩ := hBC A hA
  have hwhole : ∀ x, x ∈ W := by
    intro x
    apply hAW
    change (if ht : Nonempty (TopCat.limitCone witnessDiagram.{u, v}).pt then
      (Classical.choice ht).1 i else x.1 i) ∈ A
    simpa only [dif_pos hne] using hzA
  have hw : W = U ∨ W = V := by simpa [C] using hW
  rcases hw with rfl | rfl
  · have hh : (1 : ℝ) < 1 / 2 := hwhole (witnessThread 1)
    norm_num at hh
  · have hh : (1 / 4 : ℝ) < 0 := hwhole (witnessThread 0)
    norm_num at hh

def descentRegistration : Registration descentArena.{u, v}
    (type_of% @finite_cover_descent.{u, v}) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨projectionActual_descent_law, projectionRejected, projectionRejected_descent_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨projectionRejected, ?_, rfl, projectionRejected_descent_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := imageRegistration.dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{
    max u v + 1,0,1,0,0,0,max u v + 1,max u v,0,max u v,0,0}
    (@compact_projection_image.{u, v}) (Realization projectionSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.projectionImage
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.imageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena.{u, v}⟩
  objectArena := .source ⟨imageArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena.{u, v} ⟨imageRegistration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ p x => x.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
    definition := none
    coordinates := #[0, 2, 8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{
    max u v + 1,0,1,0,0,0,max u v + 1,max u v,0,max u v,0,0}
    (@finite_cover_descent.{u, v}) (Realization projectionSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.coverDescent
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.descentRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨descentArena.{u, v}⟩
  objectArena := .source ⟨descentArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source descentArena.{u, v} ⟨descentRegistration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ p x => x.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
    definition := none
    coordinates := #[0, 2, 8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","body","arg","body","arg",
        "fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{
    max u v + 1,0,1,0,0,0,max u v + 1,max u v,0,max u v,0,0}
    (@shadowing_inverse_limit_of_mittag_leffler.{u, v})
    (Realization dynamicsSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.shadowing
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit.dynamicsRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨dynamicsArena.{u, v}⟩
  objectArena := .source ⟨dynamicsArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dynamicsArena.{u, v} ⟨dynamicsRegistration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dynamicsSignature (fun _ p x =>
    letI := p.2.1
    limitDynamics p.2.2.1 p.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
    definition := none
    coordinates := #[0, 2, 7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms dynamicsRegistration
#print axioms registration_3
#print axioms imageRegistration
#print axioms registration_1
#print axioms descentRegistration
#print axioms registration_2
end Reg.D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
