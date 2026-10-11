import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.WholePathProjection
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open Set

namespace Reg.D5.S1.Dynamics.Shadowing.WholePathProjection

noncomputable section
universe u v

abbrev prefixSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ _ m => m) (fun e => nomatch e)

def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the entire original telescope; intervene only on the prefix's
time endpoint in the original right-hand side. -/
abbrev prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ {H : Type u} {P : Type v} [Finite H]
    (eH : H → H → Prop) (eP : P → P → Prop) (q : H → P)
    (_hq : ∀ h h', eH h h' → eP (q h) (q h')),
    graphLanguage eH q = graphLanguage eP id ↔
      ∀ a ∈ graphLanguage eP id, ∀ m,
        PrefixLift eH q a (R.readout () () m)

private abbrev hidden := ULift.{u} (Bool × Bool)
private abbrev visible := ULift.{v} Bool
private def hiddenEdge (h h' : hidden.{u}) : Prop :=
  h'.down.1 = h.down.2 ∧ h'.down.2 = h.down.2
private def visibleEdge (_ _ : visible.{v}) : Prop := True
private def projection (h : hidden.{u}) : visible.{v} := ⟨h.down.1⟩
private def badWord (n : ℕ) : visible.{v} := ⟨if n = 1 then true else false⟩

/-- Every visible vertex and edge has a hidden preimage, and every hidden
vertex is live. A hidden visible history is constant after its first edge. -/
private theorem projection_edge_onto (v w : visible.{v}) :
    ∃ h h' : hidden.{u}, projection h = v ∧ projection h' = w ∧ hiddenEdge h h' := by
  exact ⟨⟨(v.down, w.down)⟩, ⟨(w.down, w.down)⟩, by cases v; rfl,
    by cases w; rfl, rfl, rfl⟩

private theorem visible_word : badWord.{v} ∈ graphLanguage visibleEdge id :=
  ⟨badWord, fun _ => trivial, fun _ => rfl⟩

private theorem no_whole_lift : badWord.{v} ∉ graphLanguage hiddenEdge projection.{u,v} := by
  rintro ⟨b, hb, hl⟩
  have he : (b 1).down.1 = (b 2).down.1 :=
    (hb 0).1.trans ((hb 0).2.symm.trans (hb 1).1.symm)
  have h1 := congrArg ULift.down (hl 1)
  have h2 := congrArg ULift.down (hl 2)
  change (b 1).down.1 = true at h1
  change (b 2).down.1 = false at h2
  rw [h1, h2] at he
  contradiction

private theorem projection_notonto :
    graphLanguage hiddenEdge projection.{u,v} ≠ graphLanguage visibleEdge id := by
  intro heq
  exact no_whole_lift (heq ▸ visible_word)

private theorem all_zero_prefixes (a : ℕ → visible.{v}) :
    PrefixLift hiddenEdge projection.{u,v} a 0 := by
  obtain ⟨h, _, hh, _, _⟩ := projection_edge_onto.{u,v} (a 0) (a 0)
  exact ⟨fun _ => h, (fun i => Fin.elim0 i), fun i => by
    simpa only [Fin.val_eq_zero] using hh⟩

private theorem prefixRejected_law : ¬ prefixArena.{u,v}.Law prefixRejected := by
  intro h
  have hh := h hiddenEdge visibleEdge projection (fun _ _ _ => trivial)
  apply projection_notonto.{u,v}
  exact hh.2 (fun a _ _ => all_zero_prefixes a)

def prefixRegistration : Registration prefixArena.{u,v}
    (type_of% (@graphLanguage_eq_iff_prefix_lifts.{u,v})) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨@graphLanguage_eq_iff_prefix_lifts.{u,v}, prefixRejected, prefixRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected, ?_, rfl, prefixRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

abbrev boundSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature :=
  realize boundSignature (fun _ m k => decide (m ≤ k)) (fun e => nomatch e)

def boundRejected : Realization boundSignature :=
  realize boundSignature (fun _ _ _ => false) (fun e => nomatch e)

/-- The bound comparison is reified at its exact original source occurrence.
All graph, finite-type, live-target and nononto hypotheses remain universal. -/
abbrev boundArena : Arena where
  signature := boundSignature
  Law R := ∀ {H : Type u} {P : Type v} [Fintype P] [Fintype H]
    (eH : H → H → Prop) (eP : P → P → Prop) (q : H → P)
    (_hq : ∀ h h', eH h h' → eP (q h) (q h'))
    (_hP : ∀ v : P, ∃ a ∈ graphLanguage eP id, a 0 = v)
    (_hnot : graphLanguage eH q ≠ graphLanguage eP id),
    ∃ a ∈ graphLanguage eP id, ∃ m : ℕ,
      R.readout () m (Fintype.card P * 2 ^ Fintype.card H) = true ∧
      ¬ PrefixLift eH q a m

private theorem boundActual_law : boundArena.{u,v}.Law boundActual := by
  simpa only [boundArena, boundActual, realize, decide_eq_true_eq] using
    (@exists_bounded_prefix_without_lift.{u,v})

private theorem boundRejected_law : ¬ boundArena.{u,v}.Law boundRejected := by
  intro h
  have hP : ∀ v : visible.{v}, ∃ a ∈ graphLanguage visibleEdge id, a 0 = v := by
    intro v
    exact ⟨fun _ => v, ⟨fun _ => v, fun _ => trivial, fun _ => rfl⟩, rfl⟩
  obtain ⟨a, _, m, hm, _⟩ := h hiddenEdge visibleEdge projection
    (fun _ _ _ => trivial) hP projection_notonto.{u,v}
  contradiction

def boundRegistration : Registration boundArena.{u,v}
    (type_of% (@exists_bounded_prefix_without_lift.{u,v})) where
  actual := boundActual
  bridge := by simp only [boundActual, realize, decide_eq_true_eq]
  variation := ⟨boundActual_law, boundRejected, boundRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundRejected, ?_, rfl, boundRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨1, 0, 1, by change (false : Bool) ≠ true; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@graphLanguage_eq_iff_prefix_lifts.{u,v}) (Realization prefixSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.WholePathProjection.prefixCriterion
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.WholePathProjection.prefixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena.{u,v}⟩
  objectArena := .source ⟨prefixArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena.{u,v} ⟨prefixRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize prefixSignature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.WholePathProjection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "arg","body","body","body","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_bounded_prefix_without_lift.{u,v}) (Realization boundSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.WholePathProjection.boundedFailure
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.WholePathProjection.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena.{u,v}⟩
  objectArena := .source ⟨boundArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena.{u,v} ⟨boundRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ m k => decide (m ≤ k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.WholePathProjection
    definition := none
    coordinates := #[11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","body","arg","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms prefixRegistration
#print axioms registration_1
#print axioms boundRegistration
#print axioms registration_2

end
end Reg.D5.S1.Dynamics.Shadowing.WholePathProjection
