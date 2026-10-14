import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v

namespace Reg.D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
open _root_.D5.S3.ConceptDynamics.Coding.MarkerPermutationAction.Guarded
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters :=
  Σ E : Type u, Σ I : Type v, Σ m : ℕ, Σ d : ℕ,
    Σ _ : Words E I m d, Equiv.Perm I

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := ℤ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p x => replace p.2.2.2.2.1 p.2.2.2.2.2 x)
    (fun e => nomatch e)

/-- A genuine intervention replaces the observed replacement sequence by its unit shift. -/
def translated : Realization signature.{u,v} :=
  realize signature (fun _ _ x t => x (t + 1)) (fun e => nomatch e)

/-- The original telescope and both occurrence clauses remain intact. -/
def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {E : Type u} {I : Type v} {m d : ℕ}
    (W : Words E I m d) (pi : Equiv.Perm I) (x : ℤ → E) (a : ℤ),
    Occurs W (R.readout () ⟨E, I, m, d, W, pi⟩ x) a ↔ Occurs W x a

theorem actual_law : arena.{u,v}.Law actual :=
  @marker_occurrences_invariant.{u,v}

theorem statement_bridge :
    (type_of% (@marker_occurrences_invariant.{u,v})) ↔ arena.{u,v}.Law actual :=
  Iff.rfl

/-- This is an intervention witness in the full family, not a Reset-history model. -/
private def singleEdgeWords : Words (ULift.{u} Bool) (ULift.{v} Unit) 1 0 where
  marker _ := ⟨false⟩
  data _ j := nomatch j
  marker_pos := by decide
  data_short := by decide
  marker_unbordered := by intro r hr hrm; omega
  data_injective := by intro i j _; exact Subsingleton.elim i j

theorem translated_rejected : ¬ arena.{u,v}.Law translated := by
  intro h
  let x : ℤ → ULift.{u} Bool := fun t => ⟨decide (t = 1)⟩
  have before : Occurs singleEdgeWords.{u,v} x 0 := by
    intro j
    have hj : j.val = 0 := by omega
    simp [x, singleEdgeWords, hj]
  have after := (h singleEdgeWords 1 x 0).mpr before
  have bad := after (0 : Fin 1)
  change (⟨decide ((0 : ℤ) + 1 = 1)⟩ : ULift.{u} Bool) = ⟨false⟩ at bad
  simp at bad

theorem variation : Variation arena.{u,v} actual :=
  ⟨actual_law, translated, translated_rejected⟩

theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    change Unit at i
    cases i
    refine ⟨translated, ?_, rfl, translated_rejected⟩
    intro j hj
    change Unit at j
    cases j
    exact (hj rfl).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : Parameters.{u,v} :=
    ⟨ULift.{u} Bool, ULift.{v} Unit, 1, 0, singleEdgeWords, 1⟩
  let x : ℤ → ULift.{u} Bool := fun _ => ⟨false⟩
  let y : ℤ → ULift.{u} Bool := fun _ => ⟨true⟩
  refine ⟨p, x, y, ?_⟩
  intro he
  have he' : replace singleEdgeWords 1 x = replace singleEdgeWords 1 y := he
  have hx := (replace_inverse singleEdgeWords 1 x).1
  have hy := (replace_inverse singleEdgeWords 1 y).1
  have hxy : x = y := hx.symm.trans ((congrArg
    (replace singleEdgeWords (1 : Equiv.Perm (ULift.{v} Unit))⁻¹) he').trans hy)
  have bad := congrArg (fun z : ℤ → ULift.{u} Bool => (z 0).down) hxy
  change false = true at bad
  cases bad

def registration : Registration arena.{u,v}
    (type_of% (@marker_occurrences_invariant.{u,v})) where
  actual := actual
  bridge := statement_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def sourceSelection : Contract.SourceSelection where
  owner := `D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
  definition := none
  coordinates := #[0, 1, 2, 3, 4, 5]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "fn", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def source : Analysis.Source (@marker_occurrences_invariant.{u,v}) where
  signature := signature
  actual := actual
  rebuild := arena.Law
  reconstruction := .exact
  selection := sourceSelection

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@marker_occurrences_invariant.{u,v})
    (type_of% (realize signature.{u,v}
      (fun _ p x => replace p.2.2.2.2.1 p.2.2.2.2.2 x) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Coding.MarkerPermutationAction.Guarded.marker_occurrences_invariant.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.MarkerPermutationAction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v}
    (fun _ p x => replace p.2.2.2.2.1 p.2.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some sourceSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms source
#print axioms audit

end Reg.D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
