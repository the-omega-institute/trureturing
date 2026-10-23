import Reg.D5.S0.Rewriting.UniformNativeUnification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Rewriting.UniformNativeUnification
open Lambda Lambda.UniformNativeUnification NativeTermUnification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable def registration_exact_native :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UniformNativeUnification.exact_native)
      (type_of% (realize exactSignature (fun _ n E => F (n,liftEquations E)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UniformNativeUnification.unit_exact_native,
  realizationName := `Reg.D5.S0.Rewriting.UniformNativeUnification.exactEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨exactArena⟩,
  objectArena := .source ⟨exactArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source exactArena ⟨exactEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize exactSignature (fun _ n E => F (n,liftEquations E)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UniformNativeUnificationDomain,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_rejection_exact :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UniformNativeUnification.rejection_exact)
      (type_of% (realize rejectSignature (fun _ n E => F (n,E)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UniformNativeUnification.unit_rejection_exact,
  realizationName := `Reg.D5.S0.Rewriting.UniformNativeUnification.rejectEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rejectArena⟩,
  objectArena := .source ⟨rejectArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rejectArena ⟨rejectEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rejectSignature (fun _ n E => F (n,E)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UniformNativeUnificationDomain,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

abbrev rangeSignature : Signature where
  Params := Nat
  State _ := TermN
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def rangeActual : Realization rangeSignature := realize rangeSignature
  (fun _ n t => (lowerTerm n t).isSome) (fun e => nomatch e)
def rangeRejected : Realization rangeSignature := realize rangeSignature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev rangeArena : Arena where
  signature := rangeSignature
  Law R := ∀ n (t : TermN), R.readout () n t = inRange n t

private theorem range_rejected_law : ¬ rangeArena.Law rangeRejected := by
  intro h
  have bad := h 0 (.of (.inl false))
  cases bad

def rangeEvidence : Registration rangeArena
    (type_of% (@Lambda.UniformNativeUnification.lower_range)) where
  actual := rangeActual
  bridge := Iff.rfl
  variation := ⟨lower_range,rangeRejected,range_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rangeRejected,?_,rfl,range_rejected_law⟩
      intro j ne; exact (ne (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨0,.of (.inl false),.of (.inr 0),?_⟩
    change (lowerTerm 0 (.of (.inl false))).isSome ≠
      (lowerTerm 0 (.of (.inr 0))).isSome
    simp [lowerTerm]

abbrev equationsRangeSignature : Signature where
  Params := Nat
  State _ := Equations Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def equationsRangeActual : Realization equationsRangeSignature := realize equationsRangeSignature
  (fun _ n E => (lowerEquations n E).isSome) (fun e => nomatch e)
def equationsRangeRejected : Realization equationsRangeSignature := realize equationsRangeSignature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev equationsRangeArena : Arena where
  signature := equationsRangeSignature
  Law R := ∀ n (E : Equations Nat), R.readout () n E =
    E.all (fun e => inRange n e.1 && inRange n e.2)

private theorem equations_range_rejected_law : ¬ equationsRangeArena.Law equationsRangeRejected := by
  intro h
  have bad := h 0 []
  cases bad

def equationsRangeEvidence : Registration equationsRangeArena
    (type_of% (@Lambda.UniformNativeUnification.lower_equations_range)) where
  actual := equationsRangeActual
  bridge := Iff.rfl
  variation := ⟨lower_equations_range,equationsRangeRejected,equations_range_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equationsRangeRejected,?_,rfl,equations_range_rejected_law⟩
      intro j ne; exact (ne (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨0,[],[(.of (.inr 0),.of (.inr 0))],?_⟩
    change (lowerEquations 0 []).isSome ≠
      (lowerEquations 0 [(.of (.inr 0),.of (.inr 0))]).isSome
    simp [lowerEquations, lowerTerm]

noncomputable def registration_lower_range :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UniformNativeUnification.lower_range)
      (type_of% (realize rangeSignature (fun _ n t => (lowerTerm n t).isSome) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UniformNativeUnification.unit_lower_range,
  realizationName := `Reg.D5.S0.Rewriting.UniformNativeUnification.rangeEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rangeArena⟩,
  objectArena := .source ⟨rangeArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rangeArena ⟨rangeEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rangeSignature (fun _ n t => (lowerTerm n t).isSome) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UniformNativeUnificationDomain,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_lower_equations_range :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UniformNativeUnification.lower_equations_range)
      (type_of% (realize equationsRangeSignature (fun _ n E => (lowerEquations n E).isSome) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UniformNativeUnification.unit_lower_equations_range,
  realizationName := `Reg.D5.S0.Rewriting.UniformNativeUnification.equationsRangeEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨equationsRangeArena⟩,
  objectArena := .source ⟨equationsRangeArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source equationsRangeArena ⟨equationsRangeEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize equationsRangeSignature (fun _ n E => (lowerEquations n E).isSome) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UniformNativeUnificationDomain,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.UniformNativeUnification
