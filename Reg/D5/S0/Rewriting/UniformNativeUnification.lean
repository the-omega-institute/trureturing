import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.UniformNativeUnification
import Reg.Support.DependentFamily
import Mathlib.Computability.Halting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Rewriting.UniformNativeUnification
open Lambda Lambda.UniformNativeUnification NativeTermUnification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev solverSignature : Signature where
  Params := Unit
  State _ := SolverInput
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := SolverOutput
  Anchor := Empty
  finiteAnchor := inferInstance

def computableActual : Realization solverSignature := realize solverSignature
  (fun _ _ input => F input) (fun e => nomatch e)

noncomputable def undecidableOutput (input : SolverInput) : SolverOutput := by
  classical
  exact if ((Denumerable.ofNat Nat.Partrec.Code input.1).eval 0).Dom then none else some none

noncomputable def computableRejected : Realization solverSignature := realize solverSignature
  (fun _ _ input => undecidableOutput input) (fun e => nomatch e)

abbrev computableArena : Arena where
  signature := solverSignature
  Law R := Computable (fun input => R.readout () () input)

private theorem rejected_not_computable : ¬ computableArena.Law computableRejected := by
  classical
  intro h
  have he : Computable (fun c : Nat.Partrec.Code =>
      (undecidableOutput (Encodable.encode c,[])).isSome) :=
    Primrec.option_isSome.to_comp.comp (h.comp
      (Computable.encode.pair (Computable.const [])))
  have hn : Computable (fun c : Nat.Partrec.Code =>
      decide ((c.eval 0).Dom)) :=
    (Primrec.not.to_comp.comp he).of_eq (fun c => by
      simp only [undecidableOutput,Denumerable.ofNat_encode]
      split <;> simp_all)
  exact ComputablePred.halting_problem 0 hn.computablePred

private theorem empty_F : F (0,[]) = some (some []) := by
  rw [show (0,[]) = (0,liftEquations ([] : Equations (Fin 0))) from rfl,exact_native]
  unfold Constraints.unify
  rw [Constraints.unifyCore.eq_def]
  rfl

private theorem invalid_F : F (0,[(.of (.inr 0),.of (.inr 0))]) = none := by
  apply (rejection_exact _ _).mpr
  simp [inRange]

private theorem clash_F : F (0,[(.of (.inl false),.of (.inl true))]) = some none := by
  have h := exact_native 0 [(FreeMagma.of (Sum.inl false),FreeMagma.of (Sum.inl true))]
  change F (0,[(.of (.inl false),.of (.inl true))]) = _ at h
  rw [h]
  change (match Constraints.unify [(leaf false,leaf true)] SubstInfo.empty with
    | .error _ => (some none : SolverOutput)
    | .ok S => some (some (project 0 S.subst))) = some none
  unfold Constraints.unify
  rw [Constraints.unifyCore.eq_def]
  dsimp only
  rw [Constraint.unifyOne.eq_def]
  rfl

def computableEvidence : Registration computableArena
    (type_of% (@Lambda.UniformNativeUnification.computable_F)) where
  actual := computableActual
  bridge := Iff.rfl
  variation := ⟨computable_F,computableRejected,rejected_not_computable⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨computableRejected,?_,rfl,rejected_not_computable⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    -- A constant actual readout would be computable but must distinguish
    -- valid native success from malformed input in the complete domain.
    refine ⟨(),(0,[]),(0,[(.of (.inr 0),.of (.inr 0))]),?_⟩
    change F (0,[]) ≠ F (0,[(.of (.inr 0),.of (.inr 0))])
    rw [empty_F,invalid_F]
    intro h; cases h

abbrev exactSignature : Signature where
  Params := Nat
  State n := Equations (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := SolverOutput
  Anchor := Empty
  finiteAnchor := inferInstance

def exactActual : Realization exactSignature := realize exactSignature
  (fun _ n E => F (n,liftEquations E)) (fun e => nomatch e)
def exactRejected : Realization exactSignature := realize exactSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev exactArena : Arena where
  signature := exactSignature
  Law R := ∀ n (E : Equations (Fin n)), R.readout () n E =
    match Constraints.unify (E.map (fun e => (encode (finPresentation n) e.1,
      encode (finPresentation n) e.2))) SubstInfo.empty with
    | .error _ => some none
    | .ok S => some (some (project n S.subst))

private theorem exact_rejected_law : ¬ exactArena.Law exactRejected := by
  intro h
  have bad := h 0 []
  have impossible : (none : SolverOutput) = some (some []) :=
    bad.trans ((exact_native 0 []).symm.trans empty_F)
  cases impossible

def exactEvidence : Registration exactArena (type_of% (@Lambda.UniformNativeUnification.exact_native)) where
  actual := exactActual
  bridge := Iff.rfl
  variation := ⟨exact_native,exactRejected,exact_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exactRejected,?_,rfl,exact_rejected_law⟩
      intro j ne; exact (ne (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨0,[],[(.of (.inl false),.of (.inl true))],?_⟩
    change F (0,[]) ≠ F (0,[(.of (.inl false),.of (.inl true))])
    rw [empty_F,clash_F]
    intro h; cases h

abbrev rejectSignature : Signature where
  Params := Nat
  State _ := Equations Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := SolverOutput
  Anchor := Empty
  finiteAnchor := inferInstance

def rejectActual : Realization rejectSignature := realize rejectSignature
  (fun _ n E => F (n,E)) (fun e => nomatch e)
def rejectRejected : Realization rejectSignature := realize rejectSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev rejectArena : Arena where
  signature := rejectSignature
  Law R := ∀ n (E : Equations Nat), R.readout () n E = none ↔
    E.all (fun e => inRange n e.1 && inRange n e.2) = false

private theorem reject_rejected_law : ¬ rejectArena.Law rejectRejected := by
  intro h
  have bad := (h 0 []).mp rfl
  cases bad

def rejectEvidence : Registration rejectArena (type_of% (@Lambda.UniformNativeUnification.rejection_exact)) where
  actual := rejectActual
  bridge := Iff.rfl
  variation := ⟨rejection_exact,rejectRejected,reject_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectRejected,?_,rfl,reject_rejected_law⟩
      intro j ne; exact (ne (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨0,[],[(.of (.inr 0),.of (.inr 0))],?_⟩
    change F (0,[]) ≠ F (0,[(.of (.inr 0),.of (.inr 0))])
    rw [empty_F,invalid_F]
    intro h; cases h

noncomputable def registration_computable_F :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UniformNativeUnification.computable_F)
      (type_of% (realize solverSignature (fun _ _ input => F input) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UniformNativeUnification.unit_computable_F,
  realizationName := `Reg.D5.S0.Rewriting.UniformNativeUnification.computableEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨computableArena⟩,
  objectArena := .source ⟨computableArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source computableArena ⟨computableEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize solverSignature (fun _ _ input => F input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UniformNativeUnification,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


end Reg.D5.S0.Rewriting.UniformNativeUnification
