import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent
import Reg.Support.SingleDependentReadout

/-! The value comparison is observed as equality of real values. The law retains
all source types, branch guards, optimal-action sets, and prefix-record clauses. -/

namespace Reg.D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent

open _root_.D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w x y

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Only the first concluding equality is replaced by an observation. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀
    {MicroState : Type u} {MacroState : Type v} {Action : Type w}
    {Output : Type x} {Failure : Type y}
    (abstract : MicroState → MacroState)
    (micro : PartialMenuModel MicroState Action Output Failure)
    (macroModel : PartialMenuModel MacroState Action Output Failure)
    (menuFactors : ∀ state, micro.menu state = macroModel.menu (abstract state))
    (successorFactors : ∀ action state, action ∈ micro.menu state →
      abstract (micro.successor action state) =
        macroModel.successor action (abstract state))
    (rewardFactors : ∀ state action, action ∈ micro.menu state →
      micro.reward state action = macroModel.reward (abstract state) action)
    (terminalFactors : ∀ state,
      micro.terminal state = macroModel.terminal (abstract state))
    (outputFactors : ∀ state action, action ∈ micro.menu state →
      micro.output state action = macroModel.output (abstract state) action)
    (successCostFactors : ∀ state action, action ∈ micro.menu state →
      micro.successCost state action = macroModel.successCost (abstract state) action)
    (failureReportFactors : ∀ state action, action ∉ micro.menu state →
      micro.failureReport state action = macroModel.failureReport (abstract state) action)
    (failureCostFactors : ∀ state action, action ∉ micro.menu state →
      micro.failureCost state action = macroModel.failureCost (abstract state) action),
    (∀ horizon state,
      R.readout () ()
        (partialHorizonValue micro.menu micro.menuNonempty micro.successor micro.reward
          micro.terminal horizon state)
        (partialHorizonValue macroModel.menu macroModel.menuNonempty macroModel.successor macroModel.reward
          macroModel.terminal horizon (abstract state))) ∧
    (∀ horizon state,
      partialHorizonOptimalActions micro.menu micro.menuNonempty micro.successor
          micro.reward micro.terminal horizon state =
        partialHorizonOptimalActions macroModel.menu macroModel.menuNonempty macroModel.successor
          macroModel.reward macroModel.terminal horizon (abstract state)) ∧
    (∀ state actions,
      PrefixRecord.mapState abstract
          (runPrefix micro.step state actions) =
        runPrefix macroModel.step (abstract state) actions)

private theorem actual_law : arena.{u,v,w,x,y}.Law actual :=
  @partial_menu_finite_horizon_descent.{u,v,w,x,y}

/-- Singleton systems supply valid source hypotheses at every source universe. -/
private def singletonModel (State Action Output Failure : Type*)
    [Inhabited State] [Inhabited Action] [Inhabited Output] [Inhabited Failure] :
    PartialMenuModel State Action Output Failure where
  menu := fun _ => {default}
  menuNonempty := fun _ => Finset.singleton_nonempty _
  successor := fun _ _ => default
  reward := fun _ _ => 0
  terminal := fun _ => 0
  output := fun _ _ => default
  successCost := fun _ _ => 0
  failureReport := fun _ _ => default
  failureCost := fun _ _ => 0

private theorem rejected_law : ¬ arena.{u,v,w,x,y}.Law rejected := by
  let micro := singletonModel (ULift.{u} Unit) (ULift.{w} Unit)
    (ULift.{x} Unit) (ULift.{y} Unit)
  let macroModel := singletonModel (ULift.{v} Unit) (ULift.{w} Unit)
    (ULift.{x} Unit) (ULift.{y} Unit)
  intro h
  have hbad := h (fun _ => (default : ULift.{v} Unit)) micro macroModel
    (by intro _; rfl)
    (by intro _ _ _; rfl)
    (by intro _ _ _; rfl)
    (by intro _; rfl)
    (by intro _ _ _; rfl)
    (by intro _ _ _; rfl)
    (by intro _ _ _; rfl)
    (by intro _ _ _; rfl)
  exact hbad.1 0 default

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (0 : ℝ) = 1 := Eq.mpr (congrFun h 1) rfl
  exact zero_ne_one hbad

def source_registration : Registration arena.{u,v,w,x,y}
    (type_of% @partial_menu_finite_horizon_descent.{u,v,w,x,y}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partial_menu_finite_horizon_descent.{u,v,w,x,y})
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent.unit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,x,y}⟩
  objectArena := .source ⟨arena.{u,v,w,x,y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent
