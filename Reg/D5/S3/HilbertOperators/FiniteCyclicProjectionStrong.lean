import D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
import Reg.Support.RealScalarLift
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

/-! Full-telescope observation of the actual finite cyclic projection orbit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
open Filter
open scoped Topology
open _root_.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  k : Type u
  [scalar : RCLike k]
  H : Type v
  [additive : NormedAddCommGroup H]
  [inner : InnerProductSpace k H]
  [complete : CompleteSpace H]
  Us : List (ClosedSubmodule k H)


abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature
    (fun _ p => by
      letI := p.scalar
      letI := p.additive
      letI := p.inner
      letI := p.complete
      exact fun x n => (cycle p.Us ^ n) x)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ x _ => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (Us : List (ClosedSubmodule k H)) (x : H),
    Tendsto (R.readout () (@Parameters.mk k inferInstance H inferInstance inferInstance inferInstance Us) x)
      atTop (𝓝 ((sInf {U | U ∈ Us}).toSubmodule.starProjection x))

private theorem actual_law : arena.{u,v}.Law actual :=
  @tendsto_cycle_pow.{u,v}


private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have ht := h (k := ULift.{u} ℝ) (H := ULift.{v} ℝ) [⊥] (ULift.up 1)
  have hz : (ULift.up 1 : ULift.{v} ℝ) = 0 := by
    simpa [rejected, realize] using ht
  have hreal := congrArg ULift.down hz
  exact one_ne_zero hreal

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : Parameters.{u,v} :=
    @Parameters.mk (ULift.{u} ℝ) inferInstance (ULift.{v} ℝ)
      inferInstance inferInstance inferInstance []
  refine ⟨p, 0, ULift.up 1, ?_⟩
  intro h
  have hz := congrArg (fun f : ℕ → ULift.{v} ℝ => (f 0).down) h
  change (0 : ℝ) = 1 at hz
  exact zero_ne_one hz

def familyRegistration : Registration arena.{u,v}
    (type_of% (@tendsto_cycle_pow.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tendsto_cycle_pow.{u,v})
      (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong.unit
  realizationName := `Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => by
      letI := p.scalar
      letI := p.additive
      letI := p.inner
      letI := p.complete
      exact fun x n => (cycle p.Us ^ n) x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
    definition := none
    coordinates := #[0,1,2,3,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "fn","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
