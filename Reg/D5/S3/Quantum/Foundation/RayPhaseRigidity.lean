import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.RayPhaseRigidity
import Reg.Support.DependentFamily

noncomputable section
universe u
open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.RayPhaseRigidity
open _root_.D5.S3.Quantum.Foundation.RayPhaseRigidity

abbrev signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ A => Eq A) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (_hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (_hcoord : ∀ i : ι, PreservesRay A (Pi.single i 1))
    (tests : Set (ι → ℂ)) (_htests : ∀ x ∈ tests, PreservesRay A x)
    (_hconnect : RaySupportConnected tests),
    ∃ c : ℂ, ‖c‖ = 1 ∧ R.readout () ι A (c • (1 : Matrix ι ι ℂ))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hray (x : ULift.{u} Unit → ℂ) :
      PreservesRay (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) x := by
    simpa [PreservesRay] using Submodule.mem_span_singleton_self (R := ℂ) x
  obtain ⟨c, hc, hfalse⟩ := @h (ULift.{u} Unit) inferInstance inferInstance 1
    (Matrix.unitaryGroup _ _).one_mem (fun i => hray _) Set.univ
    (fun x _ => hray x) (fun i j =>
      Relation.ReflTransGen.single ⟨(fun _ => 1), Set.mem_univ _, one_ne_zero, one_ne_zero⟩)
  exact hfalse

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

def family : Registration arena.{u} (type_of% @unitary_phase_of_connected_ray_tests.{u}) where
  actual := realize signature.{u} (fun _ _ A => Eq A) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@unitary_phase_of_connected_ray_tests.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unitary_phase_of_connected_ray_tests.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.RayPhaseRigidity.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.RayPhaseRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ A => Eq A) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.RayPhaseRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Foundation.RayPhaseRigidity
