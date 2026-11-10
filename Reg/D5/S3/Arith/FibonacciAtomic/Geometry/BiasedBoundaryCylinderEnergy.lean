import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The actual constant-trace minimum and mixed-cylinder form readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (J)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG S)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (D form lift free_root_least_energy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Minimum

abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => ‖z‖^2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ q : H,
    J q = constG 1 ∧ R.readout () () q = 1 ∧
    (∀ (c : ℝ) (z : H), J z = constG c → inner ℝ q z = c) ∧
    (∀ c : Bool, q (rootEdge c) = 1/2 ∧ S [c] q = (1/2:ℝ) • q)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨q,_,h,_⟩
  change (-1 : ℝ) = 1 at h
  norm_num at h

def familyRegistration : Registration arena (type_of% constant_trace_minimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨constant_trace_minimum,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0:H),constant_trace_minimum.choose,?_⟩
    change ‖(0:H)‖^2 ≠ ‖constant_trace_minimum.choose‖^2
    rw [constant_trace_minimum.choose_spec.2.1]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@constant_trace_minimum)
    (type_of% (realize signature (fun _ _ z => ‖z‖^2) (fun e => nomatch e)))
    (Type) Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy.Minimum.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy.Minimum.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖^2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (H),
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg","body","arg","fn","arg","fn","arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false}] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Minimum

namespace Mixed

private def A : D := cylinderD (rootEdge false)
private def B : D := cylinderD ⟨[false,false],by simp⟩

abbrev signature : Signature where
  Params := Unit
  State _ := D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ F => form B F) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0:ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () A = 1/8

private theorem rejected_law : ¬ arena.Law rejected := by
  norm_num [arena,rejected,realize]

private theorem zero_lift : lift (0 : D) = 0 := by
  have h := ((free_root_least_energy (0:D)).2.2.2.2.1 0 0 (by simp)).1
  simpa using h

def familyRegistration : Registration arena (type_of% mixed_cylinder_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_cylinder_energy,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),A,(0:D),?_⟩
    change form B A ≠ form B 0
    rw [show form B A = 1/8 from mixed_cylinder_energy,form,zero_lift,inner_zero_right]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_cylinder_energy)
    (type_of% (realize signature (fun _ _ F => form B F) (fun e => nomatch e)))
    (Type) Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy.Mixed.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy.Mixed.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ F => form B F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (D),
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn","arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false}] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Mixed

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy
