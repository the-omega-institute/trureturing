import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.Binary
universe u

abbrev signature : Signature where
  Params := Σ A : Type u, ℕ → A
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def emptyAnchor : ∀ (_ : signature.{u}.Anchor) p, signature.{u}.State p :=
  fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => p.2 n)
    emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ p n => p.2 (n+1)) emptyAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [g : AddCommGroup A] (d : ℕ) (f : ℕ → A) (z : ℤ),
    read (d+1) (fun n => R.readout () ⟨A,f⟩ n) z = (z%2 : ℤ) • f 0 + read d (fun i => f (i+1)) (z/2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (A := ULift.{u} ℤ) 0
    (fun n => ULift.up (if n=0 then (1 : ℤ) else 0)) 1
  have he' := congrArg ULift.down he
  norm_num [rejected,actual,realize,_root_.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.read,digit] at he'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ,fun n => ULift.up (n : ℤ)⟩,0,1,?_⟩
  intro h
  have he := congrArg ULift.down h
  norm_num [actual,realize,_root_.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.read,digit] at he

def successor_family : Registration arena.{u} (type_of% (@read_succ.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@read_succ.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def successor_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@read_succ.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.read_succ.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.Binary.successor_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨successor_family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p n => p.2 n) emptyAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.Binary
