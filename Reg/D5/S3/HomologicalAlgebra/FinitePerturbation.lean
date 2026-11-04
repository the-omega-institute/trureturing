import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.FinitePerturbation
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import Mathlib.Algebra.Module.ULift

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FinitePerturbation
open _root_.D5.S3.HomologicalAlgebra.FinitePerturbation.Input
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.FinitePerturbation
universe u v w

structure Parameters where
  R : Type u
  U : Type v
  V : Type w
  ring : CommRing R
  groupU : AddCommGroup U
  moduleU : @Module R U ring.toSemiring groupU.toAddCommMonoid
  groupV : AddCommGroup V
  moduleV : @Module R V ring.toSemiring groupV.toAddCommMonoid
  input : @Input R U V ring groupU moduleU groupV moduleV

attribute [instance] Parameters.ring Parameters.groupU Parameters.moduleU
  Parameters.groupV Parameters.moduleV

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The observed predicate is the complete source conclusion at its actual exponent. -/
def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ p n => p.input.Conclusion n) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V)) (n : ℕ) (_hn : 1 ≤ n)
    (_nilpotent : (c.h*c.delta)^n = 0),
      r.readout () ⟨R,U,V,inferInstance,inferInstance,inferInstance,
        inferInstance,inferInstance,c⟩ n

private def liftedRingHom : ULift.{u} ℤ →+* ℤ := ULift.ringEquiv.toRingHom

private def sample : Parameters.{u,v,w} := by
  let R := ULift.{u} ℤ
  let U := ULift.{v} ℤ
  let V := ULift.{w} ℤ
  letI : Module R U := Module.compHom U liftedRingHom
  letI : Module R V := Module.compHom V liftedRingHom
  let i : U →ₗ[R] V := {
    toFun := fun x => ⟨x.down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  let p : V →ₗ[R] U := {
    toFun := fun x => ⟨x.down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  let c : Input (R := R) (U := U) (V := V) := {
    d0 := 0, h := 0, delta := 0, i := i, p := p
    d0_sq := by simp
    pi := by ext x; rfl
    di := by simp
    pd := by simp
    contraction := by
      ext x
      change (0 : ℤ) = x.down - x.down
      simp
    hh := by simp
    hi := by simp
    ph := by simp
    perturbed_sq := by simp }
  exact ⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩

private theorem sample_nilpotent :
    (sample.{u,v,w}.input.h*sample.input.delta)^1 = 0 := by
  ext x
  rfl

private theorem sample_zero_fails : ¬ sample.{u,v,w}.input.Conclusion 0 := by
  intro out
  have eq := out.K_left
  have val := DFunLike.congr_fun eq (show sample.V from ⟨1⟩)
  have down := congrArg ULift.down val
  change (0 : ℤ) = 1 at down
  exact zero_ne_one down

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  exact law sample.input 1 (by decide) sample_nilpotent

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c n hn nilpotent
  exact finite_perturbation c n hn nilpotent

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨sample,0,1,?_⟩
  change sample.input.Conclusion 0 ≠ sample.input.Conclusion 1
  intro eq
  exact sample_zero_fails (eq.mpr (finite_perturbation sample.input 1 (by decide)
    sample_nilpotent))

def source_registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected,fun other hne => (hne (Subsingleton.elim other role)).elim,
        rfl,rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HomologicalAlgebra.FinitePerturbation.Input.finite_perturbation.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p n => p.input.Conclusion n)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbation.finite_perturbation
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p n => p.input.Conclusion n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FinitePerturbation
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end Reg.D5.S3.HomologicalAlgebra.FinitePerturbation
