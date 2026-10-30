import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithUnits.SimultaneousShearInvariance
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift

namespace Reg.D5.S3.ArithUnits.SimultaneousShearInvariance

open _root_.D5.S3.ArithUnits.SimultaneousShearInvariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

/-- The original equality observes polynomials over both original carriers. -/
abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := MvPolynomial (Fin 2) (MvPolynomial p.2 p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MvPolynomial (Fin 2) (MvPolynomial p.2 p.1) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ F G => F = G) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {R : Type u} [CommRing R] [IsDomain R] [CharZero R] {σ : Type v}
    (ι : Fin 4 → σ) (hι : Function.Injective ι)
    (F : MvPolynomial (Fin 2) (MvPolynomial σ R))
    (ha : translate (fun i : Fin 2 =>
      if i = 0 then X (ι 0) else X (ι 2)) F = F)
    (hb : translate (fun i : Fin 2 =>
      if i = 0 then X (ι 1) else X (ι 3)) F = F),
    r.readout () ⟨R, σ⟩ F (C (constantCoeff F))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} ℤ) inferInstance inferInstance inferInstance
    (ULift.{v} (Fin 4)) ULift.up
    (fun _ _ he => congrArg ULift.down he) 0 (by simp) (by simp)

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ, ULift.{v} (Fin 4)⟩, 0, 1, ?_⟩
  intro he
  have hz : (1 : MvPolynomial (Fin 2) (MvPolynomial (ULift.{v} (Fin 4))
      (ULift.{u} ℤ))) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hz

def source_registration : Registration arena.{u,v}
    (type_of% @eq_constant_of_two_shears.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eq_constant_of_two_shears, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eq_constant_of_two_shears.{u,v}) (Realization signature.{u,v}) Type Unit := {
  unitName := `Reg.D5.S3.ArithUnits.SimultaneousShearInvariance.unit
  realizationName := `Reg.D5.S3.ArithUnits.SimultaneousShearInvariance.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ F G => F = G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithUnits.SimultaneousShearInvariance
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
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
end Reg.D5.S3.ArithUnits.SimultaneousShearInvariance
