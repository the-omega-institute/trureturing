import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.RegularRepresentation.RegularTrace
import Reg.Support.DependentFamily

/-! # An audit of the regular trace identity on its original coefficient rings and groups -/

namespace Reg.D5.S3.FiniteGroups.RegularRepresentation.RegularTrace

open _root_.D5.S3.FiniteGroups.RegularRepresentation.RegularTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section
universe u_1 u_2

abbrev signature : Signature where
  Params := Type u_1
  State R := R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := R → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ _ x y => x = y) (fun e => Empty.elim e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law r := ∀ {R : Type u_1} {H : Type u_2} [ring : CommRing R] [Group H] [Fintype H]
    (a : List (MonoidAlgebra R H)),
    r.readout () R
      (LinearMap.trace R (MonoidAlgebra R H)
        ((a.map (Algebra.lmul R (MonoidAlgebra R H))).prod))
      ((Fintype.card H : R) * a.prod.coeff 1)

theorem rejected_law : ¬ arena.{u_1, u_2}.Law rejected := by
  intro h
  exact (@h (ULift.{u_1} ℤ) (ULift.{u_2} PUnit)
    inferInstance inferInstance inferInstance []) (trace_lmul_list_prod [])

theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} ℤ, 0, 1, ?_⟩
  intro h
  have hbad : (1 : ULift.{u_1} ℤ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena.{u_1, u_2} (type_of% @trace_lmul_list_prod.{u_1, u_2}) where
  actual := realize signature.{u_1} (fun _ _ x y => x = y) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨trace_lmul_list_prod, rejected, rejected_law⟩
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
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_lmul_list_prod.{u_1, u_2}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.RegularRepresentation.RegularTrace.unit
  realizationName := `Reg.D5.S3.FiniteGroups.RegularRepresentation.RegularTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1, u_2}⟩
  objectArena := .source ⟨arena.{u_1, u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1, u_2} ⟨source_registration.{u_1, u_2}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ _ x y => x = y) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.RegularRepresentation.RegularTrace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.FiniteGroups.RegularRepresentation.RegularTrace
