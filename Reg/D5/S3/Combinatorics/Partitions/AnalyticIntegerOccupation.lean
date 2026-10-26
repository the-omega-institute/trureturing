import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open LeanInformationAudit Complex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open _root_.D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

namespace Normalization

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Output _ _ := ℂ → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => fun _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hh

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (r : ℕ) (τ : ℂ) (_ : 0 < τ.im),
    a.readout () ()
      (exp (-2 * Real.pi * I * τ * r / 24) *
        (∑' d : (Fin r × ℕ) →₀ ℕ,
          signedIntegerMonomial (exp (2 * Real.pi * I * τ)) d))
      ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ r)

private theorem source_bridge :
    (type_of% (@D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.normalized_signed_integer_eq_eta)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 I (by norm_num)

def family : Registration arena (type_of% (@D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.normalized_signed_integer_eq_eta)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp normalized_signed_integer_eq_eta, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.normalized_signed_integer_eq_eta) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.Normalization.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization

end Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
