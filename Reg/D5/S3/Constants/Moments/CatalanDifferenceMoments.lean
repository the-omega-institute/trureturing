import D5.S3.Constants.Moments.CatalanDifferenceMoments
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Constants.Moments.CatalanDifferenceMoments
open _root_.D5.S3.Constants.Moments.CatalanSquareHankelGrowth
open _root_.D5.S3.Constants.Moments.CatalanDifferenceMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Real
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k L => (fwdDiff (1 : Nat))^[k] catalanMoment L)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (L k : Nat) (_hL : 1 ≤ L),
    0 < O.readout () k L ∧
      3 * ((L : Real) + k) * O.readout () k L ≤
        ((L : Real) + k + 2) * O.readout () (k + 1) L ∧
      O.readout () (k + 1) L < 3 * O.readout () k L

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 0 (by omega)).1
  exact (lt_irrefl (0 : Real)) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 1, 2, ?_⟩
  norm_num [actual, realize, beta_moment_formula, catalan_one, catalan_two]

def family : Registration arena (type_of% @catalan_difference_ratio_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨catalan_difference_ratio_envelope, rejected, rejected_law⟩
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
      (@catalan_difference_ratio_envelope) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Constants.Moments.CatalanDifferenceMoments.unit
  realizationName := `Reg.D5.S3.Constants.Moments.CatalanDifferenceMoments.family
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
    owner := `D5.S3.Constants.Moments.CatalanDifferenceMoments
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Constants.Moments.CatalanDifferenceMoments
