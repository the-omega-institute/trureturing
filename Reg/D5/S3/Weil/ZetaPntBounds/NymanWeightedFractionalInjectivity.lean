import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity

/-! Faithful dependent-family audit of the original weighted transform theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity
open _root_.D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity

-- The state is the original function. The observed data occurrence is only
-- the original function in the concluding EqOn; every original premise stays.
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℝ → ℂ) (r gamma : ℝ)
    (_hr : -1 / 2 < r) (_hr1 : r < 1 / 2) (_hw : ContinuousOn w (Ioi 0))
    (_hwr : WeightedIntegrable w r)
    (_hzero : ∀ y : ℝ, 0 < y → actualTransform w gamma y = 0),
    EqOn (R.readout () () w) 0 (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hw : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Ioi 0) := continuousOn_const
  have hwr : WeightedIntegrable (fun _ : ℝ => (0 : ℂ)) 0 := by
    simp [WeightedIntegrable]
  have hzero : ∀ y : ℝ, 0 < y → actualTransform (fun _ : ℝ => (0 : ℂ)) 0 y = 0 := by
    intro y _
    simp [actualTransform, actualIntegrand]
  have hbad := h (fun _ : ℝ => (0 : ℂ)) 0 0 (by norm_num) (by norm_num) hw hwr hzero
    (show (1 : ℝ) ∈ Ioi (0 : ℝ) from by norm_num)
  norm_num [rejected, realize] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), (fun _ : ℝ => (1 : ℂ)), ?_⟩
  intro he
  have h := congrFun he (1 : ℝ)
  norm_num [actual, realize] at h

def family : Registration arena (type_of% (@weighted_fractional_transform_injective)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_fractional_transform_injective, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_fractional_transform_injective)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity.weighted_fractional_transform_injective.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity
