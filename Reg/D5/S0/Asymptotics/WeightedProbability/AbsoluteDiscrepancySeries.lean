import D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
import Reg.Support.DependentFamily
import Mathlib.MeasureTheory.Measure.Dirac
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries

open _root_.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set LeanInformationAudit
open scoped ENNReal NNReal BigOperators

noncomputable section
universe u

abbrev profileSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def profileActual : Realization profileSignature :=
  realize profileSignature (fun _ _ x => discrepancyProfile x) (fun e => nomatch e)

def profileRejected : Realization profileSignature :=
  realize profileSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem profileDependence : ObservationalDependence profileSignature profileActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hroot23 : Real.sqrt 2 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdenom : Real.sqrt 2 * Real.log 2 < Real.sqrt 3 * Real.log 3 :=
    (mul_lt_mul_of_pos_right hroot23 hlog2).trans_le
      (mul_le_mul_of_nonneg_left hlog23.le (Real.sqrt_nonneg _))
  have hlt := one_div_lt_one_div_of_lt
    (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hlog2) hdenom
  have hprofile : discrepancyProfile 1 < discrepancyProfile 0 := by
    simpa [discrepancyProfile, show (2 : ℝ) + 1 = 3 by norm_num] using hlt
  exact ne_of_gt hprofile

abbrev envelopeArena : Arena where
  signature := profileSignature
  Law r := ∀ (x : ℤ) (j : ℕ) (C : ℝ), 0 ≤ C →
    |(x : ℝ)| ≤ C * ((j : ℝ) + 1) ^ 2 →
    shiftedLogWeight j / (Real.sqrt (C + 2) *
      (2 + Real.log (C + 2) / Real.log 2)) ≤ r.readout () () x

private theorem envelopeRejected : ¬ envelopeArena.Law profileRejected := by
  intro h
  have hh := h 0 0 0 (by norm_num) (by norm_num)
  change shiftedLogWeight 0 /
    (Real.sqrt (0 + 2) * (2 + Real.log (0 + 2) / Real.log 2)) ≤ 0 at hh
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw : 0 < shiftedLogWeight 0 := by
    simpa [shiftedLogWeight] using one_div_pos.mpr hlog2
  have hp : 0 < shiftedLogWeight 0 /
      (Real.sqrt (0 + 2) * (2 + Real.log (0 + 2) / Real.log 2)) := by
    apply div_pos hw
    rw [zero_add, div_self hlog2.ne']
    positivity
  exact (not_le_of_gt hp) hh

def envelopeSource : Registration envelopeArena (type_of% @discrepancyProfile_lower_bound) where
  actual := profileActual
  bridge := Iff.rfl
  variation := ⟨discrepancyProfile_lower_bound, profileRejected, envelopeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨profileRejected, ?_, rfl, envelopeRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := profileDependence

abbrev weightSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ j => shiftedLogWeight j) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law r := ∑' j, ENNReal.ofReal (r.readout () () j) = ∞

private theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlt := one_div_lt_one_div_of_lt hlog2 (show Real.log 2 < 2 * Real.log 3 by linarith)
  have hweight : shiftedLogWeight 1 < shiftedLogWeight 0 := by
    simpa [shiftedLogWeight, show (1 : ℝ) + 2 = 3 by norm_num,
      show (1 : ℝ) + 1 = 2 by norm_num] using hlt
  exact ne_of_gt hweight

private theorem weightRejectedLaw : ¬ weightArena.Law weightRejected := by
  simp [weightRejected, realize]

def weightSource : Registration weightArena (type_of% @tsum_shiftedLogWeight_eq_top) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨tsum_shiftedLogWeight_eq_top, weightRejected, weightRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightRejected, ?_, rfl, weightRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

abbrev applicationArena : Arena where
  signature := profileSignature
  Law r := ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ℕ → Ω → ℤ), (∀ j, Measurable (E j)) →
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ j : ℕ,
      μ {ω | C * ((j : ℝ) + 1) ^ 2 < |(E j ω : ℝ)|} ≤ ENNReal.ofReal δ) →
    ∀ᵐ ω ∂μ, ∑' j, ENNReal.ofReal (r.readout () () (E j ω)) = ∞

private theorem applicationRejected : ¬ applicationArena.{u}.Law profileRejected := by
  intro h
  let μ : Measure (ULift.{u} Unit) := Measure.dirac ⟨()⟩
  let E : ℕ → ULift.{u} Unit → ℤ := fun _ _ => 0
  have hh := h μ E (fun _ => measurable_const) (by
    intro δ hδ
    refine ⟨0, ?_⟩
    intro j
    simp [E])
  simp [profileRejected, realize, μ] at hh

def applicationSource : Registration applicationArena.{u}
    (type_of% @ae_tsum_discrepancyProfile_eq_top.{u}) where
  actual := profileActual
  bridge := Iff.rfl
  variation := ⟨ae_tsum_discrepancyProfile_eq_top, profileRejected, applicationRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨profileRejected, ?_, rfl, applicationRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := profileDependence


def envelopeAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@discrepancyProfile_lower_bound) (Realization profileSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.envelopeUnit
  realizationName :=
    `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.envelopeSource
  realizationSource := none
  generated := false
  arena := .source ⟨envelopeArena⟩
  objectArena := .source ⟨envelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source envelopeArena ⟨envelopeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize profileSignature (fun _ _ x => discrepancyProfile x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms envelopeSource
#print axioms envelopeAudit


def weightAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@tsum_shiftedLogWeight_eq_top) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.weightUnit
  realizationName :=
    `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.weightSource
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ j => shiftedLogWeight j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms weightSource
#print axioms weightAudit


def applicationAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ae_tsum_discrepancyProfile_eq_top.{u}) (Realization profileSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.applicationUnit
  realizationName :=
    `Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries.applicationSource
  realizationSource := none
  generated := false
  arena := .source ⟨applicationArena.{u}⟩
  objectArena := .source ⟨applicationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source applicationArena.{u} ⟨applicationSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize profileSignature (fun _ _ x => discrepancyProfile x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "fn", "arg", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms applicationSource
#print axioms applicationAudit

end
end Reg.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
