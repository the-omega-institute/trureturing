import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExpRatioCM.Extraction
import Reg.D5.S3.Analytic.ExpRatioCM.Series

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.ExpRatioCM.Defs
open _root_.D5.S3.Analytic.ExpRatioCM.Series
open _root_.D5.S3.Analytic.ExpRatioCM.Extraction
open LeanInformationAudit Filter
open scoped Topology

noncomputable section
namespace Reg.D5.S3.Analytic.ExpRatioCM.Extraction

abbrev coefficientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ → ℝ) (fun _ => ℕ) (fun _ => ℝ)

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ b n => b n) (fun e => nomatch e)

def coefficientShift : Realization coefficientSignature :=
  realize coefficientSignature (fun _ b n => b n + 1) (fun e => nomatch e)

private theorem coefficientDependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨(fun n => (n : ℝ)), 0, 1, ?_⟩
  norm_num [coefficientActual, realize]

namespace Transfer

def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ {b r : ℕ → ℝ} {h : ℝ → ℝ},
    (∀ᶠ k : ℕ in atTop,
      (49 / 32 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))) = b 2 + r k) →
    Tendsto r atTop (𝓝 0) →
    Tendsto (fun k : ℕ => (49 / 32 : ℝ) ^ k *
      ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))))
      atTop (𝓝 (R.readout () b 2))

private theorem rejected : ¬ arena.Law coefficientShift := by
  intro hh
  have he := @hh (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (Filter.Eventually.of_forall (fun k => by simp)) tendsto_const_nhds
  have he' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa [coefficientShift, realize] using he
  have := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ))) he'
  norm_num at this

def family : Registration arena (type_of% @extraction_limit) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@extraction_limit, coefficientShift, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual coefficientShift rejected
  dependence := coefficientDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extraction_limit) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Transfer.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ b n => b n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Extraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Transfer

abbrev actualCoefficientSignature := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.coefficientSignature
abbrev actualCoefficient := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.coefficientActual
abbrev zeroCoefficient := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.coefficientZero

namespace Quotient

def arena : Arena where
  signature := actualCoefficientSignature
  Law R := ∀ i : ℕ,
    Tendsto (fun k : ℕ => (49 / 32 : ℝ) ^ k *
      ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i) (k * Real.log (7 / 4))))
      atTop (𝓝 (R.readout () i 2))

private theorem rejected : ¬ arena.Law zeroCoefficient := by
  intro h
  have hz := h 0
  have ha := quotient_extraction_limit 0
  have he := tendsto_nhds_unique hz ha
  norm_num [zeroCoefficient, _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.coefficientZero,
    realize, quotCoeff_two] at he

def family : Registration arena (type_of% @quotient_extraction_limit) where
  actual := actualCoefficient
  bridge := Iff.rfl
  variation := ⟨@quotient_extraction_limit, zeroCoefficient, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actualCoefficient zeroCoefficient rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.Second.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quotient_extraction_limit) (Realization actualCoefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Quotient.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Quotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize actualCoefficientSignature (fun _ i n => quotCoeff i n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Extraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Quotient

abbrev functionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)
def functionActual : Realization functionSignature :=
  realize functionSignature (fun _ h t => h t) (fun e => nomatch e)
def zeroFunction : Realization functionSignature :=
  realize functionSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem functionDependence : ObservationalDependence functionSignature functionActual := by
  intro i
  refine ⟨id, 0, 1, ?_⟩
  norm_num [functionActual, realize]

theorem zero_cm : CompletelyMonotoneOn (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨contDiffOn_const, ?_⟩
  intro k t ht
  simp

namespace Obstruction

def arena : Arena where
  signature := functionSignature
  Law R := ∀ {h : ℝ → ℝ} {b : ℕ → ℝ},
    Tendsto (fun k : ℕ => (49 / 32 : ℝ) ^ k *
      ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))))
      atTop (𝓝 (b 2)) → b 2 < 0 → ¬ CompletelyMonotoneOn (R.readout () h)

private theorem rejected : ¬ arena.Law zeroFunction := by
  intro hh
  have hz := @hh (ratioF 3) (quotCoeff 3) (quotient_extraction_limit 3)
    (by norm_num [quotCoeff_two])
  exact hz zero_cm

def family : Registration arena (type_of% @not_completelyMonotone_of_extraction) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@not_completelyMonotone_of_extraction, zeroFunction, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law functionActual zeroFunction rejected
  dependence := functionDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@not_completelyMonotone_of_extraction) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Obstruction.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Obstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature (fun _ h t => h t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Extraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Obstruction

end Reg.D5.S3.Analytic.ExpRatioCM.Extraction
end
