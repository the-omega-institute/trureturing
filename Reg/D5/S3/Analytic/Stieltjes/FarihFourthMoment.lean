import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Stieltjes.FarihFourthMoment
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open MeasureTheory LeanInformationAudit
open _root_.D5.S3.Analytic.Stieltjes.FarihFourthMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.Stieltjes.FarihFourthMoment

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Measure ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ μ => meanEfficiency μ) Empty.elim

def arena : Arena where
  signature := signature
  Law R :=
    FirstFourMoments uniform012 ∧ R.readout false () uniform012 = 11 / 18 ∧
    (∀ μ : Measure ℝ, FirstFourMoments μ → meanEfficiency μ ≤ 11 / 18) ∧
    (∀ μ : Measure ℝ, FirstFourMoments μ → ∀ a b : ℝ, ¬(∀ᵐ x ∂μ, x = a ∨ x = b)) ∧
    FirstThreeMoments threeMomentWitness ∧ R.readout true () threeMomentWitness = 37 / 60 ∧
    (∀ ν : Measure ℝ, FirstFourMoments ν → meanEfficiency ν < meanEfficiency threeMomentWitness)

private def eraseReading (i : Bool) : Realization signature :=
  realize signature (fun (j : Bool) _ μ => if j = i then 0 else meanEfficiency μ) Empty.elim

private theorem erased_fails (i : Bool) : ¬arena.Law (eraseReading i) := by
  intro law
  cases i
  · have h : (0 : ℝ) = 11 / 18 := by simpa [eraseReading, realize] using law.2.1
    norm_num at h
  · have h : (0 : ℝ) = 37 / 60 := by simpa [eraseReading, realize] using law.2.2.2.2.2.1
    norm_num at h

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), Measure.dirac (0 : ℝ), Measure.dirac (1 : ℝ), ?_⟩
  change meanEfficiency (Measure.dirac (0 : ℝ)) ≠ meanEfficiency (Measure.dirac (1 : ℝ))
  simp only [meanEfficiency, integral_dirac]
  norm_num [efficiency, inv_eq_one_div]

def evidence : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, eraseReading false, erased_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eraseReading i, ?_, rfl, erased_fails i⟩
      intro j hj
      funext p μ
      have hRole : (j : Bool) ≠ (i : Bool) := hj
      exact (ite_eq_right hRole).symm
    · intro i
      exact nomatch i
  dependence := actual_depends

/-- Bind both explicit attainment readings in the full settling statement. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Stieltjes.FarihFourthMoment.result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Stieltjes.FarihFourthMoment.result.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Stieltjes.FarihFourthMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ μ => meanEfficiency μ) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Stieltjes.FarihFourthMoment
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.Stieltjes.FarihFourthMoment
