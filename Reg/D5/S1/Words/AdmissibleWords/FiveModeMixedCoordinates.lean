import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

open _root_.D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The parameter is the positive law `p`; the state is the direction `u`. -/
abbrev signature : Signature where
  Params := Fin 5 → ℝ
  State _ := Fin 5 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => fisher p hiddenDirection u) (fun e => nomatch e)

/-- Adding one to the Fisher pairing. -/
def rejected : Realization signature :=
  realize signature (fun _ p u => fisher p hiddenDirection u + 1) (fun e => nomatch e)

/-- The mixed-coordinate statement with the directional derivative of `χ` read out. -/
abbrev arena : Arena where
  signature := signature
  Law R := (∀ p ∈ openSimplex, visible p ∈ openPyramid) ∧
    (∀ v ∈ openPyramid, ∀ c : ℝ,
      ∃! p : Fin 5 → ℝ, p ∈ openSimplex ∧ visible p = v ∧ hiddenChi p = c) ∧
    (∀ p : Fin 5 → ℝ, (∀ s, 0 < p s) → ∀ u : Fin 5 → ℝ,
      HasDerivAt (fun t : ℝ => hiddenChi (p + t • u)) (R.readout () p u) 0) ∧
    ∑ s, hiddenDirection s = 0 ∧ visible hiddenDirection = 0

/-- A derivative is unique, so the shifted pairing fails at the uniform law. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2.2.1 (fun _ => 1) (fun _ => one_pos) 0
  have hgood := mixed_coordinates_global_chart.2.2.1 (fun _ => 1) (fun _ => one_pos) 0
  change HasDerivAt _ (fisher (fun _ => 1) hiddenDirection 0 + 1) 0 at hbad
  have heq := hgood.unique hbad
  linarith

/-- The pairing vanishes along the zero direction and equals four along the base loop. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨fun _ => 1, 0, hiddenDirection, ?_⟩
  change fisher (fun _ => 1) hiddenDirection 0 ≠
    fisher (fun _ => 1) hiddenDirection hiddenDirection
  have d0 : hiddenDirection 0 = 1 := rfl
  have d1 : hiddenDirection 1 = -1 := rfl
  have d2 : hiddenDirection 2 = 0 := rfl
  have d3 : hiddenDirection 3 = -1 := rfl
  have d4 : hiddenDirection 4 = 1 := rfl
  simp only [fisher, Fin.sum_univ_five, d0, d1, d2, d3, d4, Pi.zero_apply]
  norm_num

def registration : Registration arena
    ((∀ p ∈ openSimplex, visible p ∈ openPyramid) ∧
      (∀ v ∈ openPyramid, ∀ c : ℝ,
        ∃! p : Fin 5 → ℝ, p ∈ openSimplex ∧ visible p = v ∧ hiddenChi p = c) ∧
      (∀ p : Fin 5 → ℝ, (∀ s, 0 < p s) → ∀ u : Fin 5 → ℝ,
        HasDerivAt (fun t : ℝ => hiddenChi (p + t • u)) (fisher p hiddenDirection u) 0) ∧
      ∑ s, hiddenDirection s = 0 ∧ visible hiddenDirection = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_coordinates_global_chart, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the Fisher pairing with the base loop through its raw source path. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_coordinates_global_chart)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ p u => fisher p hiddenDirection u) (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.mixed_coordinates_global_chart.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p u => fisher p hiddenDirection u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
