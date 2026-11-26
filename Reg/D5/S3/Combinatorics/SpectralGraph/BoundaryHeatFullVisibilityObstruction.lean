import D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction

open _root_.D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ t => boundaryHeat L t) (fun e => nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ _ t => boundaryHeat L t + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    IsK4Laplacian L ∧ IsK4Laplacian reflectedL ∧
    (∀ t : ℝ, R.readout () () t = boundaryHeat reflectedL t) ∧
    (∀ t : ℝ, boundaryHeat L t =
      1/4 + Real.exp (-4*t)/12 + Real.exp (-5*t)/6 + Real.exp (-6*t)/2) ∧
    (∀ h : ℝ, 0 < h → (krylovFrame L h).det ≠ 0 ∧ (krylovFrame reflectedL h).det ≠ 0) ∧
    IsGreatest (conductanceValues L) (11/6) ∧ IsGreatest (conductanceValues reflectedL) (16/9) ∧
    edgeConductances L ≠ edgeConductances reflectedL ∧ ¬ IsWeightedIso L reflectedL

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs := h.2.2.1 0
  change boundaryHeat L 0 + 1 = boundaryHeat reflectedL 0 at hs
  have he := boundary_heat_full_visibility_obstruction.2.2.1 0
  linarith only [hs, he]

private theorem time_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change boundaryHeat L 0 ≠ boundaryHeat L 1
  have formula := boundary_heat_full_visibility_obstruction.2.2.2.1
  have atZero := formula 0
  have atOne := formula 1
  norm_num [Real.exp_zero] at atZero atOne
  have e4 : Real.exp (-4) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have e5 : Real.exp (-5) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have e6 : Real.exp (-6) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  intro equal
  linarith only [atZero, atOne, e4, e5, e6, equal]

def sourceFamily : Registration arena (type_of% boundary_heat_full_visibility_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨boundary_heat_full_visibility_obstruction, shifted, shifted_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨shifted, ?_, rfl, shifted_fails⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro anchor
      exact nomatch anchor
  dependence := time_dependence

def heatRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      boundary_heat_full_visibility_obstruction (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction.boundary_heat_full_visibility_obstruction.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction.sourceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => boundaryHeat L t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction
