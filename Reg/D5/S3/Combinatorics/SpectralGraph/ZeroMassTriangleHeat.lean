import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat
import Reg.Support.UniverseSingleReadout

/-! The finite-mass collocated heat at fixed retained conductance, mass and
scaled time observes the hidden-edge conductance. -/

set_option autoImplicit false

open scoped Matrix
open NormedSpace (exp)

namespace Reg.D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat

open _root_.D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat
open _root_.D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance (PositiveWeights)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev Parameters := Σ _ : ℝ, Σ _ : ℝ, ℝ

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Parameters (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p c => physicalHeat p.1 c p.2.1 (p.2.1 * p.2.2) 0 0)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

/-- The intervention changes the finite-mass observation and keeps the entire
exactly massless clause of the source theorem. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k ε s : ℝ) (_hε : 0 < ε) (_hs : 0 < s),
    (∀ c ∈ Set.Ioo 0 (2 * k),
      PositiveWeights (weights k c) ∧
      masslessStiffness k c = !![k, -k; -k, k] ∧
      ∀ t : ℝ, masslessHeat k c t = exp ((-t) • (!![k, -k; -k, k] :
        Matrix (Fin 2) (Fin 2) ℝ))) ∧
    Set.InjOn (R.readout () ⟨k, ε, s⟩) (Set.Ioo 0 (2 * k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hInj := (h 2 1 1 (by norm_num) (by norm_num)).2
  have h₁ : (1 : ℝ) ∈ Set.Ioo 0 (2 * 2) := by norm_num [Set.mem_Ioo]
  have h₂ : (2 : ℝ) ∈ Set.Ioo 0 (2 * 2) := by norm_num [Set.mem_Ioo]
  have he : (1 : ℝ) = 2 := hInj h₁ h₂ rfl
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 1, 1⟩, 1, 2, ?_⟩
  change physicalHeat 2 1 1 (1 * 1) 0 0 ≠ physicalHeat 2 2 1 (1 * 1) 0 0
  intro h
  have hInj := (same_schur_distinct_heat_at_mass_time 2 1 1 (by norm_num) (by norm_num)).2
  have he : (1 : ℝ) = 2 := hInj (by norm_num [Set.mem_Ioo]) (by norm_num [Set.mem_Ioo]) h
  norm_num at he

def family : Registration arena (type_of% same_schur_distinct_heat_at_mass_time) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_schur_distinct_heat_at_mass_time, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    same_schur_distinct_heat_at_mass_time (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat.same_schur_distinct_heat_at_mass_time.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p c => physicalHeat p.1 c p.2.1 (p.2.1 * p.2.2) 0 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.SpectralGraph.ZeroMassTriangleHeat
