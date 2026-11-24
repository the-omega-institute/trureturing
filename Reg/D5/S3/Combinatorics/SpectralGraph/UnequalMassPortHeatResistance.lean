import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance
import Reg.Support.UniverseSingleReadout

/-! Effective resistance as a readout on the two positive triangles. -/

set_option autoImplicit false

open Matrix
open scoped Matrix

namespace Reg.D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance

open _root_.D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation (effRes)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Bool) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ plus => effRes triangle (conductances plus) 0 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ plus : Bool,
    (R.readout () () plus = if plus then 352/197 else 448/197) ∧
    PositiveWeights (conductances plus) ∧
    reflectionᵀ = reflection ∧ reflection * reflection = 1 ∧
    reflection *ᵥ rootMass = rootMass ∧
    reflection *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] ∧
    normalized (conductances false) = reflection * normalized (conductances true) * reflectionᵀ ∧
    (∀ t : ℝ, physicalHeat (conductances true) t 0 0 = physicalHeat (conductances false) t 0 0) ∧
    HasDerivAt (fun t => physicalHeat (conductances plus) t 1 0)
      (if plus then 4/15 else 1/15) 0 ∧
    (∀ v : Fin 3 → ℝ,
      (stiffness (conductances plus) *ᵥ v = ![1, -1, 0] ∧ v 1 = 0) ↔
        v = groundedPotential plus)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (0 : ℝ) = 352/197 := (h true).1
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(), true, false, ?_⟩
  change effRes triangle (conductances true) 0 1 ≠ effRes triangle (conductances false) 0 1
  rw [(triangle_certificate true).1, (triangle_certificate false).1]
  norm_num

def family : Registration arena (type_of% triangle_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangle_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    triangle_certificate (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance.triangle_certificate.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ plus => effRes triangle (conductances plus) 0 1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end UnequalMassPortHeatResistance
end SpectralGraph
end Combinatorics
end S3
end D5
end Reg
