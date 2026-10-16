import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
open _root_.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the real symmetric matrix after entrywise inclusion into the complex numbers. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℝ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature
    (fun _ p w => ((!![p.1, p.2; p.2, w]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p w => -((!![p.1, p.2; p.2, w]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v w : ℝ), 0 < u + w → 0 ≤ u * w - v ^ 2 →
    (R.readout () ⟨u, v⟩ w).PosSemidef

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (-((!![(1 : ℝ), 0; 0, 1]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
    simpa [rejected, realize] using h 1 0 1 (by norm_num) (by norm_num)
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hp).2
  let z : Fin 2 → ℂ := ![1, 0]
  have hz := hq z
  norm_num [rejected, realize, z, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two] at hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 1, 2, ?_⟩
  intro he
  have he' :
    ((!![(1 : ℝ), 0; 0, 1]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((!![(1 : ℝ), 0; 0, 2]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa [actual, realize] using he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) he'
  norm_num at hc

def source_registration : Registration arena
    (type_of% @posSemidef_of_trace_det) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using posSemidef_of_trace_det,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.posSemidef_of_trace_det)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature
      (fun _ p w => ((!![p.1, p.2; p.2, w]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
