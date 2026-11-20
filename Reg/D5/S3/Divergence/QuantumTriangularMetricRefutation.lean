import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Divergence.QuantumTriangularMetricRefutation
import Reg.Support.SingleDependentReadout

noncomputable section
open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Divergence.QuantumTriangularMetricRefutation
open _root_.D5.S3.Divergence.QuantumTriangularJensenShannonRefutation (QTD)
open _root_.D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState)

namespace Reg.D5.S3.Divergence.QuantumTriangularMetricRefutation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℝ, ∃ ρ₀ ρ₁ ρ₂ : Matrix (Fin 2) (Fin 2) ℂ,
    IsState ρ₀ ∧ IsState ρ₁ ∧ IsState ρ₂ ∧
      R.readout () ()
        (K * (Real.sqrt (QTD ρ₀ ρ₁) + Real.sqrt (QTD ρ₁ ρ₂)))
        (Real.sqrt (QTD ρ₀ ρ₂))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ₀, ρ₁, ρ₂, h₀, h₁, h₂, hbad⟩ := h 1
  exact hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh := congrFun he (1 : ℝ)
  change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at hh
  exact (lt_irrefl (1 : ℝ)) (Eq.mp hh (by norm_num))

def source_registration : Registration arena (type_of% @no_quasi_triangle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨no_quasi_triangle, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@no_quasi_triangle) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.QuantumTriangularMetricRefutation.no_quasi_triangle.__information_unit
  realizationName := `Reg.D5.S3.Divergence.QuantumTriangularMetricRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.QuantumTriangularMetricRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Divergence.QuantumTriangularMetricRefutation
