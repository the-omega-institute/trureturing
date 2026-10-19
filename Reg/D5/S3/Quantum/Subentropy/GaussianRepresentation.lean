import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.GaussianRepresentation
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open _root_.D5.S3.Quantum.Subentropy.GaussianRepresentation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Subentropy.GaussianRepresentation
universe u
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x⁻¹) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x⁻¹ + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s),
    (∫ z : (ι × Fin 2) → ℝ,
      Real.exp (∑ j, -(s * p j.1) * (z j)^2 / 2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) =
      ∏ i, R.readout () () (1 + s * p i)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv := @h (ULift.{u} Unit) inferInstance (fun _ => 0)
    (fun _ => by norm_num) 0 (by norm_num)
  norm_num [rejected, realize] at hv
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]
def source_registration : Registration arena.{u} (type_of% @diagonal_gaussian_laplace.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_gaussian_laplace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@diagonal_gaussian_laplace.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianRepresentation.diagonal_gaussian_laplace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianRepresentation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianRepresentation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Subentropy.GaussianRepresentation
