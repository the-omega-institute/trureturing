import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.GaussianEntropy
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.GaussianEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Subentropy.GaussianEntropy
universe u
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.negMulLog x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.negMulLog x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1),
    let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
    let X := fun (z : (ι × Fin 2) → ℝ) (i : ι) => ((z (i,0))^2 + (z (i,1))^2)/2
    let a := fun z => ∑ i, p i * X z i
    Integrable (fun z => Real.negMulLog (a z) - ∑ i, p i * Real.negMulLog (X z i)) γ ∧
      matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
        ∫ z, (R.readout () () (a z) - ∑ i, p i * Real.negMulLog (X z i)) ∂γ
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := (@h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 1)
    (fun _ => by norm_num) (by simp)).2
  have ht := (@diagonal_subentropy_gaussian_gap (ULift.{u} Unit) inferInstance inferInstance
    (fun _ => 1) (fun _ => by norm_num) (by simp)).2
  simp [rejected, realize] at hb
  simp at ht
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.exp 1, ?_⟩
  simp [actual, realize, Real.negMulLog, (Real.exp_pos 1).ne']
def source_registration : Registration arena.{u} (type_of% @diagonal_subentropy_gaussian_gap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_subentropy_gaussian_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@diagonal_subentropy_gaussian_gap.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianEntropy.diagonal_subentropy_gaussian_gap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianEntropy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.negMulLog x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Subentropy.GaussianEntropy
