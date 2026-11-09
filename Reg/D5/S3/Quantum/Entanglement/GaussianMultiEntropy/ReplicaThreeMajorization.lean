import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete strict Schur comparison statement. -/

namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization

open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : Fin 3 → ℝ, Fin 3 → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p k => value k (p.1 0) (p.1 1) (p.1 2)) (fun e => nomatch e)

def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨fun _ => 1, fun _ => 1⟩, 1, 2, ?_⟩
  have h := (parameter_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  exact ne_of_gt h

abbrev comparisonArena : Arena where
  signature := signature
  Law R := ∀ (k : ℝ) (x y : Fin 3 → ℝ), 0 < k →
    (∀ i, 0 < x i) → (∀ i, 0 < y i) → moreMixed x y →
    R.readout () ⟨x, y⟩ k ≤ value k (y 0) (y 1) (y 2) ∧
      (value k (x 0) (x 1) (x 2) = value k (y 0) (y 1) (y 2) ↔
        ∃ σ : Equiv.Perm (Fin 3), x = y ∘ σ)

private theorem comparison_rejected : ¬ comparisonArena.Law oneReadout := by
  intro h
  have hm : moreMixed (fun _ : Fin 3 => (1 : ℝ)) (fun _ => 1) :=
    ⟨fun _ _ => le_rfl, rfl⟩
  have he := (h 1 (fun _ => 1) (fun _ => 1) (by norm_num)
    (by intro i; norm_num) (by intro i; norm_num) hm).1
  have hn := value_neg 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change 1 ≤ value 1 1 1 1 at he
  linarith

def comparisonFamily : Registration comparisonArena (type_of% @schur_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨schur_comparison, oneReadout, comparison_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    comparisonArena.Law actual oneReadout comparison_rejected
  dependence := actual_dependence

def comparisonAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@schur_comparison) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization.comparisonUnit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization.comparisonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k =>
    value k (p.1 0) (p.1 1) (p.1 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms comparisonAudit

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
