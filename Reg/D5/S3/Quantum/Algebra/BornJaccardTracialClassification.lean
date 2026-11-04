import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.BornJaccardTracialClassification
import Reg.Support.DependentFamily

/-! A source-bound offset-family audit of the complete native classification. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.BornJaccardTracialClassification
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification

abbrev Parameters := Σ n : ℕ, Matrix (Fin n) (Fin n) ℂ

abbrev signature : Signature where
  Params := Parameters
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (H p.1) → Submodule ℂ (H p.1) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p c => distance p.2.toEuclideanLin c) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_hn : 2 ≤ n)
    (rho : Matrix (Fin n) (Fin n) ℂ) (_hp : rho.PosDef) (_ht : Matrix.trace rho = 1)
    (c : ℝ) (_hc : 0 ≤ c),
    ((∀ X Y Z : Submodule ℂ (H n),
        R.readout () ⟨n, rho⟩ c X Z ≤
          R.readout () ⟨n, rho⟩ c X Y + R.readout () ⟨n, rho⟩ c Y Z) ↔
      rho = (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    (rho = (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) →
      ∃ m : MetricSpace (Submodule ℂ (H n)),
        ∀ X Z, @dist _ m.toDist X Z = R.readout () ⟨n, rho⟩ c X Z) ∧
    (∀ X Z : Submodule ℂ (H n), R.readout () ⟨n, rho⟩ c X Z = 0 ↔ X = Z)

private theorem scalar_two_pos : (((2 : ℂ)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  convert (Matrix.PosDef.one (R := ℂ) (n := Fin 2)).smul
    (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) using 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h (by omega) ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    scalar_two_pos (by norm_num [Matrix.trace, Matrix.smul_apply])
    0 (by norm_num)).2.2 (⊥ : Submodule ℂ (H 2)) ⊥
  have hz := hs.mpr rfl
  norm_num [rejected, realize] at hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)⟩, 0, 1, ?_⟩
  intro heq
  have h := congrFun (congrFun heq (⊥ : Submodule ℂ (H 2))) ⊤
  norm_num [actual, realize, distance, weight, projection,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.trace_one, Submodule.starProjection_top,
    ContinuousLinearMap.coe_id, LinearMap.id_comp, finrank_euclideanSpace, Fintype.card_fin,
    Module.End.mul_eq_comp, ← Module.End.one_eq_id, H] at h

def family : Registration arena (type_of% (@tracial_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tracial_classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tracial_classification) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.BornJaccardTracialClassification.tracial_classification.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.family
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
    (fun _ p c => distance p.2.toEuclideanLin c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.BornJaccardTracialClassification
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "fn", "fn" ]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification
