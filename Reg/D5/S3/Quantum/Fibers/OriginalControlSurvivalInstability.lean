import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
import Reg.Support.DependentFamily

/-! Dependent-family escape evidence for the explicit original-control construction. -/

open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.OriginalControlComposition
open D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter Topology MeasureTheory
namespace Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance] Classical.propDecidable

def signature : Signature where
  Params := ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ c n => height c n) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => (fun _ : ℝ => (0 : ℝ))) (fun e => nomatch e)
def familyHeight (R : Realization signature) (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  R.readout () c n t

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1 / 4 : ℝ),(1 : ℕ),(2 : ℕ),?_⟩
  intro he
  have ht := congrFun he (1 / 2 : ℝ)
  norm_num [actual,realize,height,triangle,tent,Finset.sum_range_succ] at ht

def constructionArena : Arena where
  signature := signature
  Law R := ∀ (c phase : ℝ) (n : ℕ) (_hc : 0 < c) (_hc' : c < 1 / 2) (_hn : 1 ≤ n),
    ValidBase (doubleWall c) ∧
    OriginalControl (doubleWall c) 1 (familyHeight R c n) (fun _ => phase) ∧
    FiniteC1Control 1 (familyHeight R c n) (fun _ => phase) ∧
    (AbsolutelyContinuousOnInterval (familyHeight R c n) 0 1 ∧
      AbsolutelyContinuousOnInterval (fun _ : ℝ => phase) 0 1) ∧
    (familyHeight R c n 0 = c / 2 ∧ familyHeight R c n 1 = c / 2) ∧
    (∀ j < n,
      (∀ t ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1 / 2) / n), triangle c n t = c / 2 * (t - (j : ℝ) / n)) ∧
      (∀ t ∈ Icc (((j : ℝ) + 1 / 2) / n) (((j : ℝ) + 1) / n), triangle c n t = c / 2 * (((j : ℝ) + 1) / n - t))) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, c / 4 ≤ familyHeight R c n t ∧ familyHeight R c n t ≤ c / 2 ∧
      |familyHeight R c n t - c / 2| ≤ c / (4 * n)) ∧
    (0 < min (c / 4) (1 - 2 * c) ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin 5,
      min (c / 4) (1 - 2 * c) ≤ probability (doubleWall c) (familyHeight R c n t) i) ∧
    LipschitzOnWith (Real.toNNReal (3 * c / 4)) (familyHeight R c n) (Icc (0 : ℝ) 1) ∧
    eVariationOn (fun _ : ℝ => phase) (Icc (0 : ℝ) 1) = 0 ∧
    eVariationOn (familyHeight R c n) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (3 * c / 4) ∧
    (∀ t : ℝ, deriv (fun _ : ℝ => phase) t = 0) ∧
    (IntervalIntegrable (fun t : ℝ => Real.sqrt
      ((deriv (familyHeight R c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2)) volume 0 1 ∧
      IntervalIntegrable (fun t : ℝ =>
        (deriv (familyHeight R c n) t)^2 + (deriv (fun _ : ℝ => phase) t)^2) volume 0 1 ∧
      coordinateLength (familyHeight R c n) (fun _ => phase) ≤ 3 * c / 4 ∧
      quadraticCost (familyHeight R c n) (fun _ => phase) ≤ 9 * c^2 / 16) ∧
    (∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      hazard c (familyHeight R c n) t = 1 / (2 - t) ∧ |deriv (familyHeight R c n) t| ≤ 3 * c / 4) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, IntervalIntegrable (hazard c (familyHeight R c n)) volume 0 t ∧
      survival c (familyHeight R c n) t = 1 - t / 2) ∧
    OriginalControl (doubleWall c) 1 (fun _ => c / 2) (fun _ => phase) ∧
    (∀ t : ℝ, hazard c (fun _ => c / 2) t = 0 ∧ survival c (fun _ => c / 2) t = 1)

private theorem rejected_construction : ¬ constructionArena.Law rejected := by
  intro h
  rcases h (1 / 4) 0 1 (by norm_num) (by norm_num) (by norm_num) with ⟨-, -, -, -, he, -⟩
  norm_num [familyHeight, rejected, realize] at he

def construction_evidence : Registration constructionArena (type_of% (@oscillatory_original_controls)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨oscillatory_original_controls, rejected, rejected_construction⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_construction⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := actual_dependence

def discontinuityArena : Arena where
  signature := signature
  Law R := ∀ (c phase : ℝ) (_hc : 0 < c) (_hc' : c < 1 / 2),
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N,
      OriginalControl (doubleWall c) 1 (familyHeight R c n) (fun _ => phase) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |familyHeight R c n t - c / 2| < e) ∧
    (∀ n : ℕ, 1 ≤ n →
      |survival c (familyHeight R c n) 1 - survival c (fun _ => c / 2) 1|=1 / 2) ∧
    ¬ Tendsto (fun n : ℕ => survival c (familyHeight R c (n + 1)) 1) atTop
      (𝓝 (survival c (fun _ => c / 2) 1))

private theorem rejected_discontinuity : ¬ discontinuityArena.Law rejected := by
  intro h
  obtain ⟨N, -, hN⟩ := (h (1 / 4) 0 (by norm_num) (by norm_num)).1
    (1 / 16) (by norm_num)
  have he := (hN N le_rfl).2 0 (by constructor <;> norm_num)
  norm_num [familyHeight, rejected, realize] at he

def discontinuity_evidence : Registration discontinuityArena (type_of% (@uniform_height_survival_discontinuity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_height_survival_discontinuity, rejected, rejected_discontinuity⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_discontinuity⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := actual_dependence

def construction_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@oscillatory_original_controls) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability.construction_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability.construction_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨constructionArena⟩
  objectArena := .source ⟨constructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source constructionArena ⟨construction_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c n => height c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def discontinuity_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_height_survival_discontinuity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability.discontinuity_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability.discontinuity_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨discontinuityArena⟩
  objectArena := .source ⟨discontinuityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source discontinuityArena ⟨discontinuity_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c n => height c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","body","body","arg","body",
        "arg","body","body","fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability
