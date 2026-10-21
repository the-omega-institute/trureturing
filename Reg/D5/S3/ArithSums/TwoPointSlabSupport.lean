import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.TwoPointSlabSupport
import Reg.Support.DependentFamily

open Set
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ArithSums.TwoPointSlabSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ArithSums.TwoPointSlabSupport
noncomputable section

abbrev Parameters := ℝ × ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)

abbrev signature : Signature where
  Params := Parameters
  State _ := Fin 3 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x => (∑ i, x i) / 3) (fun e => nomatch e)

abbrev conclusion (T M₀ M₁ : ℝ) (c d x : Fin 3 → ℝ) (m : ℝ) : Prop :=
    let δ := fun i => pairDistance (Icc (M₀ / 3) (M₁ / 3)) (c i) (d i)
    let V := ∑ i, δ i ^ 2
    let ρ := Real.sqrt (V / 6)
    m ∈ Icc (M₀ / 3) (M₁ / 3) ∧
    (∀ i, 0 ≤ x i - T) ∧
    V ≤ ∑ i, (x i - m) ^ 2 ∧
    (∑ i, (x i - m) ^ 2) = (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ∧
    (∑ i, (x i - T) ^ 2) - 3 * (m - T) ^ 2 ≤ 6 * (m - T) ^ 2 ∧
    0 ≤ ρ ∧ ρ ≤ m - T ∧ m - T ≤ M₁ / 3 - T

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T M₀ M₁ : ℝ) (c d x : Fin 3 → ℝ),
    (∀ i, T ≤ c i) → (∀ i, T ≤ d i) →
    IsCorner c d x → (∑ i, x i) ∈ Icc M₀ M₁ →
    conclusion T M₀ M₁ c d x (R.readout () (T,M₀,M₁,c,d) x)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

theorem bridge : (type_of% (@corner_estimate)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := by
  exact corner_estimate

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by simp [IsCorner]) (by simp)
  have hm := hb.1
  norm_num [rejected,realize] at hm

def evidence : Registration arena (type_of% (@corner_estimate)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(0,0,3,(fun _ => 0),(fun _ => 1)),(fun _ => 0),(fun _ => 1),?_⟩
    norm_num [actual,realize]

def registration_corner_estimate : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@corner_estimate)
    (type_of% (realize signature (fun _ _ x => (∑ i, x i)/3) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.TwoPointSlabSupport.corner_estimate.information_unit,
  realizationName := `Reg.D5.S3.ArithSums.TwoPointSlabSupport.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => (∑ i, x i)/3) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ArithSums.TwoPointSlabSupport,
    definition := none,
    coordinates := #[0,1,2,3,4],
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "body","body","body","body","value"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration_corner_estimate
end
end Reg.D5.S3.ArithSums.TwoPointSlabSupport
