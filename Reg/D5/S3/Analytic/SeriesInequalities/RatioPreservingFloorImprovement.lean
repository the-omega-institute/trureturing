import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
open LeanInformationAudit Filter
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement

/-- The observed object is the complete candidate floor. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ → ℝ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ θ => θ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

private def testFloor (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

private theorem testFloor_positive (k : ℕ) : 0 < testFloor k := by
  unfold testFloor
  positivity

private theorem testFloor_antitone : Antitone testFloor := by
  apply antitone_nat_of_succ_le
  intro k
  unfold testFloor
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) (by norm_num)

private theorem testFloor_summable : Summable testFloor :=
  summable_geometric_of_abs_lt_one (by norm_num)

private theorem testFloor_ratio (k : ℕ) : testFloor k ≤ 2 * testFloor (k + 1) := by
  unfold testFloor
  rw [pow_succ]
  nlinarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (fun _ : ℕ => (0 : ℝ)) ≠ (fun _ : ℕ => (1 : ℝ))
  intro h
  have h0 := congrFun h 0
  norm_num at h0

def arena_1 : Arena where
  signature := signature
  Law F := ∀ {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1)) (hε : 0 < ε),
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < (F.readout () () θ) k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k)

private theorem rejected_law_1 : ¬ arena_1.Law rejected := by
  intro h
  obtain ⟨θ, hθpos, _⟩ := @h testFloor 2 1
    (by norm_num) testFloor_positive testFloor_antitone testFloor_summable
    testFloor_ratio (by norm_num)
  have hbad := hθpos 0
  change (0 : ℝ) < -1 at hbad
  norm_num at hbad

def family_1 : Registration arena_1 (type_of% (@exists_ratio_preserving_improvement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_ratio_preserving_improvement, rejected, rejected_law_1⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_1.Law actual rejected rejected_law_1
  dependence := actual_dependence

noncomputable def audit_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_ratio_preserving_improvement) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.exists_ratio_preserving_improvement_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.family_1
  realizationSource := none
  generated := false
  arena := .source ⟨arena_1⟩
  objectArena := .source ⟨arena_1⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_1 ⟨family_1⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms exists_ratio_preserving_improvement
#print axioms family_1
#print axioms audit_1

def arena_2 : Arena where
  signature := signature
  Law F := ∀ {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1))
    (hε : 0 < ε) (hεone : ε ≤ 1),
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < (F.readout () () θ) k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) ∧
      (∀ a sLo : ℝ, 0 < sLo → sLo ≤ a → ∀ H : ℝ, 1 ≤ H →
        ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, sLo ≤ s → s ≤ a →
          ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k ∧ w k ≤ 1) →
            powerProfile θ w s ≤
              max (ENNReal.ofReal C)
                (ENNReal.ofReal (H ^ (-sLo)) * powerProfile η w s))

private theorem rejected_law_2 : ¬ arena_2.Law rejected := by
  intro h
  obtain ⟨θ, hθpos, _⟩ := @h testFloor 2 1
    (by norm_num) testFloor_positive testFloor_antitone testFloor_summable
    testFloor_ratio (by norm_num) (by norm_num)
  have hbad := hθpos 0
  change (0 : ℝ) < -1 at hbad
  norm_num at hbad

def family_2 : Registration arena_2 (type_of% (@exists_uniform_profile_improvement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_profile_improvement, rejected, rejected_law_2⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_2.Law actual rejected rejected_law_2
  dependence := actual_dependence

noncomputable def audit_2 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_uniform_profile_improvement) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.exists_uniform_profile_improvement_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.family_2
  realizationSource := none
  generated := false
  arena := .source ⟨arena_2⟩
  objectArena := .source ⟨arena_2⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_2 ⟨family_2⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms exists_uniform_profile_improvement
#print axioms family_2
#print axioms audit_2

def arena_3 : Arena where
  signature := signature
  Law F := ∀ {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1))
    (hε : 0 < ε) (hεone : ε ≤ 1),
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < (F.readout () () θ) k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) ∧
      (∀ n : ℕ → ℝ, (∀ k, 1 ≤ n k) → ∀ a : ℝ, 0 < a →
        (∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile η n a u ≠ ⊤) →
          (∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile θ n a u ≠ ⊤) ∧
          (∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < (geometricProfile η n a u).toReal) ∧
          Tendsto (fun u => (geometricProfile θ n a u).toReal /
            (geometricProfile η n a u).toReal) (𝓝[>] (0 : ℝ)) (𝓝 0))

private theorem rejected_law_3 : ¬ arena_3.Law rejected := by
  intro h
  obtain ⟨θ, hθpos, _⟩ := @h testFloor 2 1
    (by norm_num) testFloor_positive testFloor_antitone testFloor_summable
    testFloor_ratio (by norm_num) (by norm_num)
  have hbad := hθpos 0
  change (0 : ℝ) < -1 at hbad
  norm_num at hbad

def family_3 : Registration arena_3 (type_of% (@exists_strict_profile_improvement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_strict_profile_improvement, rejected, rejected_law_3⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_3.Law actual rejected rejected_law_3
  dependence := actual_dependence

noncomputable def audit_3 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_strict_profile_improvement) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.exists_strict_profile_improvement_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement.family_3
  realizationSource := none
  generated := false
  arena := .source ⟨arena_3⟩
  objectArena := .source ⟨arena_3⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_3 ⟨family_3⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms exists_strict_profile_improvement
#print axioms family_3
#print axioms audit_3

end Reg.D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
