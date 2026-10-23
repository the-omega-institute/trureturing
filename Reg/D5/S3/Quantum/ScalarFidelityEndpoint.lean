import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.ScalarFidelityEndpoint
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

noncomputable section
namespace Reg.D5.S3.Quantum.ScalarFidelityEndpoint
open _root_.D5.S3.Quantum.ScalarFidelityEndpoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℝ), 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
    ((∀ A B C : ℝ, a ≤ A → A ≤ 1 → b ≤ B → B ≤ 1 → c ≤ C → C ≤ 1 →
      R.readout ⟨0, by decide⟩ ⟨b,c,A,B⟩ a ≤ R.readout ⟨1, by decide⟩ ⟨b,c,A,B⟩ C) ↔
      |a ^ 2 - b ^ 2| ≤ 1 - c ^ 2)

def actual : Realization signature := realize signature
  (fun i p s => if i = (⟨0, by decide⟩ : Fin 2) then scalarQuotient s p.1 p.2.1
    else scalarQuotient p.2.2.1 p.2.2.2 s)
  (fun e => nomatch e)

def rejectedLower : Realization signature := realize signature
  (fun i p s => if i = (⟨0, by decide⟩ : Fin 2) then 10 else scalarQuotient p.2.2.1 p.2.2.2 s)
  (fun e => nomatch e)

def rejectedUpper : Realization signature := realize signature
  (fun i p s => if i = (⟨0, by decide⟩ : Fin 2) then scalarQuotient s p.1 p.2.1 else -10)
  (fun e => nomatch e)

theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using lower_corner_dominance_iff

theorem rejected_lower_law : ¬ arena.Law rejectedLower := by
  intro h
  have hm := (h 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  have hbad := hm 1 1 0 le_rfl le_rfl le_rfl le_rfl le_rfl (by norm_num)
  norm_num [rejectedLower, realize, scalarQuotient] at hbad

theorem rejected_upper_law : ¬ arena.Law rejectedUpper := by
  intro h
  have hm := (h 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  have hbad := hm 1 1 0 le_rfl le_rfl le_rfl le_rfl le_rfl (by norm_num)
  norm_num [rejectedUpper, realize, scalarQuotient] at hbad

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedLower, rejected_lower_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      fin_cases i
      · refine ⟨rejectedLower, ?_, rfl, rejected_lower_law⟩
        intro j hj
        fin_cases j
        · exact False.elim (hj rfl)
        · rfl
      · refine ⟨rejectedUpper, ?_, rfl, rejected_upper_law⟩
        intro j hj
        fin_cases j
        · rfl
        · exact False.elim (hj rfl)
    · intro i; exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    fin_cases i
    · refine ⟨⟨1,0,1,1⟩, 1/2, 1, ?_⟩
      norm_num [actual, realize, scalarQuotient]
    · refine ⟨⟨1,0,1,1⟩, 0, 1, ?_⟩
      norm_num [actual, realize, scalarQuotient]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Quantum.ScalarFidelityEndpoint.lower_corner_dominance_iff)
    (type_of% (realize signature
      (fun i p s => if i = (⟨0, by decide⟩ : Fin 2) then scalarQuotient s p.1 p.2.1
        else scalarQuotient p.2.2.1 p.2.2.2 s)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.ScalarFidelityEndpoint.lower_corner_dominance_iff,
  realizationName := `Reg.D5.S3.Quantum.ScalarFidelityEndpoint.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun i p s => if i = (⟨0, by decide⟩ : Fin 2) then scalarQuotient s p.1 p.2.1
      else scalarQuotient p.2.2.1 p.2.2.2 s)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.ScalarFidelityEndpoint,
    definition := none, coordinates := #[1,2,9,10], readouts := #[
      { path := #[
          "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "fn", "arg", "body",
          "body", "body", "body", "body", "body", "body",
          "body", "body", "fn", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false },
      { path := #[
          "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "fn", "arg", "body",
          "body", "body", "body", "body", "body", "body",
          "body", "body", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Quantum.ScalarFidelityEndpoint
