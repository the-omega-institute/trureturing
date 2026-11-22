import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue
import Reg.Support.DependentFamily

/-! Source-bound audit of classical winning probability on the full simplex. -/

namespace Reg.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue

open _root_.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℝ
  State q := Convexity.StdSimplex ℝ (Strategy q.1 q.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q μ => mixedWin q.2.2 μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The same value, attainment, and normalization assertions with a variable mixed readout. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n m : ℕ) (p : ℝ), 2 ≤ m → m < n → 0 < p →
    p < (2 : ℝ) / ((m : ℝ) + 2) →
    let t := tParam n p
    let lam := 1 + t
    let d := m - 2
    let s := commonSize n d t
    let score₁ := lam * (n : ℝ) - (B m n : ℝ)
    let score₂ := lam * (s : ℝ) - (B d s : ℝ)
    IsGreatest (Set.range (r.readout () ⟨n, m, p⟩))
      (probability n p (max score₁ score₂)) ∧
    (∃ σ τ : Strategy n m, detScore t σ = score₁ ∧ detScore t τ = score₂) ∧
    (∑ xy : Fin n × Fin n, inputWeight p xy) = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ, hμ⟩ := (h 3 2 (1 / 4) (by decide) (by decide) (by norm_num) (by norm_num)).1.1
  have hz : commonSize 3 (2 - 2) (tParam 3 (1 / 4 : ℝ)) = 0 := by simp [commonSize]
  change (0 : ℝ) = probability 3 (1 / 4)
    (max ((1 + tParam 3 (1 / 4)) * 3 - B 2 3)
      ((1 + tParam 3 (1 / 4)) * (commonSize 3 (2 - 2) (tParam 3 (1 / 4)) : ℝ) -
        B (2 - 2) (commonSize 3 (2 - 2) (tParam 3 (1 / 4))))) at hμ
  rw [hz] at hμ
  have hscore : max ((1 + tParam 3 (1 / 4)) * 3 - B 2 3)
      ((1 + tParam 3 (1 / 4)) * (0 : ℝ) - B (2 - 2) 0) = 0 := by
    norm_num [tParam, B]
  rw [Nat.cast_zero, hscore] at hμ
  simp only [probability, mul_zero, add_zero] at hμ
  norm_num at hμ

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let σ : Strategy 3 2 := (fun _ => 0, fun _ => 0)
  let τ : Strategy 3 2 := (fun _ => 0, fun _ => 1)
  refine ⟨⟨3, 2, 1 / 4⟩, Convexity.StdSimplex.single σ, Convexity.StdSimplex.single τ, ?_⟩
  change mixedWin (1 / 4) (Convexity.StdSimplex.single σ) ≠
    mixedWin (1 / 4) (Convexity.StdSimplex.single τ)
  have evaluate (ρ : Strategy 3 2) :
      mixedWin (1 / 4) (Convexity.StdSimplex.single ρ) = detWin (1 / 4) ρ := by
    classical
    unfold mixedWin
    rw [Finset.sum_eq_single ρ]
    · simp
    · intro a _ ha
      simp [Finsupp.single_eq_of_ne ha]
    · simp
  rw [evaluate, evaluate]
  simp only [detWin, Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num [inputWeight, σ, τ]

def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue.source_registration
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
    (realize signature (fun _ q μ => mixedWin q.2.2 μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Information.ColoringGames.BolducJenningsClassicalValue
