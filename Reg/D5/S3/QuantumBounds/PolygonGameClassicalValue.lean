import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.PolygonGameClassicalValue
import Reg.Support.SingleDependentReadout

/-! Source-bound winning-probability registration for the odd polygon game. -/

namespace Reg.D5.S3.QuantumBounds.PolygonGameClassicalValue

open _root_.D5.S3.QuantumBounds.PolygonGameClassicalValue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe winning probability over every weight function, without restricting the state. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun P => (Fin P → Bool → Bool × Bool × Bool) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ P μ => winProbability P μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the upper bound's hypotheses and the complete deterministic attainment clause. -/
abbrev arena : Arena where
  signature := signature
  Law R := by
    classical
    exact ∀ P : ℕ, Odd P → 3 ≤ P →
    (∀ μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ,
      (∀ s, 0 ≤ μ s) → ∑ s, μ s = 1 →
      R.readout () P μ ≤ 1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P) ∧
    ∃ s : Fin P → Bool → Bool × Bool × Bool,
      ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P =
        1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let s : Fin 3 → Bool → Bool × Bool × Bool := fun _ _ => (false, false, false)
  let μ : (Fin 3 → Bool → Bool × Bool × Bool) → ℝ :=
    fun t => if t = s then 1 else 0
  have hb := (h 3 (by decide) (by decide)).1 μ
    (by intro t; dsimp [μ]; split <;> norm_num) (by simp [μ])
  norm_num [rejected, realize, Nat.fib] at hb

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  obtain ⟨s, hs⟩ := (result 3 (by decide) (by decide)).2
  let μ : (Fin 3 → Bool → Bool × Bool × Bool) → ℝ :=
    fun t => if t = s then 1 else 0
  refine ⟨3, (fun _ => 0), μ, ?_⟩
  dsimp only [actual, realize]
  have hz : winProbability 3 (fun _ => 0) = 0 := by simp [winProbability]
  have hd : winProbability 3 μ =
      ((Finset.univ.filter (wins 3 s)).card : ℝ) / 2 ^ 3 := by
    simp [winProbability, μ, ite_div]
  rw [hz, hd, hs]
  norm_num [Nat.fib]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.PolygonGameClassicalValue.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.PolygonGameClassicalValue.unit
  realizationName := `Reg.D5.S3.QuantumBounds.PolygonGameClassicalValue.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ P μ => winProbability P μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.PolygonGameClassicalValue
    definition := some {
      owner := `D5.S3.QuantumBounds.PolygonGameClassicalValue
      name := `D5.S3.QuantumBounds.PolygonGameClassicalValue.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.PolygonGameClassicalValue
