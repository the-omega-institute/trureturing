import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict Bayesian feedback advantage. -/

namespace Reg.D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage

open _root_.D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the strict relation between the Markovian bound and the Bayesian fidelity. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Preserve both feedback clauses and every Kraus-decomposition constraint. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (m₁ m₂ : ℕ) (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
      (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ),
      IsKrausDecomposition k₁ → IsKrausDecomposition k₂ →
        markovFidelity k₁ k₂ ≤ 1 / 2) ∧
    (∃ l₁ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
      ∃ l₂ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
      IsKrausDecomposition l₁ ∧ IsKrausDecomposition l₂ ∧
        R.readout () () (1 / 2) (bayesFidelity l₁ l₂))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, l₁, l₂, _, _, hfalse⟩
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  have hpos : (0 : ℝ) < 1 := by norm_num
  exact (lt_irrefl (1 : ℝ)) (Eq.mp he hpos)

def source_registration : Registration arena (type_of% (@result)) where
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
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
