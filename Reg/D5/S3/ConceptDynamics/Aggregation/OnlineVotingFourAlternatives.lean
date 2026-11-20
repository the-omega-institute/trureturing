import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives
import Reg.Support.DependentFamily

/-! Registration of the winner-cost readout for the prescribed-horizon lower bound. -/

namespace Reg.D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives

open _root_.D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives.Padding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

abbrev Parameters := Σ _ : ℕ, Σ α : Type, Rule α

abbrev signature : Signature where
  Params := Parameters
  State p := Election p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p e => cost e (winner p.2.2 e)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} {α : Type} (order : Order k α) (rule : Rule α),
    ∃ (e : Election k α) (best : α), e.order = order ∧
      (∀ a, cost e best ≤ cost e a) ∧ 0 < cost e best ∧
      (11753 / 3253 : ℝ) * cost e best ≤ R.readout () ⟨k, α, rule⟩ e ∧
      Real.sqrt 13 * cost e best < cost e (winner rule e)

private def exampleOrder : Order 0 (Fin 4) := finSumFinEquiv

private def exampleElection (x : ℝ) : Election 0 (Fin 4) where
  Space := ℝ
  metric := inferInstance
  voter _ := 0
  candidate _ := x
  order := exampleOrder
  rank _ a := a.val
  rank_injective _ := Fin.val_injective
  compatible _ _ _ h := (lt_irrefl _ h).elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, b, _, _, hpos, hle, _⟩ := h exampleOrder (fun _ _ => false)
  have hstrict := mul_pos (by norm_num : (0 : ℝ) < 11753 / 3253) hpos
  exact (not_le_of_gt hstrict) hle

def registration : Registration arena
    (∀ {k : ℕ} {α : Type} (order : Order k α) (rule : Rule α),
      ∃ (e : Election k α) (best : α), e.order = order ∧
        (∀ a, cost e best ≤ cost e a) ∧ 0 < cost e best ∧
        (11753 / 3253 : ℝ) * cost e best ≤ cost e (winner rule e) ∧
        Real.sqrt 13 * cost e best < cost e (winner rule e)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨worst_case, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim (α := Unit) j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, Fin 4, fun _ _ => false⟩, exampleElection 0, exampleElection 1, ?_⟩
    change (∑ _ : Fin 12, dist (0 : ℝ) 0) ≠ (∑ _ : Fin 12, dist (1 : ℝ) 0)
    norm_num [Real.dist_eq]

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@worst_case)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives.worst_case
    "__information_unit"
  realizationName := `Reg.D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p e => cost e (winner p.2.2 e)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true }
  ]

#print axioms registration

end

end Reg.D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives
