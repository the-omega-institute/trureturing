import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ → ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => replacement p.1 p.2.1 p.2.2 F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N - 2 →
    ∀ (a F : ℕ → ℝ) (ε c : ℝ), 0 ≤ ε → 0 ≤ c →
    (∑ m ∈ Ico N (2 * N), a m = 0) →
    (∑ m ∈ Ico N (2 * N), (m : ℝ) * a m = 0) →
    (∀ k ∈ Ico (q + 1) N, |F k - mobiusPrefix k| ≤ ε * (k : ℝ) + c) →
    |residual N a - R.readout () ⟨N, q, a⟩ F| ≤
      (ε + c / (q + 1 : ℕ)) / Real.log N * ((N : ℝ) * mass N a *
        (1 + 2 * Real.log ((N : ℝ) / (q + 1 : ℕ)) *
          (1 + Real.log (2 * (N : ℝ) / (q + 1 : ℕ))))) +
        (q + 1 : ℕ) * ((3 : ℝ) * (q : ℝ) / 2 + 2) * variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 3) (q := 1) (by norm_num) (by norm_num)
    (fun _ => 0) mobiusPrefix 0 0 le_rfl le_rfl (by simp) (by simp)
    (by intro k _; simp)
  norm_num [rejected, realize,
    _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual, mass, variation] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let a : ℕ → ℝ := fun m => if m = 3 then 1 else if m = 4 then -2
    else if m = 5 then 1 else 0
  refine ⟨⟨3, 1, a⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change replacement 3 1 a (fun _ => 0) ≠ replacement 3 1 a (fun _ => 1)
  have hb : Ico 3 6 = {3, 4, 5} := by decide
  have hh : Ico 2 3 = {2} := by decide
  have hl : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  norm_num [replacement, logDifference, logPair, floorPair, hb, hh, a]

def registration : Registration arena (type_of% @originalResidual_finite_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨originalResidual_finite_transfer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- The replacement readout observes F and retains the original theorem telescope. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@originalResidual_finite_transfer) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.originalResidual_finite_transfer.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p F => replacement p.1 p.2.1 p.2.2 F)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
