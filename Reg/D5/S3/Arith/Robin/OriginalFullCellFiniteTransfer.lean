import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer

open _root_.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (variation)
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
    (∀ m ∈ Ico N (2 * N), 0 ≤ a m) →
    (∀ k ∈ Ico (q + 1) N, |F k - mobiusPrefix k| ≤ ε * (k : ℝ) + c) →
    |pairing N a - R.readout () ⟨N, q, a⟩ F - meanCorrection N q a| ≤
      (ε + c / (q + 1 : ℕ)) / Real.log N * ((N : ℝ) * totalMass N a *
        (1 + 2 * Real.log ((N : ℝ) / (q + 1 : ℕ))^2 +
          2 * Real.log ((N : ℝ) / (q + 1 : ℕ)) *
          (1 + Real.log (2 * (N : ℝ) / (q + 1 : ℕ))))) +
        (q + 1 : ℕ) * ((3 : ℝ) * (q : ℝ) / 2 + 2) * variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 3) (q := 1) (by norm_num) (by norm_num)
    (fun _ => 0) mobiusPrefix 0 0 le_rfl le_rfl (by intro m _; exact le_rfl)
    (by intro k _; simp)
  norm_num [rejected, realize,
    _root_.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.pairing, totalMass, variation, meanCorrection] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let a : ℕ → ℝ := fun m => if m = 3 then 1 else 0
  refine ⟨⟨3, 1, a⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change replacement 3 1 a (fun _ => 0) ≠ replacement 3 1 a (fun _ => 1)
  have hb : Ico 3 6 = {3, 4, 5} := by decide
  have hh : Ico 2 3 = {2} := by decide
  have hl : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  norm_num [replacement, logDifference, logPair, fracPair, hb, hh, a]

def registration : Registration arena (type_of% @originalFullCell_finite_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨originalFullCell_finite_transfer, rejected, rejected_law⟩
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
    (@originalFullCell_finite_transfer) (Realization signature) Type Unit where
  unitName := `OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.registration
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
    owner := `D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
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

namespace Sharp

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N - 2 →
    ∀ (a F : ℕ → ℝ) (ε c : ℝ), 0 ≤ ε → 0 ≤ c →
    (∀ m ∈ Ico N (2 * N), 0 ≤ a m) →
    (∀ k ∈ Ico (q + 1) N, |F k - mobiusPrefix k| ≤ ε * (k : ℝ) + c) →
    |pairing N a - R.readout () ⟨N, q, a⟩ F - meanCorrection N q a| ≤
      (ε + c / (q + 1 : ℕ)) / Real.log N * ((N : ℝ) * totalMass N a *
        (1 + 2 * Real.log ((N : ℝ) / (q + 1 : ℕ))^2 +
          2 * Real.log ((N : ℝ) / (q + 1 : ℕ)) *
          (1 + Real.log (2 * (N : ℝ) / (q + 1 : ℕ))))) +
        (if q = 0 then 0 else (q + 1 : ℕ) * ((3 : ℝ) * (q : ℝ) / 2 + 2) * variation N a / 16)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 3) (q := 1) (by norm_num) (by norm_num)
    (fun _ => 0) mobiusPrefix 0 0 le_rfl le_rfl (by intro m _; exact le_rfl)
    (by intro k _; simp)
  norm_num [rejected, realize,
    _root_.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.pairing, totalMass, variation, meanCorrection] at he


def registration : Registration arena (type_of% @originalFullCell_finite_transfer_sharp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨originalFullCell_finite_transfer_sharp, rejected, rejected_law⟩
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
    (@originalFullCell_finite_transfer_sharp) (Realization signature) Type Unit where
  unitName := `OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer_sharp.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.Sharp.registration
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
    owner := `D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
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

end Sharp

end
end Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
