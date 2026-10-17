import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment

open _root_.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
open _root_.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (centered variation)
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

namespace FullPositiveTransfer

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => lowError p.1 p.2 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N-2 → ∀ (b : ℕ → ℝ),
    (|R.readout () ⟨N,q⟩ b| ≤ pairedCoefficient N q*variation N b/Real.log N) ∧
      ∀ (F : ℕ → ℝ) (ε c : ℝ), 0 ≤ ε → 0 ≤ c →
      (∀ m ∈ Ico N (2*N), 0 ≤ b m) →
      (∀ k ∈ Ico (q+1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) →
      |pairing N b-replacement N q b F-meanCorrection N q b| ≤
        (ε+c/(q+1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
          (1+2*Real.log ((N : ℝ)/(q+1 : ℕ))^2+
            2*Real.log ((N : ℝ)/(q+1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q+1 : ℕ)))))+
        pairedCoefficient N q*variation N b/Real.log N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (N := 3) (q := 0) (by norm_num) (by norm_num) (fun _ => 0)).1
  norm_num [rejected, realize, variation] at he

def registration : Registration arena (type_of% @full_positive_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_positive_transfer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let b : ℕ → ℝ := fun m => if m = 3 then 1 else 0
    refine ⟨⟨3,1⟩, (fun _ => 0), b, ?_⟩
    change lowError 3 1 (fun _ => 0) ≠ lowError 3 1 b
    have hi : Ico 3 6 = {3,4,5} := by decide
    have hj : Ioc 0 1 = {1} := by decide
    have hz : lowError 3 1 (fun _ => 0) = 0 := by
      simp [lowError, centeredLogPair, centeredPair]
    have hb : lowError 3 1 b = -(3*(Real.log ((3 : ℝ)/2)*(1/4)))/Real.log 3 := by
      norm_num [lowError, centeredLogPair, centeredPair, centered, mobiusPrefix, hi, hj, b]
      <;> ring
    have hl : 0 < Real.log ((3 : ℝ)/2) := Real.log_pos (by norm_num)
    have hL : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    rw [hz, hb]
    have hn : -(3*(Real.log ((3 : ℝ)/2)*(1/4)))/Real.log 3 < 0 := by
      apply div_neg_of_neg_of_pos _ hL
      have hp : 0 < 3*(Real.log ((3 : ℝ)/2)*(1/4)) := by positivity
      linarith
    exact (ne_of_lt hn).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_positive_transfer) (Realization signature) Type Unit where
  unitName := `DyadicLowPayment.full_positive_transfer.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment.FullPositiveTransfer.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => lowError p.1 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end FullPositiveTransfer

namespace CoefficientSaving

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N q => pairedCoefficient N q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ N q => termwiseCoefficient N q+1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N-2 → 6 ≤ q →
    R.readout () N q < termwiseCoefficient N q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 8) (q := 6) (by norm_num) (by norm_num) (by norm_num)
  change termwiseCoefficient 8 6+1 < termwiseCoefficient 8 6 at he
  linarith

def registration : Registration arena (type_of% @coefficient_saving) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coefficient_saving, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨3, 0, 1, ?_⟩
    change pairedCoefficient 3 0 ≠ pairedCoefficient 3 1
    have hj : Ioc 0 1 = {1} := by decide
    have hp0 : pairs 0 = ∅ := by simp [pairs]
    have hp1 : pairs 1 = ∅ := by norm_num [pairs, hj]
    have hu0 : unpaired 0 = ∅ := by simp [unpaired, hp0]
    have hu1 : unpaired 1 = {1} := by simp [unpaired, hp1, hj]
    have hc0 : pairedCoefficient 3 0 = 0 := by
      simp [pairedCoefficient, hp0, hu0, boundaryPrice, singlePrice]
    have hc1 : pairedCoefficient 3 1 = 3*(Real.log ((3 : ℝ)/2)*2/16) := by
      norm_num [pairedCoefficient, hp1, hu1, boundaryPrice, singlePrice, mobiusPrefix, hj]
    rw [hc0, hc1]
    have hl : 0 < Real.log ((3 : ℝ)/2) := Real.log_pos (by norm_num)
    apply ne_of_lt
    positivity

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_saving) (Realization signature) Type Unit where
  unitName := `DyadicLowPayment.coefficient_saving.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment.CoefficientSaving.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N q => pairedCoefficient N q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CoefficientSaving


end
end Reg.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
