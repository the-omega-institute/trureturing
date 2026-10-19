import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open EvenLengthAsymptotics LowerRateLimit ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval budgetLower budgetUpper)
open Filter Topology

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

/-- The selected occurrence is the full history count at the actual departure offset. -/
abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Model, Σ _ : Ownership, Σ _ : ℝ, Contract
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature
    (fun _ p T => historyImageCount p.1 p.2.1 p.2.2.1 p.2.2.2
      (observationOffset p.1 + T)) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Every original premise and every unselected source, count and error clause is retained. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership)
    (b : ℝ) (contract : Contract) (T K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    Finite (ObservedContractDictionary model o b contract (observationOffset model + T)) ∧
    r.readout () ⟨model, o, b, contract⟩ T =
      contractCount model o b contract T ∧
    (∀ side : Side, sourceImageCount side model o b contract (observationOffset model + T) =
      contractCount model o b contract T) ∧
    sourcePairImageCount model o b contract (observationOffset model + T) =
      contractCount model o b contract T ∧
    contractCount model o b contract T =
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) T ∧
    (∀ xs : ObservedContractDictionary model o b contract (observationOffset model + T),
      listWeight xs.val = T ∧
      ∀ side : Side,
        (observedPrefix side model xs.val).length = observationOffset model + T ∧
        OperationRecord o b contract (source side model xs.val)
          (OperationPairedRecord model o xs.val side) ∧
        OperationFiniteSource (source side model xs.val) ∧
        (∀ p, source side model xs.val (observationOffset model + T + p) =
          address (tailPrefix side) p) ∧
        (∃ err : ℕ → ℝ, ErrorBound b contract err ∧
          (∀ p (hp : p < observationOffset model + T),
            observe o (coordinate (sourcePrefix side model xs.val) p) (err p) =
              (history model xs.val)[p]'(by rw [xs.property.2]; exact hp)) ∧
          (∀ p, observationOffset model + T ≤ p → err p = 0) ∧
          (∀ p, observe o (coordinate (sourcePrefix side model xs.val)
              (observationOffset model + T + p)) (err (observationOffset model + T + p)) =
            observe o (coordinate (tailPrefix side) p) 0)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have changed := (h .original (fun _ => false) budget .strict 78 2 (by decide)
    budget_interval.1 budget_interval.2).2.1
  change 0 = contractCount .original (fun _ => false) budget .strict 78 at changed
  have positive := ((even_actual_positivity (fun _ => false) budget 2 (by decide)
    budget_interval.1 budget_interval.2 78 (by decide) le_rfl).2.1 .original .strict).2
  omega

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_count_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.actual_observation_count_correspondence,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨Model.original, (fun _ => false), budget, Contract.strict⟩, 1, 78, ?_⟩
    change historyImageCount .original (fun _ => false) budget .strict
        (observationOffset .original + 1) ≠
      historyImageCount .original (fun _ => false) budget .strict
        (observationOffset .original + 78)
    have one := (actual_observation_count_correspondence .original (fun _ => false)
      budget .strict 1 2 (by decide) budget_interval.1 budget_interval.2).2.1
    have many := (actual_observation_count_correspondence .original (fun _ => false)
      budget .strict 78 2 (by decide) budget_interval.1 budget_interval.2).2.1
    rw [one, many, (odd_actual_counts 1 (by decide)).2]
    exact Nat.ne_of_lt (((even_actual_positivity (fun _ => false) budget 2 (by decide)
      budget_interval.1 budget_interval.2 78 (by decide) le_rfl).2.1 .original .strict).2)

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.ObservedCountCorrespondence
