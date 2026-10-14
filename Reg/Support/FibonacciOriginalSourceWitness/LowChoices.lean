import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetCodebook ResetFactors MemoryGraph ActualCountRateBridge
open Filter Topology

open LowerRateLimit
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)
namespace Reg.Support.FibonacciOriginalSourceWitness.LowChoices
noncomputable section
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun q => Fin q → Bool) (fun _ => List Return)
def actual : Realization observationSignature := realize observationSignature
  (fun _ q z => lowChoices (q := q) z) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) (q : ℕ),
    Function.Injective (r.readout () q) ∧
    Function.Injective (fun z : Fin q → Bool => history model (lowChoices z)) ∧
    (∀ z : Fin q → Bool, listWeight (lowChoices z) = q * 58 ∧
      ActualPairSupply model o b .strict (lowChoices z)) ∧
    (∀ strict : Bool,
      2 ^ q ≤ actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (q * 58))
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have inj : Function.Injective (rejected.readout () 1) :=
    (h .original (fun _ => false) budget 2 (by decide) budget_interval.1 budget_interval.2 1).1
  have eq : (fun _ : Fin 1 => false) = (fun _ => true) := inj rfl
  have bad := congrFun eq 0
  cases bad
def evidence : Registration sourceArena (type_of% @actual_low_choice_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_low_choice_count, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
    intro same
    change lowChoices (q := 1) (fun _ => false) = lowChoices (q := 1) (fun _ => true) at same
    have inj : Function.Injective (lowChoices (q := 1)) :=
      (actual_low_choice_count .original (fun _ => false) budget 2 (by decide)
        budget_interval.1 budget_interval.2 1).1
    have eq := inj same
    have bad := congrFun eq 0
    cases bad
end
end Reg.Support.FibonacciOriginalSourceWitness.LowChoices
