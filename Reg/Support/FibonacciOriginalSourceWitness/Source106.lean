import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.Support.FibonacciFactorWitnesses
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
open Filter
open scoped Topology
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit (budget budget_interval)

namespace Reg.Support.FibonacciOriginalSourceWitness.Source106
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Return) (fun _ => ℕ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ R => R.r) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, r.readout () () R = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      ∀ model : Model, ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
        (∀ j, 0 < N j ∧ 1 ≤ actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false (N j)) ∧
        Tendsto (fun j => Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false
            (N j) : ℝ) /
          (N j : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        Tendsto (fun j => (N j : ℝ) / ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 1) ∧
        Tendsto (fun j => Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false
            (N j) : ℝ) /
          ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        (∀ j, FixedCodebook R o b K model (N j))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, bad, _⟩ := h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  norm_num [rejected, realize] at bad

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), ⟨1,1,by decide,by decide⟩, ⟨1,2,by decide,by decide⟩, ?_⟩
  norm_num [actual, realize]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_count_codebook_approximation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.original_count_codebook_approximation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source106
