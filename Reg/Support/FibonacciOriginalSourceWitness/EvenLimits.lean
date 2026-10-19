import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetCodebook ResetFactors MemoryGraph ActualCountRateBridge
open Filter Topology

open EvenLengthAsymptotics LowerRateLimit
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)
namespace Reg.Support.FibonacciOriginalSourceWitness.EvenLimits
noncomputable section
namespace Floor
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization observationSignature := realize observationSignature
  (fun _ L v => (paddingCopies L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (L : ℕ) (positive : 0 < L) (evenL : Even L),
    Tendsto (fun v : ℕ => r.readout () L v) atTop (𝓝 (1 / (L : ℝ)))
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad : (0 : ℝ) = 1 / (2 : ℝ) :=
    tendsto_nhds_unique tendsto_const_nhds (h 2 (by decide) (by decide))
  norm_num at bad
def evidence : Registration sourceArena (type_of% @full_even_floor_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_even_floor_ratio, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, 40, ?_⟩
    norm_num [actual, realize, paddingCopies]
end Floor
namespace ContractRate
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : Ownership, Σ _ : ℝ, Σ _ : ℕ, Σ _ : Model, Contract)
    (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization observationSignature := realize observationSignature
  (fun _ p v => Real.logb 2 (contractCount p.2.2.2.1 p.1 p.2.1 p.2.2.2.2 (2 * v) : ℝ) /
    ((2 * v : ℕ) : ℝ)) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∀ (model : Model) (contract : Contract),
      Tendsto (fun v : ℕ => r.readout () ⟨o,b,K,model,contract⟩ v) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (contractCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ)) (fun v : ℕ => ((2 * v : ℕ) : ℝ))
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have zero : (0 : ℝ) = eta_b 2 budget := tendsto_nhds_unique tendsto_const_nhds
    (h (fun _ => false) budget 2 (by decide) budget_interval.1 budget_interval.2
      .original .strict).1
  have positive := (original_lower_rate_limit (fun _ => false) budget 2 (by decide)
    budget_interval.1 budget_interval.2).1
  rw [← zero] at positive
  norm_num at positive
def evidence : Registration sourceArena (type_of% @contract_even_raw_asymptotics) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contract_even_raw_asymptotics, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨(fun _ => false),budget,2,Model.original,Contract.strict⟩, 0, ?_⟩
    by_contra! same
    have zero : ∀ v : ℕ, actual.readout i
        ⟨(fun _ => false),budget,2,Model.original,Contract.strict⟩ v = 0 := by
      intro v
      rw [← same v]
      simp [actual, realize]
    have limit := (contract_even_raw_asymptotics (fun _ => false) budget 2 (by decide)
      budget_interval.1 budget_interval.2 .original .strict).1
    have limitZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (eta_b 2 budget)) := by
      convert limit using 1
      funext v
      exact (zero v).symm
    have eq : (0 : ℝ) = eta_b 2 budget :=
      tendsto_nhds_unique tendsto_const_nhds limitZero
    have positive := (original_lower_rate_limit (fun _ => false) budget 2 (by decide)
      budget_interval.1 budget_interval.2).1
    rw [← eq] at positive
    norm_num at positive
end ContractRate
namespace Reindexing
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Model (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization observationSignature := realize observationSignature
  (fun _ model v => observationOffset model + 2 * v) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model), Even (observationOffset model) ∧
    Tendsto (fun v : ℕ => r.readout () model v) atTop atTop ∧
    Tendsto (fun v : ℕ => v - observationOffset model / 2) atTop atTop ∧
    (∀ᶠ v : ℕ in atTop,
      observationOffset model + 2 * (v - observationOffset model / 2) = 2 * v)
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := (h .original).2.1.eventually (eventually_ge_atTop (1 : ℕ))
  obtain ⟨v, hv⟩ := bad.exists
  change 1 ≤ 0 at hv
  omega
def evidence : Registration sourceArena (type_of% @observation_even_reindexing) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@observation_even_reindexing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨Model.original, 0, 1, ?_⟩
    change observationOffset Model.original + 2 * 0 ≠ observationOffset Model.original + 2 * 1
    omega
end Reindexing
end
end Reg.Support.FibonacciOriginalSourceWitness.EvenLimits
