/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five gain preorders induce weak Pareto dominance on actions. -/

import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Order.Defs.PartialOrder

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'D5\\.S3\\.ConceptDynamics\\.DefinitionEscape\\.Adjudication|
     paretoWeak|pareto_weak|GainVector|lifecycleCost|residualCapture|five.*coordinate|
     weak.*domin.*reflex|weak.*domin.*trans' D5 --glob '*.lean'` found no
     declaration of this gain vector, weak Pareto relation, or its order laws.
   * `rg -n -i 'pareto|GainVector|lifecycleCost|residualCapture|Reflexive.*Transitive|
     IsRefl.*IsTrans' .lake/packages/mathlib/Mathlib --glob '*.lean'` found the
     unrelated Pareto probability distribution and generic relation/order
     infrastructure, but no heterogeneous five-coordinate dominance theorem.
   * `IncomparableRepairCosts.incomparable_repairs_no_unique_choice` is about
     two concrete minimal cost receipts. It neither defines the atom's five
     gain coordinates nor supplies the general reflexivity/transitivity law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- The five heterogeneous absolute coordinates used to compare adjudication
actions. Information, residual capture, and transfer are benefits; lifecycle
cost and risk are burdens. -/
structure GainVector
    (Information Residual Transfer Cost Risk : Type u) where
  information : Information
  residualCapture : Residual
  transfer : Transfer
  lifecycleCost : Cost
  risk : Risk

/-- Action `a` weakly Pareto-dominates action `b` when it is no worse in every
absolute coordinate, reversing the comparison direction for costs and risks. -/
def ParetoWeak
    {Action Information Residual Transfer Cost Risk : Type u}
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : Prop :=
  (value b).information ≤ (value a).information ∧
    (value b).residualCapture ≤ (value a).residualCapture ∧
    (value b).transfer ≤ (value a).transfer ∧
    (value a).lifecycleCost ≤ (value b).lifecycleCost ∧
    (value a).risk ≤ (value b).risk

/-- If all five coordinate orders are preorders, the induced weak Pareto
dominance relation on actions is reflexive and transitive. -/
theorem pareto_weak_reflexive_transitive
    {Action Information Residual Transfer Cost Risk : Type u}
    [Preorder Information] [Preorder Residual] [Preorder Transfer]
    [Preorder Cost] [Preorder Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk) :
    (∀ a, ParetoWeak value a a) ∧
      (∀ ⦃a b c⦄, ParetoWeak value a b → ParetoWeak value b c →
        ParetoWeak value a c) := by
  constructor
  · intro a
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  · intro a b c hab hbc
    rcases hab with ⟨hInformationAB, hResidualAB, hTransferAB,
      hCostAB, hRiskAB⟩
    rcases hbc with ⟨hInformationBC, hResidualBC, hTransferBC,
      hCostBC, hRiskBC⟩
    exact
      ⟨le_trans hInformationBC hInformationAB,
        le_trans hResidualBC hResidualAB,
        le_trans hTransferBC hTransferAB,
        le_trans hCostAB hCostBC,
        le_trans hRiskAB hRiskBC⟩

/-- A finite inhabited instance where weak dominance holds in exactly one
direction, witnessing that the public relation and theorem are nonvacuous. -/
example :
    ∃ value : Bool → GainVector Nat Nat Nat Nat Nat,
      ((∀ a, ParetoWeak value a a) ∧
        (∀ ⦃a b c⦄, ParetoWeak value a b → ParetoWeak value b c →
          ParetoWeak value a c)) ∧
      ParetoWeak value true false ∧ ¬ ParetoWeak value false true := by
  let value : Bool → GainVector Nat Nat Nat Nat Nat := fun action =>
    if action then
      { information := 1
        residualCapture := 1
        transfer := 1
        lifecycleCost := 0
        risk := 0 }
    else
      { information := 0
        residualCapture := 0
        transfer := 0
        lifecycleCost := 1
        risk := 1 }
  refine ⟨value, pareto_weak_reflexive_transitive value, ?_, ?_⟩
  · exact ⟨Nat.zero_le 1, Nat.zero_le 1, Nat.zero_le 1,
      Nat.zero_le 1, Nat.zero_le 1⟩
  · intro hReverse
    exact (Nat.not_succ_le_zero 0) hReverse.1

#print axioms pareto_weak_reflexive_transitive

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
