/- GID: D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Both links are strict; empty, singleton, constant, and zero cases are audited. -/
/- Library-search audit trail (2026-08-25):
   * Repository searches for `DeterministicBoolSCM`, `Obs`, `Int`, and `CF` found
     `CounterfactualKernelStrictlyFiner`, which supplies the first inclusion and
     its strict witness reused below without reproving either result.
   * `ObservationInterventionSeparation` supplies an observation/intervention
     witness for a different SCM type, so it cannot populate one chain over the
     model type used by the imported counterfactual theorem.
   * No observation law was found on that imported SCM. Its structure has no
     treatment-assignment mechanism, so `Obs` below is the permitted known-
     treatment observational margin, namely the `false` slice of `Int`.
   * A pinned Mathlib search for `counterfactual`, `interventional`, and
     `structural causal` returned no matches. No external theorem is needed.
 -/

import D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.ObservationInterventionCounterfactualChain

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

/-- An observational table records outcome counts at the known factual treatment `false`. -/
abbrev ObsTable := Bool -> Nat

/-- The observable outcome margin at the known factual treatment `false`. -/
def Obs (M : DeterministicBoolSCM) : ObsTable := Int M false

/-- Equality at the interventional layer implies equality at the observational layer. -/
theorem interventional_eq_implies_observational_eq (M N : DeterministicBoolSCM)
    (hInt : Int M = Int N) : Obs M = Obs N := by
  exact congrFun hInt false
#print axioms interventional_eq_implies_observational_eq

/-- Every outcome is false, independently of the exogenous unit and treatment. -/
def constantOutcomeModel : DeterministicBoolSCM :=
  ⟨fun _exogenous _treatment => false⟩

/-- The outcome copies the treatment and ignores the exogenous unit. -/
def treatmentOutcomeModel : DeterministicBoolSCM :=
  ⟨fun _exogenous treatment => treatment⟩

/-- Equal observational margins do not determine all interventional margins. -/
theorem observation_kernel_strictness_witness :
    ∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N := by
  refine ⟨constantOutcomeModel, treatmentOutcomeModel, ?_, ?_⟩
  · funext result
    cases result <;> rfl
  · intro hInt
    have zero_eq_two : (0 : Nat) = 2 := congrFun (congrFun hInt true) true
    cases zero_eq_two
#print axioms observation_kernel_strictness_witness

/- Degeneracy audit: the model's exogenous, treatment, and outcome carriers are
fixed to `Bool`, so empty and singleton carriers and a size parameter `n` are not
inputs. The checks below establish this carrier fact and exercise the applicable
constant, identity-on-treatment, and zero-count cases. -/
example : Nonempty Bool := ⟨false⟩

example : ¬ Subsingleton Bool := by
  intro h
  exact Bool.false_ne_true (h.elim false true)

example : Obs constantOutcomeModel true = 0 := rfl

example : Obs constantOutcomeModel false = 2 := rfl

example : Obs treatmentOutcomeModel = Obs constantOutcomeModel := by
  funext result
  cases result <;> rfl

/-- Counterfactual, interventional, and observational kernels form a chain, and
both inclusions have strict witnesses. -/
theorem observation_intervention_counterfactual_chain :
    (∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
    (∀ M N : DeterministicBoolSCM, Int M = Int N → Obs M = Obs N) ∧
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) ∧
    (∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N) := by
  exact ⟨counterfactual_kernel_strictly_finer.1,
    interventional_eq_implies_observational_eq,
    counterfactual_kernel_strictly_finer.2,
    observation_kernel_strictness_witness⟩
#print axioms observation_intervention_counterfactual_chain

end D5.S3.ConceptDynamics.Causal.ObservationInterventionCounterfactualChain
