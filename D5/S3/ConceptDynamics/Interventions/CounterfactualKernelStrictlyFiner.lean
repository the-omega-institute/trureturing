/- GID: D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In deterministic binary unconfounded models with known treatment, counterfactual equality determines interventional equality, while the converse fails for an existing model pair. -/

import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'counterfactual_kernel_strictly_finer' D5
     Golden/Frozen/accepted` returned no match.
   * Searches in `D5` for `DeterministicBoolSCM`, counterfactual and interventional
     kernels, and a collapse from `CF` to `Int` found only the imported strict
     separation witness, not the factorization or the two-branch result proved here.
   * The corresponding private-declaration search returned no match. A pinned
     Mathlib search for `counterfactual|interventional` also returned no match.
   * All eight existing Interventions digests were read. None covers the collapse
     or kernel inclusion; the imported separation module supplies exactly the
     strict witness reused in the second branch. The first branch uses pointwise
     computation and equality congruence after defining the missing collapse.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/-- A counterfactual table records outcome by exogenous unit, factual treatment,
and alternate treatment. -/
abbrev CFTable := Bool -> Bool -> Bool -> Bool

/-- An interventional table records an outcome count for each treatment and result. -/
abbrev IntTable := Bool -> Bool -> Nat

/-- Aggregate a counterfactual table over the two exogenous units. The fixed
factual coordinate is immaterial for tables in the image of `CF`. -/
def collapse (table : CFTable) : IntTable :=
  fun treatment result =>
    (if table false false treatment = result then 1 else 0) +
      if table true false treatment = result then 1 else 0

/-- Interventional marginals are the exogenous aggregate of the counterfactual table. -/
theorem intervention_eq_collapse_counterfactual (M : DeterministicBoolSCM) :
    Int M = collapse (CF M) := by
  funext treatment result
  rfl

/-- Equality at the counterfactual layer implies equality at the interventional layer. -/
theorem counterfactual_eq_implies_interventional_eq (M N : DeterministicBoolSCM)
    (hCF : CF M = CF N) : Int M = Int N := by
  calc
    Int M = collapse (CF M) := intervention_eq_collapse_counterfactual M
    _ = collapse (CF N) := congrArg collapse hCF
    _ = Int N := (intervention_eq_collapse_counterfactual N).symm

/-- On deterministic binary unconfounded models, the counterfactual kernel is
strictly finer than the interventional kernel. -/
theorem counterfactual_kernel_strictly_finer :
    (∀ M N : DeterministicBoolSCM, CF M = CF N → Int M = Int N) ∧
      ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N := by
  constructor
  · intro M N hCF
    exact counterfactual_eq_implies_interventional_eq M N hCF
  · exact intervention_strictly_weaker_than_counterfactual

example : collapse (CF noEffectModel) false false = 1 := rfl

#print axioms counterfactual_kernel_strictly_finer

end D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
