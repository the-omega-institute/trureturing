/- GID: D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Blackwell dominance is reflexive and transitive, includes deterministic maps, and its Bayes-risk inequality is a direct application of mathlib's data-processing theorem. -/

import Mathlib.Probability.Decision.Risk.Basic

/- Library-search audit trail (2026-08-24):
   * Before this module was added, the command
     `rg -n -F 'bayesRisk_le_of_blackwellDominates' D5 Golden/Frozen/accepted`
     found no match.
   * Searches for `bayesRisk`, `garbl`, `Blackwell`, and `dataProcessing` found the
     fixed-suite Bayes floor and divergence data-processing modules, but no public or
     private D5 declaration of the Blackwell order or the theorem below.
   * Pinned mathlib provides `ProbabilityTheory.bayesRisk_le_bayesRisk_comp` at
     `Mathlib/Probability/Decision/Risk/Basic.lean:236`; the main proof applies it directly.
   * Pinned mathlib provides `Kernel.comp_assoc` and `IsMarkovKernel.comp` at
     `Kernel/Composition/Comp.lean:143,210`, `Kernel.deterministic_comp_eq_map` at
     `Kernel/Composition/CompMap.lean:38`, and the identity and deterministic Markov instances
     at `Kernel/Basic.lean:82,113`. The order proofs reuse them rather than reprove them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- `P` Blackwell-dominates `Q` when `Q` is obtained by garbling the output of `P`. -/
def BlackwellDominates {Theta X X' : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X']
    (P : Kernel Theta X) (Q : Kernel Theta X') : Prop :=
  ∃ eta : Kernel X X', IsMarkovKernel eta ∧ Q = eta ∘ₖ P

/-- Every experiment Blackwell-dominates itself. -/
theorem blackwellDominates_refl {Theta X : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] (P : Kernel Theta X) :
    BlackwellDominates P P := by
  exact ⟨Kernel.id, inferInstance, (Kernel.id_comp P).symm⟩

/-- Blackwell dominance is transitive under composition of garbling kernels. -/
theorem blackwellDominates_trans {Theta X X' X'' : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace X''] (P : Kernel Theta X) (Q : Kernel Theta X')
    (R : Kernel Theta X'') :
    BlackwellDominates P Q → BlackwellDominates Q R → BlackwellDominates P R := by
  rintro ⟨eta, hEta, rfl⟩ ⟨xi, hXi, rfl⟩
  letI : IsMarkovKernel eta := hEta
  letI : IsMarkovKernel xi := hXi
  exact ⟨xi ∘ₖ eta, inferInstance, (Kernel.comp_assoc xi eta P).symm⟩

/-- A measurable deterministic transformation of observations is a Blackwell garbling. -/
theorem blackwellDominates_map {Theta X X' : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X']
    (P : Kernel Theta X) (f : X → X') (hf : Measurable f) :
    BlackwellDominates P (P.map f) := by
  exact
    ⟨Kernel.deterministic f hf, inferInstance,
      (Kernel.deterministic_comp_eq_map hf P).symm⟩

/-- Blackwell dominance makes optimal Bayes risk monotone for every prior and ENNReal loss. -/
theorem bayesRisk_le_of_blackwellDominates {Theta X X' Y : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
    (P : Kernel Theta X) (Q : Kernel Theta X') (hPQ : BlackwellDominates P Q) :
    ∀ (loss : Theta → Y → ENNReal) (pi : Measure Theta),
      bayesRisk loss P pi ≤ bayesRisk loss Q pi := by
  intro loss pi
  obtain ⟨eta, hEta, rfl⟩ := hPQ
  letI : IsMarkovKernel eta := hEta
  exact bayesRisk_le_bayesRisk_comp loss P pi eta

example : BlackwellDominates (Kernel.id : Kernel Unit Unit) Kernel.id :=
  blackwellDominates_refl Kernel.id

#print axioms bayesRisk_le_of_blackwellDominates

end D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk
