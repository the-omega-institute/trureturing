/- GID: D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive weight detects blind residual pairs separated by a new definition. -/

import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'blind_kernel_reduction_measure' D5 Golden/Frozen/accepted`
     exited 1 with no declaration-name collision.
   * The type-shape search `rg -n 'Set \(X × X\)' D5` found the canonical
     `defectRelation`, `conceptKernel`, `jointKernel`, and exact imported
     `blindResidual`; the latter is reused below rather than reconstructed.
   * English synonym searches for `blind|residual|kernel|defect|reduction|
     measure|weight|mass|positive|separate|distinguish|support` found
     `ResidualJoinLaw.residual_join_law`, which measures no set and describes
     the residual pairs retained by `ker d`, not the complementary pairs
     removed by `d`. No existing set-weight definition had the required shape.
   * The Chinese search for `盲核|盲残差|残差|缺陷|降低|缩减|测度|权重|质量|
     正性|分开|区分` found only the audit comment in `BlindKernelObstruction`.
   * `ls D5/S3/ConceptDynamics/` and
     `git grep -n -E '^def |^  def ' -- D5/S3/ConceptDynamics | head -60`
     surveyed the neighboring vocabulary. The pinned-Mathlib search found
     `Set.ncard_pos`, used directly by the finite positive example below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelReductionMeasure

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- The reduction weight of a proposed definition is the weight of the blind
residual pairs lying outside that definition's equality kernel. -/
def blindKernelReductionMeasure
    {X C B Target D : Type*} (nu : Set (X × X) → ℝ)
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) (d : Concept X D) : ℝ :=
  nu (blindResidual Gamma q target ∩
    ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ)

/-- A nonnegative set weight that is positive exactly on nonempty sets gives
the displayed reduction formula, a nonnegative reduction weight, and the exact
positive-weight criterion: some blind residual pair is separated by `d`. -/
theorem blind_kernel_reduction_measure
    {X C B Target D : Type*} (nu : Set (X × X) → ℝ)
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) (d : Concept X D)
    (nu_nonnegative : ∀ set, 0 ≤ nu set)
    (nu_positive_iff_nonempty : ∀ set, 0 < nu set ↔ set.Nonempty) :
    blindKernelReductionMeasure nu Gamma q target d =
        nu (blindResidual Gamma q target ∩
          ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ) ∧
      0 ≤ blindKernelReductionMeasure nu Gamma q target d ∧
      (0 < blindKernelReductionMeasure nu Gamma q target d ↔
        ∃ pair : X × X,
          pair ∈ blindResidual Gamma q target ∧
            d pair.1 ≠ d pair.2) := by
  refine ⟨rfl, nu_nonnegative _, ?_⟩
  unfold blindKernelReductionMeasure
  rw [nu_positive_iff_nonempty]
  constructor
  · rintro ⟨pair, pair_in_reduction⟩
    refine ⟨pair, pair_in_reduction.1, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, Setoid.ker_def] using
      pair_in_reduction.2
  · rintro ⟨pair, pair_in_residual, definition_separates⟩
    refine ⟨pair, pair_in_residual, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, Setoid.ker_def] using
      definition_separates

/-- Finite counting weight satisfies both public weight premises. With an
empty package and constant baseline, the identity definition separates the
Boolean residual pair `(false, true)`, so the reduction weight is positive. -/
example :
    (∀ set : Set (Bool × Bool), 0 ≤ (set.ncard : ℝ)) ∧
      (∀ set : Set (Bool × Bool),
        0 < (set.ncard : ℝ) ↔ set.Nonempty) ∧
      0 < blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) ∧
      ∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (id : Concept Bool Bool) pair.1 ≠ id pair.2 := by
  have nu_nonnegative :
      ∀ set : Set (Bool × Bool), 0 ≤ (set.ncard : ℝ) := by
    intro set
    exact Nat.cast_nonneg set.ncard
  have nu_positive_iff_nonempty :
      ∀ set : Set (Bool × Bool),
        0 < (set.ncard : ℝ) ↔ set.Nonempty := by
    intro set
    rw [Nat.cast_pos]
    exact Set.ncard_pos
  have separated :
      ∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (id : Concept Bool Bool) pair.1 ≠ id pair.2 := by
    refine ⟨(false, true), ?_, Bool.false_ne_true⟩
    simp [blindResidual, defectRelation, jointKernel, conceptKernel]
  have law := blind_kernel_reduction_measure
    (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
    (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
    (id : Concept Bool Bool) (id : Concept Bool Bool)
    nu_nonnegative nu_positive_iff_nonempty
  exact ⟨nu_nonnegative, nu_positive_iff_nonempty,
    law.2.2.mpr separated, separated⟩

/-- The same blind residual is nonempty for a constant new definition, but no
residual pair is separated; consequently its finite counting weight is zero. -/
example :
    (blindResidual (∅ : Set (Concept Bool Unit))
      (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
      blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (fun _ : Bool => false) = 0 ∧
      ¬∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (fun _ : Bool => false) pair.1 ≠ (fun _ : Bool => false) pair.2 := by
  have nu_nonnegative :
      ∀ set : Set (Bool × Bool), 0 ≤ (set.ncard : ℝ) := by
    intro set
    exact Nat.cast_nonneg set.ncard
  have nu_positive_iff_nonempty :
      ∀ set : Set (Bool × Bool),
        0 < (set.ncard : ℝ) ↔ set.Nonempty := by
    intro set
    rw [Nat.cast_pos]
    exact Set.ncard_pos
  have residual_nonempty :
      (blindResidual (∅ : Set (Concept Bool Unit))
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ?_⟩
    simp [blindResidual, defectRelation, jointKernel, conceptKernel]
  have no_separated_pair :
      ¬∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (fun _ : Bool => false) pair.1 ≠ (fun _ : Bool => false) pair.2 := by
    rintro ⟨pair, _, separated⟩
    exact separated rfl
  have law := blind_kernel_reduction_measure
    (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
    (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
    (id : Concept Bool Bool) (fun _ : Bool => false)
    nu_nonnegative nu_positive_iff_nonempty
  refine ⟨residual_nonempty, ?_, no_separated_pair⟩
  exact le_antisymm (le_of_not_gt (law.2.2.not.mpr no_separated_pair)) law.2.1

/-- Nonnegativity alone is insufficient: the zero weight stays zero even when
the identity definition separates a blind residual pair. -/
example :
    (∀ set : Set (Bool × Bool),
      0 ≤ (fun _ : Set (Bool × Bool) => (0 : ℝ)) set) ∧
      (∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (id : Concept Bool Bool) pair.1 ≠ id pair.2) ∧
      ¬0 < blindKernelReductionMeasure
        (fun _ : Set (Bool × Bool) => (0 : ℝ))
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) := by
  refine ⟨?_, ?_, ?_⟩
  · intro set
    rfl
  · refine ⟨(false, true), ?_, Bool.false_ne_true⟩
    simp [blindResidual, defectRelation, jointKernel, conceptKernel]
  · simp [blindKernelReductionMeasure]

#print axioms blind_kernel_reduction_measure

end D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelReductionMeasure
