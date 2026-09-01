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
     removed by `d`. The search also found `experimentGain`, the set of all
     baseline target defects removed by one experiment; it does not impose
     membership in `blindResidual Gamma q target`, so it is not an exact
     replacement. No existing set-weight definition had the required shape.
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

/-- A nonnegative set weight that vanishes on the empty set gives the displayed
reduction formula and a nonnegative reduction weight. Positive reduction weight
then certifies that some blind residual pair is separated by `d`; no converse or
full-support property is assumed. -/
theorem blind_kernel_reduction_measure
    {X C B Target D : Type*} (nu : Set (X × X) → ℝ)
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) (d : Concept X D)
    (nu_nonnegative : ∀ set, 0 ≤ nu set)
    (nu_empty : nu ∅ = 0) :
    blindKernelReductionMeasure nu Gamma q target d =
        nu (blindResidual Gamma q target ∩
          ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ) ∧
      0 ≤ blindKernelReductionMeasure nu Gamma q target d ∧
      (0 < blindKernelReductionMeasure nu Gamma q target d →
        ∃ pair : X × X,
          pair ∈ blindResidual Gamma q target ∧
            d pair.1 ≠ d pair.2) := by
  refine ⟨rfl, nu_nonnegative _, ?_⟩
  intro positive_reduction
  have reduction_nonempty :
      (blindResidual Gamma q target ∩
        ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ).Nonempty := by
    by_contra not_nonempty
    rw [Set.not_nonempty_iff_eq_empty] at not_nonempty
    unfold blindKernelReductionMeasure at positive_reduction
    rw [not_nonempty, nu_empty] at positive_reduction
    exact (lt_irrefl 0) positive_reduction
  rcases reduction_nonempty with ⟨pair, pair_in_reduction⟩
  refine ⟨pair, pair_in_reduction.1, ?_⟩
  change ¬Setoid.ker d pair.1 pair.2
  exact pair_in_reduction.2

/-- Finite counting weight satisfies both public weight premises. With an
empty package and constant baseline, the identity definition separates the
Boolean residual pair `(false, true)`, so the reduction weight is positive. -/
example :
    (∀ set : Set (Bool × Bool), 0 ≤ (set.ncard : ℝ)) ∧
      ((∅ : Set (Bool × Bool)).ncard : ℝ) = 0 ∧
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
  have nu_empty : ((∅ : Set (Bool × Bool)).ncard : ℝ) = 0 := by
    simp
  have positive :
      0 < blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) := by
    unfold blindKernelReductionMeasure
    rw [Nat.cast_pos, Set.ncard_pos]
    refine ⟨(false, true), ?_⟩
    simp [blindResidual, defectRelation, jointKernel, conceptKernel]
  have law := blind_kernel_reduction_measure
    (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
    (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
    (id : Concept Bool Bool) (id : Concept Bool Bool)
    nu_nonnegative nu_empty
  exact ⟨nu_nonnegative, nu_empty, positive, law.2.2 positive⟩

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
  have nu_empty : ((∅ : Set (Bool × Bool)).ncard : ℝ) = 0 := by
    simp
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
    nu_nonnegative nu_empty
  refine ⟨residual_nonempty, ?_, no_separated_pair⟩
  have not_positive :
      ¬0 < blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : ℝ))
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (fun _ : Bool => false) := by
    intro positive
    exact no_separated_pair (law.2.2 positive)
  exact le_antisymm (le_of_not_gt not_positive) law.2.1

/-- A normalized Dirac-style weight may assign zero weight to the nonempty set
of separated residual pairs. The one-way public criterion still applies. -/
example :
    let nu : Set (Bool × Bool) → ℝ :=
      fun set => ((set ∩ {(false, false)}).ncard : ℝ)
    nu {(false, false)} = 1 ∧
      (∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (id : Concept Bool Bool) pair.1 ≠ id pair.2) ∧
      blindKernelReductionMeasure nu
        (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) = 0 ∧
      (0 < blindKernelReductionMeasure nu
          (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
          (id : Concept Bool Bool) (id : Concept Bool Bool) →
        ∃ pair : Bool × Bool,
          pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
            (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
          (id : Concept Bool Bool) pair.1 ≠ id pair.2) := by
  dsimp only
  let nu : Set (Bool × Bool) → ℝ :=
    fun set => ((set ∩ {(false, false)}).ncard : ℝ)
  have nu_nonnegative : ∀ set, 0 ≤ nu set := by
    intro set
    exact Nat.cast_nonneg _
  have nu_empty : nu ∅ = 0 := by
    simp [nu]
  have separated :
      ∃ pair : Bool × Bool,
        pair ∈ blindResidual (∅ : Set (Concept Bool Unit))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
        (id : Concept Bool Bool) pair.1 ≠ id pair.2 := by
    refine ⟨(false, true), ?_, Bool.false_ne_true⟩
    simp [blindResidual, defectRelation, jointKernel, conceptKernel]
  have law := blind_kernel_reduction_measure nu
    (∅ : Set (Concept Bool Unit)) (fun _ : Bool => ())
    (id : Concept Bool Bool) (id : Concept Bool Bool)
    nu_nonnegative nu_empty
  refine ⟨?_, separated, ?_, law.2.2⟩
  · simp
  · simp [blindKernelReductionMeasure, blindResidual, defectRelation,
      jointKernel, conceptKernel]

#print axioms blind_kernel_reduction_measure

end D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelReductionMeasure
