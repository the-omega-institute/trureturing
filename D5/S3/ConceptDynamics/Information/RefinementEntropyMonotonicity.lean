/- GID: D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement increases concept information and decreases residual entropy. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Entropy.Forgetting.DeterministicEntropyEquality

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `Concept` and `Refines` provide the canonical
     readout carrier and factorization order and are imported directly.
   * Exact repository hits `pushforward_entropy_eq_iff_injective_on_support`
     and `pushforward_entropy_lt_iff_not_injective_on_support` classify every
     deterministic entropy pushforward; both are directly applied below.
   * Exact repository hit `entropy_chain_rule` converts the information
     inequality into the source's reverse residual-entropy inequality.
   * Pinned Mathlib searches for finite Shannon and conditional entropy under
     deterministic refinement found no matching real-valued theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open D5.S3.Entropy.MaxEntropy

/-- The distribution of the coordinate reported by a concept readout. -/
noncomputable def conceptLaw {X C : Type*} [Fintype X]
    (mu : X -> Real) (q : Concept X C) : C -> Real :=
  pushforward q mu

/-- The graph-supported joint law of a concept coordinate and its source state. -/
noncomputable def conceptStateLaw {X C : Type*}
    (mu : X -> Real) (q : Concept X C) : C × X -> Real := by
  classical
  exact fun z => if q z.2 = z.1 then mu z.2 else 0

/-- Information expressed by a finite concept readout. -/
noncomputable def conceptInformation {X C : Type*} [Fintype X] [Fintype C]
    (mu : X -> Real) (q : Concept X C) : Real :=
  shannonEntropy (conceptLaw mu q)

/-- Conditional source-state entropy remaining after a finite concept readout. -/
noncomputable def conceptResidual {X C : Type*} [Fintype X] [Fintype C]
    (mu : X -> Real) (q : Concept X C) : Real :=
  conditionalEntropy (conceptStateLaw mu q)

private theorem conceptLaw_nonnegative {X C : Type*} [Fintype X]
    (mu : X -> Real) (q : Concept X C) (hmu : forall x, 0 <= mu x) :
    forall c, 0 <= conceptLaw mu q c := by
  classical
  intro c
  simp only [conceptLaw, pushforward]
  exact Finset.sum_nonneg fun x _ => by
    by_cases h : q x = c <;> simp [h, hmu x]

private theorem conceptLaw_total_mass {X C : Type*} [Fintype X] [Fintype C]
    (mu : X -> Real) (q : Concept X C) (hmu : (∑ x, mu x) = 1) :
    (∑ c, conceptLaw mu q c) = 1 := by
  classical
  simp only [conceptLaw, pushforward]
  calc
    (∑ c, ∑ x, if q x = c then mu x else 0) =
        ∑ x, ∑ c, if q x = c then mu x else 0 := Finset.sum_comm
    _ = ∑ x, mu x := by simp
    _ = 1 := hmu

private theorem conceptLaw_comp {X C D : Type*}
    [Fintype X] [Fintype C] [Fintype D]
    (mu : X -> Real) (q : Concept X D) (factor : D -> C) :
    conceptLaw mu (factor ∘ q) = pushforward factor (conceptLaw mu q) := by
  classical
  funext c
  simp only [conceptLaw, pushforward, Function.comp_apply]
  calc
    (∑ x, if factor (q x) = c then mu x else 0) =
        ∑ x, ∑ d, if q x = d ∧ factor d = c then mu x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (q x)]
      · simp
      · intro d _ hd
        simp [Ne.symm hd]
      · simp
    _ = ∑ d, ∑ x, if q x = d ∧ factor d = c then mu x else 0 :=
      Finset.sum_comm
    _ = ∑ d, if factor d = c then
          ∑ x, if q x = d then mu x else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hdc : factor d = c <;> simp [hdc]

private theorem conceptStateLaw_nonnegative {X C : Type*}
    (mu : X -> Real) (q : Concept X C) (hmu : forall x, 0 <= mu x) :
    forall z, 0 <= conceptStateLaw mu q z := by
  intro z
  classical
  simp only [conceptStateLaw]
  split_ifs
  · exact hmu _
  · exact le_rfl

private theorem conceptStateLaw_marginal {X C : Type*} [Fintype X]
    (mu : X -> Real) (q : Concept X C) :
    marginal (conceptStateLaw mu q) = conceptLaw mu q := by
  rfl

private theorem conceptStateLaw_entropy {X C : Type*}
    [Fintype X] [Fintype C] (mu : X -> Real) (q : Concept X C) :
    shannonEntropy (conceptStateLaw mu q) = shannonEntropy mu := by
  classical
  rw [shannonEntropy, Fintype.sum_prod_type, shannonEntropy]
  calc
    (∑ c, ∑ x, Real.negMulLog
        (if q x = c then mu x else 0)) =
        ∑ x, ∑ c, Real.negMulLog
          (if q x = c then mu x else 0) := Finset.sum_comm
    _ = ∑ x, Real.negMulLog (mu x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (q x)]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp

private theorem concept_entropy_balance {X C : Type*}
    [Fintype X] [Fintype C] (mu : X -> Real) (q : Concept X C)
    (hmu : forall x, 0 <= mu x) :
    shannonEntropy mu = conceptInformation mu q + conceptResidual mu q := by
  have hchain := entropy_chain_rule
    (conceptStateLaw mu q) (conceptStateLaw_nonnegative mu q hmu)
  rw [conceptStateLaw_entropy, conceptStateLaw_marginal] at hchain
  exact hchain

/-- Refining a finite concept readout increases its expressed Shannon
information and decreases its conditional source-state residual entropy. -/
theorem refinement_information_residual_monotone
    {X C D : Type*} [Fintype X] [Fintype C] [Fintype D]
    (mu : X -> Real)
    (hmu : (forall x, 0 <= mu x) ∧ (∑ x, mu x) = 1)
    (q_C : Concept X C) (q_D : Concept X D)
    (refinement : Refines q_C q_D) :
    conceptInformation mu q_C <= conceptInformation mu q_D ∧
      conceptResidual mu q_D <= conceptResidual mu q_C := by
  rcases refinement with ⟨factor, hfactor⟩
  have hlaw : (forall d, 0 <= conceptLaw mu q_D d) ∧
      (∑ d, conceptLaw mu q_D d) = 1 :=
    ⟨conceptLaw_nonnegative mu q_D hmu.1,
      conceptLaw_total_mass mu q_D hmu.2⟩
  have hinformation :
      conceptInformation mu q_C <= conceptInformation mu q_D := by
    rw [conceptInformation, conceptInformation, hfactor, conceptLaw_comp]
    by_cases hinjective : Set.InjOn factor {d | Not (conceptLaw mu q_D d = 0)}
    · exact le_of_eq
        ((pushforward_entropy_eq_iff_injective_on_support
          (conceptLaw mu q_D) factor hlaw).2 hinjective)
    · exact le_of_lt
        ((pushforward_entropy_lt_iff_not_injective_on_support
          (conceptLaw mu q_D) factor hlaw).2 hinjective)
  refine ⟨hinformation, ?_⟩
  have hcoarse := concept_entropy_balance mu q_C hmu.1
  have hfine := concept_entropy_balance mu q_D hmu.1
  linarith

/-- A constant readout refined by the identity satisfies the public hypotheses
on a nontrivial finite probability space. -/
example :
    let mu : Bool -> Real := fun _ => 1 / 2
    conceptInformation mu (fun _ : Bool => ()) <= conceptInformation mu id ∧
      conceptResidual mu id <= conceptResidual mu (fun _ : Bool => ()) := by
  dsimp only
  apply refinement_information_residual_monotone
  · constructor
    · intro x
      norm_num
    · norm_num [Fintype.sum_bool]
  · exact ⟨fun _ => (), rfl⟩

#print axioms refinement_information_residual_monotone

end D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
