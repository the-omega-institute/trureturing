/- GID: D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic coarse-graining cannot increase finite mutual information. -/

import D5.S3.Entropy.MutualInformationSymm
import D5.S3.Entropy.Submodularity.MarkovDataProcessing

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'coarse_graining_cannot_add_information' D5 Golden/Frozen/accepted`
     returned no matches.
   * The required repository scan found Renyi and KL data-processing modules, then a targeted
     mutual-information scan found
     `Entropy.Submodularity.MarkovDataProcessing.mutual_information_le_of_markov`.
   * Pinned Mathlib has KL divergence but no `mutualInformation` or `condEntropy` declaration;
     its only data-processing-name hits concern Bayes risk.
   * The proof below reuses the repository Markov data-processing theorem twice, once for each
     deterministic coordinate map, together with mutual-information symmetry. It does not
     reprove data processing.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.CoarseGrainingCannotAddInformation

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationSymm
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.MarkovDataProcessing

/-- The joint law obtained by applying the same deterministic coarse-graining map to both
coordinates of a finite microscopic joint law. -/
noncomputable def coarseGrainedJoint {X C : Type*} [Fintype X]
    (p : X × X → ℝ) (coarse : X → C) (q : C × C) : ℝ := by
  classical
  exact ∑ x, ∑ y, if coarse x = q.1 ∧ coarse y = q.2 then p (x, y) else 0

private noncomputable def deterministicRight {A B D : Type*} [Fintype B]
    (p : A × B → ℝ) (f : B → D) (q : A × D) : ℝ := by
  classical
  exact ∑ b, p (q.1, b) * if f b = q.2 then 1 else 0

private theorem deterministicRight_is_law
    {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (p : A × B → ℝ) (f : B → D)
    (hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1) :
    (∀ q, 0 ≤ deterministicRight p f q) ∧ ∑ q, deterministicRight p f q = 1 := by
  classical
  constructor
  · intro q
    rw [deterministicRight]
    exact Finset.sum_nonneg fun b _ ↦ mul_nonneg (hp.1 _) (by split_ifs <;> norm_num)
  · simp only [Fintype.sum_prod_type, deterministicRight]
    calc
      (∑ a, ∑ d, ∑ b, p (a, b) * if f b = d then 1 else 0) =
          ∑ a, ∑ b, ∑ d, p (a, b) * if f b = d then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ a, ∑ b, p (a, b) := by simp
      _ = 1 := by simpa only [Fintype.sum_prod_type] using hp.2

private theorem mutual_information_deterministic_right_le
    {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (p : A × B → ℝ) (f : B → D)
    (hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1) :
    mutualInformation (deterministicRight p f) ≤
      mutualInformation p := by
  classical
  let W : B → D → ℝ := fun b d ↦ if f b = d then 1 else 0
  let extension : A × (B × D) → ℝ :=
    fun q ↦ p (q.1, q.2.1) * W q.2.1 q.2.2
  have hW_sum (b : B) : ∑ d, W b d = 1 := by
    simp [W]
  have hextension_law : (∀ q, 0 ≤ extension q) ∧ ∑ q, extension q = 1 := by
    constructor
    · intro q
      apply mul_nonneg (hp.1 _)
      simp only [W]
      split_ifs <;> norm_num
    · simp only [extension, Fintype.sum_prod_type, ← Finset.mul_sum, hW_sum, mul_one]
      simpa only [Fintype.sum_prod_type] using hp.2
  have hmarkov := markov_of_channel p W hW_sum
  have hdpi := mutual_information_le_of_markov extension hextension_law hmarkov
  have hxy : xyProjection extension = p := by
    funext q
    simp [xyProjection, extension, W]
  have hxz : xzProjection extension = deterministicRight p f := by
    funext q
    simp [xzProjection, extension, deterministicRight, W]
  rw [hxy, hxz] at hdpi
  exact hdpi

/-- Applying one deterministic concept map to both consecutive microscopic states cannot
increase their finite Shannon mutual information. -/
theorem coarse_graining_cannot_add_information
    {X C : Type*} [Fintype X] [Fintype C]
    (p : X × X → ℝ) (coarse : X → C)
    (hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1) :
    mutualInformation (coarseGrainedJoint p coarse) ≤ mutualInformation p := by
  classical
  let right : X × C → ℝ := deterministicRight p coarse
  let swappedRight : C × X → ℝ := fun q ↦ right (q.2, q.1)
  have hright_law : (∀ q, 0 ≤ right q) ∧ ∑ q, right q = 1 := by
    simpa only [right] using deterministicRight_is_law p coarse hp
  have hswapped_law :
      (∀ q, 0 ≤ swappedRight q) ∧ ∑ q, swappedRight q = 1 := by
    constructor
    · intro q
      exact hright_law.1 (q.2, q.1)
    · simp only [swappedRight, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simpa only [Fintype.sum_prod_type] using hright_law.2
  have hright : mutualInformation right ≤ mutualInformation p := by
    simpa only [right] using mutual_information_deterministic_right_le p coarse hp
  have hboth :
      mutualInformation (deterministicRight swappedRight coarse) ≤
        mutualInformation swappedRight :=
    mutual_information_deterministic_right_le swappedRight coarse hswapped_law
  have hcoarse_swap :
      deterministicRight swappedRight coarse =
        fun q : C × C ↦ coarseGrainedJoint p coarse (q.2, q.1) := by
    funext q
    simp only [deterministicRight, swappedRight, right, coarseGrainedJoint]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : coarse x = q.2 <;>
      by_cases hy : coarse y = q.1 <;> simp [hx, hy]
  have hcoarse_information :
      mutualInformation (deterministicRight swappedRight coarse) =
        mutualInformation (coarseGrainedJoint p coarse) := by
    rw [hcoarse_swap]
    exact mutual_information_symm (coarseGrainedJoint p coarse)
  have hright_information : mutualInformation swappedRight = mutualInformation right := by
    simpa only [swappedRight] using mutual_information_symm right
  calc
    mutualInformation (coarseGrainedJoint p coarse) =
        mutualInformation (deterministicRight swappedRight coarse) :=
      hcoarse_information.symm
    _ ≤ mutualInformation swappedRight := hboth
    _ = mutualInformation right := hright_information
    _ ≤ mutualInformation p := hright

example :
    mutualInformation
        (coarseGrainedJoint (fun _q : Bool × Bool ↦ (1 / 4 : ℝ)) (fun _ ↦ ())) ≤
      mutualInformation (fun _q : Bool × Bool ↦ (1 / 4 : ℝ)) := by
  apply coarse_graining_cannot_add_information
  constructor
  · intro q
    positivity
  · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

#print axioms coarse_graining_cannot_add_information

end D5.S3.ConceptDynamics.Prediction.CoarseGrainingCannotAddInformation
