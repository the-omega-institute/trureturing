/- GID: D5/S3/Geometry/Hyperideal/WeightedFlatCertificateRefutation
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/WeightedFlatCertificateRefutation
   mirror-E: none(waiver:universal-real-inequality)
   anchors: []
   utility: none
   digest: Positive flat-candidate gaps make both dependency cycles and weighted certificates impossible. -/

import D5.S3.Geometry.Hyperideal.FlatCandidateAcyclicity
import Mathlib.Tactic

/-! Positive candidate gaps yield strict descent and a positive weighted certificate gap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.WeightedFlatCertificateRefutation

open D5.S3.Geometry.Hyperideal.FlatCandidateAcyclicity

def weightedGap {Sigma Q : Type*} [Fintype Sigma]
    (weights : Sigma → ℝ) (z : Q → ℝ)
    (q q' q'' : Sigma → Q) : ℝ :=
  ∑ sigma, weights sigma *
    (z (q sigma) - z (q' sigma) - z (q'' sigma))

private theorem weighted_gap_pos {Sigma Q : Type*} [Fintype Sigma]
    (weights : Sigma → ℝ) (z : Q → ℝ)
    (q q' q'' : Sigma → Q)
    (hpositive : ∀ v, 1 < z v)
    (hweight : ∀ sigma, 0 ≤ weights sigma)
    (hsome : ∃ sigma, 0 < weights sigma)
    (hpg : ∀ sigma, z (q sigma) ≥ 1 + z (q' sigma) + z (q'' sigma)) :
    0 < weightedGap weights z q q' q'' := by
  have hsum_pos : 0 < ∑ sigma, weights sigma := by
    apply Finset.sum_pos'
    · intro sigma hsigma
      exact hweight sigma
    · rcases hsome with ⟨sigma, hsigma⟩
      exact ⟨sigma, Finset.mem_univ _, hsigma⟩
  have hsum_gap : (∑ sigma, weights sigma) ≤ weightedGap weights z q q' q'' := by
    apply Finset.sum_le_sum
    intro sigma hsigma
    have hdiff : 1 ≤ z (q sigma) - z (q' sigma) - z (q'' sigma) := by
      linarith [hpg sigma, hpositive (q'' sigma)]
    have hmul := mul_le_mul_of_nonneg_left hdiff (hweight sigma)
    simpa [weightedGap] using hmul
  linarith

theorem flat_candidate_cycle_and_certificate_refutation
    {Q Sigma : Type*} [Fintype Sigma]
    (z : Q → ℝ) (candidate : Q → Q → Q → Prop)
    (weights : Sigma → ℝ) (q q' q'' : Sigma → Q)
    (hpositive : ∀ v, 1 < z v)
    (hpg : ∀ {a b c}, candidate a b c → z a ≥ 1 + z b + z c)
    (hweight : ∀ sigma, 0 ≤ weights sigma)
    (hsome : ∃ sigma, 0 < weights sigma)
    (hcertificate : weightedGap weights z q q' q'' ≤ 0)
    (hselected : ∀ sigma, candidate (q sigma) (q' sigma) (q'' sigma)) :
    ¬ HasDirectedCycle (candidateEdge candidate) ∧ False := by
  have hacyclic := flat_candidate_cycle_exclusion z candidate hpositive hpg
  have hqgap : ∀ sigma, z (q sigma) ≥ 1 + z (q' sigma) + z (q'' sigma) := by
    intro sigma
    exact hpg (hselected sigma)
  have hpositive_gap := weighted_gap_pos weights z q q' q'' hpositive hweight hsome hqgap
  exact ⟨hacyclic, by linarith⟩

end D5.S3.Geometry.Hyperideal.WeightedFlatCertificateRefutation
