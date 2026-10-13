/- GID: D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Optimization/WeightedCrownFirstLevelGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-level SDP inexactness on the open weighted-crown interval. -/

/-
admission_basis: open-problem-resolution (#15210; Proved).
escape_witness: WeightedCrownMomentCertificate.moment_feasible.
Escape audit unfinished: issue #15610 records missing observational-dependence evidence at
n = 3, x = 0 and x = 8, plus source-selection/report-decoding evidence for the hub/leaf
registrations. No completed registration is claimed.
upper_endpoint_lt_sector: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: WeightedCrownMomentCertificate.moment_feasible; consumers: settling root.
Direct frozen dependencies:
  D5/S3/Quantum/FiniteDimensional.QubitMatrix; declaration statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30.
  D5/S3/Quantum/FiniteDimensional.qubitX; declaration statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7.
  D5/S3/Quantum/FiniteDimensional.qubitZ; declaration statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c.
  D5/S3/Quantum/FiniteDimensional.qubit_weyl_star; declaration statement_id: sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d.
Utility none: uniform operator and real-parameter constructions, not finite enumeration.
Pair convention: use the two-element Finset subtype directly; no type alias is introduced.
-/

import D5.S3.Quantum.Optimization.WeightedCrownMomentCertificate

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Optimization.WeightedCrownFirstLevelGap
open D5.S3.Quantum.Optimization.WeightedCrownSpectralBound
open D5.S3.Quantum.Optimization.WeightedCrownMomentCertificate
attribute [local instance] Classical.propDecidable

def claim : Prop := ∀ n : ℕ, 3 ≤ n → ∀ x : ℝ, L n < x → x < U n →
  lambdaMax (crownH n x) < npa1Value n x

private lemma upper_endpoint_lt_sector (n : ℕ) (hn : 3 ≤ n) : U n < 1 + (n : ℝ) / 2 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold U
  linarith


theorem result : claim := by
  intro n hn x hxL hxU
  exact lt_of_le_of_lt
    (crown_spectral_bound n x (le_of_lt (lt_trans hxU (upper_endpoint_lt_sector n hn))))
    (constructed_value_gap n hn x hxL hxU)

end D5.S3.Quantum.Optimization.WeightedCrownFirstLevelGap
