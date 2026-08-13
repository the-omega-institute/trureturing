/- GID: D5/S1/Eigenstructure/ContractingAxisSignDepth
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/ContractingAxisSignDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Contracting-axis powers split into parity sign and inverse-golden depth. -/

import D5.S1.Scale.FibonacciEigen

namespace D5.S1.Eigenstructure.ContractingAxisSignDepth

open D5.S1.Scale

/-- Each power of the contracting eigenvalue separates into its alternating
sign and inverse-golden magnitude. -/
theorem contracting_axis_power_sign_depth (n : ℕ) :
    contractingEigenvalue ^ n =
      (-1 : ℝ) ^ n * Real.goldenRatio ^ (-(n : ℤ)) := by
  rw [contractingEigenvalue, neg_pow, one_div, inv_pow, zpow_neg, zpow_natCast]

-- The natural-number exponent domain is inhabited.
example : ℕ := 0

end D5.S1.Eigenstructure.ContractingAxisSignDepth
