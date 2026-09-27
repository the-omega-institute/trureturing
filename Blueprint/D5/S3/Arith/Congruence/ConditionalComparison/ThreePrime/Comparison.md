# Actual Distortion Chains and Conditional Convex Comparison

## Abstract

Schroeder's actual finite distortion chains, conditional cap propagation, and convex comparison for arbitrary finite histories and label supports.

**Theorem 1.1 (Actual conditional loads are dominated by aligned auxiliary loads).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison` (`✓ std3`). ∎

*Citation.* Michael Schroeder (2026). *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. DOI: [10.5281/zenodo.22760638](https://doi.org/10.5281/zenodo.22760638). URL: <https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip>.

*Commentary.*

This is a source transplant of Michael Schroeder's theorem Erdos7.ThreePrime.convex_load_comparison. The full MIT license, source archive and import mapping are recorded in `D5/L/Arith/schroeder2026noncoverage`.

A KernelChain on a finite alphabet retains the complete preceding coordinate tuple in every conditional kernel. For every label and every history, HasCaps bounds its coordinate-event probability by the survival function of a finite auxiliary run at that label's depth. The finite depth bound and nonnegative rational weights are explicit hypotheses.

For every increasing convex rational-valued function, the expected function of the actual active-label load is at most its expectation under the product of the auxiliary run laws, with a label active precisely when all its depths are below the auxiliary heights. The actual coordinate events need not be nested, and their law need not be a product law. There is no bound on the number of coordinates used by one label. Nonnegativity of the convex function is not required.

The imported proof eliminates coordinates backwards using the finite increasing-supermodular rearrangement. The ThreePrime source directory name does not impose a three-prime hypothesis on this declaration. This module supplies the existing comparison theorem; a covering-system application must still construct its actual kernels and discharge every cap hypothesis.

**Theorem 1.2 (One final normalized law bounds the union by accumulated charge).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.covered_probability_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.covered_probability_le` (`✓ std3`). ∎

*Citation.* Michael Schroeder (2026). *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. DOI: [10.5281/zenodo.22760638](https://doi.org/10.5281/zenodo.22760638). URL: <https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip>.

*Commentary.*

This is the unchanged source theorem Erdos7.ThreePrime.PhysicalChain.covered_probability_le. A PhysicalChain attaches any finite rational base law at each step, a Boolean bad event depending on the entire previous history, and a rational threshold delta with 0 <= delta < 1. Each base law is fixed for its step; its distorted conditional kernel depends on that history.

The probability, under the final chain law, that any bad event has occurred is at most totalCharge. The new charge at a step is the preceding history law's expectation of thresholdMass(delta,alpha), where alpha is the base-law probability of the current bad event. The imported one_le_charge_of_cover consequence gives totalCharge >= 1 if every full tuple is covered. Thus a strict charge bound below one supplies noncoverage under one actual normalized law.

The declaration has no three-prime or support-size restriction. It does not prove the numerical charge bound required by a particular covering family.

**Theorem 1.3 (Base-law caps provide the full-history conditional caps).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.kernels_have_caps`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.kernels_have_caps` (`✓ std3`). ∎

*Citation.* Michael Schroeder (2026). *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. DOI: [10.5281/zenodo.22760638](https://doi.org/10.5281/zenodo.22760638). URL: <https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip>.

*Commentary.*

The unchanged source theorem Erdos7.ThreePrime.PhysicalChain.kernels_have_caps takes the recursive BaseCaps hypothesis. For each label of positive depth at a step, its actual coordinate-event probability under the base law must be at most (1-delta) times the chosen RunSpec survival probability at that depth. Depth zero uses the universal probability bound one.

The imported event distortion inequality divides each base cap by 1-delta. Induction supplies HasCaps for every kernel conditional on its entire history, which is the exact input to the convex comparison above. No independence of physical coordinates is assumed.

A correlated finite head can be kept as one complete sample. To retain its joint profile, apply the tail chain results for each fixed head point and average under the chosen head law. A covering application still has to identify its actual events, establish their BaseCaps bounds, and prove the integrated charge or stopping estimate. Prefix-capacity realization supplies rational base weights but does not by itself establish those remaining bounds.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison`
- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.covered_probability_le`
- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain.kernels_have_caps`
