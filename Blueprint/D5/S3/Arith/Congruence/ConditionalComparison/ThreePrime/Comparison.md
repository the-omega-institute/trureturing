# Conditional Convex Comparison

## Abstract

Schroeder's conditional convex comparison for arbitrary finite histories and label supports.

**Theorem 1.1 (Actual conditional loads are dominated by aligned auxiliary loads).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison` (`✓ std3`). ∎

*Citation.* Michael Schroeder (2026). *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. DOI: [10.5281/zenodo.22760638](https://doi.org/10.5281/zenodo.22760638). URL: <https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip>.

*Commentary.*

This is a source transplant of Michael Schroeder's theorem Erdos7.ThreePrime.convex_load_comparison. The full MIT license, source archive and import mapping are recorded in `D5/L/Arith/schroeder2026noncoverage`.

A KernelChain on a finite alphabet retains the complete preceding coordinate tuple in every conditional kernel. For every label and every history, HasCaps bounds its coordinate-event probability by the survival function of a finite auxiliary run at that label's depth. The finite depth bound and nonnegative rational weights are explicit hypotheses.

For every increasing convex rational-valued function, the expected function of the actual active-label load is at most its expectation under the product of the auxiliary run laws, with a label active precisely when all its depths are below the auxiliary heights. The actual coordinate events need not be nested, and their law need not be a product law. There is no bound on the number of coordinates used by one label. Nonnegativity of the convex function is not required.

The imported proof eliminates coordinates backwards using the finite increasing-supermodular rearrangement. The ThreePrime source directory name does not impose a three-prime hypothesis on this declaration. This module supplies the existing comparison theorem; a covering-system application must still construct its actual kernels and discharge every cap hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.convex_load_comparison`
