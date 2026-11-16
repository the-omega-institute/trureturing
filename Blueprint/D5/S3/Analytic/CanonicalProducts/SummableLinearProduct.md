# Summable linear products of zero exponential type

## Abstract

Compact uniform convergence and a finite-head small-tail estimate for actual unordered products.

**Theorem 1.1 (Actual entire product and zero exponential type).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SummableLinearProduct.entire_zero_type_of_summable_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SummableLinearProduct.entire_zero_type_of_summable_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any index type I and complex coefficient family c with summable norms, the unordered linear product is multipliable at every complex point and differentiable on the whole plane. For every positive real epsilon there is a real A at least one bounding its norm by A times exp(epsilon times the point norm). The proof uses Mathlib local uniform product convergence on compact sets; a finite head is absorbed into A while the summable tail spends half the exponential budget. Zeros of individual factors and finite or empty index sets remain allowed. This supplies the actual analytic product used by SparseQuartetProduct.actual_product_analytic.

The sole assumption is absolute coefficient summability. This is a zero exponential type statement, with a new constant for each positive epsilon; it makes no minimal-type classification or claim about the Riemann zeta function. These are general analytic estimates, not bounded enumeration, a numerical reduction, a checker, or a certified finite instance; utility is none. The proof combines existing Mathlib convergence results with the head-tail growth estimate; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SummableLinearProduct.entire_zero_type_of_summable_norm`
