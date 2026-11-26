# Positive extension of adjacent Fibonacci marginals

## Abstract

A common-state criterion for two adjacent marginals on three Fibonacci sites.

**Theorem 1.1 (The minimum endpoint-pair weight).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension.extendible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension.extendible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On three sites with adjacent occupation forbidden the legal words are the vacuum, the three singleton words, and the pair of occupied endpoints. Measure the two adjacent edges. Each edge state has a vacuum entry and a two-dimensional singleton block. Entries between the vacuum and singleton sectors are zero. Let the occupations be pA, pB and pC, with the same pB in both edge states. Let alpha and beta be the complex entries from the middle singleton column to the endpoint singleton row.

Put q0 equal to the larger of zero and pA + pB + pC - 1. A common positive semidefinite trace-one state exists exactly when pB is nonnegative, both endpoint occupations are at least q0, and the two squared coherence moduli are at most pB × (pA - q0) and pB × (pC - q0), respectively.

The actual endpoint-pair weight q is at least q0 by positivity of the vacuum weight. The two specified principal minors of the singleton block then give the necessary coherence bounds. For sufficiency choose q0. With positive central weight, one outer product supplies both specified coherences, and nonnegative diagonal residuals supply the remaining endpoint singleton weights. With zero central weight both coherences vanish. Completing by the vacuum and endpoint-pair weights gives a trace-one state with both required partial traces.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension.extendible_iff`
