# A counterexample to the cyclic arrangement conjecture

## Abstract

The cyclic arrangement conjecture fails at the nonnegative parameters a=6 and b=1.

Javaheri's arXiv:2610.33653v1 Conjecture 1.3 identifies the largest dimension in which a cyclic power inequality holds with the largest dimension selected by a sine threshold. The formal statement keeps the real nonnegative parameter domain, the cyclic successor, the extended-natural least-upper-bound definition of the valid dimension, and the greatest-element definition of the threshold dimension.

**Theorem 1.1 (The universal dimension identity is false).**

Lean statement: `D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/javaheri-2026-cyclic-arrangement-conjecture-refutation` (refuted) by `D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"javaheri-2026-cyclic-arrangement-conjecture-refutation","declaration_gid":"D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result","resolution_kind":"refuted"} -->

*Citation.* Mohammad Javaheri (2026). *A new arrangement inequality (revised and extended version)*. DOI: [10.48550/arXiv.2610.33653](https://doi.org/10.48550/arXiv.2610.33653). URL: <https://arxiv.org/abs/2610.33653v1>.

*Commentary.*

At a=6 and b=1, the threshold set has greatest element 3. The positive cyclic triple (6,5,5) makes the difference between the two sides equal to 364, so dimension 3 is not valid. The least-upper-bound specification of a valid dimension therefore cannot equal the threshold greatest element, contradicting the universal conjecture.

## References

- Truth anchor: `D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result`
