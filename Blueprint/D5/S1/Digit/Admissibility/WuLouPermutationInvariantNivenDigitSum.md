# Permutation-Invariant Niven Digit-Sum Bound

## Abstract

Wu and Lou's permutation-invariant decimal Niven digit-sum bound.

DecimalPINN is the source-faithful object: a nonempty list of decimal digits whose digit sum divides the Nat.ofDigits value of every list permutation.

**Definition 1.1 (Permutation-invariant decimal Niven number).**

Lean statement: `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.DecimalPINN`

*Formalization.* `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.DecimalPINN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Huiling Wu; Sen-Yue Lou (2025). *Permutation-Invariant Niven Numbers*. DOI: [10.3390/sym18010186](https://doi.org/10.3390/sym18010186). URL: <https://arxiv.org/abs/2508.01611>.

*Commentary.*

The structure records a nonempty decimal digit list, its nonzero leading digit, the bound that every digit is below ten, and divisibility of every permuted Nat.ofDigits value by the source digit sum.

**Theorem 1.2 (Distinct-digit digit-sum bound).**

Lean statement: `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-lou-permutation-invariant-niven-digit-sum-bound` (proved) by `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-lou-permutation-invariant-niven-digit-sum-bound","declaration_gid":"D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Huiling Wu; Sen-Yue Lou (2025). *Permutation-Invariant Niven Numbers*. DOI: [10.3390/sym18010186](https://doi.org/10.3390/sym18010186). URL: <https://arxiv.org/abs/2508.01611>.

*Commentary.*

For at least two nonzero digit occurrences and at least two distinct digit values, the digit sum is divisible by three, is at least three, and is at most 81. The divisibility-by-three clause is literature-attested by Wu and Lou's Theorem 1 consequence in section 8.4; the lower bound follows from positivity; the upper bound is the repository-derived settlement of the conjectural bound. The formal proof reuses the source object's permutation-divisibility field and arithmetic normalization.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.DecimalPINN`
- Truth anchor: `D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.result`
