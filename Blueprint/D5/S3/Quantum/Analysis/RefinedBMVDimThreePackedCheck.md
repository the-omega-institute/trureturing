# Integer coefficients for the three-dimensional refined BMV bound

## Abstract

Integer coefficients for the three-dimensional refined BMV bound

**Theorem 1.1 (Packed sign comparison for five first factors).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck.mask_check_five`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck.mask_check_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

In Hägele’s three-dimensional pairing, combine the first two radicands into their sum Q, and let W be the third radicand. If Z is the deficit at the three distinct indices, the polynomial is four times Q times W minus the square of Z squared minus Q minus W. Evaluate this polynomial at a positional encoding of the ordered cube-root coordinates. After adding the digit midpoint, one bit in each digit tests whether the corresponding coefficient is nonnegative. Exact integer evaluation gives the comparison for five first factors.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck.mask_check_five`
