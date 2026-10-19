# The lower Gelfand–Naimark ratio inequality

## Abstract

The lower Gelfand–Naimark ratio inequality.

**Theorem 1.1 (Arbitrary-subset singular-value ratios).**

Lean statement: `D5/S3/Quantum/Schatten/LowerGelfandNaimark.lower_gelfand_naimark_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/LowerGelfandNaimark.lower_gelfand_naimark_ratio` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For invertible complex n by n matrices C and D and any subset I of the decreasing singular-value indices, the product over i in I of sᵢ(CD)/sᵢ(D) is at most the product of the |I| largest singular values of C. Invertibility makes every denominator positive; the empty subset gives the empty product one. The proof clips the scaled singular values of C below at one, compares Gram matrices, and bounds the subset product by the full determinant product.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/LowerGelfandNaimark.lower_gelfand_naimark_ratio`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](SingularValueOrder.md)
