# Odd Binary Relations and Unique Short Supports

## Abstract

Odd binary relations have unique representatives of weight at most half.

The seven nonzero ground sections have one repetition relation. Consequently each finite six-bit label has a unique coefficient vector whose Hamming support has size at most three.

**Theorem 1.1 (Unique short support representative).**

Lean statement: `D5/S3/VertexAlgebra/MonsterShortSupport.unique_short_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterShortSupport.unique_short_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. J. MacWilliams and N. J. A. Sloane (1977). *The Theory of Error-Correcting Codes*. URL: <https://archive.org/details/theoryoferrorcor00macw>.

*Commentary.*

The proof combines the kernel characterization from MonsterFusionSpan with the odd complement argument for the binary repetition code. It is a finite label theorem only: it does not assert a VOA realization, an OPE coefficient, or a Monster action.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterShortSupport.unique_short_support`
- Dependency: [D5/S3/VertexAlgebra/MonsterFusionSpan](MonsterFusionSpan.md)
