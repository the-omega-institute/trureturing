# Generating Function for a Marked Interior Descent

## Abstract

The sum of weights on interior descents is related to the weight on the final descent.

**Theorem 1.1 (Weighted interior descents).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries.marked_interior_descent_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries.marked_interior_descent_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let R be a commutative ring and w a function from nonnegative integers to R with w(0) = 0. Write C(x) for the Catalan series. In degree n, let M(x) sum, over Dyck paths of semilength n, the weights w of the lengths of all nonempty descents except the last, and let F(x) sum the weight w of the final descent length. The empty path has final descent length zero. Then (2 - C(x)) M(x) = (C(x) - 1) F(x).

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries.marked_interior_descent_enumeration`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor](InversionSeq152Factor.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection](InversionSeq152Reflection.md)
