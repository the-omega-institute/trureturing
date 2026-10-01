# Generating Function for the Penultimate Descent

## Abstract

The weight of the penultimate descent has a generating function expressed through final descent weights.

**Theorem 1.1 (Weighted penultimate descents).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries.penultimate_descent_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries.penultimate_descent_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let R be a commutative ring and w a function from nonnegative integers to R with w(0) = 0. Write C(x) for the Catalan series. In degree n, let P(x) sum w of the penultimate nonempty descent length over Dyck paths of semilength n, using length zero when there are fewer than two descents. Let F(x) sum w of the final descent length, using zero for the empty path. Then (1 - x) P(x) = x C(x) F(x).

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries.penultimate_descent_enumeration`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor](InversionSeq152Factor.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection](InversionSeq152Reflection.md)
