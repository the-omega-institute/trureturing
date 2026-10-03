# Generating Function for the Final Descent

## Abstract

The final descent statistic has a generating function determined by the Catalan series.

**Theorem 1.1 (Final descent weights).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries.final_descent_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries.final_descent_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let R be a commutative ring, q an element of R and C(x) the Catalan series with coefficients in R. Let H(x) have, as its coefficient of x to the power n, the sum of q to the power d over Dyck paths of semilength n, where d is the length of the final descent. The empty path has d equal to zero. Then (1 - q x C(x)) H(x) = 1.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries.final_descent_enumeration`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor](InversionSeq152Factor.md)
