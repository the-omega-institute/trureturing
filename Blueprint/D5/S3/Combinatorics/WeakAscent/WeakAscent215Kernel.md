# Kernel Coefficient Recursions

## Abstract

Coefficient recursions specify the common counting series and the small root of a bivariate kernel.

**Definition 1.1 (The positive-series transformation).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.positiveStep`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.positiveStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a formal power series T over a commutative semiring, the positive-series transformation is (1 + xT) squared plus x squared times (1 + xT) squared times T.

**Definition 1.2 (The natural-number coefficient recursion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.kernelCoefficients`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.kernelCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The coefficient c_d is defined recursively as the coefficient of degree d in the positive-series transformation applied to the series with coefficients c_i for i less than d and zero coefficients from degree d onward.

**Definition 1.3 (The target counting series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.targetSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.targetSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The target series over the rational numbers is 1 + x times the series whose coefficient of degree d is c_d, where c_d is given by the natural-number kernel recursion.

**Definition 1.4 (Coefficients of the small root).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRootCoefficients`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRootCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a bivariate rational power series K indexed by a distinguished coordinate and one other coordinate, define u_d recursively as the coefficient of degree d in x + x squared times K evaluated at x in the distinguished coordinate and at the series with coefficients u_i for i less than d and zero coefficients thereafter in the other coordinate.

**Definition 1.5 (The small-root series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRoot`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The small root associated with K is the rational power series whose coefficient of degree d is u_d from the small-root coefficient recursion.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.kernelCoefficients`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.positiveStep`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRoot`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.smallRootCoefficients`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel.targetSeries`
