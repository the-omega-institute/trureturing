# Continuation Series for the Second Class

## Abstract

Two continuation counts and rational power series encode the second avoidance class.

**Definition 1.1 (The paired continuation recursion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.continuationCounts`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.continuationCounts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For every nonnegative budget b, define q_0(b) = p_0(b) = 1. For nonnegative d, let S_d(b) be the sum of p_d(i + 1) over integers i from zero through b minus one. Then q_(d+1)(b) = q_d(b + 1) + S_d(b), and p_(d+1)(b) = q_d(b) + p_d(b + 1) + S_d(b). The continuation counts are the ordered pair of these q and p values.

**Definition 1.2 (The q continuation series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.qSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.qSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a nonnegative budget b, the rational power series Q_b(x) has coefficient q_d(b) in degree d.

**Definition 1.3 (The p continuation series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.pSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.pSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a nonnegative budget b, the rational power series P_b(x) has coefficient p_d(b) in degree d.

**Definition 1.4 (The numerator series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.numerator`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a rational power series T, the numerator series is T squared times the formal inverse of 1 minus x squared times T squared.

**Definition 1.5 (The ratio series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.ratio`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a rational power series T, the ratio series is its numerator series multiplied by the formal inverse of T, with the inverse taken to be zero when T has zero constant coefficient.

**Definition 1.6 (The positive-base series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.positiveBase`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.positiveBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a rational power series T, the positive-base series is its numerator series multiplied by 1 + xT.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.continuationCounts`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.numerator`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.pSeries`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.positiveBase`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.qSeries`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215RightCounting.ratio`
