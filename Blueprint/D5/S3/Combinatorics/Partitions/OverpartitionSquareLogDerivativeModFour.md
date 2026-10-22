# Hanna's Overpartition Logarithmic Derivative Modulo Four

## Abstract

The logarithmic derivative of square-indexed overpartitions has residue twice its index modulo four.

PowerSeries denotes formal power series. X is the indeterminate; coeff extracts a coefficient, mk constructs a series from its coefficient function, and derivative is PowerSeries.derivative. The product is a Finset product over Finset.Icc 1 m. All series in the displayed definitions have rational coefficients. The integer z is explicitly cast to Q in the coefficient equality. Int.ModEq uses integer modulus four. OEIS A219431 has offset one.

**Definition 1.1 (Overpartition coefficients).**

$$\forall m \in \mathbb{N},\; \operatorname{pbar}\left(m\right) = \operatorname{coeff}\left(m, (\prod_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} ((1 + X^{k}) \cdot ((1: \operatorname{PowerSeries}\left(\mathbb{Q}\right)) - X^{k})^{-1}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.pbar` (`✓ std3`).

*Citation.* Paul D. Hanna (2012). *OEIS A219431: logarithmic derivative of square-indexed overpartitions*. URL: <https://oeis.org/A219431>.

*Commentary.*

OEIS A219430, unpaginated Name line: "Number of overpartitions of n^2; a(n) = A015128(n^2)." A015128 counts overpartitions. Its generating function is the product of (1 + X^k)/(1 - X^k) for positive k. At degree m, factors with k > m cannot change the coefficient, giving the finite product displayed here.

**Definition 1.2 (The square-indexed generating function).**

$$\operatorname{G} = \operatorname{mk}\left((\operatorname{fun} n: \mathbb{N} \mapsto \operatorname{pbar}\left(n^{2}\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.G` (`✓ std3`).

*Citation.* Paul D. Hanna (2012). *OEIS A219431: logarithmic derivative of square-indexed overpartitions*. URL: <https://oeis.org/A219431>.

*Commentary.*

OEIS A219430, unpaginated Name line: "Number of overpartitions of n^2; a(n) = A015128(n^2)." The natural index n is squared before pbar is evaluated, including n = 0.

**Definition 1.3 (The logarithmic derivative).**

$$\operatorname{logDerivative} = X \cdot \operatorname{derivative}\left(\operatorname{G}\right) \cdot (\operatorname{G})^{-1}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.logDerivative` (`✓ std3`).

*Citation.* Paul D. Hanna (2012). *OEIS A219431: logarithmic derivative of square-indexed overpartitions*. URL: <https://oeis.org/A219431>.

*Commentary.*

OEIS A219431, unpaginated Name line: "Logarithmic derivative of the g.f. of the overpartitions of n^2 (A219430)." The series is X times the formal derivative of G times its inverse. The factor X gives the entry's indexing starting at one.

**Definition 1.4 (Hanna's congruences).**

$$\operatorname{claim} = (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\exists z \in \mathbb{Z},\; (\operatorname{coeff}\left(m, \operatorname{logDerivative}\right) = (z: \mathbb{Q})) \land (((\operatorname{Odd}\left(m\right)) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 2\right))) \land ((\operatorname{Even}\left(m\right)) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 0\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2012). *OEIS A219431: logarithmic derivative of square-indexed overpartitions*. URL: <https://oeis.org/A219431>.

*Commentary.*

OEIS A219431, unpaginated Comment line: "Conjecture: a(2*n+1) == 2 (mod 4), a(2*n) == 0 (mod 4)." For every natural m >= 1, one integer z equals the rational coefficient and has residue two when m is odd and zero when m is even.

**Theorem 1.5 (The conjecture holds).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\exists z \in \mathbb{Z},\; (\operatorname{coeff}\left(m, \operatorname{logDerivative}\right) = (z: \mathbb{Q})) \land (((\operatorname{Odd}\left(m\right)) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 2\right))) \land ((\operatorname{Even}\left(m\right)) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 0\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a219431-hanna-overpartition-log-derivative-mod-four` (proved) by `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a219431-hanna-overpartition-log-derivative-mod-four","declaration_gid":"D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2012). *OEIS A219431: logarithmic derivative of square-indexed overpartitions*. URL: <https://oeis.org/A219431>.

*Commentary.*

Modulo four, the product of the overpartition factors equals one plus twice the sum of their positive geometric tails: every term containing two factors of two vanishes. Its degree-m coefficient is twice the divisor count. A positive square has an odd divisor count, so G reduces to one plus twice the series with every positive coefficient equal to one. Multiplication by the inverse removes no further terms from twice its derivative modulo four, giving coefficient 2m. The unit constant coefficient of the integer lift ensures that the logarithmic derivative has integer coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.G`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.logDerivative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.pbar`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.result`
- Dependency: [D5/S1/Recurrence/Invariants/ScaledReversionCongruence](../../../S1/Recurrence/Invariants/ScaledReversionCongruence.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../../../S1/Recurrence/LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour](../../../S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs](../TwoColorPartition/AndrewsElBachraouiDefs.md)
