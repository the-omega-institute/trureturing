# Zero Slope Is Optimal Exactly When the Weighted Index Sum Is Balanced

## Abstract

A finite sample is fitted best by a line of zero slope exactly when its position-weighted total is balanced against its total, because completing the square in the slope and the intercept leaves the centred cross term as the only obstruction.

**Definition 1.1 (Squared error of an affine fit).**

$$E(c, b, \alpha, \beta) = \sum_{i=0}^{c-1}(b_i-\alpha-\beta(i+1))^{2}$$

*Formalization.* `D5/S3/Combinatorics/LeastSquaresBinaryFit.sqError` (`✓ std3`).

*Citation.* R. H. Hardin; Gus Wiseman (2023). *OEIS A222955, Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line*. URL: <https://oeis.org/A222955>.

*Commentary.*

The sample is a list of rational values indexed from zero, read as the points whose abscissa is one more than the index. The squared error of an affine function is the sum over the sample of the square of the residual. Nothing restricts the values to two, so the object is a fit to an arbitrary finite rational sample.

**Definition 1.2 (Optimality of a line of zero slope).**

$$(Z(c, b)) \Leftrightarrow (\exists \alpha_{0}, \forall \alpha, \forall \beta, E(c, b, \alpha_{0}, 0)\leq E(c, b, \alpha, \beta))$$

*Formalization.* `D5/S3/Combinatorics/LeastSquaresBinaryFit.ZeroSlopeOptimal` (`✓ std3`).

*Citation.* R. H. Hardin; Gus Wiseman (2023). *OEIS A222955, Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line*. URL: <https://oeis.org/A222955>.

*Commentary.*

A line of zero slope is optimal when some constant function attains a squared error no larger than that of any affine function. Optimality is phrased as attainment rather than as uniqueness of the minimiser, which is what the source entry's convention on a single point requires: one point is fitted exactly by every line through it, and the entry declares that case to have zero slope.

**Definition 1.3 (Balance of the weighted total).**

$$(B(c, b)) \Leftrightarrow (2\sum_{i=0}^{c-1}(i+1)b_i = (c+1)\sum_{i=0}^{c-1}b_i)$$

*Formalization.* `D5/S3/Combinatorics/LeastSquaresBinaryFit.BalancedPositions` (`✓ std3`).

*Citation.* R. H. Hardin; Gus Wiseman (2023). *OEIS A222955, Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line*. URL: <https://oeis.org/A222955>.

*Commentary.*

Twice the position-weighted total equals the length plus one times the total. For a binary word this says the positions of the ones sum to the same value before and after reversal, since reversal sends a position to the length plus one minus that position; equivalently the average position of a one is the midpoint of the index range.

**Definition 1.4 (The conjectured bridge).**

$$(claim) \Leftrightarrow (\forall c, \forall b, (0< c) \Rightarrow ((Z(c, b)) \Leftrightarrow (B(c, b))))$$

*Formalization.* `D5/S3/Combinatorics/LeastSquaresBinaryFit.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Gus Wiseman (2023). *OEIS A222955, Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line*. URL: <https://oeis.org/A222955>.

*Commentary.*

The source asserts that a binary word is counted by the entry precisely when it has the same sum of positions of ones as its reverse. The statement below carries no restriction to binary values, so the assertion about words is the instance in which every value is zero or one.

**Theorem 1.5 (The bridge holds).**

$$\forall c, \forall b, (0< c) \Rightarrow ((Z(c, b)) \Leftrightarrow (B(c, b)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LeastSquaresBinaryFit.result` (`✓ std3`). ∎

*Resolves.* `Problems/least-squares-zero-slope-binary-words` (proved) by `D5/S3/Combinatorics/LeastSquaresBinaryFit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"least-squares-zero-slope-binary-words","declaration_gid":"D5/S3/Combinatorics/LeastSquaresBinaryFit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Gus Wiseman (2023). *OEIS A222955, Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line*. URL: <https://oeis.org/A222955>.

*Commentary.*

Write the total, the position-weighted total, the mean value and the mean position; subtract the means to obtain the centred value and the centred position; and let the cross term be the sum of their products. For any intercept and slope, setting the shifted intercept to the mean value minus the intercept minus the slope times the mean position turns each residual into the centred value minus the slope times the centred position plus that shift. Expanding the square and summing, the two terms linear in the shift vanish because centred quantities sum to zero, leaving the squared error minus the centred total of squares equal to the slope squared times the sum of squared centred positions, plus the length times the shift squared, minus twice the slope times the cross term. When the cross term vanishes the remainder is a sum of two squares with nonnegative coefficients, so the mean with zero slope is optimal. When it does not vanish the length is at least two, so the sum of squared centred positions is positive, and taking the slope to be the cross term divided by it with zero shift makes the remainder negative, which no optimal line permits. At length one the centred position vanishes, so the cross term vanishes with it and both sides hold. The cross term equals the position-weighted total minus the mean position times the total, so its vanishing is the balance condition.

## References

- Truth anchor: `D5/S3/Combinatorics/LeastSquaresBinaryFit.BalancedPositions`
- Truth anchor: `D5/S3/Combinatorics/LeastSquaresBinaryFit.ZeroSlopeOptimal`
- Truth anchor: `D5/S3/Combinatorics/LeastSquaresBinaryFit.claim`
- Truth anchor: `D5/S3/Combinatorics/LeastSquaresBinaryFit.result`
- Truth anchor: `D5/S3/Combinatorics/LeastSquaresBinaryFit.sqError`
