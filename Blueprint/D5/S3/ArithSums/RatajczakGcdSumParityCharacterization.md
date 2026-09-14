# Ratajczak's A008590 gcd-filtered sum characterization

## Abstract

Both of Ratajczak's gcd-filtered sums are even exactly at multiples of eight above one.

**Definition 1.1 (The second greatest common divisor).**

$$\forall k \in \mathrm{Nat}, m \in \mathrm{Nat},\; \operatorname{gcd}_{2}\left(k, m\right) = \operatorname{gcd}\left(k, m\right) / \operatorname{lpf}\left(\operatorname{gcd}\left(k, m\right)\right)$$

*Formalization.* `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.gcd2` (`✓ std3`).

*Citation.* N. J. A. Sloane; Lechoslaw Ratajczak (2017). *OEIS A008590, Multiples of 8*. URL: <https://oeis.org/A008590>.

*Commentary.*

For a non-coprime pair, gcd_2 is the greatest proper divisor of the greatest common divisor. The slash denotes natural-number division.

**Definition 1.2 (The second least common divisor).**

$$\forall k \in \mathrm{Nat}, m \in \mathrm{Nat},\; \operatorname{lcd}_{2}\left(k, m\right) = \operatorname{lpf}\left(\operatorname{gcd}\left(k, m\right)\right)$$

*Formalization.* `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.lcd2` (`✓ std3`).

*Citation.* N. J. A. Sloane; Lechoslaw Ratajczak (2017). *OEIS A008590, Multiples of 8*. URL: <https://oeis.org/A008590>.

*Commentary.*

For a non-coprime pair, lcd_2 is the least divisor greater than one of the greatest common divisor.

**Definition 1.3 (The gcd_2-filtered sum).**

$$\forall m \in \mathrm{Nat},\; \operatorname{G}\left(m\right) = \sum_{k \in \{k \in [1, m] \mid \operatorname{gcd}\left(k, m\right) \ne 1\}} \operatorname{gcd}_{2}\left(k, m\right)$$

*Formalization.* `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.G` (`✓ std3`).

*Citation.* N. J. A. Sloane; Lechoslaw Ratajczak (2017). *OEIS A008590, Multiples of 8*. URL: <https://oeis.org/A008590>.

*Commentary.*

The sum ranges from one through m and retains exactly the indices k that are not coprime to m. Each retained term is gcd_2(k,m).

**Definition 1.4 (The lcd_2-filtered sum).**

$$\forall m \in \mathrm{Nat},\; \operatorname{L}\left(m\right) = \sum_{k \in \{k \in [1, m] \mid \operatorname{gcd}\left(k, m\right) \ne 1\}} \operatorname{lcd}_{2}\left(k, m\right)$$

*Formalization.* `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.L` (`✓ std3`).

*Citation.* N. J. A. Sloane; Lechoslaw Ratajczak (2017). *OEIS A008590, Multiples of 8*. URL: <https://oeis.org/A008590>.

*Commentary.*

The sum has the same gcd filter as G and replaces each term by lcd_2(k,m).

**Theorem 1.5 (The simultaneous parity classification).**

$$\forall m \in \mathrm{Nat},\; (m > 1) \Rightarrow (((\operatorname{Even}\left(\operatorname{G}\left(m\right)\right)) \land (\operatorname{Even}\left(\operatorname{L}\left(m\right)\right))) \Leftrightarrow (8 \mid m))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a008590-gcd-sum-parity-characterization` (proved) by `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a008590-gcd-sum-parity-characterization","declaration_gid":"D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The gcd-filtered involution parity lemma pairs k with m-k and isolates m/2 as the only possible fixed point. The resulting modulo-four classification proves that both sums are even exactly when eight divides m. At m=1 both filtered sums are empty and even, so the hypothesis excludes that boundary.

## References

- Truth anchor: `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.G`
- Truth anchor: `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.L`
- Truth anchor: `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.gcd2`
- Truth anchor: `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.lcd2`
- Truth anchor: `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.result`
