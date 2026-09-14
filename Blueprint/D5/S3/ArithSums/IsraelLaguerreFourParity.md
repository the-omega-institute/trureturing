# Israel's Laguerre Polynomial Parity Conjectures

## Abstract

Laguerre(n,4) has odd reduced numerator and denominator for every natural n.

**Definition 1.1 (The Laguerre polynomial at four).**

$$\forall n \in \mathbb{N},\; L\left(n\right) = \sum_{k = 0}^{n} binomial\left(n, k\right) \cdot (-4)^{k} / k!$$

*Formalization.* `D5/S3/ArithSums/IsraelLaguerreFourParity.L` (`✓ std3`).

*Citation.* N. J. A. Sloane; Robert Israel (2018). *OEIS A160627, Numerator of Laguerre(n, 4)*. URL: <https://oeis.org/A160627>.

*Commentary.*

The finite binomial sum is the classical Laguerre polynomial evaluated at x=4. The operator binomial denotes Nat.choose, and the slash denotes rational division after the natural factorial is cast to Q.

**Theorem 1.2 (Odd numerator and denominator).**

$$\forall n \in \mathbb{N},\; (Odd\left(num\left(L\left(n\right)\right)\right)) \land (Odd\left(den\left(L\left(n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/IsraelLaguerreFourParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a160627-israel-laguerre-four-parity` (proved) by `D5/S3/ArithSums/IsraelLaguerreFourParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a160627-israel-laguerre-four-parity","declaration_gid":"D5/S3/ArithSums/IsraelLaguerreFourParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane; Robert Israel (2018). *OEIS A160627, Numerator of Laguerre(n, 4)*. URL: <https://oeis.org/A160627>.

*Commentary.*

Every nonconstant summand has positive 2-adic valuation because the valuation of k factorial is less than k. The ultrametric sum law therefore gives valuation zero for L(n). Reducedness then excludes a factor of two from both num(L(n)) and den(L(n)).

## References

- Truth anchor: `D5/S3/ArithSums/IsraelLaguerreFourParity.L`
- Truth anchor: `D5/S3/ArithSums/IsraelLaguerreFourParity.result`
