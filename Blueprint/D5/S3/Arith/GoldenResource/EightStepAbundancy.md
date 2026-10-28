# Eight-Step Abundancy Maximum

## Abstract

The unique largest abundancy at eight prime factors counted with multiplicity is attained by 180180 and equals 224/55.

**Definition 1.1 (Prime-layer denominator).**

$$\forall p \in \mathbb{N}, k \in \mathbb{N},\; D\left(p, k\right) = \sum_{i \in range\left(k\right)} p^{i + 1}$$

*Formalization.* `D5/S3/Arith/GoldenResource/EightStepAbundancy.layerDenominator` (`✓ std3`).

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

D(p,k) denotes layerDenominator p k. It sums p to the powers one through k, with an empty sum at k = 0. For a prime p and a positive layer k, the multiplicative abundancy gain is 1 + 1/D(p,k).

**Theorem 1.2 (Monotonicity in the layer depth).**

Lean statement: `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_mono` (`✓ std3`). ∎

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

For every natural p and depths a<=b, B(p,a)<=B(p,b). This is finite-sum monotonicity on nested ranges and supplies the denominator comparison in an actual prime-layer exchange.

**Theorem 1.3 (Positive prime-layer denominator).**

Lean statement: `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_pos` (`✓ std3`). ∎

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

For every prime p and positive depth k, B(p,k)>0. The first layer equals p and every later layer adds a nonnegative natural power.

**Theorem 1.4 (The exact multiplicative gain).**

Lean statement: `D5/S3/Arith/GoldenResource/EightStepAbundancy.layer_ratio_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/EightStepAbundancy.layer_ratio_identity` (`✓ std3`). ∎

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

For every prime p and positive depth k, (1-p^(-(k+1)))/(1-p^(-k))=1+1/B(p,k), interpreted in the reals. The finite geometric sum gives this identity and hence the exact gain used in actual one-layer abundancy comparisons.

**Theorem 1.5 (The strict eighth-layer boundary).**

$$\forall p \in \mathbb{N}, k \in \mathbb{N},\; \left(Prime\left(p\right) \land 1 \le k\right) \Rightarrow \left(D\left(p, k\right) < 14 \Leftrightarrow \left(\left(k = 1 \land \left(\left(\left(\left(\left(p = 2 \lor p = 3\right) \lor p = 5\right) \lor p = 7\right) \lor p = 11\right) \lor p = 13\right)\right) \lor \left(k = 2 \land \left(p = 2 \lor p = 3\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/EightStepAbundancy.eight_step_layer_cutoff` (`✓ std3`). ∎

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

The eight events, in denominator order, are (2,1), (3,1), (5,1), (2,2), (7,1), (11,1), (3,2), and (13,1). Their denominators are 2, 3, 5, 6, 7, 11, 12, and 13.

The equivalence quantifies over every prime and every positive layer. Every excluded event has denominator at least 14. The proof first excludes all depths at least three by comparison with 2 + 4 + 8, then classifies the remaining prime bases.

**Theorem 1.6 (The unique eight-step maximizer).**

$$\begin{aligned}Z\left(180180\right) = \frac{224}{55}\\\forall n \in \mathbb{N},\; \left(0 < n \land omega\left(n\right) = 8\right) \Rightarrow \left(Z\left(n\right) \le \frac{224}{55} \land \left(Z\left(n\right) = \frac{224}{55} \Leftrightarrow n = 180180\right)\right)\\Z\left(5040\right) = \frac{403}{105} \land Z\left(5040\right) < Z\left(180180\right)\\omega\left(180180\right) = 8 \land omega\left(5040\right) = 8\\180180 = 2^{2} \cdot 3^{2} \cdot 5 \cdot 7 \cdot 11 \cdot 13\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/EightStepAbundancy.eight_step_abundancy_optimum` (`✓ std3`). ∎

*Citation.* Xiaolong Wu (2019). *A New Type of Abundant Numbers*. DOI: [10.48550/arXiv.1906.05796](https://doi.org/10.48550/arXiv.1906.05796).

*Commentary.*

Here omega(n) is the sum of n's prime exponents, equivalently Mathlib's cardFactors n, and Z(n) is sigma(1,n)/n as a real number. The competitor ranges over every positive natural number with omega(n) = 8, without a bound on n or its prime factors.

The proof applies the existing local threshold theorem at the two prices log(15/14) and log(14/13). Equality at their midpoint forces equality of each exponent. The existing objective factorization then sums the local comparisons over the union of the two finite prime supports; the equal eight-step costs cancel.

The theorem includes the exact values, both eight-step counts, and 180180 = 2^2 * 3^2 * 5 * 7 * 11 * 13. The comparison with 5040 concerns abundancy at fixed step count. It does not assert a comparison for an objective penalizing integer size.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_mono`
- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.denominator_pos`
- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.eight_step_abundancy_optimum`
- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.eight_step_layer_cutoff`
- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.layerDenominator`
- Truth anchor: `D5/S3/Arith/GoldenResource/EightStepAbundancy.layer_ratio_identity`
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](../GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
