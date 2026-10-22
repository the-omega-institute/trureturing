# Half-density modes of the asymmetric K-exclusion process

## Abstract

The half-density K-exclusion mode for small and large positive parameters.

**Definition 1.1 (The t-integer).**

$$\forall t \in \mathbb{R},\; \forall k \in \mathbb{N},\; \operatorname{qnum}\left(t, k\right) = \sum_{j\in \operatorname{Finset}.\operatorname{range}\left(k\right)} t^{j}$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qnum` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 4: “We define the t-analog of a nonnegative integer k as”. Equation (4) is [k] ≡ [k]t = ∑ᵢ₌₀ᵏ⁻¹ tⁱ. The sum over range k also gives [0] = 0.

**Definition 1.2 (The t-factorial).**

$$\forall t \in \mathbb{R},\; \forall k \in \mathbb{N},\; \operatorname{qfact}\left(t, k\right) = \prod_{j\in \operatorname{Finset}.\operatorname{range}\left(k\right)} \operatorname{qnum}\left(t, j + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qfact` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 6: “The t-analogue of the factorial is given by”. Equation (8) is [k]! ≡ [k]t! = [1][2] · · · [k]. The empty product is one.

**Definition 1.3 (The t-binomial coefficient).**

$$\forall t \in \mathbb{R},\; \forall k \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{qbinom}\left(t, k, i\right) = (\operatorname{if} i \le k \operatorname{then} \frac{\operatorname{qfact}\left(t, k\right)}{\operatorname{qfact}\left(t, k - i\right) \cdot \operatorname{qfact}\left(t, i\right)} \operatorname{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qbinom` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 6: “The t-binomial coefficient or Gaussian polynomial is”. Equation (9) is [k choose i] ≡ [k choose i]t = [k]! / ([k − i]![i]!). It is zero when i exceeds k. All indices are natural numbers and their subtraction is truncated.

**Definition 1.4 (The steady-state weight).**

$$\forall K \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall t \in \mathbb{R},\; \forall eta \in \operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left((K + 1)\right),\; \operatorname{wt}\left(K, L, t, eta\right) = \prod_{i\in \operatorname{Fin}\left(L\right)} t^{\operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(\operatorname{eta}\left(i\right)\right) \cdot \operatorname{val}\left(\operatorname{eta}\left(i\right)\right) + 2 - 3 \cdot \operatorname{val}\left(\operatorname{eta}\left(i\right)\right), 2\right)} \cdot \operatorname{qbinom}\left(t, K, \operatorname{val}\left(\operatorname{eta}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.wt` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 6: “We will show in Section 3 that the steady state weight is given by the formula,” Equation (11) is wtη(t) = ∏ᵢ t^((ηᵢ−1)(ηᵢ−2)/2) [K choose ηᵢ]. For natural a the exponent is Nat.div (a*a+2−3*a) 2; subtraction is truncated. Its values for a = 0,1,2,3,4 are 1,0,0,1,3.

**Definition 1.5 (Configurations with a fixed particle count).**

$$\forall K \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{configs}\left(K, L, n\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} eta:\operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left((K + 1)\right) \mapsto \sum_{i\in \operatorname{Fin}\left(L\right)} \operatorname{val}\left(\operatorname{eta}\left(i\right)\right) = n), (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left((K + 1)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.configs` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 4: “We denote the set of configurations by” ΩL,n ≡ ΩK L,n = {η ∈ {0, 1, . . . , K}ᴸ | ∑ᵢ₌₁ᴸ ηᵢ = n}. A configuration is a function from Fin L to Fin (K+1); the sum of its natural values is n.

**Definition 1.6 (The one-site marginal).**

$$\forall K \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{R},\; \forall s \in \operatorname{Fin}\left(L\right),\; \forall a \in \mathbb{N},\; \operatorname{occProb}\left(K, L, n, t, s, a\right) = \frac{\sum_{eta\in \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} eta:\operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left((K + 1)\right) \mapsto \operatorname{val}\left(\operatorname{eta}\left(s\right)\right) = a), \operatorname{configs}\left(K, L, n\right)\right)} \operatorname{wt}\left(K, L, t, eta\right)}{\sum_{eta\in \operatorname{configs}\left(K, L, n\right)} \operatorname{wt}\left(K, L, t, eta\right)}$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.occProb` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Page 6: “Then the steady state probability of η is”. Equation (13) is π(η) = wtη(t) / ZL,n(t). Summing this distribution over configurations whose s-th value is a gives the displayed marginal. The numerator and denominator use exactly the weights of equation (11).

**Definition 1.7 (The answer to the half-density question).**

$$claim = (\forall r \in \mathbb{N},\; \forall K \in \mathbb{N},\; \forall k \in \mathbb{N},\; (2 \le r) \Rightarrow ((1 \le K) \Rightarrow ((k < K) \Rightarrow ((\operatorname{let} s:\operatorname{Fin}\left(2 \cdot r\right)=0; \exists e \in \mathbb{R},\; (0 < e) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (((t < e) \lor (\frac{1}{e} < t)) \Rightarrow (((2 \cdot k + 1 < K) \Rightarrow (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right))))) \land (((K < 2 \cdot k + 1) \Rightarrow (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k + 1) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k + 1\right))))) \land ((2 \cdot k + 1 = K) \Rightarrow ((\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right) = \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k + 1\right)) \land (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k) \Rightarrow ((b \ne k + 1) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right))))))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.claim` (`✓ std3`).

*Citation.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

Section 4.5, page 21: “We focus on when t ≪ 1 and t ≫ 1. From the discussion in Sections 4.2 and 4.3, we know that the most likely number of particles is either k or k + 1. The question we want to address is which one is most likely.” The answer concerns L = 2r with r ≥ 2, K ≥ 1, k < K and n = (2k+1)r. The site s is the element of Fin (2r) with value zero. For all sufficiently small positive t and all sufficiently large t, the unique mode is k below half filling and k+1 above half filling. At exact half filling k and k+1 tie and dominate the other occupations in these two regimes.

**Theorem 1.8 (The modal comparisons in both parameter extremes).**

$$\forall r \in \mathbb{N},\; \forall K \in \mathbb{N},\; \forall k \in \mathbb{N},\; (2 \le r) \Rightarrow ((1 \le K) \Rightarrow ((k < K) \Rightarrow ((\operatorname{let} s:\operatorname{Fin}\left(2 \cdot r\right)=0; \exists e \in \mathbb{R},\; (0 < e) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (((t < e) \lor (\frac{1}{e} < t)) \Rightarrow (((2 \cdot k + 1 < K) \Rightarrow (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right))))) \land (((K < 2 \cdot k + 1) \Rightarrow (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k + 1) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k + 1\right))))) \land ((2 \cdot k + 1 = K) \Rightarrow ((\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right) = \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k + 1\right)) \land (\forall b \in \mathbb{N},\; (b \le K) \Rightarrow ((b \ne k) \Rightarrow ((b \ne k + 1) \Rightarrow (\operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, b\right) < \operatorname{occProb}\left(K, 2 \cdot r, (2 \cdot k + 1) \cdot r, t, s, k\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result` (`✓ std3`). ∎

*Resolves.* `Problems/ayyer-misra-2023-half-density-most-likely-occupation` (proved) by `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ayyer-misra-2023-half-density-most-likely-occupation","declaration_gid":"D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arvind Ayyer and Samarth Misra (2024). *An exactly solvable asymmetric K-exclusion process*. DOI: [10.1088/1751-8121/ad5edd](https://doi.org/10.1088/1751-8121/ad5edd). URL: <https://arxiv.org/abs/2310.03343v2>.

*Commentary.*

The finite t-binomial identity expresses the weights as sums over occupied slots with energy equal to the sum of their levels. Reflecting the block of levels 0 through 2k and then taking its complement pairs the adjacent occupations while preserving particle count and energy. Below half filling, the first unpaired energy layer has an excess of 3*Nat.choose (2r−1) (r−2) configurations favouring k. Its positivity determines the sign near zero. Particle-hole symmetry gives the comparison above half filling and the exact tie. Every marginal is unchanged by replacing t by its reciprocal, so the same comparisons hold for large t. The classification for intermediate positive t remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.claim`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.configs`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.occProb`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qbinom`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qfact`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.qnum`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result`
- Truth anchor: `D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.wt`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuDefs](../CylindricPartition/LiUncuDefs.md)
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian](../CylindricPartition/LiUncuGaussian.md)
