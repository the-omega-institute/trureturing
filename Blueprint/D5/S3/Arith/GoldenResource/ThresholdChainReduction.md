# Exact Exponent Box Chain Reduction

## Abstract

The logarithmic Robin margin on a finite prime exponent box is minimized on the chain ordered by exact marginal benefit per logarithmic unit.

**Definition 1.1 (Added layers).**

$$exponentLayers\left(B, U\right) = \{(p,k) \mid p \in primeFactors\left(U\right) \land \left(factorization\left(B, p\right) < k \land k \le factorization\left(U, p\right)\right)\}$$

*Formalization.* `D5/S3/Arith/GoldenResource/ThresholdChainReduction.exponentLayers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For divisibility endpoints B and U, each layer records its prime and its exponent index. The lower endpoint's exponent is excluded and the upper endpoint's exponent is included.

**Definition 1.2 (Exponent box).**

$$exponentBox\left(B, U\right) = \{n \mid n \in divisors\left(U\right) \land B \mid n\}$$

*Formalization.* `D5/S3/Arith/GoldenResource/ThresholdChainReduction.exponentBox` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The divisors of U that are multiples of B have precisely the prime exponents between the two endpoints. When B divides the positive U, this set contains B.

**Definition 1.3 (Ordered integer chain).**

$$layerChain\left(B, U, e, j\right) = B\cdot\prod_{i < card\left(exponentLayers\left(B, U\right)\right), i < j} fst\left(e\left(i\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/ThresholdChainReduction.layerChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equivalence e enumerates every added layer exactly once. Its first j entries multiply B by their prime factors, including repeated primes at different layers. The empty product gives B.

**Theorem 1.4 (The chain attains the box minimum).**

$$\forall B \in \mathbb{N}, U \in \mathbb{N}, e \in Equiv\left(Fin\left(card\left(exponentLayers\left(B, U\right)\right)\right), exponentLayers\left(B, U\right)\right),\; \left(3 \le B \land \left(U \neq 0 \land \left(B \mid U \land \left(\forall i \in Fin\left(card\left(exponentLayers\left(B, U\right)\right)\right), r \in Fin\left(card\left(exponentLayers\left(B, U\right)\right)\right),\; i \le r \Rightarrow goldenLayerMarginal\left(fst\left(e\left(r\right)\right), snd\left(e\left(r\right)\right)\right) \le goldenLayerMarginal\left(fst\left(e\left(i\right)\right), snd\left(e\left(i\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(card\left(exponentLayers\left(B, U\right)\right) = \sum_{p \in primeFactors\left(U\right)} (factorization\left(U, p\right)-factorization\left(B, p\right)) \land \left(card\left(exponentBox\left(B, U\right)\right) = \prod_{p \in primeFactors\left(U\right)} (factorization\left(U, p\right)-factorization\left(B, p\right)+1) \land \left(\left(\forall j \in \mathbb{N},\; j \le card\left(exponentLayers\left(B, U\right)\right) \Rightarrow layerChain\left(B, U, e, j\right) \in exponentBox\left(B, U\right)\right) \land \left(\left(\forall j \in \mathbb{N}, i \in Fin\left(card\left(exponentLayers\left(B, U\right)\right)\right), k \in \mathbb{N},\; \left(j \le card\left(exponentLayers\left(B, U\right)\right) \land \left(i < j \land \left(factorization\left(B, fst\left(e\left(i\right)\right)\right) < k \land k \le snd\left(e\left(i\right)\right)\right)\right)\right) \Rightarrow \left(\exists r \in Fin\left(card\left(exponentLayers\left(B, U\right)\right)\right),\; r < j \land e\left(r\right) = (fst\left(e\left(i\right)\right),k)\right)\right) \land \left(\left(\exists j \in \mathbb{N},\; j \le card\left(exponentLayers\left(B, U\right)\right) \land \left(IsLeast\left(image\left(robinLogMargin, exponentBox\left(B, U\right)\right), robinLogMargin\left(layerChain\left(B, U, e, j\right)\right)\right) \land IsLeast\left(\{robinLogMargin\left(layerChain\left(B, U, e, j\right)\right) \mid j \in \mathbb{N} \land j \le card\left(exponentLayers\left(B, U\right)\right)\}, robinLogMargin\left(layerChain\left(B, U, e, j\right)\right)\right)\right)\right) \land sInf\left(image\left(robinLogMargin, exponentBox\left(B, U\right)\right)\right) = sInf\left(\{robinLogMargin\left(layerChain\left(B, U, e, j\right)\right) \mid j \in \mathbb{N} \land j \le card\left(exponentLayers\left(B, U\right)\right)\}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ThresholdChainReduction.threshold_chain_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume B is at least three, U is nonzero, and B divides U. The enumeration orders the real goldenLayerMarginal values in descending order; equal values may occur in either order. Write M for the number of added layers. There are M+1 chain positions. The displayed cardinalities count the full box and all added layers, including zero-width prime directions. Every chain prefix lies in the box and includes every lower available layer of any prime that it includes. One chain position attains the minimum both over the box and over the chain.

At a box minimizer, the strictly concave function x mapped to log(log x) on x>1 has a supporting tangent with positive slope. A permitted increase of one prime exponent has marginal strictly below that slope; a permitted decrease has marginal strictly above it. Decreasing prime-layer marginals identify the adopted layers as one complete threshold prefix. Their prime product reconstructs the minimizing integer. All comparisons use real logarithms; an approximation does not supply the required order inequalities.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ThresholdChainReduction.exponentBox`
- Truth anchor: `D5/S3/Arith/GoldenResource/ThresholdChainReduction.exponentLayers`
- Truth anchor: `D5/S3/Arith/GoldenResource/ThresholdChainReduction.layerChain`
- Truth anchor: `D5/S3/Arith/GoldenResource/ThresholdChainReduction.threshold_chain_reduction`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](../../Weil/GronwallLowerEnvelope.md)
