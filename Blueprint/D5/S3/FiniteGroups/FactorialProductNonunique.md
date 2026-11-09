# Nonuniqueness of factorial-weight products

## Abstract

The products of n!/n^n do not uniquely determine a finite set of distinct integers greater than one.

**Definition 1.1 (The unrestricted set assertion).**

$$claim = \left(\forall A \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall B \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\forall m \in \mathbb{N},\; (m \in A) \Rightarrow (1 < m)) \Rightarrow ((\forall m \in \mathbb{N},\; (m \in B) \Rightarrow (1 < m)) \Rightarrow ((\prod_{m \in A}\operatorname{orbitWeight}\left(m\right) = \prod_{m \in B}\operatorname{orbitWeight}\left(m\right)) \Rightarrow (A = B)))\right)$$

*Formalization.* `D5/S3/FiniteGroups/FactorialProductNonunique.claim` (`✓ std3`).

*Citation.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Problem 5.6 of Aivazidis, Loukaki and Müller asks whether equal finite products of f(m)=Gamma(m+1)/m^m force the same distinct integer parameters after reordering. For integers m greater than one, f(m)=m!/m^m. The claim quantifies every two finite sets of natural numbers whose members exceed one. It imposes no bound, equal-cardinality hypothesis, prime restriction or group realization. The function orbitWeight is the original rational factorial-weight definition.

**Theorem 1.2 (Two disjoint sets with equal products).**

$$\neg(\forall A \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall B \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\forall m \in \mathbb{N},\; (m \in A) \Rightarrow (1 < m)) \Rightarrow ((\forall m \in \mathbb{N},\; (m \in B) \Rightarrow (1 < m)) \Rightarrow ((\prod_{m \in A}\operatorname{orbitWeight}\left(m\right) = \prod_{m \in B}\operatorname{orbitWeight}\left(m\right)) \Rightarrow (A = B))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FactorialProductNonunique.result` (`✓ std3`). ∎

*Resolves.* `Problems/alm2024-factorial-product-uniqueness` (refuted) by `D5/S3/FiniteGroups/FactorialProductNonunique.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alm2024-factorial-product-uniqueness","declaration_gid":"D5/S3/FiniteGroups/FactorialProductNonunique.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Take A={10,17,21,23,24,27,38,45,46,48,56,65,68,77,80,84,95,141} and B={11,16,20,22,25,26,39,44,47,49,57,64,69,76,81,85,94,140}. Both sets have eighteen elements, they are disjoint, and every member is greater than one. Their factorial-weight products are equal as exact rational numbers. Since ten belongs to A and not B, the equality cannot arise from reordering the parameters.

The equality can also be understood using adjacent pairs: f(n+1)/f(n)=(n/(n+1))^n. The products of these ratios agree for the starting sets {16,20,22,26,44,64,76,94,140} and {10,24,38,46,48,56,68,80,84}. The pairs have distinct even starts and hence no common endpoints. Crossing numerators and denominators gives precisely A and B. The proof checks the displayed factorial products directly in rational arithmetic; no approximation enters.

This refutes the full unrestricted uniqueness assertion, including the interpretation requiring all parameters on both sides to be distinct. It does not refute Theorem 4.6, whose parameters are primes. No minimality, composite-only strengthening or worldwide priority claim is asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/FactorialProductNonunique.claim`
- Truth anchor: `D5/S3/FiniteGroups/FactorialProductNonunique.result`
- Dependency: [D5/S3/FiniteGroups/TransversalProbabilityMonotone](TransversalProbabilityMonotone.md)
