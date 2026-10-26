# Exact finite-support normalization and binomial counting

## Abstract

Prescribed-support fibers give exact size-independent coefficients for the literal source count. Zero is fixed separately, all ties remain, and every valid original rank is included.

**Definition 1.1 (Positive support of the two coordinate arrays).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{CoordinateDataCarrier}\left(M, i\right),\; \operatorname{coordinateDataSupport}\left(d\right) = \operatorname{erase}\left(\operatorname{union}\left(\operatorname{image}\left(\operatorname{fst}\left(d\right)\right), \operatorname{image}\left(\operatorname{fst}\left(\operatorname{snd}\left(d\right)\right)\right)\right), \operatorname{zero}\left(\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.coordinateDataSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Both images range over Fin i. Remove zero from their union; no strictness, positivity or distinctness is assumed for either coordinate array. Its cardinality is bounded by 2i.

**Definition 1.2 (The admissible full-support coefficient).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \operatorname{patternCoefficient}\left(i, k\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{coordinateDataFamily}\left(k, i\right), \operatorname{supportEquals}\left(\operatorname{erase}\left(\operatorname{univ}\left(\operatorname{Fin}\left(k + \operatorname{one}\left(\right)\right)\right), \operatorname{zero}\left(\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.patternCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

At ordinary size k count exactly those admissible data using every positive coordinate from 1 through k. Ordered exceptional bits remain part of the datum, rather than being assumed unique. The coefficient is a natural number independent of n.

**Theorem 1.3 (Every prescribed support has the same coefficient).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(M + \operatorname{one}\left(\right)\right)\right),\; (S \subseteq \operatorname{erase}\left(\operatorname{univ}\left(\operatorname{Fin}\left(M + \operatorname{one}\left(\right)\right)\right), \operatorname{zero}\left(\right)\right)) \Rightarrow (\operatorname{card}\left(\operatorname{filter}\left(\operatorname{coordinateDataFamily}\left(M, i\right), \operatorname{supportEquals}\left(S\right)\right)\right) = \operatorname{patternCoefficient}\left(i, \operatorname{card}\left(S\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.coordinateDataSupport_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Mathlib orderIsoOfFin enumerates insert 0 S increasingly and fixes zero. Apply that embedding pointwise to positions and cutoffs, retaining the exceptional bits. Extending the finite embedding to a strictly increasing natural map allows direct use of coordinate_rules_refinement_iff and coordinate_rules_bounded_iff. The inverse uses the same order isomorphism on the actual two coordinate images. These two maps give a bijection of the prescribed support fibers, including S empty.

**Theorem 1.4 (Literal count as a finite binomial sum).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\operatorname{count}\left(n, n + \operatorname{one}\left(\right) - i\right) = \operatorname{sum}\left(\operatorname{range}\left(\operatorname{two}\left(\right) \cdot i + \operatorname{one}\left(\right)\right), \operatorname{lambda}\left(k, \operatorname{patternCoefficient}\left(i, k\right) \cdot \operatorname{choose}\left(n + \operatorname{one}\left(\right) - i, k\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.count_eq_binomial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Group the actual coordinate family first by support cardinality and then by its prescribed support. The support has at most 2i values. The upstream powerset-cardinality theorem counts the k-subsets of the M positive ordinary ranks by choose(M,k). The prescribed-support bijection supplies the common fiber cardinality. Finally count_eq_coordinateDataFamily_card returns this identity to the literal repeated-point source count for every i<=n+1. No eventual threshold, genericity premise or negative rank occurs. The factorial value of the top coefficient is a separate obligation.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.coordinateDataSupport`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.coordinateDataSupport_fiber_card`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.count_eq_binomial_sum`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization.patternCoefficient`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction](MazorchukXuReconstruction.md)
