# Lyndon scans for the Christoffel factor count

## Abstract

The scan gives the finite-index Lyndon factor set and count used in the Christoffel refutation.

**Theorem 1.1 (The original occurrence image).**

$$\forall \sigma: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(\sigma\right), \operatorname{factorScan}\left(\operatorname{List.map}\left(w, \operatorname{List.finRange}\left(n\right)\right)\right) = \operatorname{Finset.image}\left((p: \mathbb{N}\times\mathbb{N} \mapsto \operatorname{factor}\left(w, p.1, p.2\right)), \operatorname{lyndonOccurrences}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorChristoffelScan.factorScan_eq_occurrence_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every sigma,n and w : Fin n -> Fin sigma, the scan set equals the image sending each valid pair (i,l) in lyndonOccurrences w to factor w i l. The proof reconstructs a valid slice from an arbitrary contiguous occurrence; its nonemptiness gives l>=1 and its enclosing word gives i+l<=n.

**Theorem 1.2 (The original distinct count).**

$$\forall \sigma: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(\sigma\right), \operatorname{distinctLyndon}\left(w\right) = \operatorname{Finset.card}\left(\operatorname{factorScan}\left(\operatorname{List.map}\left(w, \operatorname{List.finRange}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorChristoffelScan.distinctLyndon_eq_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

The original distinctLyndon count is exactly the cardinality of the scan set. This is an equality of the actual factor objects, with no count recurrence or occurrence-count replacement.

The equalities relate the scan to the factor objects in the Christoffel refutation. The scan applies to finite words over Fin sigma, including the empty word. Its cardinality counts equal strings once.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorChristoffelScan.distinctLyndon_eq_scan`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorChristoffelScan.factorScan_eq_occurrence_image`
- Dependency: [D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation](LyndonFactorChristoffelMinimumRefutation.md)
- Dependency: [D5/S1/Words/Complexity/LyndonFactorTransport](LyndonFactorTransport.md)
