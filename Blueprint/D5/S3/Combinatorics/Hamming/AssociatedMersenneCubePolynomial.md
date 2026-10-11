# Cube polynomials of associated Mersenne graphs

## Abstract

The cube polynomial of the associated Mersenne graphs is determined by a cleared-denominator generating function.

Wei and Yang, Associated Mersenne graphs, arXiv:2407.08237v1, Section 6, Question 6.3 (page 18), asks verbatim: “What is cube polynomial for Associated Mersenne graph \mathcal{M}_n?” The graph here uses labelled Boolean words and Hamming-distance-one adjacency.

**Definition 1.1 (The associated Mersenne graph).**

$$\forall n \in \mathrm{Nat},\; \forall u \in Subtype\left(fun (w: Fin\left(n\right) \to Bool) \mapsto Admissible\left(w\right)\right),\; \forall v \in Subtype\left(fun (w: Fin\left(n\right) \to Bool) \mapsto Admissible\left(w\right)\right),\; (SimpleGraph.Adj\left(amGraph\left(n\right), u, v\right)) \Leftrightarrow (hammingDist\left(Subtype.val\left(u\right), Subtype.val\left(v\right)\right) = 1)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amGraph` (`✓ std3`).

*Citation.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

For each natural number n, amGraph n is the simple graph whose vertices are the admissible Boolean functions on Fin n. Two vertices are adjacent exactly when their Hamming distance is one. The admissibility predicate is the circular run constraint from the source.

**Definition 1.2 (Induced cube count).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; cubeCount\left(n, k\right) = Nat.card\left(Subtype\left(fun (S: Finset\left(Subtype\left(fun (w: Fin\left(n\right) \to Bool) \mapsto Admissible\left(w\right)\right)\right)) \mapsto Nonempty\left(SimpleGraph.Iso\left(SimpleGraph.induce\left(amGraph\left(n\right), SetLike.coe\left(S\right)\right), hypercube\left(k\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubeCount` (`✓ std3`).

*Citation.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

For natural n and k, cubeCount n k is the cardinality of the finite type of finsets of admissible words whose induced graph is isomorphic to hypercube k.

**Definition 1.3 (Cube polynomial).**

$$\forall n \in \mathrm{Nat},\; cubePoly\left(n\right) = \sum (k: \mathrm{Nat}) \in Finset.range\left((n + 1)\right) , Polynomial.monomial\left(k, cubeCount\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubePoly` (`✓ std3`).

*Citation.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The cube polynomial of the associated Mersenne graph at n is the finite polynomial sum of cubeCount n k times X to the kth power, for k from zero through n.

**Definition 1.4 (The polynomial variable as a constant series).**

$$x = PowerSeries.C\left(Polynomial.X\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.x` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

x is the constant power series whose coefficient is the polynomial variable X over the integers.

**Definition 1.5 (The length variable).**

$$z = PowerSeries.X$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

z is the power-series variable over the integer polynomial ring.

**Definition 1.6 (The cleared denominator).**

$$amcDen = 1 - z - z^{2} - x \cdot z^{3} - x \cdot \left(1 + x\right) \cdot z^{5}$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amcDen` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The denominator is 1 minus z minus z squared minus x z cubed minus x(1+x) z to the fifth power.

**Definition 1.7 (The cleared numerator).**

$$amcNum = z + 2 \cdot z^{2} + 3 \cdot x \cdot z^{3} + 5 \cdot x \cdot \left(1 + x\right) \cdot z^{5}$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amcNum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The numerator is z plus 2z squared plus 3xz cubed plus 5x(1+x) z to the fifth power.

**Definition 1.8 (The cube-counting series).**

$$cubeSeries = PowerSeries.mk\left(fun (n: \mathrm{Nat}) \mapsto if n = 0 then 0 else Polynomial.map\left(Nat.castRingHom\left(\mathrm{Int}\right), cubePoly\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubeSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The coefficient at positive length n is cubePoly n mapped from natural coefficients to integer coefficients, and the constant coefficient is zero.

**Definition 1.9 (The cleared-denominator answer).**

$$cubeSeries \cdot \left(1 - z^{2}\right) \cdot amcDen = amcNum \cdot \left(1 - z^{2}\right) - 2 \cdot z^{2} \cdot amcDen$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The source's Question 6.3 is answered by the formal power-series identity AMC-1 in cleared-denominator form.

**Theorem 1.10 (The cube polynomial formula).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/wei-yang-2024-associated-mersenne-cube-polynomial` (proved) by `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wei-yang-2024-associated-mersenne-cube-polynomial","declaration_gid":"D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The endpoint-removal characterization, the marked double count, and the weighted block-series resolvent prove the claimed generating function for every natural length.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amGraph`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amcDen`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.amcNum`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.claim`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubeCount`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubePoly`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.cubeSeries`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.x`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.z`
- Dependency: [D5/S1/Words/AssociatedMersenne/TransferResolvent](../../../S1/Words/AssociatedMersenne/TransferResolvent.md)
- Dependency: [D5/S3/Combinatorics/Hamming/InducedSubcubes](InducedSubcubes.md)
