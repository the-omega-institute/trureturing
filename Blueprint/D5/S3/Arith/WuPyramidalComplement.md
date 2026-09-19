# Wu's Pyramidal Complement Formula

## Abstract

Wu's formula enumerates every positive integer outside a k-gonal-pyramidal sequence for k at least nine.

**Definition 1.1 (The k-gonal-pyramidal sequence).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{P}\left(k, m\right) = \left(k - 2\right) \cdot \operatorname{choose}\left(m + 1, 3\right) + \operatorname{choose}\left(m + 1, 2\right)$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.pyramidal` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

The binomial expression is integral at every natural index and equals m(m+1)(m(k-2)-(k-5))/6. The value at index zero is included only as a counting extension; the source sequence uses positive indices.

**Definition 1.2 (The positive complement).**

$$\forall k \in \mathbb{N},\; \forall x \in \mathbb{N},\; \operatorname{C}\left(k, x\right) \Leftrightarrow \left(0 < x \land \left(\forall m \in \mathbb{N},\; 0 < m \Rightarrow \operatorname{P}\left(k, m\right) \ne x\right)\right)$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.complement` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

C(k,x) holds exactly when x is positive and is not P(k,m) for any positive m. This definition is independent of the proposed enumeration formula.

**Definition 1.3 (The upper threshold).**

$$\forall k \in \mathbb{N},\; \forall h \in \mathbb{N},\; \operatorname{U}\left(k, h\right) = \left(k - 2\right) \cdot h^{3} + 3 \cdot \left(k - 1\right) \cdot h^{2} + \left(2 \cdot k - 1\right) \cdot h + 6$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.upperThreshold` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

U(k,h) is the inclusive upper-branch threshold in Equation (6).

**Definition 1.4 (The lower threshold).**

$$\forall k \in \mathbb{N},\; \forall h \in \mathbb{N},\; \operatorname{L}\left(k, h\right) = h \cdot \left(h - 1\right) \cdot \left(h \cdot \left(k - 2\right) + k + 1\right)$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.lowerThreshold` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

L(k,h) is the inclusive lower-branch threshold in Equation (6).

**Definition 1.5 (The ordered source branches).**

$$\operatorname{B}\left(u, l, c, k, n, h\right) = \operatorname{if}\left(\operatorname{U}\left(k, h\right) \le 6 \cdot n, u, \operatorname{if}\left(6 \cdot n \le \operatorname{L}\left(k, h\right), l, c\right)\right)$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.branchSelector` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

The upper test is evaluated first. If it fails, the lower test is evaluated; otherwise the middle code is returned.

**Definition 1.6 (The three branch adjustments).**

$$\operatorname{E}\left(b, n, h\right) = \operatorname{match}\left(b, n + h + 1, n + h - 1, n + h\right)$$

*Formalization.* `D5/S3/Arith/WuPyramidalComplement.evaluateBranch` (`✓ std3`).

*Citation.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

The codes some(true), some(false), and none evaluate respectively to n+h+1, n+h-1 using natural subtraction, and n+h.

**Theorem 1.7 (Conjecture 1).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; 9 \le k \Rightarrow \left(1 \le n \Rightarrow \operatorname{nth}\left(\operatorname{C}\left(k\right), n - 1\right) = \operatorname{E}\left(\operatorname{B}\left(\operatorname{some}\left(true\right), \operatorname{some}\left(false\right), none, k, n, \left\lfloor\frac{6 \cdot n}{k - 2}^{\frac{1}{3}}\right\rfloor\right), n, \left\lfloor\frac{6 \cdot n}{k - 2}^{\frac{1}{3}}\right\rfloor\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/WuPyramidalComplement.wu_conjecture_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu (2025). *Algorithms for Complementary Sequences*. DOI: [10.5281/zenodo.17535229](https://doi.org/10.5281/zenodo.17535229). URL: <https://math.colgate.edu/~integers/z95/z95.pdf>.

*Commentary.*

Let h be the floor of the real cube root of 6n/(k-2). For every k at least nine and every positive n, the (n-1)-st zero-based member of the positive complement is the value selected by the exact inclusive thresholds. The proof identifies this real floor with the corresponding integer cube-root index, locates the answer strictly between consecutive pyramidal values in all three branches, and counts exactly n-1 complement values below it.

## References

- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.branchSelector`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.complement`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.evaluateBranch`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.lowerThreshold`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.pyramidal`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.upperThreshold`
- Truth anchor: `D5/S3/Arith/WuPyramidalComplement.wu_conjecture_one`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapeRecord](../ConceptDynamics/InformationEscape/EscapeRecord.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](../ConceptDynamics/InformationEscape/RegistrationTemplates.md)
