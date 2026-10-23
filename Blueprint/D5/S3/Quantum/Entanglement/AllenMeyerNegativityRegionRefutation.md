# The Allen–Meyer family omits achievable three-qutrit negativities

## Abstract

A normalized asymmetric three-qutrit vector has a negativity triple outside the family in equation (13) of Allen and Meyer.

The three factors are A, B and C, each indexed by Fin(3) = {0, 1, 2}. A vector is a complex-valued function on Fin(3) × (Fin(3) × Fin(3)); the triple (i, j, k) means (i, (j, k)). The ket |ijk⟩ is the coordinate vector with value one there and zero elsewhere. A bar denotes complex conjugation, and real coefficients in vectors are included in the complex numbers. The definitions below apply to arbitrary vectors; unit normalization is imposed in claim.

**Definition 1.1 (Tracing out C).**

$$\forall \left(psi: \left(\operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \to \mathbb{C}\right)\right), \left(\forall \left(p: \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \left(\forall \left(q: \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \left(\operatorname{pairAB}\left(psi, p, q\right) = \operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(\left(\left(\left(r, c\right): \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(3\right)\right) \mapsto psi\left(\left(r_{1}, r_{2}, c\right)\right)\right)\right)\right)\left(p, q\right) = \sum_{\left(c: \operatorname{Fin}\left(3\right)\right)} \left(psi\left(\left(p_{1}, p_{2}, c\right)\right) \cdot \overline{psi\left(\left(q_{1}, q_{2}, c\right)\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.pairAB` (`✓ std3`).

*Citation.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

The reduced matrix on A and B is partialTraceRight of rankOneDensity of the amplitude ((i, j), k) ↦ psi(i, j, k). The rank-one density has entries v(p) times the complex conjugate of v(q), and partialTraceRight sums its entries at (p, k), (q, k) over k. For p = (i, j) and q = (i', j'), its entry sums over the common C index. This is the A|B reduced state used in the negativity region following equation (13).

**Definition 1.2 (Tracing out B).**

$$\forall \left(psi: \left(\operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \to \mathbb{C}\right)\right), \left(\forall \left(p: \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \left(\forall \left(q: \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \left(\operatorname{pairAC}\left(psi, p, q\right) = \operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(\left(\left(\left(r, b\right): \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(3\right)\right) \mapsto psi\left(\left(r_{1}, b, r_{2}\right)\right)\right)\right)\right)\left(p, q\right) = \sum_{\left(b: \operatorname{Fin}\left(3\right)\right)} \left(psi\left(\left(p_{1}, b, p_{2}\right)\right) \cdot \overline{psi\left(\left(q_{1}, b, q_{2}\right)\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.pairAC` (`✓ std3`).

*Citation.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

The reduced matrix on A and C is partialTraceRight of rankOneDensity of the amplitude ((i, k), j) ↦ psi(i, j, k). Its rank-one entries are traced over the common final index j. For p = (i, k) and q = (i', k'), its entry sums over the common B index. This is the A|C reduced state used in the same region.

**Definition 1.3 (The three partial-transpose negativities).**

$$\forall \left(psi: \left(\operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \to \mathbb{C}\right)\right), \left(\left(\operatorname{negativityTriple}\left(psi\right) = \left(\frac{\left\lVert \left(\operatorname{pairAB}\left(psi\right)\right)^{\Gamma} \right\rVert_{1} - 1}{2}, \frac{\left\lVert \left(\operatorname{pairAC}\left(psi\right)\right)^{\Gamma} \right\rVert_{1} - 1}{2}, \frac{\left\lVert \left(\operatorname{rankOneDensity}\left(psi\right)\right)^{\Gamma} \right\rVert_{1} - 1}{2}\right)\right) \land \left(\forall \left(p: \operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right)\right), \left(\forall \left(q: \operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right)\right), \left(\operatorname{rankOneDensity}\left(psi, p, q\right) = psi\left(p\right) \cdot \overline{psi\left(q\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.negativityTriple` (`✓ std3`).

*Citation.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

The coordinates are the negativities of the AB and AC reduced matrices and of the pure state rankOneDensity(psi) = |psi⟩⟨psi| across A|BC, in that order. Its entry at p, q is psi(p) times the complex conjugate of psi(q). The notation Γ transposes the second factor: for row (i, j) and column (k, l), the transposed entry is the original entry at row (i, l) and column (k, j). The subscript-one norm is the trace norm. Each coordinate is (‖rho^Γ‖₁ − 1)/2. Allen and Meyer use twice this value and transpose A; transposing the other factor gives the same trace norm. The common factor one half does not change equality of triples.

**Definition 1.4 (Equation (13) for three qutrits).**

$$\forall \left(a: \mathbb{R}\right), \left(\forall \left(b: \mathbb{R}\right), \left(\forall \left(c: \mathbb{R}\right), \left(\forall \left(d: \mathbb{R}\right), \left(\operatorname{familyState}\left(a, b, c, d\right) = d \cdot |0\,0\,0\rangle + \sum_{j \in \left\{1, 2\right\}} \left(a \cdot |j\,0\,j\rangle + b \cdot |j\,j\,0\rangle + c \cdot |j\,j\,j\rangle\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.familyState` (`✓ std3`).

*Citation.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

The same coefficients a, b and c occur at both nonzero levels j = 1 and j = 2. The seven coordinate vectors in this sum are distinct. Thus its squared norm is d² + 2(a² + b² + c²), without any restriction on the real parameters.

**Definition 1.5 (The conjectured entire negativity region).**

$$\left(\operatorname{claim}: Prop\right) \Leftrightarrow \left(\forall \left(psi: \left(\operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right) \to \mathbb{C}\right)\right), \left(\left(\sum_{\left(i: \operatorname{Fin}\left(3\right) \times \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right)\right)} \left(\left|psi\left(i\right)\right|^{2}\right) = 1\right) \Rightarrow \left(\exists \left(a: \mathbb{R}\right), \left(\exists \left(b: \mathbb{R}\right), \left(\exists \left(c: \mathbb{R}\right), \left(\exists \left(d: \mathbb{R}\right), \left(\left(0 \le a\right) \land \left(\left(0 \le b\right) \land \left(\left(0 \le c\right) \land \left(\left(0 \le d\right) \land \left(\left(d^{2} + 2 \cdot \left(a^{2} + b^{2} + c^{2}\right) = 1\right) \land \left(\operatorname{negativityTriple}\left(\operatorname{familyState}\left(a, b, c, d\right)\right) = \operatorname{negativityTriple}\left(psi\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim` (`✓ std3`).

*Citation.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

For every unit three-qutrit vector, some member of equation (13) with nonnegative real coefficients and unit norm has exactly the same negativity triple. This is the conjecture immediately after equation (13), restricted to dimension three. The paper orders the pair coordinates as AC, AB and uses squared negativities; a fixed coordinate swap and squaring nonnegative negativities do not affect equality of triples.

**Theorem 1.6 (An asymmetric vector lies outside the family).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/allen-meyer-2017-negativity-region-refutation` (refuted) by `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"allen-meyer-2017-negativity-region-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grant W. Allen; David A. Meyer (2017). *Polynomial Monogamy Relations for Entanglement Negativity*. DOI: [10.1103/PhysRevLett.118.080402](https://doi.org/10.1103/PhysRevLett.118.080402). URL: <https://arxiv.org/abs/1502.04807v2>.

*Commentary.*

Write x, y and z for the paper's negativities N = ‖rho^Γ‖₁ − 1 of AB, AC and A|BC, respectively, so these are twice the coordinates of negativityTriple. For a normalized family state with nonnegative coefficients, put r = √(a² + b² + c²), u = b² + c² and delta = z − y. Its Schmidt coefficients across A|BC are d, r, r, giving z = 4dr + 2r². A difference of positive semidefinite matrices for the AC partial transpose gives y ≤ 2a² + 4ad. When r is positive this implies delta ≥ 2(1 + d/r)u.

If z ≥ 14/11 and delta ≤ 2/209, normalization and the Schmidt formula imply r > 0, 1/7 ≤ d/r ≤ 3, u ≤ 1/209 and a² ≥ 18r²/19, in particular a > 0. A Gram decomposition of the AB partial transpose as a difference of positive semidefinite matrices gives x ≤ 2b² + 4d²u/a² ≤ 2u(1 + 2d²/a²). Combining these estimates yields the separator x ≤ 5(z − y) for every family state with z ≥ 14/11 and z − y ≤ 2/209.

Now take the normalized vector (5|000⟩ + 3|101⟩ + |202⟩ + t|110⟩ + 5t|220⟩)/√(35 + 26t²) at t = 1/100. Its squared normalization factor is 175013/5000. Unitary trace certificates give lower bounds for x and y, and its three Schmidt coefficients give lower and upper bounds for z. Rational bounds on the square roots then show z ≥ 14/11, z − y ≤ 2/209 and x > 5(z − y). A family state with this triple would satisfy both opposing inequalities. Therefore this vector's negativity triple is absent from the family.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.familyState`
- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.negativityTriple`
- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.pairAB`
- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.pairAC`
- Truth anchor: `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/QuantumBounds/NegativityReductionInclusionRefutation](../../QuantumBounds/NegativityReductionInclusionRefutation.md)
