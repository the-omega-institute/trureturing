# Nonuniqueness of the multilayer percolation determinant zero

## Abstract

Three layers with degree identically 65 give three distinct interior zeros of the multilayer percolation determinant, refuting its conjectured uniqueness.

**Definition 1.1 (The multilayer matrix).**

$$\forall (M: \mathbb{N}), (\forall (C: \mathbb{R}), (\forall (q: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(M\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{multilayerMatrix}\left(M, C, q, i, j\right) = \operatorname{if} (i = j) \operatorname{then} (1 - C \cdot (\operatorname{castReal}\left(\operatorname{choose}\left(M, (\operatorname{val}\left(j\right) + 1)\right)\right) - \operatorname{castReal}\left(\operatorname{choose}\left((M - (\operatorname{val}\left(j\right) + 1)), (\operatorname{val}\left(j\right) + 1)\right)\right)) \cdot (q)^{((\operatorname{val}\left(j\right) + 1))} \cdot (1 - q)^{(M - (\operatorname{val}\left(j\right) + 1))}) \operatorname{else} (-C \cdot (\operatorname{castReal}\left(\operatorname{choose}\left(M, (\operatorname{val}\left(j\right) + 1)\right)\right) - \operatorname{castReal}\left(\operatorname{choose}\left((M - (\operatorname{val}\left(i\right) + 1)), (\operatorname{val}\left(j\right) + 1)\right)\right)) \cdot (q)^{((\operatorname{val}\left(j\right) + 1))} \cdot (1 - q)^{(M - (\operatorname{val}\left(j\right) + 1))}))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.multilayerMatrix` (`✓ std3`).

*Citation.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

Equation (3) of Guha, Towsley, Nain, Capar, Swami and Basu defines the matrix for M layers, excess-degree ratio C and occupation probability q. Here i and j range over Fin M, whose values are 0 through M − 1; the source indices are val(i) + 1 and val(j) + 1. The function choose is the natural binomial coefficient, zero when its lower argument exceeds its upper argument. Subtraction inside choose and in the exponents is natural subtraction; the binomial coefficients are cast to real numbers before their difference is taken. The definition allows every natural M and real C, q.

**Definition 1.2 (Finitely supported degree distributions).**

$$\forall (p: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{R}\right)), ((\operatorname{IsDegreeDistribution}\left(p\right)) \Leftrightarrow ((\forall (k: \mathbb{N}), (0 \le p\left(k\right))) \land (\sum_{(k: \mathbb{N}) \in \operatorname{support}\left(p\right)} (p\left(k\right)) = 1)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.IsDegreeDistribution` (`✓ std3`).

*Citation.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

The degree probabilities p(k) are nonnegative and sum to one. Finsupp(N,R) denotes the finitely supported real functions on the nonnegative integers; support(p) is the finite set where p is nonzero. Every displayed sum over support(p) is a finite sum. This is the finitely supported case of the source's degree distribution p_k.

**Definition 1.3 (The mean degree).**

$$\forall (p: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{R}\right)), (\operatorname{meanDegree}\left(p\right) = \sum_{(k: \mathbb{N}) \in \operatorname{support}\left(p\right)} (\operatorname{castReal}\left(k\right) \cdot p\left(k\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.meanDegree` (`✓ std3`).

*Citation.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

The source's mean degree is z = sum_k k p_k. The map castReal sends a natural number to the corresponding real number. The definition applies to every finitely supported real function p; positivity is imposed in the conjecture.

**Definition 1.4 (The excess-degree ratio).**

$$\forall (p: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{R}\right)), (\operatorname{excessRatio}\left(p\right) = \frac{\sum_{(k: \mathbb{N}) \in \operatorname{support}\left(p\right)} ((\operatorname{castReal}\left(k\right) - 1) \cdot \operatorname{castReal}\left(k\right) \cdot p\left(k\right))}{\operatorname{meanDegree}\left(p\right)})$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.excessRatio` (`✓ std3`).

*Citation.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

The source sets C = sum_k (k − 1) k p_k / z. In this formula k is cast to R before subtracting one. The quotient uses real division, including its value at a zero denominator; the conjecture assumes that the mean degree is positive.

**Definition 1.5 (The determinant uniqueness conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (M: \mathbb{N}), ((1 \le M) \Rightarrow (\forall (p: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{R}\right)), ((\operatorname{IsDegreeDistribution}\left(p\right)) \Rightarrow ((0 < \operatorname{meanDegree}\left(p\right)) \Rightarrow ((1 < \operatorname{excessRatio}\left(p\right)) \Rightarrow (\exists! (q: \mathbb{R}), (((0 \le q) \land (q \le 1)) \land (\operatorname{det}\left((\operatorname{multilayerMatrix}\left(M, \operatorname{excessRatio}\left(p\right), q\right))\right) = 0)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.claim` (`✓ std3`).

*Citation.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

For every M at least one and every finitely supported degree distribution with positive mean and excess-degree ratio greater than one, the determinant is asserted to have exactly one zero in the closed interval [0,1]. This is the finitely supported form of the conjecture following equation (5), repeated after Appendix C. A counterexample in this class also contradicts the assertion for arbitrary degree distributions.

**Theorem 1.6 (Three distinct zeros for three layers).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/guha-et-al-2016-multilayer-determinant-root-nonuniqueness` (refuted) by `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"guha-et-al-2016-multilayer-determinant-root-nonuniqueness","declaration_gid":"D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu (2016). *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*. DOI: [10.1103/PhysRevE.93.062310](https://doi.org/10.1103/PhysRevE.93.062310). URL: <https://arxiv.org/abs/1402.7057v4>.

*Commentary.*

Take M = 3 and the point mass at degree 65: p(65) = 1 and p(k) = 0 for k different from 65. It is a finitely supported degree distribution with z = 65 and C = 64. With u = q(1 − q)^2, v = q^2(1 − q) and w = q^3, the matrix is [[1 − 64u, −128v, −64w], [−128u, 1 − 192v, −64w], [−192u, −192v, 1 − 64w]].

Its determinant has the exact values 1, −36, 281 and −63 at q = 0, 1/4, 1/2 and 1, respectively. Each entry is a polynomial in q, so the determinant is continuous. The intermediate value theorem gives a zero in each of (0,1/4), (1/4,1/2) and (1/2,1). The endpoint values are nonzero, so these zeros lie in the open intervals and are distinct. Thus uniqueness in [0,1] fails even though z > 0 and C > 1.

This construction uses the source's matrix and degree data. It refutes the uniqueness conjecture; the source's separate proposition identifying the percolation threshold with the smallest zero is a different statement.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.IsDegreeDistribution`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.excessRatio`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.meanDegree`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.multilayerMatrix`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result`
