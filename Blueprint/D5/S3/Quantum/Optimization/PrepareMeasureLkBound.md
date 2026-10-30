# A strict prepare-and-measure bound

## Abstract

Averaging signs improves the prepare-and-measure bound uniformly for every k at least three.

**Definition 1.1 (The two real signs).**

$$\forall (s: \operatorname{Fin}\left(2\right)), \operatorname{signValue}\left(s\right) = \operatorname{ite}\left(s = (0: \operatorname{Fin}\left(2\right)), -(1: \mathbb{R}), (1: \mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.signValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

The two elements of Fin 2 encode the signs: zero represents minus one, and one represents plus one.

**Definition 1.2 (The entrywise Manhattan norm).**

$$\forall (\alpha: Type), \forall (\beta: Type), [\operatorname{Fintype}\left(\alpha\right)] [\operatorname{Fintype}\left(\beta\right)] \forall (A: \operatorname{Matrix}\left(\alpha, \beta, \mathbb{R}\right)), \operatorname{manhattan}\left(A\right) = \sum_{i: \alpha} (\sum_{j: \beta} (\left|A\left(i, j\right)\right|))$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.manhattan` (`✓ std3`).

*Citation.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

For arbitrary finite row and column types, the Manhattan norm is the sum of the absolute values of all real entries. An empty index type gives zero.

**Remark 1.3 (Matrices with standard basis rows).**

$$
\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \mathcal{W}_{n,k} = \{W: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(k\right), \mathbb{R}\right) \mid \exists (f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right)), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(k\right)), W\left(i, j\right) = \operatorname{ite}\left(f\left(i\right) = j, (1: \mathbb{R}), (0: \mathbb{R})\right)\}
$$

*Citation.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

Each function f from Fin n to Fin k encodes exactly one matrix whose ith row is the standard basis vector indexed by f(i). These are precisely the matrices in the source's set.

**Definition 1.4 (Grouped matrix entries).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (k: \mathbb{N}), \forall (f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right)), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \forall (j: \operatorname{Fin}\left(k\right)), \forall (q: \operatorname{Fin}\left(m\right)), \operatorname{fiberSum}\left(f, M, j, q\right) = \sum_{i: \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(f\left(i\right) = j, M\left(i, q\right), (0: \mathbb{R})\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.fiberSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

The fiber sum is the (j,q) entry of the transpose product WᵀM: it sums column q over the rows assigned to j.

**Definition 1.5 (The k-group matrix functional).**

$$\forall (k: \mathbb{N}), \forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \operatorname{Lk}\left(k, M\right) = \operatorname{ite}\left(0 < k, \max_{f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right)} (\operatorname{manhattan}\left(((j: \operatorname{Fin}\left(k\right)) (q: \operatorname{Fin}\left(m\right))\mapsto \operatorname{fiberSum}\left(f, M, j, q\right))\right)), (0: \mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.Lk` (`✓ std3`).

*Citation.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

For positive k, maximize the Manhattan norm of WᵀM over every assignment of rows to k groups. This is the source's L_k. At k equal to zero the definition is extended by zero. The positive branch always has an assignment, even when there are no rows.

**Definition 1.6 (The sign-vector matrix functional).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \operatorname{L}\left(M\right) = \max_{v: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)} (\sum_{j: \operatorname{Fin}\left(m\right)} (\left|\sum_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{signValue}\left(v\left(i\right)\right)) \cdot (M\left(i, j\right)))\right|))$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.L` (`✓ std3`).

*Citation.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

Choose an independent sign for each row, sum the signed rows, and take the vector's Manhattan norm. L is the maximum over all such choices.

**Definition 1.7 (The averaged absolute sign sum).**

$$\forall (k: \mathbb{N}), \operatorname{a}\left(k\right) = (\frac{1}{(2: \mathbb{R})^{k}}) \cdot (\sum_{\varepsilon: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(2\right)} (\left|\sum_{i: \operatorname{Fin}\left(k\right)} (\operatorname{signValue}\left(\varepsilon\left(i\right)\right))\right|))$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

The constant a_k averages the absolute sum of k independent uniform signs. The factor two to the power minus k divides by the number of sign vectors.

**Definition 1.8 (Uniform nontightness beyond two groups).**

$$\operatorname{claim} = (\forall (k: \mathbb{N}), (3 \le k) \Rightarrow (\exists (c: \mathbb{R}), (c < (k: \mathbb{R})) \land (\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \operatorname{Lk}\left(k, M\right) \le (c) \cdot (\operatorname{L}\left(M\right)))))$$

*Formalization.* `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.claim` (`✓ std3`).

*Citation.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

For each k at least three there is one real constant c strictly below k that bounds L_k by c times L for every real matrix and all natural row and column dimensions. This gives a uniform form of the source's conjecture that the factor k in Lemma III.4 is not tight for greater values than two.

**Theorem 1.9 (A uniform improvement of the factor k).**

$$\forall (k: \mathbb{N}), (3 \le k) \Rightarrow (\exists (c: \mathbb{R}), (c < (k: \mathbb{R})) \land (\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \operatorname{Lk}\left(k, M\right) \le (c) \cdot (\operatorname{L}\left(M\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/divianszky-et-al-2023-lk-bound-nontightness` (proved) by `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"divianszky-et-al-2023-lk-bound-nontightness","declaration_gid":"D5/S3/Quantum/Optimization/PrepareMeasureLkBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi (2023). *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*. DOI: [10.1038/s41598-023-39529-0](https://doi.org/10.1038/s41598-023-39529-0). URL: <https://arxiv.org/abs/2211.17185v2>.

*Commentary.*

For a real vector x with k coordinates, define the averaged norm:

$$
\forall (k: \mathbb{N}), \forall (x: \operatorname{Fin}\left(k\right) \to \mathbb{R}), \left(g_{k}\right)\left(x\right) = (\frac{1}{(2: \mathbb{R})^{k}}) \cdot (\sum_{\varepsilon: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(2\right)} (\left|\sum_{i: \operatorname{Fin}\left(k\right)} ((\operatorname{signValue}\left(\varepsilon\left(i\right)\right)) \cdot (x\left(i\right)))\right|))
$$

Changing coordinate signs leaves this average unchanged. Symmetry of the sign coordinates gives the lower bound for every positive k:

$$
\forall (k: \mathbb{N}), (0 < k) \Rightarrow (\forall (x: \operatorname{Fin}\left(k\right) \to \mathbb{R}), (\frac{\operatorname{a}\left(k\right)}{(k: \mathbb{R})}) \cdot (\sum_{i: \operatorname{Fin}\left(k\right)} (\left|x\left(i\right)\right|)) \le \left(g_{k}\right)\left(x\right))
$$

For every matrix W with standard basis rows, each sign combination of the rows of WᵀM is a sign combination of the rows of M. Averaging these combinations and summing the column bounds therefore gives:

$$
\forall (k: \mathbb{N}), (0 < k) \Rightarrow (\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), \forall (W: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(k\right), \mathbb{R}\right)), (W \in \mathcal{W}_{n,k}) \Rightarrow ((\frac{\operatorname{a}\left(k\right)}{(k: \mathbb{R})}) \cdot (\operatorname{manhattan}\left((W^{\mathrm{T}}) \cdot (M)\right)) \le \operatorname{L}\left(M\right)))
$$

The average at k equal to three is three halves. Adding a sign cannot decrease the average, by the triangle inequality. Consequently the choice of constant below is strictly smaller than k:

$$
\forall (k: \mathbb{N}), (3 \le k) \Rightarrow (\exists (c_{k}: \mathbb{R}), (c_{k} = \frac{(k: \mathbb{R})}{\operatorname{a}\left(k\right)}) \land ((\frac{(3: \mathbb{R})}{(2: \mathbb{R})} \le \operatorname{a}\left(k\right)) \land (c_{k} < (k: \mathbb{R}))))
$$

Maximizing the comparison over W proves the uniform inequality. The constant depends only on k, so the same bound includes empty matrix dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.L`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.Lk`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.a`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.claim`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.fiberSum`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.manhattan`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.result`
- Truth anchor: `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.signValue`
