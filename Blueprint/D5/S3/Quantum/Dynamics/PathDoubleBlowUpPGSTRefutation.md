# Pretty good state transfer at vertex 4 of the double blow-up of P_11

## Abstract

The double blow-up of P_11 admits pretty good state transfer between the two copies of source vertex 4, refuting Conjecture 1 of Bhattacharjya, Monterde and Pal.

**Definition 1.1 (Path adjacency).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{pathAdj}\left(n\right)\left(i, j\right) = \text{if} (\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right)) \text{then} (1:\mathbb{C}) \text{else} (0:\mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.pathAdj` (`✓ std3`).

*Citation.* Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal (2024). *Quantum walks on blow-up graphs*. DOI: [10.1088/1751-8121/ad6653](https://doi.org/10.1088/1751-8121/ad6653). URL: <https://arxiv.org/abs/2308.13887v2>.

*Commentary.*

Source vertices are 1 through n. A vertex j in Fin(n) represents source vertex val(j) + 1, so adjacency is the disjunction val(i) + 1 = val(j) or val(j) + 1 = val(i). Matrix entries are complex zero and one.

**Definition 1.2 (The double blow-up).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(n\right),\; \forall q \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(n\right),\; \operatorname{doubleBlowUp}\left(n\right)\left(p, q\right) = \operatorname{pathAdj}\left(n\right)\left(p.2, q.2\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.doubleBlowUp` (`✓ std3`).

*Citation.* Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal (2024). *Quantum walks on blow-up graphs*. DOI: [10.1088/1751-8121/ad6653](https://doi.org/10.1088/1751-8121/ad6653). URL: <https://arxiv.org/abs/2308.13887v2>.

*Commentary.*

Section 2, page 2 states: The blow-up of G, denoted by ⊎ⁿG, is the graph with vertex set ℤ_n × V, and two vertices (l, u) and (m, v) are adjacent in ⊎ⁿG if and only if the vertices u and v are adjacent in G. Here the number of copies is two, with carrier Fin(2) times Fin(n). The copy coordinates do not affect adjacency.

**Definition 1.3 (Pretty good state transfer).**

$$\forall I \in Type,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \forall a \in I,\; \forall b \in I,\; \operatorname{PGST}\left(A, a, b\right) \Leftrightarrow (\exists s \in \mathbb{N} \to \mathbb{R},\; \operatorname{Tendsto}\left((k:\mathbb{N} \mapsto \Vert \operatorname{ProjectionProbabilityFlow}.\operatorname{hamiltonianPropagator}\left(A, -s\left(k\right)\right)\left(a, b\right)\Vert), atTop, \operatorname{nhds}\left(1\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.PGST` (`✓ std3`).

*Citation.* Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal (2024). *Quantum walks on blow-up graphs*. DOI: [10.1088/1751-8121/ad6653](https://doi.org/10.1088/1751-8121/ad6653). URL: <https://arxiv.org/abs/2308.13887v2>.

*Commentary.*

Section 1, pages 1-2 states: A graph G exhibits PGST between u and v if there is a sequence τ_k ∈ ℝ such that lim_{k→∞} |U(τ_k)_{u,v}| = 1, i.e., |U(t)_{u,v}|² can be made arbitrarily close to one through appropriate choices of t. The matrix U(t) is exp(itA), represented by hamiltonianPropagator(A, -t). The sequence is indexed by the naturals and convergence is Tendsto atTop to nhds(1). Complex modulus is the Lean norm.

**Definition 1.4 (Conjecture 1).**

$$claim \Leftrightarrow (\forall t \in \mathbb{N},\; \forall r \in \mathbb{N},\; (2 \le t) \Rightarrow ((\operatorname{Nat}.\operatorname{Prime}\left(r\right)) \Rightarrow ((\operatorname{Odd}\left(r\right)) \Rightarrow (\forall u \in \operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(2^{t} \cdot r, 1\right)\right),\; (2^{\operatorname{Nat}.\operatorname{sub}\left(t, 1\right)} \mid \operatorname{val}\left(u\right) + 1) \Rightarrow (\neg \operatorname{PGST}\left(\operatorname{doubleBlowUp}\left(\operatorname{Nat}.\operatorname{sub}\left(2^{t} \cdot r, 1\right)\right), (0,u), (1,u)\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.claim` (`✓ std3`).

*Citation.* Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal (2024). *Quantum walks on blow-up graphs*. DOI: [10.1088/1751-8121/ad6653](https://doi.org/10.1088/1751-8121/ad6653). URL: <https://arxiv.org/abs/2308.13887v2>.

*Commentary.*

Section 8, page 8, Conjecture 1 states: Let n = 2^t r − 1, where t ≥ 2 and r is an odd prime number. If u is a multiple of 2^{t−1}, then PGST does not occur between (0, u) and (1, u) in the double blow-up of P_n. The letters t and r retain their source meaning. The source vertex u is represented by u in Fin(2^t*r - 1), whose one-based label is val(u) + 1. Both subtractions in the displayed formula are Nat.sub, the truncated natural-number subtraction.

**Theorem 1.5 (Refutation by source vertex 4 of P_11).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal (2024). *Quantum walks on blow-up graphs*. DOI: [10.1088/1751-8121/ad6653](https://doi.org/10.1088/1751-8121/ad6653). URL: <https://arxiv.org/abs/2308.13887v2>.

*Commentary.*

Take t = 2, r = 3 and u = 3 in Fin(11), representing source vertex 4. At that vertex the diagonal amplitude is one quarter of the sum of the four cosines with positive frequencies (sqrt(6)+sqrt(2))/2, sqrt(3), 1 and (sqrt(6)-sqrt(2))/2. Each pair of opposite eigenvalues carries weight one eighth on each eigenvalue. Biquadratic independence and the finite-torus character criterion give times pi/2 + pi*m(k) along which all four cosines tend to minus one. The general twin-amplitude identity then gives modulus tending to one. The source's relation theta_5 - theta_9 + theta_11 = 0 uses theta_9 = -sqrt(2); this eigenvalue has zero weight at source vertex 4, since sin(3*pi) = 0, and therefore does not obstruct transfer there.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.PGST`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.doubleBlowUp`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.pathAdj`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.result`
- Dependency: [D5/S3/Fourier/BiquadraticKroneckerTimes](../../Fourier/BiquadraticKroneckerTimes.md)
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace](../../QuantumBounds/ReferenceFrame/TopEigenspace.md)
