# A mixed middle state breaks the decomposition transport triangle inequality

## Abstract

Three block-supported mixed states have decomposition transport distances with a long side of square root three and a two-edge route of length at most square root two.

**Definition 1.1 (Pure-vector observable expectation).**

$$\forall d: \mathbb{N}, \forall H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \psi: \operatorname{Fin}\left(d\right) \to \mathbb{C}, \operatorname{expectation}\left(H, \psi\right) = \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\right), \operatorname{mulVec}\left(H, \psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.expectation` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

The vector ψ has complex coordinates indexed by Fin d. The expression is the real part of the conjugate-vector dot product with Hψ. For a unit ψ and Hermitian H, it is the usual expectation in |ψ⟩⟨ψ|. The definition also makes sense without either hypothesis. This is the expectation appearing in the pure-state reduction of equation (12).

**Definition 1.2 (The modified pure-state squared cost).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \psi: \operatorname{Fin}\left(d\right) \to \mathbb{C}, \forall \phi: \operatorname{Fin}\left(d\right) \to \mathbb{C}, \operatorname{pureCost}\left(H, \psi, \phi\right) = (\frac{1}{2}) \cdot (\sum_{n\in \operatorname{Fin}\left(N\right)} (\operatorname{expectation}\left(H\left(n\right), \psi\right) - \operatorname{expectation}\left(H\left(n\right), \phi\right))^{2})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.pureCost` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

For every finite family H, take half the sum of squared differences of the real observable expectations. On unit vectors and Hermitian observables this is the modified pure-state value in equation (12): pure marginals force the coupling |ψ⟩⟨ψ|ᵀ ⊗ |φ⟩⟨φ|. The transpose trace identity Tr(Hᵀϱᵀ) = Tr(Hϱ) preserves the observable expectations. Expanding each squared difference operator gives the sum of the two variances plus the squared difference of means. The factor 1/2 multiplies both parts. The two self-costs are the respective sums of variances, so subtracting their average cancels the variance terms. This correspondence to equation (12) is a mathematical explanation and is not formalized here. The definition is precisely the displayed expectation formula.

**Definition 1.3 (A common-weight pair of finite pure ensembles).**

$$\forall d: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Decomposition}\left(\rho, \sigma\right) = \{(K, p, \psi, \phi) : \Sigma (K: \mathbb{N}), (\operatorname{Fin}\left(K\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(K\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right)) \times (\operatorname{Fin}\left(K\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right)) \mid (\forall k: \operatorname{Fin}\left(K\right), 0 \le p\left(k\right)) \land ((\sum_{k\in \operatorname{Fin}\left(K\right)} p\left(k\right) = 1) \land ((\forall k: \operatorname{Fin}\left(K\right), \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(k\right)\right), \psi\left(k\right)\right) = 1) \land ((\forall k: \operatorname{Fin}\left(K\right), \operatorname{dotProduct}\left(\operatorname{star}\left(\phi\left(k\right)\right), \phi\left(k\right)\right) = 1) \land ((\sum_{k\in \operatorname{Fin}\left(K\right)} (\operatorname{ofReal}\left(p\left(k\right)\right)) \cdot (\operatorname{rankOneDensity}\left(\psi\left(k\right)\right)) = \rho) \land (\sum_{k\in \operatorname{Fin}\left(K\right)} (\operatorname{ofReal}\left(p\left(k\right)\right)) \cdot (\operatorname{rankOneDensity}\left(\phi\left(k\right)\right)) = \sigma)))))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.Decomposition` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Equations (18) and (19) use a common finite probability distribution. The structure stores a natural length K, nonnegative real weights p with total mass one, and two families of complex vectors ψ and φ indexed by Fin K. Every vector is unit, including those with zero weight. The two weighted sums of rankOneDensity are exactly ρ and σ. Here rankOneDensity is the existing unnormalized outer product v v*, and the unit identities make these particular outer products trace-one. The displayed dependent tuple represents the fields of this structure; no orthogonality, block support, fixed ensemble size, or relation between the paired vectors is assumed.

**Definition 1.4 (All admissible decomposition costs).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{costs}\left(H, \rho, \sigma\right) = \{c : \mathbb{R} \mid \exists q: \operatorname{Decomposition}\left(\rho, \sigma\right), c = \sum_{k\in \operatorname{Fin}\left(\operatorname{K}\left(q\right)\right)} (\operatorname{p}\left(q\right)\left(k\right)) \cdot (\operatorname{pureCost}\left(H, \operatorname{psi}\left(q\right)\left(k\right), \operatorname{phi}\left(q\right)\left(k\right)\right))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.costs` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

The set contains the weighted pureCost average for every Decomposition of the two supplied matrices. Its elements range over all finite ensemble lengths and every common probability distribution, as in equation (83). The notation p(q), ψ(q), φ(q), and K(q) selects the corresponding structure fields. The existential does not restrict to the concrete ensembles used below.

**Definition 1.5 (The squared decomposition quantity).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{decompSq}\left(H, \rho, \sigma\right) = \operatorname{sInf}\left(\operatorname{costs}\left(H, \rho, \sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.decompSq` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Equation (83) is expressed as the real infimum of the whole admissible finite cost set. Real sInf is total, including its zero convention for an empty set or a set unbounded below; the counterexample uses nonempty sets bounded below by zero. Every square in pureCost is nonnegative, and every admissible weight is nonnegative.

For positive dimension, density marginals and Hermitian observables, the following mathematical explanation identifies this finite infimum with the source minimum; it is not formalized here. Pure-state projectors form a compact space. The pureCost depends only on the projectors P and Q, and the map (P,Q) ↦ (P,Q,pureCost(P,Q)) is continuous into the finite-dimensional real space of two Hermitian matrices and a cost coordinate. Its convex hull is compact. The slice fixing the two density marginals is nonempty, since spectral decompositions with product weights give a finite common-weight ensemble. The cost coordinate attains its minimum on this compact slice. Carathéodory's theorem gives a finite representation of a minimizer, so the minimum is a finite-decomposition cost and equals sInf. A countable decomposition has its marginal-and-cost barycenter in the same closed convex hull: the image is compact and bounded, and partial probability sums completed by their remaining mass converge to that barycenter. Thus countable decompositions cannot lower the optimum. Rank-one projectors admit unit-vector representatives, giving the vector fields in Decomposition. This compactness, attainment, finite-representation and countable-extension correspondence is mathematical explanation, not a formalized theorem.

**Definition 1.6 (The decomposition distance).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{decomp}\left(H, \rho, \sigma\right) = \operatorname{sqrt}\left(\operatorname{decompSq}\left(H, \rho, \sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.decomp` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Take the nonnegative real square root of decompSq. This is the quantity denoted by the modified decomposition distance in equation (83), with the explicitly stated pure-state correspondence above.

**Definition 1.7 (The triangle assertion with an arbitrary middle state).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{IsHermitian}\left(H\left(n\right)\right)) \Rightarrow (\forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \omega: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \tau: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(\omega\right)) \Rightarrow ((\operatorname{IsDensity}\left(\tau\right)) \Rightarrow (\operatorname{decomp}\left(H, \rho, \tau\right) \le \operatorname{decomp}\left(H, \rho, \omega\right) + \operatorname{decomp}\left(H, \omega, \tau\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.claim` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section III.3.3 asks whether these quantities fulfill the triangle inequality. The assertion here ranges over all natural dimensions d and observable counts N, every family of Hermitian complex d by d matrices, and every triple of density matrices ρ, ω, τ. IsDensity is the existing positive-semidefinite, trace-one predicate. In particular ω need not be pure. Theorem 10 proves the pure-middle-state case; its hypothesis is retained in that source theorem but is absent from the universal extension considered here.

**Theorem 1.8 (A six-dimensional counterexample with a mixed middle state).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/toth-pitrik-2026-separable-decomposition-triangle` (refuted) by `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"toth-pitrik-2026-separable-decomposition-triangle","declaration_gid":"D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Use blocks A = {0,1}, B = {2,3}, C = {4,5}, and their density matrices ρA = ΠA/2, ρB = ΠB/2, ρC = ΠC/2. Let X,Y,Z be the Pauli matrices. The seven observables, written as triples of two by two diagonal blocks, are (X,X,0), (Y,Z,0), (Z,0,0), (0,Y,X), (0,0,Y), (0,0,Z), and L = diag(0,0,1,1,2,2). All seven are Hermitian. For a pure state in A with Bloch vector (x,y,z), the first six expectations are (x,y,z,0,0,0). In B they are (x,z,0,y,0,0), and in C they are (0,0,0,x,y,z). The last expectation is respectively 0, 1, or 2.

For the A-to-B side, pair the two X eigenvectors (1,±1)/√2 in A with the matching X eigenvectors in B, each with weight 1/2. Their first six expectations agree and their L expectations differ by one, giving cost 1/2. For the B-to-C side, pair the Y eigenvectors (1,±i)/√2 in B with the matching X eigenvectors in C, again with weights 1/2. Their fourth expectations agree and every other Pauli expectation vanishes; L again gives cost 1/2. Both mixtures have the required block marginals. Thus each short squared infimum is at most 1/2.

For any admissible A-to-C ensemble, the diagonal entries outside A give sums of nonnegative terms pₖ|ψₖ(j)|² equal to zero. At every positive weight all outside components therefore vanish. The corresponding statement holds outside C for φ. A unit vector in either two-dimensional block has a unit Bloch vector. The two Bloch vectors occupy disjoint observable coordinates, so their squared expectation differences sum to 1 + 1; the L difference contributes 4. Hence every positive-weight pair has pureCost 3. Zero-weight terms contribute zero and the weights sum to one, so every admissible total cost is 3. An explicit finite ensemble makes the set nonempty, and the long squared infimum is therefore 3.

Taking square roots, the long side is √3 and the two short sides sum to at most 2√(1/2) = √2. Since √3 > √2, claim is false. The middle density matrix is mixed and has the two different ensembles used on the short sides. This construction answers the general mixed-middle-state question; it does not contradict the pure-middle-state theorem.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.Decomposition`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.costs`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.decomp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.decompSq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.expectation`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.pureCost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](QubitWassersteinCouplings.md)
