# Bell-diagonal entanglement distance refutation

## Abstract

The entanglement distance of a Bell-diagonal state is not twice its squared concurrence.

**Definition 1.1 (One-site operators).**

$$\forall (\mu : \operatorname{Fin}\left(2\right)), \forall (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{onSite}\left(\mu, U\right) = (\operatorname{if} (\mu = 0) \operatorname{then} (\operatorname{Matrix}.of\left((\lambda (i : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\lambda (j : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\operatorname{if} (i.2 = j.2) \operatorname{then} (U\left(i.1\right)\left(j.1\right)) \operatorname{else} ((0 : \mathbb{C})))))\right)) \operatorname{else} (\operatorname{Matrix}.of\left((\lambda (i : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\lambda (j : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\operatorname{if} (i.1 = j.1) \operatorname{then} (U\left(i.2\right)\left(j.2\right)) \operatorname{else} ((0 : \mathbb{C})))))\right)))$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.onSite` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

For a two-qubit product basis, onSite acts by U on the selected coordinate and by the identity on the other coordinate. The two branches are selected by μ = 0 and μ ≠ 0.

**Definition 1.2 (Pauli observables on one site).**

$$\forall (\mu : \operatorname{Fin}\left(2\right)), \forall (i : \operatorname{Fin}\left(3\right)), \operatorname{sitePauli}\left(\mu, i\right) = \operatorname{onSite}\left(\mu, (\operatorname{if} (i = 0) \operatorname{then} (\operatorname{pauliMatrix}\left(\operatorname{Pauli}.X\right)) \operatorname{else} ((\operatorname{if} (i = 1) \operatorname{then} (\operatorname{pauliMatrix}\left(\operatorname{Pauli}.Y\right)) \operatorname{else} (\operatorname{pauliMatrix}\left(\operatorname{Pauli}.Z\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.sitePauli` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

sitePauli chooses X, Y or Z from the Fin(3) label i and places that Pauli on site μ through onSite. The Pauli matrices are the existing X, Y and Z matrices.

**Definition 1.3 (The variational site quantum-correlation distance).**

$$\forall (\mu : \operatorname{Fin}\left(2\right)), \forall (\sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \operatorname{siteQCD}\left(\mu, \sigma\right) = (\operatorname{Complex}.re\left(\operatorname{Matrix}.trace\left((\sigma) \cdot (\sigma)\right)\right)) - (\operatorname{sSup}\left(\{x : \mathbb{R} \mid \exists (n : \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\sum_{i : \operatorname{Fin}\left(3\right)} (n\left(i\right))^{2} = 1) \land (x = \operatorname{Complex}.re\left(\operatorname{Matrix}.trace\left((((\sigma) \cdot (\sum_{i : \operatorname{Fin}\left(3\right)} ((\operatorname{Complex}.ofReal\left(n\left(i\right)\right) : \mathbb{C})) \cdot (\operatorname{sitePauli}\left(\mu, i\right)))) \cdot (\sigma)) \cdot (\sum_{i : \operatorname{Fin}\left(3\right)} ((\operatorname{Complex}.ofReal\left(n\left(i\right)\right) : \mathbb{C})) \cdot (\operatorname{sitePauli}\left(\mu, i\right)))\right)\right))\}\right))$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.siteQCD` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

The site QCD is the real part of the trace of σ squared minus the supremum of the real trace quadratic form over real unit vectors n. Each Pauli coefficient n i is embedded into the complex matrices by Complex.ofReal. This is the one-site variational form of the source QCD.

**Definition 1.4 (The locally rotated mixture).**

$$\forall (k : \mathbb{N}), \forall (\mu : \operatorname{Fin}\left(2\right)), \forall (p : \operatorname{Fin}\left(k\right) \to \mathbb{R}), \forall (\rho{s} : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (U : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}.specialUnitaryGroup\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{rotated}\left(\mu, p, \rho{s}, U\right) = \sum_{j : \operatorname{Fin}\left(k\right)} ((\operatorname{Complex}.ofReal\left(p\left(j\right)\right) : \mathbb{C})) \cdot (((\operatorname{onSite}\left(\mu, (\operatorname{Subtype}.val\left(U\left(j\right)\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)) \cdot (\rho{s}\left(j\right))) \cdot (\operatorname{Matrix}.conjTranspose\left(\operatorname{onSite}\left(\mu, (\operatorname{Subtype}.val\left(U\left(j\right)\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.rotated` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

For a finite ensemble, rotated applies the SU(2) matrix selected for each component on site μ, conjugates that component, and averages with the real weights embedded in ℂ.

**Definition 1.5 (Entanglement distance).**

$$\forall (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \operatorname{ED}\left(\rho\right) = \operatorname{sInf}\left(\{x : \mathbb{R} \mid \exists (k : \mathbb{N}), \exists (p : \operatorname{Fin}\left(k\right) \to \mathbb{R}), \exists (\rho{s} : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (j : \operatorname{Fin}\left(k\right)), 0 \le p\left(j\right)) \land ((\sum_{j : \operatorname{Fin}\left(k\right)} p\left(j\right) = 1) \land ((\forall (j : \operatorname{Fin}\left(k\right)), (\operatorname{Matrix}.PosSemidef\left(\rho{s}\left(j\right)\right)) \land (\operatorname{Matrix}.trace\left(\rho{s}\left(j\right)\right) = (1 : \mathbb{C}))) \land ((\sum_{j : \operatorname{Fin}\left(k\right)} ((\operatorname{Complex}.ofReal\left(p\left(j\right)\right) : \mathbb{C})) \cdot (\rho{s}\left(j\right)) = \rho) \land (x = \sum_{\mu : \operatorname{Fin}\left(2\right)} \operatorname{sInf}\left(\{y : \mathbb{R} \mid \exists (U : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}.specialUnitaryGroup\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)), y = \operatorname{siteQCD}\left(\mu, \operatorname{rotated}\left(\mu, p, \rho{s}, U\right)\right)\}\right)))))\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.ED` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

ED takes the infimum over finite decompositions into positive semidefinite trace-one matrices and sums the two inner infima of the site QCD over families of local SU(2) rotations. The mixture constraint reconstructs ρ exactly. The sum includes both sites, μ = 0 and μ = 1, matching the source's twice-squared-concurrence normalization; the printed ED equation starts its site sum at μ = 1.

**Definition 1.6 (The four Bell projectors).**

$$\forall (\alpha : \operatorname{Fin}\left(4\right)), \operatorname{bellProjector}\left(\alpha\right) = \operatorname{Matrix}.of\left((\lambda (i : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\lambda (j : (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\operatorname{if} (\alpha = 0) \operatorname{then} (\operatorname{D5}.S3.QuantumBounds.CHSHWitness.bellDensity\left(i, j\right)) \operatorname{else} ((\operatorname{if} (\alpha = 1) \operatorname{then} ((\operatorname{if} ((i = (0, 0)) \land (j = (0, 0))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 1)) \land (j = (1, 1))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (0, 0)) \land (j = (1, 1))) \operatorname{then} (\frac{-(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 1)) \land (j = (0, 0))) \operatorname{then} (\frac{-(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((0 : \mathbb{C})))))))))) \operatorname{else} ((\operatorname{if} (\alpha = 2) \operatorname{then} ((\operatorname{if} ((i = (0, 1)) \land (j = (0, 1))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 0)) \land (j = (1, 0))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (0, 1)) \land (j = (1, 0))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 0)) \land (j = (0, 1))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((0 : \mathbb{C})))))))))) \operatorname{else} ((\operatorname{if} ((i = (0, 1)) \land (j = (0, 1))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 0)) \land (j = (1, 0))) \operatorname{then} (\frac{(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (0, 1)) \land (j = (1, 0))) \operatorname{then} (\frac{-(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((\operatorname{if} ((i = (1, 0)) \land (j = (0, 1))) \operatorname{then} (\frac{-(1 : \mathbb{C})}{(2 : \mathbb{C})}) \operatorname{else} ((0 : \mathbb{C})))))))))))))))))\right)$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.bellProjector` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

The four projectors are written entrywise in the product basis, in the order (|00⟩ + |11⟩)/√2, (|00⟩ − |11⟩)/√2, (|01⟩ + |10⟩)/√2 and (|01⟩ − |10⟩)/√2. These are the four Bell states in the source's Bell-diagonal decomposition.

**Definition 1.7 (Bell-diagonal states).**

$$\forall (p : \operatorname{Fin}\left(4\right) \to \mathbb{R}), \operatorname{bellDiagonal}\left(p\right) = \sum_{\alpha : \operatorname{Fin}\left(4\right)} ((\operatorname{Complex}.ofReal\left(p\left(\alpha\right)\right) : \mathbb{C})) \cdot (\operatorname{bellProjector}\left(\alpha\right))$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.bellDiagonal` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

For nonnegative weights summing to one, the weighted sum of the four Bell projectors is a Bell-diagonal state. The displayed definition also admits arbitrary real weights, embedded into the complex matrix algebra. This is the Bell-diagonal family used in the source.

**Definition 1.8 (Concurrence of a Bell-diagonal state).**

$$\forall (p : \operatorname{Fin}\left(4\right) \to \mathbb{R}), \operatorname{concurrence}\left(p\right) = \operatorname{max}\left(0, ((2) \cdot (\operatorname{Finset}.sup'\left(\operatorname{Finset}.univ\left(\right), \operatorname{Finset}.univ_{nonempty}\left(\right), p\right))) - (1)\right)$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.concurrence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

For nonnegative Bell-diagonal weights summing to one, concurrence is the positive part of twice the largest weight minus one. The displayed definition extends the same expression to arbitrary real weights.

**Definition 1.9 (The Bell-diagonal entanglement-distance claim).**

$$claim \Leftrightarrow (\forall (p : \operatorname{Fin}\left(4\right) \to \mathbb{R}), (\forall (\alpha : \operatorname{Fin}\left(4\right)), 0 \le p\left(\alpha\right)) \Rightarrow ((\sum_{\alpha : \operatorname{Fin}\left(4\right)} p\left(\alpha\right) = 1) \Rightarrow (\operatorname{ED}\left(\operatorname{bellDiagonal}\left(p\right)\right) = (2) \cdot ((\operatorname{concurrence}\left(p\right))^{2}))))$$

*Formalization.* `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.claim` (`✓ std3`).

*Citation.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

The source reports numerical evidence for the identity ED = 2 times squared concurrence on Bell-diagonal states, with its figure plotting ED/2. The claim requires this identity for every nonnegative weight vector on the four Bell states whose weights sum to one.

**Theorem 1.10 (A two-qubit counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/vesperini-bel-hadj-aissa-franzosi-2023-bell-diagonal-entanglement-distance-refutation` (refuted) by `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vesperini-bel-hadj-aissa-franzosi-2023-bell-diagonal-entanglement-distance-refutation","declaration_gid":"D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi (2023). *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*. DOI: [10.1038/s41598-023-29438-7](https://doi.org/10.1038/s41598-023-29438-7). URL: <https://arxiv.org/abs/2205.07143v2>.

*Commentary.*

Take the Bell-diagonal state with weights (16/25, 9/25, 0, 0). It is the equal mixture of the projectors onto the two nonorthogonal pure states (|00⟩ + q₊|11⟩)/√2 and (|00⟩ + q₋|11⟩)/√2, where q₊ = (7 + 24i)/25 and q₋ = (7 − 24i)/25. On either site, the SU(2) rotations diag((4 + 3i)/5,(4 − 3i)/5) and diag((3 + 4i)/5,(3 − 4i)/5) take the respective projectors to the first two Bell projectors. The rotated mixture is therefore diag(1/2,0,0,1/2). Both site QCD values are zero, hence ED is at most zero, while twice the squared concurrence is 98/625. Thus ED ≤ 0 < 98/625. These states and rotations give a counterexample to the claim.

## References

- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.ED`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.bellDiagonal`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.bellProjector`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.concurrence`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.onSite`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.rotated`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.sitePauli`
- Truth anchor: `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.siteQCD`
- Dependency: [D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot](../Entanglement/LocalMarginalCorrelationBlindSpot.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](StabilizerPairLocalUnitaryInequivalence.md)
