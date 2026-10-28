# The qutrit complementary-entropy frontier

## Abstract

Complementary qutrit channels with a qutrit environment have a sharp lower boundary for their map entropies, attained by a one-parameter family and its complementary channels.

**Definition 1.1 (Stinespring isometries).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.admissible}\left(V\right) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(V\right) \cdot V = (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)))$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.admissible` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The input, system and environment each have dimension three. Rows of V are indexed by system-environment pairs, and its columns by the input basis. The isometry condition is the trace-preserving condition in the Stinespring description of Section II.

**Definition 1.2 (Exchange of system and environment).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(V\right) = ((p:(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right))) \mapsto (i:\operatorname{Fin}\left(3\right)) \mapsto V\left((p.2,p.1), i\right))$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.swap` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

Exchanging the two row indices exchanges the system and environment. Thus channelB applied to swap V is the complementary channel of channelB applied to V, as in Section II, Equations (5)-(7).

**Definition 1.3 (The system channel).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \forall R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.channelB}\left(V, R\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(V \cdot R \cdot \operatorname{Matrix.conjTranspose}\left(V\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.channelB` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

Section II describes a channel by an isometry followed by a partial trace. D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight traces out the environment, the second factor. The displayed definition applies to every complex matrix R.

**Definition 1.4 (The joint output of the maximally mixed input).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.joint}\left(V\right) = V \cdot \operatorname{SMul.smul}\left((\frac{1}{3}:\mathbb{R}), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))\right) \cdot \operatorname{Matrix.conjTranspose}\left(V\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.joint` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The input is one third of the identity matrix. Multiplication by V and its conjugate transpose gives the joint system-environment output. For an isometry this is a positive matrix of trace one.

**Definition 1.5 (The system marginal).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.rhoB}\left(V\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.joint}\left(V\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.rhoB` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The right partial trace of the joint output retains the system. For an isometry it is the image of the maximally mixed input under the system channel in Proposition 1.

**Definition 1.6 (The environment marginal).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.rhoE}\left(V\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.joint}\left(V\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.rhoE` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft traces out the system. The resulting environment matrix is the image of the maximally mixed input under the complementary channel in Proposition 1.

**Definition 1.7 (The normalized Choi matrix).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.choi}\left(V\right) = ((p:(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right))) \mapsto (q:(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right))) \mapsto \operatorname{SMul.smul}\left((\frac{1}{3}:\mathbb{R}), \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.channelB}\left(V, \operatorname{Matrix.single}\left(p.1, q.1, (1:\mathbb{C})\right)\right)\left(p.2, q.2\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.choi` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

Section II, Equations (2)-(3), arranges the images of the matrix units into blocks. The factor one third normalizes the Choi matrix to trace one for an isometry. Matrix.single supplies the complex matrix unit with row p.1 and column q.1; the block entry has row p.2 and column q.2.

**Definition 1.8 (Entropy of the system output).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.outputEntropy}\left(V\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.rhoB}\left(V\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.outputEntropy` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy sums Real.negMulLog over the eigenvalues. Its displayed matrix argument is rhoB V; the Hermiticity proof argument obtained from positive semidefiniteness is not displayed. The logarithm is natural, and zero eigenvalues contribute zero.

**Definition 1.9 (Entropy of the normalized Choi matrix).**

$$\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(V\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.choi}\left(V\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.mapEntropy` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

This is the map entropy of Section II, Equation (3). The displayed matrix argument of D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy is choi V; the Hermiticity proof argument obtained from positive semidefiniteness is not displayed. Proposition 1 relates this entropy to the complementary output on the maximally mixed input.

**Definition 1.10 (Entropy of three real coordinates).**

$$\forall x \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.entropy3}\left(x\right) = \sum_{i:\operatorname{Fin}\left(3\right)}\operatorname{Real.negMulLog}\left(x\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.entropy3` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The sum uses Real.negMulLog, with its continuous value zero at zero. For a nonnegative triple of sum one this is Shannon entropy in nats, and for a qutrit spectrum it is the spectral entropy.

**Definition 1.11 (The binary-entropy coordinate).**

$$\forall a \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.h}\left(a\right) = \operatorname{Real.binEntropy}\left(a\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.h` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

Real.binEntropy is the first coordinate of the curve in Equation (20). On the unit interval it is the entropy of the two probabilities a and 1 - a, including their zero endpoint values.

**Definition 1.12 (The three-coordinate entropy).**

$$\forall a \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.g}\left(a\right) = \operatorname{Real.negMulLog}\left((\frac{1}{3}:\mathbb{R}) + a\right) + \operatorname{Real.negMulLog}\left((\frac{1}{3}:\mathbb{R})\right) + \operatorname{Real.negMulLog}\left((\frac{1}{3}:\mathbb{R}) - a\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.g` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The second coordinate is the entropy of the probabilities 1/3 + a, 1/3 and 1/3 - a on the interval from zero to one third. Each summand is the Mathlib function Real.negMulLog.

**Definition 1.13 (The attaining Stinespring family).**

$$\forall a \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right) = \operatorname{Matrix.single}\left((0,0), 0, (1:\mathbb{C})\right) + \operatorname{Matrix.single}\left((1,0), 1, \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(1 - 3 \cdot a\right)\right)\right) + \operatorname{Matrix.single}\left((0,1), 1, \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(3 \cdot a\right)\right)\right) + \operatorname{Matrix.single}\left((2,0), 2, (1:\mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.attainer` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The two nonzero environment slices are the source's Kraus operators diag(1, sqrt(1 - 3a), 1) and sqrt(3a) times the matrix unit with row zero and column one. The third slice is zero. Complex.ofReal displays the real-to-complex casts of the square roots. The family is an isometry for 0 <= a <= 1/3.

**Definition 1.14 (The entropy bound and its attainment).**

$$\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.claim} \Leftrightarrow ((\forall V \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.admissible}\left(V\right)) \Rightarrow (\forall a \in \mathbb{R},\; (a \in \operatorname{Set.Icc}\left(0, (\frac{1}{3}:\mathbb{R})\right)) \Rightarrow (((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(V\right) \le \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.h}\left(a\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.g}\left(a\right) \le \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(V\right)\right))) \land ((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(V\right)\right) \le \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.h}\left(a\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.g}\left(a\right) \le \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(V\right)))))) \land (\forall a \in \mathbb{R},\; (a \in \operatorname{Set.Icc}\left(0, (\frac{1}{3}:\mathbb{R})\right)) \Rightarrow (((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.admissible}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right)) \land ((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right) = \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.h}\left(a\right)) \land (\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right)\right) = \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.g}\left(a\right)))) \land ((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.admissible}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right)\right)) \land ((\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right)\right) = \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.g}\left(a\right)) \land (\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.mapEntropy}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.swap}\left(\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.attainer}\left(a\right)\right)\right)\right) = \operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.h}\left(a\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.claim` (`✓ std3`).

*Citation.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

Conjecture 1 on page 5 gives the curve and its reflection through equality of the two map entropies. The statement includes both directions of the entropy bound and the attaining family in both orders. The last term of Equation (20) is read as -(1/3 - a) log(1/3 - a), as the source's attaining channels give. The parameter interval here is the closed [0, 1/3].

**Theorem 1.15 (The sharp complementary-entropy bound).**

$$\operatorname{D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.result` (`✓ std3`). ∎

*Resolves.* `Problems/czartowski-braun-zyczkowski-2019-qutrit-complementary-entropy-frontier` (proved) by `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"czartowski-braun-zyczkowski-2019-qutrit-complementary-entropy-frontier","declaration_gid":"D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jakub Czartowski; Daniel Braun; Karol Życzkowski (2019). *Trade-off relations for operation entropy of complementary quantum channels*. DOI: [10.1142/S0219749919500461](https://doi.org/10.1142/S0219749919500461). URL: <https://arxiv.org/abs/1908.03492v1>.

*Commentary.*

The normalized Choi matrix and the environment output have the same nonzero spectrum: their characteristic polynomials differ by a factor X^6. Zero eigenvalues contribute zero to Real.negMulLog, so the Choi entropy equals the complementary output entropy, as in Proposition 1.

In eigenbases of the two output matrices, the diagonal of the joint output is a three-by-three spectral table. Its entries lie between zero and one third, its total is one, and its row and column sums are the two output spectra. A row sum r and a column sum s satisfy r + s <= 4/3 and r - s <= 2/3.

Two-point spreading for Real.negMulLog bounds the entropy of three coordinates in an interval by the entropy at the extreme triple. An output entropy at most h(a) forces a spectral coordinate r above one half, with u = 1 - r between zero and a. The table inequalities place every coordinate of the other spectrum between 1/3 - u and 1/3 + u. Its entropy is therefore at least g(u), which is at least g(a) because g decreases on the parameter interval.

The attaining family has system spectrum (1/3 + a, 1/3 - a, 1/3) and environment spectrum (1 - a, a, 0). These give map entropies h(a) and g(a); exchanging the factors gives the reflected point. Thus the entropy bounds are attained throughout the closed parameter interval.

## References

- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.admissible`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.attainer`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.channelB`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.choi`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.claim`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.entropy3`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.g`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.h`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.joint`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.mapEntropy`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.outputEntropy`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.result`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.rhoB`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.rhoE`
- Truth anchor: `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.swap`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation](../QuantumChannels/TruncatedLossDephasingOptimizerRefutation.md)
