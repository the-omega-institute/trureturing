# Refuting the binary detection threshold conjecture

## Abstract

The Section 4.3 conjecture eta* = 4/(m+4) is refuted at m = 13 by a three-input leader model and a universal local extension at efficiency 6/25.

**Definition 1.1 (The binary parity distribution).**

$$\forall G \in \operatorname{Fin}\left(13\right) \to \left(\operatorname{Fin}\left(13\right) \to \operatorname{Bool}\right),\; \forall x \in \operatorname{Fin}\left(13\right),\; \forall y \in \operatorname{Fin}\left(13\right),\; \forall a \in \operatorname{Bool},\; \forall b \in \operatorname{Bool},\; \operatorname{parityBox}\left(G, x, y, a, b\right) = \operatorname{ite}\left(\operatorname{Bool}.\operatorname{xor}\left(a, b\right) = G\left(x, y\right), \frac{1}{2}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.parityBox` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each input pair the parity box gives probability one half exactly to the two Boolean output pairs whose xor is the prescribed bit.

**Theorem 1.2 (A binary table is determined by its marginals and one entry).**

$$\forall f \in \operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right),\; \forall g \in \operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right),\; \forall ma \in \operatorname{Bool},\; \forall mb \in \operatorname{Bool},\; (\sum_{a \in \operatorname{Bool}}(\sum_{b \in \operatorname{Bool}}(f\left(a, b\right))) = \sum_{a \in \operatorname{Bool}}(\sum_{b \in \operatorname{Bool}}(g\left(a, b\right)))) \Rightarrow \left((\sum_{b \in \operatorname{Bool}}(f\left(ma, b\right)) = \sum_{b \in \operatorname{Bool}}(g\left(ma, b\right))) \Rightarrow \left((\sum_{a \in \operatorname{Bool}}(f\left(a, mb\right)) = \sum_{a \in \operatorname{Bool}}(g\left(a, mb\right))) \Rightarrow \left((f\left(ma, mb\right) = g\left(ma, mb\right)) \Rightarrow f = g\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.binary_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two real two-by-two tables agree when their total masses, one selected row sum, one selected column sum and the selected corner entry agree.

**Definition 1.3 (No-signalling box).**

$$\forall m \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right)\right)\right),\; \operatorname{IsNSBox}\left(p\right) = \left((\forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \forall a \in \operatorname{Bool},\; \forall b \in \operatorname{Bool},\; 0 \le \operatorname{p}\left(x, y, a, b\right)) \land ((\forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \sum_{a \in \operatorname{Bool}}(\sum_{b \in \operatorname{Bool}}(\operatorname{p}\left(x, y, a, b\right))) = 1) \land ((\forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \forall yPrime \in \operatorname{Fin}\left(m\right),\; \forall a \in \operatorname{Bool},\; \sum_{b \in \operatorname{Bool}}(\operatorname{p}\left(x, y, a, b\right)) = \sum_{b \in \operatorname{Bool}}(\operatorname{p}\left(x, yPrime, a, b\right))) \land (\forall x \in \operatorname{Fin}\left(m\right),\; \forall xPrime \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \forall b \in \operatorname{Bool},\; \sum_{a \in \operatorname{Bool}}(\operatorname{p}\left(x, y, a, b\right)) = \sum_{a \in \operatorname{Bool}}(\operatorname{p}\left(xPrime, y, a, b\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.IsNSBox` (`✓ std3`).

*Citation.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

Cope, Section 2, arXiv v3 p. 2: “However, we do assume that Alice and Bob can isolate their systems, also referred to here as devices, from communicating with each other.” Inputs are Fin m and outputs are Bool; the formula also records nonnegativity and normalization.

**Definition 1.4 (Lossy extension).**

$$\forall m \in \mathbb{N},\; \forall eta \in \mathbb{R},\; \forall p \in \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right)\right)\right),\; \forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; (\forall a \in \operatorname{Bool},\; \forall b \in \operatorname{Bool},\; \operatorname{lossy}\left(eta, p, x, y, \operatorname{some}\left(a\right), \operatorname{some}\left(b\right)\right) = (eta)^{2} \cdot \operatorname{p}\left(x, y, a, b\right)) \land ((\forall a \in \operatorname{Bool},\; \operatorname{lossy}\left(eta, p, x, y, \operatorname{some}\left(a\right), \operatorname{none}\right) = eta \cdot \left(1 - eta\right) \cdot \sum_{b \in \operatorname{Bool}}(\operatorname{p}\left(x, y, a, b\right))) \land ((\forall b \in \operatorname{Bool},\; \operatorname{lossy}\left(eta, p, x, y, \operatorname{none}, \operatorname{some}\left(b\right)\right) = eta \cdot \left(1 - eta\right) \cdot \sum_{a \in \operatorname{Bool}}(\operatorname{p}\left(x, y, a, b\right))) \land (\operatorname{lossy}\left(eta, p, x, y, \operatorname{none}, \operatorname{none}\right) = (1 - eta)^{2})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.lossy` (`✓ std3`).

*Citation.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

Cope, Section 2, arXiv v3 p. 2: “The model considered here adds an extra output to both parties to alter the original distribution p(ab|xy) in the following way:” The four branches are equation (3), with none denoting F.

**Definition 1.5 (Local box).**

$$\forall m \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Option}\left(\operatorname{Bool}\right) \to \left(\operatorname{Option}\left(\operatorname{Bool}\right) \to \mathbb{R}\right)\right)\right),\; \operatorname{IsLocal}\left(q\right) = \left(\exists w \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right), \operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right)\right) \to \mathbb{R},\; (\forall s \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right), \operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right)\right),\; 0 \le \operatorname{w}\left(s\right)) \land ((\sum_{s \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right), \operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right)\right)}(\operatorname{w}\left(s\right)) = 1) \land (\forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \forall a \in \operatorname{Option}\left(\operatorname{Bool}\right),\; \forall b \in \operatorname{Option}\left(\operatorname{Bool}\right),\; \operatorname{q}\left(x, y, a, b\right) = \sum_{s \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right), \operatorname{Fin}\left(m\right) \to \operatorname{Option}\left(\operatorname{Bool}\right)\right)}(\operatorname{w}\left(s\right) \cdot \operatorname{ite}\left((\operatorname{Prod}.\operatorname{fst}\left(s, x\right) = a) \land (\operatorname{Prod}.\operatorname{snd}\left(s, y\right) = b), 1, 0\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.IsLocal` (`✓ std3`).

*Citation.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

Cope, Section 2, arXiv v3 p. 2: “These distributions may always be expressed as convex combinations of deterministic distributions p(ab|xy)=δₐ,ₐₓδᵦ,ᵦᵧ, which are finite in number.” The finite weights run over pairs of deterministic Option Bool response functions.

**Definition 1.6 (Detection threshold).**

$$\forall m \in \mathbb{N},\; \operatorname{etaStar}\left(m\right) = \operatorname{sSup}\left(\ \{eta:\mathbb{R} \mid (0 \le eta) \land ((eta \le 1) \land (\forall p \in \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right)\right)\right),\; (\operatorname{IsNSBox}\left(p\right)) \Rightarrow \operatorname{IsLocal}\left(\operatorname{lossy}\left(eta, p\right)\right)))\ \}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.etaStar` (`✓ std3`).

*Citation.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

Cope, Section 2, arXiv v3 p. 3: “We will refer to η∗ as the no-signalling threshold.” etaStar is the supremum of efficiencies in [0,1] for which every no-signalling box has a local lossy extension.

**Definition 1.7 (The Section 4.3 conjecture).**

$$claim = \left(\forall m \in \mathbb{N},\; (2 \le m) \Rightarrow \operatorname{etaStar}\left(m\right) = \frac{4}{((m:\mathbb{R})+4)}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.claim` (`✓ std3`).

*Citation.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

Cope, Section 4.3, arXiv v3 p. 6: “In order to prove that our conjecture of η∗=4/(m+4) for mₐ=mᵦ=m is correct, one would need to provide a extremal NS distribution pᴺˢ, and corresponding Bell inequality sᵡʸₐ′ᵦ′, such that ∑ₐ′,ᵦ′,ₓ,ᵧ sᵡʸₐ′ᵦ′ pᴺˢη(a′b′|xy) ≰ k, ∀ η > η∗.” The Lean claim encodes the conjectured equality for every natural m at least 2; inputs are Fin m and outputs are Bool, with none denoting failure.

**Theorem 1.8 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cope-2021-binary-detection-threshold` (refuted) by `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cope-2021-binary-detection-threshold","declaration_gid":"D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Cope (2021). *The Binary-Outcome Detection Loophole*. DOI: [10.1088/1367-2630/ac10a5](https://doi.org/10.1088/1367-2630/ac10a5). URL: <https://arxiv.org/abs/2005.03344v3>.

*Commentary.*

At m = 13, the counting identity and universal extension prove 6/25 <= etaStar 13, contradicting etaStar 13 = 4/17.

The response indicators use FiberwiseEqualDistanceLift.labelKernel on paired outputs. The finite output maps use CycleSingleCutMinimax.push on the product outcome space, and the two marginal tables use ChainRule.marginal with swapped coordinates for Bob. The independent parity-bit weights use GreenClassWindowEntropy.windowLaw with complemented ScoreBridge.bernoulliMass bits.

A deterministic response atom is the product of the two response indicators. Any finite family of such atoms with nonnegative weights summing to one defines a local box: summing weights over equal response functions gives the weights in IsLocal.

For each matrix G : Fin 13 -> Fin 13 -> Bool, the parity box assigns one half exactly when Bool.xor a b = G x y. The leader model includes the all-failure atom with weight (13-12)^2/25^2 = 1/625. Each ordered triple of distinct inputs, each triple of leader bits and each of the two leader orientations has weight (48*13/25^2)/(2*13*12*11*8).

On the ordered triple i,j,k the leader returns ri,rj,rk respectively and fails on every other input. A follower at y returns the common value of Bool.xor ri (G i y), Bool.xor rj (G j y), Bool.xor rk (G k y) when all three agree, and fails otherwise. The opposite orientation transposes G and exchanges the parties. Exactly two of the eight leader bit patterns agree.

The model is the sum of these weighted deterministic response indicators and the all-failure atom. There are 1716 ordered distinct triples; for a fixed input 396 contain it and 1320 miss it. The two orientations give joint entries 18/625 on the prescribed parity and zero on the other parity, each single-failure entry 57/625, and the double-failure entry 361/625. Thus the model equals lossy (6/25) of the parity box for every G, and that lossy parity box is local.

The active leader part has total weight 624/625. Its joint conclusive probability is c = 3/52 and each party's single conclusive probability is d = 25/104, so the calibrated efficiency is c/d = 6/25. Optimizing raw joint success alone does not optimize this ratio.

Every binary no-signalling box is reconstructed as a finite mixture of locally mapped parity boxes. A common uniform threshold selects active inputs and gives pair activation probabilities equal to the minimum of their activation parameters. Independent parity bits then match each minor-output joint mass; normalization and the two marginals determine the other three entries. Local output maps preserve locality and commute with lossy, and normalized mixtures preserve both identities. This extends the leader model to every IsNSBox at m = 13.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.IsLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.IsNSBox`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.binary_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.etaStar`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.lossy`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.parityBox`
- Truth anchor: `D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationConfidenceFailure](../../Arith/FibonacciAtomic/Learning/RawCorrelationConfidenceFailure.md)
- Dependency: [D5/S3/Entropy/Forgetting/CompletionEntropyMinimality](../../Entropy/Forgetting/CompletionEntropyMinimality.md)
- Dependency: [D5/S3/Entropy/NamingWindow/FutureWordInformationChain](../../Entropy/NamingWindow/FutureWordInformationChain.md)
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](../../Entropy/NamingWindow/GreenClassWindowEntropy.md)
- Dependency: [D5/S3/Entropy/NamingWindow/SumProductUpdate](../../Entropy/NamingWindow/SumProductUpdate.md)
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope](../../Estimation/DataProcessing/FiniteSimplexFiberPolytope.md)
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../../TotalVariation/CycleSingleCutMinimax.md)
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](../../TotalVariation/Equality/FiberwiseEqualDistanceLift.md)
