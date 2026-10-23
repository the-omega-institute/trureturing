# AntidistinguishabilityOverlapNonTight

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Theorem 1.1 (squared modulus lipschitz).**

$$\forall (\operatorname{z} : \mathbb{C}) , \forall (\operatorname{w} : \mathbb{C}) , (\Vert \operatorname{z} \Vert \leq 1) \to (\Vert \operatorname{w} \Vert \leq 1) \to \lvert (\Vert \operatorname{z} \Vert)^{2} - (\Vert \operatorname{w} \Vert)^{2} \rvert \leq 2 \cdot \Vert \operatorname{z} - \operatorname{w} \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.squared_modulus_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Squared norms on the complex unit ball are Lipschitz with constant two.

**Theorem 1.2 (norm square gram factor).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{V} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{r}) \mathbb{C}) , \operatorname{Matrix}.\operatorname{map} (\operatorname{RHLinalg}.\operatorname{normSqMatrix} (\operatorname{V} \cdot (\operatorname{V}).\operatorname{conjTranspose})) (\operatorname{algebraMap} \mathbb{R} \mathbb{C}) = (\operatorname{fun} (\operatorname{i} : \operatorname{Fin} \operatorname{n}) \mapsto \operatorname{Function}.\operatorname{uncurry} (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{PureState}.\operatorname{PureStateHandshake}.\operatorname{rankOneDensity} (\operatorname{V} \operatorname{i}))) \cdot ((\operatorname{fun} (\operatorname{i} : \operatorname{Fin} \operatorname{n}) \mapsto \operatorname{Function}.\operatorname{uncurry} (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{PureState}.\operatorname{PureStateHandshake}.\operatorname{rankOneDensity} (\operatorname{V} \operatorname{i})))).\operatorname{conjTranspose}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.norm_square_gram_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The entrywise squared-modulus Gram matrix factors through the outer products of its rows.

**Theorem 1.3 (norm square gram rank).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{V} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{r}) \mathbb{C}) , (\operatorname{RHLinalg}.\operatorname{normSqMatrix} (\operatorname{V} \cdot (\operatorname{V}).\operatorname{conjTranspose})).\operatorname{rank} \leq \operatorname{r} \cdot \operatorname{r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.norm_square_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The squared-modulus Gram matrix of r-dimensional rows has rank at most r squared.

**Definition 1.4 (IsTight).**

$$\forall (n : \mathbb{N}) , IsTight n = \forall \varepsilon : \mathbb{R} , \varepsilon > 0 \to \exists (d : \mathbb{N}) (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , (\forall (i : Fin n) , \Vert \psi i \Vert = 1) \land (\forall (i j : Fin n) , i \neq j \to \Vert inner \mathbb{C} (\psi i) (\psi j) \Vert^{2} \leq cSq n + \varepsilon) \land \neg IsAntidistinguishable \psi$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.IsTight` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Section 6, page 17: “We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.” The displayed tightness condition uses a squared-overlap margin. For n ≥ 10 the source cap is positive, so squaring reparametrizes its positive margin.

**Definition 1.5 (claim).**

$$claim = \forall n : \mathbb{N} , 10 \leq n \to \neg IsTight n$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Section 6, page 17: “We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.” The statement answers the question by proving non-tightness for every n ≥ 10; n = 5,…,9 remain open.

**Theorem 1.6 (quantitative antidistinguishability).**

$$\forall (n : \mathbb{N}) , 10 \leq n \to \forall (d : \mathbb{N}) (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , (\forall (i : Fin n) , \Vert \psi i \Vert = 1) \to (\forall (i j : Fin n) , i \neq j \to \Vert inner \mathbb{C} (\psi i) (\psi j) \Vert^{2} \leq cSq n + delta n) \to IsAntidistinguishable \psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.quantitative_antidistinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.7 (result).**

$$\forall n : \mathbb{N} , 10 \leq n \to \neg IsTight n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnston-russo-sikora-2025-antidistinguishability-tightness` (proved) by `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnston-russo-sikora-2025-antidistinguishability-tightness","declaration_gid":"D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.IsTight`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.norm_square_gram_factor`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.norm_square_gram_rank`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.quantitative_antidistinguishability`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.squared_modulus_lipschitz`
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../Matrix/CommutatorGap.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum](AntidistinguishabilitySpectrum.md)
- Dependency: [D5/S3/Quantum/Measurement/OverlapLowRankDistance](OverlapLowRankDistance.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](../TensorNetworks/BridgeGraph/QuantumMaxFlowBound.md)
