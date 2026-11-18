# DoubleSidedBottleneckBSC

## Abstract

Exact binary symmetric channel optimality near independent binary sources.

**Definition 1.1 (hbInv).**

$$\forall (\operatorname{y} : \mathbb{R}) , \operatorname{hbInv} \operatorname{y} = \operatorname{Function} . \operatorname{invFun} (\operatorname{fun} (\operatorname{a} : \operatorname{Set} . \operatorname{Icc} (0 : \mathbb{R}) (1 / 2 : \mathbb{R})) \mapsto \operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{CloningMachine} . \operatorname{binaryEntropyBits} \operatorname{a} . \operatorname{val}) \operatorname{y}$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.hbInv` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The inverse is taken on the subtype [0,1/2], with zero as the nonempty witness. Proposition proof arguments are suppressed.

**Definition 1.2 (dsbs).**

$$\forall (\operatorname{p} : \mathbb{R}), (\forall (\operatorname{xy} : \operatorname{Bool} \times \operatorname{Bool}), (\operatorname{dsbs} \operatorname{p} \operatorname{xy} = ((\operatorname{if} \operatorname{xy} . 1 = \operatorname{xy} . 2 \operatorname{then} 1 - \operatorname{p} \operatorname{else} \operatorname{p}) / 2)))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.dsbs` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines dsbs.

**Definition 1.3 (bsc).**

$$\forall (\operatorname{a} : \operatorname{Set} . \operatorname{Icc} (0 : \mathbb{R}) (1 / 2 : \mathbb{R})) , \operatorname{bsc} \operatorname{a} = \operatorname{let} \operatorname{q} : \operatorname{NNReal} := \langle \operatorname{a} . \operatorname{val} , \operatorname{a} . \operatorname{property} . 1 \rangle ; \operatorname{fun} (\operatorname{x} : \operatorname{Bool}) \mapsto (\operatorname{PMF} . \operatorname{ofFintype} (\operatorname{fun} (\operatorname{z} : \operatorname{Bool}) \mapsto ((\operatorname{cond} \operatorname{z} \operatorname{q} (1 - \operatorname{q})) : \operatorname{ENNReal}))) . \operatorname{map} (\operatorname{fun} (\operatorname{z} : \operatorname{Bool}) \mapsto \operatorname{if} \operatorname{Bool} . \operatorname{xor} \operatorname{x} \operatorname{z} \operatorname{then} (1 : \operatorname{Fin} 2) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.bsc` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The map applies a Bernoulli crossover to the input bit and labels the output false by 0 and true by 1. The value q is a nonnegative real; proof arguments of the PMF constructor are suppressed.

**Definition 1.4 (mutualInformationBits).**

$$\forall (\operatorname{A} : \operatorname{Type}), (\forall (\operatorname{B} : \operatorname{Type}), ([\operatorname{Fintype} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] \forall (\operatorname{q} : \operatorname{A} \times \operatorname{B} \to \mathbb{R}), (\operatorname{mutualInformationBits} \operatorname{q} = (\operatorname{D5} . \operatorname{S3} . \operatorname{Entropy} . \operatorname{MutualInformation} . \operatorname{mutualInformation} \operatorname{q} / \operatorname{Real} . \operatorname{log} 2))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.mutualInformationBits` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines mutualInformationBits.

**Definition 1.5 (rate).**

$$\forall (\operatorname{n} : \mathbb{N}), (\forall (\operatorname{K} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{n}))), (\operatorname{rate} \operatorname{K} = (\operatorname{mutualInformationBits} (\operatorname{fun} \operatorname{xu} : \operatorname{Bool} \times \operatorname{Fin} \operatorname{n} \mapsto (\operatorname{K} \operatorname{xu} . 1 \operatorname{xu} . 2) . \operatorname{toReal} / 2))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.rate` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines rate.

**Definition 1.6 (outputJoint).**

$$\forall (\operatorname{n} : \mathbb{N}), (\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{p} : \mathbb{R}), (\forall (\operatorname{K} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{n}))), (\forall (\operatorname{L} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{m}))), (\forall (\operatorname{uv} : \operatorname{Fin} \operatorname{n} \times \operatorname{Fin} \operatorname{m}), (\operatorname{outputJoint} \operatorname{p} \operatorname{K} \operatorname{L} \operatorname{uv} = (\sum \operatorname{x} : \operatorname{Bool} , \sum \operatorname{y} : \operatorname{Bool} , \operatorname{dsbs} \operatorname{p} (\operatorname{x} , \operatorname{y}) \cdot (\operatorname{K} \operatorname{x} \operatorname{uv} . 1) . \operatorname{toReal} \cdot (\operatorname{L} \operatorname{y} \operatorname{uv} . 2) . \operatorname{toReal})))))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.outputJoint` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines outputJoint.

**Definition 1.7 (objective).**

$$\forall (\operatorname{n} : \mathbb{N}), (\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{p} : \mathbb{R}), (\forall (\operatorname{K} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{n}))), (\forall (\operatorname{L} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{m}))), (\operatorname{objective} \operatorname{p} \operatorname{K} \operatorname{L} = (\operatorname{mutualInformationBits} (\operatorname{outputJoint} \operatorname{p} \operatorname{K} \operatorname{L})))))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.objective` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines objective.

**Definition 1.8 (achievable).**

$$\forall (\operatorname{Cu} : \mathbb{R}), (\forall (\operatorname{Cv} : \mathbb{R}), (\forall (\operatorname{p} : \mathbb{R}), (\operatorname{achievable} \operatorname{Cu} \operatorname{Cv} \operatorname{p} = (\{ \operatorname{r} | \exists (\operatorname{n} \operatorname{m} : \mathbb{N}) (\operatorname{K} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{n}))) (\operatorname{L} : (\operatorname{Bool} \to \operatorname{PMF} (\operatorname{Fin} \operatorname{m}))) , \operatorname{rate} \operatorname{K} \le \operatorname{Cu} \land \operatorname{rate} \operatorname{L} \le \operatorname{Cv} \land \operatorname{r} = (\operatorname{objective} \operatorname{p} \operatorname{K} \operatorname{L} : \operatorname{EReal}) \}))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.achievable` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines achievable.

**Definition 1.9 (R).**

$$\forall (\operatorname{Cu} : \mathbb{R}), (\forall (\operatorname{Cv} : \mathbb{R}), (\forall (\operatorname{p} : \mathbb{R}), (\operatorname{R} \operatorname{Cu} \operatorname{Cv} \operatorname{p} = (\operatorname{sSup} (\operatorname{achievable} \operatorname{Cu} \operatorname{Cv} \operatorname{p})))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.R` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines R.

**Definition 1.10 (bscOptimal).**

$$\forall (\operatorname{Cu} : \mathbb{R}), (\forall (\operatorname{Cv} : \mathbb{R}), (\forall (\operatorname{p} : \mathbb{R}), (\operatorname{bscOptimal} \operatorname{Cu} \operatorname{Cv} \operatorname{p} = (\operatorname{rate} (\operatorname{bsc} (\operatorname{hbInv} (1 - \operatorname{Cu}))) \le \operatorname{Cu} \land \operatorname{rate} (\operatorname{bsc} (\operatorname{hbInv} (1 - \operatorname{Cv}))) \le \operatorname{Cv} \land \operatorname{R} \operatorname{Cu} \operatorname{Cv} \operatorname{p} = (\operatorname{objective} \operatorname{p} (\operatorname{bsc} (\operatorname{hbInv} (1 - \operatorname{Cu}))) (\operatorname{bsc} (\operatorname{hbInv} (1 - \operatorname{Cv}))) : \operatorname{EReal})))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.bscOptimal` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines bscOptimal.

**Definition 1.11 (claim).**

$$\operatorname{claim} = (\forall (\operatorname{Cu} : \mathbb{R}), (0 \le \operatorname{Cu}) \implies (\operatorname{Cu} \le 1) \implies (\forall (\operatorname{Cv} : \mathbb{R}), (0 \le \operatorname{Cv}) \implies (\operatorname{Cv} \le 1) \implies ((\operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{CloningMachine} . \operatorname{binaryEntropyBits} (\operatorname{hbInv} (1 - \operatorname{Cu})) . \operatorname{val} = 1 - \operatorname{Cu}) \land (\operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{CloningMachine} . \operatorname{binaryEntropyBits} (\operatorname{hbInv} (1 - \operatorname{Cv})) . \operatorname{val} = 1 - \operatorname{Cv}) \land (\exists (\theta : \mathbb{R}), (0 \le \theta) \land (\theta < 1 / 2) \land (\forall (\operatorname{p} : \mathbb{R}), 0 \le \operatorname{p} \to \operatorname{p} \le 1 / 2 \to \theta < \operatorname{p} \to \operatorname{bscOptimal} \operatorname{Cu} \operatorname{Cv} \operatorname{p})))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckBSC.claim` (`✓ std3`).

*Citation.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

Conjecture 3, printed p. 11: “For every $(C_{u} , C_{v}) \in [0 , 1] \times [0 , 1]$, there exists $\theta (C_{u} , C_{v})$, such that for every $\operatorname{p} > \theta (C_{u} , C_{v})$ the achieving test-channels $P_{U|X}$ and $P_{V|Y}$ are BSC with parameters $\alpha = \left(h_{b}\right)^{-1} (1 - C_{u})$ and $\beta = \left(h_{b}\right)^{-1} (1 - C_{v})$ respectively.”

The crossover p ranges over [0,1/2]; the threshold belongs to [0,1/2). Every finite output size is included, and optimality means attainment by the specified BSC pair. The entropy inverse equations and both candidate rate constraints are explicit.

**Theorem 1.12 (result).**

$$\forall (\operatorname{Cu} : \mathbb{R}), (0 \le \operatorname{Cu}) \implies (\operatorname{Cu} \le 1) \implies (\forall (\operatorname{Cv} : \mathbb{R}), (0 \le \operatorname{Cv}) \implies (\operatorname{Cv} \le 1) \implies ((\operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{CloningMachine} . \operatorname{binaryEntropyBits} (\operatorname{hbInv} (1 - \operatorname{Cu})) . \operatorname{val} = 1 - \operatorname{Cu}) \land (\operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{CloningMachine} . \operatorname{binaryEntropyBits} (\operatorname{hbInv} (1 - \operatorname{Cv})) . \operatorname{val} = 1 - \operatorname{Cv}) \land (\exists (\theta : \mathbb{R}), (0 \le \theta) \land (\theta < 1 / 2) \land (\forall (\operatorname{p} : \mathbb{R}), 0 \le \operatorname{p} \to \operatorname{p} \le 1 / 2 \to \theta < \operatorname{p} \to \operatorname{bscOptimal} \operatorname{Cu} \operatorname{Cv} \operatorname{p}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckBSC.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-dos2022c3` (proved) by `D5/S3/Entropy/DoubleSidedBottleneckBSC.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-dos2022c3","declaration_gid":"D5/S3/Entropy/DoubleSidedBottleneckBSC.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The BSC pair attains the finite-channel supremum simultaneously for all crossover probabilities above a threshold depending only on the two rate budgets.

## References

- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.R`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.achievable`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.bsc`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.bscOptimal`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.claim`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.dsbs`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.hbInv`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.mutualInformationBits`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.objective`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.outputJoint`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.rate`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckBSC.result`
- Dependency: [D5/S3/Divergence/ChainRule](../Divergence/ChainRule.md)
- Dependency: [D5/S3/Divergence/ClassicalDPI](../Divergence/ClassicalDPI.md)
- Dependency: [D5/S3/Entropy/DoubleSidedBottleneckMoments](DoubleSidedBottleneckMoments.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformation](MutualInformation.md)
- Dependency: [D5/S3/Entropy/MutualInformationProduct](MutualInformationProduct.md)
- Dependency: [D5/S3/Entropy/MutualInformationSymm](MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction](Observation/ExpectedPosteriorEntropyReduction.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining](RenyiCombining/BinaryRenyiCombining.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity](RenyiCombining/HircheCachinCombiningConcavity.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](Submodularity/MarkovDataProcessing.md)
- Dependency: [D5/S3/Entropy/Submodularity/StrongSubadditivity](Submodularity/StrongSubadditivity.md)
- Dependency: [D5/S3/Observer/ProductMeasures/FinitePmfLikelihood](../Observer/ProductMeasures/FinitePmfLikelihood.md)
- Dependency: [D5/S3/Quantum/CloningMachine](../Quantum/CloningMachine.md)
