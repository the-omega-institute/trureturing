# DoubleSidedBottleneckMoments

## Abstract

Exact binary symmetric channel optimality near independent binary sources.

**Definition 1.1 (phi).**

$$\forall (\operatorname{x} : \mathbb{R}), (\operatorname{phi} \operatorname{x} = (\operatorname{Real} . \operatorname{log} 2 - \operatorname{Real} . \operatorname{binEntropy} ((1 + \operatorname{Real} . \operatorname{sqrt} \operatorname{x}) / 2)))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines phi.

**Theorem 1.2 (phi convex).**

$$\operatorname{ConvexOn} \mathbb{R} (\operatorname{Icc} (0 : \mathbb{R}) 1) \operatorname{phi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

**Theorem 1.3 (phi strictMono).**

$$\operatorname{StrictMonoOn} \operatorname{phi} (\operatorname{Icc} (0 : \mathbb{R}) 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

**Definition 1.4 (slope).**

$$\forall (\operatorname{m} : \mathbb{R}), (\operatorname{slope} \operatorname{m} = (\operatorname{D5} . \operatorname{S3} . \operatorname{Quantum} . \operatorname{Information} . \operatorname{QubitEntropyContraction} . \operatorname{logRatio} (\operatorname{Real} . \operatorname{sqrt} \operatorname{m}) / (4 \cdot \operatorname{Real} . \operatorname{sqrt} \operatorname{m})))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckMoments.slope` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines slope.

**Theorem 1.5 (slope nonneg).**

$$\forall (\operatorname{m} : \mathbb{R}), ((\operatorname{m} \in \operatorname{Ioo} (0 : \mathbb{R}) 1) \implies (0 \le \operatorname{slope} \operatorname{m}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.slope_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

**Theorem 1.6 (avg sub).**

$$\forall (\operatorname{A} : \operatorname{Type} *), ([\operatorname{Fintype} \operatorname{A}] \forall (\operatorname{p} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{f} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{g} : \operatorname{A} \to \mathbb{R}), (\operatorname{dotProduct} \operatorname{p} (\operatorname{fun} \operatorname{i} \mapsto \operatorname{f} \operatorname{i} - \operatorname{g} \operatorname{i}) = \operatorname{dotProduct} \operatorname{p} \operatorname{f} - \operatorname{dotProduct} \operatorname{p} \operatorname{g}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.avg_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

**Theorem 1.7 (avg const).**

$$\forall (\operatorname{A} : \operatorname{Type} *), ([\operatorname{Fintype} \operatorname{A}] \forall (\operatorname{p} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{c} : \mathbb{R}), ((\sum \operatorname{i} , \operatorname{p} \operatorname{i} = 1) \implies (\operatorname{dotProduct} \operatorname{p} (\operatorname{Function} . \operatorname{const} \operatorname{A} \operatorname{c}) = \operatorname{c}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.avg_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

**Definition 1.8 (half).**

$$\forall (\operatorname{i} : \operatorname{Bool}) , \operatorname{half} \operatorname{i} = 1 / 2$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckMoments.half` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines half.

**Definition 1.9 (signed).**

$$\forall (\operatorname{a} : \mathbb{R}) , \operatorname{signed} \operatorname{a} = \operatorname{fun} (\operatorname{i} : \operatorname{Bool}) \mapsto \operatorname{if} \operatorname{i} \operatorname{then} \operatorname{a} \operatorname{else} - \operatorname{a}$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckMoments.signed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines signed.

**Definition 1.10 (productValue).**

$$\forall (\operatorname{A} : \operatorname{Type} *), (\forall (\operatorname{B} : \operatorname{Type} *), ([\operatorname{Fintype} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] \forall (\delta : \mathbb{R}), (\forall (\operatorname{p} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{s} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{q} : \operatorname{B} \to \mathbb{R}), (\forall (\operatorname{t} : \operatorname{B} \to \mathbb{R}), (\operatorname{productValue} \delta \operatorname{p} \operatorname{s} \operatorname{q} \operatorname{t} = (\sum \operatorname{i} , \sum \operatorname{j} , \operatorname{p} \operatorname{i} \cdot \operatorname{q} \operatorname{j} \cdot (- \operatorname{Real} . \operatorname{negMulLog} (1 + \delta \cdot \operatorname{s} \operatorname{i} \cdot \operatorname{t} \operatorname{j}))))))))))$$

*Formalization.* `D5/S3/Entropy/DoubleSidedBottleneckMoments.productValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed equality defines productValue.

**Theorem 1.11 (posterior local optimality).**

$$\forall (\operatorname{A} : \operatorname{Type} *), (\forall (\operatorname{B} : \operatorname{Type} *), ([\operatorname{Fintype} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] \forall (\operatorname{p} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{s} : \operatorname{A} \to \mathbb{R}), (\forall (\operatorname{q} : \operatorname{B} \to \mathbb{R}), (\forall (\operatorname{t} : \operatorname{B} \to \mathbb{R}), ((\forall \operatorname{i} , 0 \le \operatorname{p} \operatorname{i}) \implies ((\sum \operatorname{i} , \operatorname{p} \operatorname{i} = 1) \implies ((\forall \operatorname{j} , 0 \le \operatorname{q} \operatorname{j}) \implies ((\sum \operatorname{j} , \operatorname{q} \operatorname{j} = 1) \implies ((\forall \operatorname{i} , | \operatorname{s} \operatorname{i} | \le 1) \implies ((\forall \operatorname{j} , | \operatorname{t} \operatorname{j} | \le 1) \implies ((\operatorname{dotProduct} \operatorname{p} \operatorname{s} = 0) \implies ((\operatorname{dotProduct} \operatorname{q} \operatorname{t} = 0) \implies (\forall (\operatorname{a} : \mathbb{R}), (\forall (\operatorname{b} : \mathbb{R}), ((\operatorname{a} ^{2} \in \operatorname{Set} . \operatorname{Ioo} (0 : \mathbb{R}) 1) \implies ((\operatorname{b} ^{2} \in \operatorname{Set} . \operatorname{Ioo} (0 : \mathbb{R}) 1) \implies ((\operatorname{dotProduct} \operatorname{p} (\operatorname{fun} \operatorname{i} \mapsto \operatorname{phi} (\operatorname{s} \operatorname{i} ^{2})) \le \operatorname{phi} (\operatorname{a} ^{2})) \implies ((\operatorname{dotProduct} \operatorname{q} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{phi} (\operatorname{t} \operatorname{j} ^{2})) \le \operatorname{phi} (\operatorname{b} ^{2})) \implies (\forall (\delta : \mathbb{R}), ((0 \le \delta) \implies ((\delta < 1) \implies ((\delta \le 1 / (1 + 6 \cdot \operatorname{max} (\operatorname{Curvature} . \operatorname{slope} (\operatorname{a} ^{2})) (\operatorname{Curvature} . \operatorname{slope} (\operatorname{b} ^{2})))) \implies (\operatorname{productValue} \delta \operatorname{p} \operatorname{s} \operatorname{q} \operatorname{t} \le \operatorname{productValue} \delta \operatorname{half} (\operatorname{signed} \operatorname{a}) \operatorname{half} (\operatorname{signed} \operatorname{b})))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DoubleSidedBottleneckMoments.posterior_local_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Dikshtein, Or Ordentlich, Shlomo Shamai (Shitz) (2022). *The Double-Sided Information Bottleneck Function*. DOI: [10.3390/e24091321](https://doi.org/10.3390/e24091321). URL: <https://doi.org/10.3390/e24091321>.

*Commentary.*

The displayed estimate holds for every indicated parameter, including zero weights and both signs of each posterior bias.

## References

- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.avg_const`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.avg_sub`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.half`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi_convex`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.phi_strictMono`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.posterior_local_optimality`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.productValue`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.signed`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.slope`
- Truth anchor: `D5/S3/Entropy/DoubleSidedBottleneckMoments.slope_nonneg`
- Dependency: [D5/S3/Quantum/Information/QubitEntropyContraction](../Quantum/Information/QubitEntropyContraction.md)
