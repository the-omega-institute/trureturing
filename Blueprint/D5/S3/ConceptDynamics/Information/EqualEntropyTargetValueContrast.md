# Equal Entropy, Different Target Value

## Abstract

Equal information quantity can carry opposite target value.

**Theorem 1.1 (Equal entropy and compression do not imply equal target sufficiency).**

$$\begin{gathered}X = Bool \times Bool, mu(x) = \frac{1}{4},\\{}C_{1}(x) = \operatorname{fst}\left(x\right), C_{2}(x) = \operatorname{snd}\left(x\right), T(x) = \operatorname{fst}\left(x\right):\\{}\operatorname{shannonEntropy}\left(\operatorname{conceptLaw}\left(mu, C_{1}\right)\right) = \operatorname{log}\left(2\right) \land\\{}\operatorname{shannonEntropy}\left(\operatorname{conceptLaw}\left(mu, C_{2}\right)\right) = \operatorname{log}\left(2\right) \land\\{}\operatorname{ncard}\left(\operatorname{range}\left(C_{1}\right)\right) = 2 \land \operatorname{ncard}\left(\operatorname{range}\left(C_{2}\right)\right) = 2 \land\\{}\frac{\operatorname{ncard}\left(\operatorname{range}\left(C_{1}\right)\right)}{\operatorname{card}\left(X\right)} = \frac{1}{2} \land \frac{\operatorname{ncard}\left(\operatorname{range}\left(C_{2}\right)\right)}{\operatorname{card}\left(X\right)} = \frac{1}{2} \land\\{}\operatorname{targetResidualEntropy}\left(mu, C_{1}, T\right) = 0 \land\\{}\operatorname{targetResidualEntropy}\left(mu, C_{2}, T\right) = \operatorname{log}\left(2\right) \land\\{}\operatorname{Refines}\left(T, C_{1}\right) \land \neg \operatorname{Refines}\left(T, C_{2}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast.equal_entropy_target_value_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state is a uniformly distributed pair of Boolean coordinates. The two concepts report the first and second coordinates, while the target is the first coordinate.

Both canonical pushforward laws have entropy log two. Both readouts attain two labels out of four source states, so their displayed label counts and output-to-input cardinality ratios agree.

The conditional target entropy is zero after the first readout and log two after the second. The final two public conjuncts state the same contrast structurally: the target factors through the first readout but not the second.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast.equal_entropy_target_value_contrast`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../Communication/TranslationLossMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity](RefinementEntropyMonotonicity.md)
