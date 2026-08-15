# Green-Class Window Entropy

## Abstract

Independent coordinate laws induce normalized naming-window laws whose Shannon entropy is additive and bounded by naming dimension, with equality for uniform coordinates.

**Definition 1.1 (A window law is the product of its coordinate masses).**

$$\operatorname{windowLaw}(p, u) = \prod_{i} p_{i}(u_{i}).$$

*Formalization.* `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate set, the mass of a window assignment u is the product of the coordinate masses p_i(u_i). The definition imposes no normalization or positivity assumptions.

**Definition 1.2 (A coordinate law is the real singleton mass).**

$$\operatorname{coordLaw}(mu, i, a) = \operatorname{toReal}(mu_{i}\{a\}).$$

*Formalization.* `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.coordLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a family of alphabet measures mu_i, coordLaw reads the singleton mass of a letter as a real number. Probability measures make each finite coordinate law normalized.

**Theorem 1.3 (Normalized coordinate laws give a normalized window law).**

$$\sum_{u} \operatorname{windowLaw}(p, u) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw_sum_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the coordinate product over all finite window assignments factors as the product of the coordinate sums. If every coordinate sum is one, the window sum is one as well.

**Theorem 1.4 (Window entropy is the sum of coordinate entropies).**

$$H(\operatorname{windowLaw}(p)) = \sum_{i} H(p_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative-log product identity expands each assignment's entropy term into one contribution per coordinate. Finite sum-product interchange and coordinate normalization remove every complementary product.

The result is the finite Shannon entropy in nats of the product window law, equal to the sum of the coordinate entropies.

**Theorem 1.5 (Green-class mass is the window law of its pinned content).**

$$\operatorname{toReal}(mu(G(S, t))) = \operatorname{windowLaw}(\operatorname{coordLaw}(mu), {t \mid S}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.greenClass_toReal_eq_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infinite product measure of the green class G(S,t) is the finite product of the pinned singleton masses. Converting those masses to real numbers identifies that product with the corresponding window law.

**Theorem 1.6 (Naming dimension bounds green-class window entropy).**

$$H(\operatorname{windowLaw}(\operatorname{coordLaw}(mu))) \leq n \times \operatorname{namingDim}(O) \times \log{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw_le_namingDim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be the number of pinned coordinates. Entropy additivity reduces the window entropy to n coordinate entropies, and finite-alphabet maximum entropy bounds each summand by log(card O).

The identity log(card O) = namingDim(O) log(2) converts that sum into the stated naming-dimension bound.

**Theorem 1.7 (Uniform coordinate laws attain the naming-dimension bound).**

$$H(\operatorname{windowLaw}(u)) = n \times \operatorname{namingDim}(O) \times \log{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_uniform_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For uniform alphabet measures, every coordinate law has constant mass one over card O and entropy log(card O). Additivity across the pinned coordinates therefore attains the naming-dimension upper bound.

This theorem proves attainment only. The converse statement that equality forces every coordinate law to be uniform requires the Gibbs identity and is deliberately outside this module.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.coordLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.greenClass_toReal_eq_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_uniform_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw_le_namingDim`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw_sum_eq_one`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure](../../../S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](../MaxEntropy.md)
