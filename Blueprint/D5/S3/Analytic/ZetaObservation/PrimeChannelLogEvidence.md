# Prime-Channel Log-Evidence Additivity

## Abstract

Expected zeta log evidence is the summable total of its prime channels.

**Definition 1.1 (One prime channel supplies an expected log-likelihood ratio).**

$$E\left(s, t, p\right) = \sum_{k\in \mathbb{N}} PrimeMass\left(s, p, k\right) \cdot log\left(\frac{PrimeMass\left(s, p, k\right)}{PrimeMass\left(t, p, k\right)}\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source law is the geometric prime-exponent marginal at s. Its expectation of the log likelihood ratio against parameter t is the evidence assigned to that channel.

**Definition 1.2 (Global evidence is the zeta-law expected log-likelihood ratio).**

$$ZetaEvidence\left(s, t\right) = \sum_{n\in \mathbb{N}} ZetaMass\left(s, n\right) \cdot log\left(\frac{ZetaMass\left(s, n\right)}{ZetaMass\left(t, n\right)}\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The global quantity uses the same real-valued log-likelihood expression on the complete zeta distribution.

**Theorem 1.3 (A prime channel has the geometric KL closed form).**

$$E\left(s, t, p\right) = log\left(\frac{1 - p^{{-s}}}{1 - p^{{-t}}}\right) + {t - s} \cdot log\left(p\right) \cdot \frac{p^{{-s}}}{1 - p^{{-s}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the normalized geometric law separates its normalizer ratio from the expected exponent contribution.

**Theorem 1.4 (Global evidence separates into energy and partition terms).**

$$ZetaEvidence\left(s, t\right) = {t - s} \cdot ExpectedLog\left(s\right) + log\left(Z\left(t\right)\right) - log\left(Z\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The global likelihood ratio is affine in log n. Its expectation is therefore an energy difference plus a log-partition difference.

**Theorem 1.5 (Valid zeta parameters make the channel family summable).**

$$\left(1 < s \land 1 < t\right) \Rightarrow Summable\left(p\mapsto E\left(s, t, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.summable_primeChannelLogEvidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime marginal entropy and min-entropy summability isolate a summable prime-energy family. The local closed form then proves absolute summability without an extra hidden premise.

**Theorem 1.6 (Total evidence is the sum of prime-channel evidence).**

$$\left(1 < s \land 1 < t\right) \Rightarrow ZetaEvidence\left(s, t\right) = \sum_{p\in \mathbb{P}} E\left(s, t, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence_eq_tsum_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euler log bridge and prime-energy bridge identify the two global closed-form terms with their summable prime-coordinate series.

**Theorem 1.7 (Equal parameters are indistinguishable).**

$$\forall p, E\left(s, s, p\right) = 0 \land \left(ZetaEvidence\left(s, s\right) = 0 \land \sum_{p\in \mathbb{P}} E\left(s, s, p\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.equal_parameters_have_zero_evidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s equal to t, every likelihood ratio is one. Every channel, the global expectation, and the prime sum are all zero.

**Theorem 1.8 (Every prime channel distinguishes unequal parameters).**

$$\left(\left(1 < s \land 1 < t\right) \land s \ne t\right) \Rightarrow \forall p, 0 < E\left(s, t, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A geometric channel reduces to a two-point mass split. Strict finite Gibbs positivity proves that its expected log evidence is positive whenever the two parameters differ.

**Theorem 1.9 (Two positive channels strictly increase the evidence total).**

$$\left(\left(1 < s \land 1 < t\right) \land s \ne t\right) \Rightarrow \left(0 < E\left(s, t, 2\right) \land \left(0 < E\left(s, t, 3\right) \land \left(E\left(s, t, 2\right) < E\left(s, t, 2\right) + E\left(s, t, 3\right) \land E\left(s, t, 3\right) < E\left(s, t, 2\right) + E\left(s, t, 3\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.two_three_channels_strictly_accumulate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the distinct prime channels two and three, both contributions are positive, so their sum is strictly larger than either one.

**Theorem 1.10 (Disequality is necessary for strict evidence).**

$$\neg 0 < E\left(2, 2, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.parameter_disequality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete diagonal choice s equals t equals two has zero evidence at prime two, ruling out strict positivity without disequality.

**Theorem 1.11 (A divergent bare tsum is totalized to zero).**

$$\neg Summable\left(p\mapsto \frac{1}{p}\right) \land \sum_{p\in \mathbb{P}} \frac{1}{p} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.nonsummable_prime_family_totalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive reciprocal-prime family is not summable, while its bare real tsum is zero by totalization. This contrast explains why the main theorem first proves summability.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.equal_parameters_have_zero_evidence`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.nonsummable_prime_family_totalized`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.parameter_disequality_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence_eq`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.primeChannelLogEvidence_pos`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.summable_primeChannelLogEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.two_three_channels_strictly_accumulate`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence_eq`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.zetaFamilyLogEvidence_eq_tsum_prime`
- Dependency: [D5/S3/Divergence/StrictGibbs](../../Divergence/StrictGibbs.md)
