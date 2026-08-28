# The Sharp Threshold for Positive Prime Evidence

## Abstract

Prime-indexed positive evidence is summable exactly above exponent one.

**Definition 1.1 (Prime evidence is an inverse power).**

$$e_{s}(p) = p^{{-s}}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real exponent s and a prime p, prime evidence is p raised to minus s. Naming this family keeps the convergence boundary, its specializations, and the degeneration audit tied to one definition.

**Theorem 1.2 (Every prime contributes positive evidence).**

$$\forall s, p, 0 < e_{s}(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime is a positive real base, so its real power is strictly positive for every exponent, including zero and negative exponents.

**Theorem 1.3 (Prime evidence is summable above one).**

$$\forall s, 1 < s \Rightarrow Summable\left(e_{s}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural-number inverse-power series is summable for s greater than one. Restricting that family along the injective prime subtype preserves summability.

**Theorem 1.4 (Inverse-square prime evidence is summable).**

$$Summable\left(e_{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_two_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exponent two lies strictly above the threshold, so the positive family p to the power minus two has a finite sum over all primes.

**Theorem 1.5 (Prime reciprocal evidence diverges).**

$$\neg Summable\left(e_{1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_one_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent one the family is exactly the reciprocal-prime series. Euler's divergence theorem, as provided by pinned mathlib, makes this boundary family nonsummable.

**Theorem 1.6 (Exponent one is the exact summability threshold).**

$$\forall s, Summable\left(e_{s}\right) \Leftrightarrow 1 < s$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_summable_iff_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime power family is summable if and only if its exponent is strictly greater than one. Thus the convergence assumption cannot be weakened merely to positivity of the exponent.

**Theorem 1.7 (Positive prime evidence diverges at and below one).**

$$\forall s, s \le 1 \Rightarrow \left(\forall p, 0 < e_{s}(p) \land \neg Summable\left(e_{s}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_at_most_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s at most one, all prime terms remain strictly positive while the family is nonsummable. This includes s equal to zero and every negative exponent.

**Theorem 1.8 (Zero exponent gives a constant divergent family).**

$$\forall p, e_{0}(p) = 1 \land \neg Summable\left(e_{0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent zero every prime contributes exactly one. The resulting constant family over the infinite prime subtype is nonsummable, making the relevant trivial-map degeneration explicit.

**Theorem 1.9 (The smallest-prime evidence is one quarter).**

$$e_{2}(2) = \frac{1}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_two_at_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent two, the smallest prime contributes two to the power minus two, which is exactly one quarter.

**Theorem 1.10 (A positive exponent does not ensure summability).**

$$\exists s, 0 < s \land \left(\forall p, 0 < e_{s}(p) \land \neg Summable\left(e_{s}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.positive_exponent_is_insufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete exponent s equal to one is positive and every prime term is positive, yet the prime-indexed family diverges. This is the named counterexample showing why the strict threshold is necessary.

**Theorem 1.11 (One family realizes both sides of the sharp threshold).**

$$\forall p, 0 < e_{2}(p) \land \left(Summable\left(e_{2}\right) \land \left(\forall p, 0 < e_{1}(p) \land \neg Summable\left(e_{1}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_sharp_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within the same prime-indexed evidence family, exponent two gives strictly positive summable evidence while exponent one gives strictly positive nonsummable evidence.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.positive_exponent_is_insufficient`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_at_most_one`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_one_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_pos`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_sharp_threshold`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_summable_iff_one_lt`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_two_at_two`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_two_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.primeEvidence_zero`
- Dependency: [D5/S3/Analytic/ZetaGibbs](../ZetaGibbs.md)
