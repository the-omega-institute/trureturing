# Local Evidence Order Determines the Critical Exponent

## Abstract

Linear event mass and quadratic evidence have distinct prime thresholds.

本节不声称 α=1/2 与 Riemann 临界线具有解析等价、零点等价或物理因果关系。这里只存在「二次证据导致指数折半」的结构类比。

**Definition 1.1 (First-event mass).**

$$m(s)(p) = p^{{-s}}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named mass is the local probability formula p to the power minus s. A separate theorem checks its event-probability semantics.

**Definition 1.2 (Quadratic statistical energy).**

$$E(delta)(i) = delta_{i} \cdot delta_{i}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadraticStatisticalEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any index type, the energy at one coordinate is the square of its local deviation. No prime structure enters this definition.

**Theorem 1.3 (First-event mass is the zeta activation probability).**

$$P_{s}(V_{p} > 0) = m(s)(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_eq_activation_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above exponent one, the normalized zeta law exists. Its event that the p-adic exponent is positive has exactly the named first-event mass.

**Theorem 1.4 (First-event mass has threshold one).**

$$\forall s, Summable\left(m(s)\right) \Leftrightarrow 1 < s$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_summable_iff_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-indexed activation masses are summable exactly when s is strictly greater than one. Prime distribution is load-bearing.

**Theorem 1.5 (Quadratic energy doubles the exponent).**

$$E(m(alpha)) = m(2 \cdot alpha)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_eq_firstEventMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the deviation p to the power minus alpha, squaring changes the same prime family to exponent two alpha.

**Theorem 1.6 (Quadratic energy has threshold one half).**

$$\forall alpha, Summable\left(E(m(alpha))\right) \Leftrightarrow \frac{1}{2} < alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_summable_iff_half_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The doubled exponent is above one exactly when alpha is above one half. The exact iff still uses the prime-series theorem.

**Theorem 1.7 (Accumulated order determines the critical exponent).**

$${\forall s, Summable\left(m(s)\right) \Leftrightarrow 1 < s} \land \left({\forall alpha, Summable\left(E(m(alpha))\right) \Leftrightarrow \frac{1}{2} < alpha} \land 1 \ne \frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.local_evidence_order_critical_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same prime spectrum gives threshold one for linear activation mass and one half for quadratic evidence. The thresholds are unequal.

**Theorem 1.8 (First-event mass diverges at and below one).**

$$\forall s, s \le 1 \Rightarrow \neg Summable\left(m(s)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_at_most_one_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every exponent at most one lies on the nonsummable side, including the boundary itself and all nonpositive exponents.

**Theorem 1.9 (Zero exponent is constant and divergent).**

$$\forall p, m(0)(p) = 1 \land \neg Summable\left(m(0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent zero every prime contributes one, so the infinite prime family is not summable.

**Theorem 1.10 (Zero deviation has summable energy).**

$$Summable\left(E(0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadraticStatisticalEnergy_zero_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every index type, the zero deviation has identically zero quadratic energy and is summable.

**Theorem 1.11 (Finite prime truncations are summable).**

$$\forall S, s, Summable\left(m(s) chi_{S}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.finite_prime_truncation_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting to finitely many primes is summable at every exponent. This degeneration uses finite support, not prime distribution.

**Theorem 1.12 (Empty and singleton energy families are summable).**

$${\forall delta: \emptyset \to \mathbb{R}, Summable\left(E(delta)\right)} \land {\forall delta: Unit \to \mathbb{R}, Summable\left(E(delta)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_energy_empty_and_unit_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every family on the empty type or the one-element unit type has finite support, so its quadratic energy is summable.

**Theorem 1.13 (The one-half boundary diverges).**

$$\neg Summable\left(E(m(\frac{1}{2}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_one_half_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha equal to one half, quadratic energy becomes reciprocal-prime mass, so the boundary itself is not summable.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.finite_prime_truncation_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_at_most_one_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_eq_activation_probability`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_summable_iff_one_lt`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.firstEventMass_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.local_evidence_order_critical_thresholds`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadraticStatisticalEnergy`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadraticStatisticalEnergy_zero_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_energy_empty_and_unit_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_eq_firstEventMass`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_one_half_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.quadratic_prime_energy_summable_iff_half_lt`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](PrimeEvidenceSharpThreshold.md)
