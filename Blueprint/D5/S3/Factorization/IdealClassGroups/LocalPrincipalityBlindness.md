# Local Principality Is Blind to the Global Ideal Class

## Abstract

Dedekind prime-localization principality is constant and misses a concrete global gap.

**Definition 1.1 (Extend a fractional ideal to a prime localization).**

$$\operatorname{localizedFractionalIdealAtPrime}\left(p, I\right) = \operatorname{ExtendedFractionalIdeal}\left(I, \operatorname{LocalizationAtPrime}\left(R, p\right)\right).$$

*Formalization.* `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localizedFractionalIdealAtPrime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named extension uses Mathlib's fractional-ideal extension homomorphism from the fraction field of the source domain to the fraction field of its localization.

**Definition 1.2 (Read whether an ideal becomes principal at one prime).**

$$\operatorname{localPrincipalityReadout}\left(p, I\right) \iff \operatorname{IsPrincipal}\left(\operatorname{IdealMap}\left(I, \operatorname{LocalizationAtPrime}\left(R, p\right)\right)\right).$$

*Formalization.* `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localPrincipalityReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This named predicate is the integral-ideal face of the local readout. It maps the ideal into the prime localization and asks whether it is principal.

**Theorem 1.3 (A nonzero-prime localization of a Dedekind domain is a DVR).**

$$\operatorname{IsDedekindDomain}\left(R\right) \land \operatorname{IsNonzeroPrime}\left(p\right) \Rightarrow\\{}\operatorname{IsDiscreteValuationRing}\left(\operatorname{LocalizationAtPrime}\left(R, p\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localization_at_nonzero_prime_is_dvr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof invokes Mathlib's exact Dedekind localization theorem. Primality forms the localization, while nonzeroness excludes the fraction-field case.

**Theorem 1.4 (Every fractional ideal in the localized DVR is principal).**

$$\forall I, \operatorname{IsPrincipal}\left(\operatorname{localizedFractionalIdealAtPrime}\left(p, I\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localized_fractional_ideal_is_principal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A DVR inherits Mathlib's principal-ideal-ring structure. The fractional ideal instance proves the result without a nonzero-ideal premise.

**Theorem 1.5 (Every Dedekind local-principality readout equals true).**

$$\forall I, \operatorname{localPrincipalityReadout}\left(p, I\right) \iff True.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_readout_is_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mapped ideal lies in the same localized DVR, so its readout is true for every ideal, including zero and the unit ideal.

**Theorem 1.6 (A nontrivial class group supplies an indistinguishable mixed pair).**

$$\operatorname{IsDedekindDomain}\left(R\right) \land \operatorname{Nontrivial}\left(\operatorname{ClassGroup}\left(R\right)\right) \Rightarrow\\{}\exists I, J, \neg \operatorname{IsPrincipal}\left(I\right) \land \operatorname{IsPrincipal}\left(J\right) \land\\{}(\forall p, \operatorname{localPrincipalityReadout}\left(p, I\right) \iff \operatorname{localPrincipalityReadout}\left(p, J\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_observers_are_blind_of_nontrivial_class_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Surjectivity of the nonzero-ideal class map selects a nonprincipal ideal from a nonidentity class. The unit ideal is principal, while the all-true theorem equates every one of their local readouts.

**Theorem 1.7 (All local readouts identify a principal and a nonprincipal ideal).**

$$\exists I, J,\\{}\neg \operatorname{IsPrincipal}\left(I\right) \land \operatorname{IsPrincipal}\left(J\right) \land\\{}(\forall p, \operatorname{localPrincipalityReadout}\left(p, I\right) \iff \operatorname{localPrincipalityReadout}\left(p, J\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_observers_are_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonprincipal object is the existing norm-two ideal in the minus-five quadratic order; the principal comparison is the unit ideal. The existing local-global theorem supplies every local readout directly.

**Theorem 1.8 (The integer PID has trivial class group and no mixed pair).**

$$\operatorname{ClassGroupCardinality}\left(\mathbb{Z}\right) = 1 \land\\{}\neg \exists I, J, \neg \operatorname{IsPrincipal}\left(I\right) \land \operatorname{IsPrincipal}\left(J\right) \land (\forall p, \operatorname{localPrincipalityReadout}\left(p, I\right) \iff \operatorname{localPrincipalityReadout}\left(p, J\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.pid_blindness_witness_is_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's class-number theorem gives class number one for the integers. Since every integer ideal is principal, the required principal versus nonprincipal pair cannot exist.

**Theorem 1.9 (Localization at the zero prime is not a DVR).**

$$\neg \operatorname{IsDiscreteValuationRing}\left(\operatorname{LocalizationAtPrime}\left(R, 0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.zero_prime_is_not_a_dvr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a domain the zero-prime localization has zero maximal ideal, whereas a DVR has a nonzero maximal ideal. This records why the prime must be nonzero in the DVR theorem.

**Theorem 1.10 (Zero and unit ideals remain principal locally and globally).**

$$\operatorname{IsPrincipal}\left(\operatorname{ZeroIdeal}\left(R\right)\right) \land \operatorname{IsPrincipal}\left(\operatorname{UnitIdeal}\left(R\right)\right) \land\\{}\operatorname{localPrincipalityReadout}\left(p, \operatorname{ZeroIdeal}\left(R\right)\right) \land \operatorname{localPrincipalityReadout}\left(p, \operatorname{UnitIdeal}\left(R\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.zero_and_unit_ideal_readouts_are_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both degenerate ideals are globally principal and receive true local readouts. They therefore cannot supply the strict global witness.

## References

- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localPrincipalityReadout`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_observers_are_blind`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_observers_are_blind_of_nontrivial_class_group`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.local_principality_readout_is_true`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localization_at_nonzero_prime_is_dvr`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localizedFractionalIdealAtPrime`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.localized_fractional_ideal_is_principal`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.pid_blindness_witness_is_impossible`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.zero_and_unit_ideal_readouts_are_true`
- Truth anchor: `D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.zero_prime_is_not_a_dvr`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/NormTwoIdealLocalGlobalGap](../QuadraticIdeals/NormTwoIdealLocalGlobalGap.md)
