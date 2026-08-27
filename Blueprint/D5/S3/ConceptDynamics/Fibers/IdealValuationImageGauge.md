# Ideal Valuation Faithfulness, Image, and Gauge

## Abstract

Integer ideals separate faithfulness, image support, and generator gauge.

**Theorem 1.1 (Prime-ideal valuations faithfully determine integer ideals).**

$$\operatorname{Injective}(vZ).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.int_ideal_valuation_readout_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout assigns the zero ideal top at every prime and assigns each nonzero ideal the prime exponents of its nonnegative canonical generator.

Equality of the prime coordinates recovers the generator by unique factorization and then the ideal. This is a concrete theorem over the integers, not a general Dedekind-domain claim.

**Theorem 1.2 (An infinite-support exponent family is not realizable).**

$$\neg(oneAtEveryPrime \in \operatorname{range}(vZ)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.infinite_support_family_not_in_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-one family is nonzero at every prime. For any nonzero integer ideal, a prime larger than its norm has exponent zero; the zero ideal instead has the constant-top readout.

Thus even in the PID of integers the valuation image is not the full product. CompatibleResidueJointImage concerns the different map from integers to two residue rings and is not reused here.

**Theorem 1.3 (A principal ideal retains unit gauge).**

$$2 \neq -2 \land \operatorname{span}(2) = \operatorname{span}(-2) \land\\{}\exists u \in ZUnits, -2 = u \cdot 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.two_generators_unit_gauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinct integers 2 and -2 generate the same ideal, and the unit -1 carries one generator to the other. Principality therefore does not select a canonical signed generator.

The degenerate audit also identifies the zero ideal's sole generator, the unit ideal's two generators, and the two generators of every integer prime ideal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.infinite_support_family_not_in_image`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.int_ideal_valuation_readout_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.two_generators_unit_gauge`
