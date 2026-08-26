# Formal Factor Tables Are Not Analytic Functions

## Abstract

Formal local-factor data alone supplies neither convergence, a nonzero limit, nor locally uniform convergence; an explicit summability admission does.

**Theorem 1.1 (The constant-two table is not multipliable).**

$$\neg\operatorname{Multipliable}(\operatorname{constantFactorTable}(2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.constant_two_not_multipliable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite products are powers of two. Their values tend to infinity as the finite index set grows, so they cannot converge to a real number.

**Theorem 1.2 (The constant-half table has product zero).**

$$\operatorname{HasProd}(\operatorname{constantFactorTable}(\frac{1}{2}), 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.constant_half_hasProd_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite products are powers of one half. Cardinality tends to infinity, so the unconditional finite-set net converges to zero.

**Theorem 1.3 (The power family converges pointwise on its exact elementary domain).**

$$\forall x\in \mathbb{R}, \lvert x\rvert < 1 \lor x = 1 \Rightarrow \operatorname{HasProd}(n\mapsto \operatorname{parameterFactorTable}(n, x), \operatorname{endpointProductLimit}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.parameter_factor_hasProd_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior parameter the products are contracting powers and tend to zero. At one every finite product is one.

**Theorem 1.4 (The pointwise domain condition cannot be dropped).**

$$\neg\operatorname{HasProd}(n\mapsto \operatorname{parameterFactorTable}(n, 2), \operatorname{endpointProductLimit}(2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.pointwise_domain_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter two every factor is two, so the finite products diverge instead of having the claimed endpoint product.

**Theorem 1.5 (The pointwise power product is not locally uniform).**

$$\neg\operatorname{HasProdLocallyUniformlyOn}(parameterFactorTable, endpointProductLimit, \operatorname{Icc}(0, 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.parameter_factor_not_locally_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite product is continuous, while the pointwise limit jumps at one on the closed unit interval. A locally uniform limit would be continuous there.

**Theorem 1.6 (Summable deviations provide an actual product).**

$$\forall f, \operatorname{AbsoluteConvergenceAdmission}(f) \Rightarrow \operatorname{Multipliable}(f).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.absolute_convergence_admission_gives_multipliable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib turns absolute summability of the deviations from one into multipliability of the corresponding one-plus-deviation factors.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.absolute_convergence_admission_gives_multipliable`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.constant_half_hasProd_zero`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.constant_two_not_multipliable`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.parameter_factor_hasProd_pointwise`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.parameter_factor_not_locally_uniform`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples.pointwise_domain_hypothesis_is_necessary`
