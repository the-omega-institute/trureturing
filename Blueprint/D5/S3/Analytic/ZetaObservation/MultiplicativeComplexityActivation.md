# Multiplicative Complexity as a Random Activation Pattern

## Abstract

Multiplicative complexity is a finite sum of independent prime occupations.

**Definition 1.1 (Multiplicative complexity counts prime factors with multiplicity).**

$$C_{\times}(n) = \omega(n)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicativeComplexity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The FPOD complexity of n is Mathlib's existing Omega arithmetic function. The wrapper names the source concept without creating a second prime-factor-count definition.

**Definition 1.2 (A prime mode is occupied by its factorization exponent).**

$$V_{p}(n) = v_{p}(n)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.primeOccupancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime p, its occupation coordinate at n is the exponent of p in the finite prime factorization of n.

**Theorem 1.3 (Complexity is the sum of prime occupations).**

$$C_{\times}(n) = \sum_{p\in \mathbb{P}} V_{p}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicativeComplexity_eq_factorization_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact Mathlib decomposition of Omega is reused. Its Finsupp sum is over factorization support, so each fixed integer contributes only finitely many nonzero prime exponents.

**Theorem 1.4 (Only finitely many prime modes are occupied).**

$$\operatorname{Finite}\left(\operatorname{OccupiedPrimeModes}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.occupied_prime_modes_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero prime occupations form the preimage of the finite Finsupp support under the injective prime coercion.

**Theorem 1.5 (Zero, one, primes, and prime powers are explicit).**

$$C_{\times}(0) = 0 \land \left(C_{\times}(1) = 0 \land \left(C_{\times}(p) = 1 \land C_{\times}(p^{{k}}) = k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicative_complexity_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totalized convention gives complexity zero to both zero and one. A prime has complexity one, and its kth power has complexity k, including k equal to zero.

**Theorem 1.6 (The prime restriction cannot be deleted).**

$$\neg C_{\times}(1) = 1 \land \neg C_{\times}(1^{{2}}) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.primality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete nonprime base one has complexity zero rather than one, and its square has complexity zero rather than two. This names the counterexample required by the hypothesis audit.

**Theorem 1.7 (Each prime occupation is geometric).**

$$\operatorname{ProbabilityUnderZeta}\left(s, V_{p}(N) = k\right) = {1 - p^{{-s}}} \cdot p^{{-s \cdot k}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancy_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above exponent one, the probability that the p-coordinate equals k is one minus p to the minus s, times p to the minus sk. This is a direct application of the existing prime-exponent law.

**Theorem 1.8 (All prime occupations are mutually independent).**

$$1 < s \Rightarrow \operatorname{MutuallyIndependentUnderZeta}\left(s, \operatorname{PrimeOccupationFamily}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancies_mutually_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full prime-indexed iIndepFun theorem is reused, so every finite subfamily factors, including the empty family and singletons. This is stronger than pairwise independence.

**Theorem 1.9 (A prime coordinate is nonconstant and nontrivial).**

$$V_{p}(0) = 0 \land \left(V_{p}(1) = 0 \land V_{p}(p) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancy_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero and one the coordinate vanishes, while at its own prime it equals one. These values rule out the constant, identity, and zero-map degenerations for the actual coordinate family.

**Definition 1.10 (The geometric mean occupation has a closed form).**

$$m_{p}(s) = \frac{p^{{-s}}}{1 - p^{{-s}}}$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.meanPrimeOccupancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local geometric mean is q divided by one minus q, with q equal to p to the minus s. Its probabilistic reading is restricted to the zeta range above one.

**Theorem 1.11 (Mean occupations are summable above one).**

$$1 < s \Rightarrow Summable\left(p\mapsto m_{p}(s)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.mean_prime_occupancies_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime evidence q is at most one half, so q divided by one minus q is at most twice q. The existing sharp prime-evidence theorem then proves summability.

**Theorem 1.12 (Exponent one is a nonsummable counterexample).**

$$\neg Summable\left(p\mapsto m_{p}(1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.threshold_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent one, each mean occupation dominates reciprocal-prime evidence, so the family is not summable.

This is stated with Summable rather than a bare real tsum: the repository's totalized tsum is zero for nonsummable families.

The warning that physical computation costs need not obey this law is interpretive, not a mathematical assertion. FPOD 136.1 instead adds log evidence; it does not imply these occupation results.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.meanPrimeOccupancy`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.mean_prime_occupancies_summable`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicativeComplexity`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicativeComplexity_eq_factorization_sum`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.multiplicative_complexity_degenerate_audit`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.occupied_prime_modes_finite`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.primality_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.primeOccupancy`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancies_mutually_independent`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancy_degenerate_audit`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.prime_occupancy_geometric`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.threshold_hypothesis_is_necessary`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](../ZetaEntropyPlane/PrimeEvidenceSharpThreshold.md)
