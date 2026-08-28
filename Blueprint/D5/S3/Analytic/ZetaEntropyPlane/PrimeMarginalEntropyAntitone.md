# Prime Marginal Entropy Antitonicity

## Abstract

Larger primes carry strictly less complete exponent entropy at fixed temperature.

**Definition 1.1 (Geometric entropy as a ratio function).**

Lean statement: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom`

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named function hGeom is minus log of one minus the ratio, minus the ratio odds multiplied by the log ratio. Naming it exposes the definition independently of the later monotonicity theorem.

**Theorem 1.2 (The totalized endpoint values are both zero).**

$$hGeom\left(0\right) = 0 \land hGeom\left(1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_endpoint_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean's real logarithm and division are totalized. Direct substitution therefore gives hGeom value zero at both ratio zero and ratio one, even though the left limit at one is unbounded.

**Theorem 1.3 (Geometric entropy strictly increases inside the unit interval).**

$$StrictMonoOn\left(hGeom, Ioo\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On ratios strictly between zero and one, differentiation gives minus log of the ratio divided by the square of one minus the ratio. The logarithm is negative there, so the derivative is positive.

**Theorem 1.4 (The lower endpoint may be included).**

$$StrictMonoOn\left(hGeom, Ico\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_strictMonoOn_Ico` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict increase extends to the half-open interval containing zero. The endpoint value is zero, while every interior geometric entropy is strictly positive.

**Theorem 1.5 (The upper endpoint must remain excluded).**

$$\neg StrictMonoOn\left(hGeom, Ioc\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.upper_endpoint_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Including ratio one contradicts strict increase under totalization: the interior ratio one half has positive entropy, whereas hGeom at one is zero. This is a concrete named endpoint counterexample.

**Theorem 1.6 (A positive negative-power exponent reverses prime order).**

$$\forall s \in \mathbb{R}, p \in \operatorname{Primes}, r \in \operatorname{Primes},\; \left(0 < s \land p < r\right) \Rightarrow r^{-s} < p^{-s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.prime_rpow_lt_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive real exponent, a strict increase in prime value gives a strict decrease in its negative real power. This step needs only positivity of the exponent, not the stronger convergence bound.

**Theorem 1.7 (Exponent positivity is necessary).**

$$2 < 3 \land \left(\neg 3^{-0} < 2^{-0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.positive_exponent_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent zero, the ordered primes two and three both have weight one. Their strict negative-power comparison therefore fails, furnishing the required concrete counterexample.

**Theorem 1.8 (The two-three weight order remains strict at exponent one).**

$$3^{-1} < 2^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.two_three_rpow_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the smallest ordered prime pair, three to the power minus one is strictly smaller than two to the power minus one. Thus the power comparison itself does not require inverse temperature above one.

**Theorem 1.9 (Prime-exponent entropy is hGeom at the prime ratio).**

$$\forall s \in \mathbb{R}, p \in \operatorname{Primes},\; 1 < s \Rightarrow countableEntropy\left(primeExponentPMF\left(s, p\right)\right) = hGeom\left(p^{-s}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.primeExponent_entropy_eq_hGeom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing closed form for the complete prime-exponent marginal is rewritten exactly as hGeom evaluated at the prime to the power minus the inverse temperature. No entropy sum is reproved here.

**Theorem 1.10 (Complete exponent entropy strictly decreases with the prime).**

$$\forall s \in \mathbb{R}, p \in \operatorname{Primes}, r \in \operatorname{Primes},\; \left(1 < s \land p < r\right) \Rightarrow countableEntropy\left(primeExponentPMF\left(s, r\right)\right) < countableEntropy\left(primeExponentPMF\left(s, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.primeExponent_entropy_strictAntitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above inverse temperature one, ordered primes give oppositely ordered ratios inside the open unit interval. Strict increase of hGeom then makes the larger prime's complete exponent entropy smaller.

**Theorem 1.11 (Strict prime order is necessary).**

$$\left(\neg 2^{-2} < 2^{-2}\right) \land \left(\neg countableEntropy\left(primeExponentPMF\left(2, 2\right)\right) < countableEntropy\left(primeExponentPMF\left(2, 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.strict_prime_order_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Using prime two on both sides makes both the negative-power comparison and the corresponding entropy comparison irreflexive. This concrete case records why a strict prime-value hypothesis is required.

**Theorem 1.12 (Prime three has less exponent entropy than prime two).**

$$\forall s \in \mathbb{R},\; 1 < s \Rightarrow countableEntropy\left(primeExponentPMF\left(s, 3\right)\right) < countableEntropy\left(primeExponentPMF\left(s, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.two_three_entropy_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible inverse temperature, the complete exponent marginal at prime three has strictly smaller countable entropy than the one at prime two. This instantiates the result at the smallest prime pair.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_endpoint_values`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_strictMonoOn`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.hGeom_strictMonoOn_Ico`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.positive_exponent_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.primeExponent_entropy_eq_hGeom`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.primeExponent_entropy_strictAntitone`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.prime_rpow_lt_of_lt`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.strict_prime_order_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.two_three_entropy_strict`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.two_three_rpow_at_one`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.upper_endpoint_is_necessary`
