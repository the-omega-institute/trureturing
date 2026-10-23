# Actual Zeta Mass and Height

## Abstract

Actual multiplicity-exact zero mass and unconditional height-ten exclusion from the first xi resolvent at six.

The exact source family is actualData = zetaZeroData, with the real kernel pairWeight rho = Re(1/(rho*(1-rho))), and firstLiMass = 2 + EulerGamma - 2*log(2*sqrt(pi)). The normalized reflection and resolvent-positive R(6) chain uses sixWeight, sixDefect, the digamma-at-3 and H512 reductions, log(pi) and log(2) bounds, the complete von Mangoldt prime-power series, and the tail integral 1/648. The complex HasSum at six is consumed by the real HasSum for sixWeight; the positive kernel estimate and the evaluated defect are then consumed by the height contradiction.

The natural-index enumeration is equivalent to the sigma family of Fin (actualData.multiplicity n) over the exhaustive actual family. ActualZeroOccurrence, its infinite instance, actualOccurrenceEquiv : N ≃ ActualZeroOccurrence, actualZero, the exact fiber identity and fiber cardinality give exact transports of the infinite mass and the finite inclusive cutoffs. The resulting family includes both imaginary signs and every positive analytic multiplicity. The reciprocal-square summability and strict total bound are transported through those fibers. After height ten is proved, the complete inverse-square mass is sharpened to at most (101/100)*firstLiMass. The mathematical count consequence applies that sharper mass to the literal cutoff |Im(actualZero k)| ≤ T and gives ncard ≤ floor(2*T^2) for every T ≥ 10, without a filtered family or RH premise.

**Theorem 1.1 (Complete Height-Derived Inverse Square Mass).**

$$\sum_{k \in \mathbb{N}} \left(\operatorname{im}\left(\operatorname{actualZero}\left(k\right)\right)^{-1}\right)^{2} \le \frac{101}{100} \cdot \mathit{firstLiMass}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum is over every natural occurrence k, with both imaginary signs and each exact analytic multiplicity. For u = Im(rho)^2 > 100, 1/u <= (101/100)/(u+1) <= (101/100)*pairWeight(rho). Multiplication by each multiplicity and comparison of the summable full series give mass <= (101/100)*firstLiMass. The occurrence equivalence transports this bound exactly to the displayed natural-index sum. The two private refined-mass helpers feed this public conclusion. The height theorem is upstream; no height or mass certificate is assumed.

The following literal-cutoff result is a mathematical application, with its complete proof preserved in the exact transient source; it is not a retained declaration or an additional canonical consumer.

$$
\forall T \in \mathbb{R},\; 10 \le T \Rightarrow \operatorname{ncard}\left(\left\{k:\mathbb{N} \mid \left|\operatorname{im}\left(\operatorname{actualZero}\left(k\right)\right)\right| \le T\right\}\right) \le \left\lfloor2 \cdot T^{2}\right\rfloor
$$

For each distinct source zero n, the occurrence fiber is exactly {actualOccurrenceEquiv.symm (n,j) : j in Fin(actualData.multiplicity n)}. Its cardinality is actualData.multiplicity n, and multiplicity_spec identifies this number with the analytic order. The weighted reciprocal-square series is summable; its coarse mass is below 2*firstLiMass < 2. Transport through the natural equivalence gives both the natural-index summability and mass < 2. The distinct indices |Im(zero n)| <= T form a finite set for every real T: the strip bounds its spectral radius by T+1. Taking all finite occurrence fibers and mapping back by the equivalence yields exactly the inclusive natural cutoff, with no change of cutoff or sign restriction. For every real-valued weight w, the finite natural sum equals the sum over these distinct indices of multiplicity(n)*w(zero n). Its cardinality equals the sum of the exact fiber cardinalities. For T >= 10, every cutoff occurrence contributes at least 1/T^2, so count/T^2 <= the full mass <= (101/100)*firstLiMass < 2. Thus count < 2*T^2, and the natural-floor inequality displayed above follows. These statements also have complete proofs in the transient context; no removed handle is asserted here.

**Theorem 1.2 (First Resolvent at Six).**

$$\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow 10 < \left|\operatorname{im}\left(\mathit{rho}\right)\right|$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed telescope binds an arbitrary complex rho and assumes only the actual predicate IsNontrivialZero rho; its conclusion is exactly 10 < |rho.im|. The proof first obtains the endpoint estimate S < 1/3 and the conjugate-pair bootstrap u > 5. The normalized resolvents at 1 and 6, the multiplicity-preserving reflection permutation, and the rational identity produce T6 = 165 * sum_n multiplicity(n) * sixWeight(zero n). The lower kernel is 9/(10*(u+1)*(u+31)); a zero with u ≤ 100 forces T6 ≥ 297/13231. Factorization at six gives T6 = 593/60 + 6*EulerGamma - 11*log(2) - 5*log(pi) + Q6; the H512 estimate, the one-term logarithm lower bound, all von Mangoldt prime powers, and the integrable tail 1/648 give T6 < 329/15000, a strict contradiction. Exhaustivity then transfers 100 < (Im(zero n))^2 to the arbitrary rho. No height, mass, numerical, critical-line, or RH premise is introduced. These numerical reductions bound the same complete analytic quantities: firstLiMass_lt_one proves firstLiMass < 1, excluding real zeros and making conjugate indices distinct; firstLiMass_lt_third proves firstLiMass < 1/3 for the bootstrap u > 5. At the resolvent parameter 6, gamma_upper_r6 proves EulerGamma < 5787/10000, log_pi_lower_r6 proves 11447/10000 < log(pi), and Real.log_two_gt_d9 implies 6931/10000 < log(2). These upper, lower, and lower bounds have the directions required by the coefficients +6, -5, and -11. The gamma bound uses the exact harmonic sum H512 and log(512) = 9*log(2). The bound sixQ_upper proves Q6 < 7/500 for the actual Re(-zeta'(6)/zeta(6)), using its complete von Mangoldt series and every term with n >= 4 in the tail comparison. The bound sixDefect_upper combines these estimates to give T6 < 329/15000 for the same defect. The proof actual_ordinate_sq_gt_hundred consumes this bound with the low-zero lower bound, and actual_height_gt_ten transfers the contradiction to every actual nontrivial zero.

As a transient mathematical application, the seven CompleteZeroFamily fields are supplied by the exact zero, strip, height, reciprocal-square summability, reciprocal-square mass < 2, finite count shell, and count bound above. Soundness follows from zero_isNontrivial; exhaustivity follows by choosing the zero-th element of each positive finite fiber. The same construction over the conjugation index supplies the conjugate occurrence. For every h in Icc 0 2 and every real y, the literal complex spectralKernel equals the sum over n of multiplicity(n)*exp((zero n-h)*y)*resolventCoefficient(zero n,h). Absolute summability of the full natural series permits its exact equivalence and sigma-sum transports; finite fiber summation gives the complex multiplicity. The shell application holds for every m >= 1: shellWeight is summable and shellSum <= 10000*exp(-100*m). For every real m > 0 and every real gamma, lowHIntegrand is integrable on Ioi 1. The original mean bound assumes m >= 1 and gamma > 10. For an actual rho, it sets gamma = |Im rho|, so actual_height_gt_ten supplies gamma > 10. The application of complete_low_h_weighted_mean_bound uses the scalar hypothesis m ≥ 1 and the bound m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)). Here the inner h-domain is the full Icc 0 2 with weight 1+h, whose integral is 4; the Gaussian center is 16*m with variance denominator 4*m; the physical envelope has coefficient 3; and the shell estimate has core coefficient 20, giving 3*4*20 = 240 and the 2400000*exp(-83*m) term. The positive and negative extensions are 2400 and 384*exp(-28*m).

Complete exact proof provenance under /Users/macstudio/omega/research/rh-01a124c9-coordination/signed-source-envelope-20261014/r2559-aggregate-supplier-design-20261017/Robin-height-refined-mass-scoped-native-r4472/: scientific-products/original-r4464/D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.lean (SHA256 bb76e63810f119b6391c3881c44166c7969c9bb460b5a9b9ec162a69485eed04) preserves every original assertion, proof and telescope. The corresponding scientific-products/transient-checks/R4472TransientOriginalBounds.lean uses its unchanged imports and namespace. R4472TransientExactOriginalStatements.lean checks the fifteen original public propositions. The anonymous R4472TransientActualCompleteZeroFamily.lean and R4472TransientActualOriginalFieldConsumer.lean preserve the complete seven-field actual family and both original weighted applications. These files live in the same-owner scientific-products directory, outside canonical D5 sources; they establish no retained consumer. Their complete sources and native evidence are pinned in the accompanying scientific manifest.

The proof uses endpoint normalization, strip and conjugation algebra, occurrence and fiber transports, finite cutoff membership, the real-part HasSum, kernel positivity, and the von Mangoldt tail comparison.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height`
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Zeros/Endpoints/FirstLiCoefficientPositivity](../../Zeros/Endpoints/FirstLiCoefficientPositivity.md)
- Dependency: [D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder](../../Zeros/Resolvent/XiSquareExteriorRemainder.md)
