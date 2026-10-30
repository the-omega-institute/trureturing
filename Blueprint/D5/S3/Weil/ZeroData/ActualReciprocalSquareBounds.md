# Actual Zeta Mass and Height

## Abstract

Actual multiplicity-exact zero mass and unconditional height-ten exclusion from the first xi resolvent at six.

The exact source family is actualData = zetaZeroData, with the real kernel pairWeight rho = Re(1/(rho*(1-rho))), and firstLiMass = 2 + EulerGamma - 2*log(2*sqrt(pi)). The normalized reflection and resolvent-positive R(6) chain uses sixWeight, sixDefect, the digamma-at-3 and H512 reductions, log(pi) and log(2) bounds, the complete von Mangoldt prime-power series, and the tail integral 1/648. The complex HasSum at six is consumed by the real HasSum for sixWeight; the positive kernel estimate and the evaluated defect are then consumed by the height contradiction.

The natural-index enumeration is equivalent to the sigma family of Fin (actualData.multiplicity n) over the exhaustive actual family. ActualZeroOccurrence, its infinite instance, actualOccurrenceEquiv : N ≃ ActualZeroOccurrence, actualZero, the exact fiber identity and fiber cardinality give exact transports of the infinite mass and the finite inclusive cutoffs. The resulting family includes both imaginary signs and every positive analytic multiplicity. The reciprocal-square summability and strict total bound are transported through those fibers. After height ten is proved, the complete inverse-square mass is sharpened to at most (101/100)*firstLiMass. The mathematical count consequence applies that sharper mass to the literal cutoff |Im(actualZero k)| ≤ T and gives ncard ≤ floor(2*T^2) for every T ≥ 10, without a filtered family or RH premise.

**Theorem 1.1 (Complete Complex First Li Mass).**

Lean statement: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_complex_pairWeight_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_complex_pairWeight_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized xi resolvent gives the multiplicity-weighted complex first Li mass. Taking real parts yields the real pair-weight mass; transporting the complex sum to every analytic occurrence supplies the complete integrated series.

**Theorem 1.2 (First Li Mass Normalization).**

Lean statement: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_split`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first Li mass equals 2 plus the Euler constant minus twice log 2 minus log pi. This normalization supplies the height estimates and the scalar cancellation in the integrated explicit formula.

**Theorem 1.3 (Xi Logarithmic Derivative at Zero).**

Lean statement: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.zero_endpoint_logDeriv`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.zero_endpoint_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic derivative of xi at zero is minus half the first Li mass. Reflection gives the endpoint at one, and the zero endpoint normalizes the complete resolvent.

**Theorem 1.4 (Complete Height-Derived Inverse Square Mass).**

$$\sum_{k \in \mathbb{N}} \left(\operatorname{im}\left(\operatorname{actualZero}\left(k\right)\right)^{-1}\right)^{2} \le \frac{101}{100} \cdot \mathit{firstLiMass}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum is over every natural occurrence k, with both imaginary signs and each exact analytic multiplicity. For u = Im(rho)^2 > 100, 1/u <= (101/100)/(u+1) <= (101/100)*pairWeight(rho). Multiplication by each multiplicity and comparison of the summable full series give mass <= (101/100)*firstLiMass. The occurrence equivalence transports this bound exactly to the displayed natural-index sum. The two private refined-mass helpers feed this public conclusion. The height theorem is upstream; no height or mass certificate is assumed.

The complete height-derived mass bound gives the following literal-cutoff consequence.

$$
\forall T \in \mathbb{R},\; 10 \le T \Rightarrow \operatorname{ncard}\left(\left\{k:\mathbb{N} \mid \left|\operatorname{im}\left(\operatorname{actualZero}\left(k\right)\right)\right| \le T\right\}\right) \le \left\lfloor2 \cdot T^{2}\right\rfloor
$$

For each distinct source zero n, the occurrence fiber is exactly {actualOccurrenceEquiv.symm (n,j) : j in Fin(actualData.multiplicity n)}. Its cardinality is actualData.multiplicity n, and multiplicity_spec identifies this number with the analytic order. The weighted reciprocal-square series is summable; its coarse mass is below 2*firstLiMass < 2. Transport through the natural equivalence gives both the natural-index summability and mass < 2. The distinct indices |Im(zero n)| <= T form a finite set for every real T: the strip bounds its spectral radius by T+1. Taking all finite occurrence fibers and mapping back by the equivalence yields exactly the inclusive natural cutoff, with no change of cutoff or sign restriction. For every real-valued weight w, the finite natural sum equals the sum over these distinct indices of multiplicity(n)*w(zero n). Its cardinality equals the sum of the exact fiber cardinalities. For T >= 10, every cutoff occurrence contributes at least 1/T^2, so count/T^2 <= the full mass <= (101/100)*firstLiMass < 2. Thus count < 2*T^2, and the natural-floor inequality displayed above follows.

**Theorem 1.5 (First Resolvent at Six).**

$$\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow 10 < \left|\operatorname{im}\left(\mathit{rho}\right)\right|$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed telescope binds an arbitrary complex rho and assumes only the actual predicate IsNontrivialZero rho; its conclusion is exactly 10 < |rho.im|. The proof first obtains the endpoint estimate S < 1/3 and the conjugate-pair bootstrap u > 5. The normalized resolvents at 1 and 6, the multiplicity-preserving reflection permutation, and the rational identity produce T6 = 165 * sum_n multiplicity(n) * sixWeight(zero n). The lower kernel is 9/(10*(u+1)*(u+31)); a zero with u ≤ 100 forces T6 ≥ 297/13231. Factorization at six gives T6 = 593/60 + 6*EulerGamma - 11*log(2) - 5*log(pi) + Q6; the H512 estimate, the one-term logarithm lower bound, all von Mangoldt prime powers, and the integrable tail 1/648 give T6 < 329/15000, a strict contradiction. Exhaustivity then transfers 100 < (Im(zero n))^2 to the arbitrary rho. No height, mass, numerical, critical-line, or RH premise is introduced. These numerical reductions bound the same complete analytic quantities: firstLiMass_lt_one proves firstLiMass < 1, excluding real zeros and making conjugate indices distinct; firstLiMass_lt_third proves firstLiMass < 1/3 for the bootstrap u > 5. At the resolvent parameter 6, gamma_upper_r6 proves EulerGamma < 5787/10000, log_pi_lower_r6 proves 11447/10000 < log(pi), and Real.log_two_gt_d9 implies 6931/10000 < log(2). These upper, lower, and lower bounds have the directions required by the coefficients +6, -5, and -11. The gamma bound uses the exact harmonic sum H512 and log(512) = 9*log(2). The bound sixQ_upper proves Q6 < 7/500 for the actual Re(-zeta'(6)/zeta(6)), using its complete von Mangoldt series and every term with n >= 4 in the tail comparison. The bound sixDefect_upper combines these estimates to give T6 < 329/15000 for the same defect. The proof actual_ordinate_sq_gt_hundred consumes this bound with the low-zero lower bound, and actual_height_gt_ten transfers the contradiction to every actual nontrivial zero.

For the complete-zero application, the seven CompleteZeroFamily fields are supplied by the exact zero, strip, height, reciprocal-square summability, reciprocal-square mass < 2, finite count shell, and count bound above. Soundness follows from zero_isNontrivial; exhaustivity follows by choosing the zero-th element of each positive finite fiber. The same construction over the conjugation index supplies the conjugate occurrence. For every h in Icc 0 2 and every real y, the literal complex spectralKernel equals the sum over n of multiplicity(n)*exp((zero n-h)*y)*resolventCoefficient(zero n,h). Absolute summability of the full natural series permits its exact equivalence and sigma-sum transports; finite fiber summation gives the complex multiplicity. The shell application holds for every m >= 1: shellWeight is summable and shellSum <= 10000*exp(-100*m). For every real m > 0 and every real gamma, lowHIntegrand is integrable on Ioi 1. The original mean bound assumes m >= 1 and gamma > 10. For an actual rho, it sets gamma = |Im rho|, so actual_height_gt_ten supplies gamma > 10. The Gaussian moment, absolute-convergence and extension derivation uses the scalar hypothesis m ≥ 1 and the bound m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)). Here the inner h-domain is the full Icc 0 2 with weight 1+h, whose integral is 4; the Gaussian center is 16*m with variance denominator 4*m; the physical envelope has coefficient 3; and the shell estimate has core coefficient 20, giving 3*4*20 = 240 and the 2400000*exp(-83*m) term. The positive and negative extensions are 2400 and 384*exp(-28*m).

Complete-family first Li mass application.

The arbitrary-index reciprocal-mass Gaussian shell formula and its full weighted endpoint derivation are given in the existing CountableGaussianQuadraticFourthMoment exposition. For this actual family take I=N, t(k)=Im(actualZero(k)), w(k)=1, a=10 and any real m>=1. The actual_height_gt_ten theorem supplies the full-family height condition; actual_weighted_inverse_square_summable and actual_inverse_square_tsum_transport supply the natural-occurrence summability. The seven-field witness also retains its original strict mass <2, inclusive-cutoff finiteness and count bound. Soundness, exhaustiveness, exact analytic multiplicities, both conjugate occurrences, the exact occurrence fibers and their cardinalities, and the full complex multiplicity-reindexed kernel remain in that same witness.

Write R_Z=sum_k Im(actualZero(k))^(-2). First obtain Summable(k -> (|Im(actualZero(k))|+1)*exp(-m*Im(actualZero(k))^2)) and shell<=1100*R_Z*exp(-100*m)<=2200*exp(-100*m) directly from the original R_Z<2. Independently apply the substantive actual_inverse_square_mass_le_height theorem to this identical entire occurrence family: R_Z<=(101/100)*firstLiMass. Nonnegative multiplication and 1100*(101/100)=1111 give shell<=1111*firstLiMass*exp(-100*m). This uses the height-derived mass theorem, rather than substituting the old 2200 estimate. The exact firstLiMass is 2+EulerGamma-2*log(2*sqrt(pi)), twice the first Li endpoint 1+EulerGamma/2-log(2*sqrt(pi)). The kernel still uses both signs and every occurrence, with no finite-subset, critical-line, injectivity or desired-shell-bound premise.

The complete seven-field original-family application also keeps shell<=10000*exp(-100*m), integrability for every real gamma and m>0, and the original m>=1, gamma>10 mean bound m*(gamma+10)^2*(2400000*exp(-83*m)+2400+384*exp(-28*m)). For every actual nontrivial zero rho one may set gamma=|Im(rho)| because actual_height_gt_ten supplies that certificate. The 1111 first-Li-mass shell consequence alone does not certify a revised weighted 2400000 endpoint, the full Robin sign, retained Schur bounds, a completed carrier or RH. The complete weighted endpoint also requires the Gaussian moment, absolute convergence and extension bounds.

The proof uses endpoint normalization, strip and conjugation algebra, occurrence and fiber transports, finite cutoff membership, the real-part HasSum, kernel positivity, and the von Mangoldt tail comparison.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_complex_pairWeight_hasSum`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_split`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.zero_endpoint_logDeriv`
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Zeros/Endpoints/FirstLiCoefficientPositivity](../../Zeros/Endpoints/FirstLiCoefficientPositivity.md)
- Dependency: [D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder](../../Zeros/Resolvent/XiSquareExteriorRemainder.md)
