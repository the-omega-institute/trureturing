# Canonical Robin records on meshes with vanishing relative gaps

## Abstract

An attained maximal zeta zero gives a Robin lower-bound criterion on ratio-one meshes.

The sample at index k is the original robinLogMargin at the integer m(k)=strictInteger(firstLayerPrice(N(k)+1)). Write W(a,x)=x^a log(x) and B for RHSharpArithmeticEnvelope.B. Write P(Θ,u) for MaximalRealPartProjection.maximalSeries(actualCoeff,actualZero,Θ,u). The zero sequence indexes actual occurrences, so an actual zero occurs according to its analytic multiplicity.

**Theorem 1.1 (Exact lower-bound criterion under attainment).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_lower_bound_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_lower_bound_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). Let N be a strictly increasing natural sequence with N(k+1)/N(k) tending to one in ℝ. For each real 0<α≤1/2, there exist real C≥0 and natural K such that −C≤W(α,N(k)) robinLogMargin(m(k)) for every k≥K if and only if Re(ρ)≤1−α. The attaining zero is a hypothesis. The equivalence includes α=1/2.

For N(k)≥2, strictInteger_spec, strict_layer_iff and firstLayerPrice_strictAnti give a positive-price strict record whose prime support is precisely the primes up to N(k). Its largest prime is P=Pn(N(k)). RHSharpOriginalRecordMargin.margin_identity and B_prefix identify robinLogMargin(m(k))−B(N(k)) with the original full arithmetic correction. The leading estimate fullC_leading and D(P)/D(N(k))→1 give a limit of 2√2 for the correction multiplied by D(N(k))=sqrt(N(k)) log(N(k)). This positive limit gives eventual nonnegativity and boundedness. For weights with exponent below 1/2 the scaled correction tends to zero. When Re(ρ)≤1−α, the full-strip envelope for B and the nonnegative correction yield the lower bound, including at α=1/2. When Re(ρ)>1−α, unboundedness below at weight α contradicts any eventual bound.

**Theorem 1.2 (Unboundedness below above the critical weight).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). Assume Re(ρ)>1/2. Let N be a strictly increasing natural sequence with N(k+1)/N(k) tending to one in ℝ. For any real α>1−Re(ρ), real M and natural K there is k≥K with W(α,N(k)) robinLogMargin(m(k))<M. The factor N(k)^(α−(1−Re(ρ))) tends to +∞ and amplifies the fixed negative excursions.

**Theorem 1.3 (Opposite limits on two ratio-one meshes under unattainment).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the actual zero abscissa Θ is unattained and 1−Θ<α<1/2. There are two strictly increasing sequences of cutoff indices with adjacent ratios tending to one. The literal canonical margins, multiplied by N^α log(N), tend to positive infinity on one sequence and negative infinity on the other. The positive samples use the first theta crossing and the negative samples use integer ceilings. Each sign is sampled through a fixed power threshold in every late log window.

**Theorem 1.4 (Negative arithmetic excursions on a logarithmic mesh).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). Assume Re(ρ)>1/2. Let y be a real sequence tending to +∞ whose forward increments tend to zero. There is a real c>0 such that every natural K admits k≥K with exp((1−Re(ρ)) y(k)) y(k) B(exp(y(k)))<−c. Apply sign transfer to the uniformly continuous real part of the maximal-line series.

**Theorem 1.5 (Signed critical-weight samples under a closed upper bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_signed_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_signed_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1/2≤Θ<1 bound Re(ρ) from above for every nontrivial zeta zero ρ, and let N(k) tend to +∞ in ℕ. With y(k)=log(N(k)), the sum W(1−Θ,N(k)) robinLogMargin(m(k)) + exp(−Θ y(k)) actualH(y(k)) − c(Θ) tends to zero in ℂ. Here actualH is the complete complex zero series, and c(Θ) is 2√2−2 at Θ=1/2 and zero above 1/2. At equality the bound implies RH. The signed arithmetic term contributes −2 and the scaled record correction contributes 2√2. For Θ>1/2 the critical-strip signed arithmetic asymptotic applies and the scaled record correction vanishes.

**Theorem 1.6 (Exact strip criterion on fixed logarithmic windows).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_log_window_lower_bound_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_log_window_lower_bound_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix real h>0 and 0<α≤1/2. Set n(v)=strictInteger(firstLayerPrice(⌊exp(v)⌋+1)), using the natural floor and casting it to ℝ in the price. The condition Re(ρ)≤1−α for every actual nontrivial Riemann zeta zero ρ is equivalent to the existence of real C≥0 and T such that every real t≥T satisfies −C≤exp(αt) ∫₀ʰ (t+u) robinLogMargin(n(t+u)) du.

Write m(v)=v robinLogMargin(n(v)). The floor identity for B and the canonical record correction give an eventual bound 0≤m(v)−v B(exp(v))≤K exp(−v/2) for some K≥0. The strip envelope for B and the nonnegative correction give the lower bound after integration. In the other direction, eventually m(v)≤−v f(v)+(K+8) exp(−v/2) for the actual signed theta tail f. Any zero with Re(ρ)>1−α supplies arbitrarily late positive first-moment window peaks at exponent σ=−α. These force arbitrarily negative scaled Robin window values because the integrated error stays bounded after multiplication by exp(αt), including at α=1/2.

The quantifiers use one fixed width h and all sufficiently large real starts t. The integral samples the literal canonical records at the floor of each exp(t+u) throughout the interval. Under unattainment and 1−Θ<α<1/2, the two-mesh theorem gives a ratio-one mesh with an eventual pointwise lower bound even though the closed strip bound fails. At α=1/2 the zero-side condition in the equivalence is Re(ρ)≤1/2 for every actual nontrivial zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_log_window_lower_bound_iff`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_lower_bound_iff`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_signed_asymptotic`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes`
- Dependency: [D5/S3/Analytic/Asymptotics/CanonicalThresholdWindowTransfer](../../../Analytic/Asymptotics/CanonicalThresholdWindowTransfer.md)
- Dependency: [D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer](../../../Analytic/Asymptotics/VanishingGapSignTransfer.md)
- Dependency: [D5/S3/Analytic/Laplace/MaximalRealPartProjection](../../../Analytic/Laplace/MaximalRealPartProjection.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ActualUnattainedThetaWindows](../Analytic/ActualUnattainedThetaWindows.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature](../Analytic/LogLogGlobalCurvature.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](../Analytic/ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder](ActualRecordAllLogBudgetRemainder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin](RHSharpOriginalRecordMargin.md)
- Dependency: [D5/S3/Arith/Robin/ThetaTailRobinWitness](../ThetaTailRobinWitness.md)
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](../../../Weil/Mertens/CriticalThetaTailPeak.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
