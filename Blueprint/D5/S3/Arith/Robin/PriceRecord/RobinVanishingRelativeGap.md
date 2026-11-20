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

For N(k)≥2, strictInteger_spec, strict_layer_iff and firstLayerPrice_strictAnti give a positive-price strict record whose prime support is precisely the primes up to N(k). Its largest prime is P=Pn(N(k)). RHSharpOriginalRecordMargin.margin_identity and B_prefix identify robinLogMargin(m(k))−B(N(k)) with the original full arithmetic correction. The leading estimate fullC_leading gives eventual nonnegativity and boundedness at the scale D(P)=sqrt(P) log(P). The normalization D(P)/D(N(k))→1 gives the same properties at D(N(k)). For weights with exponent below 1/2 the scaled correction tends to zero. When Re(ρ)≤1−α, the full-strip envelope for B and the nonnegative correction yield the lower bound, including at α=1/2. When Re(ρ)>1−α, unboundedness below at weight α contradicts any eventual bound.

**Theorem 1.2 (Unboundedness below above the critical weight).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). Assume Re(ρ)>1/2. Let N be a strictly increasing natural sequence with N(k+1)/N(k) tending to one in ℝ. For any real α>1−Re(ρ), real M and natural K there is k≥K with W(α,N(k)) robinLogMargin(m(k))<M. The factor N(k)^(α−(1−Re(ρ))) tends to +∞ and amplifies the fixed negative excursions.

**Theorem 1.3 (Negative arithmetic excursions on a logarithmic mesh).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). Assume Re(ρ)>1/2. Let y be a real sequence tending to +∞ whose forward increments tend to zero. There is a real c>0 such that every natural K admits k≥K with exp((1−Re(ρ)) y(k)) y(k) B(exp(y(k)))<−c. Apply sign transfer to the uniformly continuous real part of the maximal-line series.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_B_negative_on_vanishing_gap_mesh`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_lower_bound_iff`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.actual_canonical_samples_unbounded_below`
- Dependency: [D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer](../../../Analytic/Asymptotics/VanishingGapSignTransfer.md)
- Dependency: [D5/S3/Analytic/Laplace/MaximalRealPartProjection](../../../Analytic/Laplace/MaximalRealPartProjection.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature](../Analytic/LogLogGlobalCurvature.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](../Analytic/ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin](RHSharpOriginalRecordMargin.md)
- Dependency: [D5/S3/Arith/Robin/ThetaTailRobinWitness](../ThetaTailRobinWitness.md)
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](../../../Weil/Mertens/CriticalThetaTailPeak.md)
