# Logarithmic Endpoint Variation

## Abstract

Cubic Mellin endpoint moments pay the entire logarithmic fourth variation.

Positive mixing of a full family of power moments reaches the weight m/log(m)^4. The proof first integrates finite prefixes and then bounds all nonnegative partial sums, so logarithmic summability is a conclusion.

**Theorem 1.1 (Cubic endpoint moments pay the full logarithmic weight).**

Lean statement: `D5/S3/Arith/Robin/LogarithmicEndpointVariation.log_four_variation_of_cubic_endpoint_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmicEndpointVariation.log_four_variation_of_cubic_endpoint_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a(m)>=0 and C>=0. For every 0<beta<=1/2 assume every finite prefix over m>=8 of m^(1-beta)*a(m) is at most C/beta^3. Then m/log(m)^4*a(m) is summable over all integers m>=2, and its infinite sum is at most its exact six-term sum over 2<=m<=7 plus 2*exp(1)*C.

For m>=8, integrate beta^3*m^(1-beta) over 0<beta<1/2. Its restriction to 0<beta<1/log(m) pays at least m/(4*exp(1)*log(m)^4). The same mixed finite prefix is at most C/2. The finite head is preserved and all partial sums are bounded before the infinite-sum theorem is applied.

**Theorem 1.2 (The logarithmic envelopes pay the complete Robin variation).**

Lean statement: `D5/S3/Arith/Robin/LogarithmicEndpointVariation.logarithmic_four_weighted_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmicEndpointVariation.logarithmic_four_weighted_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be measurable, d,a,mu>=0, x>1, and assume the same pointwise envelopes |rho(y)|<=d*y+a*(-log(y)*y) for 0<y<=1 and |rho(y)|<=mu*(1+log(y)) for y>=1. Write L=log(x), h1=1+1/L, h2=1+2/L+2/L^2, and C=(h1/2+h2)*(a+d/2+3*mu/2)/L.

With the existing clipped integral P(rho,x,m), the complete sequence m/log(m)^4*|P(rho,x,m)-P(rho,x,m+1)| for m>=2 is summable. Its infinite sum is at most the exact six-term sum over 2<=m<=7 plus 2*exp(1)*C. The strict cutoff x/m<y, including zero at equality, is the existing genericP.

The logarithmic Mellin reserve directly supplies the entire family alpha=1-beta, 0<beta<=1/2. Its bound grows at most as C/beta^3. The preceding theorem then pays the full logarithmic fourth variation. Arithmetic coefficient growth, interchange in the original integral variable and the final signed Robin estimate still require their own proofs.

## References

- Truth anchor: `D5/S3/Arith/Robin/LogarithmicEndpointVariation.log_four_variation_of_cubic_endpoint_moments`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmicEndpointVariation.logarithmic_four_weighted_variation`
- Dependency: [D5/S3/Arith/Robin/LogarithmicMellinReserve](LogarithmicMellinReserve.md)
