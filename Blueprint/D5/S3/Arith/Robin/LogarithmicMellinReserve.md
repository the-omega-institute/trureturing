# Logarithmic Mellin Reserve

## Abstract

Two logarithmic envelopes pay the absolute Mellin mass and the complete Robin kernel variation.

Let rho be a measurable real function and let d, a and mu be real coefficients. Assume |rho(y)| <= d*y+a*(-log(y)*y) for 0<y<=1, and |rho(y)| <= mu*(1+log(y)) for y>=1. These are pointwise envelopes on both parts of the positive axis. No continuity of rho is required.

For 0<alpha<1 define V(d,a,mu,alpha)=d/(1-alpha)+a/(1-alpha)^2 +mu*(1/alpha+1/alpha^2). The low endpoint imposes alpha<1 and the high endpoint imposes alpha>0. The logarithmic factors give the squared denominators. Real powers denote Real.rpow.

**Theorem 1.1 (The whole absolute Mellin integral is paid).**

Lean statement: `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_mellin_reserve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_mellin_reserve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable rho, every real d, a and mu satisfying the two envelopes, and every 0<alpha<1, the function |rho(y)|*y^(-alpha-1) is Lebesgue integrable on y>0. Its integral is at most V(d,a,mu,alpha). The hypotheses retain the entire low interval 0<y<=1 as well as y>1.

On the low interval the majorant is d*y^(-alpha) +a*(-log(y)*y^(-alpha)); its two integrals are d/(1-alpha) and a/(1-alpha)^2. On the high interval the majorant is mu*(1+log(y))*y^(-alpha-1), with integral mu*(1/alpha+1/alpha^2). The low endpoint primitive proves low integrability, while logarithm/power tail integrability pays the high endpoint. The primitives evaluate the logarithmic moments before the two interval integrals are joined.

**Theorem 1.2 (The envelopes bound the complete weighted variation).**

Lean statement: `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_weighted_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_weighted_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>1 put w(t)=(log(t)+1)/(t^2*log(t)^2). For x>1 and s>0 let P(rho,x,s) be the integral on y>0 of rho(y)*s*w(s*y), clipped to x/s<y. The value of the clipped kernel at x/s=y is zero. Write L=log(x), h1=1+1/L, h2=1+2/L+2/L^2 and C(x,alpha)=x^(alpha-1)/L*(h1+h2/(1-alpha)).

For every rho and coefficients satisfying the two envelopes, every x>1 and every 0<alpha<1, the sequence (j+1)^alpha*|P(rho,x,j+1)-P(rho,x,j+2)| is summable over all natural j. Its infinite sum is at most C(x,alpha)*V(d,a,mu,alpha). The full Mellin payment supplies the integrability hypothesis of the weighted variation theorem.

A signed arithmetic coefficient sequence paired with these kernel differences still requires its own growth estimate. The envelopes and this variation bound do not establish the complete Robin inequality or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_mellin_reserve`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmicMellinReserve.logarithmic_weighted_variation`
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
