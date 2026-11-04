# The Original Full-Band Normalizer

## Abstract

The original reciprocal-log kernel has a positive full-band normalizer in its source clock.

Keep the original g(y)=1/(y log(y)), w(y)=(log(y)+1)/(y^2 log(y)^2), H(t)=t^(4/5), and b(t)=t+H(t). The literal kernel is k(t,x)=(g(x)-g(b(t)))/(w(t)t^(11/10)) when t<x<=b(t), and zero elsewhere. Thus k(t,t)=0; the terminal support is weak and k(t,b(t))=0. For J=[ell,R], windowMass(ell,R,x)=integral_J k(t,x) dt. The integration variable here is t. The fixed-t x-moment from OriginalMovingWindowMoment is not this normalizer.

**Theorem 1.1 (The exact full-band envelope and its first-order error).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullBandNormalizer.original_full_band_normalizer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFullBandNormalizer.original_full_band_normalizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a, ell, R, x with a>=4, 4<=ell<=a, x=b(a) and x<=R, put q=a/x, delta=a^(-1/5), epsilon=x^(-1/5), and A=x^(1/2)/2. Then 0<windowMass(ell,R,x) and A q^(28/5)(1+(4/5)epsilon) <=windowMass(ell,R,x) <=A q^(5/2)(1+(4/5)delta)<A. Moreover |windowMass(ell,R,x)-A| <=(14/5)delta x^(1/2). Every fractional power is a real power. No numerical large-a cutoff is imposed.

The complete active source band is a<t<x. Strict monotonicity of b on [1,infinity) eliminates the part of [ell,R] below a, and t<x eliminates the part at or above x. Since a>=ell, the full band lies inside the original reference interval. The parameterization x=b(a), a>=ell expresses the full-band condition b(ell)<=x<=R with its unique inverse endpoint a; it does not assume ell<=x-x^(4/5). No original source intervals, prime labels or good-edge components are discarded.

Derivative bounds for b give (1+(4/5)epsilon)(t-a)<=b(t)-x <=(1+(4/5)delta)(t-a) on [a,x]. The existing price_drop and weight_ratio_lower suppliers, t/b(t)>=q and t^(-11/10)>=x^(-11/10) give the lower source triangle. For the upper triangle, y^2 w(y)=1/log(y)+1/log(y)^2 decreases for y>1, so w(y)<=(t/y)^2 w(t). Integrating this comparison against the actual price derivative g'=-w gives kappa(t)<=t^(9/10)(b(t)-x)/(x b(t)). With z=t^(1/10)>=1, t^(9/10)/b(t)=z/(z^2+1) decreases. Hence the upper coefficient is x^(-11/10) q^(9/10)(1+(4/5)delta). Here kappa is the continuous price quotient; its equality with k is used only inside a<t<x, so the strict-diagonal value is preserved.

The source triangle integrates to (x-a)^2/2, and x^(-11/10)(x-a)^2=x^(1/2)q^(8/5). These identities give precisely the powers 28/5 and 5/2. Also q=1/(1+delta) and delta>0; 1+(4/5)delta<1+delta<=(1+delta)^(5/2) makes the upper bound strict. Dropping the positive epsilon correction in the lower bound and using negative_power_lower with c=28/5 gives the stated first-order error. The two multiplicative envelope factors approach one as a tends to infinity. This is a denominator estimate for the actual full reference mass.

The original kernel is the EL Definition 1.2 kernel in FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. Definitions and source-integrability come from OriginalMovingWindowMoment and OriginalMovingCutRow. The proof reuses their public price_drop, weight_ratio_lower, triangle_integral, negative_power_lower and kernel_integrableOn, and Mathlib's power integral and monotonicity APIs.

The statement controls the complete reference mass only. It does not prove positive mass for selectedDomain, a relative selected/reference comparison, small inventory or collar loss, cofinal qualifying OriginalWindow witnesses, the signed prime numerator, or Robin/RH. No second-order correction, rearrangement or unimodality claim is assumed.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFullBandNormalizer.original_full_band_normalizer`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutRow](OriginalMovingCutRow.md)
