# Integrated transverse moment

## Abstract

Integrated logarithmic defects and the extended weighted transverse second moment.

**Definition 1.1 (The symmetric logarithmic difference).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.logKernel`

*Formalization.* `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.logKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real displacement a, height gamma and argument t, logKernel is log((t-a)^2+gamma^2)+log((t+a)^2+gamma^2)-2*log(t^2+gamma^2). The theorem uses positive heights, so all logarithm arguments are strictly positive. This is an additive symmetric difference; no convergent infinite product or chosen logarithm of such a product is assumed.

**Definition 1.2 (The endpoint integral).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.endpointKernel`

*Formalization.* `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.endpointKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

endpointKernel(a,gamma,T) is the oriented integral from zero to a of log(((T+v)^2+gamma^2)/((T-v)^2+gamma^2)). For positive gamma, shifted integral cancellation gives the scalar identity: the integral from zero to T of logKernel(a,gamma,t) equals endpointKernel(a,gamma,T). The proof of this identity retains all real a and T, including negative endpoints. For a and T nonnegative the endpoint integrand is nonnegative, and it is strictly positive on 0<v<a when a and T are positive.

**Definition 1.3 (The unordered weighted defect).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.defect`

*Formalization.* `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary index type I and real families w,a,gamma, defect(t) is the unordered tsum of w(i)*logKernel(a(i),gamma(i),t). The convergence assertions below use nonnegative weights, displacements in [0,1/2], positive heights and summability of w(i)*a(i)^2/gamma(i)^2. The definition itself adds no countability or convergence premise.

**Definition 1.4 (The integrated defect).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integratedDefect`

*Formalization.* `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integratedDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

integratedDefect(T) is the oriented integral of defect(t) from zero to T. Positivity is asserted for this integral at nonnegative T; a pointwise nonnegative logarithmic defect is not a hypothesis or a conclusion.

**Theorem 1.5 (The complete integrated moment theorem).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integrated_transverse_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integrated_transverse_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary I, assume w(i)>=0, 0<=a(i)<=1/2, gamma(i)>0 and summability of w(i)*a(i)^2/gamma(i)^2. The second derivative of x mapped to log(x^2+gamma^2) is bounded in absolute value by 2/gamma^2. Integrating the resulting first-derivative difference gives |w(i)*logKernel(a(i),gamma(i),t)|<=2*w(i)*a(i)^2/gamma(i)^2 for every i and real t. The summable majorant yields HasSumUniformlyOn on the entire real line, absolute summability at each t, and continuity of defect.

The scalar endpoint identity is exchanged with the unordered family by applying an arbitrary-filter uniform-to-zero interval-integral theorem to the net of finite partial sums. This retains arbitrary I without a Countable I assumption. Consequently, for every T>=0, integratedDefect(T)=tsum_i w(i)*endpointKernel(a(i),gamma(i),T). Each term is nonnegative. At every T>0 the integrated defect is strictly positive exactly when some index has both w(i)>0 and a(i)>0. Zero weights, zero displacements and the empty index type remain in scope.

For T>=a>=0 the scalar quantity T*endpointKernel(a,gamma,T) lies between 2*a^2*T^2/((T+a)^2+gamma^2) and 2*a^2*T^2/((T-a)^2+gamma^2). These bounds give the limit 2*a^2 for each fixed positive gamma. For 0<=a<=1/2 and T>=1 it also lies between zero and 8*a^2. The inverse-square budget controls the logarithmic series and its interval integral; it does not impose a finite total weighted second moment.

As T tends to positive infinity, ENNReal.ofReal(T*integratedDefect(T)) tends to 2*tsum_i ENNReal.ofReal(w(i)*a(i)^2). The limit belongs to the extended nonnegative reals and may be infinity. When the weighted second moment is summable, the proof uses the scalar limits and the 8*w(i)*a(i)^2 majorant in dominated convergence for tsum. When it is not summable, nonnegative finite subsums have arbitrarily large mass; their limits and their lower bounds on the complete sum force divergence to infinity. This second case is retained rather than replaced by a finite-moment hypothesis.

The real-valued quantity T*integratedDefect(T) tends to zero if and only if every index with strictly positive weight has displacement zero. In the forward direction, uniqueness of the extended limit forces every nonnegative weighted square to vanish. In the reverse direction every weighted logarithmic term vanishes identically. The criterion says nothing about displacement at an index whose weight is zero.

The index type is arbitrary, heights need only be individually positive and may approach zero, and weights are arbitrary nonnegative reals. No uniform positive lower bound on height, finite total second moment, density asymptotic, infinite-product convergence or additional limit hypothesis is used. The retained private calculus, endpoint, interchange and nonnegative-family helpers have actual consumers in this proof. These are general analytic arguments, with no bounded enumeration, checker, numerical reduction or certified finite instance; utility is none.

This theorem concerns the four displayed abstract functions. To apply it to the actual zeta zero divisor, one must still supply the actual index and multiplicity correspondence, verify the displacement and height hypotheses and inverse-square budget, and identify this additive defect and its integral with the intended zeta quantity, including any normalization or boundary terms. To conclude a critical-line assertion one must additionally establish the required real zero-limit from independent arithmetic or analytic information. Those bridges are absent here. The result supplies no actual-zeta or RH conclusion and makes no literature-novelty claim.

## References

- Truth anchor: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.defect`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.endpointKernel`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integratedDefect`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.integrated_transverse_moment`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment.logKernel`
