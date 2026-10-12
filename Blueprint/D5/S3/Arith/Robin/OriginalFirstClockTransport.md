# OriginalFirstClockTransport

## Abstract

The source-faithful signed first-clock transport

**Theorem 1.1 (Closed first-clock exclusion from the actual upper integer).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.original_upper_first_clock_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.original_upper_first_clock_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primes r and q and U>0, suppose N=r*U maximizes F(n)=log(sigma(n)/n)-log(log(log(n))) over all positive integers divisible by 5040*r. Let 243<=t<=R, r>2*R, t<=log(N), and U have exactly the strict layer counts at lambda(t)=1/(t*log(t)). Then t lies outside [q,firstClock(q)].

The actual first clock lies strictly between q and q+1 and solves lambda(firstClock(q))=log(1+1/q)/log(q). At contact, the strict inventory excludes q from U, including a price tie. Since q<=t<=R, q is not r, so q does not divide N. N*q is a legal integer in the same original class. The existing single-layer delta gives its exact log-abundancy gain log(1+1/q). Original maximality bounds this gain by f(C+log(q))-f(C), with C=log(N) and f(x)=log(log(x)); fundamental calculus gives the exact original price integral.

Contact implies q>t-1>=242, log(q)>3, and log(q)<=log(t)<=t/10. The literal weight w(x)=(1+log(x))/(x^2*log(x)^2) satisfies w(t+log(q))>(2/3)*w(t), giving log(q)*w(t+log(q))>2*w(t). The consumed delayed-atom theorem therefore excludes both contact endpoints. No fixed-price optimality or maximizer at real center t is used.

**Theorem 1.2 (Every prime is excluded on the complete original edge union).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OriginalWindow requires its labels to be exactly all primes in [exp(labelStart),exp(2*labelStart)], with attainment on each complete positive 5040*p class; an arbitrary subsample is not an OriginalWindow. canonicalSource(p) is the least maximizing integer. windowOfGA2 uses exactly all primes in [exp(ell),exp(2*ell)], and supplies attainment from an actual GA2 integer divisible by every forced 5040*p via GA2ForcedPrimeSource. This conditional constructor proves no such common witness or cofinal existence.

goodEdges includes every consecutive-label pair satisfying the original source conditions: N_p=p*U, N_r=r*U, U>0, 5040 divides U, A<C, and the literal strict inventory throughout the closed edge [A,C]. This finite set and selectedDomain, its full interval union, are independent of ell and R. OriginalBounds requires ell<=A<C<=R and p,r>2*R for every edge in that fixed complete set; bounds never select or remove an edge. The theorem excludes [q,firstClock(q)] for every prime q on this entire domain. It selects the actual edge containing a contact and applies the actual upper integer theorem. No favorable subset is chosen; the lower canonical endpoint and least attainment remain in the source data.

**Theorem 1.3 (The literal uniform error decreases to zero).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E(t)=t^(-3/10)*log(2*t) is strictly decreasing on [243,infinity) and tends to zero at infinity.

Its derivative is t^(-13/10)*(1-(3/10)*log(2*t)), strictly negative on the stated range. The logarithm grows more slowly than t^(3/10). This error supplier is consumed by the uniform complete-domain bound.

**Theorem 1.4 (The source-faithful signed first-clock transport).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every OriginalWindow with OriginalBounds(X,ell,R) and ell>=243, on S=selectedDomain(X), every prime closed first pulse is excluded and -E(ell)*M<=P1<=0, where M is the real Lebesgue measure of S. P1=sum over primes q<=2*R of log(q)*(W(firstClock(q))-W(q)). W(z) is the integral on the entire S of the reference kernel (lambda(z)-lambda(B(t)))/D(t) on t<z<=B(t). The literal B(t)=t+t^(4/5) and D(t)=w(t)*t^(11/10) are retained.

One finite prime set q<=floor(2*R) covers every nonzero contribution: the theorem also proves both weights vanish for every prime q>2*R. All prime exclusions remain unrestricted by that cutoff. The finite closed-pulse envelope is bounded by log(x), since a contributing integer lies in (x-1,x]. After source-derived exclusion, exact accounting bounds the local response by -b(t)*log(B(t)) and zero, with b(t)=(lambda(t)-lambda(B(t)))/D(t). Monotonicity of w gives b(t)<=t^(-3/10), B(t)<=2*t, and hence b(t)*log(B(t))<=E(t).

The complete domain is a finite union of compact closed intervals. The literal moving-window kernel is integrable there. Source exclusion removes actual initial ties, so its integral agrees with the reference integral at first clocks. Finite summation and integration give the uniform estimate without dependence on edge count, component count, or R. Set measure counts overlaps once. The statement also covers the empty domain; the original positive-mass witnesses are included unchanged.

No PNT, GM, H_ref asymptotic, cofinal witness or favorable signed lower coefficient is a premise or a conclusion. This proves the EL.10 transport obligation. The signed kappa<c_Q lower bound on the cofinal complete original family, the other response layers, full Robin on n>5040, and RH remain separate unresolved obligations. Fixed-slack EL.13/14 applications are not retained as new declarations.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.original_upper_first_clock_exclusion`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](../GoldenResource/GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/DelayedAtomTransport](DelayedAtomTransport.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerPhaseSeparation](EulerLayerPhaseSeparation.md)
- Dependency: [D5/S3/Arith/Robin/FinitePulseKernelTransport](FinitePulseKernelTransport.md)
- Dependency: [D5/S3/Arith/Robin/GA2ForcedPrimeSource](GA2ForcedPrimeSource.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
