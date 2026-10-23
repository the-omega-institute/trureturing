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

**Theorem 1.3 (A prime buffer around the unchanged original good edge).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.good_edge_prime_buffer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.good_edge_prime_buffer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be the original complete-label window, with ell>=243 and OriginalBounds(X,ell,R), and let (p,r) be an unchanged GoodEdge. Put a=log(canonicalSource(p)) and b=log(canonicalSource(r)). If a>=256, every prime q lies outside the closed interval [a-2,b+1]. Both original canonical integers p*U and r*U, the common positive 5040-divisible U, and its exact strict inventory at every point of [a,b] remain hypotheses. The original bounds apply to all good edges and do not select a favorable subset.

For a prime q in [a-2,a), the actual inventory gives q dividing U. Here q>16, so q does not divide 5040. Writing U=5040*q*v gives the legal deletion competitor M=p*5040*v, with 5040*p dividing M and M*q=p*U. The exact next Euler marginal is bounded by the first marginal, retaining arbitrary multiplicity of q. For a prime q in (b,b+1], the actual upper inventory excludes q from U, and the original label bounds give q different from r. Thus q does not divide r*U, and the original legal integer insertion comparison applies. Complete first-clock exclusion covers the central closed interval [a,b], including its endpoints.

For h=log(q) and the relevant endpoint x>=256, one has 5<h<=x/20. The literal Robin density satisfies (81/100)*w(x-h)<=w(x) and (81/100)*w(x)<w(x+h). The price integral is exactly the log-log difference. Its backward and forward quadratic bounds, obtained from the original curve slopes, contradict the corresponding integer comparison because (5/2)*(81/100)>2. No real-center or fixed-price maximizer replaces the original nonlinear integer objective.

The range 243<=a<256 is not included. This excludes primes only: proper prime powers and their von Mangoldt contributions remain. The affine correction gamma in the separate residual accounting is unchanged, with no sign or cancellation supplied here. The theorem gives neither good-edge existence nor cofinality, a PC cutoff identification, a prescribed residual sign, strict Robin for all integers above 5040, or RH.

**Theorem 1.4 (The literal uniform error decreases to zero).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E(t)=t^(-3/10)*log(2*t) is strictly decreasing on [243,infinity) and tends to zero at infinity.

Its derivative is t^(-13/10)*(1-(3/10)*log(2*t)), strictly negative on the stated range. The logarithm grows more slowly than t^(3/10). This error supplier is consumed by the uniform complete-domain bound.

**Theorem 1.5 (The source-faithful signed first-clock transport).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every OriginalWindow with OriginalBounds(X,ell,R) and ell>=243, on S=selectedDomain(X), every prime closed first pulse is excluded and -E(ell)*M<=P1<=0, where M is the real Lebesgue measure of S. P1=sum over primes q<=2*R of log(q)*(W(firstClock(q))-W(q)). W(z) is the integral on the entire S of the reference kernel (lambda(z)-lambda(B(t)))/D(t) on t<z<=B(t). The literal B(t)=t+t^(4/5) and D(t)=w(t)*t^(11/10) are retained.

One finite prime set q<=floor(2*R) covers every nonzero contribution: the theorem also proves both weights vanish for every prime q>2*R. All prime exclusions remain unrestricted by that cutoff. The finite closed-pulse envelope is bounded by log(x), since a contributing integer lies in (x-1,x]. After source-derived exclusion, exact accounting bounds the local response by -b(t)*log(B(t)) and zero, with b(t)=(lambda(t)-lambda(B(t)))/D(t). Monotonicity of w gives b(t)<=t^(-3/10), B(t)<=2*t, and hence b(t)*log(B(t))<=E(t).

The complete domain is a finite union of compact closed intervals. The literal moving-window kernel is integrable there. Source exclusion removes actual initial ties, so its integral agrees with the reference integral at first clocks. Finite summation and integration give the uniform estimate without dependence on edge count, component count, or R. Set measure counts overlaps once. The statement also covers the empty domain; the original positive-mass witnesses are included unchanged.

No PNT, GM, H_ref asymptotic, cofinal witness or favorable signed lower coefficient is a premise or a conclusion. This proves the EL.10 transport obligation. The signed kappa<c_Q lower bound on the cofinal complete original family, the other response layers, full Robin on n>5040, and RH remain separate unresolved obligations. Fixed-slack EL.13/14 applications are not retained as new declarations.

## Complete near-price deletion at the original least maximum

This application keeps the original nonlinear objective F(n)=W(n)-f(log(n)), with W(n)=log(sigma(n)/n) and f(t)=log(log(t)). Let m and N be positive integers with log(m)>1 and m dividing N. Assume N maximizes F over every positive multiple of m and is the smallest of all maximizers, including objective ties. For epsilon>0 set a=log(N), lambda=1/(a*log(a)), and w(a)=(1+log(a))/(a^2*log(a)^2). The complete near-price deletion mass defined below satisfies D<2*epsilon/w(a). For prime p and m=5040*p, this protects the whole forced integer 5040*p; when the original class is attained, canonicalSource(p) supplies the required least maximizer. Attainment itself remains a separate premise.

Strict concavity of f gives f(b)<f(a)+lambda*(b-a) whenever a,b>1 and b differs from a. Applying it to b=log(n) for each legal n different from N, and using the original nonlinear maximum, makes N a strict fixed-price maximum for J_lambda(n)=W(n)-lambda*log(n) on this same full domain. Nonlinear leastness is not needed for this step, and no real-center maximum or restricted-divisor domain is substituted. The public golden_resource_sigma_identity identifies J_lambda with goldenResourceObjective.

Choose the actual strict inventory C0 at lambda from optimal_layer_count_spec. The forced_inventory_least_maximum supplier makes lcm(m,C0) a fixed-price maximum on all positive multiples of m. The strict tangent comparison forces N=lcm(m,C0), hence e_q=max(s_q,c0_q), where e_q=v_q(N), s_q=v_q(m), and c0_q=optimalLayerCount(lambda,q). Inactive or price-tied forced layers remain in this maximum; N is not identified with the unrestricted inventory C0.

At mu=lambda+epsilon, choose the actual strict inventory C with c_q=optimalLayerCount(mu,q), and put U=lcm(m,C). The public positive_layers_eq_count_interval shows c_q<=c0_q because every mu-active layer is lambda-active. Consequently C divides N, U divides N, m divides U, and u_q=v_q(U)=max(s_q,c_q)<=e_q. The same forced-inventory supplier makes this literal U a shifted-price maximum; an arbitrary shifted maximizer that retains extra tied layers cannot replace it.

Take E to be every prime-layer pair (q,j) with s_q<j<=e_q and 0<r(q,j)-lambda<=epsilon, where r(q,j)=goldenLayerMarginal(q,j). This is the complete finite set, with no prime mask or selected subset. The exact strict-count interval gives (q,j) in E if and only if q is a prime divisor of N and u_q<j<=e_q. In the forward direction r<=mu prevents j<=c_q; in the reverse direction e_q=max(s_q,c0_q) makes a layer above s_q lambda-active, while j>c_q gives r<=mu. Thus r=mu is deleted and r=lambda is absent from E; every forced layer remains in U.

Define D as the sum of log(q) over the full set E. Distinct prime fibers are disjoint and j maps injectively to (q,j). Therefore D=sum_q (e_q-u_q)*log(q)=log(N)-log(U)>=0, by the native factorization logarithm identity with common support N.primeFactors. This exact mass keeps empty fibers and U=N. It is neither a proper subcollection estimate nor a bound for an arbitrary forward activation band.

Shifted-price maximality gives W(N)-W(U)<=(lambda+epsilon)*D. The actual decreasing weight w and price derivative lambda'=-w give the backward quadratic inequality lambda*D+w(a)*D^2/2<=f(a)-f(log(U)). If D>0 then U<N, and original nonlinear leastness excludes a tie at this smaller legal U, yielding f(a)-f(log(U))<W(N)-W(U). These two comparisons give w(a)*D<2*epsilon after cancellation of positive D. If D=0, the same strict capacity bound follows from epsilon>0 and w(a)>0 without cancellation.

This is an application of the existing source stack and the forced fixed-price inventory supplier; it retains no additional Lean theorem or conditional wrapper. The conclusion retains full original-domain maximality and leastness as hypotheses. It supplies no cofinal selected-core family, no signed future-deficit budget, no full-label margin, no global attainment, no Robin inequality for every n>5040, and no RH proof. The positive-epsilon strict inequality is not extended to epsilon=0.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.good_edge_prime_buffer`
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
- Dependency: [D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates](OriginalFirstClockBufferEstimates.md)
