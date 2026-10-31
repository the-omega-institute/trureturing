# OriginalFirstClockTransport

## Abstract

The source-faithful signed first-clock transport

**Theorem 1.1 (The canonical source is the least full-class maximizer when attained).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.canonical_source_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.canonical_source_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural label p, assume some N satisfies originalMaximizes(p,N). Then canonicalSource(p) maximizes the original nonlinear objective over all positive integers divisible by 5040*p, and is no larger than any other maximizer in that full class. OriginalInventoryNormalizerLoss uses the maximality projection for every label of its complete enumeration, both in source-order classification and in charging each omitted inventory-changing interval. Attainment remains an explicit premise; no cofinal source family is asserted.

**Theorem 1.2 (The canonical first clock has the exact first-layer price).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_clock_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_clock_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime q, q<firstClock(q)<q+1 and g(firstClock(q))=goldenLayerMarginal(q,1). The source is the actual reciprocal-log price and the original first layer. OriginalPrimeSourceOrder uses the strict lower location to exclude large forcing labels from complete strict inventories.

**Theorem 1.3 (A first-clock contact is absent from the complete strict inventory).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_absent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_absent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U>0, q prime, t>1 and t<=firstClock(q). If every natural factorization coordinate of U equals optimalLayerCount(g(t),q) at the same clock, then q does not divide U. Equality at the actual first clock is included because the inventory uses strict marginals. This existing supplier is consumed by OriginalPrimeSourceOrder.

**Theorem 1.4 (Closed first-clock exclusion from the actual upper integer).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.original_upper_first_clock_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.original_upper_first_clock_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primes r and q and U>0, suppose N=r*U maximizes F(n)=log(sigma(n)/n)-log(log(log(n))) over all positive integers divisible by 5040*r. Let 243<=t<=R, r>2*R, t<=log(N), and U have exactly the strict layer counts at lambda(t)=1/(t*log(t)). Then t lies outside [q,firstClock(q)].

The actual first clock lies strictly between q and q+1 and solves lambda(firstClock(q))=log(1+1/q)/log(q). At contact, the strict inventory excludes q from U, including a price tie. Since q<=t<=R, q is not r, so q does not divide N. N*q is a legal integer in the same original class. The existing single-layer delta gives its exact log-abundancy gain log(1+1/q). Original maximality bounds this gain by f(C+log(q))-f(C), with C=log(N) and f(x)=log(log(x)); fundamental calculus gives the exact original price integral.

Contact implies q>t-1>=242, log(q)>3, and log(q)<=log(t)<=t/10. The literal weight w(x)=(1+log(x))/(x^2*log(x)^2) satisfies w(t+log(q))>(2/3)*w(t), giving log(q)*w(t+log(q))>2*w(t). The consumed delayed-atom theorem therefore excludes both contact endpoints. No fixed-price optimality or maximizer at real center t is used.

**Theorem 1.5 (Every prime is excluded on the complete original edge union).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OriginalWindow requires its labels to be exactly all primes in [exp(labelStart),exp(2*labelStart)], with attainment on each complete positive 5040*p class; an arbitrary subsample is not an OriginalWindow. canonicalSource(p) is the least maximizing integer. windowOfGA2 uses exactly all primes in [exp(ell),exp(2*ell)], and supplies attainment from an actual GA2 integer divisible by every forced 5040*p via GA2ForcedPrimeSource. This conditional constructor proves no such common witness or cofinal existence.

goodEdges includes every consecutive-label pair satisfying the original source conditions: N_p=p*U, N_r=r*U, U>0, 5040 divides U, A<C, and the literal strict inventory throughout the closed edge [A,C]. This finite set and selectedDomain, its full interval union, are independent of ell and R. OriginalBounds requires ell<=A<C<=R and p,r>2*R for every edge in that fixed complete set; bounds never select or remove an edge. The theorem excludes [q,firstClock(q)] for every prime q on this entire domain. It selects the actual edge containing a contact and applies the actual upper integer theorem. No favorable subset is chosen; the lower canonical endpoint and least attainment remain in the source data.

**Theorem 1.6 (A prime buffer around the unchanged original good edge).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.good_edge_prime_buffer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.good_edge_prime_buffer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be the original complete-label window, with ell>=243 and OriginalBounds(X,ell,R), and let (p,r) be an unchanged GoodEdge. Put a=log(canonicalSource(p)) and b=log(canonicalSource(r)). If a>=256, every prime q lies outside the closed interval [a-2,b+1]. Both original canonical integers p*U and r*U, the common positive 5040-divisible U, and its exact strict inventory at every point of [a,b] remain hypotheses. The original bounds apply to all good edges and do not select a favorable subset.

For a prime q in [a-2,a), the actual inventory gives q dividing U. Here q>16, so q does not divide 5040. Writing U=5040*q*v gives the legal deletion competitor M=p*5040*v, with 5040*p dividing M and M*q=p*U. The exact next Euler marginal is bounded by the first marginal, retaining arbitrary multiplicity of q. For a prime q in (b,b+1], the actual upper inventory excludes q from U, and the original label bounds give q different from r. Thus q does not divide r*U, and the original legal integer insertion comparison applies. Complete first-clock exclusion covers the central closed interval [a,b], including its endpoints.

For h=log(q) and the relevant endpoint x>=256, one has 5<h<=x/20. The literal Robin density satisfies (81/100)*w(x-h)<=w(x) and (81/100)*w(x)<w(x+h). The price integral is exactly the log-log difference. Its backward and forward quadratic bounds, obtained from the original curve slopes, contradict the corresponding integer comparison because (5/2)*(81/100)>2. No real-center or fixed-price maximizer replaces the original nonlinear integer objective.

The range 243<=a<256 is not included. This excludes primes only: proper prime powers and their von Mangoldt contributions remain. The affine correction gamma in the separate residual accounting is unchanged, with no sign or cancellation supplied here. The theorem gives neither good-edge existence nor cofinality, a PC cutoff identification, a prescribed residual sign, strict Robin for all integers above 5040, or RH.

**Theorem 1.7 (The literal uniform error decreases to zero).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_error_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E(t)=t^(-3/10)*log(2*t) is strictly decreasing on [243,infinity) and tends to zero at infinity.

Its derivative is t^(-13/10)*(1-(3/10)*log(2*t)), strictly negative on the stated range. The logarithm grows more slowly than t^(3/10). This error supplier is consumed by the uniform complete-domain bound.

**Theorem 1.8 (The source-faithful signed first-clock transport).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every OriginalWindow with OriginalBounds(X,ell,R) and ell>=243, on S=selectedDomain(X), every prime closed first pulse is excluded and -E(ell)*M<=P1<=0, where M is the real Lebesgue measure of S. P1=sum over primes q<=2*R of log(q)*(W(firstClock(q))-W(q)). W(z) is the integral on the entire S of the reference kernel (lambda(z)-lambda(B(t)))/D(t) on t<z<=B(t). The literal B(t)=t+t^(4/5) and D(t)=w(t)*t^(11/10) are retained.

One finite prime set q<=floor(2*R) covers every nonzero contribution: the theorem also proves both weights vanish for every prime q>2*R. All prime exclusions remain unrestricted by that cutoff. The finite closed-pulse envelope is bounded by log(x), since a contributing integer lies in (x-1,x]. After source-derived exclusion, exact accounting bounds the local response by -b(t)*log(B(t)) and zero, with b(t)=(lambda(t)-lambda(B(t)))/D(t). Monotonicity of w gives b(t)<=t^(-3/10), B(t)<=2*t, and hence b(t)*log(B(t))<=E(t).

The complete domain is a finite union of compact closed intervals. The literal moving-window kernel is integrable there. Source exclusion removes actual initial ties, so its integral agrees with the reference integral at first clocks. Finite summation and integration give the uniform estimate without dependence on edge count, component count, or R. Set measure counts overlaps once. The statement also covers the empty domain; the original positive-mass witnesses are included unchanged.

No PNT, GM, H_ref asymptotic, cofinal witness or favorable signed lower coefficient is a premise or a conclusion. This proves the EL.10 transport obligation. The signed kappa<c_Q lower bound on the cofinal complete original family, the other response layers, full Robin on n>5040, and RH remain separate unresolved obligations. Fixed-slack EL.13/14 applications are not retained as new declarations.

## Cubic applications on the complete original domain

Fix any X : OriginalWindow and real ell,R with ell>=243 and OriginalBounds(X,ell,R). The labels of X are exactly all primes in [exp(X.labelStart),exp(2*X.labelStart)]. For each label p, the original objective F(n)=log(sigma(n)/n)-log(log(log(n))) attains its maximum on the full class of positive integers divisible by 5040*p, and N_p=canonicalSource(p) is the least of all such maximizers. The integration parameter ell is independent of X.labelStart; no identification of the two parameters is made.

Keep every original good consecutive-label edge (p,r). Its endpoints are a=log(N_p)<b=log(N_r), with N_p=p*U, N_r=r*U, U>0 and 5040 dividing U. At every t in the entire closed interval [a,b] and for every natural q, the full inventory satisfies v_q(U)=optimalLayerCount(g(t),q). Here strict means that a layer is counted exactly when its marginal exceeds g(t); price ties are excluded. OriginalBounds requires ell<=a<b<=R and p,r>2*R for every one of these edges. Set S=selectedDomain(X), the union of all their closed intervals, and M=volume.real(S). Overlaps are counted once. Bounds do not select edges. The frozen domain_compact and selected_domain_bounds suppliers give compact S contained in [ell,R]. The hypotheses require neither ell<=R nor R>0 separately, and allow S to be empty and M to be zero.

Use natural logarithms and the literal functions g(t)=1/(t*log(t)), w(t)=(log(t)+1)/(t^2*log(t)^2), H(t)=t^(4/5), and d(t)=t^(11/10). These are g and activationDensity from ActualRobinClockCovariance and the window and normalization used in the original transport. The DelayedAtomTransport PriceCurve instance original_curve gives g'=-w, w>0, continuity, and decreasing w on (1,infinity). In particular, on S all denominators below are positive, 1<=H(t)<=t, and t+H(t)<=2*t.

For a prime q put tau_q=firstClock(q). The existing first_clock_spec gives q<tau_q<q+1 and g(tau_q)=log(1+1/q)/log(q). The literal actualKernel has support t<=tau_q<=t+H(t). On this same S, complete_original_first_clock_exclusion excludes the whole closed pulse [q,tau_q]. Thus an active q satisfies t<q<tau_q<=t+H(t), and an initial tie t=tau_q cannot occur. This is the reason the actual support can be written with t<tau_q here, as in actual_eq_reference_on_domain. The clock remains tau_q, never the integer q. Moreover q<tau_q<=2*t<=2*R for every active term on S. Hence the fixed finite inventory I_R={q natural : q prime and q<=floor(2*R)} loses no active prime, including when S is empty.

## Exact and cubic kernels, centers, and responses

For t>1, H>=0, d>0 and 0<=u<=H define K(t,H,d,u)=(g(t+u)-g(t+H))/(w(t)*d). Its cubic price approximation is P3(t,H,d,u)=[H-u+w'(t)*(H^2-u^2)/(2*w(t))+w''(t)*(H^3-u^3)/(6*w(t))]/d. The word cubic refers to the price expansion; the density being integrated is its degree-two Taylor polynomial. ActualRobinClockCovariance.density_integral, with endpoints t+u and t+H followed by translation, gives the exact identity K(t,H,d,u)=(integral from u to H of w(t+v) dv)/(w(t)*d). Integrating w(t)+w'(t)*v+w''(t)*v^2/2 on those same endpoints gives precisely P3.

The two continuum centers are C_exact(t,H,d)=integral from 0 to H of K(t,H,d,u) du =[log(log(t+H))-log(log(t))-H*g(t+H)]/(w(t)*d), and C3(t,H,d)=integral from 0 to H of P3(t,H,d,u) du =H^2/(2*d)+w'(t)*H^3/(3*w(t)*d)+w''(t)*H^4/(8*w(t)*d). All three terms of C3 are part of the center. For C_exact, the primitive integral from 0 to H of g(t+u) du =log(log(t+H))-log(log(t)) is the existing ArithmeticMixedCornerResponse.shifted_g_integral, equivalently buffer_loglog_integral in the owning transport source with translated endpoints. Integral linearity then subtracts the constant H*g(t+H). For C3, integrating H-u, H^2-u^2, and H^3-u^3 gives H^2/2, 2*H^3/3, and 3*H^4/4 respectively, which explains the three denominators 2, 3, and 8 in its closed form.

At each t write H=H(t), d=d(t), and define J_R(t)={q in I_R : t<tau_q<=t+H}. Keep the actual response A(t)=sum over q in I_R of log(q)*actualKernel(g,t,t+H,w(t)*d,tau_q)-C_exact(t,H,d). Here actualKernel(g,t,t+H,w(t)*d,z) is (g(z)-g(t+H))/(w(t)*d) if t<=z<=t+H, and zero otherwise. Define the cubic response B(t)=sum over q in J_R(t) of log(q)*P3(t,H,d,tau_q-t)-C3(t,H,d). By the closed-pulse exclusion, the sum in A on S is exactly the sum over this same J_R(t) of log(q)*K(t,H,d,tau_q-t). Both centers and all actual clock offsets are retained in comparing A and B.

## Ordinary integrability follows from the original bounds

For every X,ell,R as above one obtains both IntegrableOn A S and IntegrableOn B S with respect to Lebesgue measure. No prime-mass estimate is needed for this application. To see this directly, fix q in the finite I_R. The frozen original_kernel_integrable applies to z=tau_q and to exactly the window t+H(t) and denominator w(t)*d(t). The frozen actual_eq_reference_on_domain identifies this reference atom with the actual atom at every point of S. Multiplication by the constant log(q) and finite summation therefore give integrability of the actual prime sum.

The closed form for C_exact deals with its moving integration endpoint exactly. On S one has t>=243, t+H(t)>1, w(t)>0 and d(t)>0. Thus log(log(t)), log(log(t+H(t))), g(t+H(t)), and the positive denominator vary continuously there. C_exact is continuous on compact S and hence integrable; subtraction supplies IntegrableOn A S. This uses the primitive rather than an assumption that a parameter-dependent integral is continuous.

For the cubic response, w,w',w'' are continuous on (1,infinity). For fixed tau_q the coefficient P3(t,H(t),d(t),tau_q-t), interpreted by its polynomial formula also outside the active window, is continuous on S. Its gate E_q={t : t<tau_q and tau_q<=t+H(t)} is measurable: the first condition is an open ray and the second is a closed sublevel condition for the continuous moving endpoint. ContinuousOn.integrableOn_compact and IntegrableOn.indicator give an integrable gated coefficient. The finite sum of these coefficients weighted by log(q) is integrable. Each of the three terms of C3 is continuous on S, so subtraction gives IntegrableOn B S. No continuity across a clock threshold is asserted or needed. Compactness also gives finite M, and these arguments include empty S without a positive-volume premise.

## The signed Taylor remainder and its integrated constants

The derivative engine in LogLogHigherDerivative gives w=positiveKernel(1,0,0), w'=-positiveKernel(2,0,0), w''=positiveKernel(3,0,0), and w'''=-positiveKernel(4,0,0) on t>1, by hasDerivAt_positiveKernel at orders 1,2,3. Expanding that existing finite recursion, with L=log(t), gives w'(t)=-(2*L^2+3*L+2)/(t^3*L^3), w''(t)=(6*L^3+11*L^2+12*L+6)/(t^4*L^4), and -w'''(t)=(24*L^4+50*L^3+70*L^2+60*L+24)/(t^5*L^5). These are derivatives of the literal density w, not replacement weights.

For s>=3, L=log(s)>=1. Every lower power in 24*L^4+50*L^3+70*L^2+60*L+24 is at most L^4, and the coefficients sum to 228. In particular this polynomial is at most 228*L^4 and hence at most 228*(L^4+L^3). Division by s^5*L^5>0 gives 0<=-w'''(s)<=228*w(s)/s^3. For 3<=t<=s, decreasing w and s^3>=t^3 give the forward bound 0<=-w'''(s)<=228*w(t)/t^3.

Put Q2(t,v)=w(t)+w'(t)*v+w''(t)*v^2/2. For t>=3 and v>0 the function w is C^3 on a neighborhood of [t,t+v]: both its real and logarithmic denominators stay nonzero there. The pinned Mathlib taylor_mean_remainder_lagrange_iteratedDeriv in Mathlib/Analysis/Calculus/Taylor.lean, with degree n=2, x0=t and x=t+v, supplies an interior xi with w(t+v)-Q2(t,v)=w'''(xi)*v^3/6. The bound above therefore gives 0<=Q2(t,v)-w(t+v)<=228*w(t)*v^3/(6*t^3). For v=0 both sides vanish. The denominator is 3!=6 from this Lagrange remainder; the weaker taylor_mean_remainder_bound with its n! denominator does not by itself give this constant. The same signed inequality follows by integrating the third derivative comparison three times from the zero initial remainders.

For H>=0, d>0 and 0<=u<=H, integrate that density inequality on [u,H] and divide by w(t)*d>0. The exact density integral for K and the polynomial integral for P3 give 0<=P3(t,H,d,u)-K(t,H,d,u)<=(19/2)*(H^4-u^4)/(t^3*d), since 228/24=19/2. In particular the difference is at most (19/2)*H^4/(t^3*d). Integrating once more over u in [0,H] gives 0<=C3(t,H,d)-C_exact(t,H,d)<=(38/5)*H^5/(t^3*d), since integral from 0 to H of (H^4-u^4) du=4*H^5/5. Thus |C_exact-C3| obeys that same 38/5 bound, including H=0. These integrations use intervalIntegral.integral_mono_on, intervalIntegral.integral_comp_add_left and integral_pow at the fixed polynomial degrees.

Let L_R(t)=sum over q in J_R(t) of log(q). Each log(q) is nonnegative. Finite-sum and ordinary triangle inequalities, with the continuum bound, now give the shared pointwise estimate on S: |A(t)-B(t)|<=L_R(t)*(19/2)*H(t)^4/(t^3*d(t))+(38/5)*H(t)^5/(t^3*d(t)). Although both P3-K and C3-C_exact are nonnegative, they enter A-B with opposite signs. No favorable sign of the centered response is inferred.

## The sharper conditional 40 application

Under the unchanged original X,ell,R hypotheses, suppose in addition that L_R(t)<=3*H(t) for every t in S. Display the two ordinary integration premises as IntegrableOn A S and IntegrableOn B S. Then |integral over S of A(t) dt-integral over S of B(t) dt|<=40*ell^(-1/10)*M. The preceding integrability application discharges these two integration premises from the original bounds alone; the uniform 3*H mass premise remains an additional condition.

Indeed the shared estimate becomes |A(t)-B(t)|<=(57/2+38/5)*H(t)^5/(t^3*d(t)) =(361/10)*t^(-1/10)<=40*t^(-1/10). Here H(t)^5/(t^3*d(t))=t^(4-3-11/10)=t^(-1/10). Since t>=ell>0 on S, this is at most 40*ell^(-1/10). Integrability permits integral_sub; the norm-of-integral bound for volume restricted to S then multiplies this uniform constant by M. No division by M or positive-measure argument is used.

The condition L_R(t)<=3*H(t) is not supplied merely by ell>=243. A short-interval prime-counting estimate can imply it only after a common sufficiently late start for every t in S. In particular the Guth-Maynard short-interval application requires such a common start. Corollary 1.3 of Guth and Maynard, arXiv:2405.20552v2, covers x^(17/30+epsilon)<=y<=x^0.99 with error O_epsilon(y*exp(-(log(x))^(1/4))). Taking epsilon=1/60, x=t and y=H=t^(4/5) puts H between the lower exponent 7/12 and 0.99 for large t. The resulting prime-count asymptotic and log(t+H)/log(t) tending to one give L_R(t)<=log(t+H)*(pi(t+H)-pi(t))<=3*H after one sufficiently late start, independent of X, labelStart and R. No start equal to 243 is established here. This 40 estimate therefore keeps its explicit mass condition. It is separate from the elementary estimate below.

## The elementary 408 application and its scope

Without a prime-distribution premise, the same original hypotheses give |integral over S of A(t) dt-integral over S of B(t) dt|<=408*ell^(-1/20)*M. To derive its mass estimate, use the already established t<q<tau_q<=t+H for q in J_R(t). These primes lie in the integer interval Ioc(floor(t),floor(t+H)). Nat.card_Ioc, finite-set inclusion, and the floor bounds give card(J_R(t))<=floor(t+H)-floor(t)<=H+1<=2*H. The last inequality uses H=t^(4/5)>=1. Since q<=t+H<=2*t, logarithm monotonicity then gives L_R(t)<=2*H*log(2*t). The argument counts all integers in that interval, so uses no GM estimate.

Substitution into the shared pointwise estimate gives |A(t)-B(t)|<=(19*log(2*t)+38/5)*t^(-1/10). The pinned Real.log_le_rpow_div at positive exponent 1/20 gives log(t)<=20*t^(1/20). Together with log(2)<=1 and t^(1/20)>=1, this gives log(2*t)<=21*t^(1/20). Hence 19*log(2*t)+38/5<=(399+38/5)*t^(1/20)=(2033/5)*t^(1/20)<=408*t^(1/20). The resulting pointwise error is at most 408*t^(-1/20)<=408*ell^(-1/20) on S. The automatic ordinary integrability derived above and MeasureTheory.norm_integral_le_of_norm_le_const for volume restricted to S yield the stated full-domain inequality.

The calculus, counting and measure results cited in these applications are from Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679, as pinned by lake-manifest.json. The repository suppliers are the existing frozen OriginalFirstClockTransport, LogLogHigherDerivative, ArithmeticMixedCornerResponse, ActualRobinClockCovariance and DelayedAtomTransport sources. Their private integrability, primitive and derivative suppliers are used with exactly the parameter correspondences given above. The existing theorem descriptions retain their own Lean statements; the displayed cubic consequences are application exposition.

Both coefficients tend to zero as ell tends to infinity, the 40 coefficient under its mass condition. Thus the estimates control error per selected volume; when M>0 one may divide by M, and when M=0 both integrals vanish. For varying domains, including zero-volume degeneracies, no total-error convergence is asserted from the coefficient alone: that requires the product of the coefficient and M to tend to zero. The 408 estimate does not imply the sharper conditional 40 estimate numerically. The elementary application needs no supplied integrability, GM, positive volume or signed-response premise. Neither application supplies a favorable signed main term, cofinal original witnesses, EL.14, a compiled GM theorem, full Robin or RH; no novelty claim is made.

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

- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.canonical_source_spec`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_exclusion`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.complete_original_first_clock_transport`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_absent`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockTransport.first_clock_spec`
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
