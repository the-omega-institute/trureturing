# Exact Three-Index Quadratic Separation

## Abstract

Two independently calibrated quadratic report families have an exact attained separation in the original three-coordinate supremum norm.

**Definition 1.1 (Original observation space).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Reports`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Reports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reports is the space of all functions from Fin 3 to the real numbers, with the ordinary Pi norm: the maximum absolute value of the three coordinates.

**Definition 1.2 (Three indices).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.nodes`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.nodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u and v, nodes(u,v) has coordinates zero, u and v, in that order. The separation theorem restricts u and v to natural numbers with 1 <= u < v.

**Definition 1.3 (Independently calibrated reports).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.report`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.report` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,t,A,B and j in Fin 3, report(u,v,t,A,B)(j) is A times the square of nodes(u,v)(j)+t, plus B. A and B belong to this report's world; the other world has its own gain and offset.

**Definition 1.4 (Right directional coefficient).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kRight`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,r, kRight(u,v,r) equals u*v/(u+2*r) when r <= (v-u)/2, and u*(v-u)/(2*r) otherwise. On the theorem's domain r >= 0 and 0 < u < v, the denominators are positive in their respective branches. At r=(v-u)/2 both displayed value formulas agree.

**Definition 1.5 (Left directional coefficient).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kLeft`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,r, kLeft(u,v,r) equals (v-u)*v/(v-u+2*r) when r <= u/2, and u*(v-u)/(2*r) otherwise. On the theorem's domain both branches have positive denominators. At r=u/2 both displayed value formulas agree. The internal spacing is reflected, so the two directional functions cannot be exchanged while keeping u fixed.

**Definition 1.6 (Sharp separation value).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.sharpValue`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.sharpValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,m,s,t, put d=t-s, rR=max(s+v/2,0) and rL=max(-t-v/2,0). The value sharpValue(u,v,m,s,t) is m*d times the minimum of kRight(u,v,rR) and kLeft(u,v,rL).

**Definition 1.7 (Exact offset from the full difference).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.center`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any three-coordinate real vector q, center(q) is minus one half of the sum of its largest and smallest coordinate. Both extrema use all three coordinates. In each attaining construction q is the full report(u,v,s,A,0)-report(u,v,t,A',0), including the constant quadratic terms. The offsets are exactly B=center(q) and B'=0.

**Definition 1.8 (All independently legal distances).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.distances`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.distances` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,m,s,t, distances(u,v,m,s,t) contains exactly the norms of report(u,v,s,A,B)-report(u,v,t,A',B') over all real A,A',B,B' with A >= m and A' >= m. The offsets are unrestricted and independent. Neither gain has an upper bound.

**Definition 1.9 (A prescribed finite pair attains).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Attains`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Attains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real u,v,m,s,t,A,A', Attains asserts A >= m, A' >= m, and equality between sharpValue(u,v,m,s,t) and the norm of the two original reports with these gains and the exact offsets B=center(q), B'=0. It is a property of this particular gain pair, rather than an existentially selected alternative.

**Theorem 1.10 (Least separation and all five finite attaining choices).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.quadratic_three_index_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.quadratic_three_index_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u,v be arbitrary natural numbers with 1 <= u < v, and let m,s,t be arbitrary real numbers with m > 0 and s < t. Put w=v-u, d=t-s, rR=max(s+v/2,0), rL=max(-t-v/2,0). The set distances(u,v,m,s,t) has least element m*d*min(kRight(u,v,rR),kLeft(u,v,rL)). Thus every independently legal four-parameter calibration has at least this distance, and a finite calibration has exactly this distance.

The same theorem gives five separately accessible attaining implications. If s <= -v/2 <= t, take A=A'=m. If s > -v/2 and s+v/2 <= w/2, take A'=m and A=m*(1+d*2/(u+2*(s+v/2))). If s > -v/2 and w/2 <= s+v/2, take A'=m and A=m*(1+d/(s+v/2)). If t < -v/2 and -t-v/2 <= u/2, take A=m and A'=m*(1+d*2/(w+2*(-t-v/2))). If t < -v/2 and u/2 <= -t-v/2, take A=m and A'=m*(1+d/(-t-v/2)). Each implication asserts both gain inequalities and exact norm equality with its own full q and the offsets B=center(q), B'=0.

Both inequalities at each directional junction are closed. Consequently both prescribed gain pairs attain there, although their gains generally differ. At the right junction rR=w/2 the two z values are 2/v and 2/w; at the left junction rL=u/2 they are 2/v and 2/u. The two formulas for the value agree at each junction. Contacts with the center are included in the first implication. Equal and unequal spacings and arbitrary signed origins are all included.

For the right-hand lower bound write f=u*(u+2*s), g=v*(v+2*s), and e for the full original report difference. The exact cancellation identity (g-f)*e(0)-g*e(1)+f*e(2)=2*A'*(t-s)*u*v*(v-u) eliminates the other gain and both offsets. Each coordinate lies between minus and plus the Pi norm. When f <= 0 the absolute coefficient sum is 2*(g-f), and when f >= 0 it is 2*g. The resulting bounds use A' >= m. Across the center the endpoint difference gives the bound directly using both gain inequalities. Reflection of the original coordinates exchanges the worlds and replaces u by v-u, supplying the left-hand bound.

For the two right-hand constructions, subtracting q(0) gives respectively the patterns (0,-2*c,-2*c) and (0,-2*c,0), where c is the corresponding sharp value. Centering the full q therefore gives norm at most c, and the universal lower bound gives equality. Reflection supplies both left-hand constructions; centering the original full q remains optimal among all offsets. These are conditional mathematical statements about the original reports. They require no prior interval, noise, injectivity of an auxiliary coordinate map, measurability, computability, estimator, risk or operational interpretation, and make no classification of all minimizing calibrations.

Original worlds and exact risk.

Fix natural indices 1 <= u < v, real endpoints a < b, a gain floor m > 0, and epsilon >= 0. Set w=v-u, L=b-a and c=2*epsilon/m. An original world consists of an origin t in [a,b], a finite real gain A >= m, an unrestricted finite real offset B, and a vector eta with |eta(j)| <= epsilon for every j in Fin 3. Its observation is report(u,v,t,A,B)+eta. The gain, offset and three noise coordinates can be chosen independently in each of two worlds. The decision is any total function from Reports to the real numbers, with no measurability or computability requirement.

Put d0=c/v, dR=c*(u+v+2*b)/(u*v+2*c), eR=c*(v+2*b)/(u*w+2*c), dL=c*(-u-2*a)/(v*w+2*c), and eL=c*(-v-2*a)/(u*w+2*c). Let Psi=max(d0,max(dR,max(eR,max(dL,eL)))) and D=min(L,Psi). All five denominators are strictly positive. Signed numerators are retained: a directional fraction can be negative, while d0 >= 0 ensures Psi >= 0. The infimum, over all decisions, of the supremum absolute error over all original legal worlds is D/2.

Actual placement of a fixed origin gap.

For a gap 0 <= d <= L, minimize the original report distance over all s,t in [a,b] with t-s=d and all independently legal gains and offsets. Write Q=u*v*w. The least distance is F(d)=m*Q*d/M(d), where M(d)=max(u*w,max(w*(u+v+2*b-2*d),max(v*(v+2*b-2*d),max(u*(-u-2*a-2*d),v*(-v-2*a-2*d))))). The maximum includes the positive constant u*w, so division is legitimate.

To locate the actual origins, define H_R(x)=max(u*w,max(w*(u+2*x),2*v*x)) and H_L(x)=max(u*w,max(u*(w+2*x),2*v*x)). The directional formulas give kRight(u,v,max(x,0))=Q/H_R(x) and kLeft(u,v,max(x,0))=Q/H_L(x). Both H functions are nondecreasing. For any s,t with gap d, H_R(s+v/2) <= H_R(b-d+v/2) and H_L(-t-v/2) <= H_L(-a-d-v/2). Hence the fixed-pair separation is at least F(d). If the first endpoint denominator is the larger one, take (s,t)=(b-d,b); otherwise take (s,t)=(a,a+d). The selected pair has denominator exactly M(d). The attained fixed-pair separation then supplies finite legal gains and offsets at this actual pair. At d=0 take s=t=a and identical calibrations.

For every real d, the positive-denominator inequality F(d) <= m*c is equivalent to Q*d <= c*M(d). Because c >= 0, multiplication distributes over this maximum. Splitting the resulting maximum into its five alternatives and cancelling the positive factors u,v,w gives exactly d <= d0 or d <= dR or d <= eR or d <= dL or d <= eL. Thus the feasible gaps in [0,L] have largest element D, and the endpoint construction attains a clean-report distance at most 2*epsilon at gap D.

Exact compatible origins in the original coordinates.

For any y in Reports, let C(y) be the set of t in [a,b] for which finite real A >= m and B satisfy |y(j)-report(u,v,t,A,B)(j)| <= epsilon at every original coordinate. This is exactly the set of origins of legal worlds whose observation is y: in one direction use the actual noise, and in the other set eta(j)=y(j)-report(u,v,t,A,B)(j). No independent error bounds on interpolation coefficients are introduced.

Use lambda=1/A, xi=2*t and omega=(A*t^2+B)/A. The compatible triples are exactly the closed linear constraints 0 <= lambda <= 1/m, 2*a <= xi <= 2*b, and |lambda*y(j)-nodes(u,v)(j)^2-xi*nodes(u,v)(j)-omega| <= epsilon*lambda for all j. These constraints cannot have lambda=0. The coordinate at zero would force omega=0; the other two coordinates would then give u*(u+xi)=0 and v*(v+xi)=0. Since 0 < u < v, they would force xi=-u=-v, a contradiction.

Conversely every feasible triple has lambda > 0 and realizes the finite legal original parameters A=1/lambda, t=xi/2 and B=omega/lambda-(1/lambda)*(xi/2)^2. Dividing each original-coordinate inequality by lambda yields the required original noise bound. Substituting the forward parameters proves the reverse inclusion. Therefore C(y) is exactly the image of this feasible set under the map taking a triple to xi/2.

The feasible set is closed and convex. It is bounded in a compact box: lambda and xi already have their displayed bounds, and the coordinate at zero gives |omega| <= (|y(0)|+epsilon)/m. Its linear xi/2 image is consequently compact and convex. Whenever y is obtainable, C(y) is nonempty and equals the closed interval from its infimum to its supremum, including a singleton when the two endpoints coincide.

Midpoint optimality and finite worlds at the lower bound.

If s,t belong to C(y), choose their compatible original clean reports. Coordinatewise triangle inequalities bound their distance by 2*epsilon. The least-distance placement and five-alternative inequality imply |s-t| <= D. For an obtainable y, write ell=inf C(y) and h=sup C(y). The decision (ell+h)/2 has conditional error exactly (h-ell)/2. Every other real answer z has max(|z-ell|,|z-h|) >= (h-ell)/2. Thus the midpoint minimizes the worst conditional absolute error, and its global error is at most D/2. On unobtainable reports any total definition is permitted.

At the extremal gap D, choose the actual endpoint placement and finite calibrations just described, with clean original reports p0 and p1. Their distance is at most 2*epsilon. Set the shared report to (p0+p1)/2 and the respective noise vectors to (p1-p0)/2 and (p0-p1)/2. Each coordinate has absolute value at most epsilon. The two legal worlds share exactly the same report and have origins s,t with t-s=D. Every decision returns one real answer there, and at least one of its two absolute errors is at least D/2. The compatible interval at that report is exactly [s,t]: it contains both origins, is an interval, and has diameter at most D. If D=0, choose one legal world twice; the same conclusions hold. In particular epsilon=0 remains included.

The supremum of the error for an arbitrary decision is allowed to be infinite. Equivalently, take the supremum of ENNReal.ofReal of the absolute error over every original legal world and then the infimum over decisions. The two-world inequality gives a lower bound for every decision in this complete lattice, while the midpoint gives a finite upper bound. Both bounds are ENNReal.ofReal(D/2), which identifies the ordinary finite minimax value without assuming that every decision has bounded error. The argument concerns this mathematical observation model and makes no empirical or worldwide originality claim.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Attains`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.Reports`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.center`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.distances`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kLeft`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.kRight`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.nodes`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.quadratic_three_index_separation`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.report`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.sharpValue`
