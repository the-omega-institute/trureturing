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
