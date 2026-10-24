# Raw Quadratic Report Recovery

## Abstract

Quadratic reports retain their original common calibration, joint noise cube and arbitrary deterministic recovery rules.

**Definition 1.1 (The six positions).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.positions`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.positions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sampling positions are exactly I={0,1,2,8,9,10}.

**Definition 1.2 (Original coordinate labels).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Index`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An Index is a natural number in I, retaining its original numerical sampling position.

**Definition 1.3 (Every original report subset).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Design`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Design` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A design J is any finite subset of the original six coordinates, including the empty subset. A design is selected independently of the actual raw reports.

**Definition 1.4 (The complete raw report domain).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Reports`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Reports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every design J, Reports(J) consists of all real functions on J, including reports incompatible with every legal world.

**Definition 1.5 (Known signed prior).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.prior`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.prior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary real H and s, prior(H,s) is the closed interval [-5+(s-H)/2,-5+(s+H)/2]. In the clock experiment H>0. Its center is -5+s/2 and its length is H. For positive m and epsilon the normalized noise parameter is c=2*epsilon/m; this normalization does not alter the worlds or the raw noise vector.

**Definition 1.6 (Finite common calibrations and joint noise).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.World`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.World` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A world consists of real tau, gain and zero, and one function noise from I to the real numbers. Every report in this world shares the same finite gain and zero. Two worlds may choose them independently. No coordinate has its own gain or offset.

**Definition 1.7 (The original legal worlds).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Legal`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Legal(m,epsilon,H,s,w) means that w.tau belongs to prior(H,s), w.gain>=m, and |w.noise(i)|<=epsilon for every one of the six original coordinates i. The source experiment assumes m>0, epsilon>0 and H>0. The auxiliary recovery results also include nonnegative epsilon.

**Definition 1.8 (Noiseless raw reports).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.signature`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real t,A,B and original coordinate i, signature(t,A,B)(i)=A*(i+t)^2+B. No report difference or coefficient error is substituted for this observation.

**Definition 1.9 (A projected raw experiment).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.observe`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.observe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a design J and a world w, observe(J,w)(i)=w.gain*(i+w.tau)^2+w.zero+w.noise(i) for i in J. The noise vector remains defined and bounded on all six original coordinates. Selecting J only projects that vector and the raw signature.

**Definition 1.10 (Every total deterministic rule).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Rule`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Rule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every design J, Rule(J) consists of all total functions from Reports(J) to the real numbers. The rule may depend on the known experiment parameters; there is no regularity or computability restriction.

**Definition 1.11 (Worst-case loss of an arbitrary rule).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.risk`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.risk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real m,epsilon,H,s, design J and total deterministic rule delta, risk is the supremum over all Legal(m,epsilon,H,s,w) of ofReal(|delta(observe(J,w))-w.tau|). This supremum is taken in the extended nonnegative reals, so an individual rule can have infinite risk. There is no measurability, continuity, computability or stochastic-noise restriction.

**Definition 1.12 (Original deterministic minimax risk).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.minimaxRisk`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.minimaxRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every parameter tuple and design J, minimaxRisk is the infimum of risk(m,epsilon,H,s,J,delta) over every total deterministic rule delta. Each experiment has its own known H and s. Comparing s=-t and s=t concerns separate known-prior experiments, and does not mix their world sets.

**Definition 1.13 (Actual compatible origins).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every raw report y on J, compatible(m,epsilon,H,s,J,y) consists of the real t for which some legal original world w has w.tau=t and observe(J,w)=y. This definition neither assumes the fiber is closed nor assumes it is an interval.

**Definition 1.14 (A total midpoint rule).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.midpointRule`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.midpointRule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a nonempty compatible set S, midpointRule returns (inf S+sup S)/2. On an empty compatible set it returns the prior center -5+s/2. Thus the rule is defined even at impossible reports. Infimum and supremum do not require the endpoints to belong to S.

**Definition 1.15 (Independent calibrations on the same raw coordinates).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.PairCompatible`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.PairCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real m,epsilon,u,v and design J, PairCompatible means that there exist finite real A,Aprime,B,Bprime with A>=m and Aprime>=m such that |signature(u,A,B)(i)-signature(v,Aprime,Bprime)(i)|<=2*epsilon for every i in J. Both offsets are free, but each remains common to its own world.

**Definition 1.16 (Joint coefficient strips).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Strips`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Strips` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real epsilon,U,V and design J, Strips means q(i)-q(j)<=4*epsilon for every ordered pair i,j in J, where q(i)=U*i^2+V*i. These simultaneous inequalities retain the original coordinate correlations. They are not independent bounds on U and V.

**Definition 1.17 (A supremum of finite common-world half-gaps).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.ambiguityRadius`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.ambiguityRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m,epsilon,H,s,J, ambiguityRadius is the extended nonnegative supremum of ofReal(|u-v|/2) over u and v in prior(H,s) satisfying PairCompatible(m,epsilon,J,u,v). Every member has finite calibrations. The definition makes no claim that a maximizing pair exists, and does not define the minimax risk.

**Theorem 1.18 (Projected noise is exactly the original cube projection).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m,epsilon,H,s with epsilon>=0, every design J, every raw report y on J and every real t, t is compatible with y if and only if t belongs to prior(H,s) and there exist finite real A,B with A>=m and |y(i)-signature(t,A,B)(i)|<=epsilon for every i in J. To extend the projected residuals to a legal original noise vector, use those residuals on J and zero on every unobserved original coordinate. Conversely, an actual world supplies its own common A and B.

**Theorem 1.19 (Finite two-world reconstruction).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.common_report_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.common_report_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m,epsilon,H,s with epsilon>=0, every design J and real u,v, there exist two legal original worlds w,wprime with origins u,v and exactly the same projected raw report if and only if u,v belong to prior(H,s) and PairCompatible(m,epsilon,J,u,v) holds. In the reverse direction the common report is the coordinatewise midpoint of the two noiseless signatures. The two noises on J are opposite half-differences, extended by zero outside J. Both full six-coordinate noise vectors satisfy the original closed cube constraints, and the supplied finite gains and offsets remain common within each world.

**Theorem 1.20 (Exact elimination and reconstruction of one common constant).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.pairCompatible_iff_strips`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.pairCompatible_iff_strips` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real m,epsilon,u,v and every design J, PairCompatible(m,epsilon,J,u,v) holds if and only if there exist finite A,Aprime>=m such that Strips(epsilon,J,A-Aprime,2*(A*u-Aprime*v)) holds. The forward implication subtracts two bounded coordinate differences. For the reverse implication put U=A-Aprime, V=2*(A*u-Aprime*v), q(i)=U*i^2+V*i and S={q(i):i in J}. When J is nonempty, set C=-(inf S+sup S)/2, B=C-A*u^2+Aprime*v^2 and Bprime=0. The bounded-set midpoint inequality gives |q(i)+C|<=2*epsilon simultaneously at all selected coordinates. The same finite A,Aprime and these two finite offsets then satisfy the original raw bounds. If J is empty no coordinate constraint remains. No independent-coordinate calibration or coefficient-noise cube is introduced.

**Theorem 1.21 (Exact raw recovery and a finite attained minimax value).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.raw_minimax`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.raw_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m,epsilon,H,s with epsilon>=0 and every design J, minimaxRisk equals ambiguityRadius. The risk of the total midpointRule equals that same value. Moreover minimaxRisk<=ofReal(H/2) and minimaxRisk is strictly below infinity. These statements apply in particular to all m>0,epsilon>0,H>0 and every signed s in the original experiment. The lower bound tests an arbitrary total rule on each pair of legal finite worlds with one common raw report: one of the two errors is at least half their origin gap. The upper bound applies the bounded-set midpoint inequality to each actual compatible set, which is bounded by the original prior. The argument uses neither closed fibers nor attainment of the supremum of pair gaps. Minimax attainment refers to the midpoint recovery rule, and does not assert an attaining world pair.

**Theorem 1.22 (Projection cannot improve recovery).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.projection_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.projection_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m,epsilon,H,s and every two fixed designs J and K with J contained in K, minimaxRisk(m,epsilon,H,s,K)<=minimaxRisk(m,epsilon,H,s,J). A rule on J is extended to K by discarding the other coordinates of the actual raw report. The original world, common calibration and joint noise vector are the same on both sides.

**Theorem 1.23 (At most two reports leave a quarter-width lower floor).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.few_reports_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.few_reports_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m>0, epsilon>=0, H>0 and real s, every design J of cardinality at most two has minimaxRisk(m,epsilon,H,s,J)>=ofReal(H/4). To see the finite-world meaning, contain J in a pair {p,q}, allowing p=q. Its response changes sign at k=-(p+q)/2. For every 0<d<H/2, one can place two origins at distance d in the upper or lower half of the prior, strictly on the same side of k. Write M=|u-k|+|v-k| and take A=m*M/|u-k| and Aprime=m*M/|v-k|. These are finite and at least m; their signed responses balance exactly. A single offset difference then makes both raw coordinates identical. Extending zero noise to the remaining original coordinates gives legal finite common worlds. Every rule therefore has risk at least d/2. Taking the supremum as d approaches H/2 gives H/4; no limiting finite endpoint world pair is asserted. Projection transfers this lower bound from the containing pair to J. The bound also covers zero or one report, without identifying their larger exact risks.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Design`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Index`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Legal`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.PairCompatible`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Reports`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Rule`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.Strips`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.World`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.ambiguityRadius`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.common_report_iff`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.compatible_iff`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.few_reports_floor`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.midpointRule`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.minimaxRisk`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.observe`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.pairCompatible_iff_strips`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.positions`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.prior`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.projection_monotone`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.raw_minimax`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.risk`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery.signature`
- Dependency: [D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper](../../Analytic/OptimalRecovery/PointwiseMinimaxUpper.md)
