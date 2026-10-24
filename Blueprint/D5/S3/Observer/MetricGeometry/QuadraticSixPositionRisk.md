# Six-Position Quadratic Risk

## Abstract

The joint strip polygon determines the exact raw deterministic risk of the six-position quadratic clock.

**Definition 1.1 (The complete fixed design).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The design full contains all original positions I={0,1,2,8,9,10}, with their original natural coordinate labels.

**Definition 1.2 (The algebraic diameter envelope).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.envelope`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.envelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real c and K, envelope(c,K) is max{c/10,c*(K+9)/(90+2*c),c*(K+7)/(72+2*c),c*K/(16+2*c)}. In the original experiment c=2*epsilon/m>0 and K=H+|s|. The prior truncation uses H, not K.

**Definition 1.3 (Slopes for deleted coordinates).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionSlope`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original coordinate p, deletionSlope(p) equals 11,2,9,11,18,9 when p is respectively 0,1,2,8,9,10. These slopes define a common quadratic difference on every coordinate of full with p removed.

**Definition 1.4 (Joint ranges on deletion designs).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionRange`

*Formalization.* `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original coordinate p, deletionRange(p) is 80 for p=1 or 9, 18 for p=2 or 8, and 14 for p=0 or 10. It bounds the entire range of i^2-deletionSlope(p)*i simultaneously over the remaining original coordinates.

**Theorem 1.5 (Lower bounds after any one deletion).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletion_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletion_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m>0,epsilon>0,H,s and every original position p, put c=2*epsilon/m, l=deletionSlope(p), and w=deletionRange(p). Then minimaxRisk(m,epsilon,H,s,full without p) is at least ofReal(min{H,c*(H+|s+l-10|)/(w+2*c)}/2). For H>0, the bound comes from two finite original worlds with the same raw reports on the deletion design. Put U=4*epsilon/w and V=-l*U. The full joint range inequality gives Strips(epsilon,J,U,V). If s*U-(10*U+V)>=0, place the origins at b-d and b, and take Aprime=(2*U*(b-d)-V)/(2*d), A=Aprime+U. Otherwise place them at a and a+d, reverse the coefficient pair, and take A=(-2*U*(a+d)+V)/(2*d), Aprime=A+U. Here a=-5+(s-H)/2, b=-5+(s+H)/2 and d is the displayed truncated diameter. The fraction bound makes both gains at least m. The exact common-offset reconstruction and opposite half-difference noises then give two legal full six-coordinate worlds. All selected coordinates share the same calibration in each world; unobserved noise coordinates can be zero. The inequality does not replace the joint raw noise cube by independent difference errors.

**Theorem 1.6 (A prior bound on every finite calibration pair).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.calibration_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.calibration_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real m,H,s,u,v,A,Aprime, suppose u and v lie in [-5+(s-H)/2,-5+(s+H)/2], u<=v, and A,Aprime>=m. Put U=A-Aprime and W=10*U+2*(A*u-Aprime*v). Then 2*(m+|U|)*(v-u)<=(H+|s|)*|U|+|W|. For U>=0 use m+U<=A and the upper prior endpoint for v; for U<=0 use m-U<=Aprime and the lower endpoint for u. The estimate holds for every finite gain pair and does not assume any noise or risk formula.

This estimate also connects sparse original reports to the full raw risk. Fix C={0,2,8,10} and T={0,2,10}. The joint strips on C give 2*|U|+|W|<=epsilon/2 by comparing coordinates 10 with 2 and 0 with 8, in both orders. The joint strips on T give 8*|U|+|W|<=2*epsilon by comparing 10 with 2 and 0 with 2, in both orders. Thus the four-coordinate argument uses coordinate 8 in addition to the three-coordinate design.

Write k=2 for C and k=8 for T. In either case k*|U|+|W|<=epsilon*k/4. For any compatible ordered pair let d=v-u and r=H+|s|-2*d; the prior gives d<=H, and the calibration estimate gives 2*m*d<=r*|U|+|W|. Assume m>0, epsilon>0, and |s|>=k+epsilon*k/(8*m). If r<k, the joint bound forces d<=epsilon*k/(8*m), while d<=H implies r>=|s|-d>=k, a contradiction. Hence r>=k. Multiplying the joint bound by r/k and using |W|>=0 gives r*|U|+|W|<=epsilon*r/4. Therefore d<=epsilon*(H+|s|)/(8*m+2*epsilon).

Let c=2*epsilon/m and q=c*(H+|s|)/(16+2*c), the last candidate in envelope(c,H+|s|). The exact raw minimax identity and the prior give the sparse upper bound ofReal(min{H,q}/2). Since q<=envelope(c,H+|s|), the full-risk formula and projection monotonicity make this bound an equality with the full raw risk. Consequently the same fixed C preserves the full risk for every H>0 whenever |s|>=2+c/8, and the same fixed T does so whenever |s|>=8+c/2. Equality at either threshold is included. For fixed c and t at these thresholds, take s=t or s=-t separately; each recovery rule may use its own known H,s, while the design is independent of H and reports. This conclusion concerns the original joint six-coordinate noise cube and all total deterministic rules. It supplies preservation upper bounds and asserts no minimal report count.

**Theorem 1.7 (Exact risk from the original joint raw reports).**

Lean statement: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full_risk`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full_risk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m>0,epsilon>0,H>0 and every signed real s, let c=2*epsilon/m and K=H+|s|. Then minimaxRisk(m,epsilon,H,s,full)=ofReal(min{H,envelope(c,K)}/2). The risk is the infimum over all total deterministic recovery rules of their worst-case absolute origin errors in the original joint six-coordinate noise cube. Each world has one finite common gain at least m and one free real zero; distinct worlds can choose different calibrations. The prior remains [-5+(s-H)/2,-5+(s+H)/2].

For the upper bound, write U=A-Aprime, V=2*(A*u-Aprime*v), and W=10*U+V. The joint strips on the original six positions imply 10*|W|<=4*epsilon, 9*|U|+9*|W|<=4*epsilon, and 16*|U|+8*|W|<=4*epsilon. For ordered compatible origins u<=v, calibration and prior bounds give 2*(m+|U|)*(v-u)<=(H+|s|)*|U|+|W|. The support of this polygon bounds the right side by 2*envelope(c,K)*(m+|U|). One obtains this support inequality by splitting r=K-2*envelope(c,K) at 0,1,2 and taking nonnegative combinations of the three joint inequalities. Thus every compatible gap is at most the envelope, and the prior bounds it by H.

For the matching lower bound, the span coefficient U=0,V=-2*epsilon/5 gives c/10. Slopes 1 and 19 have joint range 90, slopes 3 and 17 have range 72, and slope 10 has range 16. The finite calibration construction used for deletion bounds applies to every one of these full-design slopes. Choose the reflected member of each pair according to the known sign of s; the resulting candidate diameters are exactly c*(K+9)/(90+2*c), c*(K+7)/(72+2*c), and c*K/(16+2*c). Their maximum and the span candidate give the displayed risk through the exact raw minimax identity. Every positive truncated candidate has finite common-world realizations. No infinite-gain endpoint is used. The two signs are separate known-prior experiments.

The full-risk law, the deletion bounds and the sparse calibration inequalities together determine the least number of reports in one design serving every width and both separately known signs. Fix c>0 and t>=0. A design J is selected using only c,t, before H and the reports. Require R_J(H,s)=R_I(H,s) for every H>0 and each s=-t or s=t, where R denotes the original raw deterministic minimax risk and c=2*epsilon/m. Each experiment and its recovery rule retain their known H,s. Let M be the least cardinality among such designs. Then M=6 for 0<=t<2+c/8, M=4 for 2+c/8<=t<8+c/2, and M=3 for t>=8+c/2. The respective designs are I, C={0,2,8,10}, and T={0,2,10}. Thus both threshold equalities belong to the region with fewer reports. The same chosen design works for every positive m,epsilon realizing the fixed ratio c.

For sufficiency, full always preserves itself. The calibration inequalities give preservation by C when |s|>=2+c/8 and by T when |s|>=8+c/2, for every H>0, including equality. As |s|=t for each of the two known signs, these fixed choices satisfy the required outer design quantifier. No choice depends on H, on a recovered origin, or on a report.

For necessity put h1=1+2*c/9, h2=2+c/4, h3=8+c, u2=2+c/8, and u3=8+c/2. Write D(K)=envelope(c,K), FA(K)=c*(K+7)/(72+2*c), and FC(K)=c*K/(16+2*c). Direct comparison of the positive denominators gives D(K)=FA(K) on h1<=K<=h2 and D(K)=FC(K) on K>=h2. The endpoint values are D(h2)=c/8 and D(h3)=c/2.

Suppose t<u2. Take delta2=min{(h2-h1)/2,(u2-t)/2}, K2=h2-delta2, and H2=K2-t. Both entries of the minimum are positive. Hence h1<K2<h2, D(K2)>0, D(K2)<=c/8, and H2>c/8; in particular 0<D(K2)<H2. For each deleted position p, choose s=t when deletionSlope(p)-10>=0 and s=-t otherwise. Then |s|=t and H2+|s+deletionSlope(p)-10|=K2+|deletionSlope(p)-10|. For p=0,1,2,8,9,10 the resulting deletion candidates are respectively E0,E1,E2,E2,E1,E0, where E0=c*(K2+1)/(14+2*c), E1=c*(K2+8)/(80+2*c), and E2=c*(K2+1)/(18+2*c). On this strict interval E1>FA(K2) is equivalent to K2<h2, E2>FA(K2) is equivalent to K2>h1, and E0>E2. Every one of the six deletions therefore has a strictly larger risk for one of the separately known signs.

If a design J omits p, it is a subset of I without p. Projection monotonicity gives R_J>=R_(I without p). Since H2>D(K2), the inequality E>D(K2) also gives min{H2,E}>D(K2), so truncation preserves the strict risk loss. Any design preserving both signs at every width must consequently contain all six positions. This proves the first lower bound for every subset, including subsets with zero, one or two reports, without enumerating their experiments.

Suppose t<u3. Take delta3=min{(h3-h2)/2,(u3-t)/2}, K3=h3-delta3, and H3=K3-t. Now h2<K3<h3, 0<D(K3)<=c/2<H3. For each p in C choose the known sign by the same rule. Deleting 0 or 10 gives E0=c*(K3+1)/(14+2*c), which exceeds E2=c*(K3+1)/(18+2*c). Deleting 2 or 8 gives E2. The inequality E2>FC(K3) is equivalent to K3<h3. Thus every preserving design must contain C, by the same strict truncation and projection argument. Its cardinality is at least four. Combined with C sufficiency this proves the middle region, including its lower closed endpoint.

Finally, for every t>=0 choose Hinf=h3+(1+c/4)*t+1. Then Hinf>0, K=Hinf+t>h3, and c*t<8*Hinf. Therefore D(K)=FC(K)<Hinf/2 and R_I(Hinf,t)<Hinf/4. The law few_reports_floor in QuadraticRawReportRecovery gives R_J(Hinf,t)>=Hinf/4 for every J of cardinality at most two. No such design serves all widths, so every preserving design has at least three reports. The proof of that floor takes a supremum over finite compatible gaps strictly below Hinf/2; the argument uses this risk bound without requiring attainment of the limiting gap. Combined with T sufficiency it proves the last region, including t=u3.

The classification concerns only subsets of the original six positions, positive noise, free real offsets, one finite common gain per world, and the original joint noise cube. Distinct worlds may have different calibrations. The raw minimax and common-report laws derive the risk from these worlds and all total deterministic rules; the envelope is their consequence. The two known priors are never combined into one experiment with unknown sign, and the rule is allowed to depend on its known width. The strict positive widths above establish all report-count lower bounds before any truncation can erase a loss. No assertion is made about optimizing other sampling positions, acquisition costs, zero noise, or a design independent of c,t.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.calibration_bound`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionRange`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletionSlope`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.deletion_lower`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.envelope`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full`
- Truth anchor: `D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk.full_risk`
- Dependency: [D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery](QuadraticRawReportRecovery.md)
