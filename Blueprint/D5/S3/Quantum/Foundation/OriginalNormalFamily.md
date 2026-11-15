# Original normal positivity, common scale and sharp whole-face budgets

## Abstract

Original normal positivity, common scale and sharp whole-face budgets

V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.

**Theorem 1.1 (Exact whole-cone support threshold).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to closedness, strict positivity, generation and EB, assume Inj. Fix an original p, an entire chart a, ep in its full zero-confirming fiber, and Coordinates k supplied by the original restriction owner in the singleton branch. Set g=u-ep, D(v)=directionLift(k,v), and normalForm(k,alpha,v)=alpha g+D(v) as an original linear functional on all V. rho(k,v) is the supremum of -D(v)(x)/g(x) over every x in K except p. For every unit v the supremum is bounded, rho>=1, and normalForm is nonnegative on all C exactly when alpha>=rho. No positivity is inferred from an upper bound.

**Theorem 1.2 (Maximum after positivity is established).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume closedness, strict positivity and generation, with p,a,ep,k as above. For arbitrary real alpha and arbitrary vector v, if normalForm is nonnegative on the entire C, its value on all K is at most alpha+norm(v), and this value is attained at an actual point of the whole D(p). This uses the existing positive-annihilator maximum owner and the original chart formula. The positivity premise is indispensable.

**Theorem 1.3 (Actual neighboring confirmer and antipode).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under EB and Inj, for every original unit v and original pure q=a(v), the entire full zero-confirming fiber at q is a singleton eq. With lambda=1/(1+rho(k,v)), 0<lambda<=1/2 and eq(x)=(1-lambda)g(x)+lambda D(v)(x) for every x in V. At the actual old antipode a(-v), eq equals (rho-1)/(rho+1), and this antipode belongs to the whole D(q) exactly when rho=1. The exact original neighbor-uniqueness, lift and domination owners are consumed, preserving their proofs.

**Theorem 1.4 (Unique actual linear coordinate map).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Coordinates k of the actual original normal restriction, coordinateMap(k) is a linear H from all V to the chart coordinate space. H(p)=0, H(a(z))=z for every coordinate z, and every scalar component inner(v,H(x)) is represented by an element of the actual normal span. Among all original linear maps with those normal-span components and the same whole-chart values, H is unique. The construction uses inverse Riesz representation of the actual inverse-restriction direction lifts. In original_row_saturation, k is obtained from original_coordinates under EB3, Inj and the exact singleton full zero-confirming fiber; Coordinates is not supplied as a desired output of that theorem.

**Theorem 1.5 (Full opposite edge interval).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under EB and Inj with the same actual normal data, every original proper b with b(p)=0 and b(q)=1 is exactly (1-s)(u-ep)+s eq for some s in [0,1], as an equality of functionals on the entire V. Conversely every such convex combination is proper and has those endpoint readings. A common actual zero point different from p bounds the coefficient by the unique neighboring confirmer coefficient.

**Theorem 1.6 (Complete fixed edge J(p,q)).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original data, the entire original edge of proper e with e(p)=1 and e(q)=0 is exactly e=(1-s)ep+s(u-eq), s in [0,1], on all V. This is the complement of the full opposite edge, retaining every original effect. original_row_saturation consumes this interface to turn exact fixed-edge attainment into the pure-row minimum.

**Theorem 1.7 (Pure row to a genuinely positive original effect).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original normal data, a proper full confirmer eq at q, a positive lambda, its whole-V normal formula, and the exact pure-row equality T(p,s)=min(ep(s),(u-eq)(s)) for every original pure s. The theorem proves that b=(g+D(v))/2 is proper on all C, b(p)=0, b(q)=1 and b(a(-v))=0; hence the actual old antipode belongs to D(q). The proof first obtains whole-C positivity by perturbing g in the direction of H(s). Direction domination pays positivity, and only then the whole-base maximum normalizes the perturbation into an actual effect. Complementing that effect uses the entire F(p). A negative reading of g+D(v) contradicts the exact pure row. The pure-row premise is a required protected join and is not asserted for an actual collapse by this module.

**Theorem 1.8 (Common scale on the whole ball).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_ball_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_ball_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume closedness, strict positivity, generation, EB and pure reciprocity. For every pure p and every finite nondegenerate ExclusionChart a of its entire D(p), there is one t with 0<t<=1/2. For every unit direction v and pure q=a(v), a single original confirming effect e of q has e(a(z))=1-t+t inner(v,z) for every z in the whole affine chart. The same e attains T(q,a(z)) for every mixed coordinate with norm(z)<=1. No Inj or singleton confirming fiber is assumed. The proof chooses an actual minimizing effect at the antipode, uses the original peak formula, and compares distinct pure directions using PR. Strict endpoint exposure rules out zero scale.

**Theorem 1.9 (Attained optimal original budget).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_and_sharp_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_and_sharp_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same original hypotheses and arbitrary chart, choose the same common t as in the whole-ball law. For each unit v, BudgetFeasible(a,v,M) means M>=0 and an actual original linear g obeys 0<=g<=M u on all C and g(a(z))=(1+inner(v,z))/2 on the entire closed ball. extensionBudget is the infimum of this actual feasible set. The theorem supplies feasibility at 1/(2t), proves every feasible M is at least 1/(2t), and identifies the infimum with this value. The set is proved nonempty and bounded below. The attaining extension is the complement of an actual antipodal confirmer scaled by 1/(2t). For any competing g, its complementary normalized original effect supplies the reverse inequality; the budget is not defined to be a reciprocal.

**Theorem 1.10 (All affine positive functions and sharp common family budget).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_full_face_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_full_face_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original hypotheses and an arbitrary full chart, one common t gives the directional attained optimum. Every affine h on the coordinate space that is nonnegative on the closed unit ball has an actual linear extension g nonnegative on the entire C. If h is also at most one on that ball, this same g is at most u/(2t) on all C. Conversely every real B that supplies such bounded positive lifts for every affine face effect must satisfy 1/(2t)<=B. The Riesz representation h=c+inner(b,z), c>=norm(b), produces the lift (c-norm(b))u+2 norm(b)g(b/norm(b)); constant h is treated separately. The directional face effects give sharpness. No simultaneous joint instrument or unital positive linear extension operator is asserted.

The literal individual-optimum formulation uses H, all affine h between zero and one on the entire closed coordinate ball. For each h, let J(h) be the infimum, over all original positive linear extensions g of h, of max over x in K of g(x). Then sup over h in H of J(h) equals 1/(2t). Compactness of K makes each maximum finite and attained. The common bounded lifts give J(h)<=1/(2t) for every h. For an actual directional face effect h(z)=(1+inner(v,z))/2, every positive extension has maximum at least 1/(2t), because that maximum is an admissible directional budget; the supplied sharp extension attains equality. Thus the family supremum and this individual optimum are both attained. This is an application of the sharp full-family theorem, with no additional retained binding declaration.

**Theorem 1.11 (Intrinsic optimality under arbitrary charts).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_chart_independence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_chart_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two complete charts a and b of the same original D(p), there is one positive t<=1/2 such that extensionBudget(a,v)=1/(2t) for every unit direction of a and extensionBudget(b,w)=1/(2t) for every unit direction of b. Whole face-effect lifts transport through actual original linear extensions and the equality of the two complete chart images. Sharpness in both directions identifies the numerical optima; no orthogonal coordinate change is supplied as an assumption.

**Theorem 1.12 (One coefficient in every chart and every mixed input).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_chart_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_chart_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any reference chart of D(p). One t>0, t<=1/2 works in every complete chart b of that same D(p), in every unit direction v, and at every original pure q=b(v). The reciprocal budget is feasible and optimal and equals the actual infimum. An actual confirmer of q realizes the affine formula on the whole chart and the comparison formula on every mixed coordinate in its closed unit ball. Chart independence of the optimum identifies the coefficients in all charts. The theorem does not identify scales of different original exclusion faces.

**Theorem 1.13 (All mixed inputs of every pure row).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity and generation give one finite L>0 such that abs(T(p,x)-T(p,y))<=L norm(x-y) for every original pure p and all original mixed x,y in K. This consumed helper directly uses the original frozen CommonOldExclusionConfirmation.comparison_lipschitz owner, enlarging its bound to a positive constant. It provides no independent new mathematical content or escape witness. Neither EB nor PR nor Inj is needed.

**Theorem 1.14 (Universal actual scale-to-axis estimate).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, one L>0 works at every original pure p and every complete chart a. A positive common scale t<=1/2 has extensionBudget(a,v)=1/(2t) in every unit direction and 2t<=L norm(a(v)-a(-v)). These are the same actual comparison coefficient and original optimal budget, using all mixed inputs of the original scale owner.

**Theorem 1.15 (Finite budget on arbitrary whole-P label sets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any set U of original pure labels and real B>0, assume every actual chart and unit direction at every p in U has extensionBudget<=B. There is a single delta>0 with delta<=diam(D(p)) for all p in U, explicitly delta=1/(B L) for the universal comparison bound. U is an arbitrary subset of the entire P; it may be a neighborhood containing labels outside P0. This is the noncollapse direction of the local-budget argument. The reverse implication is provided by original_noncollapse_bounded_budget, and original_local_budget_iff combines them in open neighborhoods of all P.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_ball_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_chart_independence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_chart_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_full_face_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_and_sharp_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff`
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalRegularHeight](OriginalRegularHeight.md)
- Dependency: [D5/S3/Quantum/Foundation/ReciprocalEndpointExposure](ReciprocalEndpointExposure.md)
