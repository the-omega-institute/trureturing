# Intrinsic original ball scale and optimal positive extensions

## Abstract

Intrinsic original ball scale and optimal positive extensions

V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.

**Theorem 1.1 (Common scale on the whole ball).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_ball_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_ball_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume closedness, strict positivity, generation, EB and pure reciprocity. For every pure p and every finite nondegenerate ExclusionChart a of its entire D(p), there is one t with 0<t<=1/2. For every unit direction v and pure q=a(v), a single original confirming effect e of q has e(a(z))=1-t+t inner(v,z) for every z in the whole affine chart. The same e attains T(q,a(z)) for every mixed coordinate with norm(z)<=1. No Inj or singleton confirming fiber is assumed. The proof chooses an actual minimizing effect at the antipode, uses the original peak formula, and compares distinct pure directions using PR. Strict endpoint exposure rules out zero scale.

**Theorem 1.2 (Attained optimal original budget).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_and_sharp_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_and_sharp_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same original hypotheses and arbitrary chart, choose the same common t as in the whole-ball law. For each unit v, BudgetFeasible(a,v,M) means M>=0 and an actual original linear g obeys 0<=g<=M u on all C and g(a(z))=(1+inner(v,z))/2 on the entire closed ball. extensionBudget is the infimum of this actual feasible set. The theorem supplies feasibility at 1/(2t), proves every feasible M is at least 1/(2t), and identifies the infimum with this value. The set is proved nonempty and bounded below. The attaining extension is the complement of an actual antipodal confirmer scaled by 1/(2t). For any competing g, its complementary normalized original effect supplies the reverse inequality; the budget is not defined to be a reciprocal.

**Theorem 1.3 (All affine positive functions and sharp common family budget).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_full_face_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_full_face_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original hypotheses and an arbitrary full chart, one common t gives the directional attained optimum. Every affine h on the coordinate space that is nonnegative on the closed unit ball has an actual linear extension g nonnegative on the entire C. If h is also at most one on that ball, this same g is at most u/(2t) on all C. Conversely every real B that supplies such bounded positive lifts for every affine face effect must satisfy 1/(2t)<=B. The Riesz representation h=c+inner(b,z), c>=norm(b), produces the lift (c-norm(b))u+2 norm(b)g(b/norm(b)); constant h is treated separately. The directional face effects give sharpness. No simultaneous joint instrument or unital positive linear extension operator is asserted.

The literal individual-optimum formulation uses H, all affine h between zero and one on the entire closed coordinate ball. For each h, let J(h) be the infimum, over all original positive linear extensions g of h, of max over x in K of g(x). Then sup over h in H of J(h) equals 1/(2t). Compactness of K makes each maximum finite and attained. The common bounded lifts give J(h)<=1/(2t) for every h. For an actual directional face effect h(z)=(1+inner(v,z))/2, every positive extension has maximum at least 1/(2t), because that maximum is an admissible directional budget; the supplied sharp extension attains equality. Thus the family supremum and this individual optimum are both attained. This is an application of the sharp full-family theorem, with no additional retained binding declaration.

**Theorem 1.4 (Intrinsic optimality under arbitrary charts).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_chart_independence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_chart_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two complete charts a and b of the same original D(p), there is one positive t<=1/2 such that extensionBudget(a,v)=1/(2t) for every unit direction of a and extensionBudget(b,w)=1/(2t) for every unit direction of b. Whole face-effect lifts transport through actual original linear extensions and the equality of the two complete chart images. Sharpness in both directions identifies the numerical optima; no orthogonal coordinate change is supplied as an assumption.

**Theorem 1.5 (One coefficient in every chart and every mixed input).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_common_chart_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_common_chart_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any reference chart of D(p). One t>0, t<=1/2 works in every complete chart b of that same D(p), in every unit direction v, and at every original pure q=b(v). The reciprocal budget is feasible and optimal and equals the actual infimum. An actual confirmer of q realizes the affine formula on the whole chart and the comparison formula on every mixed coordinate in its closed unit ball. Chart independence of the optimum identifies the coefficients in all charts. The theorem does not identify scales of different original exclusion faces.

**Theorem 1.6 (Joint continuity on the whole original pure-pair carrier).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.pure_comparison_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.pure_comparison_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity, generation and pure reciprocity give continuity of (p,q) mapped to T(p,q) on the entire product P times P with its norm subspace topology. The uniform original row bound controls both variables after exchanging pure endpoints. This consumed helper supplies the separated-pure-pair gap construction and the whole-limit calibration proof. It supplies no independent escape witness and assumes no mixed reciprocity, label injectivity or singleton confirmer fiber.

**Theorem 1.7 (All mixed inputs of every pure row).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_uniform_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_uniform_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity and generation give one finite L>0 such that abs(T(p,x)-T(p,y))<=L norm(x-y) for every original pure p and all original mixed x,y in K. This consumed helper directly uses the original frozen CommonOldExclusionConfirmation.comparison_lipschitz owner, enlarging its bound to a positive constant. It provides no independent new mathematical content or escape witness. Neither EB nor PR nor Inj is needed.

**Theorem 1.8 (Universal actual scale-to-axis estimate).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_axis_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_axis_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, one L>0 works at every original pure p and every complete chart a. A positive common scale t<=1/2 has extensionBudget(a,v)=1/(2t) in every unit direction and 2t<=L norm(a(v)-a(-v)). These are the same actual comparison coefficient and original optimal budget, using all mixed inputs of the original scale owner.

**Theorem 1.9 (Finite budget on arbitrary whole-P label sets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_bounded_budget_noncollapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_bounded_budget_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any set U of original pure labels and real B>0, assume every actual chart and unit direction at every p in U has extensionBudget<=B. There is a single delta>0 with delta<=diam(D(p)) for all p in U, explicitly delta=1/(B L) for the universal comparison bound. U is an arbitrary subset of the entire P; it may be a neighborhood containing labels outside P0. This is the noncollapse direction of the local-budget argument. The reverse implication is provided by original_noncollapse_bounded_budget, and original_local_budget_iff combines them in open neighborhoods of all P.

**Theorem 1.10 (Every actual diameter collapse makes budgets diverge).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_diameter_collapse_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_diameter_collapse_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same complete EB plus pure PR hypotheses, let pn be any sequence of original pure labels whose full exclusion diameters tend to zero. Choose arbitrary complete original charts a(n) and any unit coordinate v(n) in each, with dimensions allowed to vary. Then their actual extensionBudget(a(n),v(n)) tends to positive infinity. The universal scale-to-diameter estimate gives 1<=budget(n) L diam(D(pn)); no finite bound can persist along the sequence. The theorem does not assume label convergence, restrict labels to P0, or replace the original budget with a reciprocal definition.

**Theorem 1.11 (Every whole-diameter lower bound gives all-chart budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalBallScale.original_noncollapse_bounded_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBallScale.original_noncollapse_bounded_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, let U be any subset of all original pure labels with diam(D(p))>=delta>0. One finite positive B bounds the actual optimal extensionBudget in every complete chart and every unit direction at every p in U. Frozen pure compactness and strict exposure give a uniform positive gap 1-T(q,r) on all pure pairs at separation delta. Each actual complete chart has a unit diameter axis, and its antipodal comparison is 1-2a. The gap gives 2a>=gamma, hence all actual optimal budgets are at most 1/gamma. The budget is the attained original positive-extension optimum, not a reciprocal definition.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_ball_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_bounded_budget_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_chart_independence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_common_chart_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_diameter_collapse_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_full_face_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_noncollapse_bounded_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_and_sharp_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_axis_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_uniform_comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.pure_comparison_continuous`
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalRegularHeight](OriginalRegularHeight.md)
- Dependency: [D5/S3/Quantum/Foundation/ReciprocalEndpointExposure](ReciprocalEndpointExposure.md)
