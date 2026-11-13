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

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_ball_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_chart_independence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_common_chart_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_full_face_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBallScale.original_scale_and_sharp_budget`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalRegularHeight](OriginalRegularHeight.md)
- Dependency: [D5/S3/Quantum/Foundation/ReciprocalEndpointExposure](ReciprocalEndpointExposure.md)
