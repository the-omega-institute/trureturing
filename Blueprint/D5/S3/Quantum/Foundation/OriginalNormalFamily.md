# Original scale, normal positivity, exclusion limits and scalar topology

## Abstract

Original scale, normal positivity, exclusion limits and scalar topology

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

**Theorem 1.13 (Joint continuity on the whole original pure-pair carrier).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_comparison_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_comparison_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity, generation and pure reciprocity give continuity of (p,q) mapped to T(p,q) on the entire product P times P with its norm subspace topology. The uniform original row bound controls both variables after exchanging pure endpoints. This consumed helper supplies the separated-pure-pair gap construction and the whole-limit calibration proof. It supplies no independent escape witness and assumes no mixed reciprocity, label injectivity or singleton confirmer fiber.

**Theorem 1.14 (All mixed inputs of every pure row).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity and generation give one finite L>0 such that abs(T(p,x)-T(p,y))<=L norm(x-y) for every original pure p and all original mixed x,y in K. This consumed helper directly uses the original frozen CommonOldExclusionConfirmation.comparison_lipschitz owner, enlarging its bound to a positive constant. It provides no independent new mathematical content or escape witness. Neither EB nor PR nor Inj is needed.

**Theorem 1.15 (Universal actual scale-to-axis estimate).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, one L>0 works at every original pure p and every complete chart a. A positive common scale t<=1/2 has extensionBudget(a,v)=1/(2t) in every unit direction and 2t<=L norm(a(v)-a(-v)). These are the same actual comparison coefficient and original optimal budget, using all mixed inputs of the original scale owner.

**Theorem 1.16 (Finite budget on arbitrary whole-P label sets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any set U of original pure labels and real B>0, assume every actual chart and unit direction at every p in U has extensionBudget<=B. There is a single delta>0 with delta<=diam(D(p)) for all p in U, explicitly delta=1/(B L) for the universal comparison bound. U is an arbitrary subset of the entire P; it may be a neighborhood containing labels outside P0. This is the noncollapse direction of the local-budget argument. The reverse implication is provided by original_noncollapse_bounded_budget, and original_local_budget_iff combines them in open neighborhoods of all P.

**Theorem 1.17 (Every actual diameter collapse makes budgets diverge).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_diameter_collapse_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_diameter_collapse_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same complete EB plus pure PR hypotheses, let pn be any sequence of original pure labels whose full exclusion diameters tend to zero. Choose arbitrary complete original charts a(n) and any unit coordinate v(n) in each, with dimensions allowed to vary. Then their actual extensionBudget(a(n),v(n)) tends to positive infinity. The universal scale-to-diameter estimate gives 1<=budget(n) L diam(D(pn)); no finite bound can persist along the sequence. The theorem does not assume label convergence, restrict labels to P0, or replace the original budget with a reciprocal definition.

**Theorem 1.18 (Every whole-diameter lower bound gives all-chart budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_noncollapse_bounded_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_noncollapse_bounded_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, let U be any subset of all original pure labels with diam(D(p))>=delta>0. One finite positive B bounds the actual optimal extensionBudget in every complete chart and every unit direction at every p in U. Frozen pure compactness and strict exposure give a uniform positive gap 1-T(q,r) on all pure pairs at separation delta. Each actual complete chart has a unit diameter axis, and its antipodal comparison is 1-2a. The gap gives 2a>=gamma, hence all actual optimal budgets are at most 1/gamma. The budget is the attained original positive-extension optimum, not a reciprocal definition.

Assume the original arbitrary finite dimensional V, closed generating pointed cone C and linear unit u strictly positive on nonzero C. K is the entire normalized base, P its entire pure locus, D(p) is the entire original exclusion, EB3 holds at every pure label, and PR exchanges only pure endpoints of the full original comparison. No Inj or singleton confirmer hypothesis is required. Under precisely these assumptions p mapped to diam(D(p)) is upper semicontinuous on all P. To see this, fix any real a and a converging sequence pn in the superlevel diam(D(pn))>=a. Compactness of K and NonemptyCompacts.isCompact_subsets_of_isCompact supply a subsequence with a whole compact limit Q. The compact_diameter_lipschitz estimate transfers the threshold to diam(Q). ReciprocalExclusionLimits.exclusion_limit_dichotomy says Q is either the whole D(p) or a pure singleton contained in D(p); in both cases Q is contained in D(p). Metric.diam_mono gives a<=diam(D(p)). The sequential closed-set criterion proves every superlevel closed, which is the full upper-semicontinuity statement.

For every natural j set S(j)={p in P : 1/(j+1)<=diam(D(p))}, and define R as the union of the interiors of S(j), all taken in P. Upper semicontinuity makes every S(j) closed. The original positive-dimensional whole-ball exclusions have strictly positive full diameter, so exists_nat_one_div_lt shows that the S(j) cover all P. ReciprocalPureCompactness.reciprocal_pure_compact, under the same closedness, strict positivity, generation and pure PR assumptions, makes P compact; Mathlib.Topology.Baire.LocallyCompactRegular supplies its Baire structure. The dense_iUnion_interior_of_closed theorem from Mathlib.Topology.Baire.Lemmas applies to this countable closed cover. Consequently IsOpen R and Dense R both hold. With Sigma=P\R, IsClosed Sigma follows from openness, and interior(closure Sigma) is empty because closure Sigma=Sigma and density of R gives empty interior of its complement. These are full consequences of the compactness, dichotomy, diameter and generic Baire results. The original_regular_iff_continuous theorem below identifies exactly this R with the Hausdorff continuity set of the entire D map; neither residual collapse branch is removed.

**Theorem 1.19 (Every discontinuity supplies an actual whole-ball collapse).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_collapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full original EB3 and pure PR hypotheses, at each Hausdorff discontinuity p there is a sequence pn of original pure labels tending to p and an actual pure q in D(p) such that the entire D(pn) tends to {q}. The proof directly consumes the frozen ReciprocalExclusionLimits.exclusion_limit_dichotomy, including its actual parameter extraction and exact whole-ball equality. If no such singleton subsequence exists, compactness of the entire family inside K makes every subsequence admit a further subsequence tending to the old whole D(p), proving continuity. This is not a conditional row premise. The stronger frozen ReciprocalPureCompactness.reciprocal_pure_compact supplies pure compactness without EB or nontriviality; no duplicate pure-compactness declaration is retained.

**Theorem 1.20 (Exact whole-ball continuity set).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_regular_iff_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_regular_iff_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure p, p belongs to R if and only if the actual whole-exclusion map is Hausdorff continuous at p. On an interior diameter layer an actual singleton collapse would contradict the positive lower bound and continuity of diameter. Conversely continuity at a nondegenerate old ball gives a positive diameter bound in an open neighborhood in all P. OriginalComparisonTopology.original_common_continuity_sets identifies this same R with both actual scalar continuity sets, and its two semicontinuity theorems cover all P.

**Theorem 1.21 (Whole-P continuity exactly equals finite local optimal budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_local_budget_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_local_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under original EB3 and pure PR, Hausdorff continuity at any original pure p is equivalent to an open neighborhood U containing p in all P and a finite positive B bounding every actual chart and unit-direction extensionBudget throughout U. Forward: the exact regular-region theorem gives a neighborhood with a positive whole-diameter lower bound, and original_noncollapse_bounded_budget supplies B. Reverse: original_bounded_budget_noncollapse gives a positive diameter floor on U, placing p inside an actual closed diameter layer and hence in the whole-ball continuity set. No uniqueness or Inj hypothesis is needed.

**Theorem 1.22 (Actual scale across every whole-ball limit).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_limit_calibration`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_limit_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original pure labels pn and p under EB3 and pure-only PR, Hausdorff convergence of the entire D(pn) to D(p) forces convergence of the actual common calibration coefficient. The coefficient is selected from original_common_chart_scale and obeys its all-chart, all-mixed-input law. Parameter extraction is reused from ExclusionIncidence.parameter_subsequence. Closedness of the original pure locus makes every limiting sphere point pure; sphere_extreme_injective_or_zero rules out positive rank loss, while nontriviality of the complete limiting ball excludes the zero map. The limiting affine map is therefore an actual full chart of D(p). Its fixed antipodal endpoints recover the same coefficient via (1-T(q,r))/2 and pure joint comparison continuity. No continuity of chosen charts or extra compact-pure premise is assumed.

**Theorem 1.23 (Actual zero and infinite limits under singleton collapse).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_singleton_limit_scalars`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_singleton_limit_scalars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every whole-exclusion sequence converging to an actual singleton has calibration tending to zero and actual optimalBudget tending to positive infinity. The latter equals the original attained extensionBudget in every chart and every unit direction; optimalBudget is never accepted solely from its reciprocal definition. Diameter continuity on nonempty compact sets and the original diameter-collapse budget theorem yield divergence. This result does not assert that any collapse exists.

**Theorem 1.24 (Both exhaustive original subsequence alternatives).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scalar_subsequence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scalar_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sequence of original pure labels tending to p has a strictly indexed subsequence on which either the whole exclusions tend to the complete D(p), with calibration and optimal budget tending to their actual values at p, or the whole exclusions tend to a pure singleton q in D(p), with calibration tending to zero and optimal budget to positive infinity. Applying the same theorem to any initial subsequence gives the complete scalar refinement. The whole-ball-or-pure-singleton dichotomy is directly reused from the frozen ReciprocalExclusionLimits owner.

**Theorem 1.25 (Upper semicontinuity on all original pure labels).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_calibration_upperSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_calibration_upperSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual common calibration is upper semicontinuous on the entire original P. For each scalar superlevel and every converging original label sequence in it, compact whole-set extraction and the exhaustive scalar alternatives force the limiting label into the same superlevel. In the singleton case the threshold is at most zero, and the actual limiting label still has strictly positive calibration. This is neither a P0 restriction nor a chosen-neighborhood statement.

**Theorem 1.26 (Lower semicontinuity of the actual optimum on all P).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_optimalBudget_lowerSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_optimalBudget_lowerSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every scalar sublevel of the actual attained optimal budget is closed in all original P. The whole branch preserves the sublevel by scalar convergence. The singleton branch is incompatible with a finite upper bound because its actual budgets diverge. Every original individual budget remains finite and at least one; infinity is a sequence limit, not the budget assigned to an individual ball.

**Theorem 1.27 (Every discontinuity retains its actual pure collapse and both scalar limits).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_scalar_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_scalar_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every actual Hausdorff discontinuity there is a sequence of original pure labels tending to p and an original pure q in D(p) such that the entire moving exclusions tend to q, their actual calibrations tend to zero and their actual optimal budgets tend to positive infinity. No collapse existence or exclusion is inferred.

**Theorem 1.28 (Exact common continuity sets and all-P local optimal budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_continuity_sets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_continuity_sets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original regular region R equals the continuity sets of the whole Hausdorff map D, the actual calibration a and the actual optimal budget beta. The result also gives the exact open-neighborhood local-budget equivalence in all P, uniform boundedness on every compact subset of R, positivity and the half-scale upper bound, and attained sharpness of beta in every actual chart and unit direction. At an irregular label the actual collapse witness has a tending to zero and beta to infinity, whereas a(p) is positive and beta(p) finite. The open dense R and closed nowhere-dense Sigma follow from the compact Baire application to the closed positive-diameter layers described here. Inj and singleton full-zero confirmer hypotheses are absent here and remain confined to OriginalRowSaturation and its normal-family prerequisites.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_ball_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_bounded_budget_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_calibration_upperSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_chart_independence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_chart_scale`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_common_continuity_sets`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_diameter_collapse_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_collapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_discontinuity_scalar_witness`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_full_face_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_local_budget_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_noncollapse_bounded_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_optimalBudget_lowerSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_regular_iff_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scalar_subsequence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_and_sharp_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_scale_axis_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_singleton_limit_scalars`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_uniform_comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_limit_calibration`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_comparison_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff`
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalRegularHeight](OriginalRegularHeight.md)
- Dependency: [D5/S3/Quantum/Foundation/ReciprocalEndpointExposure](ReciprocalEndpointExposure.md)
