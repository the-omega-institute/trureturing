# Actual scalar topology and original optimal budgets

## Abstract

Actual scalar topology and original optimal budgets

V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.

**Theorem 1.1 (All mixed inputs of every pure row).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_uniform_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_uniform_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity and generation give one finite L>0 such that abs(T(p,x)-T(p,y))<=L norm(x-y) for every original pure p and all original mixed x,y in K. This consumed helper directly uses the original frozen CommonOldExclusionConfirmation.comparison_lipschitz owner, enlarging its bound to a positive constant. It provides no independent new mathematical content or escape witness. Neither EB nor PR nor Inj is needed.

**Theorem 1.2 (Universal actual scale-to-axis estimate).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scale_axis_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scale_axis_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, one L>0 works at every original pure p and every complete chart a. A positive common scale t<=1/2 has extensionBudget(a,v)=1/(2t) in every unit direction and 2t<=L norm(a(v)-a(-v)). These are the same actual comparison coefficient and original optimal budget, using all mixed inputs of the original scale owner.

**Theorem 1.3 (Finite budget on arbitrary whole-P label sets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_bounded_budget_noncollapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_bounded_budget_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any set U of original pure labels and real B>0, assume every actual chart and unit direction at every p in U has extensionBudget<=B. There is a single delta>0 with delta<=diam(D(p)) for all p in U, explicitly delta=1/(B L) for the universal comparison bound. U is an arbitrary subset of the entire P; it may be a neighborhood containing labels outside P0. This is the noncollapse direction of the local-budget argument. The reverse implication is provided by original_noncollapse_bounded_budget, and original_local_budget_iff combines them in open neighborhoods of all P.

**Theorem 1.4 (Every whole-diameter lower bound gives all-chart budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_noncollapse_bounded_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_noncollapse_bounded_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under closedness, strict positivity, generation, EB and pure PR, let U be any subset of all original pure labels with diam(D(p))>=delta>0. One finite positive B bounds the actual optimal extensionBudget in every complete chart and every unit direction at every p in U. Frozen pure compactness and strict exposure give a uniform positive gap 1-T(q,r) on all pure pairs at separation delta. Each actual complete chart has a unit diameter axis, and its antipodal comparison is 1-2a. The gap gives 2a>=gamma, hence all actual optimal budgets are at most 1/gamma. The budget is the attained original positive-extension optimum, not a reciprocal definition.

**Theorem 1.5 (Whole-P continuity exactly equals finite local optimal budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_local_budget_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_local_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under original EB3 and pure PR, Hausdorff continuity at any original pure p is equivalent to an open neighborhood U containing p in all P and a finite positive B bounding every actual chart and unit-direction extensionBudget throughout U. Forward: the exact regular-region theorem gives a neighborhood with a positive whole-diameter lower bound, and original_noncollapse_bounded_budget supplies B. Reverse: original_bounded_budget_noncollapse gives a positive diameter floor on U, placing p inside an actual closed diameter layer and hence in the whole-ball continuity set. No uniqueness or Inj hypothesis is needed.

**Theorem 1.6 (Every actual diameter collapse makes budgets diverge).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_diameter_collapse_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_diameter_collapse_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same complete EB plus pure PR hypotheses, let pn be any sequence of original pure labels whose full exclusion diameters tend to zero. Choose arbitrary complete original charts a(n) and any unit coordinate v(n) in each, with dimensions allowed to vary. Then their actual extensionBudget(a(n),v(n)) tends to positive infinity. The universal scale-to-diameter estimate gives 1<=budget(n) L diam(D(pn)); no finite bound can persist along the sequence. The theorem does not assume label convergence, restrict labels to P0, or replace the original budget with a reciprocal definition.

**Theorem 1.7 (Actual scale across every whole-ball limit).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_whole_limit_calibration`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_whole_limit_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original pure labels pn and p under EB3 and pure-only PR, Hausdorff convergence of the entire D(pn) to D(p) forces convergence of the actual common calibration coefficient. The coefficient is selected from original_common_chart_scale and obeys its all-chart, all-mixed-input law. Parameter extraction is reused from ExclusionIncidence.parameter_subsequence. Closedness of the original pure locus makes every limiting sphere point pure; sphere_extreme_injective_or_zero rules out positive rank loss, while nontriviality of the complete limiting ball excludes the zero map. The limiting affine map is therefore an actual full chart of D(p). Its fixed antipodal endpoints recover the same coefficient via (1-T(q,r))/2 and pure joint comparison continuity. No continuity of chosen charts or extra compact-pure premise is assumed.

**Theorem 1.8 (Actual zero and infinite limits under singleton collapse).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_singleton_limit_scalars`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_singleton_limit_scalars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every whole-exclusion sequence converging to an actual singleton has calibration tending to zero and actual optimalBudget tending to positive infinity. The latter equals the original attained extensionBudget in every chart and every unit direction; optimalBudget is never accepted solely from its reciprocal definition. Diameter continuity on nonempty compact sets and the original diameter-collapse budget theorem yield divergence. This result does not assert that any collapse exists.

**Theorem 1.9 (Both exhaustive original subsequence alternatives).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scalar_subsequence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scalar_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sequence of original pure labels tending to p has a strictly indexed subsequence on which either the whole exclusions tend to the complete D(p), with calibration and optimal budget tending to their actual values at p, or the whole exclusions tend to a pure singleton q in D(p), with calibration tending to zero and optimal budget to positive infinity. Applying the same theorem to any initial subsequence gives the complete scalar refinement. The whole-ball-or-pure-singleton dichotomy is directly reused from the frozen ReciprocalExclusionLimits owner.

**Theorem 1.10 (Upper semicontinuity on all original pure labels).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_calibration_upperSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_calibration_upperSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual common calibration is upper semicontinuous on the entire original P. For each scalar superlevel and every converging original label sequence in it, compact whole-set extraction and the exhaustive scalar alternatives force the limiting label into the same superlevel. In the singleton case the threshold is at most zero, and the actual limiting label still has strictly positive calibration. This is neither a P0 restriction nor a chosen-neighborhood statement.

**Theorem 1.11 (Lower semicontinuity of the actual optimum on all P).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_optimalBudget_lowerSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_optimalBudget_lowerSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every scalar sublevel of the actual attained optimal budget is closed in all original P. The whole branch preserves the sublevel by scalar convergence. The singleton branch is incompatible with a finite upper bound because its actual budgets diverge. Every original individual budget remains finite and at least one; infinity is a sequence limit, not the budget assigned to an individual ball.

**Theorem 1.12 (Every discontinuity retains its actual pure collapse and both scalar limits).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_discontinuity_scalar_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_discontinuity_scalar_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every actual Hausdorff discontinuity there is a sequence of original pure labels tending to p and an original pure q in D(p) such that the entire moving exclusions tend to q, their actual calibrations tend to zero and their actual optimal budgets tend to positive infinity. No collapse existence or exclusion is inferred.

**Theorem 1.13 (Exact common continuity sets and all-P local optimal budgets).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_common_continuity_sets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_common_continuity_sets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original regular region R equals the continuity sets of the whole Hausdorff map D, the actual calibration a and the actual optimal budget beta. The result also gives the exact open-neighborhood local-budget equivalence in all P, uniform boundedness on every compact subset of R, positivity and the half-scale upper bound, and attained sharpness of beta in every actual chart and unit direction. At an irregular label the actual collapse witness has a tending to zero and beta to infinity, whereas a(p) is positive and beta(p) finite. The open dense R and closed nowhere-dense Sigma are provided by OriginalExclusionLimits.original_baire_regular_region. Inj and singleton full-zero confirmer hypotheses are absent here and remain confined to OriginalRowSaturation and its normal-family prerequisites.

The literal supremum over all affine face effects of their individual optimal positive-extension maxima on K agrees with the common attained budget. For each face effect the retained original_full_face_budget lift bounds its individual infimum by beta. A unit directional face effect attains beta, since every positive extension with maximum M on the compact full K is bounded by M u on C by normalization, so the directional sharp lower bound applies. Thus the supremum of the individual infima is exactly beta; it is not inferred solely from a statement about one simultaneous upper budget. The exact supremum/infimum/max-on-K formulation is checked transiently against the existing sharp theorem, with no extra named binding declaration. All results concern the original static cone, unit, full effect interval and auxiliary norm. No mixed PR, UF, CS, physical realization or novelty claim is supplied.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_bounded_budget_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_calibration_upperSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_common_continuity_sets`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_diameter_collapse_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_discontinuity_scalar_witness`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_local_budget_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_noncollapse_bounded_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_optimalBudget_lowerSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scalar_subsequence`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scale_axis_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_singleton_limit_scalars`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_uniform_comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_whole_limit_calibration`
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalBallScale](OriginalBallScale.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalExclusionLimits](OriginalExclusionLimits.md)
