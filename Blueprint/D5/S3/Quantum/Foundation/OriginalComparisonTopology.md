# Uniform original comparison estimates and bounded-budget noncollapse

## Abstract

Uniform original comparison estimates and bounded-budget noncollapse

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

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_bounded_budget_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_diameter_collapse_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_local_budget_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_noncollapse_bounded_budget`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_scale_axis_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalComparisonTopology.original_uniform_comparison`
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalBallScale](OriginalBallScale.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalExclusionLimits](OriginalExclusionLimits.md)
