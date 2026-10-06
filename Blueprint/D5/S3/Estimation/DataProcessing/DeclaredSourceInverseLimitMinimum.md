# Nearest Laws With Declared Joint Sources

## Abstract

Exact label and joint-source constraints on arbitrary finite towers have an attained completed total-variation minimum equal to the supremum of finite minima.

**Theorem 1.1 (One completed feasible law realizes the finite-minimum supremum).**

$$\begin{aligned}\operatorname{TV}\left(\mathit{rho}, \mathit{theta}\right) = \operatorname{sup}\left(d\right)\\\operatorname{min}\left(L, \operatorname{TV}\left(\mathit{rho}, \mathit{eta}\right)\right) = \operatorname{sup}\left(d\right)\\\exists E\in\operatorname{Homeomorph}\left(L, H\right)\\\operatorname{completedRadius}\left(c\right) \Leftrightarrow \operatorname{everyFiniteRadius}\left(c\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum.exists_minimum_eq_iSup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W_l, Z_l and U_l are finite nonempty discrete Borel spaces at every natural level. Their total bonding maps alpha_l, beta_l and gamma_l need not be surjective. The finite label map W_l to Z_l and joint-source map W_l to U_l commute with the respective bonds.

The completed carriers are the actual inverse-limit thread subtypes. The measurable maps f and g from the completed world carrier have coordinates label_l(x_l) and source_l(x_l). One actual Borel probability rho on the world threads determines every actual finite world law and every finite or completed source law by pushforward.

For every choice of the stated carriers, maps, laws and sets satisfying these hypotheses, there exists Qinf for which all the conclusions below hold together. The target laws Q_l on Z_l are given with exact beta compatibility. The completed target Qinf is constructed on the actual label threads and has exactly those projections. The construction uses probability extension without surjectivity of the original bonds.`D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension`

Legal sets A_l in W_l satisfy alpha_l(A_(l+1)) contained in A_l. The completed legal set is exactly the intersection of their coordinate cylinders. F_l consists of all probabilities theta_l with label pushforward Q_l, source pushforward equal to the actual joint-source law, and mass one on A_l. Each F_l is assumed nonempty with all three constraints satisfied together.

L consists of all completed probabilities theta with f-pushforward Qinf, g-pushforward equal to the g-pushforward of rho, and mass one on the completed legal set. No actual-legality assumption is imposed on rho. Arbitrary real probability masses, including zeros, remain allowed. The carriers are not required to be cyclic tuples and there are no permutation, cut or excess premises.

For every finite candidate probability, eventCost_l is the supremum of absolute differences of event probabilities from the actual finite world law. It is exactly one half of the sum of the absolute singleton-mass differences. completedEventCost is the same event supremum for rho and theta on the full Borel thread event domain.

commonCost uses the completed measures on events null-measurable for rho+theta. The theorem returns equality of completedEventCost and commonCost. Both costs are lower semicontinuous for the weak probability topology, on the whole completed probability space and on its feasible subtype L. This gives four lower-semicontinuity assertions, with no weak-continuity claim.

L is compact. Let H be the space of all compatible families with the l-th law in F_l, carrying the subtype topology of the product of weak probability spaces. There is a homeomorphism E from L to H whose l-th coordinate is the actual pushforward of theta along the l-th world projection.

For every pair of feasible completed laws and every real t between zero and one, their probability mixture remains feasible and E sends it to the same coordinatewise mixture. Conversely, a coordinatewise mixture of compatible families is sent by the inverse homeomorphism to the corresponding mixture of completed laws. These are the two explicit affine directions.

There are real numbers d_l, each attained as the minimum of eventCost_l over the exact F_l. They lie in [0,1], are monotone and converge to their supremum. One theta in L has completedEventCost equal to that supremum. Every completed feasible competitor has cost at least the supremum, so the same theta attains the completed minimum.

For every real c at least zero, one completed feasible law has cost at most c if and only if each finite level has a feasible law of cost at most c. The construction uses the same c at all levels, selecting a compatible family inside the compact radius-constrained classes. It does not assume that independently chosen finite minimizers are compatible.

The finite feasible classes are closed probability constraints. Their bonding maps preserve the label target, the actual joint-source target and legal support. Pushforward contraction and the full-event total-variation identity give the common-radius upper bound and the lower bound from every completed competitor. Compact selection is applied to probability spaces, whose carriers need not be finite or whose bonds need not be surjective.

Uniqueness of extension for a fixed compatible law family gives no uniqueness of an optimizer or original world. No measurable selection, arbitrary event-domain enlargement, or extension of every preassigned finite candidate is asserted. U_l records the source variables declared in this model; additional archive or mechanism restrictions need their own exact semantics.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum.exists_minimum_eq_iSup`
- Truth anchor: `D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension`
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension](FiniteTowerProbabilityExtension.md)
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension](InverseLimitProbabilityExtension.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
