# General convex equality on the common interior

## Abstract

General convex maximal hockey equality for actual finite reverse tests and arbitrary singular matrix pairs.

The source class is exactly the existing ReverseTest A B k, with k ranging over all natural numbers. Its p and q are nonnegative real functions on Fin k, and its density-matrix preparation realizes the original A and B. No trace normalization, invertibility, nonzero-pair or nonempty-dimension hypothesis is imposed. This statement does not identify the infimum over all finite tests with an infimum over arbitrary L1 sources or prove an arbitrary von Neumann algebra theorem.

**Definition 1.1 (The original finite affine mass).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.affineMass`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.affineMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For the real convex generator f, affineMass f A B is f(1) Tr(B) + f'_+(1)(Tr(A)-Tr(B)). The derivative is the actual right derivative from CurvatureHingeRepresentation. Both traces retain their original arbitrary values.

**Definition 1.2 (The two scalar orientations).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hinge`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hinge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For t in the strictly positive subtype, hinge u v t is max(t v-u,0) when t <= 1 and max(u-t v,0) when t > 1. Thus the full atom at one belongs to the negative branch.

**Definition 1.3 (The actual finite classical hockey kernel).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.testKernel`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.testKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

testKernel R t is the sum over Fin k of hinge (R.p i) (R.q i) t. It is nonnegative and measurable, and differs from maximalKernel by the actual positive-orientation gap at every positive threshold.

**Definition 1.4 (The actual optimized overlap kernel).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalKernel`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

Write O(t) for the supremum of Re Tr(X) over the actual positive overlaps 0 <= X <= A and X <= t B. For t <= 1 the kernel is t Tr(B)-O(t); for t > 1 it is Tr(A)-O(t). Both branches are nonnegative. maximal_kernel_eq_operational proves that these are exactly the original finite operational infima in the two orientations. The optimization is over the actual singular matrix pair.

**Theorem 1.5 (Each branch is an actual finite operational infimum).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximal_kernel_eq_operational`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximal_kernel_eq_operational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For every finite PSD A,B and positive threshold t, maximalKernel is operationalNegativeHockey A B t when t<=1 and operationalHockey A B t when t>1. Each operational quantity is independently defined as the infimum of the original sum of classical positive or negative parts over all k and actual ReverseTest A B k. Operational proves both SDP formulas with a single three-component attaining test, including empty dimension. hockey_value_eq_operational consumes this branchwise identification.

**Theorem 1.6 (The integrated original operational profiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockey_value_eq_operational`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockey_value_eq_operational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For arbitrary real f convex on Ioi 0 and every finite PSD A,B, hockeyValue equals its original finite affineMass plus the nonnegative extended curvature integral of the actual finite operational negative infimum on (0,1] and positive infimum on (1,infinity). The same actual curvature and all infinite endpoint conventions are retained. The existing hockey_le_test proof consumes this identity and bounds each operational infimum by the profile of the given actual test; both final general-convex equality directions therefore use the operational representation. No interchange of infimum and integral is asserted.

**Definition 1.7 (The full closed-perspective finite cost).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.finiteCost`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.finiteCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

finiteCost hf R is the EReal sum over Fin k of closedPerspective hf (R.p i) (R.q i). In the positive quadrant the summand is q f(p/q); on each nonzero axis it is the positive mass times the proved convex endpoint limit; at the origin it is zero even with infinite endpoints. The scalar supplier constructs the actual locally finite curvature from the right derivative for every real f convex on Ioi 0. Its exact representation proves that finiteCost is affineMass plus the nonnegative curvature integral of testKernel, including infinite values.

**Definition 1.8 (Infimum over every actual finite test).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

maximalValue hf A B is the EReal infimum of finiteCost over every k and every ReverseTest A B k. Its definition assumes neither a minimizing test nor a bound on alphabet size. A real finite infimum yields a sequence of actual tests with cost strictly below c+1/(j+1); every such cost is finite.

**Definition 1.9 (The actual integrated maximal hockey value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockeyValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockeyValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

hockeyValue hf A B is affineMass plus the ENNReal curvature integral of maximalKernel, embedded in EReal. hockey_value_eq_operational identifies these with the actual finite operational infima. Its two nonnegative integrals are over (0,1] and (1,infinity). This is the finite-affine-support convention, so infinite endpoints or infinite total curvature do not introduce an infinite difference.

**Theorem 1.10 (Sufficiency for every convex generator and extended value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.commute_implies_integrated_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.commute_implies_integrated_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For every finite PSD pair, let S=A+B, C=normalize(S,A), and P=interiorProjection(C). If PSP commutes with PCP, then maximalValue hf A B equals hockeyValue hf A B for every real f convex on the positive ray. No full-support or finite-value hypothesis is needed in this direction. The actual canonical spectral test supplied by quadratic_reverse_test_attained_profile has exactly maximalKernel at every positive threshold. Its actual closed-perspective cost integrates that profile, and the defining infimum is sandwiched between this cost and the hockey lower bound. This proves the converse with infinite endpoint values, rather than assuming canonical optimality for general f.

**Theorem 1.11 (The finite-value full-support classification).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.integrated_eq_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.integrated_eq_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For every finite type n, every pair A,B of PSD complex n by n matrices, every real f convex on Ioi 0 whose constructed curvature is positive on every nonempty open set, and every real c satisfying maximalValue hf A B = c, equality maximalValue hf A B = hockeyValue hf A B is equivalent to (PSP)(PCP)=(PCP)(PSP), with S=A+B, C=normalize(S,A), P=interiorProjection(C). Local finiteness is supplied by the constructed curvature. The statement includes zero and singular pairs and the empty matrix type. Finite-cost approximate tests have integrable nonnegative gaps; their costs split as hockeyValue plus the real gap integral. Equality and the 1/(j+1) bounds force those integrals to zero, and vanishing_curvature_gaps_imply_commute supplies the original-pair commutator. No general-f attainment theorem is used. Operator-convex generators satisfying the same curvature and finite-value hypotheses are included by this scalar-convex theorem. Necessity from equality of two infinite values is not asserted.

Attribution: the source equality question is Hiai, Mosonyi and Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, final equality question. Hiai's canonical spectral reverse-test construction and operator-convex optimality are antecedents, rather than new claims. The GGJ2005 result documented in its separate Library entry is a localization antecedent for separating common-support overlap geometry from endpoint pieces. The present proof consumes the repository's actual finite spectral and quadratic results and its scalar Stieltjes construction. No Bayer-Teichmann cubature or general-convex attainment result is consumed. The full-support approximate-test integration is a repository derivation; worldwide priority is unresolved.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.affineMass`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.commute_implies_integrated_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.finiteCost`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hinge`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockeyValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.hockey_value_eq_operational`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.integrated_eq_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalKernel`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximalValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.maximal_kernel_eq_operational`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.testKernel`
- Dependency: [D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints](../../Analytic/Convexity/CurvaturePerspectiveEndpoints.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOperational](MaximalHockeyStickOperational.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality](MaximalHockeyStickQuadraticEquality.md)
