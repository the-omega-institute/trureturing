# Original-source posterior reverse-test attainment

## Abstract

Original sigma-finite whole-complex-L1 reverse tests on an arbitrary concrete von Neumann algebra have exactly the actual compact posterior family's extended costs, and attain their infimum without a finite-cost premise.

Fix independent universe levels u and v. The source spaces X range over every Type u with any measurable structure and sigma-finite measure. H is any complete complex inner-product space of Type v, M is an actual VonNeumannAlgebra H, and rho,sigma are positive StrongDual C M.toStarSubalgebra functionals. Their sum is order-normal in the intrinsic all-directed sense: every nonempty directed positive set with an actual least upper bound has the specified uniform-tail convergence. No equivalence with a chosen abstract predual or ultraweak topology is asserted. The function f:R->R is only assumed convex on (0,infinity).

**Definition 1.1 (The original algebraic preparation).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1Preparation`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1Preparation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A preparation is a complex-linear algebraic map from the ENTIRE complex L1(X,mu) to the actual continuous dual of the operator algebra. Every output is intrinsically order-normal; a.e. nonnegative inputs have positive outputs; and Gamma(h)(1)=integral h dmu for EVERY complex h. There is no continuity, contraction, separability, finite-measure, finite-cost, faithful-state or normalization premise.

**Definition 1.2 (Actual prepared moments).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1ReverseTest`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1ReverseTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A test consists of an original preparation and measurable integrable real p,q nonnegative almost everywhere, with Gamma(toL1(ofReal p))=rho and Gamma(toL1(ofReal q))=sigma. Its cost is literally CurvaturePerspectiveEndpoints.closedPerspectiveCost hf mu p q. The representation uses exact L1 classes before applying Gamma, so no continuity of an original preparation is needed.

**Definition 1.3 (The full fixed-universe cost set).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

attainableCosts hf rho sigma directly quantifies every X:Type u, every measurable structure, every sigma-finite mu, every original algebraic whole-complex-L1 preparation Gamma and every two nonnegative ORIGINAL complex L1 elements p,q preparing rho,sigma. Their cost is literally closedPerspectiveCost hf mu Re(p) Re(q). The output universe v is independent. No chosen measurable representatives, matrices, finite sources or finite-cost premise narrow this original definition.

**Theorem 1.4 (No loss from representatives).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts_of_positive_L1`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts_of_positive_L1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ANY original preparation Gamma on any sigma-finite X:Type u and ANY two a.e. nonnegative elements p,q of the original complex L1, their cost computed from Re(p),Re(q) belongs to representativeCosts hf (Gamma p) (Gamma q), with exactly the same preparation. The original generic measurable_positive_L1_input supplier constructs measurable representatives with exact complex L1 equality. Its original cost_congr_ae supplier proves equality of the literal extended cost. Thus neither the prepared moments nor the cost depend on the representative, and the source class retains every original nonnegative L1 input.

**Definition 1.5 (The measurable presentation of the same source class).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

representativeCosts quantifies actual NormalL1ReverseTest data with measurable integrable real representatives, arbitrary sigma-finite sources at Type u and the literal cost. It is an auxiliary presentation, whose equality with the original L1-element class is proved and consumed.

**Theorem 1.6 (Exact equality with original nonnegative L1 inputs).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_representativeCosts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_representativeCosts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every convex hf and every output pair rho,sigma, attainableCosts.{u} hf rho sigma equals representativeCosts.{u} hf rho sigma. The forward implication consumes representativeCosts_of_positive_L1 and its exact L1 input and preparation equalities. Conversely, embed the two measurable real inputs into the original complex L1 space, prove their a.e. positivity, and use cost_congr_ae on their real parts. attainableCosts_eq_range consumes this equality before either cost-set inclusion. Thus the representative theorem is on the actual attainment proof path.

**Definition 1.7 (Literal compact-family cost).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the actual NormalMomentFamily.Family rho sigma, familyCost hf F is closedPerspectiveCost hf (scalarMeasure F) t (1-t), including the values at both endpoints and infinity. The measure is the actual scalar Riesz measure of the family's all-coordinate map.

**Definition 1.8 (Every original source gives a family point).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose Gamma.toLinearMap with PosteriorSourceNormalization.pullContinuous.toLinearMap. This actual map sends continuous g to the original L1 class of r*g(theta), where r=p+q almost everywhere and theta=p/r off the null mass fiber. pullContinuous_positive gives positivity; its exact 1,t,1-t L1 equalities and algebraic linearity give J1=rho+sigma and Jt=rho. NormalMomentFamily.ofLinearMap therefore gives an actual Family member. No continuity of Gamma is used and no compactness field is introduced.

**Theorem 1.9 (Riesz equals the actual weighted pushforward).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily_scalarMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily_scalarMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original test R, scalarMeasure(posteriorFamily R) equals posteriorMeasure mu R.p R.q. Both are actual finite regular measures. For every bounded continuous real g, embed g as a continuous complex function. integral_complex, the original complex mass law, and integral_pullContinuous identify their complex integrals; taking real parts gives all real test integrals. FiniteMeasure.ext_of_forall_integral_eq proves equality of measures.

**Theorem 1.10 (Exact forward extended cost identity).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.source_cost_eq_familyCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.source_cost_eq_familyCost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original test R and convex hf, closedPerspectiveCost hf mu R.p R.q equals familyCost hf (posteriorFamily R). Substitute the preceding measure equality into the original closedPerspectiveCost_posterior theorem. The statement includes arbitrary sigma-finite sources, zero fibers, both infinite endpoint coefficients and infinite total cost; no infimum relaxation replaces the literal equality.

**Definition 1.11 (Return to the fixed source universe).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedMeasure`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

liftedMeasure nu is the actual pushforward nu.map ULift.up on ULift.{u} Interval, which is a Type u even when u and the operator universe v differ. ULift.up is a measurable equivalence and is measure-preserving to this measure. The whole-L1 pullback is Mathlib's compMeasurePreserving linear isometry. Its a.e. action transports positivity, the integral mass law and exact continuous posterior L1 classes.

**Definition 1.12 (An actual original source for every family realization).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedReverseTest`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedReverseTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given the actual continuous whole-L1 normal realization constructed for a family point by compact_normal_posterior_family, compose it with that ULift L1 isometry. The resulting original algebraic preparation has positive outputs, all-output intrinsic normality and complex mass preservation. The real densities are exactly down(t).val and 1-down(t).val, are integrable for the finite mapped Riesz measure, and prepare exactly rho,sigma. Measure-equivalence integration preserves the literal affine and ENNReal curvature integrals separately.

**Definition 1.13 (The common finite affine term).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.affineCost`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.affineCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

affineCost f rho sigma is the real number f(1)*Re(sigma(1))+rightDeriv f 1*(Re(rho(1))-Re(sigma(1))). It is finite without a finite-cost assumption.

**Theorem 1.14 (Full objective and weak curvature remainder).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost_eq_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For EVERY family point F, familyCost hf F equals the EReal embedding of affineCost f rho sigma plus the EReal embedding of posteriorCurvatureCost hf (finiteMeasure F). The exact complex mass and moment identities give integral t=Re(rho(1)) and integral (1-t)=Re(sigma(1)). Integrability of continuous interval functions permits ordinary affine Bochner integration. The remaining lintegral is definitionally the original curvature objective, so there is no signed infinite subtraction.

**Theorem 1.15 (Equality of actual original and posterior cost sets).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary concrete M and positive rho,sigma with order-normal sum, attainableCosts.{u} hf rho sigma equals the actual range of familyCost hf over Family rho sigma. Forward membership uses every original algebraic preparation and the exact pushforward identity. Backward membership consumes compact_normal_posterior_family for EVERY F and uses liftedReverseTest on the actual finite pushforward measure in Type u, with exact cost preserved. Compactness, realization, lower semicontinuity and cost comparison are not assumed here.

**Theorem 1.16 (Original extended attainment, including infinity).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.original_reverse_test_extended_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.original_reverse_test_extended_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under precisely those original hypotheses, there exists F in the actual Family with familyCost hf F equal to sInf(attainableCosts.{u} hf rho sigma), and that sInf is not EReal.bot. If rho=sigma=0 the same sInf is exactly zero, proved from the actual scalar measure having zero total mass. Its scalarMeasure is regular and its liftedMeasure is finite. There is an actual original NormalL1ReverseTest on liftedMeasure(scalarMeasure F), with densities exactly down(t).val and 1-down(t).val, whose literal cost equals the same original sInf. There is also an actual continuous complex-linear Gamma on the ENTIRE complex L1(scalarMeasure F), agreeing with every family continuous moment, intrinsically normal on every output, positive, preserving every complex mass, of norm at most one and having both exact posterior moments. Its existence is obtained from the proved compact-family supplier, not stored as an optimization premise.

**Definition 1.17 (The independent standard concrete source).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.StandardL1Preparation`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.StandardL1Preparation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For actual M acting on an arbitrary complete complex Hilbert space H, a StandardL1Preparation is an algebraic complex-linear map from the entire original complex L1(X,mu) to StrongDual C M. It is positive on all a.e. nonnegative inputs, preserves the integral for EVERY complex input, and every output has an actual IsCoefficientSeries M representation: two square-summable sequences of vectors with phi(a)=sum_n <xi(n),a eta(n)>. Intrinsic normality, continuity and contraction are not input hypotheses. The definition is independent of E and of the intrinsic-normal source definition. Its toNormal conversion keeps the exact algebraic map, positivity and complex mass law; the proved series_order_normal theorem supplies intrinsic normality of every output. The conversion changes neither source, inputs nor values and assumes no converse equivalence.

**Definition 1.18 (The literal standard-original cost class).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts`

*Formalization.* `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every X:Type u with any measurable structure and sigma-finite mu, every StandardL1Preparation, and every pair of a.e. nonnegative ORIGINAL complex L1 elements p,q preparing rho,sigma exactly, include the literal closedPerspectiveCost hf mu Re(p) Re(q). The source universe u remains independent of the Hilbert-space universe v. No normalization, nonzero mass, faithful state, finite alphabet, finite source measure or finite cost restricts this definition.

**Theorem 1.19 (CodRestrict the actual realized Gamma).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_posterior_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_posterior_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho,sigma be positive actual standard-series functionals and F ANY actual Family rho sigma. Apply compact_normal_posterior_family using the proved forward normality of their sum. Its actual Gamma agrees with J=linearMap F on every continuous function. Positive-coordinate domination by ||g||J1, GNS heredity, four positive parts and closed-preimage L1 density prove every Gamma(h) belongs to E. The returned predual map is LITERALLY Gamma.codRestrict E hGammaE, with (GammaE h).val=Gamma h for all h, norm at most one and actual standard-series outputs. The same Gamma remains intrinsically normal, positive, mass-preserving on every complex input, contractive, and has both exact posterior moments. No range-membership optimizer premise or surrogate source is introduced.

**Theorem 1.20 (Exact standard-original and posterior cost equality).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts_eq_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every convex f on (0,infinity), positive actual standard-series rho,sigma, the entire standardAttainableCosts.{u} M hf rho sigma equals the actual range of familyCost hf over Family rho sigma. Forward inclusion keeps every original algebraic preparation and uses its proved intrinsic-normal inclusion and the existing original cost-set theorem. For each posterior F, standard_posterior_realization supplies its actual Gamma. liftedReverseTest composes this map with the ULift L1 isometry, and the coefficient-space series theorem proves every resulting output is standard. Embed its real integrable densities into their original complex L1 classes, retain exact prepared moments, and apply the original a.e. cost congruence and literal lifted_cost identity. Equality holds before infima and includes infinite endpoint coefficients and infinite total costs.

**Theorem 1.21 (Standard concrete-predual original attainment).**

Lean statement: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_original_reverse_test_extended_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_original_reverse_test_extended_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly those standard-series positivity hypotheses and arbitrary convexity on (0,infinity), there exists F whose literal familyCost equals sInf of the ENTIRE standard-original cost class. This sInf is not minus infinity, and is zero for the zero pair. Both scalarMeasure F and its liftedMeasure are regular, and liftedMeasure is finite. Mathlib Measure.Regular.map along the actual ULift homeomorphism proves the lifted regularity. An actual Gamma on the whole complex interval L1 has all continuous agreements, positivity, all complex masses, contraction and both exact moments. Its predual realization is precisely its codRestriction to E and has actual square-summable-series outputs. The attaining original lifted test is explicitly defined in the statement as liftedReverseTest F Gamma hn hp hm hl hr FROM THIS SAME GAMMA; every lifted output is a standard series, its densities are exactly down(t).val and 1-down(t).val, and its literal cost is the same standard-original sInf. The proof consumes the existing intrinsic attainment and exact cost equalities. It does not infer a connection between the intrinsic theorem's separately quantified R and Gamma. No finite-cost branch, nonzero division or finite-alphabet conclusion is used.

The minimization uses the actual nonempty compact Family and the weakly continuous finiteMeasure map. Compose it with PosteriorCurvatureCost.posteriorCurvatureCost_lowerSemicontinuous, then apply LowerSemicontinuousOn.exists_isMinOn with codomain ENNReal. This codomain includes top, so the argument also gives a minimizer when every cost is +infinity. In that case nonemptiness alone makes every admissible test a minimizer; this branch retains scope and is not counted as an additional independent solved optimization problem. Add the same finite affine term and use the proved cost-set equality to identify the original sInf. The affine term plus a nonnegative ENNReal coercion cannot be minus infinity. No finite-cost case split, sequential compactness replacement or nonzero-mass division is needed. The zero pair remains in all quantified statements.

Hiai--Mosonyi--Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, Remark VII.4 (PDF p. 60), asks about general-convex minimal reverse-test existence; their Section V.A(III) uses actual sigma-finite L1 sources. The standard endpoint connects the original attainment result to the independently specified concrete coefficient-series M-star source class. HMT's separate question on PDF p. 62 asks for a classification of equality between maximal hockey-stick f-divergence and maximal f-divergence; this attainment endpoint does not supply that classification.

Matsumoto, arXiv:1311.4722v4, Theorem 9.4, already proves finite-dimensional finite-value attainment under FC. His Theorem 9.9 (PDF p. 35) concerns separable B(H), under FC and the finite endpoint hypotheses f(0)<infinity and hat f(0)<infinity stated throughout Section 9.3 (PDF p. 31); Lemma 4.1 already supplies the finite compression architecture. Hiai, arXiv:1807.03118v1, Section 6 and Theorem 6.3, supplies arbitrary-von-Neumann whole-L1 spectral attainment under operator convexity, including infinite endpoint conventions. The present construction retains arbitrary convexity and does not assert spectral optimality or finite-alphabet attainment. The proof reuses standard Banach--Alaoglu, Tychonoff, scalar Riesz representation, L1 completion and weak lower semicontinuity. Global literature novelty and the equivalence of intrinsic order-normality with an abstract chosen predual are not claimed.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1Preparation`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.NormalL1ReverseTest`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.StandardL1Preparation`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.affineCost`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_range`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.attainableCosts_eq_representativeCosts`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.familyCost_eq_affine`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedMeasure`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.liftedReverseTest`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.original_reverse_test_extended_attainment`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.posteriorFamily_scalarMeasure`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.representativeCosts_of_positive_L1`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.source_cost_eq_familyCost`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standardAttainableCosts_eq_range`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_original_reverse_test_extended_attainment`
- Truth anchor: `D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment.standard_posterior_realization`
- Dependency: [D5/S3/Analytic/Convexity/PosteriorCurvatureCost](../../Analytic/Convexity/PosteriorCurvatureCost.md)
- Dependency: [D5/S3/Quantum/Analysis/ConcreteCoefficientSeries](../Analysis/ConcreteCoefficientSeries.md)
- Dependency: [D5/S3/Quantum/Analysis/NormalMomentFamily](../Analysis/NormalMomentFamily.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest](MaximalHockeyStickL1ReverseTest.md)
- Dependency: [D5/S3/Quantum/Divergence/PosteriorSourceNormalization](PosteriorSourceNormalization.md)
