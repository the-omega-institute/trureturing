# The actual all-L1 equality classifier

## Abstract

Equality of the original sigma-finite L1 maximal convex and operational hockey values is classified by the common-interior commutator, with the same criterion for every s-finite L1 source.

Let n be any finite type and let A,B be positive semidefinite complex n by n matrices. Their traces are arbitrary. Singular matrices, the zero pair and the empty matrix type are included. Let f be real valued and convex on the strictly positive ray. The scalar convention uses the actual right derivative at one and its Stieltjes curvature, with the full atom at one in the negative branch. The closed perspective is q f(p/q) in the positive quadrant, uses the proved extended endpoint limits on the axes, and is zero at the origin even when an endpoint is infinite.

**Definition 1.1 (The actual all-source infimum).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any source universe u, allL1Value hf A B is the EReal infimum of MaximalHockeyStickL1ReverseTest.allL1Costs hf A B. This set ranges over every measurable space X in Type u, every s-finite measure mu, and every positive complex-linear trace-preserving map from the entire complex L1(mu) space to the matrix algebra. The two nonnegative integrable inputs prepare exactly A and B. Measurable representatives do not restrict these L1 inputs, by allL1Costs_of_positive_L1. Continuity of preparation follows from positivity and trace preservation. The cost is the actual unnormalized closed-perspective integral: its finite affine support plus a nonnegative extended curvature remainder. Neither attainment nor a finite source alphabet is part of this definition.

**Theorem 1.2 (Identification with the actual finite maximal value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value_eq_maximalValue`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value_eq_maximalValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real convex f and every matrix pair, allL1Value hf A B equals MaximalHockeyStickConvex.maximalValue hf A B as an extended value. The latter is the infimum of the same closed-perspective sums over every actual finite ReverseTest and every alphabet size. The proof applies source_class_infimum_eq directly: finite tests embed by counting measure, while each individual finite-cost all-L1 test has an exact finite atomization preserving both prepared matrices and this one specified cost. Tests of infinite cost introduce no additional lower-bound constraint. This identifies infima without assuming an optimizer and without asserting simultaneous atomization of every generator or the full threshold profile.

**Theorem 1.3 (Convex sufficiency with extended values).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set S=A+B, C=MaximalHockeyStickSupport.normalize S A, and P=interiorProjection C. If (PSP)(PCP)=(PCP)(PSP), then allL1Value hf A B equals MaximalHockeyStickConvex.hockeyValue hf A B for every real f convex on the positive ray. No full-support curvature or finite-value assumption is imposed. Infinite scalar endpoints and infinite resulting values are retained. Source-class identification transfers the finite sufficiency theorem, whose canonical spectral reverse test realizes every maximal threshold profile under this commutator condition.

**Theorem 1.4 (The original common-interior criterion for actual all-L1 equality).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.integrated_eq_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.integrated_eq_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that the actual constructed curvature of f is positive on every nonempty open subset of the positive ray, and that allL1Value hf A B equals some real c embedded in EReal. Then allL1Value hf A B = hockeyValue hf A B if and only if (PSP)(PCP)=(PCP)(PSP), with S=A+B, C=normalize S A, and P=interiorProjection C. The finite-value premise concerns the actual all-L1 infimum itself. Source-class identification supplies precisely the finite infimum premise of MaximalHockeyStickConvex.integrated_eq_iff_commute. That reused criterion uses finite-cost approximate tests, integrable nonnegative curvature gaps and the original-pair commutator theorem; it assumes no optimal test. Sufficiency is the preceding unconditional extended-value result. Necessity from equality of infinite values is not asserted.

**Definition 1.5 (The original sigma-finite maximal value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The EReal infimum ranges over every sigma-finite measurable source X in the arbitrary universe u and every actual positive complex-linear TP preparation on its entire complex L1 space. It uses the same unnormalized closed-perspective integral as allL1Value. Finite counting sources are sigma-finite and sigma-finite sources are s-finite; sigma_finite_source_infimum_eq identifies this original infimum with the finite infimum, including extended values.

**Theorem 1.6 (Faithful original-source value identification).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value_eq_allL1Value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value_eq_allL1Value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real f convex on Ioi 0 and every matrix pair, the original sigma-finite maximal value equals the existing s-finite allL1Value. This is the sandwich between finite counting sources and all s-finite sources, using the already proved source_class_infimum_eq. It does not identify a hinge cost with a hockey integral.

**Definition 1.7 (Integrated original operational hockey infima).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalHockeyValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalHockeyValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each positive threshold t, operationalL1Hockey is the real infimum of the actual integrals of max(p-tq,0) over every original sigma-finite source test, and operationalL1NegativeHockey uses max(tq-p,0) over that same class. originalHockeyValue is affineMass plus the extended nonnegative curvature integral of the negative infimum for 0<t<=1 and the positive infimum for t>1. This includes the entire curvature atom at one in the negative branch. The source universe is arbitrary and independent of the matrix universe.

**Definition 1.8 (Integrated s-finite operational hockey infima).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.sFiniteHockeyValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.sFiniteHockeyValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This uses the same integral and branch convention as originalHockeyValue, with the infima over every s-finite L1 source. The profile sets are proved equal to the finite sets, separately from any general-f cost identification.

**Theorem 1.9 (Actual L1 profile identification is consumed).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.hockeyValue_eq_original_operational`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.hockeyValue_eq_original_operational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite PSD pair and every real convex f, the old PSD hockeyValue equals both originalHockeyValue and sFiniteHockeyValue. The proof consumes operationalL1_hockey_eq pointwise at each positive threshold. That theorem follows from direct positive-L1 three-component compression and the exact counting embedding for both orientations. Thus the integrated expression uses the literal original operational infima. No closedPerspectiveCost specialization is assumed to be a hockey integral, and no infimum is interchanged with integration.

**Theorem 1.10 (Extended all-L1 operational sufficiency).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_allL1_operational_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_allL1_operational_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every convex f and every finite PSD pair, PSP commuting with PCP implies that the actual s-finite maximal value equals both original and s-finite integrated operational hockey values. It consumes hockeyValue_eq_original_operational and the preserved PSD sufficiency theorem. Full-support curvature and a real finite value are unnecessary in this direction.

**Theorem 1.11 (Actual all-L1 operational classification).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1_operational_eq_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1_operational_eq_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual full-support curvature and a real c with allL1Value=c, equality of allL1Value with either originalHockeyValue or sFiniteHockeyValue is equivalent to (PSP)(PCP)=(PCP)(PSP). Here S=A+B, C=normalize(S,A), P=interiorProjection C. The theorem consumes the actual L1 hockey identification and the preserved finite-value PSD classifier; it includes arbitrary traces and empty, zero and singular output pairs.

**Theorem 1.12 (Original-source convex sufficiency).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_original_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_original_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the common-interior compressions commute, originalL1Value equals originalHockeyValue for every real generator convex on Ioi 0, as extended values. Both sides quantify the original sigma-finite source class, and infinite endpoints remain in scope.

**Theorem 1.13 (The original sigma-finite equality answer).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.original_eq_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.original_eq_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual full-support curvature and a real finite originalL1Value=c, originalL1Value=originalHockeyValue if and only if the original common-interior compressions PSP and PCP commute. This uses originalL1Value_eq_allL1Value and the consumed actual operational classifier. Necessity from infinity=infinity, a global commutator condition and arbitrary von Neumann output algebras are not asserted.

The preserved hockeyValue remains the PSD-overlap expression: O(t) is the supremum of Re Tr(X) over 0<=X<=A and X<=tB; its kernel is t Tr(B)-O(t) on (0,1] and Tr(A)-O(t) on (1,infinity). The newly consumed L1 profile theorem identifies precisely these expressions with both original and s-finite operational infima. Each source test has finite Bochner hockey integrals. At a fixed positive threshold both integrals are preserved by one finite test; no finite test preserving all thresholds is asserted.

Attribution: Hiai, Mosonyi and Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, supply the source equality question. Hiai's canonical spectral reverse tests and operator-convex antecedents are reused through the finite criterion. Matsumoto, A new quantum version of f-divergence, arXiv:1311.4722v4, p. 8, Lemma 4.1, already proves one-cost finite-source compression with bound 2d^2+3. The present unbounded finite-alphabet interface makes no new compression or cardinality claim. Its finite-moment implementation follows the Bayer-Teichmann proof of Tchakaloff's theorem, implemented by MeasurableFiniteMoments.finite_moments, together with the repository's positive-history Radon-Nikodym density theorem. HMT Proposition V.1 supplies the direct positive-L1 min/three-component hockey construction; its formalization is a known antecedent, not a new conjecture KPI. The finite full-support equality criterion, source-class bridge and scalar Stieltjes representation are reused at their exact scopes. This all-L1 integration does not claim a new cubature theorem, general-convex attainment, or worldwide priority.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1Value_eq_maximalValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.allL1_operational_eq_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_allL1_operational_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.commute_implies_original_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.hockeyValue_eq_original_operational`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.integrated_eq_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalHockeyValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.originalL1Value_eq_allL1Value`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.original_eq_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex.sFiniteHockeyValue`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickConvex](MaximalHockeyStickConvex.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest](MaximalHockeyStickL1ReverseTest.md)
