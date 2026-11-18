# Original whole-complex-L1 arbitrary-curvature equality classification and simultaneous standard-predual attainment

## Abstract

Original whole-complex-L1 arbitrary-curvature equality classification and simultaneous standard-predual attainment.

**Theorem 1.1 (Original source hinge profiles).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.source_hinges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapOperational.source_hinges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual algebraic positive normal preparation on the entire complex L1, the negative and positive source hinge integrals equal t sigma(1)-a_R(t) and rho(1)-a_R(t). The actual posteriorFamily and pullContinuous preserve both complex moments and the overlap observation. Real min identities and integrability of the original inputs prove the equality; neither endpoint is discarded.

**Definition 1.2 (Original whole-L1 single-hinge cost set).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.standardHingeCosts`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapOperational.standardHingeCosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the cost set itself, before any infimum: all sigma-finite sources of the fixed universe u, all StandardL1Preparation maps on the entire complex L1, all actual a.e. positive complex L1 inputs with exact output moments, and the actual negative or positive hinge integral. The independently defined coefficient-series class is required for every preparation output. The Boolean branch true selects (tq-p)+ and false selects (p-tq)+.

**Definition 1.3 (Original operational single-hinge infimum).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.operationalHinge`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapOperational.operationalHinge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real conditional infimum of standardHingeCosts. The attaining-minimum theorem establishes nonemptiness and a genuine least member for every t>0, so no empty-set infimum convention carries the result.

**Theorem 1.4 (Attained operational normal-overlap formula).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.operational_hinge_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapOperational.operational_hinge_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t>0, the actual original single-hinge infimum is t sigma(1)-v(t) for the negative branch and rho(1)-v(t) for the positive branch. It is a least element of the actual original cost set. Every source gives a feasible actual normal overlap via its posterior family, giving the lower bound. The attained maximum v(t), standard_posterior_realization, and the universe-lifted whole-L1 preparation supply a source attaining the bound with coefficient-series outputs. No chosen state or division by a functional mass is used. These overlap formulas are antecedents in Hiai--Mosonyi--Tomamichel, Proposition V.1, formulas (V.124)-(V.125).

**Definition 1.5 (Literal original maximal-hockey curvature value).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite affine term f(1)s+f_right_prime(1)(r-s) plus the nonnegative curvature integral of the actual original operational single-hinge infima. Thresholds at most one use the negative branch and the rest use the positive branch; the entire atom at one belongs to the negative branch. This is formula (V.126) with reference point one, including zero and singular inputs and arbitrary finite masses.

**Theorem 1.6 (Exact operational curvature identification).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue_eq_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue_eq_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved original single-hinge formulas identify originalHockeyValue with the two actual optimal-normal-overlap deficit integrals. Splitting at Iic 1 and Ioi 1 retains the complete curvature measure. This equality has no finite-value premise and is consumed by the classification and simultaneous attainment endpoint.

**Theorem 1.7 (Exact original operational classification).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.original_operational_equality_iff_finite_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapOperational.original_operational_equality_iff_finite_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any concrete von Neumann algebra in arbitrary Hilbert-space universe v, arbitrary positive coefficient-series rho and sigma, and any real generator convex on the positive ray, assume only that the literal original sInf of standardAttainableCosts in source universe u is real finite. Equality with the literal original maximal-hockey curvature value is equivalent to finite compatibility of actual optimal normal overlaps on the actual curvature support. FiniteCompatibility uses the computed functional antitone secants, not scalar masses alone. The support can be empty, singular continuous, atomic, uncountable, unbounded or accumulate at zero. This theorem is consumed by arbitrary_support_classification.

**Theorem 1.8 (Classification and one actual simultaneous minimizing test).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapOperational.arbitrary_support_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapOperational.arbitrary_support_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete endpoint states finiteness of the original maximal-hockey value, the exact equivalence, and existence under either equivalent condition of one actual whole-complex-L1 Gamma on a finite regular Borel measure on [0,1]. The total measure is rho(1)+sigma(1); both posterior moments are exact, every output is in the independently defined coefficient-series predual, and every overlap on curvature support attains v(t). Its literal closed-perspective cost is the original maximal infimum. The same Gamma constructs a lifted standard-original reverse test in the independent source universe u, with p=x, q=1-x, all outputs in the series predual, and exact finite cost equal to BOTH original operational quantities. Existing unconditional source equivalence and extended attainment are reused. No optimizer, compatible family, full curvature support, finite dimension, trace, injectivity, separability, faithfulness, normalization, support comparability, spectral optimality or finite alphabet is assumed. No necessity for infinity=infinity is asserted. The separate full-support localized-centralizer classification is outside this theorem; worldwide priority remains unresolved.

Hiai--Mosonyi--Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, PDF pp. 34-36 gives the original reverse-test class and operational hockey formulas; (III.11) and (III.16) give the scalar curvature and closed-perspective framework. PDF p. 62 explicitly leaves the last maximal-hockey/maximal equality case open. Standard compactness, positive functional interpolation, Riesz representation and nonnegative integral additivity are antecedents. The separate full-support localized-centralizer classification is outside this statement.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.arbitrary_support_classification`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.operationalHinge`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.operational_hinge_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.originalHockeyValue_eq_overlap`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.original_operational_equality_iff_finite_compatibility`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.source_hinges`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapOperational.standardHingeCosts`
- Dependency: [D5/S3/Quantum/Divergence/NormalOverlapCurvatureEquality](NormalOverlapCurvatureEquality.md)
