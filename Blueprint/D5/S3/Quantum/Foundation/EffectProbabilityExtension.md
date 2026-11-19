# Effect probability extension

## Abstract

Finite additivity on all effects gives a unique density representative.

Let the interface be any finite complex matrix algebra. A single real-valued function on effects is nonnegative, takes value one at the identity, and is additive whenever the sum is an effect. No scalar homogeneity or continuity is assumed. Values outside the effect interval are immaterial.

Equal finite subdivision gives rational homogeneity. Monotonicity and rational approximation give real homogeneity on the unit interval. Scaling each positive matrix into the effect interval defines a positive-cone functional; comparison at a common scale proves independence of scale and additivity.

The positive and negative parts of a Hermitian matrix define its real-linear extension. Equality of two differences is equality of cross sums, which proves well-definedness. Real and imaginary Hermitian parts then give the complex-linear extension. Existing trace-dual positivity represents this functional by a positive matrix. Normalization gives trace one, and the effect span gives uniqueness.

This converse includes dimension two. It supplies the probability representation assumed by the finite-instrument application; neither static event structure nor positive history length implies its probability hypotheses. Busch supplies the mathematical source, while the finite-dimensional construction uses only binary additivity.

## Extreme effects are orthogonal projections

For any finite index type d, let Eff(d) be the full set of complex square matrices E for which E is positive semidefinite and I-E is positive semidefinite. Regard the matrix space as a real vector space. An effect E is extreme when every equality E=t F+(1-t) G with F,G in Eff(d) and real 0<t<1 forces F=G=E. For every complex matrix E, membership in the real extreme points of Eff(d) is equivalent to E being Hermitian and E*E=E, where * denotes matrix multiplication. Thus the extreme effects are exactly the orthogonal projections. There is no nonempty-index, lower-dimension or rank assumption: empty index, dimension one, zero, identity and every projection rank are included.

The representation is the same full effect interval used by the probability extension. MatrixOrder supplies the positive-semidefinite order, with 0<=E equivalent to E.PosSemidef and E<=I equivalent to (I-E).PosSemidef. On Matrix d d ℂ, the Matrix.Norms.L2Operator scope supplies the C-star algebra structure. The star-algebra equivalence CStarMatrix.ofMatrixStarAlgEquiv sends E to the CStarMatrix carrier used above; it and its inverse preserve positivity, identity, subtraction, multiplication, adjoints and real convex combinations. Hence they identify the effect intervals and their real extreme points. Self-adjointness becomes the Hermitian condition, and idempotence remains matrix idempotence.

The supplier is Mathlib.Analysis.CStarAlgebra.Extreme, theorem isStarProjection_iff_mem_extremePoints_setOfPred_nonneg_inter_unitClosedBall. Apply it to the finite complex matrix C-star algebra. CStarAlgebra.mem_Icc_iff_norm_le_one, equivalently CStarAlgebra.norm_le_one_iff_of_nonneg on a positive matrix, identifies the order interval [0,I] with the intersection of the positive cone and the closed operator-norm unit ball. The supplier characterizes its real extreme points as IsStarProjection, whose two fields are self-adjointness and idempotence. This gives both directions of the stated matrix equivalence without restricting to diagonal, real-entry or rank-one matrices. The Mathlib source cites Sakai's C-star algebras and W-star algebras; this application makes no literature-novelty claim.

This conclusion concerns the convex geometry of the full effect interval. Finite additivity, nonnegativity and normalization of a probability assignment remain the separate hypotheses of the density-representation theorem. Extremality supplies neither those probability hypotheses nor an instrument or a rule for state update; claims about repeated measurements require the corresponding instrument assumptions.

**Theorem 1.1 (All complex effects separate matrices).**

Lean statement: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two arbitrary finite complex matrices are equal if their trace pairings agree on every positive contraction in the native C-star matrix algebra. The positive contractions span that algebra. Shared-energy pinching consumes this separation after pinching each test effect into the full total-energy commutant.

**Theorem 1.2 (Unique density representation).**

Lean statement: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation` (`✓ std3`). ∎

*Citation.* Paul Busch (2003). *Quantum States and Generalized Observables — A Simple Proof of Gleason’s Theorem*. DOI: [10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403). URL: <https://arxiv.org/html/quant-ph/9909073v3>.

*Commentary.*

Every nonnegative normalized finitely additive probability on all effects is the trace pairing with exactly one positive trace-one matrix. The construction and uniqueness preserve arbitrary finite interface dimension.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique`
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
