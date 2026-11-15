# Continuous cutoffs and compressed centralization

## Abstract

Continuous-cutoff optimality and compressed vector-functional centralization for a positive contraction C in an arbitrary concrete von Neumann algebra N and an arbitrary vector Omega.

**Definition 1.1 (Orthogonal closed-range support).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.rangeSupport`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.rangeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orthogonal projection onto the closure of the range of an actual bounded operator. For an algebra element this projection belongs to the same concrete von Neumann algebra: the range closure is invariant under its commutant. For selfadjoint operators its kernel is the original kernel. No measurable functional calculus is used.

**Definition 1.2 (Actual interior support).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.interiorSupport`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.interiorSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is the orthogonal closed-range support of C(1-C). It commutes with C by invariance of both the range closure and the kernel, rather than by an assertion that P is a continuous function of C. The direct identity xi=C xi+(1-C)xi proves the endpoint-kernel decomposition. Every feasible positive X is PXP. Endpoint accumulation, P=0, and the zero Hilbert space remain included.

**Definition 1.3 (Continuous spectral overlap).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.overlap`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G_t is the real continuous functional calculus of x maps to min(x,t(1-x)), applied to C. For t>=0 and a positive contraction it is positive, at most C and at most t(1-C), and belongs to the algebra.

**Definition 1.4 (All ambient feasible operators).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.Feasible`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.Feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X belongs to the concrete von Neumann algebra and satisfies 0<=X, X<=C, and X<=t(1-C). No commutation between X and C is assumed.

**Definition 1.5 (Fixed vector objective).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.vectorValue`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.vectorValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The objective is the real part of the original vector coefficient <Omega,T Omega>. The vector may be zero, and its coefficient need not be faithful.

**Definition 1.6 (Simultaneous overlap optimality).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.AllOverlapOptimal`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.AllOverlapOptimal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real t>0, the actual continuous overlap is feasible and dominates the vector objective of every ambient feasible operator.

**Definition 1.7 (Centralization on the interior corner).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.CompressedCentralizes`

*Formalization.* `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.CompressedCentralizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every Y in the algebra, the complex vector coefficients of (PCP)(PYP) and (PYP)(PCP) agree. The corner is specified by actual compressions, without a separate bundled corner or any representation-normality premise.

**Theorem 1.8 (Compressed centralization implies optimality).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.compressed_centralization_implies_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.compressed_centralization_implies_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centralization is equivalently centralization of C for the compressed vector P Omega. The norm-closed star subalgebra centralizing that vector contains continuous functions of C, and direct vector convergence places the support of (C-s)+ in it. At s=t/(1+t), positive-part identities give the two exact diagonal overlap formulas. Centralization removes both off-diagonal vector coefficients; compression of the two feasibility inequalities gives the objective bound. Feasible operators are supported on P by the proved endpoint-kernel argument.

**Theorem 1.9 (Actual quadratic feasible perturbations).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_cutoff_annihilation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_cutoff_annihilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For selfadjoint E,F in N, any Y in N, and G_t in N, assume u,gamma_E,gamma_F>0 and the three operator margins u(E^2+F^2)<=G_t, gamma_E E^2<=t(1-C)-G_t and gamma_F F^2<=C-G_t. Assume actual optimality of G_t against every feasible X in N. Positive-square Young inequalities show that G_t+epsilon(EYF+(EYF)*)-k epsilon^2(E^2+F^2) is feasible for both signs near zero. Optimality makes its derivative vanish; repeating with iY gives the complex cross coefficient <Omega,EYF Omega>=0. The full criterion constructs these margins explicitly, so they are not supplied as an unproved optimality-to-annihilation assumption.

**Theorem 1.10 (Optimality implies compressed centralization).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_implies_compressed_centralization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_implies_compressed_centralization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use flat continuous ramps min(1,max(0,(n+1)u-b)). Uniform weighted errors and exact kernel annihilation prove strong convergence to orthogonal range supports. An interior ramp applied to x(1-x), a lower ramp complementary to the positive part (x-s)+, and an upper ramp with b=3 give separated cutoffs at r_n=s+2/(n+1). Their three strict margins follow from scalar inequalities and continuous functional calculus. The lower cutoff retains the entire atom at s. Direct convergence of the two vectors in the inner product gives vanishing threshold cross coefficients, hence threshold centralization for P Omega. For s<=t the positive-part increment is bounded between (t-s) times the two threshold supports. Summing these bounds telescopes; finite support sums approximate C in norm with error at most 1/m. Norm closure gives centralization of C for P Omega, equivalently compressed centralization.

**Theorem 1.11 (Endpoint-correct two-way operator criterion).**

Lean statement: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.all_overlap_optimal_iff_compressed_centralizes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.all_overlap_optimal_iff_compressed_centralizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complete complex Hilbert space H, any concrete von Neumann algebra N on H, any C in N with 0<=C<=1, and any vector Omega, simultaneous optimality of every actual continuous overlap G_t for t>0 is equivalent to centralization of PCP on PNP for the original vector coefficient. All support projections are constructed in N. No separability, finite dimension, faithfulness, Borel calculus, complete positivity, Stinespring map, or GNS representation normality is assumed. This operator criterion alone does not establish the original full-curvature maximal-hockey versus maximal-f classification: the original continuous-moment supplier and whole-L1 realization bridge are separate obligations.

The ingredients are standard continuous functional calculus, orthogonal range supports, positive-square inequalities, and continuity of vector coefficients. The proof uses these ingredients directly on arbitrary Hilbert spaces.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.AllOverlapOptimal`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.CompressedCentralizes`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.Feasible`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.all_overlap_optimal_iff_compressed_centralizes`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.compressed_centralization_implies_optimal`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.interiorSupport`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_cutoff_annihilation`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.optimal_implies_compressed_centralization`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.overlap`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.rangeSupport`
- Truth anchor: `D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer.vectorValue`
