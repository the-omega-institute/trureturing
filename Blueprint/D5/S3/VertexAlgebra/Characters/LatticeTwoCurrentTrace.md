# Finite Two-Current Trace

## Abstract

Two neutral currents on complete finite energy grades.

**Definition 1.1 (Original current grade block).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentBlock`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice D, current index i and natural grades n,m, the block from grade m to grade n is the original Y(currentState i) coefficient m-n, followed by the original grade-n projection. Its domain and codomain are the original full charge and ordinary monomial grades.

**Definition 1.2 (Finite actual cycle trace).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentCycleTrace`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentCycleTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assuming the real integral Gram matrix is positive definite, the n-th full grade is finite dimensional. The cycle trace is the complex linear-map trace of B_i(n,m) composed with B_j(m,n) on that grade. No trace on the infinite carrier is taken.

**Definition 1.3 (Ordinary oscillator multiplicity).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.occupationMultiplicity`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.occupationMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicity p_D(a) is the natural cardinality of the original IntegerFiber D a, cast to the complex numbers. Every ordinary oscillator monomial has weight one.

**Theorem 1.4 (Exact finite two-current trace).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actual_two_current_grade_trace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actual_two_current_grade_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive-definite even integral Gram matrix D, every pair i,j of current indices and all natural grades n,m, put Q(beta)=chargeEnergy(beta).toNat and h_i(beta)=bilinear(unitCharge i,beta). If n=m, the actual cycle trace is the sum over positiveChargeCutoff D hD n of h_i(beta) h_j(beta) p_D(n-Q(beta)). If n differs from m, put ell=Nat.dist n m and a=min(n,m)-Q(beta). The trace is ell times G(i,j) times the sum over positiveChargeCutoff D hD min(n,m), and over k from zero through a/ell inclusive, of p_D(a-k ell). All integer and natural coefficients are cast faithfully to the complex numbers; the Gram and charge cross terms retain their signs.

At positive frequency ell, the original creation action multiplies by X(j,ell-1), and the returning annihilator has diagonal coefficient ell G(i,j) times the occupation of that variable plus one. The finite bijection deleting k marked particles identifies pairs (w,k) with k at most w(j,ell-1) with residual occupations of energy a-k ell. Its inverse adds those particles back. This establishes the marked count used in the trace sum. The opposite grade ordering follows from finite rectangular trace cyclicity and Gram symmetry. Equal grades use the original charge zero modes.

The charge cutoff contains every charge in the complete lower grade by positivity. No inverse Gram, determinant-unit, factorial pairing or convergence premise is used. Zero grades and all finite ranks are included; at rank zero there are no current indices. This finite identity makes no analytic, modular or sewing assertion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentBlock`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actualCurrentCycleTrace`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.actual_two_current_grade_trace`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.occupationMultiplicity`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeThetaCharacter](LatticeThetaCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/InvolutionRootlessLowGrades](../Lattice/InvolutionRootlessLowGrades.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
