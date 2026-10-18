# Tang–Zhang's real-order reciprocal critical-point inequality

## Abstract

The reciprocal critical-point moment has the sharp Tang–Zhang coefficient for every real p at least one. For p greater than one, equality characterizes coincident nonzero roots. The conjectured equality characterization at p=1 is false.

The source is Q. Tang and T. Zhang, Sharp Schoenberg type inequalities and the de Bruin–Sharma problem, arXiv:2508.10341v3, Conjecture 1.13. Its locator and mathematical statement are supplied by the task brief. No independent current literature search or priority claim is asserted.

Let n be at least one, let z_j be nonzero complex numbers, and set P(z)=z times the product of z−z_j. Let w_k be the n roots of P′, counted with algebraic multiplicity. Repeated z_j are permitted. The polynomial definition and reciprocal-root spectral identification are reused from TangZhangOrderMinusTwo.

**Definition 1.1 (The real-order coefficient).**

$$c_{n,p}=\frac{(n+1)^{p}+n-1}{n}$$

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.c` (`✓ std3`).

*Citation.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

The expression is defined for every natural n and real p; the theorem uses n at least one. Real powers are Real.rpow.

**Definition 1.2 (The inequality and its equality boundary).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim`

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

$\sum_{k=1}^{n} \left|w_{k}\right|^{-p}\leq c_{n,p} \sum_{j=1}^{n} \left|z_{j}\right|^{-p}$

The first conjunct asserts the displayed bound for every natural n at least one, every nonzero complex family z, and every real p at least one. The second asserts the following equivalence for every such family and every real p greater than one.

$(\sum_{k=1}^{n} \left|w_{k}\right|^{-p}=c_{n,p} \sum_{j=1}^{n} \left|z_{j}\right|^{-p}) \iff \forall i,j, z_{i}=z_{j}$

The third conjunct negates the universal equality equivalence at p=1. It is witnessed by n=2 and z=(1,2), whose critical points are 1−sqrt(3)/3 and 1+sqrt(3)/3. Their reciprocal norm sum is 3, equal to 2 times (1+1/2), although the nonzero roots differ. This refutes the source's endpoint equality clause while retaining the conjectured inequality at that endpoint.

**Theorem 1.3 (The sharp bound with the corrected equality range).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/tang-zhang-2025-real-order-schoenberg` (proved) by `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tang-zhang-2025-real-order-schoenberg","declaration_gid":"D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

Write b_j=1/z_j, D=diag(b_j), H=I+J, and R=H^(1/2). The characteristic roots of A=RDR are the reciprocal critical points, including multiplicity. The existing order-minus-two module supplies this spectral reduction and unitary Schur triangularization supplies a basis for the actual matrix A.

For p greater than one, an entire scalar trace function interpolates the weighted Schur moment. Its left strip boundary is bounded by one; the right boundary is bounded by c(n,p) times the sum of the p-th powers of the moduli of b_j. The explicit complex powers of H use the projection J/n. The three-lines theorem yields the asserted bound for all real p greater than one.

Equality at an interior strip point propagates to the right boundary by the maximum modulus principle. Nonorthogonality of the rank-one columns forces the boundary phases to coincide for every imaginary parameter, giving common phase and modulus for the b_j. Conversely, when z_j=a, P′ has the root a with multiplicity n−1 and the root a/(n+1), giving equality directly. The p=1 bound follows from the unitary rank-one trace estimate; the explicit pair (1,2) supplies the endpoint refutation.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.c`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurMomentInequality](SchurMomentInequality.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots](TangZhangConstantRoots.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo](TangZhangOrderMinusTwo.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangRealOrderCounterexample](TangZhangRealOrderCounterexample.md)
