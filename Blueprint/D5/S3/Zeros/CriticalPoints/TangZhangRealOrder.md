# Tang–Zhang's real-order reciprocal critical-point inequality

## Abstract

The reciprocal critical-point moment has the sharp Tang–Zhang coefficient for every real p at least one. For p greater than one, equality characterizes coincident nonzero roots. The conjectured equality characterization at p=1 is false.

Q. Tang and T. Zhang, Sharp Schoenberg type inequalities and the de Bruin–Sharma problem, arXiv:2508.10341v3, §1.3, Conjecture 1.13.

Conjecture 1.13. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n be the zeros of P′(z). Then for every real number p ≥ 1 we have Σ_{k=1}^n 1/|w_k|^p ≤ ((n+1)^p + n − 1)/n · Σ_{j=1}^n 1/|z_j|^p. Moreover, equality holds if and only if z_1 = ⋯ = z_n.

Let n be at least one, let z_j be nonzero complex numbers, and set P(z)=z times the product of z−z_j. Let w_k be the n roots of P′, counted with algebraic multiplicity. Repeated z_j are permitted. The polynomial definition and reciprocal-root spectral identification are reused from TangZhangOrderMinusTwo.

**Definition 1.1 (The real-order coefficient).**

$$c_{n,p}=\frac{(n+1)^{p}+n-1}{n}$$

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.c` (`✓ std3`).

*Citation.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

The expression is defined for every natural n and real p; the theorem uses n at least one. Real powers are Real.rpow.

**Definition 1.2 (Conjecture 1.13 as stated).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.conjecture`

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.conjecture` (`✓ std3`).

*Citation.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

For every n≥1 and every nonzero complex family z, the conjecture asserts both the sharp moment inequality and equality if and only if all z_j coincide, for every real p≥1.

**Theorem 1.3 (The endpoint equality criterion is false).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

Conjecture 1.13 is false. For n=2, z=(1,2), and p=1, the critical points are 1−sqrt(3)/3 and 1+sqrt(3)/3. Their reciprocal norm sum is 3, equal to c(2,1) times (1+1/2), although the nonzero roots differ.

**Definition 1.4 (The inequality and its equality boundary).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim`

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

$\sum_{k=1}^{n} \left|w_{k}\right|^{-p}\leq c_{n,p} \sum_{j=1}^{n} \left|z_{j}\right|^{-p}$

The first conjunct asserts the displayed bound for every natural n at least one, every nonzero complex family z, and every real p at least one. The second asserts the following equivalence for every such family and every real p greater than one.

$(\sum_{k=1}^{n} \left|w_{k}\right|^{-p}=c_{n,p} \sum_{j=1}^{n} \left|z_{j}\right|^{-p}) \iff \forall i,j, z_{i}=z_{j}$

The third conjunct is the literal negation of Conjecture 1.13, including both assertions for every real p≥1. Its refutation is witnessed by n=2 and z=(1,2), whose critical points are 1−sqrt(3)/3 and 1+sqrt(3)/3. Their reciprocal norm sum is 3, equal to 2 times (1+1/2), although the nonzero roots differ. This refutes the source's endpoint equality clause while retaining the conjectured inequality at that endpoint.

**Theorem 1.5 (Conjecture 1.13 is false; the sharp bound and strict-order equality case hold).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/tang-zhang-2025-real-order-schoenberg` (refuted) by `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tang-zhang-2025-real-order-schoenberg","declaration_gid":"D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

The result refutes Conjecture 1.13 as stated and proves, in the same conjunction, the sharp inequality for every real p≥1 and the equality equivalence for every real p>1.

For every n≥1, nonzero complex a and real p, the sum of norm(w)^(−p) over roots of the derivative of P(Z)=Z(Z−a)^n equals c(n,p) times the sum of norm(a)^(−p) over Fin n, where c(n,p)=((n+1)^p+n−1)/n. The derivative has the root a with multiplicity n−1 and the root a/(n+1), including the case n=1.

It is false that for every natural n and every nonzero complex family z, equality in the reciprocal-norm moment bound at p=1 is equivalent to all z_j being equal. For n=2 and z=(1,2), P′(Z)=3Z²−6Z+2 has roots 1−sqrt(3)/3 and 1+sqrt(3)/3. Both roots are positive, their reciprocal norm sum is 3, and c(2,1) times (1+1/2) is also 3, while 1 and 2 differ.

Write b_j=1/z_j, D=diag(b_j), H=I+J, and R=H^(1/2). The characteristic roots of A=RDR are the reciprocal critical points, including multiplicity. The existing order-minus-two module supplies this spectral reduction and unitary Schur triangularization supplies a basis for the actual matrix A.

For p greater than one, an entire scalar trace function interpolates the weighted Schur moment. Its left strip boundary is bounded by one; the right boundary is bounded by c(n,p) times the sum of the p-th powers of the moduli of b_j. The explicit complex powers of H use the projection J/n. The three-lines theorem yields the asserted bound for all real p greater than one.

Equality at an interior strip point propagates to the right boundary by the maximum modulus principle. Nonorthogonality of the rank-one columns forces the boundary phases to coincide for every imaginary parameter, giving common phase and modulus for the b_j. Conversely, when z_j=a, P′ has the root a with multiplicity n−1 and the root a/(n+1), giving equality directly. The p=1 bound follows from the unitary rank-one trace estimate; the explicit pair (1,2) supplies the endpoint refutation.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.c`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.claim`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.conjecture`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.counterexample`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result`
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneComplexPowers](RankOneComplexPowers.md)
