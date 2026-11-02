# Finite Synthesis Gram Distance

## Abstract

Finite synthesis into a Hilbert space gives a singular Gram formula for projection and distance.

Universally, k is an RCLike field, E is a finite-dimensional inner-product space, and H is a complete inner-product space over k. Every V below is continuous and k-linear. Set S = range V, G = V* V and b = V* x. P denotes the independently defined orthogonal projection onto S, infDist is the metric infimum over S, and MP is the constructed Moore-Penrose inverse. No injectivity or invertibility is assumed.

**Theorem 1.1 (Operator projection identity).**

$$\forall V:E\to_{k}H, P_{S} = V\operatorname{MP}(G)V^{*}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjoint target lies in the Gram range. The first Penrose law then yields the normal equation, and the residual is orthogonal to the entire synthesis range. Projection uniqueness gives the displayed equality of operators on H.

**Theorem 1.2 (Squared infimum distance).**

$$\forall V:E\to_{k}H, \forall x\in H, \operatorname{infDist}(x,S)^{2} = \Vert x\Vert^{2}-\Re(\langle b, \operatorname{MP}(G)b\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection minimality identifies infDist with the residual norm; the squared-norm expansion gives the Gram quadratic expression.

**Theorem 1.3 (Reality of the quadratic expression).**

$$\forall V:E\to_{k}H, \forall x\in H, \langle b, \operatorname{MP}(G)b\rangle = \Vert P_{S}x\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative real squared norm on the right is coerced into k. Thus over the complex field this proves reality as well as the value.

**Theorem 1.4 (Identification with the ordinary inverse).**

$$\forall A:E\equiv_{k}E, \operatorname{MP}(A) = A^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.moore_penrose_eq_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any linear equivalence on E. Its ordinary inverse satisfies all four laws, so the imported uniqueness theorem applies.

**Theorem 1.5 (Invertible Gram specialization).**

$$\forall V:E\to_{k}H, \forall x\in H, \forall G:E\equiv_{k}E, G = V^{*}V \Rightarrow \operatorname{infDist}(x,S)^{2} = \Vert x\Vert^{2}-\Re(\langle b, G^{-1}b\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only this specialization assumes that the Gram operator is a linear equivalence. The singular case remains covered by the preceding identities.

Application: a fixed coherent affine constraint.

Let ι be any finite nonempty index set, let i₀ be one of its elements, and let H be a finite-dimensional complex Hilbert space. Thus the number of amplitudes is at least one. For any actual family x : ι → H, retain its fixed cross-input complex phases. Give the coefficient space C^ι its usual Euclidean inner product, conjugate-linear in the first slot. The following application uses the actual synthesis and its Gram operator:

$Xc=\sum_{j\in \iota}c_{j}x_{j}, G=X^{*}X, b=\mathbf{1}$

$D=\operatorname{span}_{\mathbb{C}}\{x_{j}-x_{i_{0}}:j\in \iota\}, q=P_{D^{\perp}}x_{i_{0}}, t_{*}=\Vert q\Vert^{2}$

Every coefficient vector c has Gram energy equal to the real squared norm of its synthesis. Since b has every coordinate equal to one, the constraint is exactly sum c_j = 1, without conjugating the coefficients or changing the input phases.

$\forall c\in \mathbb{C}^{\iota}, \langle c, Gc\rangle=\Vert Xc\Vert^{2}, \langle b, c\rangle=\sum_{j\in\iota}c_{j}$

$\forall z\in H, (\exists c\in \mathbb{C}^{\iota}, \sum_{j\in\iota}c_{j}=1\land Xc=z)\Leftrightarrow z-x_{i_{0}}\in D$

For the forward affine-image inclusion, subtract x_i₀ and distribute the coefficient sum. For the reverse inclusion, write z − x_i₀ as a linear combination of x_j − x_i₀, then add 1 minus the sum of those coefficients to the i₀ coordinate. This gives actual feasible coefficients. Projection gives q − x_i₀ in D and q orthogonal to D. Consequently q is feasible and the minimum is attained:

$\min_{c\in \mathbb{C}^{\iota},\sum_{j\in\iota}c_{j}=1}\langle c, Gc\rangle=t_{*}=\Vert q\Vert^{2}$

$\exists c_{*}\in \mathbb{C}^{\iota}, \sum_{j\in\iota}(c_{*})_{j}=1\land Xc_{*}=q\land\langle c_{*}, Gc_{*}\rangle=t_{*}$

$\forall c\in \mathbb{C}^{\iota}, \sum_{j\in\iota}c_{j}=1\Rightarrow \Vert Xc\Vert^{2}=\Vert q\Vert^{2}+\Vert Xc-q\Vert^{2}\ge t_{*}$

Range case, including singular Gram operators.

Take G⁺ to be the constructed Moore-Penrose inverse, not an assumed optimization oracle. Suppose b lies in range G and put p = G⁺b. The first Penrose law gives Gp = b. Hence a = ⟨b,p⟩ is the real number ‖Xp‖². It is strictly positive: Xp = 0 would imply Gp = 0 and then b = 0, impossible for a nonempty coefficient set.

$b\in \operatorname{range}G\Rightarrow p=G^{+}b, Gp=b, a=\langle b, p\rangle=\Vert Xp\Vert^{2}>0$

$c_{*}=a^{-1}p, \sum_{j\in\iota}(c_{*})_{j}=1, \langle c_{*}, Gc_{*}\rangle=t_{*}=a^{-1}$

For any feasible c, the normal equation makes Xc_* orthogonal to X(c − c_*). The squared-norm decomposition proves minimality, so this explicit normalized Moore-Penrose vector attains the same minimum as q. No invertibility of G is used.

Nonrange case and an actual kernel minimizer.

If b does not lie in range G, the identities range G = (ker G)⊥ and ker G = ker X supply a kernel vector k whose inner product with b is nonzero. Normalize that vector by this inner product:

$\neg(b\in \operatorname{range}G)\Rightarrow \exists k\in \ker G, \langle b, k\rangle\neq0$

$c_{*}=\frac{1}{\langle b, k\rangle}k, \sum_{j\in\iota}(c_{*})_{j}=1, Gc_{*}=0, Xc_{*}=0, \langle c_{*}, Gc_{*}\rangle=t_{*}=0$

This produces an actual feasible minimizer even at the singular boundary. In the range case the value is (b*G⁺b)⁻¹ with a strictly positive real denominator; in the nonrange case it is zero.

Interpretation and realization boundary.

For a common-output task, the same linear contraction must act on every input, and the common output includes all records in that branch. Its coherent budget compares t |sum c_j|² with ‖Xc‖² for every complex c; restricting to sum c_j = 1 gives the optimizer above. The algebra does not replace a fixed-phase amplitude family by its rays or discard input-dependent records. It supplies an abstract optimum and coefficients, not a native finite gate word, coherent control, or availability of the exact projection as a physical branch.

The application uses the finite Moore-Penrose construction and Penrose laws from FiniteMoorePenroseInverse, the Gram and projection identities above, and the standard range/kernel, span and orthogonal-decomposition identities in Mathlib. Its source application is the finite common-branch Gram optimum in AURIC_SHARED_CONTENT_COMPATIBILITY_QUANTUM_ADDRESSING_AND_MAXIMAL_COMMON_BRANCH_V81. The constrained formula is an application of these results.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance_inverse`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_projection`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_quadratic`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.moore_penrose_eq_inverse`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](FiniteMoorePenroseInverse.md)
