# Centered Kraus trace norm on finite references

## Abstract

A variance budget controls the actual centered Kraus output in ordinary trace norm at every finite reference size.

**Theorem 1.1 (The actual rectangular centered family).**

$$(\forall E: Type, (\forall F: Type, (\forall J: Type, [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(\mathbb{C},E)] [\operatorname{FiniteDimensional}(\mathbb{C},E)], [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(\mathbb{C},F)] [\operatorname{FiniteDimensional}(\mathbb{C},F)], [\operatorname{Fintype}(J)], (\forall V: \operatorname{LinearIsometry}(\mathbb{C},E,F), (\forall h: \operatorname{Family}(J,\operatorname{LinearMap}(\mathbb{C},F,F)), \forall \Delta: \mathbb{R}, (\forall e: E, ((((\forall j: J, \operatorname{IsSymmetric}(h_{j})) \land (0 \le \Delta \land ((\forall x: E, ((\Vert x \Vert = 1) \Rightarrow (\sum_{j\in J} (\Vert h_{j}(V(x)) - \Re(\operatorname{inner}(V(x),h_{j}(V(x)))) V(x) \Vert)^{2} \le \Delta))) \land (((\exists x: E, \Vert x \Vert = 1)) \Rightarrow (\Vert e \Vert = 1)))))) \Rightarrow ((\forall c: \operatorname{Family}(J,\mathbb{R}), (\forall L: \operatorname{Family}(J,\operatorname{LinearMap}(\mathbb{C},E,F)), ((((\forall j: J, c_{j} = \Re(\operatorname{inner}(V(e),h_{j}(V(e))))) \land (\forall j: J, L_{j} = h_{j} V - c_{j} V))) \Rightarrow ((\forall n: \mathbb{N}, (\forall M: \operatorname{Family}(J,\operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),F))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C})), (((\forall j: J, M_{j} = \operatorname{MatrixOf}(\operatorname{stdBasis}(\operatorname{Ltwo}(\operatorname{Fin}(n),E)),\operatorname{stdBasis}(\operatorname{Ltwo}(\operatorname{Fin}(n),F)),\operatorname{Ref}(n,L_{j})))) \Rightarrow ((\forall X: \operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C}), \operatorname{traceNorm}(\sum_{j\in J} M_{j} X M_{j}^{*}) \le 5 \Delta \operatorname{traceNorm}(X))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_centered_kraus_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E and F be arbitrary finite-dimensional complex Hilbert spaces, J any finite type, V a complex linear isometric inclusion of E into F, and h(j) Hermitian endomorphisms of the whole ambient F. Suppose delta is nonnegative and the sum of squared ambient variances is at most delta for every unit vector of E. Choose e in E with norm one whenever E admits a unit vector. Set c(j)=Re(inner(Ve,h(j)Ve)) and L(j)=h(j)V-c(j)V. No component of L(j) in the ambient space is discarded.

For each natural reference size n, amplify each same L(j) coordinatewise on the Hilbert L2 sum of n copies. Let v and w be the standard orthonormal bases chosen by stdOrthonormalBasis for these amplified input and output spaces, and M(j) the rectangular matrix of that amplified map. Every complex input matrix X satisfies traceNorm(sum(j) M(j) X M(j) adjoint) at most 5 delta traceNorm(X). The norm is Re Tr sqrt(X adjoint X), with ordinary trace and no factor of one half. Inputs may be non-Hermitian and reference coordinates may be coupled. The empty Kraus family, zero-dimensional spaces, and n=0 are included.

The simultaneous block-centering theorem supplies the 4 delta expectation displacement and 5 delta ambient energy estimates through the coefficient direction and an equal superposition of extremal eigenvectors. Its actual amplified Kraus adjoint has operator norm at most 5 delta times the test operator norm. Unitary trace-norm duality and a singular-value expansion transfer that inequality to the actual matrix Kraus output. Orthonormal coordinates preserve the operator norm; no dimension comparison of matrix norms is used.

Ltwo(Fin(n),E) denotes the Hilbert L2 sum, stdBasis denotes stdOrthonormalBasis, and Ref(n,L) is the complex linear map satisfying Ref(n,L)(x)(r)=L(x(r)). MatrixOf(v,w,R) is LinearMap.toMatrix in the indicated orthonormal bases. FiniteRank is the complex dimension. The anchor condition is vacuous in the zero input space. This result proves the complete-reference trace-norm bridge for one actual centered rectangular family. Constructing the global center-pinched map and its defect identity, obtaining the variance premise from the same S/H selected branches and unreferenced normalized return error, and proving the full local and whole-family bounds of original Theorem 86.1 remain separate obligations.

**Theorem 1.2 (The actual defect of a unital Hermitian factor family).**

$$(\forall E: Type, (\forall J: Type, [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(\mathbb{C},E)] [\operatorname{FiniteDimensional}(\mathbb{C},E)], [\operatorname{Fintype}(J)], (\forall h: \operatorname{Family}(J,\operatorname{LinearMap}(\mathbb{C},E,E)), \forall \Delta: \mathbb{R}, (\forall e: E, ((((\forall j: J, \operatorname{IsSymmetric}(h_{j})) \land (\sum_{j\in J} h_{j} h_{j} = I \land (0 \le \Delta \land ((\forall x: E, ((\Vert x \Vert = 1) \Rightarrow (\sum_{j\in J} (\Vert h_{j}(x) - \Re(\operatorname{inner}(x,h_{j}(x))) x \Vert)^{2} \le \Delta))) \land (((\exists x: E, \Vert x \Vert = 1)) \Rightarrow (\Vert e \Vert = 1))))))) \Rightarrow ((\forall n: \mathbb{N}, (\forall H: \operatorname{Family}(J,\operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C})), (\forall M: \operatorname{Family}(J,\operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C})), (\forall Q: \operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C}), ((((\forall j: J, H_{j} = \operatorname{MatrixOf}(\operatorname{stdBasis}(\operatorname{Ltwo}(\operatorname{Fin}(n),E)),\operatorname{stdBasis}(\operatorname{Ltwo}(\operatorname{Fin}(n),E)),\operatorname{Ref}(n,h_{j}))) \land ((\forall j: J, M_{j} = H_{j} - \Re(\operatorname{inner}(e,h_{j}(e))) I) \land Q = \sum_{j\in J} M_{j}^{*} M_{j}))) \Rightarrow ((\forall X: \operatorname{Matrix}(\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\operatorname{Fin}(\operatorname{FiniteRank}(\operatorname{Ltwo}(\operatorname{Fin}(n),E))),\mathbb{C}), (X - \sum_{j\in J} H_{j} X H_{j}^{*} = \frac{1}{2} (Q X + X Q) - \sum_{j\in J} M_{j} X M_{j}^{*} \land \operatorname{traceNorm}(X - \sum_{j\in J} H_{j} X H_{j}^{*}) \le 10 \Delta \operatorname{traceNorm}(X)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_unital_kraus_defect_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be an arbitrary finite-dimensional complex Hilbert space and h(j) Hermitian endomorphisms with sum(j) h(j) composed with h(j) equal to the identity. Assume the same all-unit-vector variance budget delta and anchor condition as above. For every reference size n, H(j) is the matrix of the coordinatewise amplification of the same h(j). With c(j)=Re(inner(e,h(j)e)), M(j)=H(j)-c(j)I and Q=sum(j) M(j) adjoint M(j), the displayed centered defect identity holds for every complex input X.

The identity follows by expanding the actual M(j): the scalar linear terms and quadratic scalar terms cancel in the anticommutator minus the Kraus output. Unitality replaces sum(j) H(j) squared by I. The centered Gram norm is at most 5 delta. Testing the exact defect against a maximizing unitary bounds its two anticommutator terms by 5 delta traceNorm(X) each and its centered Kraus term by 5 delta traceNorm(X); the factor one half gives the stated 10 delta bound. No state restriction, reference dimension, rank factor, or least eigenvalue occurs.

This statement concerns a full matrix factor and includes zero E, empty J whenever its unitality premise holds, and n=0. It does not construct the source CP-TNI selected family or infer the variance premise from beta. Center-dependent scalars in a direct sum require the actual center pinching and its transfer terms; those are outside this factor statement.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_centered_kraus_trace_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_unital_kraus_defect_trace_bound`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/UniformVarianceCentering](UniformVarianceCentering.md)
