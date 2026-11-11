# Exact realization of the three PB moments

## Abstract

Three actor moments determine a minimal invertible Hermitian environment.

**Theorem 1.1 (Feasibility, minimal dimension, labelled Gram quotient, and physical blocks).**

$$\forall M0 \in \operatorname{Matrix}\left(2, 2, \mathit{Complex}\right),\; \forall M1 \in \operatorname{Matrix}\left(2, 2, \mathit{Complex}\right),\; \forall M2 \in \operatorname{Matrix}\left(2, 2, \mathit{Complex}\right),\; \forall r \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; \left(r = \operatorname{rank}\left(\mathit{M0}\right) \land k = \operatorname{rank}\left(\operatorname{momentGram}\left(\mathit{M0}, \mathit{M1}, \mathit{M2}\right)\right)\right) \Rightarrow \left(\left(\left(\exists m \in \mathit{Nat},\; \exists D \in \operatorname{Matrix}\left(m, m, \mathit{Complex}\right),\; \exists V \in \operatorname{Matrix}\left(2, m, \mathit{Complex}\right),\; \operatorname{Realizes}\left(D, V, \mathit{M0}, \mathit{M1}, \mathit{M2}\right)\right) \Leftrightarrow \left(\operatorname{PosSemidef}\left(\operatorname{momentGram}\left(\mathit{M0}, \mathit{M1}, \mathit{M2}\right)\right) \land \operatorname{ker}\left(\mathit{M0}\right) = \operatorname{ker}\left(\mathit{M2}\right)\right)\right) \land \left(\left(\left(\operatorname{PosSemidef}\left(\operatorname{momentGram}\left(\mathit{M0}, \mathit{M1}, \mathit{M2}\right)\right) \land \operatorname{ker}\left(\mathit{M0}\right) = \operatorname{ker}\left(\mathit{M2}\right)\right) \Rightarrow \left(\left(\exists D \in \operatorname{Matrix}\left(k, k, \mathit{Complex}\right),\; \exists V \in \operatorname{Matrix}\left(2, k, \mathit{Complex}\right),\; \operatorname{IsUnit}\left(D\right) \land \left(\operatorname{Realizes}\left(D, V, \mathit{M0}, \mathit{M1}, \mathit{M2}\right) \land \operatorname{PhysicalCompatibility}\left(D, V, \mathit{M1}\right)\right)\right) \land \left(\operatorname{rank}\left(\mathit{M2}\right) = r \land \left(r \le k \land \left(k \le 2 \cdot r \land 2 \cdot r \le 4\right)\right)\right)\right)\right) \land \left(\forall m \in \mathit{Nat},\; \forall D \in \operatorname{Matrix}\left(m, m, \mathit{Complex}\right),\; \forall V \in \operatorname{Matrix}\left(2, m, \mathit{Complex}\right),\; \operatorname{Realizes}\left(D, V, \mathit{M0}, \mathit{M1}, \mathit{M2}\right) \Rightarrow \left(\left(\operatorname{IsHermitian}\left(\mathit{M0}\right) \land \left(\operatorname{IsHermitian}\left(\mathit{M1}\right) \land \operatorname{IsHermitian}\left(\mathit{M2}\right)\right)\right) \land \left(k \le \operatorname{rank}\left(D\right) \land \left(\operatorname{rank}\left(D\right) \le m \land \operatorname{LabeledGramIdentification}\left(D, V, \mathit{M0}, \mathit{M1}, \mathit{M2}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBMinimalEnvironment.pb_three_moment_minimal_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix three complex two by two matrices M0, M1 and M2. The four by four block Gram matrix Gamma has block rows (M0,M1) and (M1,M2). Write r for rank M0 and k for rank Gamma. The actor coordinates remain the two original complex coordinates. For any natural number m, an actual realization uses a Hermitian m by m matrix D and a two by m coupling V, with ker D contained in ker V. The inverse used in the moments is the actual Moore–Penrose inverse D dagger, including for singular D. The three equalities are M0=V V*, M1=V D dagger V*, and M2=V (D dagger)^2 V*. Every actual realization automatically makes all three moments Hermitian. All kernels are complex.

An actual realization exists exactly when Gamma is positive semidefinite and the kernels of M0 and M2 coincide. Under these conditions an actual realization exists with D invertible on exactly k coordinates. In every actual realization k is at most rank D, which is at most m. Moreover rank M2=r and r <= k <= 2r <= 4. The result includes m=0 and k=0; on the zero space the unique endomorphism is the identity and its own inverse.

For every actual realization set F=V* and G=(D dagger) F. The quotient by ker Gamma has dimension k. The unique labelled identification with ran F plus ran G sends the class of (a,b) to F a + G b. On every pair of representatives its target inner product is exactly z* Gamma w. Consequently the quotient form descends, is positive definite, and makes this identification unitary. It keeps both actor labels and does not assert uniqueness of the environment inverse or an intertwining on the whole space.

For the minimal witness, take any Hermitian B, two real diagonal entries s1 and s2, and either original orientation sigma=1 or sigma=-1. On the direct sum of the actor and environment, t has block rows (B,V) and (V*,D), c is diag(1,2) plus a zero block, and s is diag(s1,s2) plus a zero block. These are Hermitian, as is the original response matrix g=(sigma i/2)(ct-tc)+s. A specified Schur block H equals the actual Schur expression precisely when H=B-M1.

The Penrose identities identify the original support and place both column families inside ran D. For sufficiency a positive Gram factor gives the two column families on their joint span. Equal end kernels give an injective partial operator carrying the first family to the second. Its prescribed block is symmetric by the Hermitian mixed moment. Add the orthogonal complement projection with an imaginary coefficient: the imaginary part of the quadratic form detects every complement component of a kernel vector. The remaining vector vanishes by injectivity of the partial operator. The determinant polynomial is therefore nonzero, so a real coefficient gives an invertible Hermitian extension. Its inverse and the first family give the actual matrix witness in an orthonormal basis.

This is the three-moment result in PB continuation §30.1. The Gram factor and orthogonal projection are standard finite linear algebra, and the actual inverse uses the repository's finite Penrose construction. The result makes no claim about P2 or PB transfer or classification.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBMinimalEnvironment.pb_three_moment_minimal_realization`
- Dependency: [D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance](../../Observer/Hilbert/FiniteSynthesisGramDistance.md)
