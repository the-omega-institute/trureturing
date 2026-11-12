# Asynchronous rigidity of all multilinear masses

## Abstract

Positive asynchronous invariance forces every real multilinear mass to factor.

At a global maximum on K to the power I, strict positivity of the scalar weights forces every updated scalar term to equal that maximum. For each slot, its maximizing section is a nonempty compact convex invariant subset of K. The Markov–Kakutani theorem supplies a fixed point in that section, and the full real fixed dual identifies it with the same mass-one fixed vector sigma. Replacing finitely many slots by sigma preserves the maximum. Apply the argument to minus F to obtain the same minimum. The normalized cube is therefore constant. Since K spans the real carrier, Mathlib MultilinearMap.ext_of_span_eq_top applied to the subtype of K extends this equality to every real tuple. This applies to periodic maps and boundary sigma. It asserts neither convergence of Phi iterates nor convergence of asynchronous iterates, rates, physical copies, or a tensor cone.

**Theorem 1.1 (The original compact convex spanning base).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall C \in \operatorname{ProperCone}\left(\operatorname{Real}\left(\right), A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{span}\left(\operatorname{Real}\left(\right), C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right) \Rightarrow \left(\left(\forall x \in A,\; \operatorname{Mem}\left(x, C\right) \Rightarrow \left(x \neq 0 \Rightarrow 0 < u\left(x\right)\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{base}\left(\operatorname{toPointedCone}\left(C\right), u\right)\right) \land \left(\operatorname{IsCompact}\left(\operatorname{base}\left(\operatorname{toPointedCone}\left(C\right), u\right)\right) \land \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), \operatorname{base}\left(\operatorname{toPointedCone}\left(C\right), u\right)\right) \land \operatorname{span}\left(\operatorname{Real}\left(\right), \operatorname{base}\left(\operatorname{toPointedCone}\left(C\right), u\right)\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.entire_base_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero finite-dimensional real normed space, a closed generating proper cone C and a real linear mass u strictly positive on every nonzero element of C, the entire set of x in C with u(x)=1 is nonempty, compact, convex and spans the real carrier. This set is CircuitBalancedConfirmation.base on C.toPointedCone and the same u. CircuitBalancedConfirmation.base_compact and base_convex give compactness and convexity directly. Its pure_span gives full span of the extreme points; their inclusion in the base gives full base span, and a spanning base in a nonzero carrier is nonempty. No new compactness or normalization argument is needed. This combination supplies the base used by the algebraic tensor fixed-dual theorem and both original mass results.

**Theorem 1.2 (Fixed points inside invariant compact convex sets).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall B \in \operatorname{Set}\left(A\right),\; \operatorname{IsCompact}\left(B\right) \Rightarrow \left(\operatorname{Nonempty}\left(B\right) \Rightarrow \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), B\right) \Rightarrow \left(\operatorname{MapsTo}\left(Phi, B, B\right) \Rightarrow \left(\exists x \in A,\; \operatorname{Mem}\left(x, B\right) \land Phi\left(x\right) = x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.exists_fixed_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi is any real linear endomorphism of a finite-dimensional real normed space. Each nonempty compact convex invariant B contains a fixed point. Apply D5.S3.Geometry.FixedPoint.MarkovKakutani.exists_common_fixed_point to the constant Unit family of the continuous affine map induced by Phi. Finite dimensionality supplies continuity; invariance is unchanged and commutation is reflexive. No mixing premise is needed.

**Theorem 1.3 (Every fixed vector has its original scalar mass).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(u, Phi\right) = u \Rightarrow \left(\left(\forall f \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(f, Phi\right) = f \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; f = \operatorname{smul}\left(c, u\right)\right)\right) \Rightarrow \left(\forall sigma \in A,\; Phi\left(sigma\right) = sigma \Rightarrow \left(u\left(sigma\right) = 1 \Rightarrow \left(\forall x \in A,\; Phi\left(x\right) = x \Rightarrow x = \operatorname{smul}\left(u\left(x\right), sigma\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.fixed_eq_mass_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original mass u is preserved by Phi, and every real linear functional fixed by precomposition with Phi is a scalar multiple of u. Apply rank-nullity to Phi minus the identity and to its real dual; equality of their ranks bounds the real fixed space by one dimension. A fixed sigma of mass one spans it, and applying the original u determines the scalar: every fixed x equals u(x) times sigma. Sigma may be on the cone boundary; this statement needs no cone or interior hypothesis.

**Theorem 1.4 (Factorization on all real inputs).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \forall K \in \operatorname{Set}\left(A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \forall F \in \operatorname{MultilinearMap}\left(\operatorname{Real}\left(\right), \operatorname{constantFamily}\left(I, A\right), \operatorname{Real}\left(\right)\right),\; \operatorname{comp}\left(u, Phi\right) = u \Rightarrow \left(\left(\forall f \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(f, Phi\right) = f \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; f = \operatorname{smul}\left(c, u\right)\right)\right) \Rightarrow \left(\operatorname{IsCompact}\left(K\right) \Rightarrow \left(\operatorname{Nonempty}\left(K\right) \Rightarrow \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), K\right) \Rightarrow \left(\operatorname{span}\left(\operatorname{Real}\left(\right), K\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right) \Rightarrow \left(\operatorname{MapsTo}\left(Phi, K, K\right) \Rightarrow \left(\left(\forall x \in A,\; \operatorname{Mem}\left(x, K\right) \Rightarrow u\left(x\right) = 1\right) \Rightarrow \left(\left(\forall i \in I,\; 0 < alpha\left(i\right)\right) \Rightarrow \left(\operatorname{sum}\left(alpha\right) = 1 \Rightarrow \left(\left(\forall a \in I \to A,\; \operatorname{Mem}\left(a, \operatorname{pi}\left(\operatorname{univ}\left(I\right), {i:I}\mapsto K\right)\right) \Rightarrow F\left(a\right) = \operatorname{sum}\left({i:I}\mapsto alpha\left(i\right) \cdot F\left(\operatorname{update}\left(a, i, Phi\left(a\left(i\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; \forall a \in I \to A,\; F\left(a\right) = c \cdot \operatorname{prod}\left({i:I}\mapsto u\left(a\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.multilinear_mass_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I is any finite index type. Alpha is strictly positive at every index and sums to one. K is a compact convex spanning normalized set, and Phi preserves K and u. The original-cone applications supply the entire normalized base. The full real fixed dual is the line of u. F is an arbitrary real multilinear form; its continuity is proved by a finite basis expansion. Its asynchronous identity need only hold on every normalized tuple. The conclusion holds on all real inputs, with no additional factorization or fixed-tensor hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.entire_base_geometry`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.exists_fixed_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.fixed_eq_mass_smul`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.multilinear_mass_factorization`
- Dependency: [D5/S3/Geometry/FixedPoint/MarkovKakutani](../../Geometry/FixedPoint/MarkovKakutani.md)
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](../Foundation/CircuitBalancedConfirmation.md)
