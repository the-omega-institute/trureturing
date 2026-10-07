# Real Eigenbasis Closure

## Abstract

Real eigenvalues on a complete orthonormal family determine a self-adjoint closure.

**Theorem 1.1 (The finite eigenbasis operator has a genuine self-adjoint closure).**

$$\forall H \in CompleteComplexInnerProductSpace, I \in Type, e \in \operatorname{HilbertBasis}\left(I, H\right), T \in \operatorname{LinearPartialOperator}\left(H\right), lambda \in I \to \mathbb{R},\; \left(\operatorname{domain}\left(T\right) = \operatorname{span}\left(\operatorname{range}\left(e\right)\right) \land \left(\forall j \in I,\; T\left(e\left(j\right)\right) = lambda\left(j\right) \cdot e\left(j\right)\right)\right) \Rightarrow \left(\operatorname{Closable}\left(T\right) \land \operatorname{SelfAdjoint}\left(\operatorname{closure}\left(T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/EigenbasisClosure.eigenbasis_closable_selfAdjoint` (`✓ std3`). ∎

*Citation.* Tom Ole Diem; Adam Bornemann; Gregory J. Loges (2026). *Self-adjoint closure from a real Hilbert eigenbasis*. URL: <https://github.com/HEPLean/PhysLean/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean>.

*Commentary.*

Let H be a complete complex inner product space and let e be a Hilbert basis indexed by any type I. Let T have exactly the algebraic span of those vectors as its domain. If each vector e of i is an eigenvector with real eigenvalue lambda of i, then T is closable and its genuine closure is self-adjoint.

The coefficients c of i divided by lambda of i minus zeta are square summable when zeta is plus or minus i. The denominator has modulus at least one. Common finite sums converge in both graph coordinates, and the two surjective resolvents identify the closure with its adjoint. Zero and repeated eigenvalues are allowed.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/EigenbasisClosure.eigenbasis_closable_selfAdjoint`
