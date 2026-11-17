# A simultaneous neutral coefficient plane

## Abstract

An independent complex rectangular triple with injective stack above the strict three-halves threshold has one common neutral complex two-plane.

**Theorem 1.1 (The entire Hermitian coefficient kernel).**

$$\forall a \in Nat,\; \forall b \in Nat,\; (3 \cdot a < 2 \cdot b) \Rightarrow (\forall X \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; ((\operatorname{LinearIndependent}\left(Complex, X\right)) \land (\operatorname{Injective}\left(\operatorname{mulVecLin}\left(\operatorname{stack}\left(X\right)\right)\right))) \Rightarrow (\exists L \in \operatorname{Submodule}\left(Complex, \operatorname{Fin}\left(3\right) \to Complex\right),\; (\operatorname{finrank}\left(Complex, L\right) = 2) \land (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), Complex\right),\; ((\operatorname{IsHermitian}\left(T\right)) \land (\operatorname{conjTranspose}\left(\operatorname{stack}\left(X\right)\right) \cdot \operatorname{kronecker}\left(T, \operatorname{identity}\left(a\right)\right) \cdot \operatorname{stack}\left(X\right) = 0)) \Rightarrow (\forall u \in \operatorname{Fin}\left(3\right) \to Complex,\; (\operatorname{mem}\left(u, L\right)) \Rightarrow (\forall v \in \operatorname{Fin}\left(3\right) \to Complex,\; (\operatorname{mem}\left(v, L\right)) \Rightarrow (\operatorname{dotProduct}\left(\operatorname{star}\left(u\right), \operatorname{mulVec}\left(T, v\right)\right) = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericCommonCoefficientPlane.common_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural dimensions a and b with 3a < 2b, let X be a complex-linearly independent triple of a-by-b matrices. Its stack Z has coefficient-first rows (r,i) and entries Z((r,i),j)=X(r)(i,j). If Z is injective, there is a complex submodule L of coefficient space of complex dimension two. For every Hermitian coefficient matrix T satisfying Z* (T tensor I_a) Z=0, the full sesquilinear pairing vanishes on every pair of vectors in this same L. The quantifiers include a zero kernel and every natural dimension; no nonzero form or signature is assumed.

Two product-rank inequalities force every coefficient-kernel matrix to have rank at most two. Independence excludes nonzero positive or negative semidefinite forms. A nonzero Hermitian form can therefore be put by invertible adjoint congruence into diag(1,-1,0). In these coefficients, equal column Grams give X(1)=U X(0) for a unitary U on the a-dimensional codomain.

Let D=range X(0) and R=X(2)(ker X(0)), with dimensions r and s. Stack injectivity gives r+s=b and s at most a, hence 2r>a. Restricting any kernel form to ker X(0) gives T(2,2)=0 and the cross relation (T(2,0)I+T(2,1)U)D orthogonal to R. For a nonzero cross pair, rank-nullity and the intersection dimension formula provide a nonzero v in D intersect R killed by this cross operator. The second member T(2,1) of that cross pair is nonzero, so v is a U-eigenvector. Pairing this same v against every kernel form gives one phase w with T(2,0)+w T(2,1)=0. A preimage of v under X(0) supplies the remaining neutral quadratic relation.

If all cross pairs vanish, put Q(T)=(T(0,0)+T(1,1))I+T(0,1)U+T(1,0)U*. The relation X(0)*Q(T)X(0)=0 and 2r>a make every Q(T) singular. Diagonalize the same U once. The resulting diagonal entries are real-linear functionals on the real vector space of Hermitian kernel forms. The finite-union theorem over the real field gives one diagonal coordinate vanishing on the whole kernel, and therefore a single phase for all its forms. In either branch, span{(0,0,1),(1,w,0)} is a common neutral complex plane. Invertible coefficient transport preserves its dimension and full pairing in the original coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericCommonCoefficientPlane.common_plane`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](CommonCoefficientPlane.md)
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../BlockNorm/EssentiallyHermitian.md)
