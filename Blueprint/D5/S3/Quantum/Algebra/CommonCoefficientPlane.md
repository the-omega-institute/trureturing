# A common complex coefficient plane

## Abstract

An injective stack of three independent complex 3-by-5 matrices has a common neutral coefficient plane.

**Theorem 1.1 (One plane for the entire Hermitian coefficient kernel).**

$$\forall X \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(5\right), Complex\right),\; ((\operatorname{LinearIndependent}\left(Complex, X\right)) \land (\operatorname{Injective}\left(\operatorname{mulVecLin}\left(\operatorname{stack}\left(X\right)\right)\right))) \Rightarrow (\exists L \in \operatorname{Submodule}\left(Complex, \operatorname{Fin}\left(3\right) \to Complex\right),\; (\operatorname{finrank}\left(Complex, L\right) = 2) \land (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), Complex\right),\; ((\operatorname{IsHermitian}\left(T\right)) \land (\operatorname{conjTranspose}\left(\operatorname{stack}\left(X\right)\right) \cdot \operatorname{kronecker}\left(T, \operatorname{identity}\left(3\right)\right) \cdot \operatorname{stack}\left(X\right) = 0)) \Rightarrow (\forall u \in \operatorname{Fin}\left(3\right) \to Complex,\; (\operatorname{mem}\left(u, L\right)) \Rightarrow (\forall v \in \operatorname{Fin}\left(3\right) \to Complex,\; (\operatorname{mem}\left(v, L\right)) \Rightarrow (\operatorname{dotProduct}\left(\operatorname{star}\left(u\right), \operatorname{mulVec}\left(T, v\right)\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonCoefficientPlane.common_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a complex-linearly independent triple of 3-by-5 complex matrices. The vertical stack S has rows indexed by Fin 3 times Fin 3, in coefficient-first order, with S(r,i),j = X(r)i,j. Assume its multiplication map is injective. There is a complex submodule L of complex dimension two such that, simultaneously for every Hermitian 3-by-3 coefficient matrix T with S* (T tensor I_3) S = 0, and all u,v in L, star(u) dot (T v) = 0. Here star on matrices is conjugate transpose, star on vectors is coordinatewise complex conjugation, and dot is the bilinear coordinate dot product. The conclusion is the full complex pairing. It includes a zero Hermitian coefficient kernel. The coefficient width three, matrix dimensions 3 by 5 and plane dimension two are fixed; these dimensions enter the rank and kernel arguments.

The stack compression equals the double sum of T(r,s) times X(r)* X(s). Positive semidefinite kernel elements vanish by the independent-family coefficient theorem. Two matrix rank-product inequalities, using rank S = 5 in dimension nine, imply rank T at most two for every kernel element. A nonzero Hermitian element therefore has one positive and one negative eigenvalue and one zero eigenvalue. An invertible matrix B puts it into B* T B = diag(1,-1,0). Set Y = B inverse times X on the coefficient index. Then Y(0)*Y(0) = Y(1)*Y(1), so one unitary U satisfies Y(1) = U Y(0).

Write A = Y(0) and Z = Y(2). Injectivity of the stack makes Z injective on ker A, and rank A is two or three. For every coefficient-kernel matrix, restriction to ker A gives T(2,2)=0. If rank A is two, Z(ker A) fills the three-dimensional codomain, so independence forces T(2,0)=T(2,1)=0. When all these cross coefficients vanish, the remaining relation is A* Q(T) A = 0, where Q(T) = (T(0,0)+T(1,1)) I + T(0,1) U + T(1,0) U*. These Hermitian operators commute with U. If one is nonzero, rank A is two and its nontrivial kernel lies in range A. This kernel is U-invariant and contains a U-eigenvector, which gives one phase satisfying every relation. If all Q(T) vanish, any eigenvalue of U gives such a phase.

The kernel containment used here follows directly from dimension three. For a nonzero Hermitian Q and a two-dimensional totally neutral P, either Q vanishes on P, in which case P = ker Q, or some nonzero Qx with x in P defines a nonzero linear functional whose two-dimensional kernel is P. Hermiticity puts ker Q in that functional kernel. If rank A is three and some cross coefficient is nonzero, the cross relations instead make Z(ker A) invariant under U*. An eigenvector there supplies one phase w, and surjectivity of A gives T(2,0)+w T(2,1)=0 and star(1,w,0) dot T(1,w,0)=0 for every kernel matrix. Hermiticity supplies the reverse cross pairing. Thus span{(0,0,1),(1,w,0)} is a common complex neutral plane in the normalized coefficients.

Finally, the kernel matrices for Y = B inverse times X are B* T B. Transporting the normalized plane by B preserves its complex dimension and its full sesquilinear pairing. This establishes one plane for the original entire kernel, without choosing a different plane for each T.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CommonCoefficientPlane.common_plane`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction](../TensorNetworks/BridgeGraph/FlatSpectrumObstruction.md)
