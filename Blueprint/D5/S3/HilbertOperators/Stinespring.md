# Stinespring dilation for arbitrary completely positive maps

## Abstract

Completely positive maps from arbitrary unital complex C*-algebras admit a common Hilbert-space representation and bounded compression.

**Theorem 1.1 (Generic Stinespring dilation).**

$$\forall (u: Universe), \forall (A: \operatorname{Type}(u)), \forall (H: \operatorname{Type}(u)), [\operatorname{CStarAlgebra}(A)] [\operatorname{PartialOrder}(A)] [\operatorname{StarOrderedRing}(A)] [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(C, H)] [\operatorname{CompleteSpace}(H)] \forall (phi: \operatorname{CPLinearMap}(C, A, \operatorname{B}(H))), \exists (K: \operatorname{Type}(u)), \exists (normedK: \operatorname{NormedAddCommGroup}(K)), \exists (innerK: \operatorname{InnerProductSpace}(C, K)), \exists (completeK: \operatorname{CompleteSpace}(K)), \exists (pi: \operatorname{StarAlgHom}(C, A, \operatorname{B}(K))), \exists (V: \operatorname{CLM}(C, H, K)), \forall (a: A), \forall (x: H), \operatorname{Apply}(\operatorname{phi}(a), x) = \operatorname{Apply}(\operatorname{Adjoint}(V), \operatorname{Apply}(\operatorname{pi}(a), \operatorname{V}(x)))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Stinespring.stinespring_dilation` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Stinespring dilation for arbitrary completely positive maps*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/CStarAlgebra/Stinespring.lean>.

*Commentary.*

Fix any universe u. A and H are types in that SAME universe. C denotes the complex numbers, CPLinearMap(C,A,B(H)) denotes CompletelyPositiveMap A (H ->L[C] H), and B(E) denotes the bounded complex-linear endomorphisms of E. CStarAlgebra A is the unital complex C*-algebra structure. The separate PartialOrder A and StarOrderedRing A instances give the compatible positive cone. H is a complete complex inner product space.

There exist a type K in Type u, its normed additive group, complex inner product and completeness structures, a unital complex star-algebra homomorphism pi from A to B(K), and a bounded complex-linear map V from H to K. For these SAME K, structures, pi and V, every a in A and every x in H satisfy phi(a)(x) = adjoint(V)(pi(a)(V(x))). StarAlgHom(C,A,B(K)) includes preservation of the unit, multiplication, addition, complex scalars and star. CLM(C,H,K) denotes continuous complex-linear maps, equivalently bounded linear maps in this setting. Adjoint(V) is the Hilbert-space adjoint from K to H.

On finitely supported functions f,g from A to H, form the sesquilinear expression obtained by summing inner(f(a), phi(star(a)*b)(g(b))) over their supports. Complete positivity makes its diagonal nonnegative: positive operator matrices have nonnegative quadratic forms, and the matrix with entries star(a)*b is positive. The resulting seminormed inner product space has a separated Hilbert completion K. Left multiplication by c in A has norm bounded by norm(c), so it extends to K. These extensions preserve multiplication, the unit and star and define pi.

The map V sends x to the completion class of the finitely supported function concentrated at the algebra unit with value x. Its norm is at most sqrt(norm(phi(1)))*norm(x). Evaluating the sesquilinear form on these vectors gives inner(V(y), pi(a)(V(x))) = inner(y, phi(a)(x)); adjointness and separation by inner products give the stated identity.

The theorem applies without finite dimension or separability. Complete positivity of phi is required; phi need not preserve the unit or a trace. V is asserted bounded, with no isometry conclusion. No minimality, uniqueness, dimension bound, recovery map or tensor-product realization is asserted. Finite Kraus models are special settings of operator dilation, while this statement permits arbitrary unital C*-algebras and arbitrary complex Hilbert spaces at the stated universe scope.

## References

- Truth anchor: `D5/S3/HilbertOperators/Stinespring.stinespring_dilation`
