# Inner actions and the augmentation obstruction

## Abstract

Over any field, a fixed-point-free automorphism can act internally on a finite-dimensional simple group-algebra quotient only through augmentation.

**Theorem 1.1 (Rigidity inside the representation image).**

$$\forall k \in Type*,\; \forall N \in Type*,\; \forall V \in Type*,\; [Field\left(k\right)], [Group\left(N\right)], [Finite\left(N\right)], [AddCommGroup\left(V\right)], [Module\left(k, V\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], \forall rho \in Representation\left(k, N, V\right),\; \forall hrho \in IsSimpleModule\left(MonoidAlgebra\left(k, N\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right),\; \forall phi \in MulAut\left(N\right),\; \forall hphi \in \left(\forall n \in N,\; (phi\left(n\right) = n) \Rightarrow (n = 1)\right),\; \forall r \in MonoidAlgebra\left(k, N\right),\; \forall s \in MonoidAlgebra\left(k, N\right),\; \forall hrs \in \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(r\right) \cdot \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(s\right) = 1,\; \forall hsr \in \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(s\right) \cdot \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(r\right) = 1,\; \forall hint \in \left(\forall n \in N,\; \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(r\right) \cdot rho\left(n\right) = rho\left(phi\left(n\right)\right) \cdot \operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\left(r\right)\right),\; \operatorname{Representation}.\operatorname{IsTrivial}\left(rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusInnerActionObstruction.trivial_of_inner_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Let k be any field, N a finite group and V a finite-dimensional k-representation whose k[N]-module is simple. Let phi be an automorphism with phi(n) = n only for n = 1. Suppose r and s in k[N] act as mutually inverse endomorphisms of V and rho(r) rho(n) = rho(phi(n)) rho(r) for every n. Then every rho(n) is the identity. The inverse identities are required only in the representation image; r and s need not be units of k[N].

Choose E as an algebraic closure of a universe lift of k and extend V to X = E tensor_k V. Write R = k[N], B = E[N], and psi : R -> B for coefficient extension. The existing ext_isotypic theorem supplies semisimple, V-isotypic support for X as an R-module: pure tensors generate images of R-linear maps V -> X. This is original k[N]-support. It asserts no E[N]-semisimplicity, and the proof never assumes X is a semisimple B-module.

The nonzero finite-dimensional B-module X contains a nonzero simple B-submodule Y. Its R-support is inherited through supported_submodule. Hence Y contains a simple R-submodule S isomorphic to V, giving an injective R-linear map j : V -> S -> Y. Both psi(r) and psi(s) preserve this same Y because Y is a B-submodule. Their restricted E-linear operators T and Tinv are mutually inverse: coefficient extension transports both image inverse identities. Thus the implementer cannot merely permute the simple constituents under consideration.

The compatibility of coefficient extension with the representation algebra homomorphism transports the intertwining equation to Y. The consumed private ofModule'_action helper identifies its B-module action with the algebra action of its associated representation. Apply trivial_of_equiv_fixedPointFree_of_isAlgClosed to this simple finite-dimensional E-representation and T. It makes N act trivially on Y. R-linearity and injectivity of j then force N to act trivially on V.

**Theorem 1.2 (A simple quotient admitting an inner action is the scalar field).**

$$\forall k \in Type*,\; \forall N \in Type*,\; \forall A \in Type*,\; [Field\left(k\right)], [Group\left(N\right)], [Finite\left(N\right)], [Ring\left(A\right)], [Algebra\left(k, A\right)], [IsSimpleRing\left(A\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, A\right)], \forall q \in AlgHom\left(k, MonoidAlgebra\left(k, N\right), A\right),\; \forall hq \in \operatorname{Function}.\operatorname{Surjective}\left(q\right),\; \forall phi \in MulAut\left(N\right),\; \forall hphi \in \left(\forall n \in N,\; (phi\left(n\right) = n) \Rightarrow (n = 1)\right),\; \forall u \in Units\left(A\right),\; \forall hu \in \left(\forall n \in N,\; q\left(\operatorname{MonoidAlgebra}.\operatorname{of}\left(k, N\right)\left(phi\left(n\right)\right)\right) = \operatorname{Units}.\operatorname{val}\left(u\right) \cdot q\left(\operatorname{MonoidAlgebra}.\operatorname{of}\left(k, N\right)\left(n\right)\right) \cdot \operatorname{Units}.\operatorname{val}\left(\operatorname{Inv}.\operatorname{inv}\left(u\right)\right)\right),\; (\forall n \in N,\; q\left(\operatorname{MonoidAlgebra}.\operatorname{of}\left(k, N\right)\left(n\right)\right) = 1) \land ((q = \operatorname{AlgHom}.\operatorname{comp}\left(\operatorname{Algebra}.\operatorname{ofId}\left(k, A\right), \operatorname{D5}.\operatorname{S3}.\operatorname{ArithUnits}.\operatorname{MinacNguyenTanQuestion35}.\operatorname{augmentation}\left(k, N\right)\right)) \land (Nonempty\left(AlgEquiv\left(k, A, k\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusInnerActionObstruction.inner_action_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

Let k be any field, N a finite group, and A a unital simple k-algebra finite-dimensional over k. Let q : k[N] -> A be a surjective k-algebra homomorphism, phi a fixed-point-free automorphism of N, and u a unit of A satisfying q([phi(n)]) = u q([n]) u^(-1) for every n. Then all q([n]) equal one, q equals the composite k[N] --augmentation--> k --Algebra.ofId--> A, and there exists a k-algebra equivalence A -> k. Here [n] means MonoidAlgebra.of k N n. The augmentation is the existing public D5.S3.ArithUnits.MinacNguyenTanQuestion35.augmentation, sending each [n] to one.

Finite-dimensionality makes A Artinian, so its nonzero regular module has a simple submodule U. Simplicity of the ring makes the unital action A -> End_k(U) faithful. Surjectivity of q makes the induced k[N]-module U simple and supplies preimages r, s of u, u^(-1). Their operators satisfy both inverse identities and the required intertwining equation. The image-rigidity theorem therefore makes N act trivially on U. Faithfulness detects q([n]) = 1 in A itself. The group-algebra universal property gives the exact augmentation factorization. Since q is surjective, the scalar map k -> A is surjective; it is also injective, yielding the displayed algebra equivalence.

An external intertwiner V -> V twisted by phi need not belong to the image algebra. After scalar extension it need not preserve a chosen simple B-submodule. The internal implementer and its inverse do preserve that submodule, which is the extra structure used here. The result requires no splitting-field, perfectness, characteristic, coprimality, separability or Schur-index hypothesis; it also assumes no semisimplicity of E[N] or of the whole extended representation.

For the arithmetic Frobenius direction, if a conjugation from an ambient group induces a fixed-point-free automorphism on N and is implemented by a unit in a simple quotient of k[N], that quotient must be augmentation. Applying this ingredient to representation images still requires proving that the implementer belongs to the relevant image algebra. The stronger normalized-degree statement remains open; this theorem does not prove its missing arithmetic or image-membership steps. The argument is a repository derivation using the existing fixed-point-free trace rigidity and original-module support. The cited Library note supplies the classical representation-theoretic background and provenance, not a claim that this exact synthesis is a new result in the literature.

## References

- Truth anchor: `D5/S3/FiniteGroups/FrobeniusInnerActionObstruction.inner_action_obstruction`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusInnerActionObstruction.trivial_of_inner_image`
- Dependency: [D5/S3/ArithUnits/MinacNguyenTanQuestion35](../ArithUnits/MinacNguyenTanQuestion35.md)
- Dependency: [D5/S3/FiniteGroups/FrobeniusCharacterDegrees](FrobeniusCharacterDegrees.md)
