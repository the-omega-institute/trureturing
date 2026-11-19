# Prime-field norms and relative traces

## Abstract

A prime-cyclic conjugation norm on the original relative module forces relative factors to have zero target trace.

Let p be prime and K a field of characteristic p. The group G is the additive group of K, written multiplicatively only as a type convention. Put V_d=(K[z]_(degree<d))^*, with contragredient action rho_d(a)(lambda)(f)=lambda(f(z-a)). For a natural s, M_(p,s) is the literal direct sum of V_p,V_(2p),...,V_(sp). These are the polynomial modules and the relative setting of Elmer and Kadr, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12), Section 2.2 and Lemma 2.1(iii). K need not be finite for the statements below.

**Theorem 1.1 (A conjugation sum equal to the identity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.relative_norm`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.relative_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed C=(F_p,+) into G by the prime-field inclusion. For every natural s there is an explicit endomorphism t of M_(p,s) such that sum_(c in C) rho_M(c) t rho_M(-c)=id_M. This is an ordinary sum, with no division by p. It includes p=2 and s=0, when the direct sum is the zero space.

On the primal degree<pr polynomials, use Q_r(z)=(z^p-z)^r and t_r(f)=remainder of -z^(p-1)*f modulo Q_r. The polynomial Q_r is monic of degree pr and fixed by prime-field translations, so translation commutes with taking this remainder. The identity sum_(c in F_p) -(z+c)^(p-1)=1 then makes the conjugation sum of t_r the identity. This also holds for r=0: Q_0=1 and the degree<0 space is zero.

Transpose t_r to V_(pr). The dual action uses the inverse group element, and transposition reverses composition; reindexing the finite sum by c->-c gives the stated conjugation sum on the dual. Taking the direct sum of these operators gives t on M_(p,s). Both the minus sign in -z^(p-1) and the inverse in the contragredient are part of the calculation.

**Theorem 1.2 (Trace sees through arbitrary relative factors).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.trace_relativeFactors`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.trace_relativeFactors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s, every K-representation U of G and every equivariant endomorphism h of U which factors through an M_(p,s)-relatively projective module, trace_K(h)=0. Here relatively projective means an actual equivariant retract P of X tensor M_(p,s), with X arbitrary; a factorization of h has maps U->P->U. Neither P nor X is required to be finite-dimensional. The trace operation in the statement is defined for arbitrary U; its application to the classifier uses the ordinary trace on a finite-dimensional U.

Tensor the norm-one operator on M_(p,s) with id_X. If i:P->X tensor M and r:X tensor M->P have r i=id_P, compose the maps U->P->U with i and r. The norm identity expresses h as a sum of p conjugates of one endomorphism of U. Each conjugate has the same target trace, so trace(h)=p*trace(h0)=0 in characteristic p. Only U is traced: no cyclic permutation of a trace across an arbitrary-dimensional factor is needed.

**Theorem 1.3 (A specified p-multiple factor is relatively projective).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.dualTensor_relativeProjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.dualTensor_relativeProjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now let p be prime and char K=p. For a natural s, choose an index c in Fin s and put r=c+1, so 1<=r<=s. For every natural m, the dual of K[z]_(degree<pr) tensor K[z]_(degree<m) is relatively projective with respect to M_(p,s)=the direct sum of V_p,...,V_(ps). There is no finiteness assumption on K, no positivity assumption on m and no restriction excluding p=2. Choosing c requires a nonempty summand set; it does not assert the existence of an index when s=0.

The tensor-dual equivalence identifies this module with V_(pr) tensor V_m. Flip the tensor factors to obtain V_m tensor V_(pr), then tensor the literal inclusion V_(pr)->M_(p,s) and its matching projection with id_(V_m). Their composite is the identity. This is an actual equivariant retract of X tensor M with X=V_m, so it satisfies the original definition of relative projectivity. The general definition continues to allow arbitrary X and arbitrary retract modules P, without finite-dimensional restrictions on either.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.dualTensor_relativeProjective`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.relative_norm`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.trace_relativeFactors`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization](BoundedTensorPolarization.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample](ElmerKadrTensorCounterexample.md)
