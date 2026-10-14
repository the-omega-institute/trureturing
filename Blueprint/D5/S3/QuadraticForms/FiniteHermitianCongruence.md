# Finite Hermitian Congruence

## Abstract

A Hermitian matrix over a finite field with nontrivial involution has an identity block and a zero radical in one invertible basis.

**Theorem 1.1 (Normalized orthogonal basis including the radical).**

$$\forall (K : \operatorname{Type}\left(\right)), [\operatorname{Field}\left(K\right)] [\operatorname{Finite}\left(K\right)] \forall (sigma : \operatorname{RingEquiv}\left(K, K\right)), \forall (N : \mathbb{N}), \forall (B : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), K\right)), (\operatorname{Involutive}\left(sigma\right) \land sigma \neq \operatorname{RingEquivRefl}\left(K\right) \land \operatorname{transpose}\left(\operatorname{map}\left(B, sigma\right)\right) = B) \Rightarrow \exists (T : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), K\right)), \operatorname{IsUnit}\left(T\right) \land \operatorname{transpose}\left(T\right) \cdot B \cdot \operatorname{map}\left(T, sigma\right) = \operatorname{diagonal}\left((i : \operatorname{Fin}\left(N\right)) \mapsto \operatorname{ite}\left(\operatorname{val}\left(i\right) < \operatorname{rank}\left(B\right), 1, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FiniteHermitianCongruence.finite_hermitian_congruence` (`✓ std3`). ∎

*Citation.* John D. Fulton (1977). *Representations by Hermitian Forms in a Finite Field of Characteristic Two*. DOI: [10.4153/CJM-1977-017-5](https://doi.org/10.4153/CJM-1977-017-5). URL: <https://doi.org/10.4153/CJM-1977-017-5>.

*Commentary.*

Let K be any finite field, sigma a ring automorphism of K with sigma(sigma(x))=x for every x and sigma different from the identity, N any natural number, and B an N by N matrix satisfying transpose(map(sigma,B))=B. There is an invertible N by N matrix T with transpose(T) B map(sigma,T) equal to the diagonal matrix whose i-th entry is one when i.val is less than rank(B), and zero otherwise. All matrix entries lie in K. The involution acts entrywise on both B and the same T.

The associated form b(x,y)=x-transpose B sigma(y) is linear in its first argument and sigma-semilinear in its second. It satisfies sigma(b(x,y))=b(y,x). If every b(x,x) were zero, comparing the self-pairings of x+y and x+c y for a scalar c with sigma(c) different from c would force every b(x,y) to vanish. Thus every nonzero form has a nonzero self-pairing.

The pivot value a=b(x,x) lies in the fixed field of sigma. Surjectivity of the finite-field norm and its formula c sigma(c) choose c with c sigma(c)=a-inverse. The vector e=c x then has b(e,e)=1. The kernel of the linear functional y mapped to b(y,e) is complementary to the line K e and orthogonal to e in both arguments. Its dimension is one less, so dimension induction constructs a complete normalized orthogonal basis.

When the restricted form is zero, any basis supplies the remaining radical vectors. The induction starts at dimension zero with the empty basis. Invertibility of the basis matrix T and of its sigma image preserves matrix rank, so the number of unit diagonal entries is exactly rank(B). Singular forms, the zero matrix, and N=0 are included; no orthogonal basis or norm-surjectivity premise is supplied.

This is established finite-field Hermitian-form mathematics. Fulton gives the arbitrary-rank characteristic-two congruence on page 170 of the cited paper. The characteristic-two case is included in the displayed theorem. Its conclusion concerns the matrix congruence; character sums and rank-parity or entropy formulas require additional results.

## References

- Truth anchor: `D5/S3/QuadraticForms/FiniteHermitianCongruence.finite_hermitian_congruence`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField](../FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField.md)
