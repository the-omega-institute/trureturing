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

## Application: the complete signed trace-character sum

For this application, let K be any finite field of characteristic two, sigma any nonidentity involutive ring automorphism of K, N any natural number, and B any N by N matrix over K satisfying transpose(map(sigma,B))=B. Put L=NikolovSegal.UnitaryField.fixedField(sigma) and r=rank(B). Vectors are columns indexed by Fin N. The Hermitian identity gives sigma(X-transpose B sigma(X))=X-transpose B sigma(X), so this value defines H_B(X) in L. In the following form and norm equalities, L is identified with its subfield in K; sigma acts entrywise on vectors.

$$
(H_{B} : ((\operatorname{Fin}\left(N\right) \to K) \to L)), H_{B}(X) = \operatorname{transpose}\left(X\right) \cdot B \cdot \operatorname{sigma}\left(X\right) \in L\qquad(\nu : (K \to L)), \nu(x) = \operatorname{AlgebraNorm}\left(L, x\right) = x \cdot \operatorname{sigma}\left(x\right)
$$

Equip L with the canonical ZMod.algebra L 2. The trace in the character below is Algebra.trace (ZMod 2) L, from L to the prime field, and val is the representative zero or one. Thus the character takes values in Complex. LanglandsFirstMainLemma.traceAddChar and traceAddChar_ne_one_iff, applied to the nontrivial AddChar.zmodChar on ZMod 2 with value -1 at one, give this nontrivial additive character of L.

$$
(\psi : (L \to \mathbb{C})), \psi(a) = (-1 : \mathbb{C})^{\operatorname{val}\left(\operatorname{AlgebraTrace}\left(\operatorname{ZMod}\left(2\right), L, a\right)\right)}
$$

Use the same invertible T supplied by finite_hermitian_congruence. The substitution X=T Y is a bijection on the vector space of functions from Fin N to K, and sigma(T Y)=map(sigma,T) sigma(Y). Consequently the congruence changes H_B into the sum of exactly r coordinate norms from K to L, with every remaining coordinate absent. The norm here is Algebra.norm L, whose image in K is x sigma(x) by NikolovSegal.UnitaryField.norm_formula.

$$
H_{B}(T \cdot Y) = \sum_{(i : \operatorname{Fin}\left(N\right)) \mid \operatorname{val}\left(i\right) < r} \nu(\operatorname{Y}\left(i\right))
$$

Write q=|L|. The norm fibre over zero consists only of zero. Each nonzero fibre has q+1 elements: FiniteField.unitsMap_norm_surjective gives surjectivity on units, MonoidHom.card_fiber_eq_of_mem_range identifies their fibre sizes with the kernel, and NikolovSegal.UnitaryField.card_normOne gives that kernel size. AddChar.sum_eq_zero_of_ne_one gives sum over L of psi equal to zero, while psi(0)=1. Grouping the scalar norm sum by these fibres therefore gives the exact negative factor.

$$
\sum_{(x : K)} \psi(\nu(x)) = 1 + ((\lvert L\rvert : \mathbb{C}) + 1) \cdot \sum_{(a : L) \mid a \neq 0} \psi(a) = -(\lvert L\rvert : \mathbb{C})
$$

Additivity of the character turns the diagonal sum into a product of coordinate values. Equiv.sum_comp reindexes by the invertible T, and Fintype.prod_sum factors the sum over all vectors into the coordinate sums. Each of the r norm coordinates contributes -|L| by the scalar calculation; each of the N-r radical coordinates contributes |K| because its character value is psi(0)=1. Hence, with cardinalities cast to Complex, the complete signed sum is

$$
\sum_{(X : (\operatorname{Fin}\left(N\right) \to K))} (-1 : \mathbb{C})^{\operatorname{val}\left(\operatorname{AlgebraTrace}\left(\operatorname{ZMod}\left(2\right), L, H_{B}(X)\right)\right)} = (\lvert K\rvert : \mathbb{C})^{N - \operatorname{rank}\left(B\right)} \cdot (-(\lvert L\rvert : \mathbb{C}))^{\operatorname{rank}\left(B\right)}
$$

This application composes the existing congruence, norm-fibre and character-orthogonality results; it is separate from the displayed Lean congruence theorem. For N=0 the sum and the product are both one. For B=0 the value is |K|^N. Singular forms retain all N-r radical factors, and odd as well as even ranks are included: the factor (-|L|)^r keeps its sign. This calculation makes no Fourier-orbit identification, rank-parity, global-phase or entropy assertion, and does not complete a parent atom. The congruence's unresolved REG obligation remains tracked by issue #16473; this exposition does not settle it.

## References

- Truth anchor: `D5/S3/QuadraticForms/FiniteHermitianCongruence.finite_hermitian_congruence`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField](../FiniteGroups/NikolovSegal/Unitary/UnitaryInvolutionField.md)
