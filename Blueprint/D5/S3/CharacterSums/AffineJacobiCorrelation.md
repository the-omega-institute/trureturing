# Jacobi correlations along an affine progression

## Abstract

Complete and incomplete correlations of two Jacobi symbols along an affine progression

For natural numbers b and m, let C(p,r,A,L) be the sum of (p/d)(r/d) over d = b + m(A+i) with 0 ≤ i < L. Mathlib defines the Jacobi symbol at every natural denominator, including even denominators and zero. At zero its value is one, so b = m = 0 gives C = L. Under H(p,r) the denominators are positive and odd. In the formula, T = pr. The condition H(p,r) means that b is 3 modulo 4, 4 divides m, and p and r are distinct odd primes, both coprime to m.

**Theorem 1.1 (Cancellation on complete blocks of progression indices).**

$$\forall p \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \left(0 \le \operatorname{C}\left(p, p, A, L\right) \land \operatorname{C}\left(p, p, A, L\right) \le L\right) \land \left(\operatorname{H}\left(p, r\right) \Rightarrow \left(\operatorname{C}\left(p, r, A, T\right) = 0 \land \operatorname{abs}\left(\operatorname{C}\left(p, r, A, L\right)\right) \le \operatorname{mod}\left(L, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/AffineJacobiCorrelation.affine_jacobi_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All denominators d are 3 modulo 4 under H(p,r). Quadratic reciprocity turns the two factors into quadratic characters modulo p and r, each multiplied by a sign independent of the index.

Addition of A, multiplication by the unit m, and addition of b all permute the residues modulo pr. The Chinese remainder theorem identifies these residues with pairs modulo p and r. Summing over the second coordinate gives zero because its quadratic character is nontrivial.

Every complete block of pr consecutive indices therefore contributes zero. Each remaining summand has absolute value at most one. On the diagonal the summands are squares in {0,1} for every b and m.

## References

- Truth anchor: `D5/S3/CharacterSums/AffineJacobiCorrelation.affine_jacobi_correlation`
