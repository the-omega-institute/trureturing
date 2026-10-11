# Polynomial certificates for power ranks

## Abstract

A polynomial normalized at a nilpotent specialization certifies every maximal power rank.

Let K be any field, I a finite matrix index type with decidable equality, and S any type of variables. For a polynomial matrix A and a point x : S → K, write A(x) for the matrix obtained by evaluating every entry at x. No characteristic assumption or finiteness assumption on S is needed.

**Theorem 1.1 (One polynomial certifies all powers).**

$$\forall K \in \operatorname{Type},\; \forall I \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \operatorname{MvPolynomial}\left(S, K\right)\right),\; \forall z \in S \to K,\; \forall H \in \mathbb{N},\; (((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{H} = 0) \land (\forall x \in S \to K,\; \forall r \in \mathbb{N},\; \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(x\right)\right))^{r}\right) \le \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{r}\right))) \Rightarrow (\exists P \in \operatorname{MvPolynomial}\left(S, K\right),\; (\operatorname{eval}\left(z, P\right) = 1) \land (\forall x \in S \to K,\; (\operatorname{eval}\left(x, P\right) \ne 0) \Rightarrow (\forall r \in \mathbb{N},\; \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(x\right)\right))^{r}\right) = \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{r}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/PolynomialPowerRanks.exists_polynomial_power_rank_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the specialization at z is nilpotent with cutoff H and dominates the rank of every power at every point. There is a polynomial P whose value at z is one. At every point where P is nonzero, all power ranks agree with their values at z.

For each r below H, put d equal to the rank of A(z) raised to r. Choose constant left and right matrices taking this power to rank normal form, with an identity block of size d. Lift their entries to constant polynomials and take the determinant of the corresponding block of the transformed polynomial power. Evaluation commutes with multiplication, powers, and determinants, so this determinant evaluates to one at z. A nonzero value gives a full-rank block, and the submatrix and product rank inequalities force rank at least d.

The finite product of these determinants is P. Its value at z is one, and a nonzero product forces every factor to be nonzero. The assumed rank bound supplies the opposite inequality. For powers at least H, nilpotence makes the reference power zero, and the same bound forces rank zero at every point. Empty blocks have determinant one, so zero ranks and empty matrix index types are included.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/PolynomialPowerRanks.exists_polynomial_power_rank_certificate`
