# Symplectic scalar-shear factorization

## Abstract

Every finite real J0-symplectic block matrix admits a bounded scalar shear making the upper-left block invertible and factors into symmetric shears, a dilation and the prescribed Fourier block.

**Theorem 1.1 (Bounded scalar shear and exact factorization).**

$$\forall n: \operatorname{Nat}\left(\right), \forall P: \operatorname{RealMatrix}\left(FinnFinnFinnFinn\right), {\operatorname{SymplecticJ0}\left(P, n\right)} \Rightarrow {\exists t: \operatorname{Nat}\left(\right), {t \le n} \land {\exists E: \operatorname{RealMatrix}\left(n\right), \exists H: \operatorname{RealMatrix}\left(n\right), \exists R: \operatorname{RealMatrix}\left(n\right), {E = \operatorname{aPlusScalarMulB}\left(P, t\right)} \land {\operatorname{IsUnitDet}\left(E\right)} \land {H = \operatorname{nonsingInvMul}\left(E, \operatorname{bBlock}\left(P\right)\right)} \land {R = \operatorname{nonsingInvMulRight}\left(\operatorname{cPlusScalarMulD}\left(P, t\right), E\right)} \land {\operatorname{Symmetric}\left(H\right)} \land {\operatorname{Symmetric}\left(R\right)} \land {\operatorname{ScalarShearFactorization}\left(P, t, E, H, R\right)}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymplecticScalarShear.exists_scalar_shear_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P = [[a,b],[c,d]] with P J0 P^T = J0 and J0 = [[0,I],[-I,0]], the theorem chooses a natural t <= n such that E = a + t b has nonzero determinant. It defines H = E^-1 b and R = (c+t d) E^-1, proves both are symmetric, and returns the exact six-factor identity P = N_R G_E J0 N_-H J0^-1 N_-tI. No invertibility assumption is made on a or b; n = 0 is included.

The proof uses the symplectic block identities, positive definiteness of aa^T+bb^T, the complex determinant at i, and the degree bound for det(a+Xb). The real polynomial argument is a finite existence choice; it makes no computability claim for equality over arbitrary real inputs.

This is a reusable matrix prerequisite for later quantum-unitary work. It does not establish the Schwartz, L2, Weyl, Gibbs, entropy, tensor-product or parent R22 analytic statements.

## References

- Truth anchor: `D5/S3/QuadraticForms/SymplecticScalarShear.exists_scalar_shear_factorization`
