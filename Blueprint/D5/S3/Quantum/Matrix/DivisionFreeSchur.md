# Division-free PSD compression

## Abstract

Undivided Schur minors and mixed polarization preserve positivity on arbitrary finite real matrix carriers.

**Theorem 1.1 (Undivided Schur positivity).**

$$\forall (I:Type), \forall (J:Type), [Fintype\left(I\right)] [Fintype\left(J\right)] \forall (K0:Matrix\left(I, I, \mathbb{R}\right)), (PosSemidef\left(K0\right))\Rightarrow \forall (v:I\Rightarrow\mathbb{R}), \forall (U:Matrix\left(I, J, \mathbb{R}\right)), PosSemidef\left(schur\left(K0, v, U\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/DivisionFreeSchur.schur_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite types I,J, a real PSD matrix K on I, any real vector v on I and any real rectangular matrix U from J to I, set q=v^T K v, d=U^T K U and b=U^T K v. Then schur(K,v,U)=q d-b b^T is PSD. The quadratic-discriminant inequality gives (v^T K w)^2 <= (v^T K v)(w^T K w), including zero pivot. Substituting w=Uz proves the quadratic-form assertion. Hermitian symmetry is retained. Neither a positive pivot nor nonempty carriers nor injectivity of U is assumed.

**Theorem 1.2 (Mixed polarization across two PSD matrices).**

$$\forall (I:Type), \forall (J:Type), [Fintype\left(I\right)] [Fintype\left(J\right)] \forall (K0:Matrix\left(I, I, \mathbb{R}\right)), \forall (K1:Matrix\left(I, I, \mathbb{R}\right)), ((PosSemidef\left(K0\right))\land (PosSemidef\left(K1\right)))\Rightarrow \forall (v:I\Rightarrow\mathbb{R}), \forall (U:Matrix\left(I, J, \mathbb{R}\right)), PosSemidef\left(mixed\left(K0, K1, v, U\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/DivisionFreeSchur.mixed_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite types I,J, real PSD matrices K0,K1 on I and the same v,U, write q_s=v^T K_s v, d_s=U^T K_s U and b_s=U^T K_s v. Then mixed(K0,K1,v,U)=q0 d1+q1 d0-b0 b1^T-b1 b0^T is PSD. For a test vector z, Cauchy-Schwarz bounds beta_s^2 by q_s delta_s, where beta_s=v^T K_s Uz and delta_s=(Uz)^T K_s Uz. Put E=q0 delta1+q1 delta0. All q_s,delta_s are nonnegative and E^2-4 beta0^2 beta1^2=(q0 delta1-q1 delta0)^2+4(q0 q1 delta0 delta1-beta0^2 beta1^2)>=0. Since E>=0 this gives E>=2 beta0 beta1, without division. Both zero-pivot and empty-carrier cases remain covered. The two matrices need no common factorization. RankFourLength28Purity uses this cross-matrix positivity as well as both individual Schur matrices.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/DivisionFreeSchur.mixed_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/DivisionFreeSchur.schur_posSemidef`
