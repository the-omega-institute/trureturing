# Exact Matrix Units from a Finite Weyl Pair

## Abstract

Finite Fourier combinations of the cyclic window clock and shift form exact matrix units.

**Theorem 1.1 (Weyl Fourier matrix units multiply exactly).**

$$\begin{gathered}\forall M \in \mathbb{N}_{>0},\\\forall i, j, k, l \in \mathbb{Z}/M\mathbb{Z},\\E_{ij}:=(\frac{1}{M}\sum_{a \in \mathbb{Z}/M\mathbb{Z}}\omega_{M}^{-ia}V_{M}^{a})U_{M}^{i-j},\\E_{ij}E_{kl} = \begin{cases}1,&j=k\\0,&j\neq k\end{cases}E_{il}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MatrixUnitCertificate.matrix_unit_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive window cardinality M, Fourier projection of the frozen clock V_M onto address i, followed by the frozen shift U_M^(i-j), defines E_ij. The exponent i-j is forced by the existing entry convention U_M(r,s) = 1 exactly when r-s = 1.

The standard Z/MZ characters enumerate the full finite character group. Exact character orthogonality makes the Fourier projector the single-entry matrix at (i,i), and the shift moves its nonzero column to j. Thus E_ij is exactly the standard single-entry matrix at (i,j).

Consequently E_ij E_kl equals E_il when j=k and is the zero matrix otherwise. This is an identity of complex matrices for every four window indices; it has no residual, norm bound, tolerance, or numerical approximation.

**Theorem 1.2 (Diagonal matrix units resolve the identity).**

$$\forall M \in \mathbb{N}_{>0},\ \sum_{i \in \mathbb{Z}/M\mathbb{Z}}E_{ii} = I_{M}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MatrixUnitCertificate.matrix_units_sum_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the diagonal Fourier matrix units over every cyclic address gives the identity matrix exactly. This is the finite-window completeness relation for the same Weyl-generated family.

## References

- Truth anchor: `D5/S3/Observer/MatrixUnitCertificate.matrix_unit_mul`
- Truth anchor: `D5/S3/Observer/MatrixUnitCertificate.matrix_units_sum_diagonal`
- Dependency: [D5/S3/Observer/WindowRegister](WindowRegister.md)
