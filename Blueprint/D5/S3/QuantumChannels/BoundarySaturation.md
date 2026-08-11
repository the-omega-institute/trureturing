# CP Boundary Saturation

## Abstract

Positive semidefiniteness of the 2x2 complete-positivity matrix [[1,z],[conj z,p]] forces the coherence boundary ratio |z|^2 <= p, with equality exactly at the singular CP boundary.

**Theorem 1.1 (The CP matrix bounds the coherence boundary ratio).**

$$\lvert z \rvert^{2} \le p$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/BoundarySaturation.cp_boundary_ratio_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a channel with a pure fixed point, let z = lambda_coh and p = lambda_pop be the coherence and population decay factors in the tangent space. The 2x2 complete-positivity matrix [[1, z], [conj z, p]] is Hermitian, and its determinant is p - |z|^2. Positive semidefiniteness gives a nonnegative determinant, hence the coherence RLD boundary ratio |z|^2 / p is at most one, i.e. |z|^2 <= p.

Equality |z|^2 = p holds exactly when the determinant vanishes, i.e. when the CP matrix is singular -- the channel sits at the complete-positivity boundary. No claim is made about the RLD contraction ratio itself beyond this boundary criterion.

## References

- Truth anchor: `D5/S3/QuantumChannels/BoundarySaturation.cp_boundary_ratio_le_one`
