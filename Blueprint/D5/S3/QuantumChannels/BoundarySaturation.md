# CP Boundary Saturation

## Abstract

Positive semidefiniteness of the 2×2 complete-positivity matrix [[1,z],[z̄,p]] forces the coherence boundary ratio |z|²≤p, with equality exactly at the singular CP boundary.

**Theorem 1.1 (The CP matrix bounds the coherence boundary ratio).**

$$\lvert z \rvert^{2} \le p$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/BoundarySaturation.cp_boundary_ratio_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a channel with a pure fixed point, let z = λ_coh and p = λ_pop be the coherence and population decay factors in the tangent space. The 2×2 complete-positivity matrix [[1, z], [z̄, p]] is Hermitian, and its determinant is p − |z|². Positive semidefiniteness gives a nonnegative determinant, hence the coherence RLD boundary ratio |z|²/p is at most one, i.e. |z|² ≤ p.

Equality |z|² = p holds exactly when the determinant vanishes, i.e. when the CP matrix is singular — the channel sits at the complete-positivity boundary. No claim is made about the RLD contraction ratio itself beyond this boundary criterion.

## References
