# Fifth-root residual repair

## Abstract

For every canonical density state on A times (Fin 2 times C) and every canonical channel from Fin 2 to Fin 2 times C, the actual recovered residual gives a state on the same system with ordinary conditional mutual information zero and distance at most min(1, 6 r^(1/5)). No rank or spectral floor condition is imposed.

**Theorem 1.1 (The actual marginal constrains the phase gap).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual B density state b with reduced-channel residual at most 2r, the phase gap times the modulus of b's off-diagonal entry is bounded by r plus s times the square root of g plus half the coefficient-difference bound and half the flip bound. The trace-one equation separates the sum and difference of the two diagonal-to-coherence coefficients, and isometry orthogonality bounds their sum.

**Theorem 1.2 (A dimension-independent fifth-root physical repair).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite A and C in independent universes, a canonical state rho on A times (Fin 2 times C), and every canonical channel T from Fin 2 to Fin 2 times C, let P be the actual AB marginal of rho. Set r to the half trace distance between rho and referenceState T P. There exists sigma on the same ABC carrier with ordinary qcmi zero and distance from rho at most min(1, 6 r^(1/5)). All ranks, zero eigenvalues, singleton outer dimensions and zero conditional weights are allowed; the density-state input supplies nonemptiness. Ordinary qcmi is S(AB) plus S(BC) minus S(B) minus S(ABC), using the actual marginals of sigma. This residual theorem supplies no bound in terms of the conditional mutual information of rho without a separate recovery theorem, and makes no sharpness or novelty claim.

The maximum centered Hermitian slice is attained. A small maximum yields an A-BC product directly. Otherwise diagonalizing the attained slice transports rho, its actual marginal and T coherently, and controls the total flip probability. A small retained-column gap gives an AB-C product; small B coherence gives a classical pointer repair. For large B coherence the actual marginal equation forces a product comparison. With delta the fifth root of r, the nontrivial scale delta below one sixth gives flip probability at most 2 delta to the fourth power and all comparison bounds at most 6 delta. The distance cap handles the other scales. At r zero, the same geometry gives exactly zero flips and either a common environment vector or zero coherence in the classical repair. Undoing the local B unitary returns sigma to the original system.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair`
- Dependency: [D5/S3/Quantum/Recovery/QubitPhysicalRepair](QubitPhysicalRepair.md)
