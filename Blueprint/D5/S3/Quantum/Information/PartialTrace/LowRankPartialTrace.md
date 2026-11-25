# Low-rank partial trace on disjoint tensor sites

## Abstract

Two alternative tensor sites share the same rank-constrained projection mass.

**Theorem 1.1 (Partial trace under an actual matrix rank bound).**

Lean statement: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.frobenius_sq_partialTraceLeft_le_rank_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.frobenius_sq_partialTraceLeft_le_rank_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex matrix on a tensor product, the Frobenius norm square of the first-factor partial trace is at most the actual matrix rank times the input norm square. Singular-value decomposition writes the matrix as a sum of rank-one terms. Reshaping each pair of singular vectors bounds the norm of its partial trace by one. Cauchy–Schwarz then bounds the square of the sum of the nonzero singular values.

**Theorem 1.2 (Projection mass on two alternative sites).**

Lean statement: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.two_site_mass_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.two_site_mass_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the two disjoint sites have the same positive dimension m, with any finite remaining factor. Each normalized partial trace inserts an identity on its traced site. The two Hilbert–Schmidt projections commute and compose to the projection that traces both sites. The squared norm of the common complement bounds the sum of the two projection masses by the input mass plus the mass on the union. The union has dimension m squared, so an actual rank cap of m bounds the latter mass by one over m times the input mass. The resulting factor of one plus one over m holds after summing over a finite family, including products through quantum memory blocks of dimension at most m.

**Theorem 1.3 (Attainment by storing the first site).**

Lean statement: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.basis_encoder_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.basis_encoder_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Store the first site and record the basis outcome of the remaining two factors. Each rectangular encoder matrix is a coisometry onto the stored site, and its adjoint products sum to the input identity. The normalized reverse therefore uses the adjoint in each outcome block. Each composite product has rank m. Its squared mass is m on the first site and one on the second site, so the summed bound is attained.

## References

- Truth anchor: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.basis_encoder_attains`
- Truth anchor: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.frobenius_sq_partialTraceLeft_le_rank_mul`
- Truth anchor: `D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.two_site_mass_sum_le`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../PartialTraceMutualInformation.md)
