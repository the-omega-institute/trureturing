# Finite grids of smoothed sieve weights

## Abstract

Finite grids of smoothed sieve weights

**Theorem 1.1 (Scaling product moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_moment_div_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_moment_div_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dividing each of k residue functions by c divides their product moment by c to the kth power. The formula applies to both sharp and smooth normalized variables in integer recovery.

**Theorem 1.2 (Scaling the fourth Wick defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_defect_div_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_defect_div_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dividing four residue functions by c divides their fourth moment and each of the three covariance products by c to the fourth power, and therefore scales their Wick defect by the same factor.

**Theorem 1.3 (Vanishing cubic moments on a fixed grid).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_third`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume KuperbergSmoothed. Fix a positive mesh, a bounded endpoint window and a density bound B. The normalized third moments of all admissible grid interval triples tend uniformly to zero over squarefree moduli with density at most B log h. Each tuple first supplies its own constant, with h and the modulus quantified afterwards. There are only finitely many tuples; intersecting their eventual sets takes a common threshold, equivalently their finite maximum. No weight depends on h. Dividing the cubic bound by (h log h) to the power three halves leaves a fixed multiple of h to the power minus one twenty-first times log h to the eighth power.

**Theorem 1.4 (Vanishing fourth Wick defects on a fixed grid).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under KuperbergSmoothed, the normalized fourth Wick defects of all admissible grid interval quadruples tend uniformly to zero over squarefree moduli with density at most B log h. The mesh is fixed before applying the hypothesis to each tuple and taking the maximum of finitely many thresholds. The normalized error is bounded by a fixed multiple of h to the power minus one twenty-eighth times log h to the sixteenth power. KuperbergSmoothed is an explicit premise in finite-sieve expectation coordinates; no implication from a Ramanujan or Fourier formulation is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_defect_div_scale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_grid_smoothed_third`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.sieve_moment_div_scale`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability](SieveFiniteProbability.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry](SieveIntervalGeometry.md)
