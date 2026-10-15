# Signed Original Ghost Calculation

## Abstract

Actual ordered ghost stress and BRST sums on the complete nonpositive ghost energy fiber.

**Theorem 1.1 (Exact signed ghost action).**

$$\forall S, \operatorname{energy}\left(S\right) \le 0 \Rightarrow \operatorname{ghostDoubleSum}\left(\operatorname{single}\left(S, 1\right)\right) = \operatorname{lowEnergyGhostAction}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.ghostDoubleSum_nonpositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action is four times the {1,5} basis vector for S={3}, twice the {1,3} vector for S={1}, and zero for every other nonpositive-energy subset. The support theorem proves that these cases exhaust the native exterior Fock states at these energies.

This is the sum before multiplication by one half in the original Q. The proof uses the actual ghost L modes, the original normalPair ordering threshold, and the exterior insertion and erasure signs. Support bounds reduce each already finite original sum to an explicit rectangle; no occupation cutoff is assumed.

**Theorem 1.2 (Original tensor charge).**

$$\operatorname{Q}\left(D, H, \operatorname{tensor}\left(u, g\right)\right) = \operatorname{matterGhostSum}\left(u, g\right) + (1/2)\times \operatorname{tensor}\left(u, \operatorname{ghostDoubleSum}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.Q_tmul_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matter term is the sum over every integer n of L(n)u tensor c(-n)g. The second term is the original ordered ghost sum, not an auxiliary delta. The existing statewise finite support laws justify splitting and transporting the sums on arbitrary actual tensor states.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.Q_tmul_split`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.ghostDoubleSum_nonpositive`
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis](OriginalZeroChargeEnergyBasis.md)
