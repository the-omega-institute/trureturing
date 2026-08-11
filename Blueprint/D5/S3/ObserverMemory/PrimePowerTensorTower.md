# Prime-Power Tensor Tower of a Finite Window Algebra

## Abstract

A finite window full-matrix algebra is the tensor product of all of its prime-power full-matrix factors.

**Theorem 1.1 (A finite window matrix algebra splits into all prime-power factors).**

$$\forall M>0, M_{M}(\mathbb{C}) \sim_{\mathbb{C}} \operatorname{Tensor}_{p \in \operatorname{primeFactors}(M)} M_{p^{\operatorname{factorization}(M,p)}}(\mathbb{C}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PrimePowerTensorTower.prime_power_tensor_factor_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a nonzero finite window cardinality. The canonical ZMod.equivPi ring equivalence identifies its address type with the dependent product of ZMod (p^(M.factorization p)) over p in M.primeFactors.

Reindexing both matrix coordinates gives the full matrix algebra on that dependent product. The finite Pi tensor product of the factor matrix-unit bases is carried to the global matrix-unit basis, and the map preserves multiplication. This yields a complex algebra equivalence with the actual finite tensor family, not merely an index reordering or a two-factor clock-and-shift identity.

## References

- Truth anchor: `D5/S3/ObserverMemory/PrimePowerTensorTower.prime_power_tensor_factor_decomposition`
