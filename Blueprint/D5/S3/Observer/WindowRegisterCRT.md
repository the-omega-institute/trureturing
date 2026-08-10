# Coprime Tensor Factorization of a Window Register

## Abstract

Coprime finite window clocks and shifts split into two exact CRT tensor factors.

**Theorem 1.1 (A window register splits over two coprime factors).**

$$\gcd(m,n)=1 \Rightarrow (\operatorname{reindex}_{CRT}(V_{mn}), \operatorname{reindex}_{CRT}(U_{mn})) = (\operatorname{kron}(V_{m}^{CRT}, V_{n}^{CRT}), \operatorname{kron}(U_{m}, U_{n})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m and n be positive coprime window cardinalities. The canonical Chinese remainder equivalence reindexes the global address space Z/(mn)Z as Z/mZ times Z/nZ.

The left and right clock factors restrict the global mn-th-root phase to the two coordinate summands. Additivity of the inverse CRT map turns the global diagonal phase into the product of those two local phases, so the reindexed clock is their Kronecker product exactly.

The inverse CRT map also carries a one-step cyclic difference to a one-step difference in each coordinate. Therefore the reindexed shift is the Kronecker product of the two frozen factor shifts. This theorem is the binary coprime decomposition step, applicable in particular to two distinct prime-power factors; it does not assert an iterated prime-power tower.

## References

- Truth anchor: `D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition`
- Dependency: [D5/S3/Observer/WindowRegister](WindowRegister.md)
