# The actual entrance charge is not identically zero

## Abstract

The actual entrance charge is not identically zero.

**Theorem 1.1 (The actual entrance charge is not identically zero).**

$$\forall i: Bool, \forall a: Bool, \forall k: Nat, \operatorname{entranceCharge}\left(i, a, k, 0\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Invariants.entranceCharge_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual two-point vector v and opposite center a, charge(a,v) is star(v) dot sourceQ*v minus sourceQ(a,a) times star(v) dot v. Both quadratic forms are conserved by the literal pairPulse. A zero current coordinate v(not-a) forces the charge to vanish. Consequently a nonzero charge excludes that zero at every internal real time. sourceQ idempotence is derived from the exact full projection restriction; its Hermitian property is checked on the same literal entries. The original block_mul and block_star declarations are consumed directly at their owner after reindexing the two-point matrix.

entranceCharge(i,a,k,lambda) evaluates this charge on the actual finite pulse entrance restricted to the legal edge. The theorem states nonzero charge at the mathematical reference lambda=0 for every sector, changed address and entrance index. reference_entrance and pair_ready give a nonzero scalar multiple of the ready basis vector; x>0 and x<1 give the nonzero diagonal difference. entranceCharge_analytic additionally proves real analyticity of this same expression, including complex conjugation as a real-linear operation. These are live inputs to the isolated-zero argument. The quadratic identities and analytic machinery are standard; no supplied invariant certificate, arbitrary input-state replacement, or external process law is used.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Invariants.entranceCharge_at_zero`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Edges](Edges.md)
