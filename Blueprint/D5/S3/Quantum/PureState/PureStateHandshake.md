# The Pure-State Handshake

## Abstract

A pure state sandwiches any matrix to a scalar multiple of itself.

**Theorem 1.1 (The pure-state sandwich collapses to a scalar).**

$$\rho X \rho = \operatorname{inner}(v, X v) \cdot \rho,\\\rho \rho = \rho, \operatorname{inner}(v, X v) = \operatorname{Tr}(X \rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized amplitude vector v (inner product of v with itself equal to 1), the rank-one density matrix rho = |v><v| — the outer product with entries rho i j = v i times conjugate of v j — is idempotent (rho times rho = rho), so a pure state is its own square root.

The handshake is the middle identity: for ANY matrix X, sandwiching X between two copies of rho collapses to a scalar multiple, rho X rho = <v, X v> times rho, and that scalar equals the density-matrix expectation Tr(X rho). Specializing X to an inverse state gives the mechanism behind the pure-state divergence handshake. The load-bearing new content is this sandwich-collapse identity — there is no library lemma for rho X rho with a general middle matrix — while the idempotency and the expectation-equals-trace fact are its supporting glue. Only the normalization <v,v> = 1 is used, and only for idempotency; the handshake and the trace identity hold for every v and every X, with no positivity or invertibility hypothesis.

Only the algebraic handshake mechanism is recorded here. The downstream conclusion — that the Belavkin-Staszewski and max divergences of a pure state against sigma both equal the logarithm of <v, sigma-inverse v> — is not covered by this statement.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake`
