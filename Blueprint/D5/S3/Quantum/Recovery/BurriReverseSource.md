# The literal source spaces

## Abstract

The physical complementary state and the source-ordered polar matrix.

The purified amplitude is obtained by applying the specified physical isometry V to the canonical maximally mixed qubit purification. Its row space is the reference qubit times the complete twelve-dimensional environment; all zero coordinates are retained.

**Theorem 1.1 (The actual complementary state).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseSource.complementary_state`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseSource.complementary_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing out the physical output gives X = J (Y squared / 62) J-adjoint, where J is the prescribed six-dimensional injection. The positive square root is J Y J-adjoint divided by sqrt(62).

**Theorem 1.2 (The physical marginals).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseSource.physical_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseSource.physical_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reference marginal is I/2. The environment marginal is diagonal, with active entries (11,10,10)/31 and zero elsewhere. These are partial traces of the same actual purified state.

**Theorem 1.3 (The product-marginal square root).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseSource.product_marginal_root`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseSource.product_marginal_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive root of the tensor product of these actual marginals is the active diagonal (s,t,t,s,t,t)/sqrt(62), extended by zero, with s = sqrt(11) and t = sqrt(10).

**Theorem 1.4 (Appendix A's ordered matrix).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseSource.source_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseSource.source_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the transpose of sqrt(rho tensor sigmaE) times sqrt(X) gives the exact padded matrix J activeM J-adjoint. Here activeM = Y diag(s,t,t,s,t,t)/62. The prescribed identity-padded rotation makes this full right-polar product positive semidefinite.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseSource.complementary_state`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseSource.physical_marginals`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseSource.product_marginal_root`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseSource.source_matrix`
- Dependency: [D5/S3/Quantum/Recovery/BurriReversePetz](BurriReversePetz.md)
