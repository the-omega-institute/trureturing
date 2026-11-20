# Full native matrix propagation retains every source column

## Abstract

Full native matrix propagation retains every source column.

**Theorem 1.1 (Full native matrix propagation retains every source column).**

$$\forall chi: \operatorname{SourceVector}\left(\right), \forall lambda: Real, \forall k: \operatorname{Fin}\left(15\right), \forall s: Real, \operatorname{fullDuring}\left(chi, lambda, k, s\right) = \operatorname{GlobalDuringVector}\left(chi, lambda, k, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Global.fullDuring_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

fullProjection uses the literal native weighted coefficient at physical center 10+j, equality away from that center and the actual neighboring bits, including fixed b15=1 for the last address. fullPulse keeps its global phase. Both matrices act on the complete Extended carrier. The proof derives zero off-source coefficients and identifies each same-source row with the original full legal-tail projection. Summation over fullCarrierEquiv then proves exact source/tail factorization of the actual matrix action.

For every complex source vector chi, every real lambda, every actual call k and internal real time s, fullDuring equals GlobalDuringVector. The latter denotes globalVector(chi,i mapped to during(i,lambda,k,s)), whose (q,z) coordinate is chi(q)*during(b9(q),lambda,k,s)(z). This identity retains all coordinates and phases, including zero-support source columns. It assumes no source-specific factorization certificate. full_reader_uniform_nonvanishing applies the proved uniform tail theorem: the same eta works for every chi and every q with chi(q) nonzero. This does not assert that an arbitrary chi is operationally preparable. The exact original-prefix preparation bridge and native Bell source probability law remain additional obligations; this module supplies neither of them.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Global.fullDuring_factor`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Fibers](Fibers.md)
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Uniform](Uniform.md)
