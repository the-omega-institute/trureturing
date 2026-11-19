# The normalized disk nome and its Taylor coefficients

## Abstract

The same original period has a normalized holomorphic correction, continuation and nome.

**Definition 1.1 (The original normalized nome on the disk).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialNome.Q0`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialNome.Q0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q0(r)=(r/16)exp(i pi H(r)) uses the same native H. This formula extends the whole source-normalized nome expression across zero.

**Theorem 1.2 (The normalized disk nome and its Taylor coefficients).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define Q0=(r/16)exp(i pi H). It is holomorphic on all of D, with Q0'=exp(i pi H)/(16(1-r)P squared). The exponential and the proved denominator factors are nonzero on D, so Q0' never vanishes there. The sole zero of Q0 is zero.

At zero Q0'=1/16 and Q0''=1/16. Thus the degree-one Taylor coefficient is 1/16, and the degree-two Taylor coefficient Q0''(0)/2! is 1/32. These are coefficients of the holomorphic function at zero. A nonzero derivative gives a local analytic coordinate; it does not prove global injectivity or a global half-plane or unit-disk range.

**Theorem 1.3 (The same literal period and source nome).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex point of the full lens, Q0=exp(i pi tau) for the literal tau=iP(1-r)/P(r). Substituting t0=tau and exponentiating its normalized logarithm gives the factor r/16 exactly.

For every real 0<r<1, the existing original_source_nome and reality of the original periods identify Q0(r)=r exp(2 sourceConstant(sqrt r))/16. The entire expression is extended to D by Q0; no complex extension of sourceConstant is assumed. The full Monster, vertex-algebra, conformal-field, anomaly, fusion, string and AdS/CFT objectives require additional results. No monodromy, global uniformization, operator transport or physical completion follows from these local identities.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialNome.Q0`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialContinuation](OriginalHalfBinomialContinuation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceNome](../VertexAlgebra/TwistedGround/OriginalGaussianSourceNome.md)
