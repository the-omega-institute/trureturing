# Finite two row power concavity

## Abstract

Actual finite power concavity on the full cone of nonnegative two row tables.

**Theorem 1.1 (Concavity on the full nonnegative cone).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.concaveOn_Fq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerConcavity.concaveOn_Fq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite column type and every real 1 < q < 2, Fq is concave on the entire nonnegative cone. The proof differentiates the actual operator trace in the positive definite chart, retains all three symmetric directions in the inverse metric, and passes to all boundary tables by the explicit two column regularization. The empty, singular and axial cases are included.

**Theorem 1.2 (Superadditivity).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.Fq_add_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerConcavity.Fq_add_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full cone concavity and degree one homogeneity imply Fq(W)+Fq(V) <= Fq(W+V) for all nonnegative finite tables.

**Theorem 1.3 (Entrywise monotonicity).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.monotoneOn_Fq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerConcavity.monotoneOn_Fq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 < q < 2, entrywise order between nonnegative tables implies the same order between their actual Fq trace powers.

This supplier does not prove the original Audenaert inequality for arbitrary finite complex positive semidefinite block matrices. The separately proved local output compression budget consumes its full cone concavity. Classical Carlen-Lieb fixed invertible congruence convexity is a different statement and does not supply a substitute for this theorem.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.Fq_add_ge`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.concaveOn_Fq`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerConcavity.monotoneOn_Fq`
- Dependency: [D5/S3/Quantum/NormCompression/FinitePowerMetric](FinitePowerMetric.md)
