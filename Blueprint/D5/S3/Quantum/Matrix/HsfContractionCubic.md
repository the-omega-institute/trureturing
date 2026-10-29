# Endpoint trace certificate

## Abstract

Full contraction cubic trace certificate

**Theorem 1.1 (Exact full contraction identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex matrices A,B,K that are Hermitian, 144 times (2 coefficient2(A+B,A,K) minus 6 coefficient3(A+B,A,K)) equals the sum of four weighted traceGram forms with weights (A,I-K),(A,K),(B,I-K),(B,K) and matrices M00,M01,M10,M11. The eight words are Q,QK,CA,CAK,KCA,CB,CBK,KCB, where Q=A-(A+B)K, CA=AK-KA, CB=BK-KB. Each trace has exact order L (q_i)* R q_j. Only cyclic rotations identify words; no word reversal, projection relation or commutativity is assumed.

**Theorem 1.2 (Positive-direction coefficient inequality).**

Lean statement: `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex U,H,K, assume H,U-H,K,I-K are PSD, including singular endpoints. Then 6 coefficient3(U,H,K) is at most 2 coefficient2(U,H,K). These are the original ordered coefficients of the actual exponent minus two thirds trace expansion. The statement is a coefficient result; actual derivatives and the signed constant-five conclusion require the separate analytic bridge.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_nonneg`
- Dependency: [D5/S3/Quantum/Matrix/HsfContractionGrams](HsfContractionGrams.md)
