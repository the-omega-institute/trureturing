# Scanner fibres and boundary certificates

## Abstract

Exact square-strip transitions by first boundary label.

**Theorem 1.1 (The six-coordinate scanner-fibre sum).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{q0: \operatorname{Fin}\left(3\right)} (\sum_{q1: \operatorname{Fin}\left(3\right)} (\sum_{q2: \operatorname{Fin}\left(3\right)} (\sum_{q3: \operatorname{Fin}\left(3\right)} (\sum_{q4: \operatorname{Fin}\left(3\right)} (\sum_{q5: \operatorname{Fin}\left(3\right)} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255LiteralBridge}.\operatorname{rowWeight}\left(s, ![q0, q1, q2, q3, q4, q5]\right)) \cdot ((\operatorname{if} ((\forall (j: \operatorname{Fin}\left(5\right)), (![q0, q1, q2, q3, q4, q5]\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne ![q0, q1, q2, q3, q4, q5]\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\forall (j: \operatorname{Fin}\left(6\right)), (p\left(j\right) \ne ![q0, q1, q2, q3, q4, q5]\left(j\right))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255LiteralBridge}.\operatorname{rowFinish}\left(s, ![q0, q1, q2, q3, q4, q5]\right), ![q0, q1, q2, q3, q4, q5]\right) = k))) \operatorname{then} (1) \operatorname{else} (0))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.class_fibres_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The theorem D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.class_fibres_normalized replaces individual colour rows by their exact scanner fibres. Its public interface is used by the private boundary proofs in all three certificate modules.

**Theorem 1.2 (The first label is 0).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies ((p\left((0: \operatorname{Fin}\left(6\right))\right) = (0: \operatorname{Fin}\left(3\right))) \implies (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.row_counts_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The theorem D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.row_counts_zero certifies all valid boundaries with the indicated first label. The final row_counts interface consumes it when combining the three first-label cases.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.class_fibres_normalized`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.row_counts_zero`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
