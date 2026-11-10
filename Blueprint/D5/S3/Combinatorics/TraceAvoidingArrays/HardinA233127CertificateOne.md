# Scanner fibres and boundary certificates

## Abstract

Exact square-strip transitions by first boundary label.

**Theorem 1.1 (The first label is 1).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies ((p\left((0: \operatorname{Fin}\left(6\right))\right) = (1: \operatorname{Fin}\left(3\right))) \implies (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne.row_counts_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The theorem D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.row_counts_one certifies all valid boundaries with the indicated first label. The final row_counts interface consumes it when combining the three first-label cases.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne.row_counts_one`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero](HardinA233127CertificateZero.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
