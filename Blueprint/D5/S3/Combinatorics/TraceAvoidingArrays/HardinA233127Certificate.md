# The single-row transition certificate

## Abstract

Exact square-strip transition counts from scanner fibres.

**Theorem 1.1 (Every valid scanner boundary).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate.row_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The theorem is D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.row_counts. Exact scanner fibres reduce each continuation count to label rows, preserving individual colour multiplicities and order constraints. The private proofs cover the 96 completed and two unseen valid boundaries. This public interface is consumed by finite_certificate in the square-strip recurrence module.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate.row_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateOne](HardinA233127CertificateOne.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero](HardinA233127CertificateZero.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
