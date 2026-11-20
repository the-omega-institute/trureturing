# Golomb equality certificates

## Abstract

Checked equality leaves prove integral gaps and normalized marks.

**Definition 1.1 (Exact certificates for a tied leaf).**

Lean statement: `D5/S3/Combinatorics/Golomb/EqualityReplay.LeafCertificate`

*Formalization.* `D5/S3/Combinatorics/Golomb/EqualityReplay.LeafCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

A certificate checks a contradiction, proves an integral expression for each gap, or closes both signs of a separation relation. It can also exhaust the finite integer ranks of slots in a saturated packing row. Signed combinations use only rows already proved tight, and inequality combinations require nonnegative weights.

**Definition 1.2 (Traversal checks a certificate at every tied bound leaf).**

Lean statement: `D5/S3/Combinatorics/Golomb/EqualityReplay.cover`

*Formalization.* `D5/S3/Combinatorics/Golomb/EqualityReplay.cover` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For the same tree used by the bound proof, the checker recomputes the weighted right-hand side at each bound leaf. A tie consumes the next certificate, keyed by the actual leaf identifier. Acceptance at the root requires an empty remainder.

**Theorem 1.3 (Every normalized mark is integral at an accepted target).**

Lean statement: `D5/S3/Combinatorics/Golomb/EqualityReplay.replay_marks_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Golomb/EqualityReplay.replay_marks_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

A real ruler at the target follows a valid route in one of the two orientations. The checked certificate on that route proves that its gaps are integral. Reflection reverses the gaps, and prefix sums recover every mark from the prescribed initial zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Golomb/EqualityReplay.LeafCertificate`
- Truth anchor: `D5/S3/Combinatorics/Golomb/EqualityReplay.cover`
- Truth anchor: `D5/S3/Combinatorics/Golomb/EqualityReplay.replay_marks_integral`
- Dependency: [D5/S3/Combinatorics/Golomb/Replay](Replay.md)
