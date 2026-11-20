# Real Golomb ruler bounds

## Abstract

Separated real distances justify the orientation and every row of a checked bound tree.

**Definition 1.1 (Separated distances on an ordered tuple).**

Lean statement: `D5/S3/Combinatorics/Golomb/Replay.RealGolomb`

*Formalization.* `D5/S3/Combinatorics/Golomb/Replay.RealGolomb` (`✓ std3`).

*Citation.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For a tuple of k + 1 real marks, every positive index pair has distance at least one. Distances of two distinct positive index pairs differ in absolute value by at least one. The first condition already gives strict increase. The length is the last mark minus the first.

**Theorem 1.2 (An accepted tree bounds the total gap length).**

Lean statement: `D5/S3/Combinatorics/Golomb/Replay.check_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Golomb/Replay.check_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Every admissible separation relation covers the two signs used at a branch. A nonnegative combination of valid inequalities either proves a scaled lower bound or gives a contradiction. At equality with the target, the route ends at a bound leaf whose weighted right-hand side equals the scaled target and whose positively weighted rows are tight.

**Theorem 1.3 (The verified bound holds in both orientations).**

Lean statement: `D5/S3/Combinatorics/Golomb/Replay.replay_marks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Golomb/Replay.replay_marks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Consecutive gaps express the distance of every span as a contiguous sum. Static rows are justified by unit distances, smaller-ruler bounds, or the triangular lower bound for separated distances. The first and last gaps are separated for at least three marks. One orientation satisfies the archive's prescribed sign, and reflection preserves length.

## References

- Truth anchor: `D5/S3/Combinatorics/Golomb/Replay.RealGolomb`
- Truth anchor: `D5/S3/Combinatorics/Golomb/Replay.check_sound`
- Truth anchor: `D5/S3/Combinatorics/Golomb/Replay.replay_marks`
