# An ordered scan characterizes pattern avoidance

## Abstract

Pattern avoidance is equivalent to closing the oldest or second-oldest open arc with a conditional constraint on the next closure.

**Definition 1.1 (The oldest-or-second-oldest rule).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.ScanRules`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.ScanRules` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Scan the vertices from left to right, ordering the open arcs by their left endpoints. Each closure must select the oldest or second-oldest open arc. If a second-oldest arc closes while a younger open arc is present, the next closure must select the oldest arc. Any number of openings may intervene. When exactly two arcs are open, either closure is allowed without this constraint.

**Theorem 1.2 (Equivalence of avoidance and the scan rule).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.scan_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.scan_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every perfect matching on 2n ordered vertices, avoidance of 123, 132 and 213 is equivalent to the oldest-or-second-oldest scan rule and its conditional constraint on the next closure. The condition at height two and arbitrary intervening openings are included.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.ScanRules`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.scan_characterization`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs](TripleAvoidingMatchingsDefs.md)
