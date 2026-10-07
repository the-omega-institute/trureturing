# Normalized bases and pending openings

## Abstract

Explicit local transitions retain every earlier survivor comparison at arbitrary height.

**Definition 1.1 (Post-closure base states).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Base`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Base` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

S(m) has one decreasing block of old survivors. T(a,b) has two consecutive nonempty blocks in opening order, each decreasing in closing order, with the older block closing first. Pending openings are kept separately.

**Definition 1.2 (Base survivor count).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.size`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.size` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The size of S(m) is m, and that of T(a,b) is a+b.

**Definition 1.3 (Block boundary).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.cut`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.cut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The boundary is zero for a single block and a for two blocks.

**Definition 1.4 (Normalized state validity).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Valid`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every single-block state is valid. A two-block state is valid when both block sizes are positive.

**Definition 1.5 (Prescribed precedence).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Before`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Before` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The first block precedes the second; within either block, larger opener indices precede smaller ones.

**Definition 1.6 (Deleting zero-sized blocks).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A two-block description with one empty block becomes a single decreasing block of the surviving size.

**Definition 1.7 (Explicit closing-rank rules).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Permitted`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Permitted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Ranks r are zero-based. With k pending openings, S(m) permits r<m+k and m<=r+1. T(a,b) permits exactly r+1=a, still within the active range. Thus the corresponding one-based rank i is r+1.

**Definition 1.8 (The next post-closure base).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.afterClose`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.afterClose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

After closing rank r, the survivors have consecutive block sizes r and size(base)+k-r-1, with empty blocks removed. Pending openings reset to zero.

**Definition 1.9 (Preservation of the old base).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Compatible`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

An old selected opener must precede all other old survivors. Every prescribed old comparison among the remaining openers must agree with the order imposed by this closure.

**Theorem 1.10 (Exactly the permitted ranks preserve the old constraints).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.compatible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Machine.compatible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every valid base and every number of pending openings, compatibility with all old comparisons is equivalent to the explicit S/T closing-rank rule. In a T state, closing a pending opener would reverse a required comparison between the two nonempty old blocks.

**Definition 1.11 (Original indices after deletion).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.liftRank`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.liftRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A surviving index below the deleted rank is unchanged; any other survivor index increases by one when mapped back to the old queue.

**Theorem 1.12 (Ordering survives index deletion).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.before_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Machine.before_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The two-block comparison is unchanged by lifting survivor indices back across the deleted rank.

**Theorem 1.13 (Normalization retains the exact order).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Removing empty blocks preserves survivor size and all pair comparisons and yields a valid base.

**Theorem 1.14 (Every legal transition preserves every earlier comparison).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.transition_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Machine.transition_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The new base has exactly one fewer active opener, is valid, realizes the prescribed two-block order under the actual index deletion, and is compatible with every old precedence constraint.

**Definition 1.15 (General-rank scan letters).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Step`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A vertex either opens an arc or closes an arbitrary zero-based active rank.

**Definition 1.16 (Independent local acceptance).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.AcceptFrom`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.AcceptFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Opening increases the pending count without changing the old base. Closing requires a permitted rank, replaces the base by its normalized survivor state and clears pending openings. The empty suffix requires both old and pending counts to be zero.

**Definition 1.17 (Complete scans).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Accepted`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Machine.Accepted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every n, accepted scans have length 2n and start from S(0) with zero pending openings. The carrier is defined solely by these local rules.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.AcceptFrom`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Accepted`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Base`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Before`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Compatible`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Permitted`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Step`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.Valid`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.afterClose`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.before_lift`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.blocks_spec`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.compatible_iff`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.cut`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.liftRank`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.size`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Machine.transition_spec`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Local](P13Local.md)
