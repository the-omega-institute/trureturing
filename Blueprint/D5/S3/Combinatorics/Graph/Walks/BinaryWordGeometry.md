# Words, unit edits and bounded shortest paths

## Abstract

Actual binary-word tree geometry

A word is a finite list of Boolean letters in its physical order. APPEND adds one letter at the right end; POP removes exactly that last letter. A path is an actual finite sequence of these edits. Its length counts every edit, and Within requires the initial, intermediate and terminal words all to satisfy the given height bound.

**Definition 1.1 (Actual binary words).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Word`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Word is the type List Bool, including the empty word and every finite physical bit sequence.

**Definition 1.2 (Longest common initial word).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.lcp`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.lcp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function compares the first letters, retains equal letters and stops at the first difference or at an empty word.

**Definition 1.3 (Actual unit operations).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Step`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two constructors relate w to w followed by one Boolean letter, and that extended word back to w. No other transition has unit cost.

**Definition 1.4 (Actual edit sequences).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Path`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An empty sequence stays at its word. A nonempty sequence consists of one actual Step followed by another actual sequence with the matching endpoint.

**Definition 1.5 (Charged path length).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.length`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.length` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty sequence has length zero; each actual edit adds one.

**Definition 1.6 (All intermediate heights).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Within`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Within` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every path p and natural height L, Within(p,L) requires every word in the sequence, including both endpoints, to have length at most L.

**Definition 1.7 (Common-prefix distance).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.distance`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.distance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any words u and v, distance(u,v) is length(u)+length(v)-2*length(lcp(u,v)), using natural subtraction. The common prefix is no longer than either word.

**Theorem 1.8 (Exact shortest actual POP/APPEND distance).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.shortest_pop_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.shortest_pop_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two actual binary words u and v, lcp(u,v) is a prefix of each and contains every common prefix. Every actual edit path from u to v has length at least distance(u,v). There exists an actual path of exactly that length, all of whose word lengths are at most max(length(u),length(v)). The proof bounds the change in distance under each literal APPEND or POP, then constructs the attaining sequence by popping the suffix of u to the common prefix and appending the suffix of v. Empty words and coincident endpoints are included.

For the finite tree consisting of words of length at most L, endpoints in that tree therefore have a shortest path entirely inside the same tree. This supplies the operation-distance statement in section 39 of Recursive Relational Observation IV. The exact distinct unordered near-pair count IV.113, its finite representation bijection, recorder injection IV.112, bound IV.114 and closed form IV.115 are not established here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Path`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Step`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Within`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.Word`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.distance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.lcp`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.length`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.shortest_pop_append`
