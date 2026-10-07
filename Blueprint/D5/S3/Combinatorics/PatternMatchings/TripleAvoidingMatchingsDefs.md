# Perfect matchings and the Catalan-Fibonacci generating function

## Abstract

Perfect matchings avoiding three patterns are counted by an ordinary generating function in the number of arcs.

**Definition 1.1 (Perfect matchings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Matching`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Matching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A perfect matching on 2n ordered vertices is a fixed-point-free involution of the vertices numbered from zero through 2n-1. Each orbit of size two is an arc. The empty matching is included.

**Definition 1.2 (The finite family of perfect matchings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.instFintypeMatching`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.instFintypeMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For each nonnegative integer n, the perfect matchings on 2n ordered vertices form a finite family. An enumeration of this family permits counting those matchings that satisfy pattern avoidance.

**Definition 1.3 (Three-arc pattern occurrences).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Occurs`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Occurs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

An occurrence chooses three increasing left endpoints, all preceding every chosen right endpoint. For each pair of chosen arcs, the order of the right endpoints is opposite to the order of their pattern labels. Thus 123 labels three nested arcs and 321 labels three mutually crossing arcs.

**Definition 1.4 (The three forbidden patterns).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.P1`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.P1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The pattern set P1 consists of 123, 132 and 213, represented by the zero-based label sequences (0,1,2), (0,2,1) and (1,0,2).

**Definition 1.5 (Avoidance of the pattern set).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.AvoidsP1`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.AvoidsP1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A matching avoids P1 when none of its three-arc selections is an occurrence of 123, 132 or 213 under the right-endpoint convention just specified.

**Definition 1.6 (The number of avoiding matchings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.a`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For each nonnegative integer n, a_n is the number of perfect matchings on 2n ordered vertices that avoid P1. Matchings are distinguished by their pairs of vertices.

**Definition 1.7 (The matching generating function).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.aSeries`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.aSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A(z) is the formal power series with integer coefficients whose coefficient of z^n is a_n. The variable counts arcs rather than individual vertices.

**Definition 1.8 (The Catalan-Fibonacci series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.hSeries`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.hSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

H(z) is the sum over nonnegative integers k of Cat_k F_{k+3} z^k, where Cat_k is the kth Catalan number and F_0 = 0, F_1 = 1 are the Fibonacci initial values.

**Definition 1.9 (The enumeration identity).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.claim`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The enumeration asserts (1-z-zH(z))A(z) = 1-zH(z) in the ring of formal power series with integer coefficients. Since 1-z-zH(z) has constant coefficient one, this is equivalent to A(z) = (1-zH(z))/(1-z-zH(z)).

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.AvoidsP1`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Matching`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.Occurs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.P1`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.a`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.aSeries`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.hSeries`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.instFintypeMatching`
