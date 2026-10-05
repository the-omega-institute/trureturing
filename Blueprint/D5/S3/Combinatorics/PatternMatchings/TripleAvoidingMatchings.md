# The generating function for matchings avoiding 123, 132 and 213

## Abstract

The Catalan-Fibonacci series gives the generating function of all perfect matchings avoiding 123, 132 and 213.

**Theorem 1.1 (The perfect-matching enumeration).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Let a_n count the perfect matchings on 2n ordered vertices avoiding P1 = {123, 132, 213}, with three-arc occurrences requiring all three left endpoints to precede all three right endpoints and with labels complementary to right-endpoint order. Put A(z) = sum a_n z^n and H(z) = sum Cat_k F_{k+3} z^k over nonnegative integers. Then (1-z-zH(z))A(z) = 1-zH(z), equivalently A(z) = (1-zH(z))/(1-z-zH(z)). This enumerates the P1 clause of Section 6, Question 1 of Biswas, Shankar and Sivasubramanian. The identity holds as a formal power series with integer coefficients and includes the empty matching.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk](TripleAvoidingMatchingsBulk.md)
