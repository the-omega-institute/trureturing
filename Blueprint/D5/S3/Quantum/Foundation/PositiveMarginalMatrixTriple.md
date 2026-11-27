# Missing singleton marginals on one actual triple

## Abstract

A normalized positive spectator recovers both missing singleton marginals of one actual full-Hermitian triple.

**Definition 1.1 (Actual one-triple input in (24)).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.TripleMarginals`

*Formalization.* `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.TripleMarginals` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The fixed real-bilinear preparations are M from A times A into D and L from D times A into E, with full complex Hermitian carriers and canonical traces. Both preparations are positive on every pair of positive inputs. The actual primitive maps r, p12, p13 and p23 are positive on their entire source cones and trace preserving. The four all-vector readback identities are those of (24), with the same M in each pair output.

**Theorem 1.2 (Recover the two missing singleton marginals).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.triple_recover`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.triple_recover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Given Spans M and any positive c0 of trace one, take r2 = r composed with p23 composed with L(-,c0), as in (26). Its actual preparation readback is r2(M(x,y)) = tr(x)y, as in (27). Take r3 = r2 composed with p13. The trace factorization (25) and real spanning in D extend the calculated r3 readback on products to r3(L(d,c)) = tr(d)c for every d and c. The theorem returns Marginals M r r2 and Marginals L p12 r3, including global positivity and trace preservation for both recovered maps. To apply the binary structure results to L, supply Spans L. This proof covers singleton recovery on the given left triple. Orientation and abstract Euclidean Jordan classification are separate results.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.TripleMarginals`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.triple_recover`
- Dependency: [D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition](PositiveMarginalMatrixComposition.md)
