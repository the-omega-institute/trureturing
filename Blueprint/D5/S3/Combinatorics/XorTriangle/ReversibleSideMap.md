# Three Turns of a Binary XOR Triangle

## Abstract

The clockwise right-edge map of a finite binary XOR triangle has third iterate equal to the identity. At each width it is a permutation whose inverse is two clockwise turns.

Start with a finite list of Boolean bits. Replace each adjacent pair by its XOR until one bit remains. The right edge is read from the upper-right corner to the apex, with every position retained. The construction is exactly rightEdge from the binary value-one classification, so leading zero bits and the empty row retain their original treatment.

**Theorem 1.1 (Three turns recover the row).**

$$\forall row \in \operatorname{List}\left(\operatorname{Bool}\right),\; \operatorname{rightEdge}\left(\operatorname{rightEdge}\left(\operatorname{rightEdge}\left(row\right)\right)\right) = row$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.rightEdge_cube` (`✓ std3`). ∎

*Citation.* Ilya Bogdanov (2020). *Answer to Number triangle*. URL: <https://mathoverflow.net/a/359278>.

*Commentary.*

For every finite Boolean row, applying rightEdge three times returns that same row. There is no restriction on length or on the first bit. The empty row is included. For a nonempty row of width n plus one, write a cell using nonnegative coordinates a, b and c with a plus b plus c equal to n. One clockwise change of side cyclically permutes these coordinates. The local XOR relation is preserved because any one of its three bits is the XOR of the other two. Three cyclic permutations recover every original cell. The proof identifies these coordinates with the actual adjacent-XOR list construction before applying the rotation identity. The argument is adapted from Ilya Bogdanov's MathOverflow answer 359278, revision 5, under CC BY-SA 4.0.

**Definition 1.2 (A permutation at each fixed width).**

Lean statement: `D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.rightEdgeEquiv`

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.rightEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ilya Bogdanov (2020). *Answer to Number triangle*. URL: <https://mathoverflow.net/a/359278>.

*Commentary.*

For every natural width n, rightEdgeEquiv is an equivalence from Boolean rows of length n to themselves. Its forward function is rightEdge and its inverse applies rightEdge twice. Both compositions are the three-turn identity. Retaining the width is essential: decoding the boundary as a natural number can discard leading zeros. The equivalence gives exact boundary reconstruction for arbitrary rows, beyond the special value-one case. The dimension and proper fixed-vector counting results in Bogdanov's answer require further arguments and are separate statements.

## References

- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.rightEdgeEquiv`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.rightEdge_cube`
- Dependency: [D5/S3/Combinatorics/XorTriangle/ValueOne](ValueOne.md)
