# Actual finite cyclic flag graphs and their Jacobi quotient

## Abstract

Actual finite cyclic flag graphs and their Jacobi quotient

**Definition 1.1 (Finite flag graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.Diagram`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.Diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A diagram has an arbitrary finite flag type, a fixed-point-free involutive edge pairing, and a vertex rotor whose cube is the identity. Exactly the fixed rotor flags are labeled leaves, each either ordinary red or blue or a true numbered anchor; all other rotor orbits have length three. No simplicity, connectedness, genus or edge-orientation hypothesis is imposed. Loops and parallel edges are retained.

**Definition 1.2 (The actual AS, IHX and ordinary CL relations).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.JacobiSpace`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.JacobiSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational free module on these actual finite graphs is divided by the span of geometric relators: color- and rotor-preserving flag isomorphisms, reversal of one actual trivalent rotor with sign minus one, the literal six-flag I minus H plus X socket, and exchange of the colors on two actual consecutive ordinary legs. Numbered anchors never participate in CL, and flag isomorphisms preserve every anchor label. The socket preserves the entire edge pairing and every exterior flag, including arbitrary port-to-port pairings. The quotient is not defined by the kernel of a desired normalization map.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.Diagram`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.JacobiSpace`
