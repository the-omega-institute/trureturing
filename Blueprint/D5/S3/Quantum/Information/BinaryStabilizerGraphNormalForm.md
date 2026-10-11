# Quadratic amplitudes and the graph form of stabilizer states

## Abstract

Binary quadratic phases describe graph states. A Pauli stabilizer line can be put in this form by single-qubit unitaries.

**Lemma 1.1 (The sign of the binary representative).**

$$\forall (a : \operatorname{ZMod}\left(2\right)), \operatorname{complexSign}\left(a\right) = (-1 : \mathbb{C})^{(a).val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.complex_sign_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complexSign value is −1 raised to the natural representative of a binary residue.

**Definition 1.2 (The binary graph amplitude).**

$$\forall (N : \mathbb{N}), \forall (\Gamma : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))), \operatorname{graphAmp}\left(\Gamma, x\right) = (-1 : \mathbb{C})^{(\operatorname{normalExponent}\left(\Gamma, (x : (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))\right)).val}$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.graphAmp` (`✓ std3`).

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Each edge contributes its binary quadratic monomial. The ordered upper-triangular sum is normalExponent; graphAmp is the complexSign value of that exponent, equivalently −1 raised to its natural representative. This definition accepts every binary matrix, without a symmetry or diagonal hypothesis.

**Theorem 1.3 (A graph amplitude for every stabilizer line).**

$$\forall (N : \mathbb{N}), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{StabilizedBy}\left(pauliSet, \psi\right) \Rightarrow (\exists (U : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), \exists (\Gamma : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \exists (c : \mathbb{C}), (\forall (i : \operatorname{Fin}\left(N\right)), \operatorname{U}\left(i\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((\Gamma).IsSymm \land ((\forall (i : \operatorname{Fin}\left(N\right)), \Gamma(i, i) = 0) \land (\psi = SMul.\operatorname{smul}\left(c, (\operatorname{tensorOp}\left(U\right) *_{v} \operatorname{graphAmp}\left(\Gamma\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.stabilizer_graph_normal_form` (`✓ std3`). ∎

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

The Pauli stabilizers of a nonzero common eigenline span a binary Lagrangian subspace. Coordinate swaps and a diagonal shear express that subspace as the graph of a symmetric matrix with zero diagonal. Hadamard and phase gates implement these transformations, and Pauli signs identify the remaining line with the quadratic amplitude. Taking the inverse gates gives the unitaries U and the scalar c in the displayed equation; SMul.smul denotes scalar action on the amplitude vector.

## References

- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.complex_sign_val`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.graphAmp`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.stabilizer_graph_normal_form`
- Dependency: [D5/S3/Quantum/Information/BinaryLagrangianGraphForm](BinaryLagrangianGraphForm.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../../VertexAlgebra/LatticeTwistedGroundRealization.md)
