# Quadratic amplitudes and the graph form of stabilizer states

## Abstract

Binary quadratic phases describe graph states. A Pauli stabilizer line can be put in this form by single-qubit unitaries.

**Lemma 1.1 (The sign of the binary representative).**

$$\forall (a : \operatorname{ZMod}\left(2\right)), \operatorname{complexSign}\left(a\right) = (-1 : \mathbb{C})^{(a).val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.complex_sign_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complexSign value is −1 raised to the natural representative of a binary residue.

**Definition 1.2 (The binary symplectic bilinear form).**

$$\forall (N : \mathbb{N}), \forall (u : ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))), \forall (v : ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))), \operatorname{spForm}\left(N\right)(u, v) = BinaryLagrangianGraphForm.\operatorname{sp}\left(u, v\right)$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.spForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary symplectic form pairs the translation coordinates of either vector with the phase coordinates of the other.

**Lemma 1.3 (Alternation of the binary symplectic form).**

$$\forall (N : \mathbb{N}), (\operatorname{spForm}\left(N\right)).IsAlt$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.sp_alt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every binary vector has zero symplectic pairing with itself.

**Lemma 1.4 (Nondegeneracy of the binary symplectic form).**

$$\forall (N : \mathbb{N}), (\operatorname{spForm}\left(N\right)).Nondegenerate$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.sp_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vector that pairs to zero with every binary vector is the zero vector.

**Definition 1.5 (The binary graph amplitude).**

$$\forall (N : \mathbb{N}), \forall (\Gamma : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))), \operatorname{graphAmp}\left(\Gamma, x\right) = (-1 : \mathbb{C})^{(\operatorname{normalExponent}\left(\Gamma, (x : (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))\right)).val}$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.graphAmp` (`✓ std3`).

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Each edge contributes its binary quadratic monomial. The ordered upper-triangular sum is normalExponent; graphAmp is the complexSign value of that exponent, equivalently −1 raised to its natural representative. This definition accepts every binary matrix, without a symmetry or diagonal hypothesis.

**Lemma 1.6 (Adjoints of tensor products).**

$$\forall (N : \mathbb{N}), \forall (A : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), Matrix.\operatorname{conjTranspose}\left(D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(A\right)\right) = D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(\lambda (i : \operatorname{Fin}\left(N\right)) \mapsto Matrix.\operatorname{conjTranspose}\left(A(i)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate transpose of a tensor product is the tensor product of the conjugate transposes of its factors.

**Lemma 1.7 (Tensor products of unitary factors).**

$$\forall (N : \mathbb{N}), \forall (A : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), (\forall (i : \operatorname{Fin}\left(N\right)), A(i) \in Matrix.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \Rightarrow (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(A\right) \in Matrix.\operatorname{unitaryGroup}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every single-qubit factor is unitary, their tensor product is unitary on the full binary register.

**Lemma 1.8 (Scalars in tensor products).**

$$\forall (N : \mathbb{N}), \forall (r : (\operatorname{Fin}\left(N\right) \to \mathbb{C})), \forall (A : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(\lambda (i : \operatorname{Fin}\left(N\right)) \mapsto SMul.\operatorname{smul}\left(r(i), A(i)\right)\right) = SMul.\operatorname{smul}\left(\prod_{i \in \operatorname{Fin}\left(N\right)} r(i), D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scaling each single-qubit factor scales the tensor product by the product of those scalars.

**Lemma 1.9 (The tensor action of binary Weyl factors).**

$$\forall (N : \mathbb{N}), \forall (v : ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))), \forall (f : ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \to \mathbb{C})), Matrix.\operatorname{mulVec}\left(D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.\operatorname{tensorOp}\left(\lambda (i : \operatorname{Fin}\left(N\right)) \mapsto Matrix.\operatorname{of}\left(\lambda (t : \operatorname{Fin}\left(2\right)) \mapsto \lambda (s : \operatorname{Fin}\left(2\right)) \mapsto (if \operatorname{id}\left((s : \operatorname{ZMod}\left(2\right))\right) = \operatorname{id}\left((t : \operatorname{ZMod}\left(2\right))\right) + (v).fst(i) then \operatorname{complexSign}\left((v).snd(i) \cdot \operatorname{id}\left((s : \operatorname{ZMod}\left(2\right))\right)\right) else 0)\right)\right), f\right) = \lambda (t : (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right))) \mapsto \operatorname{complexSign}\left(\sum_{i: \operatorname{Fin}\left(N\right)} ((v).snd(i) \cdot (t(i) + (v).fst(i)))\right) \cdot f(t + (v).fst)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each single-qubit matrix translates the binary coordinate by v.fst(i) and multiplies it by the sign of v.snd(i) times the input coordinate. The displayed matrix entries and translated function write out both sides of the tensor action. Fin 2 and ZMod 2 have the same binary representatives; id leaves these representatives unchanged.

**Definition 1.10 (Binary choices of Hadamard and phase gates).**

$$\forall (h : Bool), \forall (d : \operatorname{ZMod}\left(2\right)), \operatorname{gate}\left(h, d\right) = (if d = 0 then 1 else Matrix.\operatorname{diagonal}\left(![1, Complex.\operatorname{I}\left(\right)]\right)) * (if h then BinaryStabilizerLocalInequivalence.\operatorname{hadamard}\left(\right) else 1)$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.gate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary phase choice multiplies the optional Hadamard gate on the left. Zero phase selects the identity and nonzero phase selects the diagonal matrix with entries 1 and i.

**Lemma 1.11 (Unitarity of the binary gate family).**

$$\forall (h : Bool), \forall (d : \operatorname{ZMod}\left(2\right)), \operatorname{gate}\left(h, d\right) \in Matrix.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.gate_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every combination of the binary phase choice and the Hadamard choice is a unitary single-qubit matrix.

**Theorem 1.12 (A graph amplitude for every stabilizer line).**

$$\forall (N : \mathbb{N}), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{StabilizedBy}\left(pauliSet, \psi\right) \Rightarrow (\exists (U : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), \exists (\Gamma : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \exists (c : \mathbb{C}), (\forall (i : \operatorname{Fin}\left(N\right)), \operatorname{U}\left(i\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((\Gamma).IsSymm \land ((\forall (i : \operatorname{Fin}\left(N\right)), \Gamma(i, i) = 0) \land (\psi = SMul.\operatorname{smul}\left(c, (\operatorname{tensorOp}\left(U\right) *_{v} \operatorname{graphAmp}\left(\Gamma\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.stabilizer_graph_normal_form` (`✓ std3`). ∎

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

The Pauli stabilizers of a nonzero common eigenline span a binary Lagrangian subspace. Coordinate swaps and a diagonal shear express that subspace as the graph of a symmetric matrix with zero diagonal. Hadamard and phase gates implement these transformations, and Pauli signs identify the remaining line with the quadratic amplitude. Taking the inverse gates gives the unitaries U and the scalar c in the displayed equation; SMul.smul denotes scalar action on the amplitude vector.

## References

- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.complex_sign_val`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.gate`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.gate_unitary`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.graphAmp`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.spForm`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.sp_alt`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.sp_nondegenerate`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.stabilizer_graph_normal_form`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_adj`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_smul`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_unitary`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.tensor_weyl`
- Dependency: [D5/S3/Quantum/Information/BinaryLagrangianGraphForm](BinaryLagrangianGraphForm.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../../VertexAlgebra/LatticeTwistedGroundRealization.md)
