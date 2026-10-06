# Binary Lagrangian subspaces in graph form

## Abstract

After exchanging the two coordinates at a set of positions and a diagonal shear, every Lagrangian subspace of a binary symplectic space is the graph of a symmetric matrix with zero diagonal.

**Definition 1.1 (The binary symplectic form).**

$$\forall N: \mathbb{N}, \forall u v: ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z})), \operatorname{sp}\left(u, v\right) = \sum_{i} (\operatorname{fst}\left(u\right)(i) \cdot \operatorname{snd}\left(v\right)(i) + \operatorname{snd}\left(u\right)(i) \cdot \operatorname{fst}\left(v\right)(i))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.sp` (`✓ std3`).

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Write V(N) for the functions Fin N → ℤ/2ℤ and E(N) = V(N) × V(N). The form pairs the first coordinate of one vector with the second of the other at every position.

**Definition 1.2 (Exchanging coordinates on a set of positions).**

$$\forall N: \mathbb{N}, \forall H: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), \forall v: ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z})), \operatorname{swapAt}\left(H, v\right) = (\lambda i \mapsto \operatorname{ite}\left(i \in H, \operatorname{snd}\left(v\right)(i), \operatorname{fst}\left(v\right)(i)\right), \lambda i \mapsto \operatorname{ite}\left(i \in H, \operatorname{fst}\left(v\right)(i), \operatorname{snd}\left(v\right)(i)\right))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.swapAt` (`✓ std3`).

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

At the positions in H the two coordinates are exchanged and elsewhere they are kept; on a stabilizer symbol this is the action of a Hadamard gate on those qubits.

**Theorem 1.3 (Every Lagrangian subspace is a graph after a swap and a shear).**

$$\forall N: \mathbb{N}, \forall L: \operatorname{Submodule}\left(\mathbb{Z}/2\mathbb{Z}, ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}))\right), (\forall u v: ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z})), u \in L \land v \in L \Rightarrow \operatorname{sp}\left(u, v\right) = 0) \Rightarrow \operatorname{finrank}\left(\mathbb{Z}/2\mathbb{Z}, L\right) = N \Rightarrow \exists H: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), \exists d: (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}), \exists \Gamma: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{Z}/2\mathbb{Z}\right), \operatorname{IsSymm}\left(\Gamma\right) \land (\forall i: \operatorname{Fin}\left(N\right), \Gamma(i, i) = 0) \land (\forall v: ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z})), v \in L \Leftrightarrow (\operatorname{snd}\left(\operatorname{swapAt}\left(H, v\right)\right) + (\lambda i \mapsto d(i) \cdot \operatorname{fst}\left(\operatorname{swapAt}\left(H, v\right)\right)(i)) = \operatorname{mulVec}\left(\Gamma, \operatorname{fst}\left(\operatorname{swapAt}\left(H, v\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.lagrangian_graph_form` (`✓ std3`). ∎

*Citation.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Let L be isotropic for the form and of dimension N. Choose a set H maximizing the rank of the first projection of the swapped subspace. If that rank were below N, a vector of L with zero first projection and a nonzero second coordinate at some position i would exist; isotropy keeps the unit vector at i out of the old first projection, so erasing the coordinate i is injective there, and exchanging the coordinates at i adds that unit vector to the new first projection, so the rank strictly increases, against maximality. Hence the first projection is bijective and the swapped subspace is the graph of a linear map A, symmetric by isotropy on the preimages of the unit vectors. With d the diagonal of A and Γ = A minus its diagonal, a vector lies in L exactly when its swapped second coordinate, plus d times the swapped first coordinate, equals Γ applied to the swapped first coordinate; on symbols the shear is the action of phase gates. This is the binary form of Theorem 1 of Van den Nest, Dehaene and De Moor (Phys. Rev. A 69, 022316), which constructs the Hadamard set from a rank decomposition of the generator matrix; the proof here chooses it by maximizing the rank instead.

## References

- Truth anchor: `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.lagrangian_graph_form`
- Truth anchor: `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.sp`
- Truth anchor: `D5/S3/Quantum/Information/BinaryLagrangianGraphForm.swapAt`
