# The tripartite maximal-class length bound fails

## Abstract

A tripartite state of dimensions (3, 3, 7) has coordinate length nine and all four kernel dimensions zero, contradicting the proposed lower bound eleven.

A tripartite state is a complex coefficient array in a fixed product basis. The contractions below are complex linear maps formed by multiplying coefficients without complex conjugation. Their kernel dimensions are the four algebraic entanglement invariants of Appendix A. The length counts nonzero coefficients in this basis; it depends on the basis. All dimensions and lengths are natural numbers, and subtraction is natural-number subtraction, truncated at zero.

**Definition 1.1 (Tripartite coefficient arrays).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right) = ((\operatorname{Fin}\left(d1\right) \times (\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d3\right))) \to \mathbb{C}))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.State` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The coordinates in the product basis are indexed by Fin d1, Fin d2 and Fin d3, with complex coefficients.

**Definition 1.2 (Contraction over the first factor).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (w: (\operatorname{Fin}\left(d1\right) \to \mathbb{C})), (\forall (j: \operatorname{Fin}\left(d2\right)), (\forall (k: \operatorname{Fin}\left(d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat1}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), (\operatorname{Fin}\left(d1\right) \to \mathbb{C}), ((\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d3\right)) \to \mathbb{C})\right))\left(w, (j, k)\right) = \sum_{(i: \operatorname{Fin}\left(d1\right))} ((v\left((i, j, k)\right)) \cdot (w\left(i\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat1` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A1) contracts the first index against a vector in the first factor. Its kernel is the space K1.

**Definition 1.3 (Contraction over the second factor).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (w: (\operatorname{Fin}\left(d2\right) \to \mathbb{C})), (\forall (i: \operatorname{Fin}\left(d1\right)), (\forall (k: \operatorname{Fin}\left(d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat2}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), (\operatorname{Fin}\left(d2\right) \to \mathbb{C}), ((\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(d3\right)) \to \mathbb{C})\right))\left(w, (i, k)\right) = \sum_{(j: \operatorname{Fin}\left(d2\right))} ((v\left((i, j, k)\right)) \cdot (w\left(j\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat2` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A2) contracts the second index against a vector in the second factor. Its kernel is the space K2.

**Definition 1.4 (Contraction over the third factor).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (w: (\operatorname{Fin}\left(d3\right) \to \mathbb{C})), (\forall (i: \operatorname{Fin}\left(d1\right)), (\forall (j: \operatorname{Fin}\left(d2\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat3}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), (\operatorname{Fin}\left(d3\right) \to \mathbb{C}), ((\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(d2\right)) \to \mathbb{C})\right))\left(w, (i, j)\right) = \sum_{(k: \operatorname{Fin}\left(d3\right))} ((v\left((i, j, k)\right)) \cdot (w\left(k\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat3` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A3) contracts the third index against a vector in the third factor. Its kernel is the space K3. The contracted vector coordinate is indexed by k, the summation index.

**Definition 1.5 (The first family of array contractions).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (z: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (a: \operatorname{Fin}\left(d1\right)), (\forall (b: \operatorname{Fin}\left(d1\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block1}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right), ((\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(d1\right)) \to \mathbb{C})\right))\left(z, (a, b)\right) = \sum_{(j: \operatorname{Fin}\left(d2\right))} (\sum_{(k: \operatorname{Fin}\left(d3\right))} ((v\left((a, j, k)\right)) \cdot (z\left((b, j, k)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block1` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A4) sums over the second and third indices, leaving two indices in the first factor.

**Definition 1.6 (The second family of array contractions).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (z: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (a: \operatorname{Fin}\left(d2\right)), (\forall (b: \operatorname{Fin}\left(d2\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block2}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right), ((\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d2\right)) \to \mathbb{C})\right))\left(z, (a, b)\right) = \sum_{(i: \operatorname{Fin}\left(d1\right))} (\sum_{(k: \operatorname{Fin}\left(d3\right))} ((v\left((i, a, k)\right)) \cdot (z\left((i, b, k)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block2` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A5) sums over the first and third indices, leaving two indices in the second factor.

**Definition 1.7 (The third family of array contractions).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (z: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), (\forall (a: \operatorname{Fin}\left(d3\right)), (\forall (b: \operatorname{Fin}\left(d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block3}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right), ((\operatorname{Fin}\left(d3\right) \times \operatorname{Fin}\left(d3\right)) \to \mathbb{C})\right))\left(z, (a, b)\right) = \sum_{(i: \operatorname{Fin}\left(d1\right))} (\sum_{(j: \operatorname{Fin}\left(d2\right))} ((v\left((i, j, a)\right)) \cdot (z\left((i, j, b)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block3` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Equation (A6) sums over the first and second indices, leaving two indices in the third factor.

**Definition 1.8 (The three contraction families together).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.joint}\left(v\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right), (((\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(d1\right)) \to \mathbb{C}) \times (((\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d2\right)) \to \mathbb{C}) \times ((\operatorname{Fin}\left(d3\right) \times \operatorname{Fin}\left(d3\right)) \to \mathbb{C})))\right)) = \operatorname{LinearMap.prod}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block1}\left(v\right), \operatorname{LinearMap.prod}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block2}\left(v\right), \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.block3}\left(v\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.joint` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

LinearMap.prod combines the three families, with the second and third grouped together. Its kernel consists of arrays satisfying all three families of equations and is the space K123 of Appendix A.

**Definition 1.9 (The first kernel dimension).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n1}\left(v\right): \mathbb{N}) = \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.ker}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat1}\left(v\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n1` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The invariant n1 is the complex dimension of K1 in Appendix A.

**Definition 1.10 (The second kernel dimension).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n2}\left(v\right): \mathbb{N}) = \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.ker}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat2}\left(v\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n2` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The invariant n2 is the complex dimension of K2 in Appendix A.

**Definition 1.11 (The third kernel dimension).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n3}\left(v\right): \mathbb{N}) = \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.ker}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.flat3}\left(v\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n3` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The invariant n3 is the complex dimension of K3 in Appendix A.

**Definition 1.12 (The joint kernel dimension).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n123}\left(v\right): \mathbb{N}) = \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.ker}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.joint}\left(v\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n123` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The invariant n123 is the complex dimension of K123 in Appendix A. This is the intersection of the kernels of the three array contractions.

**Definition 1.13 (The maximally entangled class).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.InMEC}\left(v\right)) \Leftrightarrow (\forall (w: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n1}\left(v\right) \le \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n1}\left(w\right)) \land ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n2}\left(v\right) \le \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n2}\left(w\right)) \land ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n3}\left(v\right) \le \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n3}\left(w\right)) \land (\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n123}\left(v\right) \le \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.n123}\left(w\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.InMEC` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

Definition II.1 requires each of the four invariants to attain its least value among all states of the same dimensions, simultaneously.

**Definition 1.14 (The nonzero coordinates).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.coordSupport}\left(v\right): \operatorname{Finset}\left((\operatorname{Fin}\left(d1\right) \times (\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d3\right)))\right)) = \operatorname{Finset.filter}\left(\lambda (p: (\operatorname{Fin}\left(d1\right) \times (\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d3\right)))) \mapsto (v\left(p\right) \ne 0), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(d1\right) \times (\operatorname{Fin}\left(d2\right) \times \operatorname{Fin}\left(d3\right)))\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.coordSupport` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The support selects exactly the product-basis indices whose coefficients are nonzero.

**Definition 1.15 (Coordinate length).**

$$\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.length}\left(v\right): \mathbb{N}) = \operatorname{Finset.card}\left(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.coordSupport}\left(v\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.length` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The length in Section III and equation (2) is the cardinality of the coordinate support.

**Definition 1.16 (The proposed tripartite length lower bound).**

$$(\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.claim}) \Leftrightarrow (\forall (d1: \mathbb{N}), (\forall (d2: \mathbb{N}), (\forall (d3: \mathbb{N}), ((3 \le d1) \Rightarrow ((3 \le d2) \Rightarrow ((3 \le d3) \Rightarrow (\forall (v: \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.State}\left(d1, d2, d3\right)), ((\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.InMEC}\left(v\right)) \Rightarrow ((((d1) + (d2)) + (d3)) - (2) \le \operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.length}\left(v\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.claim` (`✓ std3`).

*Citation.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

The clause of Conjecture III.4 with all three dimensions at least three asserts that the shortest length in the maximally entangled class is d1 + d2 + d3 - 2. Its lower-bound assertion requires every state in that class to have at least this length.

**Theorem 1.17 (A length-nine state in dimensions three, three and seven).**

$$\neg (\operatorname{D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/buniy-feger-kephart-2024-tripartite-mec-length-refutation` (refuted) by `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"buniy-feger-kephart-2024-tripartite-mec-length-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Roman V. Buniy, Robert P. Feger, Thomas W. Kephart (2024). *Decoherence and the classes of maximally entangled states*. DOI: [10.1142/S0219749924500357](https://doi.org/10.1142/S0219749924500357). URL: <https://arxiv.org/abs/2210.07618v1>.

*Commentary.*

At dimensions (3, 3, 7), take the state whose seven slices are the six off-diagonal 3 by 3 matrix units and the identity. In zero-based coordinates its coefficients are one at (0,1,0), (0,2,1), (1,0,2), (1,2,3), (2,0,4), (2,1,5), (0,0,6), (1,1,6) and (2,2,6), and zero elsewhere. Its length is nine.

The identity slice makes the first two flattenings injective, and the seven linearly independent slices make the third injective. For an array in the joint kernel, the third contraction family forces every slice to be diagonal with trace zero. The first two families force two diagonal entries of each of slices zero through five to vanish, and the trace equations force the third. The diagonal equations of the first family then force all diagonal entries of slice six to vanish. Thus the joint kernel also contains only zero.

All four invariants are zero, their least possible value, so this state belongs to the maximally entangled class. Its length nine is less than 3 + 3 + 7 - 2 = 11, refuting the stated lower bound.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.InMEC`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.State`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block1`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block2`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.block3`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.coordSupport`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat1`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat2`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.flat3`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.joint`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.length`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n1`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n123`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n2`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.n3`
- Truth anchor: `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result`
