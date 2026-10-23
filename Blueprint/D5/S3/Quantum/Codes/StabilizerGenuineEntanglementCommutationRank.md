# Genuine entanglement and commutation rank

## Abstract

Genuine entanglement forces a lower bound on the dimension of the Pauli commutation space over a prime field.

**Definition 1.1 (Pauli word coordinates).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\operatorname{structure} \operatorname{PauliWord}\left(N, p\right): \operatorname{Type} \operatorname{where} \{(\operatorname{phase}: \operatorname{ZMod}\left(p\right)), (x: (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right))), (z: (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)))\}))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.PauliWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

A PauliWord has a phase residue and two functions x and z assigning residues to the N parties. This is a record of coordinates, with no multiplication imposed on the record itself. The parameters N and p are arbitrary natural numbers.

**Definition 1.2 (The matrix of a Pauli word).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), ([\operatorname{NeZero}\left(p\right)] (\forall (w: \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{pauliWordOperator}\left(w\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right)) = (\operatorname{windowRoot}\left(p\right)^{w.phase.val}) \cdot (\operatorname{Matrix.of}\left(((u: \operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \mapsto (((v: \operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \mapsto (\prod_{n: \operatorname{Fin}\left(N\right)} (\operatorname{displacement}\left(p, w.x\left(n\right), w.z\left(n\right), u\left(n\right), v\left(n\right)\right))))))\right))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.pauliWordOperator` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

For nonzero p, the matrix is the phase windowRoot(p) raised to the natural representative w.phase.val, multiplying the tensor product of the local displacements X to the power w.x(n) followed by Z to the power w.z(n). The product gives its entries in the basis indexed by functions from Fin N to ZMod p. The dot denotes complex scalar multiplication of a matrix. See final_5.tex, lines 190–196 and 215–216.

**Definition 1.3 (Local commutation phases).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (a: \operatorname{PauliWord}\left(N, p\right)), (\forall (b: \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{commutationVector}\left(a, b\right): (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right))) = ((n: \operatorname{Fin}\left(N\right)) \mapsto (((a.z\left(n\right)) \cdot (b.x\left(n\right))) - ((a.x\left(n\right)) \cdot (b.z\left(n\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.commutationVector` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

At party n the commutation exponent is a.z(n)b.x(n) minus a.x(n)b.z(n), computed in ZMod p. Thus the global phases of a and b do not affect this vector. This is the coordinate form of the local commutation exponents in final_5.tex, lines 375–382.

**Theorem 1.4 (Multiplication of coordinate-product matrices).**

$$\forall (I: \operatorname{Type}), (\forall (T: \operatorname{Type}), ([\operatorname{Fintype}\left(I\right)] ([\operatorname{DecidableEq}\left(I\right)] ([\operatorname{Fintype}\left(T\right)] (\forall (M: I \to \operatorname{Matrix}\left(T, T, \mathbb{C}\right)), (\forall (L: I \to \operatorname{Matrix}\left(T, T, \mathbb{C}\right)), ((\operatorname{Matrix.of}\left(((u: I \to T) \mapsto (((v: I \to T) \mapsto (\prod_{n: I} (M\left(n\right)\left(u\left(n\right), v\left(n\right)\right))))))\right)) \cdot (\operatorname{Matrix.of}\left(((u: I \to T) \mapsto (((v: I \to T) \mapsto (\prod_{n: I} (L\left(n\right)\left(u\left(n\right), v\left(n\right)\right))))))\right)) = \operatorname{Matrix.of}\left(((u: I \to T) \mapsto (((v: I \to T) \mapsto (\prod_{n: I} (((n: I) \mapsto ((M\left(n\right)) \cdot (L\left(n\right))))\left(n\right)\left(u\left(n\right), v\left(n\right)\right))))))\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.coordinate_product_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

For finite coordinate and local index types, multiplying two matrices whose entries are products of local entries gives the coordinate product of the local matrix products. The sum over intermediate configurations factors into independent sums over each local index.

**Theorem 1.5 (The coordinate product of identity matrices).**

$$\forall (I: \operatorname{Type}), (\forall (T: \operatorname{Type}), ([\operatorname{Fintype}\left(I\right)] ([\operatorname{DecidableEq}\left(T\right)] (\operatorname{Matrix.of}\left(((u: I \to T) \mapsto (((v: I \to T) \mapsto (\prod_{n: I} ((1: \operatorname{Matrix}\left(T, T, \mathbb{C}\right))\left(u\left(n\right), v\left(n\right)\right))))))\right) = (1: \operatorname{Matrix}\left((I \to T), (I \to T), \mathbb{C}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.coordinate_product_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

For finitely many coordinates and any local index type with decidable equality, the coordinate product of identity matrices is the identity on configurations. Each entry is one exactly when the two configurations agree at every coordinate. The local index type need not be finite.

**Definition 1.6 (The common fixed subspace).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ([\operatorname{NeZero}\left(p\right)] (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{stabilizerSubspace}\left(G\right): \operatorname{Submodule}\left(\mathbb{C}, ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C})\right)) = \operatorname{iInf}\left(((i: \operatorname{Fin}\left(k\right)) \mapsto (\operatorname{LinearMap.fixedSubmodule}\left((\operatorname{pauliWordOperator}\left(G\left(i\right)\right)).mulVecLin\right)))\right))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.stabilizerSubspace` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

Intersect the fixed submodules of the matrix actions of all generators. A vector belongs precisely when every generator fixes it; the same then holds for every finite product of generators. The intersection iInf is indexed by i in Fin k. See final_5.tex, lines 224–230.

**Definition 1.7 (Factorization across a bipartition).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (Q: \operatorname{Set}\left(\operatorname{Fin}\left(N\right)\right)), (\forall (\psi: (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C}), (\operatorname{productAcross}\left(Q, \psi\right) = (\exists (u: (\operatorname{CoeSort.coe}\left(Q\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C}), (\exists (v: (\operatorname{CoeSort.coe}\left(Q^{c}\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C}), (\forall (x: \operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), (\psi\left(x\right) = (u\left(((q: \operatorname{CoeSort.coe}\left(Q\right)) \mapsto (x\left((\operatorname{Subtype.val}\left(q\right): \operatorname{Fin}\left(N\right))\right)))\right)) \cdot (v\left(((q: \operatorname{CoeSort.coe}\left(Q^{c}\right)) \mapsto (x\left((\operatorname{Subtype.val}\left(q\right): \operatorname{Fin}\left(N\right))\right)))\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.productAcross` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

A vector factors across Q when its amplitude at every configuration x is the product of one amplitude u depending only on the Q coordinates and one amplitude v depending only on the complementary coordinates. CoeSort.coe makes the subtype belonging to a set explicit, and Subtype.val(q) is its inclusion into Fin N. No nonzero or normalization condition is imposed here. See final_5.tex, lines 122–129.

**Definition 1.8 (Entanglement of every nonzero fixed vector).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ([\operatorname{NeZero}\left(p\right)] (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), (\operatorname{genuinelyEntangled}\left(G\right) = (\forall (\psi: (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C}), ((\psi \in \operatorname{stabilizerSubspace}\left(G\right)) \Rightarrow ((\psi \ne (0: (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)) \to \mathbb{C})) \Rightarrow (\forall (Q: \operatorname{Set}\left(\operatorname{Fin}\left(N\right)\right)), ((Q.Nonempty) \Rightarrow (((Q^{c}).Nonempty) \Rightarrow (\neg (\operatorname{productAcross}\left(Q, \psi\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.genuinelyEntangled` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

Every nonzero vector of the common fixed subspace must fail to factor across every bipartition whose two sides are nonempty. This condition itself does not assert that the fixed subspace contains a nonzero vector. See final_5.tex, lines 120–136 and 141.

**Definition 1.9 (The span of the commutation vectors).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Nat.Prime}\left(p\right)\right)] (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{commutationSpace}\left(G\right): \operatorname{Submodule}\left(\operatorname{ZMod}\left(p\right), (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right))\right)) = \operatorname{Submodule.span}\left(\operatorname{ZMod}\left(p\right), \operatorname{Set.range}\left(((ij: \operatorname{Fin}\left(k\right) \times \operatorname{Fin}\left(k\right)) \mapsto (\operatorname{commutationVector}\left(G\left(ij.1\right), G\left(ij.2\right)\right)))\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.commutationSpace` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

For prime p, take the ZMod p linear span of the commutation vectors of all ordered pairs of generators. The pair ij runs through Fin k times Fin k. This is the space K of final_5.tex, lines 375–391.

**Definition 1.10 (Finite products of the generator matrices).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ([\operatorname{NeZero}\left(p\right)] (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{generatedOperators}\left(G\right): \operatorname{Submonoid}\left(\operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right)\right)) = \operatorname{Submonoid.closure}\left(\operatorname{Set.range}\left(((i: \operatorname{Fin}\left(k\right)) \mapsto (\operatorname{pauliWordOperator}\left(G\left(i\right)\right)))\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.generatedOperators` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

The generated submonoid is the smallest multiplicatively closed collection containing the identity and all generator matrices. Its elements are finite products of those matrices. This formulation does not require a group structure on PauliWord.

**Definition 1.11 (Commutativity and exclusion of nonidentity scalars).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ([\operatorname{NeZero}\left(p\right)] (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), (\operatorname{IsStabilizer}\left(G\right) = ((\forall (i: \operatorname{Fin}\left(k\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\operatorname{Commute}\left(\operatorname{pauliWordOperator}\left(G\left(i\right)\right), \operatorname{pauliWordOperator}\left(G\left(j\right)\right)\right)))) \land (\forall (A: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right)), ((A \in \operatorname{generatedOperators}\left(G\right)) \Rightarrow (\forall (c: \mathbb{C}), ((A = \operatorname{Matrix.scalar}\left((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(p\right)), c\right)) \Rightarrow (c = (1: \mathbb{C}))))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.IsStabilizer` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

The generator matrices commute pairwise, and every scalar matrix in their generated submonoid has scalar equal to one. The identity is already in that submonoid. For nonzero p the Pauli matrices form a finite collection of invertible matrices, so the generated submonoid is a group. These are the two stabilizer conditions of final_5.tex, lines 218–223.

**Definition 1.12 (The commutation-rank bound).**

$$\operatorname{claim} = (\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ((1 \le N) \Rightarrow (\forall (hp: \operatorname{Nat.Prime}\left(p\right)), (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{IsStabilizer}\left(G\right)) \Rightarrow ((\operatorname{genuinelyEntangled}\left(G\right)) \Rightarrow (\operatorname{Nat.div}\left((((N) - (1)) + ((p) - (2))), ((p) - (1))\right) \le \operatorname{Module.finrank}\left(\operatorname{ZMod}\left(p\right), \operatorname{CoeSort.coe}\left(\operatorname{commutationSpace}\left(N, p, k, \langle hp \rangle, G\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.claim` (`✓ std3`).

*Citation.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

For every positive number N of parties, every prime p and every family G of k Pauli words generating a stabilizer, genuine entanglement implies the displayed rank bound. This is Conjecture 1 in final_5.tex, lines 457–463. Subtraction and Nat.div are natural-number operations: because p is prime, the quotient is exactly the ceiling of (N minus one) divided by (p minus one). The proof hp supplies the nonzero modulus and the instance ⟨hp⟩ in the explicitly applied commutationSpace. CoeSort.coe displays the submodule as its type of elements; its finrank is a natural number.

**Theorem 1.13 (Genuine entanglement forces the rank bound).**

$$\forall (N: \mathbb{N}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), ((1 \le N) \Rightarrow (\forall (hp: \operatorname{Nat.Prime}\left(p\right)), (\forall (G: \operatorname{Fin}\left(k\right) \to \operatorname{PauliWord}\left(N, p\right)), ((\operatorname{IsStabilizer}\left(G\right)) \Rightarrow ((\operatorname{genuinelyEntangled}\left(G\right)) \Rightarrow (\operatorname{Nat.div}\left((((N) - (1)) + ((p) - (2))), ((p) - (1))\right) \le \operatorname{Module.finrank}\left(\operatorname{ZMod}\left(p\right), \operatorname{CoeSort.coe}\left(\operatorname{commutationSpace}\left(N, p, k, \langle hp \rangle, G\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.result` (`✓ std3`). ∎

*Resolves.* `Problems/makuta-kuzaka-augusiak-2023-stabilizer-commutation-rank` (proved) by `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"makuta-kuzaka-augusiak-2023-stabilizer-commutation-rank","declaration_gid":"D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak (2023). *Fully non-positive-partial-transpose genuinely entangled subspaces*. DOI: [10.22331/q-2023-02-09-915](https://doi.org/10.22331/q-2023-02-09-915). URL: <https://arxiv.org/abs/2203.16902v2>.

*Commentary.*

Products of tensor-product matrices are computed coordinate by coordinate, and multiplication of the root-of-unity phases follows addition in ZMod p. A word with zero x and z is a scalar matrix. Multiplying two words again gives a word: add x and z, and add both phases and the sum of a.z(n)b.x(n). There are finitely many words when p is nonzero, and every word matrix is invertible, since the shift and clock matrices and the scalar phase are invertible.

A commuting family of complex endomorphisms on a nonzero finite-dimensional space has a common eigenvector: its Lie span is abelian, and a nontrivial weight space supplies the vector. Now consider matrices c(i) times A(i) tensor B(i), with the B(i) commuting, and let W be their common fixed subspace. The actions of identity tensor B(i) preserve W and commute there. A nonzero W therefore contains a common eigenvector w with eigenvalues χ(i). Choose a nonzero coordinate w(xy), and take a(x) = w(x,xy.2) and b(y) = w(xy.1,y). The eigenvector equations give B(i)b = χ(i)b, and the fixed-vector equations give (c(i)χ(i))A(i)a = a. Hence a tensor b is fixed by every c(i)A(i) tensor B(i), and its coordinate at xy is w(xy) squared, so it is nonzero.

The local displacement identity gives the commutation phase a.z(n)b.x(n) minus a.x(n)b.z(n). Multiplying over the parties shows that the global commutation phase is the root of unity raised to the representative of the sum of these coordinates. A word with some nonzero x or z coordinate has trace zero: its trace is its scalar phase times the product of the local displacement traces, and the corresponding local trace vanishes.

Let S be a finite set of words and T its generated matrix submonoid, excluding nonidentity scalar matrices. The word matrices form a finite submonoid containing T, so T is finite. Every element of T other than the identity has trace zero: if all its x and z coordinates vanished it would be scalar and therefore the identity. Thus M, the sum of all matrices in T, has trace equal to Fintype.card(Fin N → ZMod p) cast from ℕ to ℂ. This cast is nonzero, so M is nonzero and Mv is nonzero for some vector v. Left multiplication by any generator is injective on the finite set T, since the generator is invertible; it therefore permutes T. Consequently every generator fixes Mv.

Suppose the sums of the commutation coordinates over a set Q vanish for every pair in S, and take a nonzero common fixed vector ψ. Applying the global commutation identity to ψ forces the total phase sum to be zero, by primitivity of windowRoot(p). The complementary sum is therefore zero too. Split configurations into their restrictions to Q and its complement using the corresponding equivalence of function spaces. Each word matrix becomes c(i)A(i) tensor B(i), and the complementary matrices B(i) commute by the vanishing complementary phase sums. Transport ψ through this equivalence and apply the preceding product-vector construction. Transporting back gives a nonzero common fixed vector factoring across Q.

For a family u of r vectors with m coordinates over ZMod p, assume r(p minus one) is less than m. Define f(i) as the sum over j of u(i,j) times X(j) to the power (p minus one). The sum of their total degrees is at most r(p minus one), hence is less than m. Chevalley–Warning makes the number of common zeros divisible by p. Zero is one common zero, so it cannot be the only one. Choose a nonzero common zero x. Fermat's identity makes x(j) to the power p minus one equal to one on its nonempty support Q and zero elsewhere. Therefore the sum of u(i,j) over Q is zero for every i.

Apply this fact to the first n coordinates of a basis b of a submodule K in ZMod p to the power n plus one. If n exceeds finrank(K)(p minus one), it produces a nonempty Q in Fin n whose coordinate-sum linear map L vanishes on every basis vector. Thus L is zero on K. Consequently, whenever every nonempty Q has some vector of K with nonzero coordinate sum, n is at most finrank(K)(p minus one).

For the generators G on n plus one parties, put S equal to their finite image. Its generated submonoid lies in generatedOperators(G), so scalar exclusion gives the nonzero common fixed vector just constructed. If a nonempty Q in Fin n had zero coordinate sum for every vector of commutationSpace(G), the generator-pair commutation vectors would have zero sum there. Embed Q into Fin(n plus one) by castSucc and call its image R. The set R is nonempty and its complement contains the last party. The product-vector construction then gives a nonzero vector in stabilizerSubspace(G) factoring across R, contrary to genuine entanglement. Thus every such Q has a vector with nonzero sum, and the rank estimate applies to commutationSpace(G).

Finally, write the positive N as n plus one and use p minus one greater than zero. The inequality n ≤ (p minus one)finrank(commutationSpace(G)), after adding p minus two on both sides, gives the displayed bound by the natural-number division criterion. This includes N equal to one.

## References

- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.IsStabilizer`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.PauliWord`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.claim`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.commutationSpace`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.commutationVector`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.coordinate_product_mul`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.coordinate_product_one`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.generatedOperators`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.genuinelyEntangled`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.pauliWordOperator`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.productAcross`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.result`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.stabilizerSubspace`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTrace](../Algebra/WeylDisplacementTrace.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylPhaseArithmetic](../Algebra/WeylPhaseArithmetic.md)
