# Commuting encodings and local reflections

## Abstract

Commuting product unitaries and commuting local reflections encode exactly the same qubit states.

**Definition 1.1 (A commuting product encoding).**

$$\forall (n: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), (\forall (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingProductEncoding}\left(\psi, U\right) = ((\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (U\left(a, j\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)))) \land ((\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (b: \operatorname{Fin}\left(2^{n}\right)), ((\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(a\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(b\right)\right)) = (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(b\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(a\right)\right))))) \land (\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (b: \operatorname{Fin}\left(2^{n}\right)), (\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))} ((\operatorname{star}\left(\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(a\right)\right), \psi\right)\left(x\right)\right)) \cdot (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(b\right)\right), \psi\right)\left(x\right))) = \operatorname{ite}\left(a = b, (1: \mathbb{C}), (0: \mathbb{C})\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.IsCommutingProductEncoding` (`✓ std3`).

*Citation.* Jef Pauwels; Otfried Gühne (2026). *The Entanglement Content of Quantum Measurement Bases*. URL: <https://arxiv.org/abs/2608.21185v1>.

*Commentary.*

For n qubits, U has exactly 2ⁿ labels and one unitary two-by-two factor at each site. The complete tensor operators commute pairwise, and their images of ψ are orthonormal. Thus they form a basis of the 2ⁿ-dimensional state space. The local factors themselves are not required to commute. This combines the local-encoding definition in main.tex, lines 328–340, with the commuting families discussed in lines 374–384. The predicate imposes no separate normalization hypothesis on ψ.

**Definition 1.2 (A commuting reflection encoding).**

$$\forall (n: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), (\forall (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingReflectionEncoding}\left(\psi, U\right) = ((\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingProductEncoding}\left(\psi, U\right)) \land (\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Matrix.IsHermitian}\left(U\left(a, j\right)\right)) \land ((U\left(a, j\right)) \cdot (U\left(a, j\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.IsCommutingReflectionEncoding` (`✓ std3`).

*Citation.* Jef Pauwels; Otfried Gühne (2026). *The Entanglement Content of Quantum Measurement Bases*. URL: <https://arxiv.org/abs/2608.21185v1>.

*Commentary.*

A commuting reflection encoding is a commuting product encoding whose every local factor is Hermitian and squares to the identity matrix. This is the commuting-reflection case of the encoder-structures definition in main.tex, lines 357–368. The tensor operators commute even when some of their factors anticommute.

**Definition 1.3 (Equality of the two encoding classes).**

$$\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.claim} = (\forall (n: \mathbb{N}), ((1 \le n) \Rightarrow (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))} (\left\lVert \psi\left(x\right) \right\rVert^{2}) = (1: \mathbb{R})) \Rightarrow ((\exists (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingProductEncoding}\left(\psi, U\right))) \Leftrightarrow (\exists (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingReflectionEncoding}\left(\psi, U\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.claim` (`✓ std3`).

*Citation.* Jef Pauwels; Otfried Gühne (2026). *The Entanglement Content of Quantum Measurement Bases*. URL: <https://arxiv.org/abs/2608.21185v1>.

*Commentary.*

For every positive natural number n and every normalized n-qubit vector ψ, existence of a commuting product encoding is equivalent to existence of a commuting reflection encoding. Section VI, main.tex lines 1539–1546, asks for the state class defined by commuting encoders with non-Hermitian local factors. The displayed assertion specifies equality with the reflection class. The source characterizes the reflection class in lines 542–560.

**Theorem 1.4 (Reflection replacements for commuting product encodings).**

$$\forall (n: \mathbb{N}), ((1 \le n) \Rightarrow (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))} (\left\lVert \psi\left(x\right) \right\rVert^{2}) = (1: \mathbb{R})) \Rightarrow ((\exists (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingProductEncoding}\left(\psi, U\right))) \Leftrightarrow (\exists (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), (\operatorname{D5.S3.Quantum.Information.CommutingEncodingReflectionClass.IsCommutingReflectionEncoding}\left(\psi, U\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.result` (`✓ std3`). ∎

*Resolves.* `Problems/pauwels-guhne-2026-commuting-encoding-reflection-class` (proved) by `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pauwels-guhne-2026-commuting-encoding-reflection-class","declaration_gid":"D5/S3/Quantum/Information/CommutingEncodingReflectionClass.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jef Pauwels; Otfried Gühne (2026). *The Entanglement Content of Quantum Measurement Bases*. URL: <https://arxiv.org/abs/2608.21185v1>.

*Commentary.*

Fix n ≥ 1, ψ and a commuting product encoding U. For two labels a and b, the tensor products of the local products U(a,j)U(b,j) and U(b,j)U(a,j) are equal and nonzero. Choose a nonzero entry of this tensor matrix and vary only its row and column coordinates at site j. Cancelling the product of the other entries shows that the two local products are proportional. Their nonzero two-by-two determinants give c² = 1 for the proportionality scalar. Consequently each pair of local factors either commutes or anticommutes.

At each site choose a unitary V(j) as follows. If a nonscalar factor has nonzero trace, anticommutation with an invertible factor would negate its trace under conjugation, which is impossible. All factors therefore commute with it. Its two eigenvalues are distinct, so its unitary eigenbasis makes every factor diagonal. Otherwise each nonscalar factor is traceless. Its two unit-modulus eigenvalues are opposites, so it is a unit-modulus scalar times a Hermitian involution; scalar factors have the same form with the identity involution. Cancelling these phases preserves all commutation signs. Send a nonscalar involution to ±Z. If all involutions commute with Z, they also commute or anticommute with X. Otherwise a diagonal unitary fixing Z sends an anticommuting involution to X, and the signs with this pair determine all remaining factors. The four possibilities are scalar multiples of I, X, Y and Z. If all factors are scalar, the identity change of basis suffices.

Put A(a,j) = V(j)U(a,j)V(j)ᴴ. Expand each tensor operator in Pauli words using its trace coefficients. Represent a Pauli letter by its two binary translation and phase coordinates, and let S be the binary linear span of the symbols of every word with a nonzero coefficient in any such expansion. At a diagonal site only I and Z can have nonzero trace coefficients. At a Pauli site only the letter proportional to A(a,j) can occur. Hence for any two words occurring in the expansions, their local Pauli commutation signs are exactly the signs of the corresponding local A factors. The complete A operators commute and their products are nonzero, so the product of these signs is one. Their binary symplectic pairing is therefore zero. Bilinearity makes S isotropic, and every tensor operator lies in the complex span of the Pauli words with symbol in S.

Extend S to an inclusion-maximal isotropic subspace L in the finite binary symplectic space. A vector orthogonal to L could be adjoined while retaining isotropy, since the form is alternating. Maximality therefore gives L = L⊥. Nondegeneracy and the ambient dimension 2n imply dim L = n. Choose a basis of L and Pauli-word representatives of its basis vectors. These representatives are commuting involutions. Their products, indexed by binary strings a, define matrices H(a) with H(a+b) = H(a)H(b). Each H(a) is a unit-modulus phase times a Pauli word, and its symbol is the basis-coordinate image of a. Thus H(0) is the identity and every other H(a) has trace zero. Unitarity and H(a)² = I make H(a) Hermitian. Conversely every Pauli word whose symbol lies in L is a nonzero scalar multiple of one H(a).

A Hermitian phase multiple of a nonzero Hermitian Pauli word has real phase, hence phase ±1. Absorb this sign into site zero, which exists because n ≥ 1. This expresses each H(a) as a tensor product of local Hermitian involutions R(a,j), with no change to its multiplication or trace identities.

For binary strings a and x, let χ(a,x) = ∏ⱼ(−1)^((a(j)).val (x(j)).val) in the complex numbers. Form P(x) = ∑ₐ χ(a,x)H(a). Translation of the summation index gives H(a)P(x) = χ(a,x)P(x). The trace identities give tr P(x) = 2ⁿ, so P(x) has a nonzero column. Choose such a column v(x) and normalize it by multiplying by the inverse of the complex inclusion of its real norm. Distinct x and y differ at a site j; the Hermitian operator H(eⱼ) then has opposite eigenvalues on the two normalized columns, making them orthogonal. These columns form a unitary matrix F satisfying FᴴH(a)F = diagonal(χ(a,·)). Since every Pauli word with symbol in L lies in the span of the H(a), conjugation by F diagonalizes all of them and therefore all tensor operators formed from A. Write their diagonals as eig(a,x). Unitarity gives star(eig(a,x))eig(a,x) = 1.

Conjugating the original encoding by the tensor product of V(j) preserves unitarity, commutation and inner products. Write its state in the F basis as c = Fᴴ(tensorOp(V)ψ). Identify the 2ⁿ labels with binary strings and form the square matrix M(x,a) = c(x)eig(a,x). The encoding's orthonormality gives MᴴM = I, hence MMᴴ = I. Each diagonal row equation, together with the unit modulus of eig(a,x), gives (↑(Fintype.card (Fin n → Fin 2)) : ℂ) star(c(x))c(x) = 1. Here the cardinality is cast from the natural numbers to the complex numbers. Since that cardinality is 2ⁿ, every squared amplitude is 1/(2ⁿ : ℂ).

The operators tensorOp(R(a)) act on these flat amplitudes by the real signs χ(a,x). Their pairwise overlap is therefore the sum of χ(a,x)χ(b,x) divided by (2ⁿ : ℂ). A binary additive character sums to its domain's cardinality when trivial and to zero otherwise. This product character is trivial exactly when a = b, as evaluation on each coordinate string shows. Its sum is consequently (2ⁿ : ℂ) for equal labels and zero otherwise. The R operators therefore give an orthonormal orbit. Their diagonal forms commute, and each local Hermitian involution is unitary. Relabelling by Fin (2ⁿ) gives a commuting reflection encoding of tensorOp(V)ψ.

Finally conjugate its local factors by V(j)ᴴ. Unitary conjugation preserves Hermitian involutions and the encoding conditions, and the inverse tensor unitary returns the state to ψ. This proves the forward implication. For the reverse implication retain the same factors and discard the additional Hermitian and involution conditions. The forward construction already obtains normalization from the orthonormal orbit; it does not need the separate unit-vector hypothesis in the displayed statement.

## References

- Truth anchor: `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.IsCommutingProductEncoding`
- Truth anchor: `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.IsCommutingReflectionEncoding`
- Truth anchor: `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.claim`
- Truth anchor: `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.result`
- Dependency: [D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm](CommutingEncoding/LocalSiteNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
