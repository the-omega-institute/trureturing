# Paired partial permutations on rectangle partitions

## Abstract

A rectangle partition with matched sides gives a unitary with an exact tensor factor count.

Let X, Y and T be arbitrary finite types. Empty types and empty blocks are allowed. For each t in T choose finite subsets I(t) of X and J(t) of Y and a bijection φ(t): J(t) ≃ I(t). Assume every pair (x,y) belongs to exactly one rectangle I(t) × J(t). Here subsets in the bijection are subtype carriers. Equality on X and Y is decidable, as it can always be made for finite types.

Define A(t)(i,j) to be 1 if some y in J(t) satisfies y=j and φ(t)(y)=i, and 0 otherwise. Put U=∑t A(t)⊗A(t)ᴴ. Its rows are indexed by X×Y and its columns by Y×X: the first local factor maps Y to X, and the second maps X to Y. Define realignment by R(U)((i,j),(k,l))=U((i,k),(j,l)), with i,l in X and j,k in Y. Let Tplus={t in T: J(t) is nonempty}.

**Theorem 1.1 (Unitarity and exact achieved width).**

$$\forall X \in FiniteType,\; \forall Y \in FiniteType,\; \forall T \in FiniteType,\; \forall I \in T \to \operatorname{Finset}\left(X\right),\; \forall J \in T \to \operatorname{Finset}\left(Y\right),\; \forall phi \in \operatorname{BlockBijections}\left(I, J\right),\; \operatorname{UniqueRectangleCoverage}\left(I, J\right) \Rightarrow \left(\operatorname{conjTranspose}\left(U\right) \cdot U = 1 \land \left(U \cdot \operatorname{conjTranspose}\left(U\right) = 1 \land \left(\operatorname{rank}\left(\operatorname{R}\left(U\right)\right) = \operatorname{card}\left(Tplus\right) \land \left(U = \sum_{t:Tplus} \operatorname{kronecker}\left(A\left(\operatorname{val}\left(t\right)\right), \operatorname{conjTranspose}\left(A\left(\operatorname{val}\left(t\right)\right)\right)\right) \land \left(\left(\exists rows \in Tplus \to \operatorname{Prod}\left(X, Y\right),\; \exists cols \in Tplus \to \operatorname{Prod}\left(Y, X\right),\; \operatorname{submatrix}\left(\operatorname{R}\left(U\right), rows, cols\right) = 1\right) \land \left(\forall Q \in FiniteType,\; \forall M \in Q \to \operatorname{Matrix}\left(X, Y, Complex\right),\; \forall N \in Q \to \operatorname{Matrix}\left(Y, X, Complex\right),\; U = \sum_{q:Q} \operatorname{kronecker}\left(M\left(q\right), N\left(q\right)\right) \Rightarrow \operatorname{card}\left(Tplus\right) \le \operatorname{card}\left(Q\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition.unitary_exact_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such finite X,Y,T,I,J,φ and unique-coverage hypothesis, both Gram identities hold on the original carriers: UᴴU is the identity on Y×X and UUᴴ is the identity on X×Y. The rank of R(U) equals the cardinality of Tplus. Deleting empty blocks gives the displayed exact decomposition of U indexed by Tplus. There are actual row and column maps from Tplus whose submatrix of R(U) is the identity. Finally, for every finite type Q and arbitrary complex factors M(q): Matrix X Y and N(q): Matrix Y X, the equality U=∑q M(q)⊗N(q) implies |Tplus|≤|Q|. No independence or positivity of these factors is assumed.

The disjoint union of the rectangles is bijective to X×Y: coverage gives surjectivity and uniqueness gives injectivity. Given an input (j,l), its rectangle contains (l,j). Inside that rectangle route it to (φ(t)(j),φ(t)⁻¹(l)). Both entries stay in the same rectangle. The inverse sends (i,k) to (φ(t)⁻¹(i),φ(t)(k)) using the rectangle of (i,k). The tensor sum is exactly the coordinate matrix of this equivalence. Applying SequentialRegisterCircuit.coordinate_gram to the route and its inverse gives the two Gram identities.

For each nonempty block t choose j(t) in J(t) and put i(t)=φ(t)(j(t)). Rectangle disjointness gives A(u)(i(t),j(t))=1 exactly when u=t. Consequently R(U) restricted to rows (i(s),j(s)) and columns (j(t),i(t)) is the identity on Tplus. The existing rank_submatrix_le and rank_one results give the lower rank bound. This construction is also valid for empty Tplus, with empty row and column families.

For arbitrary factors, realignment of ∑q M(q)⊗N(q) is B C, where B((i,j),q)=M(q)(i,j) and C(q,(k,l))=N(q)(k,l). Thus rank(R(U))≤rank(B)≤|Q| by rank_mul_le_left and rank_le_card_width. This uses ordinary vectorization of N, with no conjugation. Apply it first to the decomposition after deleting empty blocks for the upper rank bound, and then to any proposed decomposition for the arbitrary factor lower bound. If J(t) is empty, A(t)=0; the bijection also makes I(t) empty. If X or Y is empty, every block is empty.

The supplied decomposition achieves width |Tplus| and the lower bound rules out fewer terms for this same operator U with these original local carriers. This is exact generalized operator Schmidt rank in the sense of allowing different input and output local spaces. It makes no minimum-width assertion across other operators of the same dimensions. No physical swap is postcomposed.

Realignment rank as a tensor factor count is established mathematics: Müller-Hermes and Nechita, arXiv:1612.07616v1, Proposition 2.1 and Remark 2.2, discuss the rank bridge; Definition 3.1 and Lemma 3.2 give permutation-tableaux constructions with preserved local spaces. Tyson, arXiv:quant-ph/0306144v2, Definition 1, permits four distinct local input and output spaces. The construction here proves the general rectangle-partition route and its identity-minor certificate on the exchanged rectangular carriers. No global novelty claim is made.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition.unitary_exact_width`
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../../Entanglement/SequentialRegisterCircuit.md)
