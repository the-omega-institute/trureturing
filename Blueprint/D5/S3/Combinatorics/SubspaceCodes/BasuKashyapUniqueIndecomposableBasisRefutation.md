# A Unique Indecomposable Basis Without Intersection Closure

## Abstract

A unique indecomposable basis need not imply intersection closure.

**Definition 1.1 (Subspace distance).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall X \in \operatorname{Submodule}\left(F, V\right),\; \forall Y \in \operatorname{Submodule}\left(F, V\right),\; \operatorname{dS}\left(X, Y\right) = (\operatorname{finrank}\left(F, X\right):\mathrm{Int}) + (\operatorname{finrank}\left(F, Y\right):\mathrm{Int}) - 2 \cdot (\operatorname{finrank}\left(F, \operatorname{Min}.\operatorname{min}(X,Y)\right):\mathrm{Int})$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.dS` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

On page 2 the subspace distance is d_S(X,Y) = dim X + dim Y − 2 dim(X ∩ Y). Dimensions are Module.finrank; the casts to integers precede subtraction. The ambient space in the conjecture is Fin n → F.

**Definition 1.2 (Linear subspace codes).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall L \in \operatorname{LinearCode}\left(F, V\right),\; \begin{aligned}(L.\mathrm{U}:\operatorname{Set}\left(\operatorname{Submodule}\left(F, V\right)\right))\\(L.\mathrm{botMem}:\operatorname{Bot}.\operatorname{bot} \in L.\mathrm{U})\\(L.\mathrm{op}:L.\mathrm{U} \to \left(L.\mathrm{U} \to L.\mathrm{U}\right))\\(L.\mathrm{assoc}:\forall x \in L.\mathrm{U},\; \forall y \in L.\mathrm{U},\; \forall z \in L.\mathrm{U},\; L.\mathrm{op}(L.\mathrm{op}(x,y),z) = L.\mathrm{op}(x,L.\mathrm{op}(y,z)))\\(L.\mathrm{comm}:\forall x \in L.\mathrm{U},\; \forall y \in L.\mathrm{U},\; L.\mathrm{op}(x,y) = L.\mathrm{op}(y,x))\\(L.\mathrm{leftId}:\forall x \in L.\mathrm{U},\; L.\mathrm{op}(\langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle,x) = x)\\(L.\mathrm{rightId}:\forall x \in L.\mathrm{U},\; L.\mathrm{op}(x,\langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle) = x)\\(L.\mathrm{inverse}:\forall x \in L.\mathrm{U},\; \exists y \in L.\mathrm{U},\; (L.\mathrm{op}(x,y) = \langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle) \land (L.\mathrm{op}(y,x) = \langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle))\\(L.\mathrm{self}:\forall x \in L.\mathrm{U},\; L.\mathrm{op}(x,x) = \langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle)\\(L.\mathrm{isometry}:\forall x \in L.\mathrm{U},\; \forall y \in L.\mathrm{U},\; \forall z \in L.\mathrm{U},\; \operatorname{dS}\left(\operatorname{val}\left(L.\mathrm{op}(x,y)\right), \operatorname{val}\left(L.\mathrm{op}(x,z)\right)\right) = \operatorname{dS}\left(\operatorname{val}\left(y\right), \operatorname{val}\left(z\right)\right))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.LinearCode` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

Pages 4–5, Definition 1 (TeX label L): “A subset 𝒰 ⊆ ℙ_q(n), with {0} ∈ 𝒰, is a linear subspace code if there exists a function ⊞ : 𝒰 × 𝒰 → 𝒰 such that: (i) (𝒰, ⊞) is an abelian group; (ii) the identity element of (𝒰, ⊞) is {0}; (iii) X ⊞ X = {0} for every group element X ∈ 𝒰; (iv) the addition operation ⊞ is isometric, i.e., d_S(X ⊞ Y₁, X ⊞ Y₂) = d_S(Y₁, Y₂) for all X, Y₁, Y₂ ∈ 𝒰.” LinearCode records U, its bottom membership, and the operation on the subtype, followed by exactly these laws. The identity is the subtype pair formed from bottom and botMem.

**Definition 1.3 (The identity codeword).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall L \in \operatorname{LinearCode}\left(F, V\right),\; L.\mathrm{codeZero} = \langle\operatorname{Bot}.\operatorname{bot},L.\mathrm{botMem}\rangle$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.codeZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

The identity codeword is the zero submodule equipped with its membership proof.

**Definition 1.4 (Indecomposable codewords).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall L \in \operatorname{LinearCode}\left(F, V\right),\; \forall x \in L.\mathrm{U},\; (L.\mathrm{Indecomposable}(x)) \Leftrightarrow ((\operatorname{val}\left(x\right) \ne \operatorname{Bot}.\operatorname{bot}) \land (\neg (\exists y \in L.\mathrm{U},\; \exists z \in L.\mathrm{U},\; (x = L.\mathrm{op}(y,z)) \land \left((\operatorname{finrank}\left(F, \operatorname{val}\left(y\right)\right) < \operatorname{finrank}\left(F, \operatorname{val}\left(x\right)\right)) \land (\operatorname{finrank}\left(F, \operatorname{val}\left(z\right)\right) < \operatorname{finrank}\left(F, \operatorname{val}\left(x\right)\right))\right))))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.Indecomposable` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

Page 19, Definition 11 (TeX label 9): “A codeword Y ≠ {0} of a linear subspace code 𝒰 is said to be indecomposable if Y cannot be expressed as Y = Y₁ ⊞ Y₂ for any Y₁,Y₂ ∈ 𝒰 with dim Y₁, dim Y₂ < dim Y.” The two strict inequalities concern ambient subspace dimensions; the summation uses L.op.

**Definition 1.5 (An unordered basis).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall L \in \operatorname{LinearCode}\left(F, V\right),\; \forall S \in \operatorname{Finset}\left(L.\mathrm{U}\right),\; (L.\mathrm{IsBasis}(S)) \Leftrightarrow (\forall x \in L.\mathrm{U},\; \exists!(T:\operatorname{Finset}\left(L.\mathrm{U}\right)), (T \subseteq S) \land (\operatorname{Finset}.\operatorname{fold}(L.\mathrm{op},L.\mathrm{codeZero},\mathrm{id},T) = x))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.IsBasis` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

Section 6, page 22: “We observed earlier that the indecomposable codewords in a linear subspace code constitute a basis for the vector space over 𝔽₂ formed by the code (Remark 5). We refer to such a basis as an indecomposable basis.” A basis is a finite subset S of the subtype L.U such that every codeword has exactly one representing finite subset T of S. Finite sums use Finset.fold with L.op, identity L.codeZero and id, with associative and commutative instances supplied by L.assoc and L.comm; the empty sum is L.codeZero. This is the 𝔽₂-space formed by the code operation. It is not an ordered list or an ambient F-basis.

**Definition 1.6 (An indecomposable basis).**

$$\forall F \in \mathrm{Type},\; \forall V \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(F, V\right)], \forall L \in \operatorname{LinearCode}\left(F, V\right),\; \forall S \in \operatorname{Finset}\left(L.\mathrm{U}\right),\; (L.\mathrm{IsIndecomposableBasis}(S)) \Leftrightarrow ((L.\mathrm{IsBasis}(S)) \land (\forall x \in L.\mathrm{U},\; (x \in S) \Rightarrow (L.\mathrm{Indecomposable}(x))))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.IsIndecomposableBasis` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

Section 6, page 22: “We refer to such a basis as an indecomposable basis.” Every member of this basis is indecomposable, and the basis is an unordered finite subset of codewords.

**Definition 1.7 (Conjecture 6.1).**

$$(\mathrm{claim}) \Leftrightarrow (\forall F \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)], \forall n \in \mathrm{Nat},\; \forall L \in \operatorname{LinearCode}\left(F, \operatorname{Fin}\left(n\right) \to F\right),\; (\exists!(S:\operatorname{Finset}\left(L.\mathrm{U}\right)), L.\mathrm{IsIndecomposableBasis}(S)) \Leftrightarrow (\operatorname{InfClosed}\left(L.\mathrm{U}\right)))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.claim` (`✓ std3`).

*Citation.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

Page 23, Conjecture 6.1: “A linear code 𝒰 in ℙ_q(n) has a unique indecomposable basis if and only if 𝒰 is closed under intersection.” F ranges over finite fields in Type, n over natural numbers, and L over all subsets of Submodule F (Fin n → F) with every operation satisfying the four defining axioms. Uniqueness is uniqueness of an unordered finite subset of codewords, with basis and indecomposability relative to that same operation. InfClosed L.U expresses closure under the infimum of actual submodules: page 15, Definition 9 (TeX label 8), “A linear code 𝒰 ⊆ ℙ_q(n) with the property that X ∩ Y ∈ 𝒰 whenever X, Y ∈ 𝒰 is said to be a linear code closed under intersection.”

**Theorem 1.8 (Refutation by a Klein family).**

$$\neg \mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/basu-kashyap-2019-unique-indecomposable-basis` (refuted) by `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"basu-kashyap-2019-unique-indecomposable-basis","declaration_gid":"D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pranab Basu, Navin Kashyap (2019). *The Lattice Structure of Linear Subspace Codes*. URL: <https://arxiv.org/abs/1911.00721v1>.

*Commentary.*

For every finite field, split the coordinates into three disjoint blocks I,P,Q of dimensions i,a,b with 0 < i < a and i < b. The subspaces A = I ⊕ P, B = I ⊕ Q and C = P ⊕ Q, together with zero, form a linear subspace code under Klein addition. Their intersections are I,P,Q; their dimensions are i+a,i+b,a+b. Translation preserves the literal integer subspace distance.

Exactly A and B are indecomposable: C = A ⊞ B has two strictly smaller summands, whereas every decomposition of A or B includes a summand of at least its dimension. The four distinct subset sums of {A,B} exhaust the code, and every indecomposable basis must contain both. The nonzero intersection I is outside the code. The universal conjecture fails at F = ZMod 2, i = 1, a = b = 2, n = 5.

Remark 5 on page 21 assumes intersection closure when asserting that the indecomposables form a basis. That qualifier is omitted in the Section 6 recap. The source's intersection-closed direction remains intact, as do its proved lattice statements under that hypothesis; the separate Braun–Etzion–Vardy cardinality conjecture is unaffected.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.Indecomposable`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.IsBasis`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.IsIndecomposableBasis`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.LinearCode`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.codeZero`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.dS`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result`
