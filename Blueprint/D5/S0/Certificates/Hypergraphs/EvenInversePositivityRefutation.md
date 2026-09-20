# Even Hyperedges Do Not Ensure Inverse Positivity

## Abstract

Six four-element edges on eight vertices give inverse coefficient minus fourteen.

**Definition 1.1 (The source equivalence for simple hypergraphs).**

$$\mathit{claim} = \left(\forall n \in \mathit{Nat},\; 0 < n \Rightarrow \left(\forall E \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \left(\left(\forall e \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; e \in E \Rightarrow 2 \le \operatorname{card}\left(e\right)\right) \land \left(\forall e \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; e \in E \Rightarrow \left(\forall f \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; f \in E \Rightarrow \left(e \subseteq f \Rightarrow e = f\right)\right)\right)\right) \Rightarrow \left(\left(\forall m \in \operatorname{Finsupp}\left(\operatorname{Fin}\left(n\right), \mathit{Nat}\right),\; 0 \le \operatorname{coeff}\left(m, \operatorname{signedIndependence}\left(E\right)^{-1}\right)\right) \Leftrightarrow \left(\forall e \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; e \in E \Rightarrow \operatorname{Even}\left(\operatorname{card}\left(e\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.claim` (`✓ std3`).

*Citation.* Chaithra P; Shushma Rani; R. Venkatesh (2025). *Marked multi-colorings and marked chromatic polynomials of hypergraphs and subspace arrangements*. DOI: [10.48550/arXiv.2507.20847](https://doi.org/10.48550/arXiv.2507.20847). URL: <https://arxiv.org/html/2507.20847v1>.

*Commentary.*

Section 8.1, PDF p. 23, states: “Let 𝒢 be a simple hypergraph. Then we have I(𝒢,−x)⁻¹ ≥ 0 if and only if all edges of 𝒢 must have even number of elements.” Mathematical glyphs and whitespace in the quotations are normalized; the prose is verbatim.

Section 3.1, PDF p. 7, begins: “Let n be a positive integer.” Definition 2(1), p. 7, says: “A hypergraph 𝒢 is called simple if for any e,f ∈ ℰ, we have |e| ≥ 2 and e ⊆ f implies e = f.” Definition 2(5), p. 7, says: “A subset I ⊆ 𝒱 is called independent if no edge of 𝒢 is entirely contained in I, i.e., e ⊈ I for all e ∈ ℰ.”

The formula expands SourceSimple into its edge-size and inclusion conditions. Fin n relabels the source vertex set [n]. Finsupp(Fin n,Nat) is the type Fin n →₀ Nat of all exponent multiindices. The signed independence series belongs to MvPowerSeries (Fin n) ℚ: for every independent subset S it has the monomial with exponent indicator S and coefficient (−1)^|S|, where indicator S is one on S and zero elsewhere. Definition 3, p. 7, sums over all independent subsets, including the empty subset. Consequently the constant coefficient is one. The coefficient ring is rational (p. 1), and the order is coefficientwise (p. 2); the assertion concerns every multiindex, not only squarefree ones. This is the ordinary independence polynomial, without a choice of marked vertices.

**Theorem 1.2 (An eight-vertex counterexample).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/even-hypergraph-inverse-positivity-refutation` (refuted) by `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"even-hypergraph-inverse-positivity-refutation","declaration_gid":"D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chaithra P; Shushma Rani; R. Venkatesh (2025). *Marked multi-colorings and marked chromatic polynomials of hypergraphs and subspace arrangements*. DOI: [10.48550/arXiv.2507.20847](https://doi.org/10.48550/arXiv.2507.20847). URL: <https://arxiv.org/html/2507.20847v1>.

*Commentary.*

Label vertices 0,…,7 by a1,a2,a3,b1,b2,b3,s,t. Take the edges {6,7,0,1}, {6,7,1,2}, {6,7,2,0}, {6,7,3,4}, {6,7,4,5}, and {6,7,5,3}. These are six distinct four-element sets. Thus every edge has even size at least two, and containment between edges forces equality.

For a subset T, put i = |T ∩ {0,1,2}| and j = |T ∩ {3,4,5}|. Let d(0),d(1),d(2),d(3) be 1,1,0,−4, respectively. Set c(T)=1 when T does not contain both 6 and 7, and c(T)=2−d(i)d(j) otherwise. For a subset U let f(U)=(−1)^|U| when U is independent, and f(U)=0 otherwise. The exact subset convolution satisfies c(∅)=1 and, for nonempty T, c(T)=−∑_{∅≠U⊆T} f(U)c(T∖U).

The actual formal inverse has constant coefficient one. A decomposition of the squarefree exponent indicator T is uniquely a subset U of T and its complement T∖U. Its coefficient recurrence is therefore precisely the displayed subset convolution. Induction on |T| identifies c(T) with the actual inverse coefficient; every nonempty U leaves a smaller complement. At the full vertex set the coefficient is 2−(−4)(−4)=−14. This single negative coefficient contradicts the even-edges-to-positivity direction and hence refutes the full equivalence.

The same coefficient has a compact algebraic explanation. Write A=∏(1−a_i), B=∏(1−b_i), J_A=1−a1−a2−a3 and J_B=1−b1−b2−b3. The signed independence polynomial is F=(1−s−t)AB+stJ_AJ_B, so [st]F⁻¹=2/(AB)−J_AJ_B/(A²B²). The coefficient of a1a2a3 in J_A/A² is 8−3·4=−4, and the b coefficient is identical. The full squarefree coefficient is thus 2−16=−14. This expresses the same counterexample and certificate.

## References

- Truth anchor: `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.result`
