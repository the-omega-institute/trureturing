# Noncommutativity does not imply complete incompatibility

## Abstract

In every complex dimension d ≥ 4, two orthonormal bases can have noncommuting coordinate projectors for every pair of nonempty proper index sets while failing complete incompatibility.

**Definition 1.1 (Coordinate orthogonal projectors).**

$$\forall d \in \mathbb{N},\; \forall b \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \operatorname{projector}\left(b, S, i, j\right) = \sum_{k \in S} b\left(k\right)\left(i\right) \cdot \operatorname{star}\left(b\left(k\right)\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.projector` (`✓ std3`).

*Citation.* Stephan De Bièvre (2023). *Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality*. DOI: [10.1063/5.0110267](https://doi.org/10.1063/5.0110267). URL: <https://arxiv.org/abs/2207.07451v1>.

*Commentary.*

Section 3, p. 5: “Given bases 𝒜 and ℬ, we introduce a family of orthogonal projectors as follows. For every S,T ⊂ ⟦1,d⟧ := {1,2,...,d},” followed by Π_𝒜(S) = ∑_{i∈S} |a_i⟩⟨a_i| and Π_ℬ(T) = ∑_{j∈T} |b_j⟩⟨b_j|. The displayed matrix entry is exactly this sum of rank-one projectors. star is complex conjugation; b(k)(i) is the i-th coordinate of the k-th basis vector.

**Definition 1.2 (Condition (ii)).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; \forall b \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; (\operatorname{NonCommutingProjectors}\left(a, b\right)) \Leftrightarrow (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{Nonempty}\left(S\right)) \Rightarrow ((S \ne \operatorname{univ}\left(\operatorname{Fin}\left(d\right)\right)) \Rightarrow ((\operatorname{Nonempty}\left(T\right)) \Rightarrow ((T \ne \operatorname{univ}\left(\operatorname{Fin}\left(d\right)\right)) \Rightarrow (\operatorname{projector}\left(a, S\right) \cdot \operatorname{projector}\left(b, T\right) \ne \operatorname{projector}\left(b, T\right) \cdot \operatorname{projector}\left(a, S\right))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.NonCommutingProjectors` (`✓ std3`).

*Citation.* Stephan De Bièvre (2023). *Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality*. DOI: [10.1063/5.0110267](https://doi.org/10.1063/5.0110267). URL: <https://arxiv.org/abs/2207.07451v1>.

*Commentary.*

Proposition 7(ii), p. 16: “For all S,T ⊂ ⟦1,d⟧, with 1 ≤ |S|, |T| < d, [Π_𝒜(S),Π_ℬ(T)] ≠ 0.” Nonempty proper finite subsets express precisely the two cardinality bounds. The two products are complex matrix products, so their inequality expresses a nonzero operator commutator.

**Definition 1.3 (Condition (i): complete incompatibility).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; \forall b \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; (\operatorname{CompletelyIncompatible}\left(a, b\right)) \Leftrightarrow (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{card}\left(S\right) + \operatorname{card}\left(T\right) \le d) \Rightarrow (\operatorname{inf}\left(\operatorname{span}\left(\mathbb{C}, \operatorname{image}\left(a, \operatorname{coe}\left(S\right)\right)\right), \operatorname{span}\left(\mathbb{C}, \operatorname{image}\left(b, \operatorname{coe}\left(T\right)\right)\right)\right) = \operatorname{bot}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.CompletelyIncompatible` (`✓ std3`).

*Citation.* Stephan De Bièvre (2023). *Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality*. DOI: [10.1063/5.0110267](https://doi.org/10.1063/5.0110267). URL: <https://arxiv.org/abs/2207.07451v1>.

*Commentary.*

Definition 4, p. 14: “We say that two bases 𝒜 and ℬ are completely incompatible (COINC) if and only if all index sets S,T in ⟦1,d⟧ for which |S|+|T|≤d have the property that Π_𝒜(S)ℋ∩Π_ℬ(T)ℋ={0}.” The image of each coordinate projector is the complex span of the indicated basis vectors. coe denotes SetLike.coe from Finset (Fin d) to Set (Fin d); image is set image; inf is intersection of complex submodules; bot is the zero submodule. Empty index sets remain in scope.

**Definition 1.4 (De Bièvre's conjecture).**

$$(claim) \Leftrightarrow (\forall d \in \mathbb{N},\; (4 \le d) \Rightarrow (\exists a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; \exists b \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(d\right)\right)\right),\; (\operatorname{NonCommutingProjectors}\left(a, b\right)) \land (\neg(\operatorname{CompletelyIncompatible}\left(a, b\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.claim` (`✓ std3`).

*Citation.* Stephan De Bièvre (2023). *Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality*. DOI: [10.1063/5.0110267](https://doi.org/10.1063/5.0110267). URL: <https://arxiv.org/abs/2207.07451v1>.

*Commentary.*

Section 5, p. 16: “We conjecture it is true that (ii) does not imply (i) in all dimensions d ≥ 4, but we have not produced such examples in other dimensions than 4 and 6.” Thus for each natural dimension at least four there exist two arbitrary orthonormal bases satisfying condition (ii) and failing condition (i).

**Theorem 1.5 (The conjecture holds in every dimension at least four).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephan De Bièvre (2023). *Relating incompatibility, noncommutativity, uncertainty and Kirkwood-Dirac nonclassicality*. DOI: [10.1063/5.0110267](https://doi.org/10.1063/5.0110267). URL: <https://arxiv.org/abs/2207.07451v1>.

*Commentary.*

Take the standard basis and the columns of H = I − (2/q)wwᵀ, where w = (1,2,...,2) and q = 4d−3. This real Householder reflection is unitary over the complex space. For a nonempty proper set T let m = ∑_{k∈T} w_k², so 0 < m < q. Every off-diagonal entry of its coordinate projector equals (2w_iw_j/q²)(2m−q(1_T(i)+1_T(j))). The last factor is nonzero: indicator sums zero and two use the strict mass bounds, and indicator sum one uses the oddness of q. A coordinate inside S and one outside S then give a nonzero commutator entry for every nonempty proper S. Finally 2e₀−e₁ is nonzero and equals 2He₀−He₁, so it lies in both two-coordinate spans for S = T = {0,1}. Their total cardinality is four, which is at most d.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.CompletelyIncompatible`
- Truth anchor: `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.NonCommutingProjectors`
- Truth anchor: `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.projector`
- Truth anchor: `D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.result`
