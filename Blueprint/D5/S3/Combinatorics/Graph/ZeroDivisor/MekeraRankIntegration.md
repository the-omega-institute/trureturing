# Rank tests for ordered annihilator-digraph arcs

## Abstract

Block ranks characterize ordered arcs in full matrix rings over fields.

**Theorem 1.1 (The ordered arc rank criterion).**

$$\forall (F: \operatorname{Type}) [\operatorname{Field}\left(F\right)], \forall n: \mathbb{N}, 2 \le n \to \forall A, B: \left(M_{n}\right)\left(F\right), A \ne B \to (A \ne 0 \land \operatorname{det}\left(A\right) = 0) \to (B \ne 0 \land \operatorname{det}\left(B\right) = 0) \to (\operatorname{arc}\left(A, B\right) \iff ((\operatorname{rank}\left(A \cdot B\right) < \operatorname{rank}\left(A\right) \land \operatorname{rank}\left(A \cdot B\right) < \operatorname{rank}\left(\operatorname{fromCols}\left(A \cdot B, B\right)\right)) \lor (\operatorname{rank}\left(A \cdot B\right) < \operatorname{rank}\left(B\right) \land \operatorname{rank}\left(A \cdot B\right) < \operatorname{rank}\left(\operatorname{fromRows}\left(A \cdot B, A\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.arc_iff_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

Mekera, Somer and Yeşil ask in the second paragraph of Section 7 how the arcs of the annihilator digraph of the full matrix ring can be characterized in terms of matrix ranks. Let F be any field, n at least two, and A and B distinct nonzero singular n-by-n matrices over F. Nonzero singular matrices are exactly the vertices of the digraph.

Write C = AB. The left witness exists exactly when the rank of C is strictly below both the rank of A and the rank of the horizontal block formed by adjoining the columns of B to C. The right witness exists exactly when the rank of C is strictly below both the rank of B and the rank of the vertical block formed by stacking the rows of A below C. Either witness suffices for the arc from A to B. The reverse arc uses BA with the endpoint roles exchanged.

The right witness requires a vector in the kernel of C outside both endpoint kernels. Two proper subspaces cannot cover the kernel of C, even over the binary field. Rank–nullity converts the resulting strict kernel inclusions into the two right-witness inequalities. Transposing and exchanging the endpoints gives the left-witness inequalities.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.arc_iff_rank`
- Dependency: [D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation](../../../../S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.md)
