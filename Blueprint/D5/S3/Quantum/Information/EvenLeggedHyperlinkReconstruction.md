# Reconstruction from even-legged hyperlinks

## Abstract

Universal rational leg factors reconstruct every real complement-symmetric set function vanishing at the empty set from its nonempty even hyperlinks.

**Definition 1.1 (The signed subset transform).**

$$\forall alpha \in \operatorname{Type},\; \forall S \in (\operatorname{Finset}\left(alpha\right) \to \mathbb{R}),\; \forall I \in \operatorname{Finset}\left(alpha\right),\; \operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.hyperlink}\left(S, I\right) = \sum_{B \in \operatorname{Finset.powerset}\left(I\right)} ((-1: \mathbb{R})^{(\operatorname{Finset.card}\left(I\right) - \operatorname{Finset.card}\left(B\right): \mathbb{N})} \cdot S\left(B\right))$$

*Formalization.* `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.hyperlink` (`✓ std3`).

*Citation.* Silvia N. Santalla, Sudipto Singha Roy, Germán Sierra, Javier Rodríguez-Laguna (2026). *The hyperlink representation of entanglement and the inclusion-exclusion principle*. DOI: [10.1103/gmjw-rb13](https://doi.org/10.1103/gmjw-rb13). URL: <https://arxiv.org/abs/2601.17926v2>.

*Commentary.*

Equation (5) defines the hyperlink by inclusion-exclusion over all subsets of I. The exponent is the natural-number difference between the two cardinalities, and the sign and set-function values are real. No symmetry or vanishing hypothesis is needed for this definition.

**Definition 1.2 (The triangular inverse coefficients).**

$$\forall r \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.legInverseCoeff}\left(r\right) = (\text{if} r = 0 \text{then} 1 \text{else} (\text{if} \operatorname{Even}\left(r\right) \text{then} -(\frac{1}{2}: \mathbb{Q}) \cdot \sum_{j: \operatorname{Fin}\left(r\right)} ((\text{if} \operatorname{Even}\left(\operatorname{val}\left(j\right)\right) \text{then} (\operatorname{Nat.choose}\left(r, \operatorname{val}\left(j\right)\right): \mathbb{Q}) \cdot \operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.legInverseCoeff}\left(\operatorname{val}\left(j\right)\right) \text{else} 0)) \text{else} 0))$$

*Formalization.* `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.legInverseCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at rank zero is one. Odd ranks have coefficient zero. At a positive even rank r, the coefficient is minus one half of the sum over j : Fin r, whose summand is Nat.choose r val(j) times the coefficient at val(j) when val(j) is even, and zero otherwise. Here val(j) is the natural value of j : Fin r. Each binomial coefficient is cast to the rational numbers before multiplication. This recurrence determines a rational sequence by strong recursion.

**Definition 1.3 (The rational leg factors).**

$$\forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.legFactor}\left(m, p\right) = (\text{if} p \le m \text{then} -(\frac{1}{2}: \mathbb{Q}) \cdot \sum_{k \in \operatorname{Finset.range}\left(m + 1\right), (2 \le k) \land (\operatorname{Even}\left(k\right))} (\operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.legInverseCoeff}\left((m - k: \mathbb{N})\right) \cdot ((\operatorname{Nat.choose}\left(m, k\right): \mathbb{Q}) - (\operatorname{Nat.choose}\left(p, k\right): \mathbb{Q}) - (\operatorname{Nat.choose}\left((m - p: \mathbb{N}), k\right): \mathbb{Q}))) \text{else} 0)$$

*Formalization.* `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.legFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p at most m, the sum ranges over even k between two and m, inclusive. The binomial difference counts the k-element subsets of an m-element set meeting both sides of a split into p and m minus p elements. Each binomial coefficient is cast to the rational numbers before subtraction. Both m minus k and m minus p use natural-number subtraction. The value is zero when p exceeds m.

**Definition 1.4 (A single coefficient family for every finite system).**

$$(\operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.claim}) \Leftrightarrow (\exists L \in (\mathbb{N} \to (\mathbb{N} \to \mathbb{Q})),\; (\forall m \in \mathbb{N},\; (L\left(m, 0\right) = 0) \land (L\left(m, m\right) = 0)) \land ((\forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; L\left(m, p\right) = L\left(m, (m - p: \mathbb{N})\right)) \land (\forall N \in \mathbb{N},\; \forall S \in (\operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right) \to \mathbb{R}),\; (S\left(\emptyset\right) = 0) \Rightarrow ((\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right),\; S\left(\operatorname{Finset.compl}\left(A\right)\right) = S\left(A\right)) \Rightarrow (\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right),\; S\left(A\right) = \sum_{I \in \operatorname{Finset.powerset}\left((\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right))\right), (\operatorname{Even}\left(\operatorname{Finset.card}\left(I\right)\right)) \land (I \ne \emptyset)} ((L\left(\operatorname{Finset.card}\left(I\right), \operatorname{Finset.card}\left(\operatorname{Finset.inter}\left(I, A\right)\right)\right): \mathbb{R}) \cdot \operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.hyperlink}\left(S, I\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.claim` (`✓ std3`).

*Citation.* Silvia N. Santalla, Sudipto Singha Roy, Germán Sierra, Javier Rodríguez-Laguna (2026). *The hyperlink representation of entanglement and the inclusion-exclusion principle*. DOI: [10.1103/gmjw-rb13](https://doi.org/10.1103/gmjw-rb13). URL: <https://arxiv.org/abs/2601.17926v2>.

*Commentary.*

Appendix B, (B2), proposes reconstruction using even-legged hyperlinks with leg factors independent of the number of parties. The coefficient existential precedes N and S: one rational family works for every N and every real complement-symmetric set function vanishing at the empty set. The two coefficient laws give zero values at both ends and symmetry under p mapping to m minus p, for all natural m and p. The sum includes precisely the nonempty even subsets of Fin N. Entanglement entropies of a finite-dimensional pure state have the two set-function properties: complementary reduced states have the same nonzero spectrum, and the empty block has entropy zero. This identification is mathematical background and is not part of the formal statement.

**Theorem 1.5 (The rational leg factors give the reconstruction).**

$$\operatorname{D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.result` (`✓ std3`). ∎

*Resolves.* `Problems/santalla-singha-roy-sierra-rodriguez-laguna-2026-even-legged-reconstruction` (proved) by `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"santalla-singha-roy-sierra-rodriguez-laguna-2026-even-legged-reconstruction","declaration_gid":"D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Silvia N. Santalla, Sudipto Singha Roy, Germán Sierra, Javier Rodríguez-Laguna (2026). *The hyperlink representation of entanglement and the inclusion-exclusion principle*. DOI: [10.1103/gmjw-rb13](https://doi.org/10.1103/gmjw-rb13). URL: <https://arxiv.org/abs/2601.17926v2>.

*Commentary.*

The theorem concerns every real complement-symmetric set function vanishing at the empty set. The explicit coefficient family is legFactor. Möbius inversion on subsets recovers the set function from all its hyperlinks. The complement transform expresses each hyperlink of the complemented function as its parity sign times the sum over containing subsets. Descending induction then shows that the nonempty even hyperlinks, together with the empty value, uniquely determine a complement-symmetric set function.

For each nonempty even subset K, the auxiliary family q_K has value minus one half when K meets both A and its complement, and zero otherwise. Its even hyperlinks give a triangular system over containing subsets. The recurrence defining legInverseCoeff inverts this system. The resulting linear combination of the q_K has the same even hyperlinks as the original function, so uniqueness identifies the two functions. Counting the subsets of each I that cross the split between A and its complement gives legFactor at the cardinalities of I and its intersection with A. This proves the reconstruction in (B2) for every finite N, along with the zero and symmetry laws.

## References

- Truth anchor: `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.claim`
- Truth anchor: `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.hyperlink`
- Truth anchor: `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.legFactor`
- Truth anchor: `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.legInverseCoeff`
- Truth anchor: `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.result`
