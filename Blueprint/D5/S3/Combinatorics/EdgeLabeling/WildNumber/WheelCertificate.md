# WheelCertificate

## Abstract

All terminal greedy runs on the four-colored wheel have six edges.

**Definition 1.1 (Elist).**

$$(\operatorname{Elist} : \operatorname{List} ((\operatorname{Fin} 8) \times (\operatorname{Fin} 8))) = ([ (0 , 1) , (0 , 3) , (0 , 4) , (0 , 2) , (0 , 6) , (4 , 5) , (6 , 7) , (0 , 5) , (0 , 7) , (1 , 2) , (1 , 7) , (5 , 6) , (2 , 3) , (3 , 4) ])$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.Elist` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Definition 1.2 (H).**

$$(\operatorname{H} : \operatorname{SimpleGraph} (\operatorname{Fin} 8)) = (\operatorname{SimpleGraph} . \operatorname{fromRel} (\operatorname{fun} \operatorname{u} \operatorname{v} \mapsto (\operatorname{u} , \operatorname{v}) \in \operatorname{Elist}))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.H` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Definition 1.3 (edgeColor).**

$$\forall (\operatorname{e} : \operatorname{Sym2} (\operatorname{Fin} 8)) , \operatorname{edgeColor} \operatorname{e} = (\operatorname{if} \operatorname{e} = \operatorname{s} (0 , 1) \lor \operatorname{e} = \operatorname{s} (0 , 3) \lor \operatorname{e} = \operatorname{s} (0 , 4) \operatorname{then} 0 \operatorname{else} \operatorname{if} \operatorname{e} = \operatorname{s} (0 , 2) \lor \operatorname{e} = \operatorname{s} (0 , 6) \lor \operatorname{e} = \operatorname{s} (4 , 5) \lor \operatorname{e} = \operatorname{s} (6 , 7) \operatorname{then} 1 \operatorname{else} \operatorname{if} \operatorname{e} = \operatorname{s} (0 , 5) \lor \operatorname{e} = \operatorname{s} (0 , 7) \lor \operatorname{e} = \operatorname{s} (1 , 2) \lor \operatorname{e} = \operatorname{s} (1 , 7) \lor \operatorname{e} = \operatorname{s} (5 , 6) \operatorname{then} 2 \operatorname{else} 3)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.edgeColor` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Definition 1.4 (gamma).**

$$(\operatorname{gamma} : \operatorname{H} . \operatorname{edgeSet} \to \operatorname{Fin} 4) = (\operatorname{fun} (\operatorname{e} : \operatorname{H} . \operatorname{edgeSet}) \mapsto \operatorname{edgeColor} \operatorname{e})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.gamma` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.5 (H connected).**

$$\operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{H} . \operatorname{Connected}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.H_connected` (`✓ std3`). ∎

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.6 (gamma surjective).**

$$\operatorname{Function} . \operatorname{Surjective} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{gamma}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.gamma_surjective` (`✓ std3`). ∎

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Definition 1.7 (O).**

$$(\operatorname{O} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Fin} 8))) = (\{ \operatorname{s} (0 , 3) , \operatorname{s} (0 , 7) , \operatorname{s} (1 , 2) , \operatorname{s} (4 , 5) , \operatorname{s} (5 , 6) \})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.8 (O card).**

$$\operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{O} . \operatorname{card} = 5$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O_card` (`✓ std3`). ∎

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.9 (O color connecting).**

$$\operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{H} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{gamma} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{O}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O_color_connecting` (`✓ std3`). ∎

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.10 (color connecting card ge five).**

$$\forall (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Fin} 8))) , \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{H} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{gamma} \operatorname{W} \to 5 \leq \operatorname{W} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.color_connecting_card_ge_five` (`✓ std3`). ∎

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

**Theorem 1.11 (all outputs six).**

$$\forall (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Fin} 8))) , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{H} \operatorname{WheelCertificate} . \operatorname{Wheel} . \operatorname{gamma} \operatorname{W} \to \operatorname{W} . \operatorname{card} = 6$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.all_outputs_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Example 5.12, PDF page 17: “As an example in which the Greedy Algorithm produces a color-connecting wild set that is not an ideal wild set, consider the wheel graph in Figure 9, which has vertex set V = {vᵢ : 0 ≤ i ≤ 7} and colored edge sets” The vertices are numbered from 0 to 7 and the four colors from 0 to 3. The set O has edges 03, 07, 12, 45, and 56.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.Elist`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.H`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.H_connected`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O_card`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.O_color_connecting`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.all_outputs_six`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.color_connecting_card_ge_five`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.edgeColor`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.gamma`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate.gamma_surjective`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror](ComponentMirror.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy](Greedy.md)
