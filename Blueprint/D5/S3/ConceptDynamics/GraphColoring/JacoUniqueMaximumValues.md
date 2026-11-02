# Unique values across all Jaco graph orders

## Abstract

The positive maximum-degree values attained at exactly one recursive Jaco graph order are the complete source sequence, realized by one explicit infinite indexed family.

**Definition 1.1 (Across-orders value uniqueness).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.UniqueValue`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.UniqueValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an integer k, UniqueValue k means k is at least one and there is a natural order n at least two with the ordinary maximum degree of jaco n equal to k, such that every natural m at least two with that same maximum degree equals n. This is numerical value uniqueness across orders, not uniqueness of a maximizing vertex within one graph.

**Definition 1.2 (The entire source sequence).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.sequenceValue`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.sequenceValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural t, sequenceValue t is the integer floor of t times phi squared, minus one, where phi=(1+sqrt(5))/2 is Real.goldenRatio. The theorem uses every t at least one, exactly the displayed formula of arXiv:2507.16500v1, Conjecture 2.3, printed page 5. Zero is an auxiliary index outside the claimed sequence.

**Definition 1.3 (One explicit order function).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.realizingOrder`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.realizingOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write B(q)=floor(q*phi) for integer q. The natural realizingOrder t is the nonnegative part of B(floor(t*phi squared))-1. The theorem proves it is at least two for every positive t, so this conversion truncates nothing on the source domain.

**Theorem 1.4 (Complete classification and infinite realizing family).**

$$(\forall k \in \mathbb{Z},\; (1 \le k) \Rightarrow ((\operatorname{UniqueValue}\left(k\right)) \Leftrightarrow (\exists t \in \mathrm{Nat},\; (1 \le t) \land (k = \operatorname{sequenceValue}\left(t\right))))) \land (\exists r \in \mathrm{Nat} \to \mathrm{Nat},\; (r = \mathrm{realizingOrder}) \land (\forall t \in \mathrm{Nat},\; (1 \le t) \Rightarrow ((2 \le \operatorname{r}\left(t\right)) \land ((1 \le \operatorname{sequenceValue}\left(t\right)) \land ((\operatorname{maxDegree}\left(\operatorname{jaco}\left(\operatorname{r}\left(t\right)\right)\right) = \operatorname{sequenceValue}\left(t\right)) \land (\forall m \in \mathrm{Nat},\; (1 \le m) \Rightarrow ((\operatorname{maxDegree}\left(\operatorname{jaco}\left(m\right)\right) = \operatorname{sequenceValue}\left(t\right)) \Rightarrow (m = \operatorname{r}\left(t\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.result` (`✓ std3`). ∎

*Resolves.* `Problems/kok-jaco-unique-maximum-values` (proved) by `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kok-jaco-unique-maximum-values","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Maximum degrees are viewed as integers through the natural embedding. The graph is the existing underlying simple graph of the original f(x)=x recursive Jaco construction, not a graph defined by the desired degree formula. Reuse JacoMaximumDegree.result for its maximum degree at all n at least two. Irrational floor inversion gives the entire fiber B(k+1)-1 <= n <= B(k+2)-2. Both endpoints belong to the positive-order source domain. The fiber is a singleton exactly when floor((k+2)/phi)=floor((k+1)/phi). A strict jump is equivalent to k+1 belonging to the positive lower Beatty sequence. Direct application of Mathlib's Irrational.beattySeq_symmDiff_beattySeq_pos at phi and phi squared gives precisely its complementary upper Beatty sequence. This proves both directions for every positive integer k.

For each positive t, the same explicit function realizingOrder selects the lower endpoint of that singleton fiber. Its degree is sequenceValue t, which is positive. The singleton graph has maximum degree zero, so uniqueness extends to every positive m including one. Thus G_t=jaco(realizingOrder t) is one whole infinite indexed realizing family. The source's family notation is read memberwise, its existence allows selection of corresponding orders, and the parameter is ordinary degree restricted to globally unique positive values. No total parameter on ineligible graphs or requirement G_t=J_t is added. These are the explicit source conventions; they do not assert an author-issued correction. Conjecture 2.5 concerns a different vertex-count property. The separately reported MathDB answers concern 2.2 and 2.5; neither report is attributed here to 2.3. Literature screening and external priority remain bounded; no worldwide novelty claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.UniqueValue`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.realizingOrder`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.result`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.sequenceValue`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree](JacoMaximumDegree.md)
