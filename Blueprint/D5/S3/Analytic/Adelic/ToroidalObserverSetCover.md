# Toroidal Observer Design as Weighted Set Cover

## Abstract

Positive-cost toroidal observers on a spectral window form a weighted set-cover problem over their nonvanishing regions.

**Theorem 1.1 (Toroidal observer design is weighted set cover).**

$$\begin{aligned}\forall I: \operatorname{Type}(), d: \operatorname{ToroidalObserverDesign}(I), K: \operatorname{Set}(\mathbb{C}),\\\operatorname{toroidalObserverCost}(d, K) = \operatorname{sInf}(\{v \in \operatorname{EReal}() \mid \exists F: \operatorname{Finset}(I), K \subseteq \operatorname{Union}(i \in F, \{s \in \mathbb{C} \mid \operatorname{twist}(d, i, s) \neq 0\}) \land v = \sum_{i \in F} \operatorname{cost}(d, i)\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalObserverSetCover.toroidal_observer_design_is_weighted_set_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source does not construct the completed quadratic L-functions, so the Lean design accepts the twist family as an abstract parameter. Its visible region is the existing canonical nonvanishingDomain, and every observer cost is strictly positive.

A finite selection is feasible exactly when the ambient compact-window set K is contained in the union of its nonzero-twist regions. The objective is the extended-real infimum of the corresponding finite cost sums; an absent finite cover therefore retains value top.

The definition is realizable rather than vacuous: on the one-element index type, the constant twist one with cost one covers the whole complex plane by its singleton selection, with total cost one.

No identification of the cost with torus length, log discriminant, or conductor is asserted, and no optimality claim for discriminant five is formalized; the source supplies neither definitions nor proofs for those stronger clauses.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalObserverSetCover.toroidal_observer_design_is_weighted_set_cover`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCechCompletion](ToroidalCechCompletion.md)
