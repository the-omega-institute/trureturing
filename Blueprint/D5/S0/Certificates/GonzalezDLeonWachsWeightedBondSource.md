# Weighted Bond Poset Source Semantics

## Abstract

A literal finite model of the weighted bond poset and its source Mobius polynomial.

**Definition 1.1 (The source Mobius polynomial).**

$$sourceMobiusPolynomial\left(G\right) = maximalConnectedWeightedMuSum\left(G\right)$$

*Formalization.* `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.sourceMobiusPolynomial` (`✓ std3`).

*Citation.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The displayed maximal-sum notation abbreviates the Lean definition: blocks are connected, weights satisfy 0 <= w < block cardinality, refinement uses the permitted merge increment, maximal elements are selected, and each coefficient is the incidence-algebra Mobius value from the singleton weighted bottom with exponent equal to the total block weight.

**Theorem 1.2 (The three-vertex source encoding is injective).**

$$Injective\left(localNormalFormToSource\left(hG\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.local_normal_form_to_source_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Bottom, edge-and-weight middle elements, and top weights are recovered from the actual weighted partition. This is an encoding theorem for the literal source carrier, not a replacement recurrence.

## References

- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.local_normal_form_to_source_injective`
- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.sourceMobiusPolynomial`
