# Topological Factor Minimality

## Abstract

Continuous surjective equivariant factors descend forward-orbit minimality.

**Theorem 1.1 (A continuous surjective equivariant factor descends minimality).**

$$\forall M: Type, \forall X: Type, \forall Y: Type,\ [\operatorname{AddMonoid}(M)] [\operatorname{TopologicalSpace}(X)] [\operatorname{TopologicalSpace}(Y)] [\operatorname{AddAction}(M, X)] [\operatorname{AddAction}(M, Y)] [\operatorname{AddActionIsMinimal}(M, X)] f: X \to Y, hf: \operatorname{Continuous}(f), hsurj: \operatorname{Surjective}(f), hequiv: \forall m: M, \forall x: X, f(vadd(m, x))=vadd(m, f(x))\Rightarrow \operatorname{AddActionIsMinimal}(M, Y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/TopologicalFactorMinimality.continuous_surjective_equivariant_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous surjective map intertwining two additive monoid actions carries every dense source orbit onto a dense target orbit. The proof uses only continuity, surjectivity, and the equivariance identity; no compactness or separation assumptions are required.

For a target point choose a source preimage. A second target point is the continuous image of a point in the closure of the source orbit. Equivariance maps each source orbit element into the target orbit, so `map_mem_closure` gives the result.

**Theorem 1.2 (A continuous semiconjugate factor preserves forward-orbit minimality).**

$$\forall X: Type, \forall Y: Type,\ [\operatorname{TopologicalSpace}(X)] [\operatorname{TopologicalSpace}(Y)],\ f: X \to X, g: Y \to Y, factor: X \to Y, hfactor: \operatorname{Continuous}(factor), hsurj: \operatorname{Surjective}(factor), hsemiconj: \operatorname{Semiconj}(factor, f, g), hminimal: \forall x: X, \operatorname{Dense}(\operatorname{Setrange}((n\in \mathbb{N} \mapsto f^n(x))))\Rightarrow \forall y: Y, \operatorname{Dense}(\operatorname{Setrange}((n\in \mathbb{N} \mapsto g^n(y)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/TopologicalFactorMinimality.dense_forward_orbit_of_continuous_surjective_semiconj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same closure argument is stated directly for iterates of two self-maps. A continuous surjective semiconjugacy sends each iterated source orbit into the corresponding target orbit.

This form applies to symbolic observation factors and provides the bridge from symbolic dynamics to topological dynamics without choosing a particular alphabet or metric.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/TopologicalFactorMinimality.continuous_surjective_equivariant_minimality`
- Truth anchor: `D5/S3/Observer/Dynamics/TopologicalFactorMinimality.dense_forward_orbit_of_continuous_surjective_semiconj`
