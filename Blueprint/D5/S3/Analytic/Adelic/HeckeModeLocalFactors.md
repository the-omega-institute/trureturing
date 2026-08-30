# Hecke Mode Local Factors

## Abstract

Split primes alone carry the regulator-mode dependence of the golden local factors.

**Theorem 1.1 (Split, inert, and ramified local factors).**

$$\forall mode1 \in \operatorname{Int}(), mode2 \in \operatorname{Int}(), s \in \mathbb{C}, p \in \operatorname{Nat}(), theta \in \operatorname{Real}(),\; \operatorname{Prime}(p) \Rightarrow \left(\left(\operatorname{legendreSym}(5, p) = 1 \Rightarrow \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode1, s) = (1 - 2 \times \operatorname{cos}(mode1 \times theta) \times p^{{-s}} + p^{{-(2 \times s)}})^{-1}\right) \land \left(\left(\operatorname{legendreSym}(5, p) = -1 \Rightarrow \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode1, s) = (1 - p^{{-(2 \times s)}})^{-1}\right) \land \left(\left(\operatorname{legendreSym}(5, p) = -1 \Rightarrow \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode1, s) = \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode2, s)\right) \land \left(\operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(5, theta), mode1, s) = (1 - 5^{{-s}})^{-1} \land \left(\operatorname{det}(\operatorname{goldenLocalBranchOperator}(p)) \ne 1 \Rightarrow \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode1, s) = \operatorname{localHeckeEulerFactor}(\operatorname{goldenLocalPrimePlaces}(p, theta), mode2, s)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/HeckeModeLocalFactors.hecke_mode_local_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A local factor is constructed from its prime-ideal place data. Each place contributes its norm and regulator phase to one Euler factor, and the contributions are multiplied.

The canonical quadratic character selects two conjugate norm-p places on the split branch, one zero-phase norm-p-squared place on the inert branch, and one zero-phase norm-p place on the ramified branch.

Multiplying the conjugate split factors gives the cosine denominator. The zero phases make the inert and ramified factors independent of the mode. The canonical local branch operator then confines all possible mode dependence to its determinant-one branch.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/HeckeModeLocalFactors.hecke_mode_local_factors`
- Dependency: [D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification](../../PrimeForms/Splitting/GoldenLocalBranchClassification.md)
