# Target-Relative Pair Universe

## Abstract

Target identification requires separating exactly the unordered model pairs on which the target values differ.

**Theorem 1.1 (Target identifiability is coverage of target-disagreement pairs).**

$$\begin{aligned}\forall I, R, Y: \operatorname{Type},\\r: I \to \operatorname{Fin}(n) \to R, T: \operatorname{Fin}(n) \to Y,\\(\forall i, j: \operatorname{Fin}(n), T(i) \neq T(j) \Rightarrow \exists a: I, r(a)(i) \neq r(a)(j))\\\iff \{\{i, j\} \mid T(i) \neq T(j)\} \subseteq \operatorname{Union}\left(a, \{\{i, j\} \mid r(a)(i) \neq r(a)(j)\}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse.target_relative_pair_universe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The required universe is constructed canonically on Sym2(Fin n): it contains precisely the unordered pairs of models whose target values differ. Pairs with equal target values impose no identification requirement.

Each intervention contributes the unordered pairs separated by its readout. The theorem states that every target-disagreement pair admits such an intervention exactly when the target-relative universe is covered by the union of these separation sets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse.target_relative_pair_universe`
