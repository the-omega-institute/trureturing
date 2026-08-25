# Noninterference Excludes Secret Flow

## Abstract

Deterministic noninterference excludes secret-dependent changes in the public output of a program flow.

**Theorem 1.1 (Secret differences cannot change the public output under noninterference).**

$$\begin{aligned}\forall X, L, H, Y, B: \operatorname{Type},\\l: X \to L, h: X \to H,\\F: X \to Y, O: Y \to B,\\\operatorname{Refines}\left(O \circ F, l\right) \Rightarrow \neg (\exists x, y: X, l\left(x\right) = l\left(y\right) \land \neg h\left(x\right) = h\left(y\right) \land \neg O\left(F\left(x\right)\right) = O\left(F\left(y\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion.noninterference_secret_flow_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Noninterference makes the public output after the program flow a postprocessing of the low-security input. Equal low inputs therefore force equal public outputs.

A forbidden witness would have equal low inputs and unequal public outputs, alongside the source's explicit unequal-secret clause. Applying noninterference to its low-input equality contradicts the output inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion.noninterference_secret_flow_exclusion`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
