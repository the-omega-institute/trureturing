# Finite Information-Escape Arenas

## Abstract

Finite arenas keep construction separate from the seal's nondegeneracy check.

**Definition 1.1 (Finite arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/Arena.Arena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Arena.Arena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arena packages a state type, its finite enumeration, and decidable equality.

**Definition 1.2 (Arena cardinality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/Arena.card`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Arena.card` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena cardinality is computed from its stored finite enumeration.

**Definition 1.3 (Arena nondegeneracy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/Arena.Nondegenerate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Arena.Nondegenerate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nondegeneracy is the separately decidable requirement that the state cardinality is at least two.

**Definition 1.4 (Arena from a finite type).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/Arena.ofFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Arena.ofFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any type with finite enumeration and decidable equality can be packaged as an arena.

**Theorem 1.5 (A nondegenerate arena has distinct states).**

$$\operatorname{Nondegenerate}(arena) \Rightarrow \exists x, y: \operatorname{State}(arena), x \neq y.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Arena.exists_ne_of_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinal lower bound converts to the standard finite-type distinct-pair witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Arena.Arena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Arena.Nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Arena.card`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Arena.exists_ne_of_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Arena.ofFintype`
