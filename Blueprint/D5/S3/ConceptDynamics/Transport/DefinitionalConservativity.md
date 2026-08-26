# Definitional Conservativity

## Abstract

Definitional extensions obtained by expanding every axiom and rule are conservative on the old language.

**Theorem 1.1 (Definitional conservativity).**

$$\begin{gathered}\forall B, E: \operatorname{Type}, \\{}C: \operatorname{Calculus}(B), e: E \to B, i: B \to E,\\{}{(\forall phi: B, e(i(phi)) = phi)},\\{}phi: B,\\{}(\operatorname{Derivation}(\operatorname{pullbackCalculus}(C, e), \operatorname{i}(phi))) \Rightarrow \operatorname{Derivation}(C, phi).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/DefinitionalConservativity.definitional_conservativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A calculus consists of an axiom predicate and a rule predicate on finite lists of premises. The extension calculus is constructed by applying the source expansion map to every axiom, premise, and conclusion; it introduces no independent axiom or rule.

The old-language embedding is required to be a section of expansion. Induction on an extended derivation then yields a base derivation of the expanded conclusion, and the section law identifies that conclusion with the original old-language sentence.

This is the source's definitional-extension conservativity clause: every old-language sentence derivable in the expansion-only calculus was already derivable in the base calculus.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/DefinitionalConservativity.definitional_conservativity`
