# No Terminal Self-Description

## Abstract

A terminal pro-object stage cannot contain its twisted self-evaluation concept.

**Theorem 1.1 (A twisted self-evaluation escapes every terminal-stage listing).**

$$\forall J, Y,\ [\operatorname{SmallCategory}\left(J\right)], [\operatorname{IsFiltered}\left(J\right)],\ X: \operatorname{Opposite}\left(J\right) \to \operatorname{Type}, i\in \operatorname{Opposite}\left(J\right),\ \operatorname{Presented}\left(X\right) \equiv \operatorname{Const}\left(\operatorname{Stage}\left(X, i\right)\right) \implies \forall e: \operatorname{Stage}\left(X, i\right) \to (\operatorname{Stage}\left(X, i\right) \to Y), tau: Y \to Y,\ (\forall y, tau(y) \neq y) \implies \neg ((x \mapsto tau(e(x)(x))) \in \operatorname{range}\left(e\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ProObjects/NoTerminalSelfDescription.no_terminal_self_description` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a cofiltered stage diagram and let stage i faithfully represent its whole pro-object through the displayed isomorphism with the constant object on X_i.

A listing e assigns to every stage coordinate a same-typed concept from X_i to Y. Its self-evaluation is formed at x by evaluating the x-th listed concept at x and then applying tau.

When tau has no fixed point, this explicit concept is outside the range of e. Thus the listing cannot contain every same-typed concept, even under the terminal faithful-stage claim.

The exact repository theorem relative_diagonal_escape proves the range exclusion directly; the canonical pro-object constructions are imported rather than redeclared.

## References

- Truth anchor: `D5/S3/ObserverMemory/ProObjects/NoTerminalSelfDescription.no_terminal_self_description`
- Dependency: [D5/S0/Diagonal/Naturality/RelativeDiagonalEscape](../../../S0/Diagonal/Naturality/RelativeDiagonalEscape.md)
- Dependency: [D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry](ConceptAnchorHomAsymmetry.md)
