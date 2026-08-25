# Complement Selector Diagonal

## Abstract

Pointwise avoidance supplies the twist required for diagonal escape.

**Theorem 1.1 (Avoidance selection produces diagonal escape).**

$$\begin{gathered}\forall selector: \operatorname{AvoidanceSelector}\left(Output\right),\\{}catalog: Address \to Address \to Output,\\{}\operatorname{IsEscaped}\left(\operatorname{choose}\left(selector\right), catalog\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/ComplementSelectorDiagonal.avoidanceSelector_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The catalog assigns an output to every address pair. Self-evaluation reads the diagonal value at an address, and the selector replaces that value by a distinct output.

The selector's avoidance field supplies fixed-point-freedom for its choice function. The repository's qualitative Lawvere theorem then turns that pointwise inequality into escape from every catalog diagonal entry.

No surjectivity, enumeration, or finiteness premise is used; the claim depends only on the explicitly typed catalog and the supplied avoidance-selector structure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/ComplementSelectorDiagonal.avoidanceSelector_diagonal_escape`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](../../../S0/Diagonal/Lawvere/QualitativeEscape.md)
- Dependency: [D5/S3/ConceptDynamics/Negation/InvolutiveNegation](InvolutiveNegation.md)
