# Lawvere Escape

## Abstract

A fixed-point-free twist escapes every listing, with no finiteness hypothesis.

The self-application fragment reads a listing as a map sending each address to a function on addresses, applies a twist to the values sitting on the diagonal, and calls the listing escaped when the resulting function is absent from its range.

The qualitative half of Lawvere's fixed-point theorem is that a twist without a fixed point escapes every listing. The repository already reached that conclusion by counting, which needs both the address set and the alphabet to be finite. The argument below needs neither: a row that equals the twisted diagonal exhibits a fixed point at its own address, so no row can equal it.

The hypothesis is not decorative. On the two-symbol alphabet the identity twist fixes every point, and the constant listing at a single address is then captured rather than escaped, so the implication cannot be strengthened by dropping its premise.

**Theorem 1.1 (A fixed-point-free twist escapes every listing).**

$$\left(\forall y \in Y,\; \operatorname{f}\left(y\right) \ne y\right) \Rightarrow \operatorname{IsEscaped}\left(f, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/QualitativeEscape.escaped_of_fixedPointFree` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

Suppose the twisted diagonal lies in the range of the listing, say as the row at some address. Evaluating that equality at the address itself makes the twist fix the diagonal entry there, contradicting the hypothesis. No finiteness is used.

**Lemma 1.2 (A twist with a fixed point captures a listing).**

$$\exists f \in \mathit{Y0}, g \in \mathit{L0},\; \neg \operatorname{IsEscaped}\left(f, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/QualitativeEscape.exists_captured_listing_of_fixedPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity twist on the two-symbol alphabet together with the constant listing at a one-point address set is captured, which shows the fixed-point-free premise carries weight.

**Lemma 1.3 (Escape is attained on a two-symbol alphabet).**

$$\operatorname{IsEscaped}\left(f, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/QualitativeEscape.not_escaped_isEscaped_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negation twist has no fixed point, so the constant listing on a one-point address set is escaped. Escape is therefore attained and the universal statement is not vacuous for want of listings.

**Theorem 1.4 (The self-application fragment packaged).**

$$\left(\left(\forall y \in Y,\; \operatorname{f}\left(y\right) \ne y\right) \Rightarrow \operatorname{IsEscaped}\left(f, g\right)\right) \land \left(\exists f \in \mathit{Y0}, g \in \mathit{L0},\; \neg \operatorname{IsEscaped}\left(f, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/QualitativeEscape.self_application_fragment_package` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

One conjunction carrying the fragment: the diagonal construction is pointwise the twist applied to the diagonal entries, escape is exactly absence of that diagonal from the range, a fixed-point-free twist escapes every listing, and the premise cannot be dropped.

## References

- Truth anchor: `D5/S0/Diagonal/Lawvere/QualitativeEscape.escaped_of_fixedPointFree`
- Truth anchor: `D5/S0/Diagonal/Lawvere/QualitativeEscape.exists_captured_listing_of_fixedPoint`
- Truth anchor: `D5/S0/Diagonal/Lawvere/QualitativeEscape.not_escaped_isEscaped_witness`
- Truth anchor: `D5/S0/Diagonal/Lawvere/QualitativeEscape.self_application_fragment_package`
- Dependency: [D5/S0/Diagonal/EscapeCount](../EscapeCount.md)
