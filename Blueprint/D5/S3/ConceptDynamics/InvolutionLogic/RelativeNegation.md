# Relative Negation

## Abstract

For a proposition inside the old ambient, negation grows by the admitted region.

**Theorem 1.1 (An enlarged relative complement splits into old and new parts).**

$$\forall P, U0, U1: \operatorname{Set}\left(X\right), (P \subseteq U0 \land U0 \subseteq U1) \Rightarrow \operatorname{relativeNegation}\left(U1, P\right) = \operatorname{union}\left(\operatorname{relativeNegation}\left(U0, P\right), U1 \setminus U0\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.relative_complement_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the proposition lies in the old universe and the old universe lies in the new one.

Removing the proposition from the enlarged universe leaves the old relative complement together with the points newly admitted by the universe expansion.

The equality is conditional on both displayed inclusions; without them the decomposition is not asserted.

**Theorem 1.2 (The newly available negative region is exactly the universe difference).**

$$\forall P, U0, U1: \operatorname{Set}\left(X\right), (P \subseteq U0 \land U0 \subseteq U1) \Rightarrow \operatorname{relativeNegation}\left(U1, P\right) \setminus \operatorname{relativeNegation}\left(U0, P\right) = U1 \setminus U0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.relative_complement_new_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same two inclusions, subtracting the old relative complement from the new one removes every previously available negative point.

What remains is precisely the set difference between the new and old universes, with no additional proposition-dependent region.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.relative_complement_expansion`
- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.relative_complement_new_region`
