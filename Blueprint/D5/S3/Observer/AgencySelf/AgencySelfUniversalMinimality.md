# Agency Self Universal Minimality

## Abstract

A sufficient history interface uniquely maps its effective image to the agency-self quotient.

**Theorem 1.1 (A sufficient interface has a unique agency-self factor).**

$$\begin{gathered}\forall H, I, O, R: Type,\\{}Gamma: H \to \left(I \to \operatorname{PMF}\left(O\right)\right), r: H \to R,\\{}F: R \to \left(I \to \operatorname{PMF}\left(O\right)\right),\\{}Gamma = F \circ r \Rightarrow\\{}\exists! rbar: \operatorname{range}\left(r\right) \to \operatorname{Quotient}\left(\operatorname{ker}\left(Gamma\right)\right), \forall h: H, \operatorname{class}\left(h\right) = \operatorname{rbar}\left(\operatorname{rangePoint}\left(\operatorname{r}\left(h\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencySelfUniversalMinimality.agency_self_universal_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the complete future-interaction profile is decoded from a history interface.

The interface then induces a factor from its realized range to histories quotiented by equality of complete interaction profiles.

The factor sends every realized interface value to the corresponding profile class and is unique with this property, including when the history type is empty.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/AgencySelfUniversalMinimality.agency_self_universal_minimality`
- Dependency: [D5/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality](../../ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality.md)
