# Four Fates of Self-Application

## Abstract

Every non-degenerate binary fractional self-map has exactly one of four fates, with the live fate characterizing the golden family.

A binary fractional map is classified as empty, dead, collapsed, or live by the coefficients and discriminant of its fixed-point polynomial. For every non-degenerate map exactly one classification holds.

**Theorem 1.1 (Non-degenerate self-application has exactly one fate).**

$$\forall m,\ \operatorname{Nondegenerate}(m) \Rightarrow (\exists! fate,\ \operatorname{HasFate}(m,fate)) \land (\operatorname{HasFate}(m,\mathrm{live}) \Leftrightarrow \operatorname{IsPhiFamily}(m)) \land (\operatorname{HasFate}(m,\mathrm{live}) \Rightarrow \operatorname{fixedCoefficients}(m)\in\{(1,-1,-1), (1,1,-1)\}) \land (\operatorname{HasFate}(m,\mathrm{live}) \Rightarrow \operatorname{discriminant}(m)=1^2+4=5)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/SelfApplicationFates.self_application_four_fates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The live cases are precisely the two golden-family maps, whose fixed-point coefficient triples are (1, -1, -1) and (1, 1, -1). In either case the discriminant is 1 squared plus 4, hence exactly 5.

## References

- Truth anchor: `D5/S0/Diagonal/SelfApplicationFates.self_application_four_fates`
