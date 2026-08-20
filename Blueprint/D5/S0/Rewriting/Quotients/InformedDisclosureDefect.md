# Informed Disclosure Defect

## Abstract

A pair with identical disclosure and different consequences defeats every disclosure-only distinction and rules out full consequence recovery.

**Theorem 1.1 (A disclosure collision obstructs fully informed choice).**

$$\forall Z, B, Y, R: \operatorname{Type},\\D: Z \to B, K: Z \to Y,\\z, zprime: Z,\\D(z) = D(zprime) \land K(z) \neq K(zprime) \Rightarrow\\(\forall rule: B \to R, rule(D(z)) = rule(D(zprime))) \land\\\neg \exists recover: B \to Y, K = recover \circ D.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/InformedDisclosureDefect.informed_disclosure_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The premise supplies two decision situations with the same disclosed value and different true consequences. A disclosure-only rule is an arbitrary function on disclosed values, so congruence forces it to return the same decision on this pair.

Exact informedness in the source means a recovery function from the disclosure domain to the consequence domain. Such a function would send the equal disclosures to equal consequences, contradicting the witnessed consequence difference.

Pinned Mathlib's congrArg is applied directly for the decision clause. Searches found adjacent fiber-factorization machinery but no exact theorem combining this universal decision limitation with the negated recovery factorization.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/InformedDisclosureDefect.informed_disclosure_defect`
