# RewFour

## Abstract

Seven lawful capture-avoiding rewriting and substitution identities over arbitrary signatures.

Throughout, L is an arbitrary first-order signature and S is a family indexed by natural numbers, with LCWQ S, SyntacticRewriting L S S and LawfulSyntacticRewriting L S. The map f sends natural-number free variables to syntactic terms over L. In the formulas, act is the rewriting action, lift sends x to bShift(f(x)), extend sends zero to the free variable zero and successor x to shift(f(x)), and insert sends zero to t and successor x to the free variable x. The operation cast substitutes the empty vector into an element of S(0); single denotes substitution of one term.

**Lemma 1.1 (Freeing commutes with lifted rewriting).**

$$\operatorname{free}\left(\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{lift}\left(f\right)\right), \mathit{phi}\right)\right) = \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{extend}\left(f\right)\right), \operatorname{free}\left(\mathit{phi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_rewrite_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every phi in S(1), freeing after rewriting with the bound-variable lift agrees with rewriting the freed expression by extend(f).

**Lemma 1.2 (Shifting commutes with rewriting).**

$$\operatorname{shift}\left(\operatorname{act}\left(\operatorname{rewrite}\left(f\right), \mathit{phi}\right)\right) = \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{extend}\left(f\right)\right), \operatorname{shift}\left(\mathit{phi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.shift_rewrite_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every phi in S(0), shifting after rewriting agrees with rewriting the shifted expression by extend(f).

**Lemma 1.3 (Rewriting commutes with single substitution).**

$$\operatorname{act}\left(\operatorname{rewrite}\left(f\right), \operatorname{single}\left(\mathit{phi}, t\right)\right) = \operatorname{single}\left(\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{lift}\left(f\right)\right), \mathit{phi}\right), \operatorname{rewriteTerm}\left(f, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every syntactic term t and phi in S(1), rewriting a substitution agrees with lifted rewriting followed by substitution of the rewritten term.

**Lemma 1.4 (Freeing an empty substitution shifts).**

$$\operatorname{free}\left(\operatorname{cast}\left(\mathit{phi}\right)\right) = \operatorname{shift}\left(\mathit{phi}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_subst_nil` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every phi in S(0), freeing its empty-vector substitution equals its shift.

**Lemma 1.5 (Lifted rewriting preserves the empty substitution).**

$$\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{lift}\left(f\right)\right), \operatorname{cast}\left(\mathit{phi}\right)\right) = \operatorname{cast}\left(\operatorname{act}\left(\operatorname{rewrite}\left(f\right), \mathit{phi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_nil` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every phi in S(0), lifted rewriting of the empty-vector substitution equals the empty-vector substitution after rewriting.

**Lemma 1.6 (Single substitution cancels an empty-vector cast).**

$$\operatorname{single}\left(\operatorname{cast}\left(\mathit{phi}\right), t\right) = \mathit{phi}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.cast_subst_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every syntactic term t and phi in S(0), substituting t after the empty-vector cast returns phi.

**Lemma 1.7 (Rewriting a freed expression realizes substitution).**

$$\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{insert}\left(t\right)\right), \operatorname{free}\left(\mathit{phi}\right)\right) = \operatorname{single}\left(\mathit{phi}, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_free_eq_subst` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every syntactic term t and phi in S(1), rewriting free(phi) by insert(t) equals single substitution of t into phi.

These are retained prerequisite APIs for first-order finite derivations. They do not establish the complete CSA defining graphs, definition elimination, ZFC conservativity or model existence.

The seven mathematical commands are retained from Foundation/Syntax/Predicate/Rew.lean, lines 955-989 within capacity span 954-1080, at revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, modification notices, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md. Compiler companions are not independently authored theorems.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.cast_subst_eq`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_rewrite_eq`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_subst_nil`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_free_eq_subst`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_eq`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_nil`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.shift_rewrite_eq`
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Quantifier](../ZfcPredicate/Quantifier.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Term](../ZfcPredicate/Term.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcSupport/Function](../ZfcSupport/Function.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree](RewThree.md)
