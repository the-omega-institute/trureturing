# RewFour

## Abstract

Seven general lawful syntactic-rewriting identities from the licensed Foundation source.

This document mirrors the seven retained theorems in the capacity span Foundation/Syntax/Predicate/Rew.lean:954-1080 at revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. They express identities between rewriting operations on an abstract family of formulas.

All seven statements assume a language L, a family S : Nat -> Type, LCWQ S, SyntacticRewriting L S S and LawfulSyntacticRewriting L S. S(n) has n available bound-variable indices; free variables are labelled by natural numbers. S(0) can still contain free variables. A SyntacticTerm(L) has no bound variables and may contain natural-number-labelled free variables.

In the formulas, act(w, phi) is the formula action w ▹ phi, apply(w, t) is the term action w t, and rewrite(f) is Rew.rewrite f. bShift and shiftTerm are Rew.bShift and Rew.shift on terms. shift and free are Rewriting.shift and Rewriting.free on formulas. fvar(i) is &i. cons(t, g) maps 0 to t and i+1 to g(i); compose(g, f) maps i to g(f(i)). subst(phi, t) means phi/[t]. cast(phi) means Rewriting.subst phi ![] with source S(0) and target S(1); it adds an unused bound-variable slot. The free operation replaces the sole available bound variable by &0 and shifts the old free-variable labels.

**Lemma 1.1 (Freeing the bound slot transports a lifted rewrite).**

$$\forall f: \mathbb{N} \to \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(1\right), \operatorname{free}\left(\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{compose}\left(bShift, f\right)\right), phi\right)\right) = \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{cons}\left(\operatorname{fvar}\left(0\right), \operatorname{compose}\left(shiftTerm, f\right)\right)\right), \operatorname{free}\left(phi\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_rewrite_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Lift each replacement term with bShift before rewriting a formula in S(1). Freeing its bound slot then agrees with first freeing the formula and rewriting with a map that fixes &0 and shifts every original replacement term.

**Lemma 1.2 (Shifting a rewritten formula transports the replacement map).**

$$\forall f: \mathbb{N} \to \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(0\right), \operatorname{shift}\left(\operatorname{act}\left(\operatorname{rewrite}\left(f\right), phi\right)\right) = \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{cons}\left(\operatorname{fvar}\left(0\right), \operatorname{compose}\left(shiftTerm, f\right)\right)\right), \operatorname{shift}\left(phi\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.shift_rewrite_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For a formula in S(0), shifting after rewriting equals rewriting the shifted formula with &0 prepended to the map of shifted replacement terms.

**Lemma 1.3 (Rewriting a substitution rewrites both the formula and the substituted term).**

$$\forall f: \mathbb{N} \to \operatorname{SyntacticTerm}\left(L\right), t: \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(1\right), \operatorname{act}\left(\operatorname{rewrite}\left(f\right), \operatorname{subst}\left(phi, t\right)\right) = \operatorname{subst}\left(\operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{compose}\left(bShift, f\right)\right), phi\right), \operatorname{apply}\left(\operatorname{rewrite}\left(f\right), t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For phi in S(1) and t a syntactic term, rewrite phi/[t] by f. The same result is obtained by rewriting phi with bShift composed with f, and then substituting the term produced by rewriting t with f.

**Lemma 1.4 (Freeing an unused bound slot shifts the free variables).**

$$\forall phi: \operatorname{S}\left(0\right), \operatorname{free}\left(\operatorname{cast}\left(phi\right)\right) = \operatorname{shift}\left(phi\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_subst_nil` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The cast from S(0) to S(1) introduces no occurrence of its new bound variable. Applying free to that cast therefore has exactly the effect of shift.

**Lemma 1.5 (A lifted rewrite commutes with adding an unused bound slot).**

$$\forall f: \mathbb{N} \to \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(0\right), \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{compose}\left(bShift, f\right)\right), \operatorname{cast}\left(phi\right)\right) = \operatorname{cast}\left(\operatorname{act}\left(\operatorname{rewrite}\left(f\right), phi\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_nil` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Rewriting cast(phi) with bShift composed with f agrees with casting the result of rewriting phi with f.

**Lemma 1.6 (Substituting into an unused bound slot recovers the original formula).**

$$\forall t: \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(0\right), \operatorname{subst}\left(\operatorname{cast}\left(phi\right), t\right) = phi.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.cast_subst_eq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every syntactic term t, substituting t into cast(phi) returns phi. The cast has no occurrence of the added bound variable to replace.

**Lemma 1.7 (Substitution can be expressed by freeing and then rewriting).**

$$\forall t: \operatorname{SyntacticTerm}\left(L\right), phi: \operatorname{S}\left(1\right), \operatorname{act}\left(\operatorname{rewrite}\left(\operatorname{cons}\left(t, fvar\right)\right), \operatorname{free}\left(phi\right)\right) = \operatorname{subst}\left(phi, t\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_free_eq_subst` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

After freeing phi, send &0 to t and each &(i+1) back to &i. This rewrite agrees with directly substituting t for the bound slot in phi.

Each declaration retains its upstream name, hypotheses and proof body. The source map, modification notices, Apache-2.0 license and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

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
