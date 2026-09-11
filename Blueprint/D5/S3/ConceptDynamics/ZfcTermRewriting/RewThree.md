# RewThree

## Abstract

Licensed Foundation.Syntax.Predicate.Rew source selected from the historical first-order pair extension.

This document mirrors the retained declarations from Foundation.Syntax.Predicate.Rew, lines 638-953, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. The excerpt records the term-rewriting laws and interfaces associated with the concrete first-order pair extension; current downstream consumer usage has not been re-queried.

The immutable source map, modification notices, full Apache-2.0 license and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

**Lemma 1.1 (Fixing bound variables preserves the variable with an enlarged finite index).**

$$\forall n, m, x\in \operatorname{Fin}\left(n\right), \operatorname{fixitr}\left(n, m, \operatorname{bvar}\left(x\right)\right) = \operatorname{bvar}\left(\operatorname{castAdd}\left(x, m\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_bvar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite bound index x, fixing m variables maps the bound variable to its castAdd representative in the enlarged context.

**Lemma 1.2 (Fixing free variables either binds or shifts them).**

$$\forall n, m, x\in \mathbb{N}, \operatorname{fixitr}\left(n, m, \operatorname{fvar}\left(x\right)\right) = \operatorname{if}\left(\operatorname{lt}\left(x, m\right), \operatorname{bvar}\left(\operatorname{natAdd}\left(n, \operatorname{pair}\left(x, \operatorname{proof}\left(x, m\right)\right)\right)\right), \operatorname{fvar}\left(x - m\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_fvar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A free variable below the fixed prefix becomes a bound variable; otherwise its index is decreased by the prefix length.

**Lemma 1.3 (Rewrites agree when they agree on the variables visible in a term).**

$$\forall omega1, omega2, t (\operatorname{agreeBvar}\left(omega1, omega2\right) \land \operatorname{agreeOn}\left(\operatorname{fvarSupport}\left(t\right), omega1, omega2\right)) \Rightarrow \operatorname{eq}\left(\operatorname{apply}\left(omega1, t\right), \operatorname{apply}\left(omega2, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.rew_eq_of_funEqOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement on every bound variable and on the free variables occurring in the term is sufficient for equality after rewriting that term.

**Lemma 1.4 (Language maps commute with term binding).**

$$\forall phi, b, e, t \operatorname{lMap}\left(phi, \operatorname{bind}\left(b, e, t\right)\right) = \operatorname{bind}\left(\operatorname{compose}\left(\operatorname{lMap}\left(phi\right), b\right), \operatorname{compose}\left(\operatorname{lMap}\left(phi\right), e\right), \operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping function symbols through a language homomorphism commutes with binding both bound and free variables.

**Lemma 1.5 (Language maps commute with variable maps).**

$$\forall phi, b, e, t \operatorname{lMap}\left(phi, \operatorname{map}\left(b, e, t\right)\right) = \operatorname{map}\left(b, e, \operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map that changes variable indices and free-variable labels commutes with the language map on terms.

**Lemma 1.6 (Language maps commute with bound-variable shifting).**

$$\forall phi, t \operatorname{lMap}\left(phi, \operatorname{bShift}\left(t\right)\right) = \operatorname{bShift}\left(\operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one bound-variable slot before or after a language map gives the same term.

**Lemma 1.7 (A free variable after rewriting comes from a source variable (the canonical selector is RewThreeCompat.fvar_rew; the source name is fvar?_rew).).**

$$\forall omega, t, x \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, t\right), x\right) \Rightarrow (\exists i, \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, \operatorname{bvar}\left(i\right)\right), x\right) \lor \exists z, (\operatorname{contains}\left(\operatorname{fvarSupport}\left(t\right), z\right) \land \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, \operatorname{fvar}\left(z\right)\right), x\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_rew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a free variable occurs in a rewritten term, it came either from a rewritten bound variable or from a free variable of the source term.

**Lemma 1.8 (Bound-variable shifting preserves free-variable support (the canonical selector is RewThreeCompat.fvar_bShift; the source name is fvar?_bShift).).**

$$\forall t, x \operatorname{fvarAt}\left(\operatorname{bShift}\left(t\right), x\right) \Leftrightarrow \operatorname{fvarAt}\left(t, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bShift operation changes only bound indices, so the set of free variables is unchanged.

**Definition 1.9 (A term with no free variables is converted to an empty-variable term).**

$$\forall t \operatorname{freeVariables}\left(t\right) = \emptyset \Rightarrow \operatorname{toEmpty}\left(t\right) \in \operatorname{ClosedSemiterm}\left(\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.toEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A closed semiterm is recursively retyped as a ClosedSemiterm; the free-variable case is impossible under the empty support hypothesis.

**Lemma 1.10 (Embedding the empty-variable form recovers the original term).**

$$\forall t \operatorname{freeVariables}\left(t\right) = \emptyset \Rightarrow \operatorname{emb}\left(\operatorname{toEmpty}\left(t\right)\right) = t.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.emb_toEmpty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the term produced by toEmpty is definitionally equal to the original term.

**Definition 1.11 (A rewriting action applies rewrites to formulas and respects quantifiers).**

$$\operatorname{Rewriting}\left(L, xi, F, zeta, G\right) = \operatorname{app}\left(\operatorname{Rew}\left(L, xi, n1, zeta, n2\right), \operatorname{F}\left(n1\right)\right) \land \operatorname{app}\left(omega, \operatorname{forall}\left(phi\right)\right) = \operatorname{forall}\left(\operatorname{app}\left(\operatorname{q}\left(omega\right), phi\right)\right) \land \operatorname{app}\left(omega, \operatorname{exists}\left(phi\right)\right) = \operatorname{exists}\left(\operatorname{app}\left(\operatorname{q}\left(omega\right), phi\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.Rewriting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Rewriting instance supplies an action of term rewrites on formulas, with universal and existential quantification transported through the rewrite.

**Definition 1.12 (The identity rewrite acts as the identity on formulas).**

$$\forall phi \operatorname{app}\left(\operatorname{id}\left(L\right), phi\right) = phi.$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.ReflectiveRewriting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflectivity records that applying Rew.id leaves every formula unchanged.

**Definition 1.13 (Composed rewrites act by successive formula application).**

$$\forall omega12, omega23, phi \operatorname{app}\left(\operatorname{comp}\left(omega23, omega12\right), phi\right) = \operatorname{app}\left(omega23, \operatorname{app}\left(omega12, phi\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.TransitiveRewriting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transitivity identifies application of a composed rewrite with applying the first rewrite and then the second.

**Definition 1.14 (Injective variable and label maps induce an injective formula action).**

$$\forall b, f (\operatorname{Injective}\left(b\right) \land \operatorname{Injective}\left(f\right)) \Rightarrow \operatorname{Injective}\left(\operatorname{mapAction}\left(b, f\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.InjMapRewriting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If both the bound-variable map and free-variable map are injective, the induced map on formulas is injective.

**Definition 1.15 (Lawful syntactic rewriting combines identity, composition and injectivity).**

$$\operatorname{LawfulSyntacticRewriting}\left(L, S\right) = \operatorname{ReflectiveRewriting}\left(L, S\right) \land \operatorname{TransitiveRewriting}\left(L, S\right) \land \operatorname{InjMapRewriting}\left(L, S\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.LawfulSyntacticRewriting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lawful syntactic interface packages reflective, transitive and injective rewriting for the same syntactic formula family.

**Lemma 1.16 (Shifting a conjunction shifts each formula (the canonical selector is RewThreeCompat.shift_conj_two; the source name is shift_conj₂).).**

$$\forall gamma \operatorname{shift}\left(\operatorname{conj}\left(gamma\right)\right) = \operatorname{conj}\left(\operatorname{map}\left(\operatorname{shift}\left(\right), gamma\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shift_conj_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift of a finite conjunction is the conjunction of the shifted list, including the empty and singleton cases.

**Lemma 1.17 (Substituting the first free variable after shifting is free).**

$$\forall phi: \operatorname{S}\left(1\right), \operatorname{subst}\left(\operatorname{shift}\left(phi\right), \operatorname{fvar}\left(0\right)\right) = \operatorname{free}\left(phi\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a one-variable formula, shifting and substituting the zero free variable agrees with the free operation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.InjMapRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.LawfulSyntacticRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.ReflectiveRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.Rewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.TransitiveRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.emb_toEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_bvar`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_fvar`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bShift`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bind`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_map`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.rew_eq_of_funEqOn`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.toEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_rew`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shift_conj_two`
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Quantifier](../ZfcPredicate/Quantifier.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Term](../ZfcPredicate/Term.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcSupport/Function](../ZfcSupport/Function.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo](RewTwo.md)
