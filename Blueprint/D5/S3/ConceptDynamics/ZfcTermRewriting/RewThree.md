# RewThree

## Abstract

Licensed Foundation.Syntax.Predicate.Rew source selected from the historical first-order pair extension.

This document mirrors the retained declarations from Foundation.Syntax.Predicate.Rew, lines 638-953, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. The excerpt records the term-rewriting laws and interfaces associated with the concrete first-order pair extension; current downstream consumer usage has not been re-queried.

The immutable source map, modification notices, full Apache-2.0 license and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

**Lemma 1.1 (Fixing bound variables preserves the variable with an enlarged finite index).**

$$\forall n, m, x\in \operatorname{Fin}\left(n\right), \operatorname{fixitr}\left(n, m, \operatorname{bvar}\left(x\right)\right) = \operatorname{bvar}\left(\operatorname{castAdd}\left(x, m\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_bvar` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every finite bound index x, fixing m variables maps the bound variable to its castAdd representative in the enlarged context.

**Lemma 1.2 (Fixing free variables either binds or shifts them).**

$$\forall n, m, x\in \mathbb{N}, \operatorname{fixitr}\left(n, m, \operatorname{fvar}\left(x\right)\right) = \operatorname{if}\left(\operatorname{lt}\left(x, m\right), \operatorname{bvar}\left(\operatorname{natAdd}\left(n, \operatorname{pair}\left(x, \operatorname{proof}\left(x, m\right)\right)\right)\right), \operatorname{fvar}\left(x - m\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_fvar` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

A free variable below the fixed prefix becomes a bound variable; otherwise its index is decreased by the prefix length.

**Lemma 1.3 (Rewrites agree when they agree on the variables visible in a term).**

$$\forall omega1, omega2, t (\operatorname{agreeBvar}\left(omega1, omega2\right) \land \operatorname{agreeOn}\left(\operatorname{fvarSupport}\left(t\right), omega1, omega2\right)) \Rightarrow \operatorname{eq}\left(\operatorname{apply}\left(omega1, t\right), \operatorname{apply}\left(omega2, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.rew_eq_of_funEqOn` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Agreement on every bound variable and on the free variables occurring in the term is sufficient for equality after rewriting that term.

**Lemma 1.4 (Language maps commute with term binding).**

$$\forall phi, b, e, t \operatorname{lMap}\left(phi, \operatorname{bind}\left(b, e, t\right)\right) = \operatorname{bind}\left(\operatorname{compose}\left(\operatorname{lMap}\left(phi\right), b\right), \operatorname{compose}\left(\operatorname{lMap}\left(phi\right), e\right), \operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bind` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Mapping function symbols through a language homomorphism commutes with binding both bound and free variables.

**Lemma 1.5 (Language maps commute with variable maps).**

$$\forall phi, b, e, t \operatorname{lMap}\left(phi, \operatorname{map}\left(b, e, t\right)\right) = \operatorname{map}\left(b, e, \operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_map` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The map that changes variable indices and free-variable labels commutes with the language map on terms.

**Lemma 1.6 (Language maps commute with bound-variable shifting).**

$$\forall phi, t \operatorname{lMap}\left(phi, \operatorname{bShift}\left(t\right)\right) = \operatorname{bShift}\left(\operatorname{lMap}\left(phi, t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bShift` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Adding one bound-variable slot before or after a language map gives the same term.

**Lemma 1.7 (A free variable after rewriting comes from a source variable (the canonical selector is RewThreeCompat.fvar_rew; the source name is fvar?_rew).).**

$$\forall omega, t, x \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, t\right), x\right) \Rightarrow ((\exists i: \operatorname{Fin}\left(n1\right), \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, \operatorname{bvar}\left(i\right)\right), x\right)) \lor (\exists z: xi1, (\operatorname{contains}\left(\operatorname{fvarSupport}\left(t\right), z\right) \land \operatorname{fvarAt}\left(\operatorname{apply}\left(omega, \operatorname{fvar}\left(z\right)\right), x\right)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_rew` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

If a free variable occurs in a rewritten term, it came either from a rewritten bound variable or from a free variable of the source term.

**Lemma 1.8 (Bound-variable shifting preserves free-variable support (the canonical selector is RewThreeCompat.fvar_bShift; the source name is fvar?_bShift).).**

$$\forall t, x \operatorname{fvarAt}\left(\operatorname{bShift}\left(t\right), x\right) \Leftrightarrow \operatorname{fvarAt}\left(t, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The bShift operation changes only bound indices, so the set of free variables is unchanged.

**Definition 1.9 (A term with no free variables is converted to an empty-variable term).**

$$\begin{aligned}toEmpty: \forall n: \mathbb{N}, \forall t: \operatorname{Semiterm}\left(L, xi, n\right), h: \operatorname{freeVariables}\left(t\right) = \emptyset \Rightarrow \operatorname{ClosedSemiterm}\left(L, n\right)\\\operatorname{toEmpty}\left(\operatorname{bvar}\left(x\right), h\right) = \operatorname{bvar}\left(x\right) \text{where} x: \operatorname{Fin}\left(n\right), h: \operatorname{freeVariables}\left(\operatorname{bvar}\left(x\right)\right) = \emptyset\\\operatorname{toEmpty}\left(\operatorname{fvar}\left(z\right), h\right) = \operatorname{impossible}\left(h\right) \text{where} h: \operatorname{freeVariables}\left(\operatorname{fvar}\left(z\right)\right) = \emptyset\\\operatorname{toEmpty}\left(\operatorname{func}\left(f, v\right), h\right) = \operatorname{func}\left(f, i \mapsto \operatorname{toEmpty}\left(\operatorname{at}\left(v, i\right), hi\right)\right) \text{where} \forall i: \operatorname{Fin}\left(k\right), hi: \operatorname{freeVariables}\left(\operatorname{at}\left(v, i\right)\right) = \emptyset\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.toEmpty` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The dependent definition recurses by cases: a bound variable is returned unchanged, a free-variable case is impossible from its empty-support proof, and a function node is rebuilt from recursively converted arguments, each carrying the empty-support proof derived from the parent.

**Lemma 1.10 (Embedding the empty-variable form recovers the original term).**

$$\forall t \operatorname{freeVariables}\left(t\right) = \emptyset \Rightarrow \operatorname{emb}\left(\operatorname{toEmpty}\left(t\right)\right) = t.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.emb_toEmpty` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The retained structural induction proves that embedding the term produced by toEmpty recovers the original term.

**Definition 1.11 (A rewriting action applies rewrites to formulas and respects quantifiers).**

$$\operatorname{Rewriting}\left(L, xi, F, zeta, G\right) = (app: \forall n1: \mathbb{N}, n2: \mathbb{N}, \operatorname{Rew}\left(L, xi, n1, zeta, n2\right) \to \operatorname{Hom}\left(\operatorname{F}\left(n1\right), \operatorname{G}\left(n2\right)\right), \forall n1: \mathbb{N}, n2: \mathbb{N}, omega12: \operatorname{Rew}\left(L, xi, n1, zeta, n2\right), phi: \operatorname{F}\left(n1+1\right), \operatorname{appAll}\left(omega12, phi\right): \operatorname{app}\left(omega12, \operatorname{forall1}\left(phi\right)\right) = \operatorname{forall1}\left(\operatorname{app}\left(\operatorname{q}\left(omega12\right), phi\right)\right) \land \operatorname{appExs}\left(omega12, phi\right): \operatorname{app}\left(omega12, \operatorname{exists1}\left(phi\right)\right) = \operatorname{exists1}\left(\operatorname{app}\left(\operatorname{q}\left(omega12\right), phi\right)\right)).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.Rewriting` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

A Rewriting instance supplies an action of term rewrites on formulas, with universal and existential quantification transported through the rewrite. The app field is indexed by both bound-variable sizes; app_all and app_exs each take φ:F(n1+1) and use the lifted rewrite q(ω):Rew(L,ξ,n1+1,ζ,n2+1).

**Definition 1.12 (Formula substitution is the substitution rewrite action).**

$$\forall n1: \mathbb{N}, n2: \mathbb{N}, phi: \operatorname{F}\left(n1\right), w: \operatorname{Fin}\left(n1\right) \to \operatorname{Semiterm}\left(L, xi, n2\right), \operatorname{subst}\left(phi, w\right) = \operatorname{app}\left(\operatorname{RewSubst}\left(w\right), phi\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.subst` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every indexed formula φ and substitution vector w:Fin(n1)→Semiterm(L,ξ,n2), the abbreviation subst(φ,w) is exactly app(Rew.subst(w),φ) through the Rewriting action.

**Definition 1.13 (Formula shift is the shift rewrite action).**

$$shift: \operatorname{Hom}\left(\operatorname{F}\left(n\right), \operatorname{F}\left(n\right)\right) = \operatorname{app}\left(RewShift\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shift` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The shift connective homomorphism applies Rew.shift to formulas while increasing free-variable indices.

**Definition 1.14 (Formula free operation removes the last bound-variable slot).**

$$free: \operatorname{Hom}\left(\operatorname{F}\left(n+1\right), \operatorname{F}\left(n\right)\right) = \operatorname{app}\left(RewFree\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.free` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The free connective homomorphism maps the last bound slot to free variable &0 and shifts each existing free variable &m to &(m+1), taking formulas from the n+1 bound-variable context to the n context.

**Definition 1.15 (Formula-list shift maps each member).**

$$shifts: \operatorname{List}\left(\operatorname{F}\left(n\right)\right) \to \operatorname{List}\left(\operatorname{F}\left(n\right)\right) = \operatorname{map}\left(shift\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shifts` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The shifts definition maps the shift homomorphism over a finite list of formulas.

**Lemma 1.16 (Shifting an empty formula list stays empty).**

$$\operatorname{shifts}\left([]\right) = [].$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_nil` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The ASCII compatibility selector forwards the source shifts_nil theorem, including its exact LCWQ and Rewriting assumptions.

**Lemma 1.17 (Shifting a cons list shifts its head and tail).**

$$\operatorname{shifts}\left(\operatorname{cons}\left(phi, Gamma\right)\right) = \operatorname{cons}\left(\operatorname{shift}\left(phi\right), \operatorname{shifts}\left(Gamma\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_cons` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The ASCII compatibility selector forwards the source shifts_cons theorem pointwise over the head and tail.

**Lemma 1.18 (Shifting a negated formula list commutes with negation).**

$$\operatorname{shifts}\left(\operatorname{negList}\left(Gamma\right)\right) = \operatorname{negList}\left(\operatorname{shifts}\left(Gamma\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_neg` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The ASCII compatibility selector forwards the source shifts_neg theorem for list negation.

**Definition 1.19 (Empty-label formulas embed as connective homomorphisms).**

$$emb: \operatorname{Hom}\left(\operatorname{O}\left(n\right), \operatorname{F}\left(n\right)\right) = \operatorname{app}\left(RewEmb\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.emb` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The ASCII compatibility selector exposes the source emb connective homomorphism from an empty-label family O to a ξ-labelled family F.

**Definition 1.20 (Slash syntax expands to formula substitution).**

$$\forall phi: \operatorname{S}\left(1\right), phi/[\operatorname{fvar}\left(0\right)] = \operatorname{subst}\left(phi, \operatorname{Matrix}.\operatorname{vecCons}(\operatorname{fvar}\left(0\right), \operatorname{Matrix}.\operatorname{vecEmpty})\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.substNotation` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The repository compatibility parser selector mirrors the source substNotation macro: φ/[w] expands to φ ⇜ ![w]. For the one-entry vector used below, ![&0] is Matrix.vecCons(fvar(0), Matrix.vecEmpty).

**Definition 1.21 (The identity rewrite acts as the identity on formulas).**

$$\forall phi \operatorname{app}\left(\operatorname{id}\left(L\right), phi\right) = phi.$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.ReflectiveRewriting` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Reflectivity records that applying Rew.id leaves every formula unchanged.

**Definition 1.22 (Composed rewrites act by successive formula application).**

$$\forall omega12, omega23, phi \operatorname{app}\left(\operatorname{comp}\left(omega23, omega12\right), phi\right) = \operatorname{app}\left(omega23, \operatorname{app}\left(omega12, phi\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.TransitiveRewriting` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Transitivity identifies application of a composed rewrite with applying the first rewrite and then the second.

**Definition 1.23 (Injective variable and label maps induce an injective formula action).**

$$\forall b, f (\operatorname{Injective}\left(b\right) \land \operatorname{Injective}\left(f\right)) \Rightarrow \operatorname{Injective}\left(\operatorname{mapAction}\left(b, f\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.InjMapRewriting` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

If both the bound-variable map and free-variable map are injective, the induced map on formulas is injective.

**Definition 1.24 (Lawful syntactic rewriting combines identity, composition and injectivity).**

$$\begin{aligned}\operatorname{LawfulSyntacticRewriting}\left(L, S\right) (L: Language, S: \mathbb{N} \to Type) [\operatorname{LCWQ}\left(S\right)] [\operatorname{SyntacticRewriting}\left(L, S, S\right)]\\\text{extends} (\operatorname{ReflectiveRewriting}\left(L, \mathbb{N}, S\right), \operatorname{TransitiveRewriting}\left(L, \mathbb{N}, S, \mathbb{N}, S, \mathbb{N}, S\right), \operatorname{InjMapRewriting}\left(L, \mathbb{N}, S, \mathbb{N}, S\right)).\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.LawfulSyntacticRewriting` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

With [LCWQ S] and [SyntacticRewriting L S S] as its parameters, the class extends ReflectiveRewriting L ℕ S, TransitiveRewriting L ℕ S ℕ S ℕ S, and InjMapRewriting L ℕ S ℕ S. These are inherited interfaces, not a proposition asserted by an equality.

**Lemma 1.25 (Shifting a conjunction shifts each formula (the canonical selector is RewThreeCompat.shift_conj_two; the source name is shift_conj₂).).**

$$\forall gamma \operatorname{shift}\left(\operatorname{conj}\left(gamma\right)\right) = \operatorname{conj}\left(\operatorname{map}\left(\operatorname{shift}\left(\right), gamma\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shift_conj_two` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

The shift of a finite conjunction is the conjunction of the shifted list, including the empty and singleton cases.

**Lemma 1.26 (Substituting the first free variable after shifting is free).**

$$[\operatorname{LCWQ}\left(S\right)] [\operatorname{SyntacticRewriting}\left(L, S, S\right)] [\operatorname{LawfulSyntacticRewriting}\left(L, S\right)] \Rightarrow \forall phi: \operatorname{S}\left(1\right), \operatorname{subst}\left(\operatorname{shift}\left(phi\right), \operatorname{Matrix}.\operatorname{vecCons}(\operatorname{fvar}\left(0\right), \operatorname{Matrix}.\operatorname{vecEmpty})\right) = \operatorname{free}\left(phi\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For a one-variable formula, shifting and substituting the zero free variable agrees with the free operation. The substitution vector is the explicit one-entry Matrix.vecCons(fvar(0), Matrix.vecEmpty), and the law is stated under the LCWQ, SyntacticRewriting, and LawfulSyntacticRewriting context.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.InjMapRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.LawfulSyntacticRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.ReflectiveRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.Rewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.TransitiveRewriting`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.emb_toEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_bvar`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_fvar`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.free`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bShift`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bind`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_map`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.rew_eq_of_funEqOn`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shift`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shifts`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.subst`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.toEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.emb`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_rew`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shift_conj_two`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_cons`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_neg`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_nil`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.substNotation`
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Quantifier](../ZfcPredicate/Quantifier.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcPredicate/Term](../ZfcPredicate/Term.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcSupport/Function](../ZfcSupport/Function.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo](RewTwo.md)
