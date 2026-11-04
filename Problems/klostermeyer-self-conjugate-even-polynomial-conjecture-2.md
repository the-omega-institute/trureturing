---
slug: klostermeyer-self-conjugate-even-polynomial-conjecture-2
bibkey: klostermeyer2026nullspace
doi: null
url: https://arxiv.org/html/2610.31475v1#Thmconj2
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/TranslationInvariantPolynomial.exists_comp_of_translation_invariant
---

# Self-conjugate even polynomial Conjecture 2

## Problem

The sole target is Section 2, Conjecture 2 of the versioned source identified
by the literature note, PDF page 4 immediately after Theorem 9:

> Let p(x) be an even polynomial over GF(2). Then p(x) is self-conjugate if and only if p(x)=x^{2^{k_1}}+x^{2^{k_2}}+...+x^{2^{k_m}}, where m is odd if x^0 is a term and m is even otherwise.

The source defines self-conjugacy by f(x)=f(x+1), as equality of formal
polynomials. For each of the six explicit conventional readings e of even,
let Domain(e,p) mean, respectively: every supported exponent is even; the
natural degree is even; the support cardinality is even; the constant
coefficient is zero; X divides p; or p(-X)=p(X). For each such e the complete
published assertion is
\[
 \forall p\in\mathbb F_2[X],\quad
 \operatorname{Domain}(e,p)\Longrightarrow
 \left[p(X+1)=p(X)\ \Longleftrightarrow\
 \exists m\in\mathbb N,\ k:\operatorname{Fin}(m)\to\mathbb N,
 \ p=\sum_{i\in\operatorname{Fin}(m)}X^{2^{k(i)}}
 \ \land\ \operatorname{SourceParity}(p,m)\right],
\]
where SourceParity(p,m) is the conjunction of the implications from nonzero
constant coefficient to odd m and from zero constant coefficient to even m.
The indices may repeat; m=0 and k(i)=0 remain allowed. The optional-constant
variant separately adds an arbitrary c in the same field as C(c) to the sum.
It is robustness of the witnesses and does not repair the literal display.

The Lean claim is the existential disjunction, over these six readings, of
the complete published iff or its optional-constant counterpart. Thus its
literal negation refutes every complete published iff and every separately
labelled robustness counterpart. There is no auxiliary family condition in
the claim whose failure could stand in for a source refutation.

## Motivation

Translation-invariant polynomial algebra gives a direct way to test the
proposed sparse characterization. The existing classifier named in
motivation_gids supplies this mathematical context; it is not a proof
dependency of the direct family refutation. Its separate unfinished audit
#18608 is not asserted to be complete or inherited by this result.

## Gap

The source leaves even polynomial undefined and mentions a constant term
absent from its displayed sum. The family belongs simultaneously to the six
conventional domains and excludes even all sums with an arbitrary constant,
so neither ambiguity changes the obstruction within this stated scope. The
bounded primary-source, arXiv-author, Crossref, MathDB and repository review
in preregistration #21419 located no actual prior full answer. This is not a
global priority, ownership or exhaustive absence claim.

## Route

Let U=X^4+X^2 and P(r)=U^r. For every odd natural r at least three,
Frobenius gives U(X+1)=U(X), hence P(r)(X+1)=P(r)(X). Monicity gives nonzero
P(r) and exact degree 4r. Expanding (X^2+X)^r by two shows that every
supported exponent is even. Evaluation at zero gives zero constant
coefficient and divisibility by X. Evaluation at one gives zero; every
nonzero coefficient is one, so the support cardinality is even. Reflection
invariance follows from -X=X.

Odd r is coprime to every power of two. The equality 4r=2^k would make r
a divisor of a coprime number, forcing r=1, contrary to r at least three.
The coefficient of P(r) at exponent 4r is one, whereas the coefficient of
any finite powers-of-two sum with an arbitrary constant is zero there.
Consequently no such representation exists, for any c, m or k.

Each P(r) is therefore in every listed source domain and is self-conjugate,
but fails the necessary direction of each full iff. This refutes the
complete equivalence, including both parity branches, under every listed
reading. The uniform argument holds for all eligible r; r=3 is used only
to discharge existence in the final negation of claim. No new classification
of the sufficient direction is asserted.

## Falsifier

An actual previously published answer to the same full assertion would
invalidate new-resolution credit. An authoritative source restriction
excluding this family would change the target and require re-review. A
formal polynomial equality with one of the excluded representations would
contradict the leading-coefficient calculation. Equality merely as
functions on the two field elements is a different assertion.

## Evidence

The source is `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.lean`.
Its public result has literal type `Not claim`, where claim has literal
type Prop. The consumed private theorem family_event proves every clause
for every odd r at least three, and family_refutes_source applies the
necessary direction of the full universally quantified source iff to these
witnesses. The result permits only the standard propext, Classical.choice
and Quot.sound axiom closure. The Blueprint explains the full family,
source parity/index/constant wording and interpretation boundary.
The designated utility-refutation result is exempt from four-slot escape
registration; there is no other newly authored public theorem in this module.

## Triage

This is one Tier 1 recently posed named conjecture, preregistered in #21419.
Its admission basis is open-problem-resolution under CLAUDE.md Section 3.2;
the result and consumed proof helpers have proof_shape bind-only. Old
invariant-algebra ingredients do not receive new mechanism credit. The
family members, six readings and optional-constant robustness do not count
as additional problems. Conjecture 1, Question 3 and the source's infinitude
and algorithm questions remain separate.

Proved: every odd r at least three gives the complete simultaneous family
properties and refutes the necessary direction of each published iff. The
failure is the sparse classification: translation invariance is preserved
under powers, whereas the positive leading exponent 4r is outside the
powers-of-two support allowed by the proposed representation. Neither the
source parity rule nor an arbitrary constant changes that coefficient.

Surviving proved structure: the family remains translation-invariant under
all powers, as expressed by p_invariant. The general invariant-algebra
classification in the Mattarei–Pizzato reference is an existing result,
not an additional settlement. The sufficient direction of the literal
source assertion is not separately settled by this unit. Theorem 9 precedes
the conjecture; no later result of the source is identified as depending on
it. Conjecture 1, Question 3 and the infinitude and algorithm questions
retain their separate unresolved status here.

Exact successor candidate, unresolved in this unit: for every
p in GF(2)[X] whose positive supported exponents are all powers of two,
p.comp(X+1)=p if and only if the number of positive supported exponents is
even, independently of its constant coefficient. This restricted
classification requires its own literature and library check; existing
Frobenius results may supply it by binding. It is not asserted as a new
open problem, proved result or additional resolution credit, and creates
no further declaration in this module.

## ASSUMED-UNVERIFIED

The unique author-intended meaning of even, global absence of an earlier
full answer, publication priority and global ownership remain unverified.
The mathematical refutation covers precisely the six stated conventional
readings in the source's unrestricted formal-polynomial context. No
irreducibility or Fibonacci restriction, repaired source statement or
functional-equality interpretation is assumed.
