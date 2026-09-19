---
slug: sharma-primitive-polynomial-conjecture-4-2
bibkey: sharma2026primitivepolynomials
doi: null
url: https://arxiv.org/abs/2608.07262v2
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/InformationEscape/TheoremUnit
---

# Sharma's primitive-polynomial Conjecture 4.2

## Problem

The target is the literal Conjecture 4.2 in Avnish K. Sharma's
*Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence
Results and Conjectures*, arXiv:2608.07262v2. For every odd prime \(p\), every
finite field \(K\) with characteristic \(p\) and \(|K|=p^2\), and every
\(\lambda\in K\) satisfying the source multiplicative-generator condition
\(\operatorname{ord}(\lambda)=|K|-1\), the source claim says that
\(X^p+X+\lambda\) is the monic minimal polynomial of a multiplicative
generator in an extension \(L/K\) of degree \(p\). “Primitive” here means
multiplicative order; it does not mean `Polynomial.IsPrimitive`.

The [primary statement](https://arxiv.org/html/2608.07262v2), printed page 16,
reads (mathematical typography transliterated):

> Let p be an odd prime. Then, for every primitive element λ∈F_(p²), the polynomial x^p+x+λ is primitive over F_(p²).

The negated statement proved here is
\[
\neg\bigl[\forall p\text{ odd prime},\ \forall K\text{ finite field of
characteristic }p\text{ with }|K|=p^2,\ \forall\lambda\in K,
\ \operatorname{ord}(\lambda)=|K|-1\ \Longrightarrow
\exists L/K,\alpha\in L:\ [L:K]=p\ \land
\operatorname{minpoly}_K(\alpha)=X^p+X+\lambda\ \land
\operatorname{ord}(\alpha)=|L|-1\bigr].
\]
The extension is a finite field extension. The minimal polynomial is monic.
The existential Conjecture 4.1 is not the target.

The Lean definition `fullClaim` preserves all of these quantifiers and the
source conclusion. The candidate coefficient is the source leading
coefficient, so the public `result` is exactly `Not fullClaim` after unfolding
the coefficient parameter.

## Motivation

The source strengthens its existential Conjecture 4.1 to every primitive
lambda when the base field has cardinality p squared. Its reported tests
cover primes 3 through 37. A primitive lambda at p=41 for which no primitive
extension generator has the stated minimal polynomial negates precisely
that stronger universal claim.

## Gap

The bounded source, library and ownership audit in #8851 found no inspected
resolution of Conjecture 4.2 in its checked scope. The finite tests in
Remark 4.2 do not establish the unbounded universal claim. The required
formal gap is a primitive-lambda counterexample with a certificate applying
to every hypothetical root in the source extension, not a sampled root.

## Route

The refutation instantiates \(p=41\) with
\(K=\operatorname{QuadraticAlgebra}(\mathbb Z/41\mathbb Z,3,0)\) and
\(\lambda=5+u\), where \(u^2=3\). Eight kernel-checked coefficient-list
product identities evaluate the certificate polynomial at any root α of
\(X^{41}+X+\lambda\) and prove \(z^{83}=\alpha\). The same source proves
\(|K|=1681\), `orderOf λ = 1680`, and the actual degree-41 condition.

Assuming the conjecture for this λ would produce a degree-41 extension \(L\),
so \(|L|=1681^{41}\) and a primitive α of order \(|L|-1\). Finite-field
exponentiation applied to \(z\), together with \(z^{83}=\alpha\), forces α to
have order dividing \((1681^{41}-1)/83\). This is a strict positive divisor
bound below the claimed order, giving the contradiction and the full claim
negation.

## Evidence

The source theorem is
`D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.result`.
The source-owned information law is
`D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullCounterexampleLaw`;
it includes the actual degree, the coefficient-dependent universal root
certificate, and the negation of the coefficient-indexed claim. The actual
readout uses `actualSourceCoefficientRealization`, while the zero-coefficient
realization has degree one. The registration therefore records substantive
variation and sensitivity, with the continuation marked `open` before Freeze.

The utility header requests the typed closed-negation relation from
`D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullClaim` to
`D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.result` under
`certified-instance` / `refutes`. The native producer owns its source-bound
evidence. No frozen identity or typed open-problem settlement is asserted here.

## Falsifier

A defect in the source quantifiers, the order/minimal-polynomial definition,
the degree-41 certificate, the eight-product Horner identities, or the finite
extension cardinality argument would invalidate the route. A finite sample of
primes or lambdas would not address the universal claim.

## Triage

`theorem`, targeting the published Conjecture 4.2 under
`open-problem-resolution`, subject to final review. The computational
content is a `certified-instance` with the utility basis `refutes`: the
conclusion is the negation of the full universal conjecture. The current
dossier carries no frozen settlement and makes no merge or KPI claim.

## ASSUMED-UNVERIFIED

The numerical discovery preceded
[preregistration #8851](https://github.com/the-omega-institute/trureturing/issues/8851).
The source hashes and bounded literature/library/ownership search results are
in [the Library note](../Library/ArithUnits/sharma2026primitivepolynomials.md).
No inspected resolution was found in the checked arXiv, OpenAlex and Crossref
scope; Semantic Scholar was rate-limited. The repository ownership scan
covered issue/PR bodies but not every comment. These limits do not establish
worldwide absence of prior resolution, and no priority claim is made.
Independent review, Freeze-last settlement and the later typed
`OpenProblemResolutionClaim` remain caller-owned obligations.
