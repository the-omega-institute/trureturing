---
bibkey: sharma2026primitivepolynomials
authors: Avnish K. Sharma
year: 2026
title: "Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures"
doi: null
url: https://arxiv.org/abs/2608.07262v2
claim: "Conjecture 4.2 asserts that for every odd prime p, every finite field K of cardinality p^2, and every multiplicative generator λ of K, X^p+X+λ is the monic minimal polynomial of a multiplicative generator in a degree-p extension."
strata_touched:
  - D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation
license: CC-BY-4.0
triage: anchor
---

# Primitive polynomials of the form g(x)+λ

Avnish K. Sharma's arXiv version 2 (arXiv:2608.07262v2, August 30, 2026)
studies primitive polynomials of the form \(g(x)+\lambda\) over finite fields.
Conjecture 4.2, printed page 16, states (mathematical typography transliterated):

> Let p be an odd prime. Then, for every primitive element λ∈F_(p²), the polynomial x^p+x+λ is primitive over F_(p²).

Its full scope is: for every odd prime \(p\), every finite field
\(K\) of cardinality \(p^2\) and characteristic \(p\), and every
\(\lambda\in K\) satisfying the source multiplicative-generator condition
\(\operatorname{ord}(\lambda)=|K|-1\), the polynomial \(X^p+X+\lambda\) is
the monic minimal polynomial of a multiplicative generator in a degree-\(p\)
extension. Here “primitive” means the source's multiplicative-generator
condition, not `Polynomial.IsPrimitive` (coefficient content).

## Verified locator

Versioned arXiv record: https://arxiv.org/abs/2608.07262v2.
The primary sources are the [versioned PDF](https://arxiv.org/pdf/2608.07262v2)
and [versioned HTML](https://arxiv.org/html/2608.07262v2). The audited PDF
SHA256 is `6b4318dbf8743a53ee8541993bd2a63332828fcd7632937861e2e656aab2d635`;
the HTML SHA256 is
`494fb73698fbf2bf9c09b38656be21f304640ef95a0da8b58bf7dcb7975b12d1`.
Remark 4.2 checks every primitive lambda only for primes 3 through 37;
41 is outside that reported range. The existential Conjecture 4.1 is a
different statement and is not refuted here.

## Formal source and refutation

The Lean module
`D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.lean` defines the
source predicate `SourcePrimitivePolynomial`, the primitive-lambda predicate,
and the exact coefficient-parameterized polynomial. Its public `fullClaim` is
the complete universal Conjecture 4.2 with the source multiplicative order and
minimal-polynomial meaning. The public `result` has type
`Not (claimFor SourceLeadingCoefficient)`; it is the unconditional negation of
that full claim.

The certificate uses
\[
 K = \operatorname{QuadraticAlgebra}(\mathbb Z/41\mathbb Z,3,0),\qquad
 \lambda = 5+u,
\]
where \(u^2=3\). The kernel checks that \(|K|=41^2=1681\), that λ has
order \(1680=|K|-1\), and that the actual source polynomial has degree 41.
The 41 coefficients in `certificateCoefficients` are multiplied by eight
exact product identities. Horner semantics then give, for every field
extension \(L/K\) and every root α of \(X^{41}+X+\lambda\),
\[
 z = \operatorname{aeval}_{\alpha}(\texttt{certificatePolynomial}),
 \qquad z^{83}=\alpha.
\]
If Conjecture 4.2 supplied a degree-41 extension and a primitive root α, then
\(|L|=1681^{41}\). The finite-field exponent for z forces
\(\alpha^{(1681^{41}-1)/83}=1\), while primitivity requires order
\(1681^{41}-1\). Since the exponent is positive and strictly smaller, this
is impossible. The argument uses the source's full universal root certificate
and multiplicative-order conclusion; it does not replace them by a finite
enumeration or by a coefficient-content statement.

## Registration and bounded literature scope

The four-slot registration is source-owned by `sourceCounterexampleArena`.
Its readout is the enrolled direct `sourceCoefficientRealization`, its law
contains the actual degree-41 condition, the coefficient-dependent universal
root certificate, and the full claim negation. The merged `realization inline`
syntax produces a registration-owned `LegacyPrimitiveRealization`: its forward
direction proves the degree and root certificate from the source and retains
the incoming full-claim negation; its reverse direction projects that negation.
There is no separately authored bridge theorem. The altered coefficient zero
has degree one, providing the variation and slot-sensitivity witnesses. The
continuation is explicitly `open`; no frozen identifier or
`OpenProblemResolutionClaim` is asserted in this pre-Freeze artifact.

The candidate was numerically discovered before
[preregistration #8851](https://github.com/the-omega-institute/trureturing/issues/8851),
which records the target, source audit and library search. No first-discovery
or publication-priority claim is made. That bounded audit found arXiv v1 dated
August 7 and current v2 dated August 30, with no later version found. Checked
arXiv/title/author, OpenAlex and Crossref results contained no inspected
resolution; Semantic Scholar was rate-limited. This does not establish
worldwide absence of a resolution.

Local semantic surfaces and all-ref exact identifier/author history had no
exact delivery. All-state GitHub exact/formula searches and a paginated
issue/PR-body scan found no exact owner; every issue comment was not searched.
The pinned Mathlib search (commit
`db584cd6d46c92f209a44c0f1c829460d327499d`) supplied the quadratic algebra,
minimal-polynomial, finite-field cardinality and multiplicative-order APIs.
The bounded external Lean search found unrelated GF8/GF256 models and
antiderivative uses of the name PrimitivePolynomial, without a proof of this
conjecture. The source certificate is repository-derived; no external proof
code is transplanted.
