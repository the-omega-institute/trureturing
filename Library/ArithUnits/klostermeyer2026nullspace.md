---
bibkey: klostermeyer2026nullspace
authors: William F. Klostermeyer
year: 2026
title: Prime Nullspace Matrices and Even Dominating Sets
doi: null
url: https://arxiv.org/html/2610.31475v1#Thmconj2
claim: "Conjecture 2 asserts a sparse powers-of-two characterization of self-conjugate even polynomials over GF(2), with parity determined by the constant term."
strata_touched:
  - D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation
license: CC-BY-4.0
triage: anchor
---

# Self-conjugate even polynomials

## Verified locator

Source: https://arxiv.org/html/2610.31475v1#Thmconj2

The verified scope is arXiv:2610.31475v1, Section 2, Conjecture 2,
on PDF page 4 immediately after Theorem 9. The definition of self-conjugacy
and the literal iff are quoted below; the even/constant ambiguity and bounded
known-answer limits below remain part of this source reading.

## Source statement

The versioned source is https://arxiv.org/html/2610.31475v1#Thmconj2.
Section 2, Conjecture 2, on PDF page 4 immediately after Theorem 9, states:

> Let p(x) be an even polynomial over GF(2). Then p(x) is self-conjugate if and only if p(x)=x^{2^{k_1}}+x^{2^{k_2}}+...+x^{2^{k_m}}, where m is odd if x^0 is a term and m is even otherwise.

The preceding definition reads:

> We say a polynomial f(x) is self-conjugate if f(x)=f(x+1).

The equality is in the formal polynomial ring. Natural indices, including
zero and repetitions, and an arbitrary finite number of summands are retained.
The paper does not define “even polynomial”; its display omits the constant
mentioned by the prose. No unique intended meaning or corrected statement is
asserted. The stated polynomial domain has no irreducibility or Fibonacci
restriction. Conjecture 1, Question 3 and the nullspace-prime infinitude and
algorithm questions are separate assertions.

## Uniform obstruction

In GF(2)[X], put U = X^4 + X^2 and P(r) = U^r. For every odd natural r at
least three, P(r) is monic, nonzero and translation-invariant, has degree 4r,
only even supported exponents, zero constant coefficient and an even number
of supported terms. It is divisible by X and satisfies P(r)(-X) = P(r)(X).
The degree 4r is not a power of two. Its coefficient in P(r) is one, while
its coefficient in any finite sum of powers-of-two monomials, even with an
arbitrary constant, is zero. Thus every such r supplies the same obstruction
under each conventional reading, before imposing either source parity branch.
The optional-constant exclusion is robustness of these witnesses and does not
replace the literal display.

The definitions and proof are in
`D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.lean`. The public claim
is the disjunction, over the six explicit conventional domains, of the full
published universal iff or its separately labelled optional-constant variant.
Its negation refutes each complete iff; no failed auxiliary family property
can refute this claim.

## Literature boundary

The general translation-invariant polynomial mechanism is classical; see
`D5/L/ArithUnits/mattareipizzato2017reciprocal`, Section 5. The direct family
argument uses Frobenius, monicity, polynomial expansion and coefficients.
The bounded primary-source, arXiv-author, Crossref, MathDB and repository
review in issue #21419 located no prior full answer to this sparse-power iff.
That observation does not establish global absence, ownership or priority.
The author-intended meaning of “even” remains unverified. An authoritative
restriction excluding this family would change the scope of the assertion.
