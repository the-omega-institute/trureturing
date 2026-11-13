---
slug: alm2024-factorial-product-uniqueness
bibkey: aivazidis2023commontransversal
doi: 10.48550/arXiv.2209.00986
url: https://arxiv.org/abs/2209.00986v2
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/FactorialProductNonunique.result
---

# Factorial-product uniqueness

## Problem

S. Aivazidis, M. Loukaki and T. W. Müller, *On the common transversal probability*, Journal of Group Theory 27(6) (2024), 1233–1285, Problem 5.6, printed p. 1281; arXiv:2209.00986v2, printed p. 37, ask whether

$$\prod_{i=1}^{n}f(t_i)=\prod_{j=1}^{k}f(s_j),\qquad f(x)=\frac{\Gamma(x+1)}{x^x},$$

for distinct integers greater than one implies uniqueness:

> Can we then conclude that n=k and t_i=s_i for all i after rearranging appropriately?

Both primary versions contain this question. The journal's word “distinct” is unparenthesized. The finite sets below are disjoint, satisfying distinctness even across the two lists. The source has no additional group realization, prime, sum or length hypothesis. The prime-parameter result in Theorem 4.6 is separate.

The return authors are Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore; ChronoAI Pte Ltd, Singapore). The source-question authors are not thereby coauthors.

## Motivation

The factors in the common-transversal counting formula are rational numbers of the form m!/m^m. Uniqueness of their products would recover the integer parameter set from that arithmetic invariant. Theorem 4.6 establishes a separate prime-parameter case; the question here permits every integer greater than one.

## Gap

The unrestricted assertion fails. Its exact formal correspondence is:

| Source clause | Formal counterpart |
| --- | --- |
| Arbitrary finite lists with distinct integer parameters greater than one | Arbitrary `A B : Finset ℕ` with `∀ m ∈ A, 1 < m` and the same for B; positive integers identify with these naturals. |
| `f(m)=Gamma(m+1)/m^m` on this domain | The original `TransversalProbabilityMonotone.orbitWeight m = (m.factorial : ℚ)/(m : ℚ)^m`. |
| Equal products | Literal finite products in ℚ; no approximation. |
| Same parameters after reordering | `A = B`; finsets remove ordering and forbid repeated factors. |
| Negative answer | `result : ¬ claim`, where `claim : Prop` is closed and universally quantified. |

The claim places no bound on either cardinality or any member. A single exact finite counterexample refutes it.

## Route

The adjacent ratio identity is

$$\frac{f(n+1)}{f(n)}=\left(\frac{n}{n+1}\right)^n.$$

The starting sets U={16,20,22,26,44,64,76,94,140} and V={10,24,38,46,48,56,68,80,84} have equal products of these ratios. All starts are even and distinct, so the corresponding adjacent pairs have no common endpoint. Crossing the ratios gives A and B below. The formal proof verifies the factorial products themselves, so this explanation introduces no unproved analytic supplier.

## Falsifier

Let

$$A=\{10,17,21,23,24,27,38,45,46,48,56,65,68,77,80,84,95,141\},$$

$$B=\{11,16,20,22,25,26,39,44,47,49,57,64,69,76,81,85,94,140\}.$$

Both sets are nonempty, have eighteen elements, are disjoint, and contain only integers greater than one. Their exact products satisfy

$$\prod_{a\in A}\frac{a!}{a^a}=\prod_{b\in B}\frac{b!}{b^b}.$$

The proof evaluates these two rational products directly and applies the universal claim to A and B. Since A and B differ, this gives its literal negation.

The finite data also admit an adjacent-pair reconstruction. Put

$$U=\{16,20,22,26,44,64,76,94,140\},\qquad
V=\{10,24,38,46,48,56,68,80,84\}.$$

The sets $U$ and $V$ are disjoint and every start is even. With $S+1=\{s+1:s\in S\}$,

$$A=V\cup(U+1),\qquad B=U\cup(V+1).$$

Thus the eighteen adjacent pairs are disjoint, both displayed sets have cardinality 18, and their sums are both 965. For
$r(n)=f(n+1)/f(n)=(n/(n+1))^n$, the exponent sums
$\sum_{n\in S}n(v_p(n)-v_p(n+1))$ agree for $S=U,V$ at the ten displayed primes
$2,3,5,7,11,13,17,19,23,47$, and no other prime occurs in the adjacent factors. The common certificate is

$$\frac{2^{1150}7^{44}}
{3^{326}5^{42}11^{10}13^{38}17^{16}19^{18}23^{22}47^{46}}.$$

The exponent table and support explain the adjacent-pair certificate; the original refutation proof checks the factorial products directly.

For every finite $C$ disjoint from $A\cup B$, adjoining $C$ to both sides preserves the actual products and distinctness, gives equal sums
$965+\sum_{c\in C}c$, and leaves the symmetric difference equal to $A\cup B$ of cardinality 36. When the representations are required to have parameters greater than one, impose that condition on C as well. The explicit choice $C=\{142,\ldots,141+(k-18)\}$, empty at $k=18$, gives distinct $k$-element representations for every $k\ge18$. For $k>18$ the two extensions share $C$; they are not asserted to be disjoint.

For each fixed $k\ge19$, choose $|D|=k-19$ outside $A\cup B$ and vary $c$ above every element of $A\cup B\cup D$. One explicit choice is $D=\{142,\ldots,141+(k-19)\}$, empty at $k=19$. The two $k$-element representations have equal sums within each pair and common positive rational value
$F(A)F(D)f(c)$. Positivity and strict decrease of $f$ on positive arguments make these values pairwise different. The positive constant $F(A)F(D)$ preserves strict decrease, so this map from an infinite integer tail is injective and its image is infinite. Their sums may vary with $c$; no fixed-sum infinitude statement is made.

For strictly increasing equal-length lists of integers greater than one with $a_i\le b_i$ coordinatewise, the product at the $a$ list is at least the product at the $b$ list, with equality exactly when all coordinates agree. The empty-list boundary is the empty product 1 when length zero is admitted. Strictness is restricted to the positive domain: the total orbit weight has value 1 at both 0 and 1.

The counterexample settles the unrestricted assertion. It does not contradict the prime-only theorem and does not establish minimum cardinality, minimum maximum parameter, or a composite-only version.

The associated decreasing-vector comparison is only a finite incomparability check: the first partial sums are $141>140$, while the ninth are $714<715$. It is not a generic weak-majorisation theorem and does not refute the source's Appendix A. The journal Problem 5.6, arXiv v2 Problem 5.6 and arXiv v1 Problem 12.6 are covered; Problems 5.1--5.5 and 5.7--5.8, group realization, least-cardinality and minimum-maximum claims, and an all-composite restriction remain outside this settlement.

## Evidence

The result and its claim are in `D5/S3/FiniteGroups/FactorialProductNonunique.lean`; their corresponding formulas and mathematical exposition are in its Blueprint Scribe. The original factorial factor remains defined in `TransversalProbabilityMonotone`, and is directly reused.

The reusable weight owner supplies the adjacent-ratio/antitone comparison chain used by the application. Strictness additionally follows because for positive n the adjacent ratio is a nonzero power of a rational strictly between zero and one; chaining the strict adjacent drops covers every pair of positive indices. All weights are positive by positivity of the factorial and denominator, with the zero case evaluated separately; the total definition has orbitWeight 0 = orbitWeight 1 = 1. The finite extensions and the fixed-cardinality infinite family are written compositions of the displayed witness, finite-set operations, and this positivity/strictness argument; no new Lean declaration is retained for a bind-only application.

Admission basis: `open-problem-resolution`, preregistration [#27274](https://github.com/the-omega-institute/trureturing/issues/27274). The finite rational normalization is classified `proof_shape: bind-only`; its named external-problem conclusion supplies the stated admission basis. Utility is `certified-instance` with `refutes=claim`. The only new public theorem is the designated literal refutation result and is exempt from four-slot escape registration.

## Triage

### What the settlement shows

The exact finite counterexample refutes the unrestricted assertion through a ternary-coefficient multiplicative relation among adjacent ratios, which yields parameters without repetition. The theorem requiring distinct primes on one side survives. Minimum cardinality, minimum maximum parameter and an all-composite restriction remain unresolved here. The asymptotic smooth-pair route is unnecessary for this finite refutation and is not asserted as a formal theorem.

## ASSUMED-UNVERIFIED

The source and qualification readings are bounded by #27274. The two primary texts state the question; their retention does not prove that no later settlement exists. Worldwide novelty remains `suspected-novel`, and completeness of the literature screen is `ASSUMED-UNVERIFIED`. No original-priority claim is made.
