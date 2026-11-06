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

The counterexample settles the unrestricted assertion. It does not contradict the prime-only theorem and does not establish minimum cardinality, minimum maximum parameter, or a composite-only version.

## Evidence

The result and its claim are in `D5/S3/FiniteGroups/FactorialProductNonunique.lean`; their corresponding formulas and mathematical exposition are in its Blueprint Scribe. The original factorial factor remains defined in `TransversalProbabilityMonotone`, and is directly reused.

Admission basis: `open-problem-resolution`, preregistration [#27274](https://github.com/the-omega-institute/trureturing/issues/27274). The finite rational normalization is classified `proof_shape: bind-only`; its named external-problem conclusion supplies the stated admission basis. Utility is `certified-instance` with `refutes=claim`. The only new public theorem is the designated literal refutation result and is exempt from four-slot escape registration.

## Triage

### What the settlement shows

The exact finite counterexample refutes the unrestricted assertion through a ternary-coefficient multiplicative relation among adjacent ratios, which yields parameters without repetition. The prime-only theorem survives. Minimum cardinality, minimum maximum parameter and an all-composite restriction remain unresolved here. The asymptotic smooth-pair route is unnecessary for this finite refutation and is not asserted as a formal theorem.

## ASSUMED-UNVERIFIED

The source and qualification readings are bounded by #27274. The two primary texts state the question; their retention does not prove that no later settlement exists. Worldwide novelty remains `suspected-novel`, and completeness of the literature screen is `ASSUMED-UNVERIFIED`. No original-priority claim is made.
