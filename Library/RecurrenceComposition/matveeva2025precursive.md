---
bibkey: matveeva2025precursive
authors: Anastasia Matveeva
year: 2025
title: On the integrality of some P-recursive sequences
doi: null
url: https://arxiv.org/abs/2511.02121v1
claim: The literal nonzero-parameter belief in Sections 4.2 and 7 is refuted by the rational sequence s_n = n + 1.
strata_touched:
  - D5/S1/Recurrence/MatveevaGlobalBoundedness
license: citation-only
triage: anchor
---

# Rational recurrence solutions and global boundedness

## Verified locator

Version: arXiv:2511.02121v1, https://arxiv.org/abs/2511.02121v1.
Primary source: https://arxiv.org/src/2511.02121v1.
The locators are Definitions 1.4 and 1.5, Section 4.2, equation (4.1)
and the paragraph following its general generating-function solution, and
Section 7, Concluding remarks.

## Source statements

Definition 1.4 calls a rational power series almost integral when a nonzero
integer C makes C^n s_n integral for every n >= 1. Definition 1.5 adds a
nonzero complex radius of convergence to define global boundedness.
The constant coefficient need not be integral.

Section 4.2 considers rational parameters a1, a2, b0, b1, b2 with a1 and a2
nonzero and b0 outside {-2, -3, ...}, and rational initial values s0 and s1.
Its recurrence is

$$
(n+b_0)s_n+(a_1n+b_1)s_{n-1}+(a_2n+b_2)s_{n-2}=0
\qquad(n\geq 2).
$$

Immediately after the general solution, the source states:

> Supposedly, if e does not vanish in the equation above, S(x) is not globally bounded. However, this question remains open for now.

Section 7 makes the parameter condition explicit:

> The case of $b_2 \neq \frac{2a_2b_1-a_1a_2b_0}{a_1}$ is still poorly understood, although we believe it leads to not globally bounded solutions.

The literal parameter interpretation is E = a1*a2*b0 + a1*b2 - 2*a2*b1
nonzero. It does not require an exponential factor to remain after
simplifying the full generating function, nor minimal recurrence order,
nonrationality, or normalized initial values. A statement with such an
additional hypothesis would be a different statement. Conjecture 4.1 is a
separate assertion and is outside this result.

## Mathematical conclusion

For (b0, a1, b1, a2, b2) = (1, -3, -1, 2, 1), the rational sequence
s_n = n + 1 satisfies the recurrence at every n >= 2, has s0 = 1 and
s1 = 2, and has E = -5. Its coefficients are integral with C = 1.
For every complex z with norm less than 1, the full series with terms
(n+1)z^n is summable. Thus this solution is globally bounded and refutes
the universal parameter-condition assertion.

The conclusion concerns this literal reading of the quoted belief.
The bounded literature screening does not establish worldwide priority
or the absence of another published resolution.
