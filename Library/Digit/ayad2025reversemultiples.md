---
bibkey: ayad2025reversemultiples
authors: Mohamed Ayad; Rachid Bouchenna
year: 2025
title: "Which Integer Divides the Reverse of Any of Its Multiples?"
doi: 10.5281/zenodo.15283699
url: https://math.colgate.edu/~integers/z37/z37.pdf
claim: "Problem 1: Let B ≥ 2 be any number base. Are the divisors of B² − 1 the only positive integers satisfying the property P*_B ?"
strata_touched:
  - D5/S1/Digit/AyadBouchennaReverseMultipleDivisors
license: citation-only
triage: anchor
---

# Reversal of every multiple in an arbitrary base

Mohamed Ayad and Rachid Bouchenna, INTEGERS 25 (2025), #A37,
published April 25, 2025. The following passages were checked against
the printed pages of the source PDF on September 20, 2026.

Section 4.1, p. 8, defines reversal verbatim (with the displayed expression
written inline):

> For every positive integer $m = a_k B^k + \cdots + a_1 B + a_0$, we call the integer
> $m^*_B = a_0 B^k + a_1 B^{k-1} + \cdots + a_k$.
> the reverse of $m$ in base $B$

The same page defines the property verbatim:

> A positive integer $n$ is said to have the property $P^*_B$ if $n$ divides $m^*_B$ for any positive multiple $m$ of $n$, that is, if for every positive integer $m$, if $n$ divides $m$, then $n$ divides $m^*_B$.

Proposition 5, p. 8, states verbatim:

> Let $B \geq 2$ be a number base and $n$ be a positive divisor of $B^2 - 1$. Then $n$ has the property $P^*_B$.

Problem 1, p. 9, asks verbatim:

> Let $B \geq 2$ be any number base. Are the divisors of $B^2 - 1$ the only positive integers satisfying the property $P^*_B$ ?

The formal reversal is exactly `Nat.ofDigits B (Nat.digits B m).reverse`.
`Nat.digits` lists digits from least to most significant, so this expression
evaluates the reversed positional expansion, including numbers ending in zero.
The property quantifies over positive natural multiples. The characterization
quantifies over every natural base at least two and every positive natural n.
Its sufficiency direction is Proposition 5; its necessity direction answers
Problem 1 affirmatively. The new characterization is repository-derived;
the source supplies the definitions, the question, and the sufficiency direction.

Theorem 3 of the paper already settles base ten. No claim about Problem 2
or about the weakened property in section 4.2 is made here.

## Verified locator

- DOI: 10.5281/zenodo.15283699
- URL: https://math.colgate.edu/~integers/z37/z37.pdf
- Scope: Printed p. 8, section 4.1 definitions and Proposition 5; printed p. 9, Problem 1.
