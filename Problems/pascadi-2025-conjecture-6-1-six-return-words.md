---
slug: pascadi-2025-conjecture-6-1-six-return-words
bibkey: pascadi2025nonabelianamplification
doi: null
triage: window
motivation_gids:
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period
url: https://arxiv.org/abs/2511.08445v2
---

# Pascadi Conjecture 6.1: six-letter return-word count

## Problem

For even $q$, units $a_1,a_2\in(\mathbb Z/c\mathbb Z)^\times$, and alternating integer
ranges $|h_i|\le H_1$ or $H_2$, count the tuples whose alternating $T,S$ product is the
identity in $\mathrm{PSL}_2(\mathbb Z/c\mathbb Z)$. Conjecture 6.1 of Pascadi predicts

$$\#\{h\}\ll_q c^{o(1)}\left(H_2^{(q-2)/2}+
\frac{(H_1H_2)^{q/2}}{c^3}\right).$$

The first unresolved target is $q=6$, with six alternating letters and
$1\le H_1\le H_2\ll c$. Pascadi's Proposition 6.2 proves only

$$\#\{h\}\ll c^{o(1)}\left(H_2^2+\frac{(H_1H_2)^2}{c}\right),$$

and records special parameter ranges where the conjectured estimate is known. The full
median-range six-letter estimate is presented as open in arXiv:2511.08445v2, §6.

## Motivation

The six-letter central-return calculation is the first nontrivial median-range case of
Pascadi's counting conjecture. The completion fiber isolates the arithmetic obstruction
created by a nonunit coefficient, so a later bounded count can separate gcd strata instead
of informally dividing modulo a composite modulus.

## Gap

The source's uniform six-letter estimate, and hence Conjecture 6.1 in its median range,
is not proved here. The current result only supplies necessary compatibility equations and
a periodicity lemma for a fixed middle stratum.

## Route

The module fixes the middle coordinates $h_2,h_3,h_5,h_6$ and a central scalar $\gamma$.
It proves the three entrywise compatibility equations forced by a six-letter central return,
without dividing by the possibly nonunit coefficient
$D=1-a_1a_2h_2h_3$. It then proves that two points in the same completion fiber differ by
the additive order $c/\gcd(c,D.val)$ in each free coordinate. This supplies the gcd-periodic
fiber decomposition needed before a finite-range count can be attempted.

The matrix product is cancelled on the right by an explicit inverse for the final two
transfer matrices. Entrywise comparison gives the three equations. For two completions,
subtract the equations and use the additive-order characterization of zero scalar
multiples in `ZMod c`; the resulting period is `c / gcd(c,D.val)`.

## Falsifier

A bounded six-tuple count exceeding Pascadi's conjectured right-hand side, for fixed
implicit constants and a growing modulus family, would falsify the source conjecture. A
purported completion with the stated central return but violating one of the three
compatibility equations would falsify the formal milestone.

## Evidence

The kernel-checked declarations are
`completion_equations_of_sixReturnWord` and `completionFiber_period` in
`D5/S3/Arith/CharacterSums/PascadiSixWordFiber`. The targeted Lean build passed under
Lean 4.35 with 1579/1579 jobs, and the scoped Lean report extracted one module and eight
declarations. The source locator is Alexandru Pascadi, arXiv:2511.08445v2, §6,
Conjecture 6.1 and Proposition 6.2.

## Triage

This is a `window`: the source conjecture remains a live quantitative target, while the
repository delivers a structural first step rather than a settlement. No claim is made
that the weaker Proposition 6.2 or the full conjecture has been reproved.

This is a partial structural result. It does not prove the uniform Conjecture 6.1 bound,
does not count bounded integer representatives, and does not claim a resolution of the
source problem. Literature completeness and priority are not asserted.

## ASSUMED-UNVERIFIED

The external literature screen is limited to the cited arXiv version and the repository's
reuse search. The complete six-letter conjecture and any priority claim remain unverified.
