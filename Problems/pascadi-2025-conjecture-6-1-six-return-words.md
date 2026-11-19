---
slug: pascadi-2025-conjecture-6-1-six-return-words
bibkey: pascadi2025nonabelianamplification
doi: null
triage: window
motivation_gids:
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord_fixed_middle_count
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
created by a nonunit coefficient. Its gcd period controls a bounded count without
dividing by that coefficient modulo a composite modulus.

## Gap

The source's uniform six-letter estimate for arbitrary moduli, and hence the full
Conjecture 6.1 in its median range, is not proved here. The repository now proves a
uniform original-tuple slice for c=p^3: for every epsilon>0, C0>=1 and fixed
alpha<26/7, the total count over all scalar centers is at most
`K(epsilon,C0,alpha)*Y^2*p^epsilon` when `p^(3/2)<=X<=Y`,
`XY<=C0*p^alpha`, `6Y<p^2`, and the two alternating coefficients are units.
This includes all middle coordinates, zero and nonunit rows and ordered
multiplicities. It does not settle other moduli or the strict cutoff endpoint.

## Route

The module fixes the middle coordinates $h_2,h_3,h_5,h_6$ and a central scalar $\gamma$.
It proves the three entrywise compatibility equations forced by a six-letter central return,
without dividing by the possibly nonunit coefficient
$D=1-a_1a_2h_2h_3$. It then proves that two points in the same completion fiber differ by
the additive order $N=c/\gcd(c,D.val)$ in each free coordinate. For arbitrary $c>0$,
units $a_1,a_2$ in $\mathbb Z/c\mathbb Z$, $\gamma^2=1$, fixed middle coordinates
in $\mathbb Z/c\mathbb Z$, and every natural $H$, the actual fixed-middle count is

$$\#\{(h_1,h_4)\in\{0,\ldots,H-1\}^2:
\mathrm{sixReturnWord}(a_1,a_2,h_1,h_2,h_3,h_4,h_5,h_6)=\gamma I\}
\le (\lfloor H/N\rfloor+1)^2.$$

No bound is assumed. The statement includes empty intervals, $H>c$, composite moduli,
and $D=0$, when $N=1$.

The matrix product is cancelled on the right by an explicit inverse for the final two
transfer matrices. Entrywise comparison gives the three equations. For two completions,
subtract the equations and use the additive-order characterization of zero scalar
multiples in `ZMod c`; the resulting period is `c / gcd(c,D.val)`. Since $N$ divides
$c$, congruence of reduced representatives modulo $N$ gives congruence of the natural
coordinates. Two actual solutions with equal coordinatewise quotients by $N$ therefore
coincide. These quotients lie in $\{0,\ldots,\lfloor H/N\rfloor\}^2$, proving the count.

## Falsifier

A bounded six-tuple count exceeding Pascadi's conjectured right-hand side, for fixed
implicit constants and a growing modulus family, would falsify the source conjecture. A
purported completion with the stated central return but violating one of the three
compatibility equations, or a fixed-middle interval count exceeding the displayed
gcd-period bound, would falsify the formal milestone.

## Evidence

The strengthened prime-cube result is
`prime_cube_scalar_return_count_of_exponent` in
`D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount`; its complete exact-root
build and scoped standard-axiom report passed on 18 November 2026.
The earlier `prime_cube_scalar_return_count` statement with exponent 18/5
is preserved. Canonical publication and required remote checks remain separate
from these local proofs. Source-bound four-slot audits are unfinished under
[issue #31176](https://github.com/the-omega-institute/trureturing/issues/31176).

The kernel-checked declarations are
`completion_equations_of_sixReturnWord`, `completionFiber_period`, and
`sixReturnWord_fixed_middle_count` in `D5/S3/Arith/CharacterSums/PascadiSixWordFiber`.
The count uses the first two declarations on its proof path. The source locator is
Alexandru Pascadi, arXiv:2511.08445v2, §6,
Conjecture 6.1 and Proposition 6.2.

## Triage

This is a `window`: the source conjecture remains a live quantitative target.
The repository delivers both the original fixed-middle result for arbitrary moduli
and the later uniform prime-cube slice above. The full Conjecture 6.1 remains open.
Literature completeness and priority are not asserted; see the linked Library
entry for the bounded primary-source comparison and its remaining gap.

## ASSUMED-UNVERIFIED

The external literature screen includes the cited arXiv and journal versions and
the bounded comparison described in the Library entry. The final 2021 Shkredov
Journal of Number Theory Lemma 15 primary text was not obtained. The complete
six-letter conjecture and any exhaustive priority claim remain unverified.
