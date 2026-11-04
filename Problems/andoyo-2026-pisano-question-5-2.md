---
slug: andoyo-2026-pisano-question-5-2
bibkey: andoyo2026pisanolegendrecollision
doi: 10.62072/acm.2026.09011
url: https://arxiv.org/html/2601.10561v1#S5.Thmquestion2
triage: theorem
motivation_gids:
  - D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.result
---

# Andoyo Question 5.2: infinitude of exact prime fibers

## Problem

Jason D. Andoyo, *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*, Question 5.2, asks:

> Suppose that $a$ and $b$ are integers with $(a,b)\ne(0,0)$. For every $k\in\chi(a,b)$, is $|\vartheta_{(a,b)}(k)|=\aleph_0$?

The exact locator is [the versioned preprint, Question 5.2](https://arxiv.org/html/2601.10561v1#S5.Thmquestion2). The [journal text](https://www.technoskypub.com/wp-content/uploads/2026/04/acm-090111.pdf) has DOI 10.62072/acm.2026.09011. The existing Library citation `andoyo2026pisanolegendrecollision` identifies this same article and is reused.

Statement echo: $F_0=a$, $F_1=b$, $F_{n+2}=F_{n+1}+F_n$; $\pi_p(a,b)$ is the least positive scalar period, valid at every index including zero. For $j\in\{-1,0,1\}$, $N_j$ counts indices $0\le n<\pi_p(a,b)$ with Legendre symbol $j$, with multiplicity. Set $K=N_1-N_{-1}-N_0$ in the integers, $\chi(a,b)=\{K(p,a,b):p\text{ odd prime}\}$, and $\vartheta_{(a,b)}(k)=\{p:p\text{ odd prime},K(p,a,b)=k\}$. The Lean `claim` asserts that every such attained fiber is infinite, equivalently countably infinite because it is a subset of the natural numbers. Seeds are signed and may be nonprimitive; primes dividing both are included.

## Motivation

The [preregistered assertion](https://github.com/the-omega-institute/trureturing/issues/22882#issuecomment-6453955282) is the original universal Question 5.2. Its infinitude requirement concerns the exact unbounded fiber, rather than the number of observed occurrences in a prime sample.

## Gap

The proposed universal infinitude fails at a common prime divisor of permitted seeds. For $(a,b)=(0,3)$, the zero orbit at three gives an attained odd balance, while every other odd prime has an even period and therefore an even balance. No mathematical gap remains for this literal counterexample. Worldwide literature priority remains unverified.

## Route

The existing compiled candidate is `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.lean`. Its symbolic norm identity is

$$F_{n+1}^2-F_nF_{n+1}-F_n^2=(-1)^n(b^2-ab-a^2).$$

Finite invertible recurrence-state dynamics gives a positive period. If the norm is nonzero modulo an odd prime, returning the state forces even period. For $(0,3)$ the norm is nine, nonzero whenever $p\ne3$. Legendre trichotomy gives $\pi=N_1+N_{-1}+N_0$, so $K=2N_1-\pi$ is even at every other odd prime. At three the zero orbit has least period one and $K=-1$. Consequently $\vartheta_{(0,3)}(-1)=\{3\}$.

## Falsifier

A single nonzero integer seed pair and an attained value with finite exact odd-prime fiber falsify the source assertion. The pair $(0,3)$, value $-1$, and fiber $\{3\}$ meet this criterion. The result does not depend on excluding primes dividing both seeds.

## Evidence

`claim : Prop` retains the complete source quantifiers, and the sole public theorem `result : Not claim` negates them. The eight private helpers `recurrence_state`, `period_exists`, `recurrence_norm`, `period_even`, `count_partition`, `zero_mod_three`, `value_at_three`, and `fiber_subset` are all consumed. Public imported definitions `F`, `ScalarPeriod`, `pi`, `signCount`, `K`, and `chi` retain their original meanings. The Blueprint Scribe binds `result` to this problem with `OpenProblemResolutionClaim(Refuted)` and explains the norm and partition arguments.

The admission basis is `open-problem-resolution (#22882; Refuted)`, with content on the live proof path. Utility is `none`: the contribution is an unbounded symbolic prime obstruction; the zero orbit is a consumed base case, not a separate computational-instance delivery. The result therefore has no utility-refutation audit exemption. Its four-slot audit remains unfinished under [#22882](https://github.com/the-omega-institute/trureturing/issues/22882): a successfully compiled complete source-owner registration and current source-selection binding evidence for the dependent prime-fiber family are not available. No validated registration is asserted. Imported Q5.3 audit boundaries remain under #22843.

## Triage

The original Question 5.2 is refuted by the exact singleton fiber. This conclusion is not replaced by a restricted target. An internal successor candidate is: for every coprime integer pair $(a,b)$ and every $k\in\chi(a,b)$, the exact odd-prime fiber is infinite. That candidate is untested and needs separate source/literature screening and preregistration; no answer or external open-problem credit is asserted for it.

## ASSUMED-UNVERIFIED

The source and bounded literature checks supplied with #22882 found no exact prior settlement in their searched scope. Completeness over the worldwide literature and Lean ecosystem is unverified; no worldwide-priority claim is made. The result has canonical Frozen membership and imports the canonical Q5.3 module. Exact-head admission and integration remain separate duties; an unfinished registration is neither a mathematical gap nor validated audit evidence.
