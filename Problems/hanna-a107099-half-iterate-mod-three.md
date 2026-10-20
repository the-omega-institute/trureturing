---
slug: hanna-a107099-half-iterate-mod-three
bibkey: hanna2005a107099
doi: null
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.result
url: https://oeis.org/A107099
---

## Problem

Paul D. Hanna's OEIS A107099 comment states: "Coefficients [x^n] A(x) = 0 (mod 3) except at n = 3^k (conjecture)." The Name states: "G.f. satisfies A(A(x)) = x + 4*x^3, where A(x) = Sum_{n>=0} a(n)*x^(2*n+1)." The displayed expansion begins with $x$, fixing the linear coefficient to one.

The exact binding claim of [#18858](https://github.com/the-omega-institute/trureturing/issues/18858) includes existence and integrality: there exists an odd $A\in\mathbb Q[[x]]$ with linear coefficient one and $A\circ A=x+4x^3$; for every such $A$ and every $n\in\mathbb N$, its coefficient equals an integer $m$, and $3\mid m$ whenever $n$ is not a power of three. No nonvanishing assertion at powers of three is imposed.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Odd generating function | `IsGF`: every even coefficient vanishes | The literal preregistered condition, including degree zero. |
| Expansion begins with $x$ | `IsGF`: linear coefficient one | The source normalization. |
| $A(A(x))=x+4x^3$ | `IsGF`: formal self-substitution equation | Substitution is Mathlib formal power-series substitution. |
| Coefficients vanish modulo three outside $3^k$ | `claim`: every natural degree has an integer coefficient representative and the off-power implication | The rational coefficient is compared with the cast of that integer. |
| The entry defines a generating function | `claim`: an `IsGF` solution exists | Prevents vacuity. Universal solution quantification introduces no additional hypothesis. |

## Motivation

The congruence requires a common integral half-iterate and its reduction modulo three. Rational coefficient uniqueness connects every source solution to that same integral construction.

## Gap

The literature screen recorded in #18858 found no proof or refutation in the entry and its links, the searched OEIS-proof papers, OEIS Open and formal-conjecture catalogues. The screen includes the GPT Pro literature reading named there. Completeness and continued external open status are `ASSUMED-UNVERIFIED`. The conjecture is an explicitly published OEIS question; no novelty of the general lifting method is claimed.

## Route

An integer approximation starts at $X$. The compositional residual is divisible by four when the approximation has the form $X+2B$. An even correction cancels the next residual coefficient. Compatible finite-degree approximations define an integral series satisfying the equation. The coefficient of a change in its compositional square is twice the coefficient of the change itself, so strong induction proves uniqueness whenever two is nonzero in a domain. Reflection through $-X$ then proves oddness over the rationals.

Over $\mathbb F_3$, Frobenius and substitution preserve support on powers of three. Comparing a solution with its truncation and using the triangular coefficient identity forces every off-support coefficient to vanish. Rational uniqueness transfers the constructed integer coefficients to every `IsGF` solution.

The actual reused owners are `CompositionalSquareDyadicDenominators.Agree`, `agree_subst`, `composition_top`, `residual`, `residual_four`, `C_dvd_iff_coeff`, and `CubicFifteenSubstitutionParity.prime_power_subst`. Their original statements and proofs are retained. The formal route uses support closure and induction; it does not construct a Frobenius-symbol square root.

## Falsifier

A source solution with a nonintegral coefficient, or an off-power coefficient not divisible by three, would contradict `result`. A series without the source normalization would address a different question.

## Evidence

`D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree.result` proves the exact `claim`. The admission basis is `open-problem-resolution (#18858; Proved)`, with no anchor atom. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished under [#19129](https://github.com/the-omega-institute/trureturing/issues/19129). Its targets are `HannaHalfIterateCubicModThree.result`, `CompositionalSquareDyadicDenominators.agree_subst`, `composition_top`, `C_dvd_iff_coeff`, `residual_four`, and `CubicFifteenSubstitutionParity.prime_power_subst`; the published owner definitions `CompositionalSquareDyadicDenominators.Agree` and `residual` are also included in the delivery audit. No Reg mirror is delivered: faithful source reconstruction, an enrolled complete readout, and variation, sensitivity and observational-dependence evidence are missing. No `declared_validated` status is claimed.

### Experiment

[Published checker and data](https://github.com/the-omega-institute/trureturing-experiments/tree/f2c2a220d884330280c621e6301102b442b646e5/docs/reports/oeis-a107099-hanna-half-iterate-mod3).
Command: `python3 check.py 243 b107099.txt`, run in that directory; exit 0, `RESULT PASS`. The pinned `check.py` SHA-256 is `3af136655f74bc1a9b57b64f0e0cb9d8532f6f3b7e0229df5043f4fc581298e1`.
The self-composition equation holds through degree 243, the series is odd in that range, and $a(0),\ldots,a(121)$ match the b-file. Every off-power coefficient through degree 243 vanishes modulo three. At degrees $1,3,9,27,81,243$ the residues are $1,2,1,1,2,1$, matching $\binom{1/2}{k}$ modulo three for $0\le k\le5$. This computation establishes no unbounded result by itself.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| Exact binding settlement | Proved, kernel-checked | `HannaHalfIterateCubicModThree.result`. |
| Novelty basis | Literature reading; completeness `ASSUMED-UNVERIFIED` | External named conjecture #18858; no new-method claim. |
| Support-induction formal route | Proved, kernel-checked | Private `half_mod_three_support` and `integer_reduction_support` on `result`'s proof path. |
| Integral solution and rational uniqueness | Proved, kernel-checked | Private `integral_equation`, `half_unique`, `half_odd`, `rational_integral_equation`, consumed by `result`. |
| Finite equation, b-file and residues | Computed | The pinned experiment above, exactly through degree 243 and sequence index 121. |
| Cubic parameter generalization | Proved in prose | The coefficient recursion and reduction argument below. |
| Lean formalization of the parameter generalization | Open | No general-parameter declaration is delivered. |
| Stronger binomial residue formula | Proved in prose | Additive-series symbol construction below; finite checks only through $k=5$. |
| Optional Lean formalization of the stronger binomial residue formula | Open | The public settlement asserts only off-power vanishing. |
| Vanishing at a power of three | Proved in prose below | $\binom{1/2}{6}=-21/1024$ implies zero residue at degree 729; not part of the finite computation. |
| Coefficient growth | Open | No growth or asymptotic estimate is asserted. |
| Source consequences | Proved in this module for the quoted conjecture | `result` establishes precisely the entry's off-power congruence; no additional dependent source theorem is identified in #18858. |
| Escape registration | Open | #19129 and the missing evidence above. |

### What the settlement shows

**Proved, kernel-checked.** The decisive mechanisms are the even integral correction invariant and strong induction on support after reduction modulo three. The unbounded conclusion is the exact preregistered claim, with existence and integer representatives. Only the private helpers just named and the public `result` supply these kernel-checked claims.

**Proved in prose.** Let $c\in\mathbb Z$ satisfy $4\mid c$, and write $A=x+2B$ with $B$ of order at least three. Expanding $B(x+2B)$ by the integral divided derivatives $D_jB=\sum_m b_m\binom mj x^{m-j}$ turns $A\circ A=x+cx^3$ into

$$B+\sum_{j\ge1}2^{j-1}B^jD_jB=(c/4)x^3.$$

The sum has finitely many contributions at each degree. In its nonlinear terms an occurrence of $b_m$ has degree at least $m+2$, because $B$ starts in degree three. Thus each $b_m$ is uniquely an integer polynomial in earlier coefficients and $c/4$. This constructs an integral $A$; the multiplier-two recursion gives uniqueness over $\mathbb Q$. If also $c\equiv1\pmod3$, reduction gives the same normalized half-square equation $\overline A\circ\overline A=x+x^3$. The coefficient recursion is unique over $\mathbb F_3$, so the same off-power support conclusion follows. For arbitrary $c\equiv1\pmod3$, the rational multiplier-two recursion instead lies in $\mathbb Z[1/2]\subset\mathbb Z_{(3)}$ and still admits this reduction. These parameter extensions are not Lean theorems in this delivery.

**Proved in prose.** The formal binomial series $s(F)=\sum_{k\ge0}\binom{1/2}{k}F^k$ belongs to $\mathbb Z[1/2][[F]]$: for $k\ge1$ its coefficient is $(-1)^{k-1}C_{k-1}/2^{2k-1}$, with $C_j$ the integer Catalan number. The formal binomial identity gives $s(F)^2=1+F$. After reduction modulo three, associate $\sum c_kF^k$ with $\sum c_kx^{3^k}$. Frobenius fixes each coefficient in $\mathbb F_3$ and sends $x^{3^j}$ to $x^{3^{j+1}}$, so multiplication of symbols becomes composition of these additive series. The symbol $s$ therefore supplies a normalized half-iterate of $x+x^3$. The triangular recursion's uniqueness identifies it with $\overline A$, proving $[x^{3^k}]A\equiv\binom{1/2}{k}\pmod3$. In particular $\binom{1/2}{6}=-21/1024$ is divisible by three in $\mathbb Z[1/2]$, so the coefficient at degree 729 vanishes modulo three. This explains why the source's exception does not assert nonzero residues. Formalizing this stronger formula is a follow-up; no additional declaration is delivered for it.

**Open.** No coefficient-growth result follows from the stated support argument. The source's quoted conjecture is settled; stronger residue formulas and any other source assertions keep their stated evidence boundaries.

## ASSUMED-UNVERIFIED

Literature-search completeness and the continued external absence of an earlier proof or refutation are not certified by Lean. The prose parameter and binomial arguments are not kernel-checked here. Escape registration is unfinished as disclosed above.
