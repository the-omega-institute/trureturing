---
slug: phunphayap-noppakaew-pongsriiam-2023-digit-sum-arcs
bibkey: phunphayap2023digitsumarcs
doi: 10.61091/um124-06
url: https://arxiv.org/abs/2303.13017v1
triage: theorem
motivation_gids:
  - D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.result
---

# Question 3 on outgoing digit-sum arcs

## Problem

Phunphayap, Noppakaew and Pongsriiam, *Directed graphs of integers with arcs
determined by an arithmetic function*, arXiv:2303.13017v1, Question 3
(Question 3.3 in Utilitas Mathematica 124, DOI 10.61091/um124-06), ask:

> We obtain in Theorem 2 that Out(s_b, n) contains every multiple of s_b(n). Does Out(s_b, n) contain an infinite number of positive integers that are not divisible by s_b(n)? When d = 1 and s_b(n) ≥ 2, the answer is yes. Can we determine a simple necessary and sufficient condition for the infinitely many elements in A ∩ Out(s_b, n) where A is the set of positive integers that are not divisible by s_b(n)? In that case, does Out(s_b, n) has a natural density?

For $b\ge2$ and $n\ge1$, write $s=s_b(n)$ and $d=\gcd(b-1,n)$.
The answer is that the difference set is infinite exactly when $d<s$, and
$\operatorname{Out}(s_b,n)$ has natural density $1/d$. It contains every
sufficiently large positive multiple of $d$.
Preregistration: [#19415](https://github.com/the-omega-institute/trureturing/issues/19415).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Base $b\ge2$ and positive $n$ | `claim` binders `b n : ℕ`, hypotheses `2 ≤ b`, `1 ≤ n` | Full parameter range. |
| Positive arc from $n$ to $u$, witnessed by positive $N$ with $n\mid N$ and $s_b(N)=u$ | `Out` | Both positivity clauses, divisibility and the complete digit-list sum are literal. |
| Infinitely many elements of $A\cap\operatorname{Out}$ | First conjunct of `claim` | Set difference by the multiples of $(\operatorname{Nat.digits}\ b\ n).sum$. |
| Necessary and sufficient condition | First conjunct of `result` | Biconditional with $\gcd(b-1,n)<s_b(n)$. |
| Natural density | Second conjunct of `result` | Real limit of the count in $[1,x]$, divided by $x$, equal to $1/d$. |
| Cofiniteness among positive multiples of $d$ | Private `out_cofinite`, consumed by `result` | An existential threshold; no numerical threshold is asserted. |

`Out` and `claim` inline the preregistered digit-sum and density expressions.
Proofs use `MaxDigitSumBase.digitSum` and the shifted
`AsymptoticDensity.HasDensity`; `density_count_shift` and `density_as_limit`
connect the interval conventions. No additional public mathematical statement
or strengthened hypothesis is used.

## Motivation

The criterion answers both parts of Question 3 uniformly, including bases and
integers for which $d>1$. The settling declaration is
`D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.result`.
The source note is `Library/Digit/phunphayap2023digitsumarcs.md`.

## Gap

The bounded literature screen in #19415 reads arXiv v1, the published question,
the authors' publication list, Sanna's complement identity (JIS 15, Lemma 6),
and Dartyge–Luca–Stănică. It finds no exact published settlement in that scope.
Balog–Dartyge, Stolarsky, Gelfond, and Dartyge–Tenenbaum beyond its theorem
statements remain unread. This is a literature reading with completeness
`ASSUMED-UNVERIFIED`; no originality claim is made for the complement identity
or numerical-semigroup saturation.

## Route

Concatenating digit blocks gives `sum_concat` and additive closure `out_add`.
The induction `sum_complement` yields
$s_b(b^L-1-m)+s_b(m)=(b-1)L$ for $m<b^L$.
Consequently `sum_multiple_complement` and `out_complement` put $(b-1)L$
in the arc set whenever $n<b^L$. Two adjacent lengths and the digit-sum
congruence yield `out_setGcd`. The consumed Mathlib theorem
`Nat.exists_mem_closure_of_ge`, together with `out_closure`, gives
`out_cofinite`.

For $s>d$, the progression $s(t+T)+d$ is injective, divisible by $d$, and
not divisible by $s$. Its tail lies in the arc set. For $s=d$, `out_dvd`
excludes all elements of the difference set. This proves `out_infinite_iff`.
The count of positive multiples of $d$ is $\lfloor x/d\rfloor$;
`density_cofinite_multiples` bounds its discrepancy from the arc count by a
constant. The consumed frozen `A400361PillaiMean.quotient_ratio_limit`
and `density_as_limit` establish the stated limit.

## Falsifier

A base $b\ge2$ and $n\ge1$ violating either conjunct of `claim`, or failing
qualitative saturation in $d\mathbb N$, would contradict the corresponding
kernel-checked declaration. Finite reachability computations cannot certify
the universal limit or exclude every possible counterexample.

## Evidence

The source module is
`D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.lean`.
Its public declarations are `Out`, `claim` and `result`; its 19 proof helpers
are private. The Scribe displays both definition bodies and the expanded
statement of `result`, with one `Proved` resolution claim.

Escape audit unfinished:
[#19481](https://github.com/the-omega-institute/trureturing/issues/19481).
The sole audit target is
`D5.S1.Digit.PhunphayapNoppakaewPongsriiamDigitSumArcs.result`.
No Reg mirror or validated registration is delivered. The missing evidence is
a faithful source reconstruction and equivalence bridge, actual-positive law,
whole-family variation and sensitivity, and observational dependence for the
quantified conjunction of infinitude and a real limit.

### Experiment

[Registered reachability checks](https://github.com/the-omega-institute/trureturing-experiments/tree/79e0c150f367061731111613899a1dd8fb0ac2e4/docs/reports/phunphayap-noppakaew-pongsriiam-2023-digit-sum-arcs-question-3).
Command: `python3 docs/reports/phunphayap-noppakaew-pongsriiam-2023-digit-sum-arcs-question-3/check.py`,
from the experiments checkout; exit 0, `RESULT PASS`.
Script SHA-256: `ff19effb32dcb8420e948ce3cda0b80a0a0c9e18d39e2b3df70da7e81253d00d`.
Exact digit-automaton reachability covers 165 pairs:
$b\in\{2,3,4,5,10\}$ and $n\in\{1,\ldots,30,99,121,343\}$.
For each pair, $L$ is the least positive integer with $b^L>n$,
$T_0=(b-1)((s/d)(L+1)-1)$, and $S_{\max}=T_0+6s+20$.
The automaton computes exactly the attainable sums up to $S_{\max}$.
It checks divisibility by $d$ within that range, attainment of the multiples
of $d$ in $[\max(d,T_0),S_{\max}]$, and existence of a sum in
$[T_0,S_{\max}]$ not divisible by $s$ exactly when $s>d$.
These are finite computations, separate from the universal Lean conclusions.

## Triage

Tier 1 external named question, #19415.
`admission_basis: open-problem-resolution (#19415; Proved)`;
`generality: I`; `utility: none`.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Exact Question 3 settlement | Proved, kernel-checked: public `result` gives the infinitude biconditional and natural density. Private `out_cofinite` proves qualitative cofiniteness. |
| Concatenation and additive closure | Proved, kernel-checked: `sum_concat`, consumed by `out_add`, and `out_closure`. |
| Two adjacent complement lengths determine the gcd | Proved, kernel-checked: `sum_complement`, `sum_multiple_complement`, `out_complement`, `out_setGcd`. |
| Numerical-semigroup saturation | Proved, kernel-checked: `out_cofinite` applies the consumed `Nat.exists_mem_closure_of_ge`. |
| Progression establishes infinitude; bounded discrepancy establishes density | Proved, kernel-checked: `out_infinite_iff`, `multiples_count`, `density_cofinite_multiples`, `density_as_limit`, consumed by `result`. |
| All $b\ge2$, $n\ge1$ | Proved, kernel-checked: the complete universal binders and hypotheses of `result`. |
| Positive Out witnesses | Proved, kernel-checked: `Out` includes both $u>0$ and $N>0$; `out_add`, `out_self` and `out_complement` construct such witnesses. |
| Density using $[1,x]$ | Proved, kernel-checked: the second conjunct of `result`; `density_count_shift` justifies the change from zero-based counting. |
| No changed definitions or weakened claim | Proved by literal statement comparison: the statement echo lists every supplied clause, with digit-sum and density bodies expanded. |
| Explicit saturation threshold | Open in this Lean delivery. `out_cofinite` gives existence of a threshold only; no explicit value is kernel-checked. |
| Density $1/d-1/s$ of the difference set | Open in this Lean delivery; no theorem here states that limit. |
| Question 1 equality classification | Open: this delivery does not classify when $\operatorname{Out}=d\mathbb N_{>0}$. |
| Sharp Frobenius bounds in Question 4 | Open: qualitative finiteness of missing multiples follows from `out_cofinite`, but neither a sharp bound nor the registered explicit threshold is formalized. |
| Novelty and prior art | Open (prior-art completeness); literature reading: no exact settlement found in the bounded screen in #19415. Complement identities and numerical-semigroup saturation carry no originality claim; completeness is `ASSUMED-UNVERIFIED`. |
| Registered numerical check | Computed: the pinned experiment, command, exit code, SHA-256 and exact 165-pair scope are given above. |

The result extends the qualitative support description to arbitrary $d$, and
settles the two requested clauses without requiring $d=1$. It introduces no
claim about the optimal threshold. The source's other theorems are not
reproved or altered; its Question 1 and sharp Question 4 remain outside this
settlement.

## ASSUMED-UNVERIFIED

Prior-art completeness is `ASSUMED-UNVERIFIED`, with the unread sources named
in Gap. The independent mathematical truth of the formal statements is
relative to the pinned Lean system and its standard axiom closure.
The escape audit is unfinished as recorded in #19481; the issue supplies no
registration evidence. The numerical experiment covers only its stated
finite parameter set.
