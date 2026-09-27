---
bibkey: sun2026generalizations
authors: Zhi-Hong Sun
year: 2026
title: Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers
doi: 10.48550/arXiv.2608.13192
url: https://arxiv.org/html/2608.13192v1
claim: "Conjecture 5.2 states both strict lowercase g and v Turan inequalities for every positive index on the complete real domains x <= -1 and x <= -1/8."
strata_touched:
  - D5/S1/Recurrence/Sun/Sequences
  - D5/S1/Recurrence/Sun/GEndpoint
  - D5/S1/Recurrence/Sun/GStrict
  - D5/S1/Recurrence/Sun/VTail
  - D5/S1/Recurrence/Sun/VStrict
license: citation-only
triage: anchor
---

# Sun's two lowercase Turan conjectures

Zhi-Hong Sun, *Generalizations of the Christoffel-Darboux formula and
congruences involving Apéry-like numbers*, arXiv:2608.13192v1,
13 August 2026. Source URL: https://arxiv.org/html/2608.13192v1.
DOI: 10.48550/arXiv.2608.13192. The source's Conjecture 5.2 is a single
two-clause question; neither clause alone settles it.

## Verified locator

DOI: 10.48550/arXiv.2608.13192.
Versioned source URL: https://arxiv.org/html/2608.13192v1.
The displayed lowercase definitions and Conjecture 5.2 are the source
scope checked here; no theorem about the older uppercase sequences is
substituted for either negative-domain clause.

## Source statement and definitions

The paper defines lowercase sequences over real arguments by

$$
g_0(x)=1,\quad g_1(x)=\frac{x+1}{2},\quad
(n+1)^2g_{n+1}(x)=\left(2n(n+1)+\frac{x+1}{2}\right)g_n(x)-n^2g_{n-1}(x),
$$

and

$$
v_0(x)=1,\quad v_1(x)=x,\quad
(n+1)^3v_{n+1}(x)=(2n+1)(n(n+1)+x)v_n(x)-n^3v_{n-1}(x),
$$

with both recurrences for every integer `n >= 1`. Conjecture 5.2 states,
for every such `n`,

$$
g_n(x)^2>g_{n-1}(x)g_{n+1}(x)\quad(x\leq-1),\qquad
v_n(x)^2>v_{n+1}(x)v_{n-1}(x)\quad(x\leq-1/8).
$$

Both endpoints belong to the source domains. Lean `Sequences.g` and
`Sequences.v` use the quotient form of these same multiplied recurrences.
`GStrict.g_strict_turan` and `VStrict.v_strict_turan` prove the two literal
lowercase conclusions for arbitrary positive natural index and every real
argument in the respective closed domain. Reversing the two factors in the
second product uses commutativity of real multiplication.

## Prior art and limits

The paper relates uppercase `G_n,V_n` to lowercase `g_n,v_n` at argument
`2x^2+2x+1`. For real `x`, that argument is at least `1/2`; the uppercase
results in Jianxi Mao and Qiqi Xiao, *Second order determinants for
three-term recurrence polynomial sequences*, *Filomat* 40(9) (2026),
3169-3178, Theorems 3.2 and 3.6, therefore do not cover either negative
lowercase domain. Y.-T. Li and Z.-H. Sun, arXiv:2609.28098v1, Theorem 3.3
and Remark 3.1 address p-adic material around Conjecture 4.2, not these
real inequalities. Krasikov's weighted tail result is recorded separately
in `D5/L/Recurrence/krasikov2011turan`; it requires additional local and
endpoint arguments for this target.

The bounded source/version/formula searches reported in the source
assessment did not locate an exact later proof through 25 September 2026.
This is a search limit, not a claim of worldwide absence or priority.
The bodies of Abreu--Bustoz and Bustoz--Ismail were unread in that
assessment; they supply neither a verified match nor negative evidence.
No external Lean code was ported.
