---
slug: palindromic-density
bibkey: freeman2017generalized
doi: 10.1216/RMJ-2018-48-1-219
url: https://arxiv.org/abs/1604.06755v2
triage: theorem
motivation_gids:
  - D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result
---

# Freeman's upper-limsup density bound

## Problem

David M. Freeman, *Generalized Palindromic Continued Fractions*, arXiv:1604.06755v2, Conjecture 7.1, page 10:

> For $m\in\mathbb{N}$ and $A\in\mathbb{N}^{\mathbb{N}_0}$ an $m$-palindromic sequence that is not eventually periodic, we have $d_m([A])\leq1/\varphi$. Furthermore, for $r,s\in\mathbb{N}$ with $r\not=s$, we have $d_m([F(m,r,s)])=1/\varphi$.

The first sentence is refuted. The separate Fibonacci equality remains open here. Section 6 defines $d_m$ as the upper limsup of the ratios of consecutive lengths in the complete increasing list of qualifying prefixes; it is not a lower limsup or the reciprocal of a forward-ratio limsup.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $m$ is a positive integer | `claim` quantifies natural `m` with `0 < m` | Lean naturals include zero, so positivity is explicit. |
| Every digit of $A$ is positive | Natural sequence `A` with pointwise positivity | Includes the initial digit. |
| $[U]=m[\widetilde U]$ | `IsFiniteMPalindrome`, rational `finiteCF` and `List.reverse` | Nonempty positive lists; the empty evaluator value is excluded. |
| Prefix length counts digits | `PrefixLength`, positive `n` and `List.ofFn` | A prefix ending at index $i$ has length $i+1$. |
| Infinitely many qualifying prefixes | `IsMPalindromic`, an infinite set of lengths | No prescribed subsequence replaces the whole set. |
| Complete increasing prefix list and upper limsup | `density`, `Nat.nth` and `Filter.limsup` at `Filter.atTop` | Numerator and denominator are cast to reals. |
| Not eventually periodic | Existing `D5.S1.Words.Complexity.EventuallyPeriodicWord` | Its positive-period tail condition is the source condition. |
| Bound $1/\varphi$ | `claim`, `Real.goldenRatio` | $\varphi=(1+\sqrt5)/2$. |
| Negation of the first sentence | `result` | No additional hypothesis; the Fibonacci sentence is outside `claim`. |

The finite evaluator is Mathlib's `GenContFract.convs'` on the source's finite digit lists. The proof directly consumes `WordPower.wordPower`, `WordPower.length_wordPower` and `WordPower.wordPower_getElem?`; no duplicate word-power definition is introduced.

## Motivation

Preregistration [#22972](https://github.com/the-omega-institute/trureturing/issues/22972) supplies the verbatim source and quantified target. The settling GID is `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result`; its admission basis is `open-problem-resolution (#22972; Refuted)`, its generality is `G`, and its utility is `none`. The settlement is a symbolic construction and limit argument with no finite certificate.

## Gap

Finite scans cannot establish infinite aperiodicity or the value of the upper limsup. The needed statements concern the actual next qualifying prefix, including any qualifying prefixes not nominated by the construction. Journal-version agreement and exhaustive priority clearance remain unverified.

## Route

Set $m=2$, $r=2$, $s=3$. Let $U_0=(4,2)$ and

$$U_{k+1}=U_k^{k+2}(6,3)^{k+1}U_k^{k+2}.$$

The nested positive stages define an infinite word $A$. Freeman's Lemmas 3.1–3.2 give the matrix criterion: if $M(U)=\begin{pmatrix}p&q\\u&v\end{pmatrix}$ for a positive nonempty word, then $[U]=m[\widetilde U]$ exactly when $q=mu$. The proof supplies the rational-evaluator bridge and applies the weighted-transpose construction to the stages and their powers.

Both $t_k=(k+1)|U_k|$ and $t'_k=(k+2)|U_k|$ qualify. If $L_{i_k}=t_k$ in the complete qualifying list, then $L_{i_k+1}\le t'_k$. Thus $L_{i_k}/L_{i_k+1}\ge(k+1)/(k+2)$ at unbounded indices. All ratios lie between zero and one, so the upper limsup is one. Arbitrarily long $(6,3)$ blocks followed by a digit $4$ exclude every eventual period. Since $1/\varphi<1$, the universal upper bound fails.

## Falsifier

A mismatch between the source's upper-limsup convention and `claim` would invalidate the source correspondence. Failure of the finite evaluator bridge, prefix nesting, positive-digit condition, aperiodicity or the actual-successor bound would invalidate this proof route. Finite scans alone are not a falsifier of the universal assertion.

## Evidence

The module's public `result` proves the literal type `¬ claim`. Its private `finiteCF_eq_p_div_u` and `finiteCF_mul_reverse_iff` supply the exact evaluator/matrix bridge; `qualifying_pow` supplies the qualifying prefixes; `limitA_pos` and `limitA_aperiodic` supply positivity and nonperiodicity; `witness_density_one` proves density exactly one, using `limsup_nth_ratio_one` and `nth_successor_bound` for the complete list.

The four-slot escape audit of `D5.S1.Depth.ContinuedFractions.FreemanPalindromicDensityRefutation.result` is unfinished: [#27283](https://github.com/the-omega-institute/trureturing/issues/27283). No Reg registration is delivered. The actual density readout still lacks compiled observational-dependence and lawful source-selection/reconstruction evidence. `utility: none` provides no refutation exemption; no `declared_validated` status is asserted.

### Experiment

[Exact finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/7abc41a29f3c5f18e4594875e8644e7d6dc5a2e1/docs/reports/palindromic-continued-fraction-density). Command: `git -C /Users/auric/trureturing-experiments show 7abc41a29f3c5f18e4594875e8644e7d6dc5a2e1:docs/reports/palindromic-continued-fraction-density/check.py | python3`, with pipeline failure propagation enabled; exit 0. Script SHA-256: `208e436c59caaf1d4b58d24649136c3283db749f4176620af2e8de066518c19e`.

The checker covers 24 triples with $2\le m\le5$, $1\le r,s\le3$, $r\ne s$, scanning all 5,188 positive prefix lengths through encoded stage 4 for each triple: 124,512 positions and 96 nominated pairs. At $(m,r,s)=(2,2,3)$ the nominated actual successive ratios are $1/2,2/3,3/4,4/5$. It also checks 3,279 words of lengths 1–7 over $\{1,2,3\}$, 324 weighted-transpose pairs, source identities and the length/ratio recurrence for $k=0,\ldots,99$. Its tail-start and period screen covers only $0\le N\le32$ and $1\le p\le32$ and is not an infinite aperiodicity certificate.

## Triage

1. **Proved, kernel-checked:** the fixed witness refutes the exact upper-limsup bound (`result`); its density is exactly one (`witness_density_one`).
2. **Proved, kernel-checked:** dense clusters of qualifying powers force upper limsup one, through `qualifying_pow`, `nth_successor_bound` and `limsup_nth_ratio_one`. The complete successor bound permits additional qualifying prefixes between the nominated lengths.
3. **Computed:** the pinned experiment checks all 24 triples and complete prefix scans through encoded stage 4, with the command, exit code and script identity above. No infinite conclusion follows from this computation.
4. **Open:** uniform Lean extension to every $m\ge2$ and every distinct positive $r,s$. The preregistration supplies a paper route; this module fixes $(m,r,s)=(2,2,3)$.
5. **Open:** a liminf replacement, the separate Fibonacci equality and a sharper neighbouring classification.
6. **Open:** the journal-version formulation and exhaustive priority clearance. Literature completeness is `ASSUMED-UNVERIFIED`.

### What the settlement shows

**Proved in this module:** arbitrarily late clusters of qualifying powers, together with the actual-successor inequality, force the upper limsup to one. Large gaps between clusters do not change this conclusion. The aperiodicity argument uses separator digits rather than a finite period search. The failure is therefore in the asserted universal upper bound for the source's upper-limsup convention.

**Proved in prose:** for any increasing positive length list, each consecutive ratio is at most one, so one is the sharp universal upper bound whenever such a density is defined. This is the nearest surviving upper bound. A liminf replacement is a different assertion and is open here. The independent Fibonacci equality is unchanged by this refutation. No source theorem relying on Conjecture 7.1 was identified in the inspected material; no such theorem is claimed settled by this module.

### Literature status

The preregistration's source and literature screen covers the arXiv v2 source, Crossref metadata, OpenAlex and Semantic Scholar citation lists, Longhi–Murru–Saettone's arXiv:2302.04017, arXiv searches and the other services named in #22972. It found no settlement in the inspected scope. Crossref identifies the journal article as *Rocky Mountain Journal of Mathematics* 48(1), 219–236. Citation indexes and queried services do not give exhaustive priority clearance.

## ASSUMED-UNVERIFIED

The journal full text was inaccessible in the source screen, so agreement with arXiv v2's upper-limsup convention is unverified. Freeman's later epicycloid paper was not read in full. Literature completeness and priority remain unverified. The uniform formal family, liminf replacement, Fibonacci equality and sharper classification remain open. Escape registration remains unfinished under #27283.
