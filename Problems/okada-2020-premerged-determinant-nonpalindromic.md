---
slug: okada-2020-premerged-determinant-nonpalindromic
bibkey: okada2020merged
doi: 10.48550/arXiv.2003.02112
url: https://arxiv.org/abs/2003.02112v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.result
---

# Okada's pre-merged Gaussian determinants of width at least three are not almost palindromic

## Problem

So Okada, *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*, arXiv:2003.02112v2 (2020 preprint, revised 2024), states the following in the subsection “On the almost palindromicity”, conjecture labelled `conj:palindromic-width-three`, `phases.tex`, lines 8770–8779:

> Let $\mu\in\Z_{\geq 3}$. Then, $\dt(U)_{a}^{b}(\mu,\iota^{\mu}(1),\iota^{\mu}(1), 0, \iota^{\mu}(q))$ is not an almost palindromic $q$-polynomial, provided $\tp{\mu,a,b}$ is almost strictly pre-fitting.

The quotation retains the source macros: `\Z` denotes $\mathbb Z$, `\dt` denotes $\tilde d$, and `\tp` prints a tuple. The source defines almost strictly pre-fitting by $0\le a_1<\cdots<a_\mu\le b_1<\cdots<b_\mu$ (lines 8337–8346), and almost palindromic by equality of the coefficient list with its reverse after zero coefficients are omitted (Definition `def:almost`, lines 8503–8512).

At these parameters, the pre-merged determinant is the integer polynomial $P=A-B$, where $A=\prod_{i=1}^{\mu}{b_i\brack a_i}_q$ and $B=\prod_{i=1}^{\mu}{b_i\brack a_{\mu+1-i}}_q$. This specialization follows from the source's tuple Gaussian product (lines 3505–3519), unit base-shift factors (lines 5942–5955), and pre-parcel and pre-merged determinant definitions (lines 6005–6048). The scalar degree shift is zero.

Issue [#25498](https://github.com/the-omega-institute/trureturing/issues/25498) fixes the reading: for every natural $\mu\ge3$ and every such pair of tuples, the nonzero coefficients of $P$, ordered by increasing degree, do not form a palindrome. This is proved.

## Motivation

Okada's paper studies merged-log-concavity, unimodality and palindromicity of expressions constructed from Gaussian binomial coefficients, with applications to ideal boson-fermion gases. This conjecture isolates a combinatorial distinction between width two and every larger width. It asks whether reversing the lower-index tuple leaves an unavoidable asymmetry even when gaps in the coefficient sequence are ignored. The settlement concerns that coefficient symmetry at unit weights, unit base shifts and zero degree shift.

## Gap

The bounded literature check recorded in #25498 reports:

- the conjecture remains in arXiv:2003.02112v2, and the orchestrator's arXiv author search found no later paper by So Okada;
- the orchestrator's Semantic Scholar citation query returned an empty list, while the search contribution reported zero INSPIRE citing records; OpenAlex was rate-limited and was not counted;
- the search contribution reported no matching endpoint comparison in arXiv:2510.14124v2, 2302.04067v2, 2111.03369v2 and 2004.01968v1, or in the Reiner–Stanton and Sagan statements cited by Okada;
- the orchestrator's Zenodo phrase searches and repository searches found no prior settlement in their searched scope.

`not-found-in-searched-scope`.

## Route

Use zero-based indices, as in Lean. Fix $\mu\in\mathbb N$ and $a,b:\mathrm{Fin}\,\mu\to\mathbb N$ with $3\le\mu$, `StrictMono a`, `StrictMono b`, and $a_i\le b_j$ for every $i,j$. These are the hypotheses of `index_bounds`, `low_end`, `reversed_degree_gap` and `high_end` below. Put $t=b_0-a_{\mu-1}$, $r=t+1$, $c=\mu$ if $a_0>0$ and $c=\mu-1$ otherwise, and $d=\sum_i a_i(b_i-a_i)$. All subtractions in these definitions are natural subtraction.

1. **Factorial cancellation.** Write $Q_n=\prod_{h=1}^{n}(1-q^h)$, the private definition `qFactorial`. For natural $n,k$ with $k\le n$, `factorial_identity` gives ${n\brack k}_q Q_kQ_{n-k}=Q_n$. For any natural $\mu$ and natural tuples satisfying $a_i\le b_j$ for every $i,j$, `factorial_product_identity` gives $A\prod_iQ_{b_i-a_i}=B\prod_iQ_{b_i-a_{\mu-1-i}}$. Under the full fixed hypotheses, `index_bounds` gives $b_i-a_i\ge t+2$ for every $i$, the reversed difference $t$ at index zero, and $b_i-a_{\mu-1-i}\ge t+2$ for every index with $i>0$.
2. **The low end.** For a commutative ring $S$ and ring homomorphism $\phi:\mathbb Z[q]\to S$, `qFactorial_image_stable` gives $\phi(Q_n)=\phi(Q_m)$ when $m,n\in\mathbb N$, $m\le n$ and $\phi(q^{m+1})=0$; `qFactorial_image_unit` makes every $\phi(Q_n)$ a unit when $\phi(q)$ is nilpotent. Apply these in $\mathbb Z[q]/(q^{t+3})$, with $m=t+2$, to the preceding identity. Cancellation gives $B\equiv A(1-q^{t+1})(1-q^{t+2})\pmod{q^{t+3}}$. For a positive natural width, strictly increasing natural $a$, and natural $b$ satisfying $a_i<b_i$ for every $i$, `gaussian_product_low` gives $A_0=1$ and $A_1=c$. Under the full fixed hypotheses, `low_end` therefore gives $P_r=1$, $P_{r+1}=c+1$, and $P_n=0$ for every $n<r$.
3. **The high end.** For natural $n,k$ with $k\le n$, `gaussian_shape` states that ${n\brack k}_q$ is monic, has natural degree $k(n-k)$ and equals its polynomial reverse. For any natural width and natural tuples with $a_i\le b_i$ for every $i$, `gaussian_product_shape` gives the corresponding product properties. Under the full fixed hypotheses, `reversed_degree_gap` gives $\sum_i a_{\mu-1-i}(b_i-a_{\mu-1-i})+2\le d$. Thus the reversed product cannot change the top two coefficients of $A$. With those same full hypotheses, `high_end` gives $\operatorname{natDegree}P=d$, $P_d=1$, $P_{d-1}=c$, and $d\ge t+4$.
4. **The coefficient-list contradiction.** `palindrome_contradiction` applies to an integer polynomial $p$ and natural $r,d,c$ when $p_r=1$, $p_{r+1}=c+1$, $\operatorname{natDegree}p=d$, $p_d=1$, $p_{d-1}=c$, every coefficient below $r$ is zero, $c>0$, $r+1<d-1$, $c+1\ne c$, and `IsAlmostPalindromic p` holds. It derives a contradiction by comparing the second and penultimate entries in the sorted-support coefficient list. For $p=P$, `result` obtains every coefficient and degree condition from `low_end` and `high_end`; the fixed hypotheses also give $c\ge2$ and the required separation.

## Falsifier

The proof would not answer the source if it used ordinary coefficient reversal without omitting zeros, restricted the width to three, or changed the pre-merged expression. The module uses:

- `IsAlmostPalindromic f`, defined as `List.Palindrome` of the coefficients on `f.support`, sorted by increasing degree; in particular, the zero polynomial has the empty palindromic list;
- `preMerged a b`, exactly the difference of Gaussian products above, with `Fin.rev` sending $i$ to $\mu-1-i$;
- the integer Gaussian polynomial `LiUncuDefs.gauss`, defined by the $q$-Pascal recurrence, with value one at lower index zero and value zero when the lower index exceeds the upper index;
- every natural width $\mu\ge3$, strictly increasing natural tuples, and the cross condition $a_i\le b_j$ for every $i,j$, equivalent here to $a_{\mu-1}\le b_0$.

Viewing these integer coefficients as rational coefficients changes neither their support nor their equality. The allowed boundary $a_0=0$ is included through the case $c=\mu-1$; no density assumption is imposed on the intermediate coefficients.

## Evidence

The canonical source is `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.lean.json`.

Declaration statements:

- `result`: `sha256:47ab1b49abe9da5dc5b79528eb6b912451f58c9282a1848dc02a277fe6a0ef4e`;
- `claim`: `sha256:4151ca11cba5d60d2909ef2bebac64bc50c6057ddaecd4feb6f0683747afa521`.

## Triage

Tier 1 conjecture of a 2020 preprint retained in its 2024 v2, preregistered in issue #25498 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $\mu\ge3$ and every pair of strictly increasing natural tuples $a,b:\mathrm{Fin}\,\mu\to\mathbb N$ with $a_i\le b_j$ for every $i,j$, `preMerged a b` is not almost palindromic: its nonzero coefficients in increasing degree do not form a palindrome.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and scope.* Under the full hypotheses stated in Route, the endpoint statements of `low_end` and `high_end` locate a mismatch of exactly one between the second and penultimate nonzero coefficients, while `high_end` supplies their separation. The contradiction uses no information about coefficients strictly between those positions. Missing degrees there therefore cannot restore a palindromic list, and the argument covers arbitrary width and arbitrary tuple gaps within the stated hypotheses. It gives no positivity, density or unimodality assertion for the interior.
- *Width and strictness boundaries.* For every natural $n\ge1$, width-two tuples $a=(0,1)$ and $b=(n,n+1)$ give $P=q^n$, since the Gaussian recurrence at lower index one is ${n+1\brack1}_q={n\brack1}_q+q^n$; the singleton coefficient list is palindromic. With $a=(0,0,1)$ and $b=(n,n+1,n+2)$ the same recurrence gives $P=q^n+q^{n+1}$, whose nonzero coefficient list is $(1,1)$, so weakening strict increase of $a$ also permits almost palindromicity. For a constant upper tuple, the two Gaussian products differ only by a permutation of their factors and their difference is zero, so weakening strict increase of $b$ permits almost palindromicity as well. These arguments explain why those hypotheses cannot simply be dropped.
- *Overall monomial shifts.* Under the hypotheses of `result`, multiplication of $P$ by $q^s$, for any natural $s$, translates its support degrees by $s$ and preserves their ordered coefficient values, hence preserves non-almost-palindromicity. This observation concerns an overall shift; the source's parameter $e$ instead shifts only the reversed product.
- *Effect on the paper and neighbouring questions.* The width-three premise invoked in Okada's width-two discussion (`phases.tex`, lines 8783–8788) is supplied. That passage describes the width-two expression as one that “would not be palindromic” when $a_2-a_1\ge2$ and $b_2-b_1\ge2$, invoking the conjecture's $\mu=3$ cases. Its reduction to width two remains `open` here and is not a conclusion of `result`. The width-two counting conjecture `conj:non-palindromic-seq` (lines 8794–8807), base-shift transitivity `conj:transitivity-palindromicity` (lines 8838–8851), density conjecture `conj:density`, width-two unimodality conjecture `conj:unimodal-width-two`, and physical phase-transition statements remain outside this settlement. In particular, the proved unit-base-shift, zero-degree-shift case supplies no transitivity step to other base shifts or degree shifts.

## ASSUMED-UNVERIFIED

The literature check is bounded to the searches recorded in #25498 and does not establish exhaustive worldwide novelty or priority. The author search, citation-service readings, Zenodo searches, and readings of the four later preprints and the Reiner–Stanton and Sagan statements are attributed to the issue's orchestrator or search contribution; they were not independently reproduced for this dossier. The arXiv v2 source, its definitions and quoted conjecture were read directly.

The statements labelled “Argued, not formalized” are not additional Lean conclusions. In particular, the symbolic width-two and weakened-strictness examples, invariance under an overall monomial shift, and the assessment of consequences for other source statements are not formalized here. The source's proposed reduction from width three to its neighbouring width-two claim remains unverified here. General weights, nonunit base shifts, nonzero degree shifts, density, unimodality, counting and physical claims are not settled by this module.
