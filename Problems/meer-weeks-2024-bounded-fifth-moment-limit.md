---
slug: meer-weeks-2024-bounded-fifth-moment-limit
bibkey: meerweeks2024boundedmoments
doi: 10.1371/journal.pone.0297862
url: https://arxiv.org/abs/2308.05006v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.result
---

# The Meer–Weeks fifth-moment bounds for distributions bounded on one side

## Problem

D. J. Meer and E. R. Weeks, *Bounded distributions place limits on skewness and larger moments*, PLOS ONE 19, e0297862 (2024), arXiv:2308.05006v2, subsection “Higher order generalized moments”, `plos_latex_template.tex`, lines 506–510:

> One can immediately put in a value for $a$ of interest and get a potential limit of $D_n$. For example, for distributions bounded from below by $x_{\rm min}$ we conjecture
>
> $D_5 \geq D_{5,{\rm min}} = z^3 - z^1 + z^{-1} - z^{-3}$
>
> with $z = \delta / (1 - x_{\rm min}/\mu)$ as above. As with $D_3$, our conjectured $D_{5,{\rm max}}$ is a similar equation using $z = \delta / (x_{\rm max}/\mu - 1)$.

The quotation preserves the source's text and formula, with its displayed equation rendered as a separate mathematical paragraph. The v2 TeX was read directly; its MD5 is `4452c28a26c7a76c87642af46fe0c8a9`. The source defines central moments and standardized moments at lines 228–236, the original coefficient of variation at lines 290–295, and the shifted one-sided ratios at lines 397–409. See [the literature note](../Library/StatisticalMechanics/meerweeks2024boundedmoments.md).

Write $\nu$ for the probability law, distinguishing it from the paper's mean $\mu$, take $X(x)=x$, and put

$m=\int x\,d\nu(x)$, $v=\int(x-m)^2\,d\nu(x)$, $\sigma=\sqrt v$, $D_5=\int(x-m)^5\,d\nu(x)/\sigma^5$, and $F(z)=z^3-z+z^{-1}-z^{-3}$.

In Lean, these are `Defs.mean`, `centralMoment id 2`, `Real.sqrt`, the ratio involving `centralMoment id 5`, and `fifthBound`, respectively. Issue [#21300](https://github.com/the-omega-institute/trureturing/issues/21300) fixes the statement: for every Borel probability law on $\mathbb R$ with $\int|x|^5\,d\nu(x)<\infty$ and $v>0$, both of the following implications hold:

- for every real $L$, if $X\ge L$ almost surely, then $F(\sigma/(m-L))\le D_5$;
- for every real $U$, if $X\le U$ almost surely, then $D_5\le-F(\sigma/(U-m))$.

This statement is proved by `result : claim`. Attainment by two-point laws, also discussed in #21300, is not part of `claim` or `result`.

## Motivation

The paper relates support bounds, the coefficient of variation and standardized moments. Its fifth-moment conjecture asks whether the value obtained from a two-point distribution constrains every distribution with the same mean, variance and one-sided support bound. Resolving this replaces the numerical evidence for the fifth-moment envelopes in Fig. 2b by an inequality for arbitrary probability laws under the stated moment assumptions.

## Gap

The bounded literature check recorded in #21300 reports:

- the explicit conjecture in arXiv v2, with its retention in the PLOS ONE version;
- two citing works listed by OpenAlex for `W4391677775`: Meer et al., Phys. Rev. E 109, 064905 (2024), arXiv:2404.02316v1, concerning skewness bounds without a settlement, and a CEIDP 2025 paper checked only at abstract level;
- no reported entry in MathDB or `google-deepmind/formal-conjectures`, and no prior issue, module or dossier found by the preregistration's repository search.

`not-found-in-searched-scope`.

The explicit conjecture in the v2 TeX is independently checked. The other readings remain attributed to #21300. The issue places the classical ingredients in the Chebyshev–Markov–Krein moment-problem tradition; no novelty claim for that general theory follows from this settlement.

## Route

1. **Integrability and a positive mean gap.** For a probability measure $\nu$ on $\mathbb R$ with integrable $|x|^5$, every real $c$ and every natural $k\le5$, `integrable_centered_pow` gives integrability of $(x-c)^k$. For such a probability law with the additional assumptions $v>0$ and $X\ge L$ almost surely, where $L$ is real, `mean_gap_pos` gives $a=m-L>0$: a zero integral of the nonnegative function $X-L$ would force $X=L$ almost surely and $v=0$.
2. **A polynomial minorant.** For arbitrary real $a,b,y$ with $y\ge-a$, `polynomial_minorant` proves $Ay^2+By+C\le y^5$, where

   $A=-a^3+2a^2b-3ab^2+4b^3$,

   $B=2a^3b-4a^2b^2+6ab^3-3b^4$,

   $C=-a^3b^2+2a^2b^3-3ab^4$.

   Its certificate is $y^5-(Ay^2+By+C)=(y+a)(y-b)^2Q(y)$, with

   $Q(y)=y^2+(2b-a)y+3b^2-2ab+a^2=(y+b-a/2)^2+2(b-a/4)^2+5a^2/8\ge0$.

3. **Integration.** For a probability measure $\nu$ with integrable $|x|^5$, a real $L$ with $X\ge L$ almost surely, and $a=m-L>0$, `integrated_bound` sets $b=v/a$ and obtains $ab(b-a)(a^2+b^2)\le\int(x-m)^5\,d\nu(x)$. With $y=x-m$, the centered first moment is zero, the second is $ab$, and integration of the minorant gives the bound through $Aab+C=ab(b-a)(a^2+b^2)$.
4. **Standardization.** For real $a,v,M$ satisfying $a>0$, $v>0$ and $a(v/a)(v/a-a)(a^2+(v/a)^2)\le M$, `normalization` proves $F(\sqrt v/a)\le M/(\sqrt v)^5$ by the identity $F(\sqrt v/a)(\sqrt v)^5=a(v/a)(v/a-a)(a^2+(v/a)^2)$. For a probability measure with integrable $|x|^5$, $v>0$, a real $L$ and $X\ge L$ almost surely, `lower_bound` combines these lemmas to give the lower-support implication.
5. **Reflection.** For a probability measure with integrable $|x|^5$, $v>0$, a real $U$ and $X\le U$ almost surely, `upper_bound` applies the lower bound to the image law under $x\mapsto-x$. In this setting reflection preserves fifth absolute integrability, negates the mean and fifth central moment, preserves the second central moment, and supplies the lower bound $-U$. This gives the upper-support implication. `result` supplies both implications for every probability measure satisfying the finite fifth absolute moment and positive variance hypotheses.

## Falsifier

A mismatch of normalization, support assumptions or the reflected sign would prevent the theorem from settling the preregistered statement.

- The source's $m_n$ and $D_n$ are the central and standardized moments used here. Where the original $\delta=\sigma/m$ is defined, $\delta/(1-L/m)=\sigma/(m-L)$. The direct gap ratio also covers $m=0$, as does the source's shifted normalization.
- At the upper endpoint, the signed variable in the source's Eq. `DNlimits` is $\delta/(1-U/m)=-\sigma/(U-m)$ wherever these expressions are defined. Since $F(-z)=-F(z)$ for $z\ne0$, the preregistered upper reading is the reflected bound $-F(\sigma/(U-m))$.
- Support bounds in `claim` are almost sure inequalities for arbitrary real $L$ or $U$. Each implication has its own support hypothesis. No density, finite support, or bound on the opposite side is assumed.
- The finite fifth absolute moment and strictly positive second central moment are explicit premises. With these premises and the relevant almost sure support bound, `mean_gap_pos`, or its reflected application in `upper_bound`, establishes the positive mean gap. Point masses and undefined standardized moments at zero variance are outside the claim.

## Evidence

The canonical source is `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.lean` (193 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.lean.json`, statement `sha256:40afe881918c7cadb2fb29e7a88dda1d4172c5279a1becc26544c748457b3faf`.

Declaration statements:

- `result`: `sha256:9422da59a02a7422b78ea2e380d54026953f339dd3a89d75e3b3fb33c330f43a`;
- `claim`: `sha256:0137fdc8a401b9f7a16f36f8812050d2ccf43dc754837e53234380cf9a00223a`.

## Triage

Tier 1 conjecture of a 2024 journal paper, preregistered in issue #21300 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every Borel probability measure $\nu$ on $\mathbb R$ with integrable $|x|^5$ and $v=\int(x-m)^2\,d\nu(x)>0$, where $m=\int x\,d\nu(x)$, the conjunction holds: for every real $L$ with $X\ge L$ almost surely, $F(\sqrt v/(m-L))\le\int(x-m)^5\,d\nu(x)/(\sqrt v)^5$; and for every real $U$ with $X\le U$ almost surely, $\int(x-m)^5\,d\nu(x)/(\sqrt v)^5\le-F(\sqrt v/(U-m))$.

**Argued, not formalized**:

- *Decisive mechanism.* For a probability law with integrable $|x|^5$, $v>0$ and $X\ge L$ almost surely, `mean_gap_pos` supplies $a=m-L>0$, and `integrated_bound` uses $b=v/a$. Under these hypotheses, `polynomial_minorant` at $y=x-m\ge-a$ bounds the fifth power from below by a quadratic whose expectation uses only the fixed mean and variance. The factor $(y-b)^2$ permits contact at the second support point without changing the sign of the remainder. This explains the two-point expression without decomposing a general law into two-point laws.
- *Sharpness and equality.* For any prescribed real mean $m$, variance $v>0$ and real lower bound $L<m$, set $a=m-L>0$ and $b=v/a>0$. Assigning mass $b/(a+b)$ to $X=L$ and $a/(a+b)$ to $X=m+b$ gives a probability law with finite fifth absolute moment, the prescribed mean and variance, and equality in the lower bound by the displayed moment formulas. Moreover, $Q(y)\ge5a^2/8>0$. For any probability law with the same mean and variance, finite fifth absolute moment and $X\ge L$ almost surely, put $Y=X-m$. Integrability and nonnegativity of the certificate show that equality in the integrated inequality forces $(Y+a)(Y-b)^2Q(Y)=0$ almost surely. Thus $Y$ is supported on $\{-a,b\}$, and its zero mean fixes those weights. Reflection gives the corresponding upper-bound construction and equality description for prescribed $U>m$. These attainment and equality statements are informal deductions, not conclusions stated by `result`.
- *Neighbouring questions and effect on the paper.* The lower and reflected upper fifth-moment envelopes used in Fig. 2b are justified for all laws in `claim`, so the source's Conclusion request for a counterexample at $n=5$ has a negative answer within these hypotheses. The source's skewness results and kurtosis arguments at lines 427–467 do not depend on the fifth-moment conjecture and receive no additional verification from this module. The broader odd-moment discussion at lines 512–525 and the proposed relations between general $D_n$ and $D_m$ at line 532 remain outside the settlement: no statement for $n>5$, no general moment-comparison theorem, and no classification of the kurtosis bounds is supplied by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #21300 does not establish exhaustive worldwide novelty or priority. The PLOS ONE version's conjecture text, the OpenAlex citation enumeration, the contents of its two listed citing works, the MathDB and `google-deepmind/formal-conjectures` search coverage, and the preregistration's original repository absence check have not been independently reproduced for this dossier. One listed citing work was checked only at abstract level. No specific theorem of the general Chebyshev–Markov–Krein theory is identified or formally compared here.

The deductions labelled “Argued, not formalized”, including attainment, equality classification and the interpretation of effects on other source statements, are not additional formal results. The source's simulations were not reproduced. The v2 TeX quotation, the Lean statement and its axiom closure are directly checked.
