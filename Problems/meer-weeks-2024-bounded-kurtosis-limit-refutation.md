---
slug: meer-weeks-2024-bounded-kurtosis-limit-refutation
bibkey: meerweeks2024boundedmoments
doi: 10.1371/journal.pone.0297862
url: https://arxiv.org/abs/2308.05006v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result
---

# A three-point law exceeds the Meer–Weeks two-sided kurtosis upper limit

## Problem

David J. Meer and Eric R. Weeks, *Bounded distributions place limits on skewness and larger moments*, PLOS ONE 19, e0297862 (2024), DOI 10.1371/journal.pone.0297862; arXiv:2308.05006v2, subsection “Kurtosis $D_4$”, `plos_latex_template.tex`, line 467:

> While we have not proven that the bidisperse distribution sets the limits for $D_4$ for all other distributions, this is suggestive that Inequalities \ref{D4mostgeneral} are indeed limits for the kurtosis for any distribution.

The quotation is checked against the v2 TeX source, md5 `4452c28a26c7a76c87642af46fe0c8a9`. The referenced inequalities are at lines 461–464; their definitions are at lines 437–460. The moment conventions are at lines 228–236 and 290–293. See [the literature note](../Library/StatisticalMechanics/meerweeks2024boundedmoments.md).

Issue [#21539](https://github.com/the-omega-institute/trureturing/issues/21539) fixes the following universal reading. For every real interval $L<U$ and every probability law $P$ on $\mathbb R$ with $L\le X\le U$ almost surely, mean $\mu=\mathbb E X>0$ and variance $v=\mathbb E[(X-\mu)^2]>0$, put

$\sigma=\sqrt v$, $\delta=\sigma/\mu$, $\delta_{\min}=|1-L/\mu|$, $\delta_{\max}=|1-U/\mu|$, $\delta_1=\min(\delta_{\min},\delta_{\max})$, $\delta_2=\max(\delta_{\min},\delta_{\max})$, $\delta'=\sqrt{\delta_1\delta_2}$,

and $D_4=\mathbb E[(X-\mu)^4]/v^2$, $D_{4,m}(\delta)=(\delta/\delta_m-\delta_m/\delta)^2+1$ for $m=1,2$. The assertion requires both:

- if $\delta<\delta_1$, then $1\le D_4\le D_{4,2}(\delta)$;
- if $\delta_1\le\delta<\delta'$, then $D_{4,1}(\delta)\le D_4\le D_{4,2}(\delta)$.

This reading is refuted. It makes no assertion for $\delta\ge\delta'$; the positive-mean restriction suffices for the refutation.

## Motivation

The proposed bounds would let the support, mean and variance constrain the fourth standardized moment of any bounded distribution by the extrema obtained from two-point distributions. The question is whether this restriction to two-point laws preserves the upper kurtosis limit when additional support points are allowed.

## Gap

The bounded literature check recorded in #21539 before any Lean reports:

- the v2 source retains the quoted expectation;
- OpenAlex record W4391677775 lists two citing works; the orchestrator (Claude Code, Opus) reports reading Meer et al. (2024), arXiv:2404.02316v1, Phys. Rev. E 109, 064905, and finding no kurtosis statement;
- the search seat cited in #21300 reports that the other indexed citing work, a CEIDP 2025 paper, was available only as an abstract;
- the repository search recorded in #21539 found no prior kurtosis settlement; #21300 concerns the separate fifth-moment conjecture.

A refutation of these two-sided kurtosis limits was `not-found-in-searched-scope`.

## Route

All helper names below belong to `BoundedKurtosisLimitRefutation`; the helpers are private and concern its fixed witness $\nu=\tfrac14\operatorname{Dirac}_1+\tfrac12\operatorname{Dirac}_2+\tfrac14\operatorname{Dirac}_3$.

1. **Probability and support.** `witness_probability` states that $\nu$ is a probability measure. `witness_bounds` states $1\le x\le3$ almost everywhere with respect to this same measure.
2. **Exact moments.** For every function $f:\mathbb R\to\mathbb R$, with no additional hypothesis, `integral_witness` gives $\int f\,d\nu=f(1)/4+f(2)/2+f(3)/4$. Integrability against each weighted Dirac measure is established inside its proof. `mean_witness`, `moment_two_witness` and `moment_four_witness` state respectively $\operatorname{mean}(\nu)=2$, $m_2(\nu)=1/2$ and $m_4(\nu)=1/2$.
3. **The bound at the witness.** `coefficient_lt` states the fixed inequality $\sqrt{1/2}/2<1/2$. `bound_value` states the fixed equality $\operatorname{kurtosisBound}(\sqrt{1/2}/2,1/2)=3/2$; its proof uses $(\sqrt{1/2})^2=1/2$.
4. **Contradiction.** `result` assumes `claim` and applies it with $L=1$, $U=3$ and $P=\nu$, using $1<3$, the probability and almost-everywhere support facts, positive mean $2$ and positive variance $1/2$. Substitution gives $\delta=\sqrt{1/2}/2$, $\delta_1=\delta_2=1/2$ and $D_4=2$. The first implication would give $2\le3/2$.

## Falsifier

The refutation would not address the source if the moments, coefficient of variation or endpoint distances were different. The module uses `Defs.mean` as the integral of $x$, Mathlib's `centralMoment id k` as the integral of $(x-\mu)^k$, and $D_4=m_4/m_2^2$ without subtracting three. Here $\delta=\sigma/\mu$, as in the source's two-sided definitions; it is not the shifted coefficient used elsewhere in the paper for a one-sided bound.

The witness has positive mean and variance, lies in $[1,3]$ almost surely and assigns positive mass to both endpoints. Thus the contradiction does not depend on loose endpoint bounds, zero variance or a zero mean. It concerns the proposed upper bound in the first branch; the negation of the universal conjunction does not separately refute its lower bounds or its second branch.

## Evidence

The canonical source is `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.lean` (125 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses `D5.S3.Analytic.MomentMinors.Defs.mean`, Mathlib's `ProbabilityTheory.centralMoment`, and integration over sums of weighted Dirac measures.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.lean.json`, statement `sha256:84f8d5faa01858f079772baa51240e0b606b2138c75a0598adb8088837dbcf9b`.

Declaration statements:

- `result`: `sha256:7bc2e80395612ed40ad9c1fc4ec6e66d759bf729dece824eea30e15da66b875e`;
- `claim`: `sha256:4f5fa8196d5db310a219cf15d1c037ca5b823ff491c37aff5a3c7e5110f279ae`.

## Triage

Tier 1: a hedged expectation in a 2024 journal paper, preregistered in issue #21539 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: finite Dirac integrals, square-root identities and rational arithmetic instantiate existing results | open-problem-resolution |
| `kurtosisBound`, `claim` | bind-only | none | definitions used by `claim` and `result` |
| the witness and private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion that both displayed implications hold for every real interval $L<U$ and every probability measure concentrated almost everywhere on that interval with positive mean and positive second central moment is false. The theorem states `¬ claim`.

**Computed, not formalized** (exact rational calculation; every entry reproduced by the orchestrator by hand from $D_4=1/r$ and $D_{4,2}(\delta)=r+1/r-1$): for the laws assigning masses $r/2,1-r,r/2$ to $1,2,3$, the tested values give:

| $r$ | $D_4$ | $D_{4,2}(\delta)$ | excess |
| --- | --- | --- | --- |
| $1/4$ | $4$ | $13/4$ | $3/4$ |
| $1/2$ | $2$ | $3/2$ | $1/2$ |
| $3/4$ | $4/3$ | $13/12$ | $1/4$ |
| $1$ | $1$ | $1$ | $0$ |

The first three tested laws exceed the proposed upper limit and satisfy $\delta<\delta_1$; $r=1$ is the boundary $\delta=\delta'$, outside the implications. This finite calculation is not a formal result for other values of $r$.

**Argued, not formalized**.

- *Mechanism and a replacement upper bound.* Let a probability law have mean $\mu>0$, support almost surely in $[\mu-h,\mu+h]$ with $h>0$, and variance $v>0$. Put $Y=X-\mu$ and $r=v/h^2$. Bounded support makes these moments finite. Since $Y^2\le h^2$, $0<r\le1$, and $Y^4\le h^2Y^2$ gives $D_4\le h^2/v=1/r$. The masses $r/2,1-r,r/2$ at $\mu-h,\mu,\mu+h$ have mean $\mu$, variance $rh^2$ and fourth central moment $rh^4$, attaining $D_4=1/r$. Here $\delta_1=\delta_2=h/\mu$, so the proposed upper value is $r+1/r-1$. For every $0<r<1$, the three-point value exceeds it by $1-r$. The general family and sharp replacement bound are not statements of `result`.
- *The missing restriction.* For a two-point law with mean $\mu$, write its centered support as $-a,b$ with $0<a,b\le h$. Mean zero fixes the weights as $b/(a+b),a/(a+b)$, so $v=ab$ and $D_4=(a^2+b^2)/v-1$. The inequality $(h^2-a^2)(h^2-b^2)\ge0$ gives $D_4\le h^2/v+v/h^2-1=r+1/r-1$. Equality is attainable with $a=h$, $b=v/h$. Thus in this symmetric-interval setting the proposed upper value is justified for two-point laws; allowing mass at the mean removes that restriction.
- *A surviving lower bound and boundary.* Since $\mathbb E[(Y^2-v)^2]=\mathbb E[Y^4]-v^2\ge0$, $D_4\ge1$ survives. Equal masses at $\mu\pm\sqrt v$ attain it within the symmetric interval. When $r=1$, $h^2-Y^2\ge0$ has expectation zero, hence vanishes almost surely; the law is supported at the two endpoints and mean $\mu$ forces equal masses, giving $D_4=1$. These arguments do not settle the second branch for asymmetric intervals.
- *Effect on the source.* Equation `D4mostgeneral` cannot characterize all bounded laws, and its upper-bound use in the Conclusion (TeX line 532) requires correction. The counterexample does not challenge the identities restricted to bidisperse laws in `Dnbi`, `Dnrhoeqn` and `DNlimits` (lines 483–505), or the source's skewness bounds and Pearson-based one-sided lower bounds. The separate fifth-moment conjecture at lines 506–510 is not refuted by this result. The source's warning that the fourth-moment mixture argument is untrue even for equal component coefficients of variation (line 523) is consistent with the failure to extend the two-point upper bound. No general replacement for asymmetric intervals is formalized here; that question remains open in this dossier.

## ASSUMED-UNVERIFIED

The bounded literature check in #21539 does not establish exhaustive worldwide novelty or priority. The OpenAlex count and the citing-paper readings are attributed to the orchestrator and search seat; they were not independently reproduced. The full text and full bibliographic identity of the CEIDP 2025 item are unavailable in the preregistration record.

The numerical grid search recorded in #21539 and Meer and Weeks's Fig. 2 simulations were not rerun. The source's line 467 states, “For this example, $\delta_1=1.0$ and $\delta'=3.25$.” For that example, $(L,U,\mu)=(0,5,1)$, substituting into its definitions gives $\delta_1=1$, $\delta_2=4$ and $\delta'=2$. This arithmetic discrepancy is separate from the certified counterexample.

The finite rational table and every statement grouped under “Argued, not formalized” are outside the type of `result`. The symmetric-interval sharp bound, its equality cases, the two-point restriction argument and the surviving lower bound have not been formalized in this settlement. The source's other results are not independently verified by this refutation. No settlement of the second branch alone or a sharp kurtosis region for arbitrary asymmetric intervals is claimed.
