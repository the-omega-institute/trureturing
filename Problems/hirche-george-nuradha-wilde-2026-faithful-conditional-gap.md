---
slug: hirche-george-nuradha-wilde-2026-faithful-conditional-gap
bibkey: hirchegeorgenuradhawilde2026conditional
doi: null
url: https://arxiv.org/abs/2608.27171v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Divergence/FaithfulConditionalGap.result
---

# A faithful divergence separates complete and conditional contraction

## Problem

Hirche, George, Nuradha and Wilde, *Conditional contraction coefficients and their applications to quantum networks*, arXiv:2608.27171v1, §9, second bullet, printed p. 72:

> Can we find a concrete example such that η_D^c(N) < η_D^Δ(N) for some faithful divergence D? A particularly interesting case would be that of the relative entropy. Although it would be natural to conjecture that such an example exists, the unbounded reference systems make it difficult to confirm.

The original existential asks for a divergence family $D$ on every finite-dimensional quantum density-state pair and a finite CPTP channel $N:A\to B$. The family must be nonnegative, satisfy $D(\rho\Vert\sigma)=0\iff\rho=\sigma$, and obey data processing for every CPTP map between arbitrary finite source and target dimensions. Relative entropy is an optional special case, not a condition of the existential.

For every finite quantum reference $R$, write $\rho'=({\rm id}_R\otimes N)\rho$, $\sigma'=({\rm id}_R\otimes N)\sigma$, and let $\rho_R,\sigma_R$ be their input reference marginals. Trace preservation makes these equal to the corresponding output marginals. The coefficients are

$$
\eta^c_D(N)=\sup\left(\{0\}\cup
\left\{\frac{D(\rho'\Vert\sigma')}{D(\rho\Vert\sigma)}:
R\text{ finite},\ \rho,\sigma\in\mathcal D(R\otimes A),\
\rho_R=\sigma_R,\ 0<D(\rho\Vert\sigma)<\infty\right\}\right),
$$

$$
\eta^\Delta_D(N)=\sup\left(\{0\}\cup
\left\{\frac{D(\rho'\Vert\sigma')-D(\rho_R\Vert\sigma_R)}
{D(\rho\Vert\sigma)-D(\rho_R\Vert\sigma_R)}:
R\text{ finite},\ \rho,\sigma\in\mathcal D(R\otimes A),\
0<D(\rho\Vert\sigma)-D(\rho_R\Vert\sigma_R)<\infty\right\}\right).
$$

There is no bound on the finite reference dimension and no classical restriction on its states. Adjoining zero implements the source's empty-set convention. No additivity, direct-sum or joint-convexity axiom is imposed.

## Motivation

A concrete separation distinguishes equal-reference contraction from contraction after subtracting reference information. The source identifies the unrestricted reference system as the obstacle. A finite classical witness alone cannot provide the required uniform complete upper bound.

## Gap

[The source registration](https://github.com/the-omega-institute/trureturing/issues/30303) records the official v1 PDF and bounded literature, citing-paper and repository duplicate checks. No resolution of this second bullet was located in that searched scope; exhaustive novelty and priority are unverified. The existing hockey-stick dossier owns the first bullet and remains a separate result.

## Route

Set $D(\rho\Vert\sigma)=T(\rho,\sigma)^2$, with $T(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. The actual channel on $A=B=\mathrm{Fin}\,2$ measures in the computational basis and applies

$$
W=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix}.
$$

Its four Kraus matrices are $K_{yx}=\sqrt{W_{yx}}\,|y\rangle\langle x|$. Their adjoint products sum to the identity. On an arbitrary input matrix $X$, the output is diagonal with entries $(3X_{00}+X_{11})/4$ and $(X_{00}+3X_{11})/4$.

For every finite quantum reference and every equal-marginal state pair, the difference matrix has reference blocks $X_{(r,0),(s,0)}+X_{(r,1),(s,1)}=0$ for all $r,s$. The amplified channel sends it to one half of its binary pinching. This pinching is $(X+UXU^*)/2$, where $U=I_R\otimes\operatorname{diag}(1,-1)$. Unitary invariance and the trace-norm triangle inequality yield the complete bound $1/4$ after squaring. Off-diagonal reference entries are included.

In the ordered native carrier $(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)$, take normalized density matrices

$$
\rho=\operatorname{diag}(1/2,0,0,0,1/2,0),\qquad
\sigma=\operatorname{diag}(0,0,1/2,0,0,1/2).
$$

Their outputs are $\operatorname{diag}(3/8,1/8,0,0,3/8,1/8)$ and $\operatorname{diag}(0,0,3/8,1/8,1/8,3/8)$. Their reference marginals are $\operatorname{diag}(1/2,0,1/2)$ and $\operatorname{diag}(0,1/2,1/2)$. The input, output and reference trace distances are respectively $1,3/4,1/2$. Thus the conditional denominator is $3/4$, numerator $5/16$, and ratio $5/12$.

Heterogeneous data processing follows by the positive/negative Jordan decomposition, positivity and trace preservation of the actual CPTP map, and the trace-norm triangle inequality. Faithfulness follows from vanishing trace norm. Nonnegative squaring preserves these properties.

## Evidence

The source is [FaithfulConditionalGap.lean](../D5/S3/Quantum/Divergence/FaithfulConditionalGap.lean), with its [owning Scribe](../Blueprint/D5/S3/Quantum/Divergence/FaithfulConditionalGap.scribe.cs). `FiniteDivergence` quantifies over every finite index type and over heterogeneous channels. `completeRatios` and `conditionalRatios` quantify over every finite quantum reference and actual density-state pairs. `completeCoefficient` and `conditionalCoefficient` take the indicated real suprema. The endpoint proves

$$
\exists D\ \exists N:\mathcal D(\mathbb C^2)\to\mathcal D(\mathbb C^2),\qquad
\eta^c_D(N)\le\frac14<\frac5{12}\le\eta^\Delta_D(N),
$$

where $N$ is a canonical finite CPTP channel and $D$ has all the laws above. The conditional ratio set for this instance is bounded above by one, so its real supremum is justified. The axiom boundary is `Classical.choice`, `Quot.sound`, `propext`.

The source reuses the original `act`, `amp_entry` and `ptr_amp` of `ConditionalHockeyStickOrthogonalReduction`; only their visibility is exposed for actual consumers. No duplicate action, reproof or wrapper is introduced.

The positive-result four-slot audit is **unfinished** under [#30303, comment 6874572340](https://github.com/the-omega-institute/trureturing/issues/30303#issuecomment-6874572340). The attempted new Reg build exited 2; exact `sourceSelection` and whole-family observational dependence remain missing. The failed new source was removed. The linked-issue exception of CLAUDE.md §3.9 applies; neither the issue nor successful mathematical checks supplies a `declared_validated` registration. Historical audit #21914 is outside this result.

## Triage

Tier 1 external open problem; positive `proved` mathematical resolution. The endpoint has `proof_shape: bind-only`, `admission_basis: open-problem-resolution`, and no escape witness. All 21 private proof helpers are also bind-only and have actual consumers on the endpoint's proof path; their status is proof organization, not additional mathematical content. The six public typed handles are the divergence structure, two ratio sets, two coefficients and `result`. Definitions are consumed by the public result. This classification follows the independent full pre-freeze approval and supplies no manufactured escape witness.

**Proved:** a faithful finite real-valued divergence and actual finite CPTP channel satisfy $\eta^c_D(N)\le1/4<5/12\le\eta^\Delta_D(N)$ with unrestricted finite quantum references and heterogeneous data processing. The mechanism is equal-marginal block cancellation plus contractive pinching, together with a conditional witness whose marginal subtraction produces the larger ratio.

**Unresolved:** neither exact optimal coefficient is asserted. The relative-entropy case remains unresolved. The positive-result audit remains unfinished as specified above. Source novelty beyond the bounded search is unverified.

**Candidate only:** whether a faithful divergence satisfying additional source-independent structural laws, such as a specified direct-sum law, admits such a separation. This requires a new precisely quantified question, library/literature screening and preregistration; it is not proved or started by this result.
