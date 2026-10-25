---
slug: inesta-davies-kar-wehner-2026-entanglement-buffer-availability-lower-bound
bibkey: inestaetal2026entanglementbuffering
doi: 10.1038/s41534-025-01161-3
url: https://arxiv.org/abs/2502.20240v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound.result
---

# The always-failing purification policy attains the sharp availability lower bound

## Problem

Á. G. Iñesta, B. Davies, S. Kar and S. Wehner, *Entanglement buffering with multiple quantum memories*, arXiv:2502.20240v1 (npj Quantum Information 12, 64, 2026), pose the conjecture immediately after Corollary 1. The v1 source archive's `main.tex` (MD5 `c1b5c2a56b45349a94ac22e6fde7bd87`), lines 500–502, reads verbatim:

> Unlike the upper bound, we note that the lower bound from (\ref{eq.A_bounds}) has not yet shown to be tight.
> We believe that the availability at $q=1$ of a policy that always fails purification ($c_k=d_k=0$, $\forall k$) constitutes a tight lower bound for any other purification policy.
> We leave this proof as future work.

The system has one long-lived storage memory and $n$ short-lived generation memories per node. Write $p_g$ for the generation probability per short-lived memory, $p_c$ for the consumption probability, $q$ for the probability of attempting purification, $\Gamma$ for the depolarising decay parameter and $F_{\mathrm{new}}$ for the newly generated fidelity.

The module's `admissible` requires, for each $k\in\mathrm{Fin}\,n$ and every $f\in[1/4,1]$,
$$
0\le c_k(f-1/4)+d_k\le1,\qquad
0\le a_k(f-1/4)+b_k\le\frac34\bigl(c_k(f-1/4)+d_k\bigr).
$$
Here $k$ represents the source's $k.\mathrm{val}+1$ generated links. These are the probability and unnormalised output-fidelity conditions of Appendix C, `main.tex` lines 1734–1767.

Write $A((a,b,c,d),q)$ for `availability n pg pc q gam fnew a b c d`, the real-valued closed formula in the source's Theorem 1 (`main.tex` lines 378–415). Issue [#21747](https://github.com/the-omega-institute/trureturing/issues/21747) fixes the reading: for every natural $n\ge1$, real $p_g,p_c\in(0,1]$, $\Gamma\ge0$, $F_{\mathrm{new}}\in(1/4,1]$, admissible real coefficient families $a,b,c,d:\mathrm{Fin}\,n\to\mathbb R$, and $q\in[0,1]$,
$$
A((0,0,0,0),1)\le A((a,b,c,d),q).
$$
This is `claim`, and `result : claim` proves it. The identification of the closed formula with the limiting fraction of consumption requests finding a link is the source's Theorem 1; that stochastic identification is not formalized in this module. The definitions and source locators are also in [the literature note](../Library/QuantumContext/inestaetal2026entanglementbuffering.md).

## Motivation

Availability measures whether buffered entanglement is present when requested. Purification can improve fidelity while risking the loss of the stored link, so a policy-independent lower bound limits how much this risk can reduce availability. The conjecture asks for the exact worst case over the coefficient families and the purification probability. Its settlement separates that extremal value from the fidelity-dependent behaviour of individual policies.

## Gap

The bounded literature check in #21747 reports:

- the preregistration orchestrator (Claude Code, Opus) found no settlement in searches by paper title, entanglement buffering, availability and tight lower bounds, including the authors' theses, Crossref bibliographic search and Zenodo;
- the same author reports that the journal text retains the conjecture;
- the preregistration's search contributor reports three citing works listed through Dimensions and the related continuous-time, two-memory paper arXiv:2311.10052v3 (Quantum 8, 1458, 2024), without a settlement of this discrete-time multi-memory statement.

The arXiv abstract page lists only v1, whose TeX contains the quoted question. Crossref identifies the journal article and DOI above. The literature outcome is `not-found-in-searched-scope`.

## Route

Set $g=1-(1-p_g)^n$, $\mu=p_c$ and $H=F_{\mathrm{new}}-1/4$.

1. **Generation weights (`generation_mass`).** For natural $n\ge1$ and $0<p_g\le1$, the weights
   $$w_k=\binom{n}{k.\mathrm{val}+1}p_g^{k.\mathrm{val}+1}(1-p_g)^{n-(k.\mathrm{val}+1)},\qquad k\in\mathrm{Fin}\,n,$$
   sum to $g$, and $0<g\le1$.

2. **Endpoint constraints (`aggregate_endpoints`).** For any natural $n$, $0\le p_g\le1$, admissible $a,b,c,d$, and the identity $\sum_k w_k=g$, let $\bar a,\bar b,\bar c,\bar d$ be their sums weighted by $w_k$. Nonnegative weights and admissibility at $f=1/4$ and $f=1$ give
   $$
   0\le\bar d\le g,\quad 0\le\tfrac34\bar c+\bar d\le g,\quad
   0\le\bar b\le\tfrac34\bar d,\quad
   0\le\tfrac34\bar a+\bar b\le\tfrac34(\tfrac34\bar c+\bar d).
   $$

3. **Two-coordinate estimate (`two_state_mass`).** For real $u,v,w,z,\ell,\mu,\eta$ with $v,w\ge0$, $\mu>0$, $0\le\eta\le1$ and
   $$\ell\le u+w\le1-\mu,\qquad \ell\le v+z\le1-\mu,$$
   put
   $$\delta=(1-u)(1-z)-vw,\qquad N_2=(1-z+w)\eta+(v+1-u)(1-\eta).$$
   The lemma proves $0<\delta\le(1-\ell)N_2$. For positivity it applies the imported `det_pos_of_dominant` to the transpose of $I-\begin{pmatrix}u&v\\w&z\end{pmatrix}$: the diagonal is positive and each off-diagonal row norm sum is strictly smaller than its diagonal. For the inequality, put $y_0=(1-z)\eta+v(1-\eta)$ and $y_1=w\eta+(1-u)(1-\eta)$. Both are nonnegative, and
   $$(1-\ell)(y_0+y_1)-\delta=(u+w-\ell)y_0+(v+z-\ell)y_1\ge0.$$

4. **Scalar formula (`scalar_mass`).** For real $g,\mu,q,e,h,a,b,c,d$ with $0<g\le1$, $0<\mu\le1$, $0\le q\le1$, $e\ge1$, $0\le h\le3/4$, and all four endpoint constraints
   $$0\le d\le g,\quad0\le\tfrac34c+d\le g,\quad0\le b\le\tfrac34d,\quad0\le\tfrac34a+b\le\tfrac34(\tfrac34c+d),$$
   set
   $$t=q(1-\mu),\quad\ell=(1-qg)(1-\mu),\quad p=\mu+qg(1-\mu)=1-\ell,\quad x=e-\ell,$$
   $$\Delta=(x-ta)(p-td)-t^2bc,\qquad N=x-ta+tch.$$
   With $r=1/e$, the constructed two-state coefficients have nonnegative off-diagonal entries and column sums
   $$\ell+t\bigl(r(\tfrac34c+d)+(1-r)d\bigr),\qquad\ell+td,$$
   both in $[\ell,1-\mu]$. Thus `two_state_mass` applies with $\eta=4h/3$. The identities $e\delta=\Delta$ and $eN_2=N$ yield $x,p,\Delta>0$ and $1\le pN/\Delta$.

5. **Policy bound (`policy_bound`).** For natural $n\ge1$, $p_g,p_c\in(0,1]$, $\Gamma\ge0$, $F_{\mathrm{new}}\in(1/4,1]$, admissible coefficient families and $q\in[0,1]$, apply `scalar_mass` with $e=e^\Gamma$, $h=H$ and the four weighted coefficients. With $s=N/\Delta$, it gives $s>0$ and $1\le ps$. The source formula's normalised determinant equals $\Delta/(xp)>0$; cancellation identifies its occupied duration with $s$ and its availability with $s/(1/g+s)$. Since $q\le1$,
   $$p\le\mu+(1-\mu)g,\qquad1\le s\bigl(\mu+(1-\mu)g\bigr).$$
   Positive-denominator cross multiplication gives
   $$\frac{g}{\mu+(2-\mu)g}\le A((a,b,c,d),q).$$

6. **Attainment (`failing_value`) and comparison (`result`).** For arbitrary natural $n$ and real $p_g,\Gamma,F_{\mathrm{new}}$ with $g>0$, and $0<p_c\le1$, `failing_value` proves
   $$A((0,0,0,0),1)=\frac{g}{p_c+(2-p_c)g}.$$
   `result` uses this identity and `policy_bound` under exactly the hypotheses of `claim` stated in Problem.

## Falsifier

A formula mismatch would leave the source conjecture unsettled. The correspondence is explicit:

- `pg`, `pc`, `gam` and `fnew` are $p_g$, $p_c$, $\Gamma$ and $F_{\mathrm{new}}$; `gam` enters through `Real.exp gam`.
- `Fin n` enumerates the source's indices $1,\ldots,n$, with precisely the binomial weights of Theorem 1. The four normalised coefficient sums and both duration expressions are those of that theorem.
- `admissible` imposes its inequalities for every fidelity in $[1/4,1]$, including zero-success branches. It does not certify that every admissible tuple is an implementable purification circuit.
- The comparison concerns the closed formula. It does not assert convergence of a stochastic process, an optimal consumed fidelity, or uniqueness of the minimizing policy.
- The definition uses total real division, including at zero outside the stated domain. The proof establishes positivity of the denominators it cancels under the claim's hypotheses; $n=0$, $p_g=0$ and $p_c=0$ are excluded.

## Evidence

The canonical source is `D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound.lean` (330 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound.lean.json`, statement `sha256:9ff78008b73b5ba508562b98664d8ae96e731d302a44b29e905504728603163b`.

Declaration statements:

- `result`: `sha256:6f82640409847a02c32c66d86289017201f0a10a6f26892cffb1bc958f63daa4`;
- `claim`: `sha256:c2c83197f5b9c2ec5f2b24f6989e4d485a8f8467779f051dbaaa667203309b28`.

## Triage

Tier 1 conjecture of a 2025 preprint and its 2026 journal version, preregistered in issue #21747 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge1$, real $p_g,p_c\in(0,1]$, $\Gamma\ge0$, $F_{\mathrm{new}}\in(1/4,1]$, coefficient families $a,b,c,d:\mathrm{Fin}\,n\to\mathbb R$ satisfying `admissible`, and $q\in[0,1]$, the module's formula satisfies $A((0,0,0,0),1)\le A((a,b,c,d),q)$.

**Computed, not formalized**

- Exact rational evaluation of Theorem 1's formula used 81 coefficient choices parametrised by $d,z,u,v\in\{0,1/2,1\}$:
  $$c=\tfrac43(z-d),\quad b=\tfrac34du,\quad a=zv-du.$$
  Each choice satisfies the endpoint constraints. Homogeneous families used $n\in\{1,2,4\}$, $p_g\in\{1/4,1\}$, $p_c\in\{1/3,1\}$, $q\in\{0,1/2,1\}$, $e^\Gamma\in\{1,2\}$ and $F_{\mathrm{new}}\in\{1/2,1\}$, giving 11,664 evaluations. All 6,561 ordered pairs of coefficient choices were also evaluated at $n=2$, $p_g=1/4$, $p_c=1/3$, $q=1$, $e^\Gamma=2$, $F_{\mathrm{new}}=1/2$. For this tested family, a violation of $A\ge g/(\mu+(2-\mu)g)$ was not observed; the minimum exact difference was zero. All checked formula denominators were positive. The zero families at $q=1$ attained equality in 48 further evaluations.
- At $g=7/16$, $\mu=1/3$, $\Gamma=\log2$, the source's Corollary 1 lower bound evaluates to $168/569$, whereas the sharp lower bound is $7/17$.
- The preregistration orchestrator (Claude Code, Opus), in #21747, reports 200,000 floating-point samples with $n\le4$, including boundary values. For the tested family, a violation beyond floating-point scale was not reported: the minimum computed difference was $-1.1\cdot10^{-16}$. This sampling is not a proof, and its program and random seed are not supplied in the issue.

**Argued, not formalized**

- *Sharpness and meaning of the benchmark.* Under the Problem hypotheses, substituting four zero families makes every admissibility inequality $0\le0\le0$ or $0\le0\le1$. Thus the benchmark belongs to the admissible class. Together with `failing_value` for $g>0$, $0<p_c\le1$ and arbitrary $\Gamma,F_{\mathrm{new}}$, this shows why its attained value cannot be raised as a uniform lower bound for that class. Conversely, if $c_k=d_k=0$, admissibility at $f=1/4$ forces $b_k=0$, and at $f=1$ forces $a_k=0$. The benchmark therefore matches the source's always-failing coefficients without assigning a fidelity to an impossible successful branch.
- *Decisive mechanism and scope.* Under all the hypotheses of `two_state_mass` in Route, the nonnegative $y_0,y_1$ make the displayed mass identity control the denominator and numerator together. The weighted endpoint constraints let `scalar_mass` use that identity without separately optimizing potentially incompatible coefficient values. Its stated hypotheses include every $e\ge1$ and $h\in[0,3/4]$. Keeping natural $n\ge1$, $p_g,p_c\in(0,1]$, $\Gamma\ge0$, admissibility and $q\in[0,1]$, the same argument also reaches $F_{\mathrm{new}}=1/4$: `generation_mass` and `aggregate_endpoints` are unchanged, `scalar_mass` accepts $h=0$, and the positive-denominator comparison and `failing_value` still apply. This endpoint extension is not a statement of `result`.
- *Nonuniqueness at a boundary.* Under the Problem hypotheses with $p_c=1$, $t=q(1-p_c)=0$, all four normalised coefficient sums vanish, and the formula becomes $A=g/(1+g)$ for every admissible family and every $q\in[0,1]$. Thus attainment does not imply uniqueness. A classification of minimizers when $0<p_c<1$ is not established here.
- *Effect on the source's availability bounds.* For the parameter domain in Problem, set $\gamma=e^\Gamma-1\ge0$. Corollary 1 (`main.tex` lines 479–486) gives the lower expression
  $$L_{\mathrm{old}}=\frac{g(\gamma+\mu)}{D_{\mathrm{old}}},$$
  $$D_{\mathrm{old}}=\gamma\mu+\mu^2+\bigl(1+2\gamma+(2-\gamma)\mu-2\mu^2\bigr)g+2(1-\mu)^2g^2.$$
  Writing $D_{\mathrm{new}}=\mu+(2-\mu)g$, direct expansion gives
  $$D_{\mathrm{old}}-(\gamma+\mu)D_{\mathrm{new}}=g(1-\mu^2)+2(1-\mu)^2g^2\ge0.$$
  Both denominators are positive: $D_{\mathrm{new}}>0$ and $D_{\mathrm{old}}\ge(\gamma+\mu)D_{\mathrm{new}}>0$. Consequently $L_{\mathrm{old}}\le g/D_{\mathrm{new}}$, strictly if $\mu<1$ and with equality if $\mu=1$. The original lower inequality remains valid, while the availability-bound plots can use the stronger lower envelope. The attained minimum is independent of $\Gamma$ and $F_{\mathrm{new}}$; individual policies' availability need not be.
- *Other conclusions and neighbouring questions.* The source places the conjecture after its proved availability corollary; the settlement supplies the missing comparison, rather than a proof of its separate monotonicity or consumed-fidelity results. The Outlook (`main.tex` line 815) states: “Additionally, finding policies that optimize availability or average consumed fidelity remains an important open question.” The formula's worst availability is settled under the stated conditions. Optimal ordering of implementable purification protocols and optimization of consumed fidelity or the availability–fidelity tradeoff remain outside `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The publisher-text comparison, broad web searches, Crossref bibliographic search, Zenodo search, three Dimensions citing-work readings and the reading of arXiv:2311.10052v3 are reports from #21747 and were not independently reproduced for this dossier. The separate Crossref DOI metadata and the v1 arXiv source and version listing were checked directly.

B. Davies's TU Delft thesis, *Performance analysis of near-term quantum networks*, remains unread: #21747 records a refused repository connection and failed Firecrawl retrieval. Whether it contains a proof of this lower bound is unverified. The issue's 200,000-sample calculation was not reproduced.

The source's stochastic identification of Theorem 1 with operational availability, its physical protocol-to-coefficient model and implementability of arbitrary admissible coefficients are not formalized here. All computations and the arguments labelled “Argued, not formalized,” including the endpoint extension, minimizer discussion and comparison with the older bound, are outside the type of `result`.
