---
slug: yadavalli-andrejic-kunjwal-2024-biased-trine-joint-measurability
bibkey: yadavalliandrejickunjwal2024qualitative
doi: 10.1103/PhysRevA.110.L060201
url: https://arxiv.org/abs/2008.10100v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.result
---

# The exact triplewise joint-measurability threshold of biased trine qubit measurements

## Problem

S. A. Yadavalli, N. Andrejic and R. Kunjwal, *Qualitative equivalence between incompatibility and Bell nonlocality*, arXiv:2008.10100v3; Phys. Rev. A 110, L060201 (2024), Supplemental Material, Section III, Example 1. Its TeX source `qualequiv_supp_arxiv.tex`, lines 151–158, states:

> Based on our numerical evaluation and visual inspection, we conjecture the exact form of $\eta_1^{(3)}(b)$ to be
> $$\eta_1^{(3)}(b)=\begin{cases}
> 1+b,\quad -1\leq b<-\frac{1}{3},\\
> \frac{2}{3},\quad b\in\left[-\frac{1}{3},\frac{1}{3}\right],\\
> 1-b,\quad \frac{1}{3}< b\leq 1.
> \end{cases}$$

The family is defined in lines 112–118, and the threshold is defined in lines 147–150 by triplewise joint measurability if and only if $\eta\leq\eta_1^{(3)}(b)$. For $k\in\{1,2,3\}$ and $x\in\{-1,+1\}$, its effects on $\mathbb C^2$ are

$$E_k(x)=\frac12\big((1+xb)I+\eta x\,\vec n_k\cdot\vec\sigma\big),\qquad
\vec n_k=\cos\frac{2k\pi}{3}\vec e_x+\sin\frac{2k\pi}{3}\vec e_z.$$

The parameter domain is $-1\leq b\leq1$, $0\leq\eta\leq1$ and $|b|\leq1-\eta$. Triplewise joint measurability means the existence of eight positive semidefinite complex $2\times2$ matrices $G_s$, indexed by $s\in\{-1,+1\}^3$, such that $\sum_sG_s=I$ and $\sum_{s:s_k=x}G_s=E_k(x)$ for every $k$ and $x$.

Issue [#22692](https://github.com/the-omega-institute/trureturing/issues/22692) fixes the reading: for every real $b,\eta$ in this domain, these three measurements are triplewise jointly measurable if and only if $\eta\leq\eta_1^{(3)}(b)$ for the displayed piecewise function. This is proved.

## Motivation

The paper studies which quantum realizations of a joint measurability structure can violate a Bell inequality. Its first biased trine family provides a two-parameter setting in which to distinguish pairwise compatibility from compatibility of the whole triple. The conjectured threshold determines the triplewise boundary in its first plot and enters the characterization of the $3$-Specker region, where every pair is compatible and the triple is incompatible. An exact criterion replaces that numerical boundary with a necessary and sufficient condition.

## Gap

The bounded literature check before any Lean is recorded in #22692:

- The v3 Supplemental Material explicitly retains the conjecture quoted above.
- Crossref reported two citing works; #22692 records a screening of arXiv:2408.08347 and arXiv:2409.14991 with no settlement found.
- The orchestrator's web search found results for unbiased triples and biased pairs, but no settlement of this biased triple threshold.
- The issue reports the unbiased slice $b=0$, with threshold $2/3$, as already known, citing Yu and Oh, arXiv:1312.6470; no novelty is claimed for that slice.
- The issue records no matching repository problem; the existing four-setting compatibility problem concerns a different universal optimum.

`not-found-in-searched-scope`.

## Route

Write $S(t,a)=tI+a\cdot\vec\sigma$ for real $t$ and $a\in\mathbb R^3$, and put $n_k=\operatorname{trineDir}(k)$. The module's indices in $\mathrm{Fin}\,3$ correspond to the source's indices $1,2,3$.

1. **Coordinates and positivity.** For every $k\in\mathrm{Fin}\,3$, `trine_source` identifies the explicit coordinates with the source's cosine and sine directions, and `trine_norm` gives $\|n_k\|=1$; `trine_sum` gives $\sum_kn_k=0$. For every real $t$ and $a\in\mathbb R^3$, the reused `FourQubitParentConstruction.scalarB_posSemidef_iff` gives $S(t,a)\succeq0$ if and only if $\|a\|\leq t$.
2. **Necessary bound.** For arbitrary real $b,\eta$ with `TriplewiseJointlyMeasurable b η`, `parent_coordinates` supplies real $q_s$ and vectors $r_s$ with $\|r_s\|\leq q_s$, $\sum_sq_s=1$ and $\sum_ss_kr_s=\eta n_k$ for each $k$. For every sign string, `sign_sum_bound` gives $\|a_s\|\leq2$, where $a_s=\sum_ks_kn_k$. Under the same joint-measurability hypothesis, `necessity_certificate` proves

   $$3\eta=\sum_s\langle a_s,r_s\rangle\leq2\sum_s\|r_s\|\leq2\sum_sq_s=2.$$

   For real $b,\eta$, adding the hypothesis $|b|\leq1-\eta$ is exactly what `necessity` requires to conclude $\eta\leq\operatorname{trineThreshold}(b)$.
3. **Parent template.** Let $m^{(k)}$ have its only negative sign at $k$ and let $p^{(k)}=-m^{(k)}$. For any real $c,d,u,v,e,f$, `parent` assigns $S(c,-un_k)$ to $m^{(k)}$, $S(d,vn_k)$ to $p^{(k)}$, $S(e,0)$ to the all-positive string and $S(f,0)$ to the all-negative string. For these arbitrary real coefficients, `parent_sum` gives the total $S(3c+3d+e+f,0)$, and `parent_marginal` gives, for every $k$ and either outcome, the positive marginal $S(2c+d+e,(u+v)n_k)$ and the negative marginal $S(c+2d+f,-(u+v)n_k)$. For real $b,\eta,c,d,u,v,e,f$, `parent_valid` constructs the required parent under all seven conditions

   $$|u|\leq c,\qquad |v|\leq d,\qquad 0\leq e,\qquad 0\leq f,$$
   $$2c+d+e=\frac{1+b}{2},\qquad c+2d+f=\frac{1-b}{2},\qquad u+v=\frac\eta2.$$

4. **Three sufficient constructions.** `parent_central` assumes $-1/3\leq b\leq1/3$ and $0\leq\eta\leq2/3$ and uses $c=(1+3b)/6$, $d=(1-3b)/6$, $u=3c\eta/2$, $v=3d\eta/2$, $e=f=0$. `parent_positive` assumes $b\geq1/3$ and $0\leq\eta\leq1-b$ and uses $(c,d,u,v,e,f)=((1-b)/2,0,\eta/2,0,(3b-1)/2,0)$. `parent_negative` assumes $b\leq-1/3$ and $0\leq\eta\leq1+b$ and uses $(c,d,u,v,e,f)=(0,(1+b)/2,0,\eta/2,0,(-1-3b)/2)$. Each choice satisfies all the conditions of `parent_valid`. The three branches of `trineThreshold` select these constructions in `result`, which states the equivalence under all five source-domain inequalities.

## Falsifier

The proof would not answer the source conjecture if its matrices or parent condition represented a different family. Here `trineEffect` uses the source's common bias, its factor $1/2$ and its Pauli expansion; `true` means $+1$ and `false` means $-1$. The explicit vector order is $(-1/2,0,\sqrt3/2)$, $(-1/2,0,-\sqrt3/2)$, $(1,0,0)$, as identified with the source by `trine_source` for every module index.

`TriplewiseJointlyMeasurable` unfolds to `FamilyJointlyMeasurable`, whose parent is indexed by all eight functions $\mathrm{Fin}\,3\to\mathrm{Bool}$. Its `IsPOVM` condition is positivity of every matrix and sum equal to the identity, and its marginal equalities range over every setting and outcome. The threshold is an explicit piecewise real function, with both $b=\pm1/3$ in the central branch; it is not defined by an infimum or supremum. The theorem includes $\eta=0$ and $b=\pm1$ within its stated domain.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.lean`.

- **Proof.** It proves `result`, the universally quantified equivalence on the source parameter domain stated above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.lean.json`.

Declaration statements:

- `result`: `sha256:0247a9c92ec1a74f591d4156cb2c97c24809ca1b23ad5a97b547440fcea5b7c7`.

## Triage

Tier 1 conjecture from a numerical SDP boundary in a 2024 Phys. Rev. A Letter, preregistered in issue #22692 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $b,\eta$ with $-1\leq b\leq1$, $0\leq\eta\leq1$ and $|b|\leq1-\eta$, the three binary measurements with effects defined by `trineEffect` are triplewise jointly measurable if and only if $\eta\leq\operatorname{trineThreshold}(b)$, where `trineThreshold` is exactly the three-branch function in the quoted conjecture.

**Computed, not formalized** (orchestrator, recorded in #22692): the threshold was checked numerically by a semidefinite program before preregistration.

**Argued, not formalized.**

- *Decisive mechanism and scope.* For any real $b,\eta$ admitting a joint parent, `necessity_certificate` gives $3\eta\leq2$ without a bound on $b$ or a sign assumption on $\eta$. Geometrically, the equal-sign strings give $a_s=0$, and each other string gives $a_s=\pm2n_k$, because the three unit directions sum to zero. This makes the necessary purity bound independent of the common bias. On the source domain, $|b|\leq1-\eta$ supplies the other bound. For $b<-1/3$ the smaller bound is $1+b$, for $-1/3\leq b\leq1/3$ it is $2/3$, and for $b>1/3$ it is $1-b$. Thus the piecewise function equals $\min(2/3,1-|b|)$ there. This explanation uses the fixed trine directions and the common bias; thresholds for unequal biases or other directions are open here.
- *Attainment and sharpness.* For every $b\in[-1,1]$, put $T=\operatorname{trineThreshold}(b)$. In the central branch $T=2/3$ and $|b|\leq1/3=1-T$; in the two outer branches $T=1-|b|\in[0,2/3]$. Hence $(b,T)$ satisfies every hypothesis of `result`, which gives an actual parent at the boundary. For $|b|<1/3$, any $0<\varepsilon\leq1/3-|b|$ makes $\eta=2/3+\varepsilon$ physically admissible, and `result` excludes a parent. For $1/3\leq|b|\leq1$, the threshold equals the physical upper bound $1-|b|$, so every admissible purity is compatible. At $b=\pm1$ the admissible purity is only zero. These observations establish sharpness as a consequence of the equivalence, without an optimization-limit assumption.
- *Effect on the source's dependent statement.* Yadavalli, Andrejic and Kunjwal (2024), arXiv:2008.10100v3, Supplemental Material lines 159–162, infer the $3$-Specker condition $|b|\leq1/3$ and $2/3<\eta\leq\sqrt{3-2b^2}-1$. Conditional on their separate pairwise criterion in lines 139–145, this follows: outside the central band the pairwise threshold equals the proved triplewise threshold, leaving no pairwise-only region; inside it, intersecting pairwise compatibility with failure of triplewise compatibility gives precisely these inequalities. At either endpoint $|b|=1/3$ the upper bound is $2/3$, so that region is empty. The settlement supplies the previously conjectural triplewise ingredient; it does not formalize the pairwise criterion.
- *Neighbouring questions and Bell nonlocality.* The source's second biased family in lines 166–193 has a numerical triplewise boundary, and its third family has a different conjecture in lines 195–216; both remain open in this settlement. The claim about absence of $I_{3322}$ violation for the first family's $3$-Specker region is a separate numerical statement in line 163, for which a compatibility boundary alone gives no Bell-value bound. The main text, lines 83–111, constructs Bell-violating realizations through $N$-Specker scenarios and direct sums, independently of this trine conjecture; the settlement changes neither that construction nor the distinction between existence of a Bell-violating realization and Bell violation by a specified realization.

## ASSUMED-UNVERIFIED

The bounded literature check in #22692 does not establish exhaustive worldwide novelty or priority. The two citing-work screenings, the orchestrator's web search, the repository search recorded in the issue and the attribution of the known unbiased threshold to Yu and Oh were not independently reproduced. The arXiv v3 Supplemental Material TeX was read directly and has md5 `99ad6f21ee4fb05ae64c577ed2d1efef`; its quoted conjecture and the source-family correspondence were checked against that text.

The numerical check attributed to the orchestrator was not rerun. The statements grouped under "Computed, not formalized" and "Argued, not formalized" are not additional formalized results. In particular, the pairwise criterion, the derived $3$-Specker characterization, Bell-violation or nonviolation claims, the other two families and extensions beyond the common-bias trine family are not proved by `result`; the generalizations identified as open are not settled here.
