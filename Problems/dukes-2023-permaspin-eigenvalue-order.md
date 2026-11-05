---
slug: dukes-2023-permaspin-eigenvalue-order
bibkey: dukes2023permaspin
doi: 10.1016/j.physa.2023.129090
url: https://arxiv.org/abs/2211.08908v3
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.result
---

# The largest root of Dukes's permaspin cubic dominates the two explicit eigenvalues

## Problem

Mark Dukes, *An Ising model having permutation spin motivated by a permutation complexity measure*, Physica A 626 (2023) 129090, DOI 10.1016/j.physa.2023.129090, arXiv:2211.08908v3, Section 4, `permaspin.tex`, lines 510–513:

> Let $\lambda^{*}$ be the largest root of $t(\lambda)=0$.
> It remains to see which of the eigenvalues $\lambda^{*}$, $\lambda_4$, and $\lambda_5$ is largest.
> Numerical investigations indicate that  $\lambda^{*}$ appears to be the largest and this is supported by the evidence presented by
> in Figures~\ref{figblue1} and \ref{figblue2}.

The source sets $c=a^4$ and $d=b^2$, where $a=e^{H'/2}$ and $b=e^{J'}$ (lines 458 and 490). These parameters are positive for real $H',J'$. Its two explicit expressions are $\lambda_4=c(1-d)^2$ and $\lambda_5=c(1-d^2)$ (lines 500–503), and its cubic is (lines 504–509)

$t_{c,d}(x)=x^3-(cd^2+c^2+2cd+c+1)x^2-c(cd^3+3c^2d+cd^2+c^2+cd+c+3d+1)(d-1)x+(d^2+4d+1)c^3(d+1)(d-1)^3$.

The definitions and source context are in [the literature note](../Library/StatisticalMechanics/dukes2023permaspin.md). The module's `dukesCubic c d` is this polynomial, defined for all real $c,d$, and `largestRoot c d` is $\lambda^*(c,d)=\sup S_{c,d}$, where $S_{c,d}=\{x\in\mathbb R:t_{c,d}(x)=0\}$.

Issue [#22514](https://github.com/the-omega-institute/trureturing/issues/22514) fixes the reading: for every real $c>0$ and $d>0$, $S_{c,d}$ is nonempty and bounded above, and $\max(\max(\lambda^*(c,d),c(1-d)^2),c(1-d^2))=\lambda^*(c,d)$. This is proved.

## Motivation

Dukes (2023), arXiv:2211.08908v3, Section 4, expresses the partition function of the one-dimensional 3-permaspin model in an external field through a symmetric $6\times6$ transfer matrix. The source identifies the cubic's three roots and the two explicit expressions as its eigenvalue candidates, with one explicit eigenvalue repeated. The ordering selects the largest candidate used in the paper's free-energy analysis. The Section 4 proposition (lines 515–532) makes this ordering an explicit hypothesis.

## Gap

The bounded literature check recorded in #22514 reports that a web search for “permaspin” found only the source, Zenodo returned no record for that term, and repository searches found no prior issue, module, Library note or dossier for the paper. The issue also records contributor-reported checks that the indexed citing work arXiv:2411.02897 does not settle the ordering, MathDB lists a related free-energy question as open, and formal-conjectures has no match. These reported searches have not been independently reproduced.

`not-found-in-searched-scope`.

## Route

Write $t=t_{c,d}$ and $q=c(1+d)^2$. All helper names below belong to `D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder` and are private.

1. **The cubic data and comparison value.** For every real $c,d$, `cubic_data` gives degree three and leading coefficient one, and `cubic_at_comparison` gives $t(q)=-4c^2d^2(d+1)((d+1)(c-1)^2+4cd)$. For $c>0$ and $d>0$, `cubic_at_comparison_neg` gives $t(q)<0$: the inner sum has a nonnegative first term and a positive term $4cd$, and the remaining factors have the required positive signs.
2. **A root above the comparison value.** For every real $c,d$, `roots_bddAbove` proves that $S_{c,d}$ is bounded above, using the nonzero polynomial supplied by `cubic_data`. For $c>0$ and $d>0$, `root_above_comparison` gives a real $r$ with $q<r$ and $t(r)=0$. It applies the intermediate value theorem to the continuous polynomial evaluation, its tendency to positive infinity at positive infinity, and `cubic_at_comparison_neg`; degree three and leading coefficient one supply the degree and leading-coefficient hypotheses.
3. **The supremum and the two maxima.** For $c>0$ and $d>0$, `comparison_gaps` gives $c(1-d)^2<q$ and $c(1-d^2)<q$. In `result`, boundedness of $S_{c,d}$ and membership $r\in S_{c,d}$ justify $r\le\sup S_{c,d}$ by `le_csSup`. The same $r$ supplies nonemptiness. Each explicit expression is therefore at most $\lambda^*(c,d)$, so both nested maxima reduce to that supremum.

## Falsifier

The proof would miss the source question if the polynomial coefficients, explicit expressions or parameter domain differed. `dukesCubic` uses the coefficients printed at source lines 506–507, and `claim` compares exactly $c(1-d)^2$ and $c(1-d^2)$ for every positive real $c,d$. No assumption of distinct roots or $d\ne1$ is imposed.

The supremum is a total Lean definition; its use as an upper bound is supported by the nonemptiness and boundedness included in `claim`, not by an unstated convention about empty or unbounded sets. The module does not encode the transfer matrix or verify its characteristic polynomial. The interpretation as an eigenvalue ordering uses the source's spectral identification; the formal conclusion concerns the displayed cubic and explicit expressions.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.lean.json`.

Declaration statements:

- `result`: `sha256:5b95ff13860b3bf465e53915c17455d0f1f171dbed4b03097fb6d04b0f26989e`;
- `claim`: `sha256:8e7ff95b713255d9ef78085d0bb3f27e41b38da5609b40f9a330030271ce030e`.

## Triage

Tier 1 numerically supported expectation of a 2023 paper, preregistered in issue #22514 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $c>0$ and $d>0$, $S_{c,d}$ is nonempty and bounded above, and the maximum of its supremum with the two explicit expressions, nested as $\max(\max(\lambda^*(c,d),c(1-d)^2),c(1-d^2))$, equals that supremum. This is the full public result; its statement does not assert strict inequalities or that the supremum is itself a root.

**Computed, not formalized** (Codex, exact symbolic calculation):

- At $c=0$, the largest real root is $1$ for every real $d$.
- At $d=0$, the largest real root is $\max(1,c,c^2)$ for every real $c\ge0$.
- At $d=1$, the largest real root is $c^2+4c+1$ and both explicit expressions vanish for every real $c>0$.

**Argued, not formalized.**

- *Decisive mechanism and strictness.* For $c>0$ and $d>0$, `cubic_at_comparison_neg` and `root_above_comparison` place a real root strictly above $q$, while `comparison_gaps` places both explicit expressions strictly below $q$. Boundedness from `roots_bddAbove`, root membership and `le_csSup` give $\lambda_4,\lambda_5<q<r\le\lambda^*(c,d)$. Thus the proof's intermediate inequalities imply strict separation, although `result` exposes only the maximum identity. No premise about all three cubic roots being real is used in this argument.
- *Boundary extension and ties.* The weak conclusion extends to $c,d\ge0$ by direct boundary analysis. At $c=0$, $t_{0,d}(x)=x^2(x-1)$, so the real root set is finite, nonempty and has supremum $1$, while both explicit expressions are zero. At $d=0$ and $c\ge0$, $t_{c,0}(x)=(x-1)(x-c)(x-c^2)$, so the real root set is finite and nonempty with supremum $\max(1,c,c^2)\ge c$, and both explicit expressions equal $c$. Together with `result` for $c>0,d>0$, these cases give the weak statement on the closed nonnegative quadrant. At $c=1,d=0$, all three candidate values equal $1$, so strict separation does not extend to that boundary. This extension is not a declaration of the module.
- *Effect on the paper and neighbouring questions.* The ordering hypothesis of the Section 4 proposition (source lines 515–532) is supplied for positive parameters. Its printed free-energy formula and its specification of the root $z$ require separate verification. The source additionally states (line 533): “For larger values of $c$ and $d$ it seems that that $\lambda_4$ serves as a close lower bound to the $\lambda^{*}$.” Ordering supplies the lower-bound direction for positive parameters, but gives no approximation error or asymptotic closeness. Neither that quantitative question nor the ensuing low-temperature approximations (lines 534–598), nor a generalization to larger permutation spins, is established by this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #22514 does not establish exhaustive worldwide novelty or priority. Its web and Zenodo results, repository nonmatch, arXiv:2411.02897 reading, MathDB status and formal-conjectures search have not been independently reproduced. The source's numerical investigations have not been reproduced.

The transfer-matrix construction, characteristic-polynomial calculation, spectral identification, exponential parameter bridge and free-energy analysis are not formalized in this module. Their descriptions above are source readings, not additional Lean conclusions; the matrix's characteristic polynomial has not been independently recalculated. The printed free-energy formula, the description of $z$, the large-parameter closeness assertion and the low-temperature approximations remain unverified. The statements under “Computed, not formalized” and “Argued, not formalized” have no separate formal declarations; in particular the closed-quadrant extension, strict maximum comparison and approximation questions are outside the type of `result`.
