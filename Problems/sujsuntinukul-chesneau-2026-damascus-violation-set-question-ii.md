---
slug: sujsuntinukul-chesneau-2026-damascus-violation-set-question-ii
bibkey: sujsuntinukulchesneau2026damascus
doi: 10.1007/s11139-026-01345-1
url: https://arxiv.org/abs/2601.00916v4
triage: theorem
motivation_gids:
  - D5/S3/Analytic/DamascusViolationSetBoundedness.result
---

# Boundedness of the Damascus violation sets

## Problem

Chanatip Sujsuntinukul and Christophe Chesneau, *Variants of the Damascus inequality*, arXiv:2601.00916v4, Section 5, page 19, ask:

> In addition to the above, it is natural to ask whether analogous structural properties hold for I_n^m when m is arbitrary. Can one prove or disprove that I_n^m (i) stays uniformly away from 1, (ii) is bounded, or (iii) forms an increasing family in n?

The source concludes: “Thus this question, together with question (iii), remains open.” This dossier settles question (ii).

Write $f_n(x)=(x^n-1)/(x^{n+1}+1)$, $H_m=\{x\in(0,\infty)^m:\prod_jx_j=1\}$ and $I_n^m=\{x\in H_m:\sum_j f_n(x_j)>0\}$. For all natural numbers $m,n\ge1$, the result is

$$I_n^m\text{ is bounded}\quad\Longleftrightarrow\quad m\le3\ \lor\ (m=4\land n\le4)\ \lor\ (m\in\{5,6\}\land n=1).$$

The classification is the repository's answer, rather than a proposition quoted from the paper.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Summand of inequality (1), page 2 | `term` | Literal real quotient $(x^n-1)/(x^{n+1}+1)$; no transformed predicate. |
| $H_m$ consists of positive coordinates with product one | `H` | Functions `Fin m → ℝ`; every coordinate is positive and occurs once in the product. |
| $I_n^m\subset H_m$ has strictly positive summand sum | `I` | Membership in `H m` and a strict inequality $0<\sum_j f_n(x_j)$. |
| Arbitrary dimension and positive integer exponent | `claim`, binders $m,n$ and guards $1\le m$, $1\le n$ | Both parameters vary without upper bounds. Dimensions one and two are included; dimension zero and exponent zero are outside the question. |
| Boundedness | `Bornology.IsBounded (I n m)` | The usual sup norm on a finite real coordinate space. |
| Answer to question (ii) | `result : claim` | Exactly the displayed three-branch classification, in both directions. The classification branches express the answer; they are not additional hypotheses. |

## Motivation

The settling GID is `D5/S3/Analytic/DamascusViolationSetBoundedness.result`, with Lean name `D5.S3.Analytic.DamascusViolationSetBoundedness.result`. Its admission basis is `open-problem-resolution (#18584; Proved)`, as preregistered in [#18584](https://github.com/the-omega-institute/trureturing/issues/18584).

The delivery has one general module, four public definitions and one public theorem. Its private helpers are consumed by the settling proof. All authored theorem proofs are conservatively classified bind-only after expansion into pinned Mathlib facts, finite-sum/product operations, explicit scalar estimates and normalization. No independent escape witness or supporting-module admission is claimed. The module has `generality: G` and `utility: none`: the delivered result is a universally quantified analytic classification, and the scalar evaluations are premises used in that proof.

## Gap

Question (ii) is settled for every positive natural dimension and exponent. General nesting in $n$, separation from coordinate-one planes for arbitrary $m$, and a Lean theorem for the exact scalar-supremum criterion remain open in this delivery.

The four-slot escape audit of the sole public theorem `D5.S3.Analytic.DamascusViolationSetBoundedness.result` is unfinished under [#19895](https://github.com/the-omega-institute/trureturing/issues/19895). The inspected iff and dependent-family enrollments do not supply the faithful nonconstant actual readout family, source reconstruction, realization bridge, variation, sensitivity and binding evidence for this parameterized statement. A singleton state in each $(m,n)$ fiber cannot establish observational dependence. No Reg mirror or `declared_validated` registration is claimed.

## Route

For $x>0$, the scalar helpers establish $-1<f_n(x)<1/x$; for $0<x\le1$ and $n\ge1$, they establish $f_n(x)+1\le2x$. There is a uniform upper bound $c_n<1$. The sharper bounds $f_1(x)\le5/24$ and $f_4(x)\le4999/10000$, together with monotonicity in $n$ for $x\ge1$, give the bounded cells.

If $(m-2)c<1$, put $\delta=1-(m-2)c$, $K=1+8/\delta$ and $B=K^{m-1}$. A coordinate above $B$ forces a different coordinate below $1/K$ by the product-one identity. The pair's summands sum to less than $-1+3/K$, while the remaining summands sum to at most $(m-2)c$. The total is negative, contradicting violation. The private `bounded_of_upper` implements this confinement argument using Mathlib's `Finset.prod_le_prod₀`, `Finset.prod_erase_mul`, `Finset.add_sum_erase`, `isBounded_iff_forall_norm_le` and `pi_norm_le_iff_of_nonneg`.

For unboundedness put $k=m-2$ and use

$$(t,1/(t r^k),r,\ldots,r),\qquad t>1.$$

Its product is one. If $k f_n(r)\ge1$, then the first term is positive and the second is strictly greater than $-1$, so the sum is strictly positive. The private `escape_mem` proves membership, and `unbounded_of_middle` makes the first coordinate exceed any proposed norm bound. Taking $r=2$ for $n\le4$ or $r=3/2$ for $n\ge5$ covers every unbounded cell. Private `bounded_cells` and `unbounded_cells` combine these estimates; `result` states the complete classification.

## Falsifier

A positive-natural pair $(m,n)$ whose violation set has boundedness different from the classification would refute `claim`. A tuple outside the positive product-one constraint, a non-strict violation predicate, or a different notion of boundedness is outside the settled statement.

## Evidence

The kernel-checked settling declaration is `D5.S3.Analytic.DamascusViolationSetBoundedness.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. Its Scribe node displays the entire quantified proposition and carries one Proved `OpenProblemResolutionClaim`. The source note is `Library/Estimation/sujsuntinukulchesneau2026damascus.md`. The canonical freeze is deposit-uncovered without an anchor atom or coverage step.

Experiment: [pinned numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/43878a67fd7ab5668558cb05992b4806419c0f79/docs/reports/sujsuntinukul-chesneau-2026-damascus-violation-set-boundedness). Command from the main repository root: `python3 ../trureturing-experiments/docs/reports/sujsuntinukul-chesneau-2026-damascus-violation-set-boundedness/check.py`; exit 0, `RESULT PASS`. Script SHA-256: `47e10ae0abd6fd3734b6ff4a564606e51f92805e341b025fa748ff2b1f009f28`. The executed script's bytes agree with that commit.

The computation compares the scalar root formula with a grid maximum for $1\le n\le20$, checks the specified scalar identities symbolically or with exact fractions, and compares all classification cells $1\le m,n\le10$. In every unbounded cell with $4\le m\le10$, $1\le n\le10$, the rational family has positive sum at $t=10^3,10^6$. The equality family $(t,2,2,2,1/(8t))$ is also checked at $t=10,10^3,10^6$. In 60000 seeded random product-one samples for each of $(m,n)=(3,1),(3,7),(4,2),(4,4),(5,1),(6,1)$, the largest violating coordinate divided by the computed $B$ is $5.535\times10^{-3}$. These finite computations do not establish a uniform theorem.

## Triage

| Item | Status and evidence |
| --- | --- |
| Complete boundedness classification, including dimensions one and two | Proved in Lean: `DamascusViolationSetBoundedness.result`; the canonical module and its consumed helpers compile. |
| One general module; no extra general module | Verified artifact scope: `D5/S3/Analytic/DamascusViolationSetBoundedness.lean`, `generality: G`, `utility: none`, with the stated open-problem-resolution admission basis. |
| Canonical freezing and escape registration | The settling module has a canonical frozen state record; the four-slot audit remains open under #19895. Freeze membership is not escape-registration completion. |
| External literature verification, novelty and publication readiness | Literature reading: the source and preregistration's identified follow-ups leave general-dimension boundedness open in the searched scope. Completeness is ASSUMED-UNVERIFIED; novelty and publication readiness are not established. |
| Explicit rational escape families in all unbounded regimes | Proved in Lean: private `escape_mem`, `unbounded_of_middle` and `unbounded_cells`, consumed by `result`; choose rational $t>1$ and the stated rational $r$. |
| Equality threshold $(m,n)=(5,2)$ | Proved in Lean: private `middle_two_two`, `escape_mem` and `unbounded_cells`; three middle terms contribute exactly one, and the other two contribute strictly more than minus one. |
| Explicit bounding box | Proved in prose in the subsection below from the confinement proof and product constraint; the Lean theorem states boundedness, rather than this box formula. |
| Scalar maximum values and exact scalar identities | Computed in the pinned experiment above: root/grid comparison for $n\le20$, exact symbolic/fraction checks for the listed $n=1,2,4,5$ identities. The exact supremum theorem is not a Lean claim. |
| Finite classification table and rational-family checks | Computed in the pinned experiment above, only in the stated $m,n,t$ ranges. |
| Bounded-regime sampling | Computed in the pinned experiment above, exactly six regimes and 360000 samples. A sample is not a proof of confinement. |
| General nesting in $n$, question (iii) and Conjecture 5.5 | Open in this delivery. The preregistration reports Deonarine's dimension-three nesting result as literature reading; its full scope is not independently verified here. |
| Separation from coordinate-one planes for arbitrary $m$ | Open in this delivery. |
| A Lean theorem for the exact criterion $(m-2)M_n\ge1$ | Open in this delivery; neither existence nor the exact maximum $M_n$ is added as a Lean declaration. |
| Source results depending on boundedness | The source's dimension-three boundedness is included in `result`. No nesting or coordinate-plane assertion is inferred from boundedness. |

### What the settlement shows

The decisive mechanism is the balance between an escaping large/small coordinate pair and the remaining $m-2$ summands. The pair has summand sum strictly greater than $-1$ at finite escape parameters. Thus equality in the middle-summand threshold still gives an unbounded violation set. This is the mechanism used by the Lean private `escape_mem` and `unbounded_of_middle`, and it explains the boundary case $(5,2)$ without a numerical limit argument.

For $m\ge2$ in a bounded cell, the confinement proof gives $0<x_i\le B$. Its explicit constants are $\delta=1-(m-2)c>0$, $K=1+8/\delta$ and $B=K^{m-1}$, where $c$ is the uniform scalar bound used in `bounded_of_upper`. Since $1=x_i\prod_{j\ne i}x_j\le x_iB^{m-1}$, every coordinate also satisfies $x_i\ge B^{-(m-1)}$. This establishes the box $[B^{-(m-1)},B]^m$ in prose. For $m=1$, the product constraint forces the only coordinate to be one, the summand is zero, and the violation set is empty. The delivered Lean conclusion asserts boundedness; it does not state a sharp optimal box.

The classification extends the source's boundedness result to every positive natural dimension and exponent. It gives negative answers to arbitrary-dimension boundedness precisely in the complementary cells, with minimal unbounded pairs $(4,5)$, $(5,2)$ and $(7,1)$. It leaves the source's nesting question, Conjecture 5.5 and arbitrary-dimensional coordinate-plane separation unchanged. The exact maximum criterion and general nesting are follow-up candidates, with no additional theorem included here.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source quotations and definitions follow arXiv:2601.00916v4. The journal-version, Deonarine and Dannan–Sitnik follow-up descriptions are attributed to the preregistration's search seat unless explicitly stated otherwise; they do not establish an exhaustive priority search. No novelty or publication-readiness claim is made. The unfinished escape audit is disclosed under #19895; no four-slot validation is claimed.
