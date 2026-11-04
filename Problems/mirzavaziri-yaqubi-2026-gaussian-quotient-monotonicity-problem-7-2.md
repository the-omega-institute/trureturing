---
slug: mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2
bibkey: mirzavaziri2026gaussianquotient
doi: 10.48550/arXiv.2610.19249
url: https://arxiv.org/abs/2610.19249v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.result
---

# Gaussian quotient monotonicity does not force two exceptional signs

## Problem

Mirzavaziri and Yaqubi, *Graph binomial coefficients and a positivity conjecture of Guo and Krattenthaler*, arXiv:2610.19249v1, Problem 7.2, p. 16, ask:

> Characterize the quadruples $(N,k,a,b)$ for which $\genfrac{[}{]}{0pt}{}{N}{k}_q/([a]_q[b]_q)$ is a polynomial whose only negative coefficients are $-1$ at $q^1$ and at $q^{D-1}$. In particular, is this always the case when $\genfrac{[}{]}{0pt}{}{N}{k}_q/[a]_q$ is weakly increasing from $q^1$ to its middle coefficient?

The answer to the final sufficiency question is negative. The full characterization remains open.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Gaussian polynomial and q-integers | Existing `LiUncuDefs.gauss` and `QProductNecessityRefutation.qInteger` | The q-Pascal Gaussian and finite geometric sum are reused; q-integers are mapped from natural to integer coefficients. |
| The two ordinary quotients are polynomials | `claim` quantifies integer polynomials $U,P$ with the two exact multiplication identities | These identities state exact division, without rational-function ambiguity. |
| Weak increase from $q^1$ to the middle | `increasingFromOne` | Every adjacent comparison at $2\le s\le\lfloor\deg(U)/2\rfloor$; no comparison from degree zero is imposed. |
| Only negative coefficients are $-1$ at $1,D-1$ | `twoExceptionSignPattern` | Both exceptional coefficients equal $-1$; every other natural index is nonnegative, including the zero tail. Here $D=\deg(P)$. |
| Is this always the case? | `claim`, negated by `result` | Universal natural indices $N,k,a,b$, with $k\le N$ and positive $a,b$, and all exact polynomial quotients. |
| Domain conventions | Natural subtraction and division; $k\le N$, $1\le a,b$ | Subtraction is truncated. These are the preregistered conventions; the numerical screen's narrower conditions are not added as hypotheses. |

The private `adjacent_iff_monotoneOn` correspondence connects the literal adjacent condition to `MonotoneOn` on the closed interval. It changes no public definition.

## Motivation

The frozen settling declaration is `D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.result`. It refutes the universal sufficiency assertion by the exact witness $(N,k,a,b)=(30,3,7,10)$. The public surface consists of the three source definitions and this single theorem. The admission basis is `open-problem-resolution (#21322; Refuted)`; proof shape is bind-only, with the existing Gaussian identities and explicit polynomial normalization supplying the certificate.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

The bounded source and literature screen is recorded in [#21322](https://github.com/the-omega-institute/trureturing/issues/21322). It identified no prior settlement of this exact final question. Guo–Krattenthaler arXiv:1301.7651v3, Lemma 5.1, requires unimodality including the degree-zero comparison; the witness has $u_0=1>u_1=0$. The inspected weighted complete-intersection and basic-hypergeometric positivity results do not state this implication or its negation. These are literature comparisons, not dependencies of the Lean proof. Completeness is ASSUMED-UNVERIFIED.

## Route

Write $G={30\brack3}_q$, $G=[7]_qU$ and $U=[10]_qP$. The private `small_gauss_product` uses `LiUncu.gauss_hook` and `LiUncu.gauss_symmetry` to establish

$$
(1-q)(1-q^2)(1-q^3)G=(1-q^{28})(1-q^{29})(1-q^{30}).
$$

Cancellation and exact polynomial arithmetic verify the first quotient against the literal polynomial `smallU`. The second quotient is checked against `smallP`. The private degree certificates give $\deg(U)=75$ and $\deg(P)=66$, and `small_increasing` verifies every comparison through degree $37$. Finally `smallP_bad` gives $[q^{11}]P=-1$. Since $11\ne1,65$, the asserted nonnegativity fails.

The coefficient recurrence explains the failure. Multiplying $U=[10]_qP$ by $1-q$ gives $(1-q)U=(1-q^{10})P$. Coefficient comparison yields

$$
p_t-p_{t-10}=u_t-u_{t-1},
$$

where negative indices have coefficient zero. Thus the plateau $u_{10}=u_{11}=3$ propagates $p_1=-1$ to $p_{11}=-1$. This recurrence is an explanation proved here in prose, not an additional kernel-checked theorem.

## Falsifier

A failed exact quotient identity, a failed monotonicity comparison at any $2\le s\le37$, or a nonnegative degree-eleven coefficient would invalidate the witness. The settling proof checks all these requirements. The finite certificate does not assert the unbounded family or the complete classification.

## Evidence

The Lean module has one public theorem, `D5.S3.Combinatorics.GaussianQuotient.MirzavaziriYaqubiMonotonicityRefutation.result`. Its private helpers establish the two quotient identities, the degrees, the degree-eleven coefficient, and all required adjacent comparisons.

The exact experiment is pinned in [trureturing-experiments at c9ab263c1e90358645b266282e0d0c168e7f2523](https://github.com/the-omega-institute/trureturing-experiments/tree/c9ab263c1e90358645b266282e0d0c168e7f2523/docs/reports/mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2). The script is `docs/reports/mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2/check.py`, SHA-256 `f67ed55ee555037daf83cc71c4e7a3dc4faea2839d4e00abc80689cfb5528a99`. Measured command: `python3 /Users/auric/.sshx/51d1ff3ec52431d3525f4fbc/attempt-1/experiment-check.py`, using bytes matching the pinned repository script: exit 0, `ALL_CHECKS_OK`.

The computation checks the $m=0$ witness independently by enumerating all $4060$ three-element subsets. It checks exact polynomiality, degrees, reciprocity and the complete monotonicity antecedent for $N=30+420m$, $k=3,a=7,b=10$, at $m=0,\ldots,20,100$ (22 cases), both 42-entry residue tables, and 50 periods of the auxiliary difference sequence. It also reproduces the source's exceptional cases in Theorem 4.3 at $m=4,6$ and $P^{(1)}=1+q^2+q^4$.

The primary TeX is `gk74-2.tex` from arXiv:2610.19249v1, SHA-256 `8e15a5d14b845dcc082a0a0e819126ca875269aa6f166737d163c7a88a8dd865`. Its Lemma 4.1 and final Section 7 question give the strictness boundary below.

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** the universal sufficiency assertion is false at $(30,3,7,10)$, by `result`.
2. **Proved, kernel-checked:** the chosen $U$ is weakly increasing for every $2\le s\le\lfloor\deg(U)/2\rfloor=37$, by private `small_increasing`, `smallU_degree` and `adjacent_iff_monotoneOn`, used in `result`.
3. **Proved, kernel-checked:** $\deg(P)=66$ and $[q^{11}]P=-1$, with $11\notin\{1,65\}$, by private `smallP_degree`, `smallP_bad` and `result`.
4. **Computed:** the $m=0$ witness satisfies $2\le k\le N/2$, $2\le a\le b\le N$ and $\gcd(a,b)=1$. The exact experiment above checks these restrictions; they do not remove this counterexample.
5. **Computed:** $u_{10}=u_{11}=3$ and the negative coefficients of $P$ occur precisely at $1,11,55,65$, all equal to $-1$, by the exact experiment. The recurrence in Route explains their propagation in prose; only the degree-eleven certificate is needed by the settling theorem.
6. **Computed:** the proposed family passes full exact polynomial, degree, reciprocity and monotonicity checks at $m=0,\ldots,20,100$, and both 42-entry residue tables pass, by the exact experiment. This is exactly the tested scope.
7. **Open:** the unbounded-family nomination is not Lean-proved by the finite certificate. The 22 finite checks do not prove its universal quantifier.
8. **Open:** the complete classification of quadruples, necessity of a strictness condition, and Conjectures 4.4 and 4.5 are not settled here.
9. **Computed/source reading:** Lemma 4.1 retains its additional strictness hypothesis; the exact experiment gives $u_{11}=u_{10}$, so this counterexample does not meet it. Inspection of the primary TeX, Lemma 4.1 and Section 7, identified no theorem assuming an affirmative answer to Problem 7.2. This is a source-reading boundary, not a new Lean proof of the source's theorems. The original lemma and its stated applications retain their additional hypotheses.

Every computed item uses the single pinned experiment entry above, with exit 0 and the stated SHA-256. The source-reading part of item 9 uses the primary TeX locator and hash above. The nearest surviving sufficient statement is the source's Lemma 4.1: $U$ is reciprocal, $b\ge2$, $P=U/[b]_q$ is a polynomial of degree $D\ge3$, $u_0=1,u_1=0$, and $u_s\ge u_{s-1}$ for $2\le s\le\lfloor D/2\rfloor$; additionally, if $b+1\le\lfloor D/2\rfloor$, then $u_{b+1}>u_b$. Under these hypotheses the source proves the two-exception pattern. This counterexample refutes removal of the strictness hypothesis from the final universal question, without proving it necessary for each individual quadruple.

## ASSUMED-UNVERIFIED

Literature-screen completeness and global priority are ASSUMED-UNVERIFIED. The source and nearby theorem checks are bounded; Semantic Scholar returned HTTP 429 and several web responses were ineffective. The unbounded family, complete classification, and neighbouring conjectures remain open within this delivery. No numerical experiment is presented as a universal proof.
