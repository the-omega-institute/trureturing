---
slug: zhang-2024-l-complexity-question-3
bibkey: zhang2024lcomplexity
doi: 10.48550/arXiv.2411.19364
url: https://arxiv.org/abs/2411.19364v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/ZhangLComplexityEventualStability
---

# Eventual stability of Zhang's l-complexity

## Problem

Pengcheng Zhang, *The 2-complexity of even positive integers*,
arXiv:2411.19364v1, Integers 24 (2024), A109, Question 3, page 10:

> Let l > 1 and define A_l := {n ∈ lZ⁺ : ‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}.

> Can one say anything about the set A_l? For example, is it true that for every n ∈ lZ⁺, there exists m₀ ≥ 0 such that l^{m₀} · n ∈ A_l?

The every-orbit assertion is proved. The broader request to describe $A_l$
and to bound the first stable index remains open here. Preregistration: #19862.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| $l>1$ | Natural parameter `l` with `1 < l`. |
| $n\in l\mathbb Z^+$ | Natural parameter `n` with `0 < n` and `l ∣ n`. |
| Minimal number of copies of $l$, with addition, multiplication and parentheses | Public `value` evaluates the existing `KumarPengTranModularComplexity.Expr`; public `complexity` is the natural infimum of attainable `Expr.leaves`. |
| $A_l$ | Public `A` states positivity, divisibility and the source equality for every natural exponent, including zero. |
| Some $m_0\geq0$ with $l^{m_0}n\in A_l$ | `claim` quantifies over natural `m₀`; public `result : claim` proves it. |

The natural evaluation and minimum are the literal conventions of #19862.
The private `mem_A_iff` identifies them with the frozen evaluator and minimum
at modulus zero through injectivity of the natural-to-integer cast. The
public claim retains the source's natural definitions. No additional premise
or finite cutoff is present.

## Motivation

Every orbit of positive multiples under multiplication by $l$ meets $A_l$.
The result gives permanent linear growth from a suitable translate, rather
than only an observed constant tail in a finite computation.

## Gap

The literature screen recorded in #19862 covers the arXiv version, the
published question, the ordinary-complexity stabilization method and later
abstracts. The search found no dominating settlement of this every-orbit
assertion in that scope. The author's thesis and full texts of four later
papers are outside the inspected scope. Completeness is ASSUMED-UNVERIFIED.

The generic antitone-chain theorem is already in pinned Mathlib and is used
directly. The source-specific obligations are existence of expressions,
the exponential leaf bound and extension by one leaf.

## Route

For $l>1$, structural induction bounds an expression with $s$ leaves between
$l$ and $l^s$. At an addition node both values are at least two, so their sum
is at most their product. A positive multiple of $l$ has an expression by
repeated addition, and the minimum leaf count is attained. Multiplication
by one additional leaf gives $\|lu\|_l\leq\|u\|_l+1$.

For a positive multiple $n$, $n\geq l$. Thus
$l^{m+1}\leq l^mn\leq l^{\|l^mn\|_l}$ and
$\|l^mn\|_l\geq m+1$. Consequently the natural defect
$d_m=\|l^mn\|_l-m$ is positive and nonincreasing.
`WellFoundedLT.antitone_chain_condition` gives a constant tail. Its equality
and the lower bound allow cancellation of natural subtraction, yielding
$\|l^r(l^{m_0}n)\|_l=r+\|l^{m_0}n\|_l$ for every $r\geq0$.

## Falsifier

A natural $l>1$ and positive multiple $n$ such that every translate
$l^{m_0}n$ fails the defining growth equality would contradict `result`.
Finite agreement of computed defects alone does not rule out this falsifier.

## Evidence

Kernel-checked declaration:
`D5.S3.Arith.Congruence.ZhangLComplexityEventualStability.result`, in
`D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.lean`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Finite experiment

[Published experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ffbf16ab17fc78fc53ff70b7bd8850aade42a8d4/docs/reports/zhang-2024-l-complexity-question-3).
The script is `check.py` at that revision, SHA-256
`9fe54cee5d762ca5b2a00f3e3af293281cc1a4815cb399deb2f6c2031d3d21f8`.
The verified bytes were executed with
`python3 /Users/auric/.sshx/bce7d3f527bcf4aa34c6834e/attempt-1/experiment.py`, exit 0.
The script computes $\|54\|_2=8$ and $\|216\|_2=9$; checks Theorem 2(1)
for $0\leq m\leq5$, $1\leq r\leq4$ with $2^m6^r\leq2^{15}$;
and checks Proposition 1's lower bound using floating logarithms with tolerance $10^{-9}$ on positive multiples up to $2^{15}$
for $l=2$ and $3^9$ for $l=3$. For $n<400$ it tests 199 orbits for $l=2$
and 133 for $l=3$, restricted to those upper bounds: zero increases in the
defect and equality of the final two computed values in all tested orbits.
These are computed finite checks, not proofs of the corresponding uniform
extensions or of an explicit first-stability bound.

### Escape audit

The sole public theorem audit target is `result`. Its four-slot escape audit
is unfinished: [issue #21973](https://github.com/the-omega-institute/trureturing/issues/21973).
The existential template does not reconstruct the full universal source
telescope; a complete dependent-family reconstruction, bridge, variation,
sensitivity and observational-dependence evidence is not supplied. There is
no retained Reg registration and no `declared_validated` claim.

## Triage

| Item | Status and evidence |
| --- | --- |
| Every-orbit assertion of Question 3 | Proved, kernel-checked public `result`. |
| Dominating theorem search | Literature reading: no l-complexity settlement found in the scope recorded in #19862; completeness ASSUMED-UNVERIFIED. The generic chain theorem is reused. |
| Discrete-defect mechanism | Proved in prose in Route; source-specific steps are the module's private `value_bounds`, `complexity_mul_le`, `defect_antitone` and `defect_pos`, consumed by `result`. This applies the established method rather than claiming a new general method. |
| Every orbit meets $A_l$ | Proved, kernel-checked `result`. |
| Each orbit has an eventual stable defect | Proved in prose: apply the imported chain condition to the nonincreasing natural defect as in Route. No separate public theorem is asserted. |
| Source values, Theorem 2(1) instances, Proposition 1 instances and finite defect checks | Computed, with precisely the scope, command, exit and SHA-256 in Finite experiment. The exact values and Theorem 2(1) instances have only the computed scope stated above; Route proves the general lower-bound argument and `result` proves eventual stability. |
| Fuller description of $A_l$ | Open; no classification is delivered. |
| Bound on the first stable index $m_0$ | Open; existence supplies no explicit bound. |
| Literature visibility | Literature reading: repo-prior-exposed; supplied search evidence was read. No blinded search or multi-seat consensus is claimed. |

### What the settlement shows

The decisive mechanism is a positive integer defect with a nonincreasing
orbit, proved in prose in Route and used in the kernel-checked `result`.
The conclusion ranges over every natural $l>1$ and every positive multiple
$n$, with no upper bound on either parameter or on the exponent. Positivity
and $l>1$ are the proved scope; relaxation and sharpness outside that scope
are open here.

The source compares this question with ordinary integer-complexity
stabilization under multiplication by three. The proof uses the established
discrete-defect method with this source's expression bound. The finite
checks reproduce the listed source examples and instances; they do not
supply new uniform versions of its other results. No source result is
claimed to depend on this answer without a verified dependency. The
classification of $A_l$ and effective control of $m_0$ are further candidates.

## ASSUMED-UNVERIFIED

Literature completeness and first-publication priority are unverified.
The source and literature checks are attributed to the preregistration's
orchestrator and search seat. The four-slot escape audit remains unfinished
under #21973. No model-diversity or exhaustive theorem-absence claim is made.
