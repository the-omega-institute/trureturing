---
slug: mathar-a027182
bibkey: matharkimberling2026a027182
doi: null
url: https://oeis.org/A027182
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA027182SelfConvolution.result
---

# Mathar and Kimberling's self-convolution recurrence

## Problem

OEIS A027182 revision 8 states Mathar's FORMULA conjecture for the
self-convolution of the rows of Kimberling's A027170 revision 32.
The verbatim source is in
[the source note](../Library/RecurrenceComposition/matharkimberling2026a027182.md),
and the quantified statement is preregistered in
[#23023](https://github.com/the-omega-institute/trureturing/issues/23023).

For $n,k\in\mathbb N$, define
$t(n,k)=\binom{n+2}{k+1}+\binom{n+1}{k}+\binom{n+1}{k+1}+\binom nk$,
$T(n,k)=t(n,k)-t(0,0)+1$, with natural subtraction, and
$g_n(X)=\sum_{k=0}^n T(n,k)X^k\in\mathbb N[X]$.
Put $a_n=[X^n]g_n(X)^2$.
The settling theorem proves, for every $n\ge6$,

$$
2(n+2)a_n+(-17n-23)a_{n-1}+(47n+36)a_{n-2}
+2(-22n-17)a_{n-3}+4(-n+20)a_{n-4}
+8(2n-9)a_{n-5}+24(12n-47)=0.
$$

The coefficient arithmetic is in $\mathbb Z$ and sequence indices use
natural subtraction. The proposition asserts this recurrence; it does
not assert a separate formal D-finiteness predicate.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Four binomial terms defining $t$ in A027170 | `t` | Same terms, order and natural carrier. |
| $T(n,k)=t(n,k)-t(0,0)+1$ | `T` | Literal natural subtraction, with the source row domain $0\le k\le n$. |
| Row generating polynomial over $k=0,\ldots,n$ | `g` | Literal finite sum, including both endpoints. |
| Central coefficient of the squared row polynomial | `a` | Coefficient $n$ of $g_n^2$. |
| Six sequence terms and affine forcing term in the FORMULA field | `claim`, `result` | Every coefficient and lag is preserved, over all natural $n\ge6$. |
| Published offset $1$ | Total `a` with $a_0=1$ | The extension is explicit; no extra hypothesis restricts the published range. |
| No additional source clause | Integer casts and total definitions | Coefficient arithmetic is integer arithmetic; totality outside the source row domain does not weaken the quantified claim. |

## Motivation

The frozen settling GID is
`D5/S1/Recurrence/MatharA027182SelfConvolution.result`.
It resolves the named recurrence conjecture as **Proved**, using
`admission_basis: open-problem-resolution (#23023; Proved)`.
All theorem proofs in this module are bind-only after expansion to pinned
Mathlib; consumed private helpers organize the proof. No escape witness
or independent supporting module is claimed. The module is general in
the index and has `utility: none`; finite calculations are external evidence.

## Gap

The published recurrence is proved. Minimal annihilator order,
parameterized diamondization families and integration with a formal
D-finiteness API remain open. Literature completeness is
`ASSUMED-UNVERIFIED`.

Escape registration for
`D5.S1.Recurrence.MatharA027182SelfConvolution.result` is unfinished:
[#23110](https://github.com/the-omega-institute/trureturing/issues/23110).
The guarded and pointwise equality templates do not by themselves supply
the source reconstruction, realization bridge and variation/sensitivity
evidence for the natural-index guard and six coupled shifted evaluations.
No validated registration is asserted.

## Route

The private theorems `t_pascal` and `row_cast` reduce the row to
$T(n,k)=2\binom{n+2}{k+1}+\binom nk-4$ on its row domain.
`row_symm` proves symmetry under $k\mapsto n-k$, and `square_sum` turns
central self-convolution into a square sum. `sum_A_sq`, `sum_A` and
`sum_AB` apply the binomial square-sum, row-sum and Vandermonde identities.
`closed_form` gives

$$
a_n=4\binom{2n+4}{n+2}+4\binom{2n+2}{n+1}+\binom{2n}{n}
-72\,2^n+16n+40.
$$

Write $h_n$ for the three-binomial part. Four instances of
`Nat.succ_mul_centralBinom_succ` give `h_recurrence`:

$$
2(m+4)h_{m+2}-(7m+27)h_{m+1}-(4m+2)h_m=0.
$$

For an arbitrary integer sequence $f$, let
$Bf(m)=2(m+4)f_{m+2}-(7m+27)f_{m+1}-(4m+2)f_m$,
and let $Lf(m)$ be the published six-term homogeneous expression at
$n=m+5$. The private theorem `operator_factor` proves

$$
Lf(m)=Bf(m+3)-5Bf(m+2)+8Bf(m+1)-4Bf(m).
$$

Thus `h_annihilated` proves $Lh=0$. Substitution of `closed_form` into
this identity gives `result_shift`, and index translation gives `result`.

## Falsifier

A natural index $n\ge6$ with nonzero residual would contradict `result`.
The source's displayed example says $5^2+10^2+5^2=120$; its defining
expression and sequence data instead give $150$. That arithmetic typo
is separate from the recurrence conjecture.

## Evidence

Kernel evidence is the settling theorem and its consumed private
helpers in
[the Lean module](../D5/S1/Recurrence/MatharA027182SelfConvolution.lean).
The public surface consists of `t`, `T`, `g`, `a`, `claim` and `result`.
It imports only pinned Mathlib; there are no direct frozen D5 dependencies.

### Exact computations

The experiment is
[mathar-a027182-recurrence at cf3aaa31442cac5cd2997b9c5577b98e339a310d](https://github.com/the-omega-institute/trureturing-experiments/tree/cf3aaa31442cac5cd2997b9c5577b98e339a310d/docs/reports/mathar-a027182-recurrence).
The referenced `check.py` exists at that revision and its SHA-256 is
`ed87e906c89a49cda14ed1a5cfbd18654a26f99e85b08de1ecccf71d48b7c0c1`.
The command `python3 check.py` exits 0 with `ALL_CHECKS_OK`, checking
the initial values through $a_5$, the closed form for $0\le n\le25$,
the recurrence for $5\le n\le30$, and the exact symbolic operator identity.
These finite computations do not establish the universal theorem.

The command `python3 -i check.py` also exits 0. In that interpreter, the
published `a` and `recurrence_residual` functions were evaluated at
$n=0,1,2,3,4$, padding the finite value list on the right with five copies
of $a_0$ so that Python's negative list indices implement truncated
natural subtraction. This gives residuals
$-1137,-747,-338,-100,-8$, respectively. The computation uses the same
pinned script and SHA-256; no uniform extension below $n=5$ is asserted.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Symmetric row and Vandermonde mechanism | Proved; kernel-checked private `row_symm`, `square_sum`, `closed_form` | $a_n=h_n-72\,2^n+16n+40$ for every natural $n$. |
| Order-two recurrence and universal operator factorization | Proved; kernel-checked private `h_recurrence`, `operator_factor`, `h_annihilated` | Four adjacent central-binomial identities imply $Bh=0$; the displayed factorization holds for every integer sequence. |
| One-step extension of the published range | Proved; kernel-checked private `result_shift` | Every $m\ge0$, hence every $n\ge5$, under the explicit $a_0$ extension. The public `result` states $n\ge6$. |
| Truncated-index lower boundary | Computed; pinned checker evaluated as described in Evidence, exit 0, SHA-256 given there | Residuals at $n=0,1,2,3,4$ are $-1137,-747,-338,-100,-8$; in particular $n=4$ fails. |
| Minimal annihilator order, diamondization parameters and D-finiteness API | Open | Neither the settling theorem nor the finite checks establish these extensions. |

The source's recurrence conjecture therefore becomes a theorem. Its
D-finite wording is supported by an explicit polynomial-coefficient
recurrence; no separate Lean D-finiteness API result is asserted.
No further source theorem depending on this conjecture was identified
in the preregistration's inspected OEIS entries. Dependence in unread
later literature remains unverified.

## ASSUMED-UNVERIFIED

The preregistration's literature screen found no prior settlement in its
searched scope. It records rate limits at OpenAlex, Semantic Scholar and
the arXiv API; restricted MathDB access; and three identified Mathar
works unavailable in full. The inspected Zenodo survey treats A027175
and mentions A027170, without settling A027182. Completeness of that
screen and continued external open status are `ASSUMED-UNVERIFIED`.
The search is not a proof of absence, and the recurrence proof is not
an independent novelty certification.
