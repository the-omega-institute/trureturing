---
slug: dement-2005-a113249-odd-index-squares
bibkey: dement2005a113249
doi: null
url: https://oeis.org/A113249
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/OEISA113249OddIndexSquares.result
---

# Dement's odd-index square conjecture for OEIS A113249

## Problem

The Name field of [OEIS A113249](https://oeis.org/A113249) defines the integer family by
$a_0=-1$, $a_1=4$, $a_2=-13+6(m-1)+3(m-1)^2$,
$a_3=(m^2-8)^2$, and
$a_{n+4}=m^4a_n+4m^2a_{n+1}-4a_{n+3}$.
Its Comments field states:

> Conjecture: a(m, 2*n+1) is a perfect square for all m, n.

The parameter and index range over natural numbers including zero, and the values
are integers. Subtraction in $m-1$ is integer subtraction. Preregistration
[#19316](https://github.com/the-omega-institute/trureturing/issues/19316) fixes these conventions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Four stated initial values | `a` at indices 0, 1, 2, 3 | Literal integer expressions, including all casts of the natural parameter. |
| Fourth-order recurrence | `a` at index `n+4` | The source recurrence with all indices shifted by four. |
| All family parameters and odd indices | `claim` | Both quantifiers range over the naturals, including zero. |
| Perfect square | Mathlib `IsSquare` over the integers | Existence of an integer whose product with itself is the term. |
| Entire conjecture | `result` | No additional hypothesis. |

## Motivation

The conjecture asks for one square property across every member of the family,
beyond the fixed $m=8$ case recorded at [A113254](https://oeis.org/A113254).
The settling declaration is `D5/S1/Recurrence/OEISA113249OddIndexSquares.result`.

## Gap

The literature screen recorded in #19316 covers A113249 and its related fixed-parameter
entries, exact-phrase searches, MathDB, formal-conjectures, AlphaProof Nexus,
the OEIS Open benchmark and the four arXiv papers named there. It locates a proof
for $m=8$, and no general proof in that searched scope. This is a literature
reading with completeness `ASSUMED-UNVERIFIED`, not an exhaustive priority claim.

## Route

Put $b_0=2$, $b_1=m^2-8$ and $b_{r+2}=-4b_{r+1}-m^2b_r$.
The odd subsequence $C_r=a_{2r+1}$ and $b_r^2$ satisfy

$$
x_{r+3}=(16-m^2)x_{r+2}+(m^4-16m^2)x_{r+1}+m^6x_r.
$$

They agree for $r=0,1,2$. The private declarations `odd_rec` and `b_sq_rec`
establish the two recurrence identities; `odd_window` applies the imported and
consumed `LinearRecurrence.eq_iff_eqOn_range_order` to their initial agreement.
The public `result` applies `IsSquare.sq` to the resulting square expression.

## Falsifier

A natural pair $(m,n)$ for which the literal integer $a(m,2n+1)$ is not an
integer square would contradict `result`.

## Evidence

The Lean source is `D5/S1/Recurrence/OEISA113249OddIndexSquares.lean`.
The Scribe displays the complete definitions of `a` and `claim`, and the full
quantified proposition of `result`, with one `Proved` resolution claim.
The only public theorem is `result`. Its escape audit is unfinished:
[#19434](https://github.com/the-omega-institute/trureturing/issues/19434).
No Reg mirror or validated registration is delivered; the missing evidence is
an exact source reconstruction and typed whole-family variation, sensitivity
and observational-dependence bridge for the universally quantified square claim.

### Experiment

[Registered integer checks](https://github.com/the-omega-institute/trureturing-experiments/tree/995dd5c17c9dc8f5dfdcfe1fc921644e36f489a1/docs/reports/dement-2005-a113249-odd-index-squares).
Command: `python3 docs/reports/dement-2005-a113249-odd-index-squares/check.py`,
run from that experiments checkout; exit 0, `RESULT PASS`.
The script SHA-256 is `d592f768fe3e6df40a781732ee56cdc1f4309edb4957ebcfc6ad53ed5e7899c9`.
It reproduces the listed $m=3$ data, checks $a(m,2r+1)=b_r^2$ for
$0\le m\le60$ and $0\le r<60$, the closed form for $0\le n<122$,
and the doubling identity for $0\le k\le60$, both for $0\le m\le60$.
These finite readings are computations, not evidence of universal quantification.

## Triage

Tier 1 external named conjecture, preregistered in #19316.
`admission_basis: open-problem-resolution (#19316; Proved)`;
`generality: I`; `utility: none`. The proof is classified `bind-only`: its
family-specific identities use normalization, and its uniform equality uses
pinned recurrence uniqueness. Every private helper has a mathematical consumer.
No fixed-parameter certificate, bounded enumeration, checker or numerical
reduction is retained in the Lean module.

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Direct odd-subsequence recurrence route | Kernel-checked: private `odd_rec`, `b_sq_rec`, `odd_window`, consumed by `result`; no closed-form assumption. |
| Reason the route works | Kernel-checked: `odd_rec` and `b_sq_rec` give the identical order-three recurrence; `odd_window` proves agreement of the three-term windows. |
| Fixed-case reuse | Proved in prose from the import boundary: only the two stated Mathlib modules are imported, with no AlphaProof Nexus proof term. The attribution of the recurrence-window pattern is a literature reading recorded in #19316. |
| Universal natural-parameter conjecture | Kernel-checked: `D5.S1.Recurrence.OEISA113249OddIndexSquares.result`. This includes $m=0$ and the repeated-root parameter $m=2$. |
| Closed-form and double-angle explanation | Computed over precisely the experiment ranges above. A general trigonometric formula is open in this Lean delivery; the expression $\cos\theta=-2/m$ requires additional domain conditions and is not asserted at $m=0$. |
| Even indices need not be squares | Proved in prose: the recurrence at $m=3$ gives $a_2=11$, $a_3=1$, $a_4=59$, $a_5=484$, $a_6=81\cdot11+36\cdot1-4\cdot484=-1009<0$. Integer squares are nonnegative. |
| Extension to integer parameters and $\mathbb Z[M]$ | Proved in prose below; not exported as a Lean theorem. |
| Consequences for source results | The conditional odd-square assertion is discharged over natural parameters. No other source theorem is identified in the literature screen as requiring a separate update; completeness remains `ASSUMED-UNVERIFIED`. |

For the polynomial extension, let $M$ be the indeterminate in $\mathbb Z[M]$
and define $A$ and $B$ by the same recurrences and initial values.
The linear combination of the recurrence at $k+2$, minus four times the
recurrence at $k+1$, plus $M^2$ times that at $k$, gives the step-six identity
for $A$. Squaring $B_{r+3}=-4B_{r+2}-M^2B_{r+1}$ and substituting
$B_{r+2}=-4B_{r+1}-M^2B_r$ gives the displayed order-three recurrence
for $B_r^2$ by polynomial expansion. The first three odd values are
$4$, $(M^2-8)^2$, and $(32-6M^2)^2$; these are exactly $B_0^2,B_1^2,B_2^2$.
Induction on that recurrence proves $A_{2r+1}=B_r^2$ in $\mathbb Z[M]$.
Evaluation at any integer parameter preserves all additions and products, so
it proves the integer-parameter extension. If $c_0=1$, $c_1=-2$ and
$c_{k+2}=-4c_{k+1}-M^2c_k$, then $B_r=-c_{r+1}$: the initial values agree
at $r=0,1$, and the same second-order recurrence preserves the equality.
Consequently $A_{2r+1}=c_{r+1}^2$ also holds in $\mathbb Z[M]$.
This argument uses no division or
root-separation hypothesis. The broader polynomial identity and a general
closed form are not claims about the compiled public theorem's statement.

## ASSUMED-UNVERIFIED

Completeness of the external literature search and any novelty or priority
claim beyond its recorded scope are `ASSUMED-UNVERIFIED`.
The four-slot escape audit remains unfinished under #19434; neither the
mathematical proof nor the issue supplies registration completion.
