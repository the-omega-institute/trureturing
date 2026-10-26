---
slug: giacomelli-2026-log-concave-cone-convexity-question
bibkey: giacomelli2026logconcavity
doi: 10.48550/arXiv.2604.14391
url: https://arxiv.org/abs/2604.14391v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex
---

# Giacomelli's cone of infinitely log-concave initial data

## Problem

P. Giacomelli, [arXiv:2604.14391v1](https://arxiv.org/abs/2604.14391v1),
Section 7 (1), printed page 13, asks:

> (Cone of initial data for variable coefficients.) Proposition 3.4 gives a matrix condition on v₀ for log-concavity of a general P-recursive sequence. Characterize the geometry of the cone C∞ = {v₀ : Lⁱ(aₙ) ≥ 0 ∀ n, i} for d ≥ 3. Is it convex? Simply connected?

The convexity question is GIA-1 in preregistration
[#18698](https://github.com/the-omega-institute/trureturing/issues/18698), a tier-1
published question. The [Library note](../Library/Certificates/giacomelli2026logconcavity.md)
contains the source's recurrence and operator definitions.

### Statement echo

The Lean namespace is `D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (3): $a_{n+1}=\sum_{k=0}^{d-1}(p_kn+q_k)a_{n-k}$ for $n\ge d-1$ | `seq` | Literal recurrence, with argument $m=n+1$, increasing-order initial coordinates, and the natural subtraction performed before the real cast. |
| Definition 2.1: $L(a)_k=a_k^2-a_{k+1}a_{k-1}$ | `logConcaveOp` | Literal expression; natural subtraction is truncated. |
| $C_\infty=\{v_0:L^i(a_n)\ge0\ \forall n,i\}$ | `coneInf` | Every $i,n\in\mathbb N$ with $i\le n$; these are the interior indices where the complete dependence window exists. |
| Infinitely log-concave initial data | Iteration zero in `coneInf` | Requires original nonnegative terms. Both witnesses also satisfy the convention starting at $i=1$; the midpoint fails at $i=1$. |
| “for d ≥ 3. Is it convex?” | `claim` | Every natural $d\ge3$ and every pair of real coefficient vectors, using Mathlib's `Convex`. |
| Negative answer to convexity | `result` | Negates the complete affirmative assertion; $d=3$ supplies the counterexample. |
| Characterization and simple connectedness | Separate open items in Triage | Neither is included in the settled assertion. |

There is no additional coefficient hypothesis. The binding definitions are
literal source expressions with the index convention above.

## Motivation

Geometric solutions sit on the zero locus of the log-concavity determinant.
Mixing two such solutions can produce a negative determinant, despite all
interior iterates of each original solution being nonnegative.

## Gap

The source and literature screen recorded in #18698 read the full source PDF
and searched its arXiv citation context, the formal-conjectures catalogue,
repository dossiers and issues. No earlier answer was found in that searched
scope. Literature-search completeness is `ASSUMED-UNVERIFIED`.

## Route

Set $d=3$, $p=(1,-3,2)$ and $q=(3,-2,0)$. Strong induction in `result`
shows that $U=(1,1,1)$ and $V=(1,2,4)$ generate respectively $1$ and $2^n$.
Induction on the operator iterate establishes zero for every $1\le i\le n$;
iteration zero is nonnegative. Thus both initial vectors are in $C_\infty$.
Their midpoint $M=(1,3/2,5/2)$ has
$L(\operatorname{seq}(p,q,M))_1=(3/2)^2-(5/2)\cdot1=-1/4$.
The real convexity assertion would put this midpoint in the same cone,
contradicting its defining inequality at $i=n=1$.

| Declaration | proof_shape | escape_witness | Direct frozen dependencies |
| --- | --- | --- | --- |
| `D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex.result` | content | The conclusion itself: the constructed recurrence counterexample and the all-index recurrence and interior-iterate inductions | none |

The module's admission basis is `open-problem-resolution (#18698; Refuted)`.
There is no anchor atom. No separate supporting or general module is required.

## Falsifier

The witness would fail if either geometric sequence did not solve the stated
recurrence or if the midpoint's first determinant were nonnegative. The
compiled proof establishes membership for both sequences and derives a
contradiction from the midpoint inequality under the literal definitions.
The assertion concerns interior indices; it does not assert zero iterates
at the truncated boundary $n<i$.

## Evidence

The kernel-checked theorem `result` proves `¬ claim`. Its local recurrence
and iterate facts are used inside that proof; they are not additional public
theorems. The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The [exact-rational check](https://github.com/the-omega-institute/trureturing-experiments/tree/f4ac87b685e2850ca65c1fb745b795c83a39ca54/docs/reports/giacomelli-2026-log-concave-cone-convexity)
is pinned to commit `f4ac87b685e2850ca65c1fb745b795c83a39ca54`.
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/giacomelli-2026-log-concave-cone-convexity/check.py 40`; exit 0.
Script SHA-256: `17cbb044ee20dbc54fa1130e3278e2e7844327227ebe1caff9a3ec855701d7a5`.
The implementation seat verified the pinned object and reran those script bytes.
The computation checks the three sequence formulas for $0\le n<40$, all
available interior iterates of the two members through depth $20$, and the
midpoint determinants $-1/4$ and $-1/2$ at indices $1$ and $2$.
At depths without a complete finite window, no additional point is tested.
It is a finite computation, not a proof of a uniform extension.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| GIA-1 convexity question | Proved false in Lean by `result` | One order-three recurrence refutes universal convexity under the binding conventions. |
| Two members and negative midpoint | Proved in prose by the recurrence substitutions and interior-iterate argument below | These are also local steps of `result`; no standalone Lean theorem for them is asserted. |
| Generated sequence formulas on $0\le n<40$ | Computed by the pinned experiment, exit 0 | Includes the midpoint's formula; the module does not assert its all-index formula as a separate theorem. |
| Iterates through depth $20$ and midpoint values at indices $1,2$ | Computed by the pinned experiment, exit 0 | Exact tested finite windows only. |
| Characterization of $C_\infty$ | Open | Membership of two vectors and exclusion of their midpoint is not a characterization. |
| Simple connectedness | Open | Nonconvexity does not decide simple connectedness. |
| A formal theorem for every recurrence admitting two distinct positive geometric solutions | Open | The algebraic mechanism below is proved in prose; no uniform Lean theorem is delivered. |
| Construction of such a recurrence for every $d\ge3$ | Open | The certified witness has $d=3$. |
| Source results depending on affirmative convexity | Literature-reading boundary | Section 7 poses a question; the screen in #18698 establishes no dependent result invalidated by this refutation. Proposition 3.4 is not a dependency of this proof. |

The two witness solutions are verified in prose as follows. For the constant
sequence, the recurrence coefficient sum is
$(n+3)-(3n+2)+2n=1$. For the power sequence, factoring out $2^{n-2}$
leaves $4(n+3)-2(3n+2)+2n=8$ for $n\ge2$, giving $2^{n+1}$.
Both match their prescribed first three terms; strong induction gives the
all-index solutions. A geometric sequence has zero first determinant at
interior indices. Each successive interior iterate is zero, since its
three predecessor values are zero. Original terms are positive. The
midpoint determinant at index one is $-1/4$, so its membership fails.

The failure mechanism has a direct algebraic explanation, proved in prose:
for $r,s>0$, $r\ne s$ and $n\ge1$, distributing the products and cancelling
the pure-power terms gives
$$(r^n+s^n)^2-(r^{n+1}+s^{n+1})(r^{n-1}+s^{n-1})
=-r^{n-1}s^{n-1}(r-s)^2<0.$$
For the midpoint the determinant is one quarter of this expression.
The positivity of $r,s$ and the nonzero square justify strict negativity.
A single positive geometric sequence has zero first determinant at every
interior index, and each further interior iterate is zero. This explains
the surviving geometric members and the failure of closure under their mixture.
Applying the mechanism to an arbitrary recurrence also requires establishing
that both geometric sequences solve that same recurrence. The uniform
formal theorem and its recurrence construction remain open above.

## ASSUMED-UNVERIFIED

- Completeness of the literature search and absence of an earlier published answer beyond the scope recorded in #18698.
- A characterization, simple connectedness, and a uniform Lean theorem for recurrences with two distinct positive geometric solutions remain open in this delivery.
