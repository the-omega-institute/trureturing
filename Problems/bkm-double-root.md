---
slug: bkm-double-root
bibkey: ballotkimberlingmoses2017polynomialtrees
doi: 10.1080/00150517.2017.12427731
url: https://www.fq.math.ca/Papers1/55-5/BallotKimberlingMoses.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PolynomialTrees/BallotKimberlingMosesDoubleRootGeneration.result
---

# The double-root row of Ballot–Kimberling–Moses Table 5

## Problem

Christian Ballot, Clark Kimberling and Peter J. C. Moses, *Linear Recurrences
Originating From Polynomial Trees*, The Fibonacci Quarterly 55(5), 15–27,
Table 5, gives $q(x)=x^2-2x+1$, initial counts
$1,1,2,4,7,11,16,22,29,37,46$, and recurrence coefficients $3,-3,1$.
Section 5 states: “Most of the entries in the column headed ‘linear recurrence’
are conjectured as ‘eventual’; i.e., the recurrence applies after some unspecified
number of initial terms.” The selected assertion and literal Lean conventions
are specified in [the problem statement](https://github.com/the-omega-institute/trureturing/issues/23638).
The Library note records the published PDF quotations and verified locator.
A source arXiv identifier has not been located.

Start at $0$ in $\mathbb Z[x]$, applying $p\mapsto(p+1)\bmod q$ or
$p\mapsto xp\bmod q$, with monic remainders. Let $S_n$ contain the distinct labels
reached within $n$ edges. Put $g(0)=\{0\}$ and $g(n+1)=S_{n+1}\setminus S_n$,
and $G_n=|g(n)|$. The assertion is
$\exists N\geq3\;\forall n\geq N,\;G_n=3G_{n-1}-3G_{n-2}+G_{n-3}$,
with the recurrence arithmetic over $\mathbb Z$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Table 5 polynomial $x^2-2x+1$ | `q` | Literal integer polynomial. |
| Root $0$; children $p+1$ and $xp$ modulo $q$ | `addChild`, `mulChild`, `seen` | Literal monic-remainder operations and finite recursion. |
| Remove repeated labels | `seen`, `generation` | Finsets remove same-generation duplicates; set difference removes every earlier label. Parent order does not change the label sets. |
| $G_n=|g(n)|$, including the root | `G` | Natural cardinality of the finite generation. |
| Eventual recurrence $3,-3,1$ | `claim`, `result` | Existential threshold, every tail index, and integer arithmetic are retained; the proof chooses $N=3$. |

The pair coordinates occur only in private proof definitions; the public sequence
retains the source's polynomial operations. Natural predecessor subtraction is
used only under $n\geq N\geq3$ in the recurrence. The zero root is a separate case.

## Motivation

`D5/S3/Combinatorics/PolynomialTrees/BallotKimberlingMosesDoubleRootGeneration.result`
proves the complete selected assertion. The object is the polynomial-form tree
$T((x-1)^2)$; evaluating at the root $1$ loses the derivative coordinate and gives
a different tree. No claim about the six subsequent restricted families is needed.

## Gap

The source records a computer-detected eventual recurrence without a proof of this
row. The bounded literature screen in #23638 found no prior settlement of this
specific quotient-tree assertion. Its completeness is ASSUMED-UNVERIFIED.
The unread MathOverflow discussion, incomplete author bibliographies, unavailable
source TeX and blocked searches remain limitations of that screen.

## Route

Write $L(a,b)=C(a)+C(b)(X-1)$ for natural coordinates. The private declarations
`label_injective`, `addChild_label` and `mulChild_label` establish injectivity and
$A(a,b)=(a+1,b)$, $M(a,b)=(a,b+a)$ for the literal operations.

The induction `seen_spec` establishes exactly
$S_n=\{L(0,0)\}\cup\{L(a,b):0<a\leq n,\;b\leq a(n-a)\}$.
For a positive target $a$, an attaining predecessor subtracts $a$ from $b$ when
$b\geq a$; otherwise it decreases $a$ by one, with the root handled separately.
The declarations `generation_succ_spec` and `generation_succ_eq` partition each
shell into its top label and disjoint finite intervals. `G_succ` counts the
intervals, `G_sum` includes generation zero, and `G_difference` yields the
consecutive-difference identity used by `result`.

## Falsifier

A missing or extra reachable label relative to the exact reach bound would
invalidate the shell argument. A recurrence failure at any index $n\geq3$ would
contradict the settling theorem. A previously published settlement would affect
the literature claim, without changing the kernel-checked mathematical statement.

## Evidence

The Lean owner and its Blueprint Scribe provide the proof and expanded statement.
The axiom closure is bounded by the standard permitted set
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The finite experiment is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2962a068f496f8cf04ab18cfb52ecbc1dd319504/docs/reports/ballot-kimberling-moses-t5).
At commit `2962a068f496f8cf04ab18cfb52ecbc1dd319504`, file
`docs/reports/ballot-kimberling-moses-t5/check.py` has SHA-256
`af584d951450cc7b2b36bfbcba32add83575dca091ade00b280f816c271409f6`.
Command `python3 docs/reports/ballot-kimberling-moses-t5/check.py`, exit 0,
compares entire integer-remainder and pair BFS shells through depth 100:
166751 visited points, 101 shell counts, recurrence indices 3–100, zero
mismatches, `ALL_CHECKS_OK`. Universal-tree generations 0–14 and all 16383
nonzero labels in them also satisfy the degree/weight and remainder-coordinate
checks. These are finite computations.

The escape audit of the public `result` is unfinished:
[issue #24117](https://github.com/the-omega-institute/trureturing/issues/24117).
No faithful compiled source realization, bridge and observation-dependence
evidence for an enrolled four-slot registration is supplied; no validated
registration is claimed.

## Triage

1. **Proved; kernel-checked:** literal operations have injective natural-pair
   labels $L(a,b)$, with $A(a,b)=(a+1,b)$ and $M(a,b)=(a,b+a)$.
   Evidence: `label_injective`, `addChild_label`, `mulChild_label`.
2. **Proved; kernel-checked:** all finite reach balls and shells are exact,
   including the sole zero-$a$ root. In generation $n+1$, each non-top positive
   row has exactly $a$ labels and the top row has one. Evidence: `seen_spec`,
   `generation_succ_spec`, `generation_succ_eq`, and the interval-cardinality
   computation within `G_succ`.
3. **Proved; kernel-checked:** $G_n=1+\sum_{a<n}a$ for every natural $n$;
   the source recurrence holds for every $n\geq3$, with $N=3$.
   Evidence: `G_sum`, `G_difference`, `result`.
4. **Computed:** both entire BFS shells agree through depth 100, with 166751
   points, 101 shell counts, recurrence indices 3–100 and zero mismatches;
   `ALL_CHECKS_OK`. Evidence: the pinned experiment and exact command, exit
   code and SHA-256 in Evidence. No uniform conclusion is inferred from this
   finite check.
5. **Open:** other Table 5/6 rows, all six $k$-restricted families and higher
   multiplicity quotients are outside the proof. This module settles none of
   these neighbours.

### What the settlement shows

**Proved in this module:** the exact finite reach invariant explains quadratic
shell growth through an interval partition. Subtracting consecutive instances
of `G_sum` gives `G_difference`; its second difference is constant, and the third
finite difference vanishes. The zero root and each top row are included, so the
threshold $N=3$ requires no exceptional initial segment beyond the three
predecessor indices. This settles the entire selected row for unbounded depth.

**Open:** the argument is specialized to the fixed double-root polynomial.
It proves no assertion for higher multiplicities or other rows and removes no
$k>2$ restriction from the source's neighbouring families. No downstream source
result relying on another conjecture is asserted here.

## ASSUMED-UNVERIFIED

Literature-screen completeness and absence of another published settlement are
ASSUMED-UNVERIFIED. Source evidence uses the published journal PDF; no arXiv
source or TeX quotation is claimed. The finite experiment's scope ends at depth
100; the unbounded recurrence rests on Lean. The escape audit remains unfinished
under #24117.
