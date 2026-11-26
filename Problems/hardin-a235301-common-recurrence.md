---
slug: hardin-a235301-common-recurrence
bibkey: hardin2014a235301
doi: null
url: https://oeis.org/A235301
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C
---

# Hardin's common order-ten recurrence for stress-three rectangles

## Problem

Write $C(h,w)$ for the number of indexed $(h+1)\times(w+1)$ arrays
over $\{0,1,2,3\}$ in which every contiguous $2\times2$ block has
absolute difference three between its diagonal and antidiagonal sums.
For every fixed $k\ge 1$, OEIS A235301 proposes that both $a(n)=C(n,k)$
and $a(n)=C(k,n)$ satisfy the following equality over the integers,
for every $n\ge 11$.

$$
\begin{aligned}
a(n)&=3a(n-1)+17a(n-2)-57a(n-3)-86a(n-4)\\
&\quad+372a(n-5)+76a(n-6)-972a(n-7)+360a(n-8)\\
&\quad+864a(n-9)-576a(n-10).
\end{aligned}
$$

The first full window uses indices 1 through 11.
[Pinned table](../Library/Automata/hardin2014a235301.md)
[Pinned coefficients](../Library/Automata/hardin2014a235292.md)

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Indexed rectangle, four symbols | `C 3 3 h w` counts functions `Fin (h+1) × Fin (w+1) → Fin 4`. |
| Every contiguous block has absolute diagonal difference three | The count restricts the grid by `Legal 3` over all coordinates in `Fin h × Fin w`. |
| Common signed recurrence | `hardin_a235301` explicitly gives both signed ten-lag equalities over integers. |
| Positive indices | `1 ≤ k` and `11 ≤ n` ensure every count in both windows has positive sides. |

## Motivation

This is the boundary case of constant-stress rectangles where stress
equals the largest symbol. The strict-deficit equivalence requires
$d<M$ and does not cover $d=M=3$.
[Problem #34376](https://github.com/the-omega-institute/trureturing/issues/34376)

## Gap

The A235301 revision 7 and A235292 revision 10 describe the recurrence
as empirical. The preregistered search in #34376 found no exact proof
within its stated literature and repository scope.

## Route

In the ring modulo six, both possible signed block differences equal
three. Subtracting $3ij$ from the $(i,j)$ entry gives a grid with
vanishing mixed differences. It has the additive form determined by
two boundary words, with one normalized initial letter. The crossing
constraints give exactly the valid original rectangles on positive
sides.

A weighted row transfer records the row parity, last letter and the
mask of compatible column edges. Every fixed positive width gives an
acceptance function depending only on the mask. In the kernel-checked
certificate, the first three signed residual vectors satisfy
$R_2=-3R_1-2R_0$ and the first two have zero sum after grouping by mask.
The linear transfer action propagates the relation and consequently
all residuals have zero evaluation on mask-dependent acceptance
functions. Transposition supplies the other axis.

## Falsifier

Any verified literal rectangle count violating either signed identity
at positive fixed side and left index at least eleven refutes the claim.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301`.
Its Lean axiom closure is `propext`, `Classical.choice` and `Quot.sound`.
An independent literal cardinality and the first full window instantiate
the theorem in Lean.

## Triage

### What the settlement shows

The result covers every positive fixed side. The two axes share the
same coefficients. Restricting the recurrence to the square diagonal
changes both dimensions simultaneously. The A235290 proof uses the two
axial recurrences and a checked initial window for the simultaneous
shift residual. [A235290 dossier](hardin-a235290-diagonal-recurrence.md)

## ASSUMED-UNVERIFIED

Global proof priority and minimal recurrence order remain unverified.
