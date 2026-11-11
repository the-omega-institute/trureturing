---
slug: coons-strict-adjacent-multiplicity-growth
bibkey: coons2026calkinwilf
doi: null
url: https://arxiv.org/html/2611.08109v1
triage: theorem
motivation_gids:
  - D5/S1/Digit/CoonsAdjacentGrowthRefutation.result
---

# Equal adjacent growth exponents in Coons's partition question

## Problem

Michael Coons, *The Calkin–Wilf problems on ℓ-ary partition functions*,
arXiv:2611.08109v1, Section 3, “Further remarks”, asks immediately before
Acknowledgements:

> As a generalisation, we ask whether it is always the case that

$$
\limsup_{n\to\infty}\frac{\log b_{k,\ell}(n)}{\log n}
<
\limsup_{n\to\infty}\frac{\log b_{k+1,\ell}(n)}{\log n},
$$

> for all $k\geqslant\ell-1$?

The source displays CC BY 4.0. This quotation transcribes its words and
mathematical alttext; display layout is adapted. Full attribution, license
link and definition locators appear in the
[source note](../Library/Digit/coons2026calkinwilf.md).

For natural $\ell\geq2$, $k\geq\ell-1$ and $n\geq0$, define

$$
\mathcal P_{k,\ell}(n)=
\left\{a:\mathbb N\to\mathbb N:\operatorname{supp}(a)\text{ finite},\quad
\forall i\ a(i)\leq k,\quad \sum_{i\in\operatorname{supp}(a)}a(i)\ell^i=n\right\},
\qquad b_{k,\ell}(n)=\#\mathcal P_{k,\ell}(n).
$$

This is exactly the coefficient count in Section 2's product
$\prod_{j\geq0}(1+z^{\ell^j}+\cdots+z^{k\ell^j})$.
Zero padding does not create distinct objects, and $b_{k,\ell}(0)=1$.
The weight $\ell^i$ follows the product and the prose; the introduction's
printed general term $a_m\ell^n$ has an index typo.
Although the introduction starts with $k,\ell\geq2$, Section 3's explicit
range includes $(\ell,k)=(2,1)$ through the same definition.

Write, with all indices natural and suprema and infimum in the extended reals,

$$
A(k,\ell)=\inf_{\substack{N\in\mathbb N\\N\geq2}}
\sup_{\substack{n\in\mathbb N\\n\geq N}}
\frac{\log b_{k,\ell}(n)}{\log n}.
$$

The complete statement is
$\forall\ell\geq2\ \forall k\geq\ell-1,\ A(k,\ell)<A(k+1,\ell)$.
There is no extra finite-exponent hypothesis. The count is finite because
nonzero digits have bounded indices; ordinary radix expansions give a
positive count throughout this parameter range. Inputs zero and one do not
enter any tail.

| Source object or clause | Formal counterpart in `CoonsAdjacentGrowthRefutation` |
| --- | --- |
| Multiplicity at each power, counted once | `a : Nat →₀ Nat` and `Partitions k ell n` |
| Weighted sum equals the natural input | `weight ell a = n` |
| Coefficient $b_{k,\ell}(n)$ | `count k ell n := Nat.card (Partitions k ell n)` |
| Finiteness and positivity of the actual carrier | `partitions_finite`, `count_positive` |
| Logarithmic ratio at each natural input | `readout k ell n` |
| Every natural tail, in extended reals | `exponent k ell : EReal` |
| All radices and adjacent bounds, including the binary endpoint | `claim : Prop` |
| Negative answer to the whole universal statement | `result : Not claim` |

## Motivation

Increasing $k$ includes every old representation, so point counts are
nondecreasing. Strict increase of their asymptotic exponent is a stronger
assertion: the extra digits can leave the upper exponent unchanged.
The admissible pair $(\ell,k)=(4,5)$ demonstrates this distinction:

$$
A(5,4)=A(6,4)=\tfrac12.
$$

One such equality refutes the entire universal strict-adjacency statement.
It does not answer the separate following sentence, “What about the limit
inferiors?”, or the preceding first-linear-maximal-growth question CW2.

## Gap

The source leaves the displayed adjacent-multiplicity question unanswered.
The bounded fulltext readings of Calkin–Wilf's 19-page preprint and
Coons–Spiegelhofer's published eight-page hyper-expansion paper found no
exact prior settlement in those inspected texts. The former contains a
linear-threshold question and fixed-binary-family maxima; the latter treats
digit bound equal to radix, with an argument shift. These statements cannot
be substituted for the displayed universal comparison without further
bridges. Their scope and bibliographic identifiers are in the source note.

The exact identity of the obtained Calkin–Wilf copy with its cited 2009
update is unverified. Reznick's chapter fulltext was not obtained. These
limits preclude an exhaustive-literature or worldwide-novelty assertion.

## Route

Fix $5\leq k\leq6$. The proof uses the same finite-support carrier at every
step, rather than a recurrence model without a representation bridge.

For $n<4^{m+1}$, every partition has zero digits above index $m$, and its
digit at index $m$ is less than four. Record the quotients
$\lfloor a(i)/4\rfloor\in\{0,1\}$ for $i<m$; the top quotient is zero.
Two partitions with the same record have equal units digits modulo four
because their weighted sums agree. Their units quotients agree as well,
so their units digits agree. Remove the common units digit and divide by
four; induction recovers every digit. This injects the actual partition set
into $\{0,1\}^m$, proving

$$
n<4^{m+1}\quad\Longrightarrow\quad b_{k,4}(n)\leq2^m.
$$

With $m=\lfloor\log_4 n\rfloor$, this gives
$b_{k,4}(n)^2\leq4^m\leq n$ for every $n\geq1$.
Thus the logarithmic ratio is at most $1/2$ at every $n\geq2$.

For the matching lower bound, set $R_m=\sum_{i=0}^{m}4^i$, so that
$4^m\leq R_m<4^{m+1}$. Choose arbitrary binary interior carries
$c_1,\ldots,c_m$, with $c_0=c_{m+1}=0$, and put

$$
a(i)=1+4c_{i+1}-c_i\quad(0\leq i\leq m),\qquad a(i)=0\quad(i>m).
$$

These digits belong to $\{0,1,4,5\}$ and are admissible for both bounds.
The identities $a(i)+c_i=1+4c_{i+1}$ telescope after multiplication by
$4^i$, giving weighted value $R_m$. The recurrence recovers all carries
from the digit function and $c_0=0$, so the $2^m$ choices remain distinct
even when the top digit vanishes. Combined with the upper bound, this proves
$b_{k,4}(R_m)=2^m$.

For $m\geq1$ it follows that

$$
\frac{\log b_{k,4}(R_m)}{\log R_m}
\geq\frac{m\log2}{(m+1)\log4}
=\frac{m}{2(m+1)}.
$$

Given any natural tail threshold $N\geq2$ and real $r<1/2$, choose a natural
$m>\max\{N,2r/(1-2r)\}$. Then $R_m\geq N$ and
$r<m/(2(m+1))$. Therefore every whole-tail supremum is at least $1/2$;
the all-input upper bound makes it exactly $1/2$. Taking the literal
extended-real infimum of those suprema gives $A(k,4)=1/2$.
The repunits supply witnesses within every tail; they never replace the
tail's domain by a subsequence or by block maxima. Substitution of $k=5$
and $k+1=6$ contradicts strictness at the same radix four.

## Falsifier

A counterexample to the all-input square bound, a failure of the carry map's
weighted value or injectivity, or a failure of the every-tail argument would
break this proof mechanism. The upper-bound map must distinguish the actual
functions, including functions with a zero top digit. A proof of the literal
universal `claim` would contradict the stated refutation in the same formal
system; finite data or a strict comparison at another parameter pair would
not do so.

## Evidence

The retained mathematical source is
`D5/S1/Digit/CoonsAdjacentGrowthRefutation.lean`; its corresponding exposition
is `Blueprint/D5/S1/Digit/CoonsAdjacentGrowthRefutation.scribe.cs`.
The source's `count_upper`, `count_repunit`, `tail_supremum` and
`exponent_eq_half` supply the bounds and the full-tail equality above.
`result` has the literal conclusion `Not claim`, using the admissible
pair $\ell=4,k=5$. The associated audit source is
`Reg/D5/S1/Digit/CoonsAdjacentGrowthRefutation.lean`.

The separate source-function audit for `partitions_finite` remains unresolved
at the function operand. Its [disclosure](https://github.com/the-omega-institute/trureturing/issues/29338#issuecomment-6807673538)
identifies that gap; the link supplies neither a proof nor completion of the
audit. The existing compiled mathematics and helper audit evidence are
retained. Independent source/form and admission assessment is still required;
this dossier supplies source content for that assessment.

## Triage

`theorem`: the mathematical candidate refutes the exact strict-adjacent
limsup statement by equality of two admissible adjacent exponents.
The typed `Refuted` annotation refers to this dossier's unchanged slug.
This description does not certify canonical admission, publication or a
solution-count credit, and asserts no irreducibility or historical priority.

## ASSUMED-UNVERIFIED

Literature completeness and the Calkin–Wilf 2009 version identity remain
unverified. No Reznick chapter theorem was checked from fulltext. The bounded
readings do not establish global openness or absence of prior solutions.
The introductory typo and endpoint convention are resolved as stated above
from the source's own product and final quantifier, without additional author
confirmation. The source-function audit limitation remains as disclosed;
the separate liminf and first-linear-threshold questions remain outside this
statement.
