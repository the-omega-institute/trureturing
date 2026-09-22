[Index](../../marked_head_profile.md) · [Balanced selection](408-a-balanced-five-tree-selection-controls-all-heights.md) · [Fixed-depth gluing](409-ternary-prefixes-preserve-terminal-common-laws.md)

# An initial ternary budget permits an arbitrary stopping frontier

Three initial ternary levels can supply enough margin to glue actual
terminal laws at different later depths. The resulting single law
passes the finite-height moment target even when its terminal profiles
cannot pass the synchronized, all-prefix-height interface of report 409.

These are ordinary mathematical proofs and exact research constructions,
not Lean certification, source-minimax optimality or an unrestricted
Erdős #7 conclusion. The stopping architecture and actual terminal
probabilities are explicit sufficient conditions.

## One law on an actual finite stopping tree

Fix a total seven-adic height `K`. Let `F` be the leaves of a finite
rooted tree of actual seven-adic prefixes, with exactly three distinct
selected children at every internal node. Prefixes read the lowest
digit first. The leaves are prefix-free. Write `h(u)` for leaf depth,
and assume `a<=h(u)<K`. The depths need not agree; their spread has
no uniform bound as `K` varies.

At each leaf `u` choose an actual probability `eta_u` on
`{1,2,3,4} x Z/7^(K-h(u))`, before the layout phases are chosen.
Require its embedded support `(r,u+7^h(u)*y)` to lie in the given
global source `R`. For constants `beta<=gamma`, suppose every tail
law has row mass at most `beta`, pure prefix mass at positive depth
`j` at most `3^(-j)`, and joint row/prefix mass at most
`gamma*3^(-j)`.

Define one actual probability by

\[
 \nu=\sum_{u\in F}3^{-h(u)}(i_u)_*\eta_u,
 \qquad i_u(r,y)=(r,u+7^{h(u)}y).
 \tag{AS1}
\]

The supports are disjoint. The finite full-ternary Kraft identity
`sum_u 3^(-h(u))=1` proves normalization.

If a selected prefix `v` at depth `n` is still in the stopping tree,
the same Kraft identity on its descendants gives mass `3^(-n)`
and row mass at most `beta*3^(-n)`. Below an already stopped leaf
`u`, the tail estimates give pure mass at most
`3^(-h(u))*3^(-(n-h(u)))=3^(-n)` and joint mass at most
`gamma*3^(-n)`. Prefixes outside the support have zero mass. Thus

\[
 \begin{aligned}
 \operatorname{pure}_n&\le3^{-n}&& (0\le n\le K),\\
 \operatorname{joint}_n&\le\beta3^{-n}&& (0\le n\le a),\\
 \operatorname{joint}_n&\le\gamma3^{-n}&& (a<n\le K).
 \end{aligned}
 \tag{AS2}
\]

No common stopping depth was used.

## The finite budget preserves all original independent phases

Use the squared-load maximum `Gamma_(1,K)` from report 409, retaining
every original divisor label of `5*7^K` with its own independent
phase. A phase in the unused fifth row gives an empty event. At
largest seven-adic depth `n`, the square expansion has `2n+1`
ordered depth pairs, one pure/pure type and three row-constrained
types. Every compatible intersection is its literal LCM cell.

Write

\[
 t_n=\sum_{j=0}^{n}(2j+1)3^{-j}=3-(n+2)3^{-n},
 \qquad A=1+3\beta,\quad D=1+3\gamma.
\]

Applying AS2 under the same law AS1 gives

\[
 \boxed{\Gamma_{1,K}(\nu)\le U_{a,K}:=At_a+D(t_K-t_a).}
 \tag{AS3}
\]

Hence the exact sufficient finite test is
`(2-D)t_K+(D-A)t_a>=0`. If `beta<=1/3<=gamma`, a sufficient
height-independent budget is

\[
 g_a:=3(2-A)-(D-A)(a+2)3^{-a}\ge0,
 \tag{AS4}
\]

since the exact finite target gap is

\[
 2t_K-U_{a,K}=g_a+(D-2)(K+2)3^{-K}.
 \tag{AS5}
\]

The smaller joint masses in the first `a` levels pay for the larger
joint masses permitted after different stopping depths. The terminal
profiles need not pass report 409's two all-prefix-height budgets.
Failure of AS4 is a certificate failure, not a source obstruction.

## Three initial levels suffice for the two-level seed

The selected 25-point seed law from report 408 has maximum row mass
`8/25`, pure prefix masses `1/5,1/25`, and joint maxima `4/25,1/25`.
Attach actual uniform five-ary tails independently at its selected
labelled points. For remaining height `d>=2`, row masses are unchanged,
pure depth-`j` mass is `5^(-j)`, and joint mass is at most `4/25`
at `j=1` and `5^(-j)` at `j>=2`.

These laws satisfy the tail interface with

\[
 \beta=\frac8{25},\quad\gamma=\frac{12}{25},\quad
 A=\frac{49}{25},\quad D=\frac{61}{25}.
\]

The joint bound is exact at the first tail digit:
`(12/25)/3=4/25`. For `j>=2`, the ratio `3^j*5^(-j)` is at most
`9/25<12/25`. Pure caps follow from `5^(-j)<=3^(-j)`.
Different leaves can use different row permutations, prefix-preserving
digit relabellings, tail trees and remaining heights.

For every such stopping frontier with minimum depth at least three,

\[
 \Gamma_{1,K}(\nu)\le\frac{49}{25}t_3
                      +\frac{61}{25}(t_K-t_3),
\]

\[
 \boxed{
 2t_K-\Gamma_{1,K}(\nu)
 \ge\frac7{225}+\frac{11(K+2)}{25\,3^K}>\frac7{225}.
 }
 \tag{AS6}
\]

This is a quantified extension to asynchronous stopping, without
a uniform bound on the spread of stopping depths.

## One actual law outside every synchronized 409 certificate

Take `K=8` and all 27 ternary prefixes of depth three. Stop at 26
of them. At the remaining prefix, keep one continuing child and stop
at the other two; repeat until depth six, where all three children
stop. The resulting 33 leaves have depths three, four, five and six.
At each leaf use the same report-408 seed and row names, followed by
uniform five-ary tails to total height eight. Every tail and the global
law have row masses `(8,5,5,7)/25`.

The exact global pure and joint maxima are

\[
 (m_n,c_n)=
 \begin{cases}
 (3^{-n},\frac8{25}3^{-n}),&0\le n\le3,\\
 (3^{-n},\frac{12}{25}3^{-n}),&4\le n\le6,\\
 (\frac15 3^{-6},\frac4{25}3^{-6}),&n=7,\\
 (\frac1{25}3^{-6},\frac1{25}3^{-6}),&n=8.
 \end{cases}
 \tag{AS7}
\]

For a synchronized prefix depth `q in {0,1,2,3}`, the tight common
tail caps are AS7 at depth `q+j`, multiplied by `3^q`. Any nominated
row cap admitted by report 409 lies in `[8/25,1/3]`. The best possible
intercept budget therefore uses `beta=1/3`, or `A=2`; increasing the
pure or joint tail caps only worsens it. With `d=8-q` and `C` the report-409
weighted tail budget, the exact best intercepts are

| Cut `q` | `2A-C-2(d+2)3^(-d)` at `A=2` |
| --- | --- |
| 0 | `-473/164025` |
| 1 | `-238/2025` |
| 2 | `-6547/18225` |
| 3 | `-4724/6075` |

Thus no admissible profile parameters repair a 409 certificate for
this law at these cuts. This checks every allowed nominated row cap,
not just the smallest actual one.

For `q>=4`, this law cannot be uniform on one complete ternary prefix:
at depth four it has `26*5+3=133` positive prefixes, exceeding
`3^4=81`. Each later positive prefix has at least three positive
children until height eight, so the strict excess persists. The same
law is therefore outside the synchronized constructor at these cuts
as well. Another successful 409 law on the same source is not excluded.
AS6 still certifies this actual law.

## Actual admissible sources support the asynchronous construction

At every internal stopping-tree node, place its three recursively
built continuing sources in the selected children, and full five-ary
tails in a fixed row `r_0` in two additional children. At every
stopped leaf, use the report-408 source with five-ary tails to the
remaining height, which is at least two in this family. For this
source construction, all rows at the same seed seven-residue share
the same attached tail tree, so its projection remains a complete
five-tree. The probability construction above does not require this
additional source-family convention.

The source projection is a complete five-tree. Each row pair excluding
`r_0` has three continuing children carrying pair-ternary trees.
Each pair containing `r_0` has the two private children and a continuing
child. Thus all six pair conditions hold. A proper row set omitting
`r_0` lacks both private children; a proper row set containing `r_0`
has no full-five continuing child, by induction from the seed.
No proper row set supports a full five-tree.

In any uniform full-five selection, a leaf outside `r_0` must pass
through continuing children during at least the first three levels.
Its outside-row mass is at most `(3/5)^3`, so the mass of `r_0` is
at least `98/125>11/20`. This violates the necessary row-mass
consequence of report 408's balance criterion for every such selection.
The nonuniform law AS1 nevertheless satisfies AS6.

## Exact controls and scope

[adaptive_ternary_stopping_common_law.py](../../frontier/cover-geometry/adaptive_ternary_stopping_common_law.py)
constructs and verifies arbitrary supplied actual ternary frontiers
and tail probabilities under AS4. It also constructs the admissible
padded source family. Exact checks cover differing stopping depths,
independently rotated terminal row laws, every prefix cap, and literal
independent layout controls. Twenty-one malformed inputs are rejected
with validation active under Python optimization. Two additional
controls have the correct number of positive prefixes but the wrong
branching structure; the synchronized audit checks the actual complete
ternary tree as well as cardinality.

The height-six family has 29 stopping leaves, 16,024 source points
and 3,325 positive law atoms. The height-eight separation has 33
stopping leaves, 400,564 source points and 82,825 law atoms, with
AS3 bound `978437/164025` and AS5 margin `5213/164025>7/225`.
The all-height statement rests on AS1--AS6, not these finite checks.

Report 409 requires a common tail profile satisfying two budgets for
all added prefix heights. The present certificate uses a finite
initial margin and allows terminal joint peaks at different global
depths. Generic gluing and the original-label shell count are reused.
No theorem here guarantees that an arbitrary admissible E7 source
contains a qualifying stopping frontier and actual terminal laws.
That extraction remains the missing bridge to a general source theorem.
