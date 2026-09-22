[Index](../../marked_head_profile.md) · [Root laws](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [All-root obstruction](391-diagonal-prefix-sources-obstruct-the-finite-height-moment-comparison.md)

# Root-optimal laws do not tensorize the full-layout bound

Even after excluding a first root in both coordinates, optimizing the
root probability and using its identical product at two digit levels
need not preserve the proposed second-moment comparison. The seven-point
type-B source of report 390 has exact root minimax `631/166`. The product
of its symmetric optimal root law violates the height-two target `529/81`.

This is a failure of the specified probability construction, not a
counterexample to existence of a good law. On the same 49-point source,
an explicit product with different low- and high-digit laws has full
independent-layout maximum `6157/1000<529/81`. Thus neither correlation
between digit levels nor failure of every product law follows.

The reusable finite separation formula below keeps all nine divisor
labels and arbitrary independent residues. Its integer implementation
supports further source searches. The root proof and exact finite
controls are not Lean-certified. No source here is asserted to arise
as a residual of an actual minimum odd cover, and Erdős #7 remains open.

## 1. A normalized source at every height

Use the seven root points

\[
 B=\{(1,1),(2,2),(2,3),(3,2),(3,4),(4,2),(4,5)\}
       \subset\mathbb Z/5\times\mathbb Z/7.
 \tag{RT1}
\]

Call `(1,1)` type `I`, the three points in column 2 type `H`, and
the remaining three points type `P`. These names label points, not
additional residue classes. For `h>=1`, let `R_h` consist of paired
digit words whose digit pair at every level belongs to `B`:

\[
 R_h=\left\{\left(\sum_{j<h}r_j5^j,\sum_{j<h}c_j7^j\right):
                         (r_j,c_j)\in B\right\}.
 \tag{RT2}
\]

It has `7^h` points and no zero first root in either coordinate.
It meets every product of a complete ternary 5-tree and complete
five-ary 7-tree of depth `h`. Indeed, any three 5-roots contain at
least two of the four active rows; any pair of active rows has at
least three neighbors in `B`. Those neighbors meet every five-element
7-root set. Choose such a root pair and repeat inside the two chosen
subtrees. This recursive choice reaches a point of `R_h`.

The 7-projection is the complete five-ary tree with digits `1,...,5`.
It meets every complete ternary 7-tree at the same depth. These are
the full tree hypotheses, including their literal depths. The claim
does not use a marginal cardinality test in place of tree intersection.

## 2. Exact root minimax

For a probability on `B`, let `Gamma_35` maximize the squared complete
load over all independent residues for divisors `1,5,7,35`, as in
report 390. Permuting the three spoke rows and their private columns
simultaneously preserves the source and all test layouts. Since
`Gamma_35` is a maximum of linear functions of the probability,
averaging a law over these six permutations cannot increase it.
It therefore suffices for minimization to consider per-point masses

\[
 \nu(I)=a,\qquad \nu(H)=b,\qquad \nu(P)=c,
 \qquad a+3b+3c=1.
 \tag{RT3}
\]

Three admissible layouts give the respective expectations

\[
 1+15a,\qquad 1+14b+8c,\qquad 1+3b+15c.
 \tag{RT4}
\]

They select, respectively: the isolated row, column and point;
a spoke row, common column and its private point; and a spoke row,
its private column and private point. Average RT4 with weights
`31/166`, `90/166`, `45/166`. Their nonconstant weighted sum is

\[
 \frac{465}{166}(a+3b+3c)=\frac{465}{166}.
\]

Thus every supported law has `Gamma_35>=631/166`. Equality is
attained by the single symmetric law

\[
 (a,b,c)=\frac{(62,35,55)}{332}.
 \tag{RT5}
\]

For completeness, apply the exact root expansion TB4 of report 390.
After multiplying its nonconstant part by 332, the maximum over the
freely chosen point residue for each row/column category is:

| Chosen row | Chosen column | Nonconstant numerator |
| --- | --- | ---: |
| spoke | common | 930 |
| isolated | common | 811 |
| spoke | its private column | 930 |
| spoke | another spoke's private column | 710 |
| isolated | private | 661 |
| isolated | isolated | 930 |
| spoke | isolated | 766 |

Choices in absent rows, columns or point cells contribute an identically
zero indicator; replacing one by any supported choice only increases
the nonnegative load. The table therefore covers the full maximum.
Consequently

\[
 \inf_{\nu\text{ on }B}\Gamma_{35}(\nu)
       =\Gamma_{35}(\nu_*)=1+\frac{930}{332}
       =\frac{631}{166}<4.
 \tag{RT6}
\]

No uniqueness of the optimizing law is asserted. In particular, RT6
does not say that every optimal law has the same higher-digit behavior.
Its isolated atom `62/332` exceeds `1/6`, so RT5 is not the capped
witness TB8 used in report 390's separate uniform-tail estimate.

## 3. The identical product of this optimal law fails

Take `R_2` in `Z/25 x Z/49`, with one copy of RT5 independently at
each digit level. Preserve the original nine numerical divisor labels
of `1225`. The following fixed test is allowed:

| Divisor | 1 | 5 | 25 | 7 | 49 | 35 | 175 | 245 | 1225 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Residue | 0 | 1 | 11 | 1 | 15 | 1 | 36 | 211 | 561 |

Directly grouping its squared loads by the two point types in RT3
gives, for an identical product with general masses `(a,b,c)`,

\[
 \mathbb E L^2
 =16a^2+139ab+84ac+9b^2+18bc+9c^2.
 \tag{RT7}
\]

At RT5 this is `361237/55112`. The proposed comparison is

\[
 T_{2,2}=\left(1+\frac33+\frac59\right)^2
        =\frac{529}{81},\qquad
 \frac{361237}{55112}-\frac{529}{81}
        =\frac{105949}{4464072}>0.
 \tag{RT8}
\]

This one literal layout already proves the failure. The complete
separation calculation in section 5 also confirms it is maximizing
for this law, but that exhaustive upper bound is not required for RT8.
The residues of distinct divisors are not identified or required to
share a center.

The earlier type-B witness of report 390, with masses `(3,2,3)/18`,
also fails after taking its identical product: its complete maximum
is `2117/324`, exceeding `529/81=2116/324` by `1/324`. These two
examples do not exclude other identical products, different laws
at different digit levels, or correlated supported laws.

## 4. A depth-dependent product law succeeds on the same source

Give each low-digit and high-digit point its indicated per-point mass:

\[
 \nu_{\rm low}(I,H,P)=\frac{(54,35,47)}{300},\qquad
 \nu_{\rm high}(I,H,P)=\frac{(63,27,52)}{300}.
 \tag{RT9}
\]

Each law normalizes because `I,H,P` have respectively one, three
and three points. The single product probability
`nu=nu_low x nu_high` on the original 49 points satisfies

\[
 \Gamma_{1225}(\nu)=\frac{6157}{1000},\qquad
 \frac{529}{81}-\Gamma_{1225}(\nu)
          =\frac{30283}{81000}>0.
 \tag{RT10}
\]

A layout centered at the literal CRT point `106 mod 1225` attains
RT10. The upper certificate covers **all** independent layouts;
it is obtained by the complete integer separation described below.
This is an exact value for RT9, not a minimax claim over all laws
on `R_2` and not a general bound for all excluded-root sources.

The high-digit law alone has a root test of value
`1+15(63/300)=83/20>4`. Thus imposing the same root bound on every
digit law is not necessary for RT10 either. The objective is the
complete original load under one law, rather than separate local
objectives whose compatibility has not been established.

## 5. Exact separation with a singleton final intersection

This reduction applies to any finite nonempty source in
`Z/p^2 x Z/q^2`, for coprime integers `p,q>1`, with one probability
on its distinct CRT points. Its test family is exactly the nine labels
`{p^a q^b:0<=a,b<=2}`. These are all divisors of the carrier when
`p,q` are prime; for composite inputs this is only the stated selected
family, not the complete divisor family. Let `w_z` be nonnegative integer weights
of positive total `W`; division by `W` is performed at the end.

Fix arbitrary supported residues for `p,p^2,q,q^2,pq`. Include the
constant divisor-one term in their baseline load `v_z`. The remaining
three labels are `p^2 q`, `p q^2`, and `p^2 q^2`.
Write `B,C` for their first two chosen cylinders; the last chooses
one point. Any `B` and `C` intersect in at most one source point,
because their lcm is the full carrier. Put

\[
 h_z=(2v_z+1)w_z,\quad
 G_B=\sum_{z\in B}h_z,\quad G_C=\sum_{z\in C}h_z,
\]
\[
 H_0=\max_z h_z,\qquad
 H_B=\max_{z\in B}(h_z+2w_z),\qquad
 H_C=\max_{z\in C}(h_z+2w_z).
 \tag{RT11}
\]

All maxima over cylinders range over nonempty source cells.
Source-empty residues can be discarded by pointwise domination.
The exact maximum increment beyond `sum_z v_z^2 w_z` is

\[
 \max\{M_0,M_B,M_C,M_I\},                           \tag{RT12}
\]
\[
 \begin{aligned}
 M_0&=\max_B G_B+\max_C G_C+H_0,\\
 M_B&=\max_B(G_B+H_B)+\max_C G_C,\\
 M_C&=\max_B G_B+\max_C(G_C+H_C),\\
 M_I&=\max_z\left[
 G_{B(z)}+G_{C(z)}+2w_z
 +\max\{H_0,H_{B(z)},H_{C(z)},h_z+4w_z\}\right].
 \end{aligned}
\]

Here `B(z),C(z)` are the unique corresponding cylinder cells
containing `z`. The formula includes points of weight zero.

To prove it, first fix `B,C`. Adding their indicators contributes
`G_B+G_C+2 w(B intersect C)`. At a chosen final point `z`, the
additional contribution is
`h_z+2w_z 1_B(z)+2w_z 1_C(z)`. Its maximum is the maximum of
`H_0,H_B,H_C` and, when the intersection is `{u}`, `h_u+4w_u`.
If the intersection has positive mass, all these choices are included
in `M_I`. If it has zero mass, `M_0,M_B,M_C` bound the possibilities.
Conversely, each of the first three displayed quantities is at most
the true maximum: choose its maximizing cylinders and point, and the
omitted intersection or point bonuses are nonnegative. Each `M_I`
candidate is the exact fixed-cylinder value. This proves equality.

The last three choices therefore require linear work in the source
size and the two cylinder inventories after group sums have been
computed. They do not require enumerating every triple of residues.
All five baseline choices are still exhausted; the result remains
a finite exact algorithm, not a bound on unbounded arithmetic depth.

## 6. Reusable program and finite certificates

The [integer separation program](../../frontier/cover-geometry/height_two_layout_second_moment.py)
implements RT11--RT12, reconstructs a maximizing layout independently
by examining every final cylinder pair at the winning baseline, and
checks its squared load using the original numerical moduli.
It accepts explicit source data for further experiments; it uses
NumPy integer arrays, exact rational output, and an overflow guard.

The default controls cover all 56,000 baseline choices for each of
the three laws above on `R_2`. Their final cylinder inventories have
28, 35 and 49 nonempty choices. Small independent full-layout
enumerations check the formula on sources with different incidences
and a zero point weight. The root RT5 law is also checked against
all 1,225 independent root layouts. These controls verify the stated
finite certificates and the implementation; the general separation
identity follows from the proof in section 5.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_layout_second_moment.py
```

Reports 376, 378 and 379 supply the original tree conditions and their
conditional or forest probability constructions. Report 390 supplies
the exact root expansion reused in section 2. The result here separates
root optimization, its proposed identical-product extension, and a
different successful full-height law on the same normalized source.
It supplies neither the missing general constrained-tail law nor a
contradiction for unrestricted original covering families.
