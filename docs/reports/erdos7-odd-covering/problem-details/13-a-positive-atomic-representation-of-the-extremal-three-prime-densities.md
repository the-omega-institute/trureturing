[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](12-coupling-the-shared-zero-exponent-layout.md) · [Next](14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md)

<a id="a-positive-atomic-representation-of-the-extremal-three-prime-densities"></a>
### A positive atomic representation of the extremal three-prime densities

The density coordinates used by the exact R357=1649/360 relaxation
certificate are

    (t,v35,v37,v57)=(21/8,7/4,21/10,103/40).

They admit a genuine positive probability space for the abstract subsystem
survival events. Consequently, adding Gram positivity or higher moment
positivity for those events alone cannot exclude this density point.
This probability space is not asserted to arise from actual residue
classes; it does not rule out an improvement using CRT compatibility or
the actual cylinder indicators.

Let Ω have five atoms. The table gives their probabilities and indicators
of E357, E35, E37, E57:

| Probability | E357 | E35 | E37 | E57 |
|---:|---:|---:|---:|---:|
| 8/21 | 1 | 1 | 1 | 1 |
| 1/15 | 0 | 1 | 1 | 1 |
| 2/105 | 0 | 1 | 1 | 0 |
| 1/5 | 0 | 1 | 0 | 1 |
| 1/3 | 0 | 0 | 1 | 1 |

All probabilities are strictly positive and their sum is one. Direct
summation gives

    λ357=8/21, λ35=2/3, λ37=4/5, λ57=103/105.

Dividing by λ357 gives exactly the displayed density coordinates.
Moreover,

    P(E35∩E37)=49/105,
    P(E35∩E57)=68/105,
    P(E37∩E57)=82/105,
    P(E35∩E37∩E57)=47/105.

Thus the pair-survival failures have disjoint masses 1/3, 1/5, and
2/105<=1/15; the extra failure of full three-prime survival has mass
1/15. These satisfy the exact-support budgets. Every union-of-subsystems
inequality derived only from those budgets is therefore valid on this
atomic model. The three prime-adjoining bounds also hold:

    λ357=(4/7)λ35,
    λ357 >= (6/13)λ37 = 24/65,
    λ357 >= (5/14)λ57 = 103/294.

For a concrete matrix certificate, put Y=(1,1_E357,1_E35,1_E37,1_E57).
The normalized Gram matrix M=E[YYᵀ]/λ357 is

    [ 21/8   1   7/4    21/10   103/40 ]
    [ 1      1   1      1       1      ]
    [ 7/4    1   7/4    49/40   17/10  ]
    [ 21/10  1   49/40  21/10   41/20  ]
    [ 103/40 1   17/10  41/20   103/40 ].

Its positive rank-one decomposition uses the five table vectors, prefixed
by 1, with weights

    1, 7/40, 1/20, 21/40, 7/8.

For every real vector z,

    zᵀMz = sum_ω weight(ω) (z·Y(ω))² >= 0.

In fact M is positive definite: the five vectors span R⁵. Subtracting the
second vector from the first isolates the E357 coordinate; subtracting
each of the last three vectors from the second isolates the other three
event coordinates; the constant coordinate follows. Hence a zero quadratic
form forces z=0. No numerical eigenvalue calculation is needed.

For arbitrary polynomial functions f₁,...,f_m of these indicators, the
same identity shows the moment matrix E[f_i f_j] is positive semidefinite.
All Boolean relations and inclusions E357⊆E35∩E37∩E57 hold pointwise.
The obstruction therefore applies to every order of abstract subsystem
moment positivity, not merely to a second-order PSD relaxation. It does
not apply to matrices that additionally encode realizable congruence
intersections or conditional root-residue profiles.

<a id="nonuniform-two-root-survivor-laws"></a>
### Nonuniform two-root survivor laws

The following two-prime constructions remain valid. The uniform law in
(ZG1) now gives the stronger pair `(Γ35,R35)≤(55/4,15/7)`, which dominates
both (N1) and (N2). Their weighted-root method also supplies the different
nonuniform construction for the rectangular obstruction family below.

For every finite family of distinct moduli supported on `{3,5}`, there is a
probability law supported on its complete survivor set satisfying

\[
 \boxed{\Gamma\le14,\qquad R\le15/7.} \tag{N1}
\]

This law is either the uniform survivor law or a specified law constant
within each of the two surviving ternary roots. A single explicit weighting
rule also gives the separate tradeoff

\[
 \boxed{\Gamma\le277/20,\qquad R\le11/5.} \tag{N2}
\]

These are arbitrary-height mathematical bounds with exact rational
verification of the continuous parameter inequalities. They are not Lean
formalizations, and the new law does not inherit uniform-law profile bounds.

<a id="complete-survivor-parameters-and-positivity"></a>
#### Complete-survivor parameters and positivity

First suppose an actual modulus-3 class is present. Let `A,B` be the other
two ternary roots, and let `w,v` be their relative pure-ternary survivor
densities. Set `y=1/4`, `a=7/8`. The established distinct-modulus budgets are

\[
 1/2\le w,v\le1,\quad w+v\ge3/2,\quad
 3/4\le z\le1,\quad \alpha,\beta\ge0,\quad\alpha+\beta\le y,
\]
\[
 t,u\ge0,\quad t+u\le y/6,\qquad
 d=z-\alpha,\quad e=z-\beta,\quad
 n=wd/3-t,\quad m=ve/3-u. \tag{N3}
\]

Here `z` is the pure-5 survivor density, `α,β` are the actual first-level
mixed exclusions inside it, and `t,u` are the remaining mixed exclusions in
the two roots. The complete survivor densities `n,m` are exact. Both satisfy

\[
 n,m\ge\tfrac12\frac{1-2y}{3}-\frac y6=\frac1{24}>0. \tag{N4}
\]

Thus an empty surviving root cannot occur for this family class. All
normalizations below are positive. Missing higher powers merely decrease
the actual exclusions and are already included in these inequalities.

For arbitrary `h,k≥0`, not both zero, put `S=hn+km`. Give raw survivor
points in `A,B` the density multipliers `h,k`, respectively, and normalize
by `S`. This defines a complete-survivor probability `μ_{h,k}`. Write

\[
 x_h=(hw+kv)/3,
\]
\[
 P_h=\max\{h(3n+d),\ 3hn+2ke/3,\ k(3m+e),\ 3km+2hd/3\},
\]
\[
 Q_h=\max\{h(w+1),\ hw+2k/3,\ k(v+1),\ kv+2h/3\}. \tag{N5}
\]

<a id="weighted-layout-and-cylinder-inequalities"></a>
#### Weighted layout and cylinder inequalities

The universal weighted-root bounds are

\[
 \Gamma(\mu_{h,k})\le1+\frac{P_h+a(x_h+Q_h)}S, \tag{N6}
\]
\[
 R(\mu_{h,k})\le\frac{\max(hn,km)+\max(hd,ke)/6
       +y\{x_h+\max(hw,kv)/3+\max(h,k)/6\}}S. \tag{N7}
\]

To prove (N6), first consider the pure-ternary part of one complete test
layout. Its root masses before normalization are `hn,km`; its depth-`j`
cylinder caps in the two roots are `hd/3^j,ke/3^j`. The existing two-root
finite-itinerary Bellman inequality, applied to these weighted caps, bounds
its second moment by `S+P_h`. The constant diagonal is `S` and the
modulus-3 diagonal plus its two crosses with the constant give `3hn` or
`3km`. All later choices, including choices in the forbidden root, are
included by that same finite-itinerary argument.

For positive 5 exponents, let `η` be the finite positive measure on the
pure-ternary survivor set with root density multipliers `h,k` and no mixed
exclusions. Its mass is `x_h`, root masses are `hw/3,kv/3`, and depth caps
are `h/3^j,k/3^j`. The same Bellman inequality gives
`Γ(η)≤x_h+Q_h`.

Group ordered test-divisor pairs by their 5-adic least-common-multiple
exponent `b≥1`. For each ordered pair of outside exponents with maximum
`b`, the two old residue choices form complete pure-ternary layouts,
including divisor one and every old cofactor. The selected 5-adic residues
may depend on the old divisor. Pair by pair their intersection has uniform
5-adic mass at most `5^{-b}`. Dropping actual 5 and mixed exclusions only
increases the nonnegative integral. After summing the old indicators,
Cauchy–Schwarz under `η` bounds the cross moment of the two complete old
layouts by `Γ(η)`. There are `2b+1` outside exponent pairs. Finally
`∑_{b≥1}(2b+1)5^{-b}=7/8=a`, proving (N6) after division by `S`.
This whole-layout estimate replaces the weaker maximum-root-density cap.

For (N7), the pure-ternary cylinder sum is bounded by
`max(hn,km)+max(hd,ke)∑_{j≥2}3^{-j}`. For every positive 5 exponent, drop
its exclusions and sum the pure-ternary cylinder maxima of `η`. The
constant term is `x_h`, its depth-one term is `max(hw,kv)/3`, and its
remaining tail is `max(h,k)/6`. Summing `5^{-b}` over `b≥1` contributes
`y`. This proves (N7). Both arguments are upper bounds for every finite
prime height; the infinite series omit no actual test divisor.

<a id="explicit-balanced-law-and-full-continuous-domain-certificate"></a>
#### Explicit balanced law and full continuous-domain certificate

Choose

\[
 h=v+1,\qquad k=w+1. \tag{N8}
\]

The first and third terms of `Q_h` then both equal `(w+1)(v+1)`. Each
cross term is smaller, since `2(w+1)/3≤v+1` and its symmetric inequality
hold throughout (N3). Consequently `Q_h=(w+1)(v+1)`.

For each of the four branches of `P_h`, clear the positive denominator in
(N6) with proposed bound `277/20`. For each of the sixteen choices of the
four maxima in (N7), do the same with proposed bound `11/5`. The resulting
20 polynomial margins are nonnegative throughout (N3), as follows.
They are separately affine in the three parameter groups
`(α,β)`, `z`, and `(t,u)`, so it suffices to use their `3×2×3=18` vertices.
At each such vertex they have the form

\[
 f(w,v)=A_0+B_0w+C_0v+D_0wv.
\]

On the triangle `1/2≤w,v≤1`, `w+v≥3/2`, such a bilinear function has no
strict interior minimum. Its edges `w=1` and `v=1` are affine. On the
remaining edge substitute `v=3/2−w`, `1/2≤w≤1`, and check the quadratic's
endpoints and any interior critical point with positive quadratic
coefficient. This is a complete exact minimum calculation, not a grid.
The accompanying verifier checks all `20×18=360` minima with rational
arithmetic; every margin is nonnegative. This proves (N2).

<a id="uniform-fallback-preserving-the-r-bound"></a>
#### Uniform fallback preserving the R bound

Let `U` denote the right side of (N6) at `h=k=1`. Define the law in (N1):
choose the uniform complete-survivor law when `U≤14`; otherwise choose
(N8). The uniform case has `Γ≤14` by (N6), and its established nine-cell
bound gives `R≤15/7`. It remains to prove the same R bound when `U>14`.

With `h=k=1`, `Q_h=max(w+1,v+1)`. Number the four pure branches in the
order of (N5), starting at zero, and the two mixed branches `w+1,v+1`
also starting at zero. Define the eight uniform margins

\[
 F_i=13(n+m)-P_{\lfloor i/2\rfloor}
                -a\{(w+v)/3+Q_{i\bmod2}\},\qquad0\le i<8.
\]

Then `U>14` means at least one `F_i<0`. Six of these margins, all except
`F_1,F_4`, are nonnegative throughout (N3). Let `E_j`, `0≤j<16`, be the
balanced-law R margins at `15/7`. Their branch order is the lexicographic
order of choices from `(hn,km)`, `(hd,ke)`, `(hw,kv)`, `(h,k)`, with the
last choice varying fastest. For each `i∈{1,4}`, the following nonnegative
multipliers satisfy `E_j+λ_{ij}F_i≥0` throughout (N3):

| `i` | Nonzero multipliers; all others zero |
| --- | --- |
| `1` | `λ_1,4=1/168`, `λ_1,5=1/21`, `λ_1,10=8/21`, `λ_1,11=1/21` |
| `4` | `λ_4,4=1/21`, `λ_4,5=8/21`, `λ_4,10=1/21`, `λ_4,11=1/168` |

The same affine-group and bilinear-triangle method checks the six safe
uniform margins and these 32 combined margins: `38×18=684` exact
continuous minima. Hence if a uniform branch fails, every `E_j≥0`, giving
`R≤15/7` for the balanced choice. Its Gamma is already at most
`277/20<14`. This proves (N1).

If the actual modulus-3 class is absent, choose the established uniform
law, whose unsplit bounds are `Γ≤215/24` and `R≤17/12`; these satisfy
both (N1) and (N2). Thus no choice of a nonexistent pair of roots is needed.

<a id="coherent-propagation-to-three-primes-and-its-limitation"></a>
#### Coherent propagation to three primes and its limitation

Keep the chosen two-root multipliers fixed. Form the product of this
complete `{3,5}` law with the uniform pure-7 survivor law, and then condition
away the new mixed classes. This produces a law on the full `{3,5,7}`
survivor set with the same fixed root multipliers. It is generally
nonuniform. No estimate proved only for the uniform `{3,5,7}` law is used.

For an input pair `(G,R)`, the deleted mass `λ` is at most `R/5`. The
pure-7 cylinder caps give a product-layout bound `(5/3)G`, and the product
cylinder sum is at most `(6/5)(R+1)−1`. Every complete layout load is at
least one, so deleting mass `λ` removes at least `λ` from its second
moment. Both normalized upper bounds increase with `λ`, giving

\[
 \Gamma_{357}\le\frac{(5/3)G-R/5}{1-R/5},\qquad
 R_{357}\le\frac{(6/5)(R+1)-1}{1-R/5}. \tag{N9}
\]

For the uniform law from (ZG1), the same construction is again uniform
on the complete three-prime survivors. Substituting `G=55/4`, `R=15/7`
in the first inequality gives

\[
 \Gamma_{357}\le\frac{(5/3)(55/4)-3/7}{1-3/7}=\frac{1889}{48}.
\]

This law also has the established uniform bound `R357≤1649/360`.
Both coordinates improve the following nonuniform propagation bounds;
this is a direct consequence of (ZG1), not a separate Lean theorem.

Thus the balanced law gives `(Γ357,R357)≤(6793/168,71/14)`, while the
hybrid law gives

\[
 \boxed{\Gamma_{357}\le481/12,\qquad R_{357}\le97/20.} \tag{N10}
\]

The Gamma bound is below the earlier `653/16` transport bound. Its R bound
is above the uniform-law `1649/360` bound; those two estimates concern
different laws and cannot be combined. Continuing (N9)'s argument through
prime 11 gives only `Γ35711≤350/3` for the hybrid law, above the established
uniform four-prime bound `4939031/47730`. No four-prime or unrestricted
Erdős #7 improvement follows from the present propagation.

[The nonuniform-law verifier](../verify_nonuniform_root_law.py)
and its [fixed certificate](../certificates/nonuniform_root_certificate.json)
verify the 1,044 continuous polynomial minima, root positivity, absent-modulus
branch, both law bounds, fixed fallback multipliers and exact coherent
propagation. The numerical certificate concerns only these rational
inequalities; the weighted-layout mapping above is an ordinary proof.

<a id="search-result-and-reuse-boundary"></a>
#### Search result and reuse boundary

The local project supplies the two-root Bellman theorem and the existing
uniform cylinder bounds. Pinned Mathlib provides `Sion.exists_isSaddlePointOn`
for compact convex minimax; no new minimax wrapper is needed here.
BBMST, arXiv:1901.11465, section 5.3, constructs nonuniform survivor
probabilities by linear programming and controls subsequent deletion and
renormalization. That construction is squarefree and does not directly
supply (N6)–(N10) for arbitrary powers. The new step here is the weighted
complete-layout inequality and its continuous distinct-modulus budget
certificate, not the general linear-programming method.

<a id="a-universal-nonuniform-law-below-the-sharp-uniform-bound"></a>
### A universal nonuniform law below the sharp uniform bound

For every finite family of distinct moduli greater than one supported on
`{3,5}`, with one forbidden residue class per modulus, there is a probability
law `μ` on its complete survivor set such that

\[
 \boxed{\Gamma(\mu)\le687/50<55/4,\qquad
 R(\mu)\le37/17,\qquad
 \frac{d\mu}{dU_S}\le16/15.} \tag{NC1}
\]

Here `U_S` is the uniform law on the same complete survivor set. The last
inequality is pointwise. The law is constant within each surviving ternary
root; its ratio of root multipliers is one of `1`, `11/12`, and `12/11`.
The finite prime heights and the mixed residue choices are arbitrary. The
Gamma bound is strictly below the sharp universal uniform-law bound; the
R bound is higher than the uniform-law `15/7` bound.

As usual, a complete test layout chooses one residue for every divisor of
the finite product period, including divisor one. Its load `L` is the sum
of those indicators, and `Γ(μ)=max_L ∫L² dμ`. Define
`R(μ)=∑_{d>1} max_a μ(a mod d)`, over the same divisors. Neither the
layouts nor the mixed forbidden classes are assumed to have product form.

<a id="actual-parameters-and-the-law"></a>
#### Actual parameters and the law

Suppose first that an actual modulus-3 class is present. Its complement
consists of two ternary roots `A,B`. Set `y=1/4` and `a=7/8`. The actual
pure-ternary survivor densities within these roots are `w,v`; the actual
pure-5 survivor density is `z`. Within the pure-5 survivors, let `α,β` be
the ambient 5-coordinate measures excluded by the union of the `3·5^b` classes whose ternary
root is respectively `A,B`. These unions are constant across their whole
ternary root. Let `t,u` be the further ambient masses removed in `A,B`
by classes `3^i5^b` with `i≥2,b≥1`, after the preceding exclusions.
Distinct moduli give the budgets

\[
 1/2\le w,v\le1,\quad w+v\ge3/2,\qquad
 3/4\le z\le1,\quad \alpha,\beta\ge0,\quad\alpha+\beta\le1/4,
\]
\[
 t,u\ge0,\quad t+u\le1/24,\qquad
 d=z-\alpha,\quad e=z-\beta,\quad
 n=wd/3-t,\quad m=ve/3-u. \tag{NC2}
\]

The last two quantities are the exact ambient densities of complete
survivors in the two roots. Indeed the sum of pure-ternary exclusions at
depth at least two is at most `1/6`; the first mixed layer has total 5-mass
at most `y`; and the deeper mixed classes have total ambient mass at most
`(1/6)y`. Omitting any actual modulus only reduces these budgets. In
particular `d,e≥1/2` and

\[
 n,m\ge(1/2)(1/2)/3-1/24=1/24>0. \tag{NC3}
\]

For positive numbers `h,k`, give each complete survivor in `A` raw density
`h`, and each in `B` raw density `k`, relative to ambient uniform measure.
Normalize this measure by `S=hn+km` to obtain `μ_{h,k}`. This definition
allows old fibres to be partly or entirely removed. It never conditions
on a fibre having positive mass. Both surviving roots themselves have
positive mass by (NC3).

Let `η` be the raw pure-ternary survivor measure with the same root
multipliers `h,k`, and set

\[
 x=(hw+kv)/3,\qquad
 A_A=\max\{h(w+1),hw+2k/3\},\quad
 A_B=\max\{k(v+1),kv+2h/3\},\quad B=\max(A_A,A_B),
\]
\[
 P_A=\max\{3hn+hd,3hn+2ke/3\},\qquad
 P_B=\max\{3km+ke,3km+2hd/3\}. \tag{NC4}
\]

The coupled weighted envelope is

\[
 \Gamma(\mu_{h,k})\le1+
 \frac{\max\{P_A+ax+yA_A+(a-y)B,
                 P_B+ax+yA_B+(a-y)B\}}{S}. \tag{NC5}
\]

<a id="preserving-the-zero-exponent-layout"></a>
#### Preserving the zero-exponent layout

Fix a complete `{3,5}` test layout `L`. For each 5-exponent `b`, let `L_b`
be its complete pure-ternary layout after stripping the 5-parts of the
divisors. Divisor one and every old cofactor remain. The selected 5-adic
residue may depend on the old cofactor. The positive-measure domination

\[
 \mu_{h,k}\le S^{-1}(\eta\times U_5)
\]

holds by dropping pure-5 and mixed exclusions, without requiring any
conditional fibre lower bound. Write `A_0=∫L_0² dη` and `B_0=Γ(η)`.
The zero-zero block is exactly `∫L_0² dμ_{h,k}`. For the ordered blocks
`(0,b),(b,0)` at positive exponent `b`, each pair of outside cylinders
has uniform intersection mass at most `5^{-b}`. Sum this bound over the
old indicators before applying `2L_0L_b≤L_0²+L_b²`. Their joint
contribution is at most `5^{-b}(A_0+B_0)/S`.

There are `2b−1` remaining ordered exponent pairs with both exponents
positive and maximum `b`. Each old-layout cross moment is at most `B_0`
by Cauchy–Schwarz. Since
`∑_{b≥1}5^{-b}=y` and `∑_{b≥1}(2b−1)5^{-b}=a−2y`, it follows that

\[
 \int L^2\,d\mu_{h,k}\le\int L_0^2\,d\mu_{h,k}
               +\frac{yA_0+(a-y)B_0}{S}. \tag{NC6}
\]

All omitted infinite-tail terms are nonnegative, so this holds at every
finite height. It is an inequality for each fixed `L`; the same `L_0`
must occur in both terms on the right.

Apply the established root-labelled finite-itinerary Bellman bound to
this `L_0`. For the raw complete measure the two root masses are `hn,km`
and the depth-`j` cylinder caps are `hd/3^j,ke/3^j`. Under `η` the
corresponding data are `hw/3,kv/3` and `h/3^j,k/3^j`.
If the modulus-3 test chooses root `A`, these bounds give

\[
 \int L_0^2\,d\mu_{h,k}\le1+P_A/S,\quad
 A_0\le x+A_A,\quad B_0\le x+B. \tag{NC7}
\]

For root `B` use `P_B,A_B`. The root-labelled formula accounts for the
constant diagonal, the initial-root diagonal and constant crosses, and
all later choices, including moves between the two surviving roots.
It is the same finite-itinerary inequality underlying
`TernaryRootLoadTail.root_load_tail_le` and
`TwoRootEventMoment.two_root_event_moment_le`; no product-layout
assumption is introduced.

If the modulus-3 test instead chooses the actual forbidden root, its event
has zero mass. The same tail bound gives raw excess at most
`(2/3)max(hd,ke)` and `A_0−x≤(2/3)max(h,k)`. This branch is dominated:
if `hd≥ke`, use the `B` branch, since `P_B≥2hd/3` and
`A_B=max(k(v+1),kv+2h/3)≥(2/3)max(h,k)`. If `ke≥hd`, use `A`
symmetrically. Substitution in (NC6) proves (NC5), including this third
possible initial test root.

The same law also obeys the cylinder envelope

\[
 R(\mu_{h,k})\le
 \frac{\max(hn,km)+\max(hd,ke)/6
       +y\{x+\max(hw,kv)/3+\max(h,k)/6\}}{S}. \tag{NC8}
\]

For pure ternary divisors the first term handles depth one, and the
remaining cap sum is `max(hd,ke)∑_{j≥2}3^{-j}`. For each positive
5-exponent, dropping its exclusions leaves the pure-ternary cylinder
sum of `η`, including the divisor-one mass `x`. Summing `5^{-b}`
gives (NC8). The pointwise relative density is exactly `h(n+m)/S`
on root `A` and `k(n+m)/S` on root `B`; consequently

\[
 \frac{d\mu_{h,k}}{dU_S}\le\frac{(n+m)\max(h,k)}{S}. \tag{NC9}
\]

<a id="the-adaptive-rule-and-its-exact-certificate"></a>
#### The adaptive rule and its exact certificate

Let `C=687/50`. Expand (NC5)'s maxima into 32 numerators `N_j` in this
order: first choose `(P_A,A_A)` or `(P_B,A_B)`; then one of the two
displayed entries of that `P`; then one of the two entries of that `A`;
finally one of the four entries of `(A_A,A_B)`, with the last choice
varying fastest. Set

\[
 E_j(h,k)=(C-1)(hn+km)-N_j(h,k),\qquad F_i=E_i(1,1). \tag{NC10}
\]

If every `F_i≥0`, choose `h=k=1`. Otherwise let `i` be the least index
with `F_i<0`, and choose weights as in the table. Only its six listed
indices can be negative anywhere in (NC2).
If several are negative, the same proof works for any one of them;
choosing the least index simply makes the law deterministic.

| Trigger `i` | `h`, with `k=1` | Nonzero `λ_ij`; all others zero | `ρ_i` |
| --- | --- | --- | --- |
| 0 | 11/12 | `λ_0,16=97/1764`, `λ_0,18=1135/6264`, `λ_0,26=535/6264` | 5/51 |
| 2 | 11/12 | `λ_2,16=97/6264`, `λ_2,18=1135/1764`, `λ_2,26=535/1764` | 10/1227 |
| 8 | 11/12 | `λ_8,16=97/1764`, `λ_8,18=1135/12264`, `λ_8,26=535/12264` | 5/801 |
| 16 | 12/11 | `λ_16,0=1135/1617`, `λ_16,2=97/5742`, `λ_16,8=535/1617` | 40/4499 |
| 18 | 12/11 | `λ_18,0=1135/5742`, `λ_18,2=97/1617`, `λ_18,8=535/5742` | 20/187 |
| 26 | 12/11 | `λ_26,0=1135/11242`, `λ_26,2=97/1617`, `λ_26,8=535/11242` | 20/2937 |

The fixed rational certificate verifies, throughout the full domain,

\[
 E_j(h_i,1)+\lambda_{ij}F_i\ge0\quad(0\le j<32),
\]
\[
 (16/15)(h_in+m)-\max(h_i,1)(n+m)+\rho_iF_i\ge0. \tag{NC11}
\]

Every multiplier is nonnegative. Hence `F_i<0` implies each required
Gamma margin and the density margin is nonnegative. It also checks all
16 cleared branches of (NC8) at `R=37/17`, globally for each of the two
fixed nonuniform ratios. No trigger restriction is needed for this R
bound. Its exact envelope maximum over the budget domain is `37/17`.
The uniform fallback uses the existing same-law `R≤15/7<37/17`, and
has relative density one.

This verification covers a continuous domain. Every cleared expression
in (NC10)–(NC11) and the fixed-weight R margins is affine in each of the
four groups `(w,v)`, `(α,β)`, `z`, `(t,u)` while the other groups are
fixed. Its value at a convex combination in any one group is the same
convex combination of vertex values. Applying this successively reduces
nonnegativity to exactly the `3·3·2·3=54` product vertices

\[
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\qquad
 (\alpha,\beta)\in\{(0,0),(1/4,0),(0,1/4)\},
\]
\[
 z\in\{3/4,1\},\qquad
 (t,u)\in\{(0,0),(1/24,0),(0,1/24)\}. \tag{NC12}
\]

The verifier checks 1,404 safe-uniform, 10,368 adaptive-Gamma, 1,728
fixed-weight-R, and 324 adaptive-density vertex inequalities: 13,824 in
total. Their minimum margins are respectively `97/1200,0,0,0`.
These checks require only exact rational arithmetic and remain active
under Python optimization. They do not approximate the parameter domain
by a grid or enumerate only selected finite families.

If an actual modulus-3 class is absent, choose the existing uniform law:
its bounds `Γ≤215/24`, `R≤17/12` and relative density one satisfy (NC1).
This includes missing powers and avoids inventing a pair of surviving
roots in that case. Thus (NC1) applies to all finite families under the
stated hypotheses.

<a id="downstream-use-and-boundary"></a>
#### Downstream use and boundary

The density bound can transfer any nonnegative observable from `U_S`
to this same-family law with factor at most `16/15`. It does not preserve
the uniform law's sharper cylinder profile unchanged, and it does not
state a conditional cap in every old fibre.

One coherent general propagation keeps the chosen root multipliers,
forms the product with the uniform pure-`p` survivor law, and conditions
away the new mixed classes. Given simultaneous bounds `(G,R)`, write
`ℓ=R/(p−2)`. When `ℓ<1`, the resulting law satisfies

\[
 G'\le\frac{\frac{p^2+1}{(p-1)(p-2)}G-\ell}{1-\ell},\qquad
 R'\le\frac{\frac{p-1}{p-2}(R+1)-1}{1-\ell}. \tag{NC13}
\]

The loss bound uses every old cofactor. The subtraction in the first
numerator is valid because each complete layout has load at least one
on the deleted set. Applying (NC13) to (NC1), then to prime 11, gives

\[
 (\Gamma_{357},R_{357})\le(1273/32,239/48),\qquad
 (\Gamma_{35711},R_{35711})\le(230569/1930,2438/193).
\]

The four-prime Gamma bound exceeds the existing uniform bound
`4939031/47730`. Thus the present general repair proves a strict
two-prime Gamma improvement, but this propagation does not improve the
known four-prime bound or establish the existential Gamma-73 target.

The [standalone verifier](../verify_nonuniform_coupled_law.py)
and its [fixed certificate](../certificates/nonuniform_coupled_certificate.json) check the displayed rational
certificate, positivity, fallback comparisons and propagation. The
arbitrary-family layout correspondence and continuous-domain reduction
above are ordinary mathematical proofs. No full Lean formalization of
(NC1) is claimed.

The reused local ingredients are the root-labelled finite-itinerary
estimate and uniform cylinder budgets. The nonuniform-survivor linear
program in [BBMST, section 5.3](../../../../Library/Arith/balister2019erdos.md)
is a squarefree predecessor; it does not supply this arbitrary-power
weighted-envelope certificate.
